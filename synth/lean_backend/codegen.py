"""Helper-citation codegen — RESEARCH.md §H.2.

The per-class Lean verification path defaults to running a generic
tactic chain (`omega | nlinarith | aesop | simp_all`) on each
(constraint kind, chosen-atom-subset) tuple.  For axiom-heavy
benchmarks (Floyd-Warshall, modular_exp, etc.) this chain rarely
closes the obligation and costs 30-60s per call.

When the benchmark ships a Tier-3 helper (a hand-proven Lean
theorem that discharges a class of obligations from named
hypotheses), we can replace the generic chain with a one-line
`exact <helper> <args>` term.  Lean type-checks the citation in
~2s (cached `.olean` + no tactic search).

Boundaries
----------
This module is STRUCTURAL plumbing.  It does NOT write semantic
proofs.  The boundary between "what the codegen owns" and "what
the driver-LLM / human curator owns":

  Codegen owns:
    - Theorem signature (mechanically derivable from sc_kind +
      chosen_atoms).
    - Citation glue: `:= by exact <helper_name> <args>` where
      args are pulled from the theorem's binders via a
      registry-supplied lambda.
    - Subset-matching: a helper applies iff its required atoms
      are a subset of the chosen atoms.

  Driver-LLM / curator owns:
    - The helper's PROOF body (lives in
      `lean/SynthLean/Y2Corpus/<bench>/Helpers.lean`).
    - The semantic claim being proved.
    - The atom-index → helper-arg mapping (encoded in the
      `cite` lambda — knowledge of which τ atom plays which
      role in the helper's statement).

Wire-up
-------
Per-benchmark:

  1. Write helper(s) in `Helpers.lean`.  Import from
     `SynthLean.lean` so they build into `.olean`.
  2. Build a `HelperRegistry` listing each helper with:
     - `applies_to`: predicate over (sc_kind, loop_id, branch_idx).
     - `required_atoms`: per-hole set of atom indices that must
       be in the chosen subset for the helper to apply.
     - `cite`: lambda(chosen_atoms, hyp_for) → Lean proof body
       string.
  3. Set `Problem.helper_registry = REGISTRY`.

At verifier time, `try_helper_citation` is called BEFORE the
generic tactic chain.  On match, it returns the proof body
string; the verifier substitutes it.  On miss, returns None; the
verifier falls through to today's generic chain.

Soundness
---------
Lean type-checks every citation.  A buggy `cite` lambda (wrong
helper applied to wrong atoms) produces an unprovable goal that
Lean rejects.  Codegen NEVER bypasses Lean — it only changes the
proof body to be faster to check.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Any, Callable, Optional


HypForFn = Callable[..., str]
"""Map (hole_id, original-atom-index, role=..., chain_k=...) → Lean hypothesis name.

`original-atom-index` is the index in `Problem.atoms[hole_id]`,
NOT the position in the chosen subset.  The hyp_for callable
translates: it finds the chosen subset's position of that atom
and returns `h_<prefix>_tau_<position>` matching the translator's
emitted binders, where `<prefix>` depends on `role`:

  - `role="local"` (default) — `h_tau_<pos>`.  For the CURRENT
    loop's τ atoms in flat-shape theorems (most safety /
    ranking obligations).

  - `role="enc"` — `h_enc_tau_<pos>`.  For the ENCLOSING loop's
    τ atoms when the obligation is a chain-aware bundle on a
    NESTED loop.  Emitted by `theorem_for_entry_bundle_chain`
    and `theorem_for_chain_bundle_chain` when
    `enclosing_loop_id is not None`.

  - `role="chain"` (with `chain_k`) — `h_i<chain_k>_<loop_id>_tau_<pos>`.
    For a Loop item appearing as the `chain_k`-th item in a
    chain prefix.  `hole_id` must be `tau@<loop_id>` of that
    chain-Loop, and `chain_k` is its 0-based index in the chain.
    The translator's `_emit_chain_item_hyps` emits these for
    Loop items in chain prefixes.

F11 (community-validation 2026-06-08): the role/chain_k kwargs
were added after Q3 (count_pairs_equal) agent had to hardcode
`h_enc_tau_*` and `h_i1_L1_tau_*` strings — `hyp_for` couldn't
derive them.  Existing benchmarks that hardcode the prefixes
continue to work; new authors should use the role API.

Raises `ValueError` if the requested atom is NOT in the chosen
subset (a registry bug — the helper required an atom the matcher
should have filtered out).
"""


CiteFn = Callable[[dict, HypForFn], str]
"""(chosen_atoms, hyp_for) → Lean proof body string.

The returned string is what follows `:= by\n  ` in the emitted
theorem.  Typically a single `exact <helper_name> <args>` line,
but multi-line tactic sequences are allowed.
"""


@dataclass(frozen=True)
class HelperEntry:
    """One Tier-3 helper registered for the codegen path.

    The matcher applies this entry to a (sc_kind, loop_id,
    branch_idx, chosen_atoms) tuple iff:
      1. `applies_to(sc_kind, loop_id, branch_idx)` returns True.
      2. For each `(hole_id, required)` in `required_atoms`, the
         chosen subset for `hole_id` contains every original
         atom index in `required`.
    """
    helper_name: str
    applies_to: Callable[[str, str, Optional[int]], bool]
    required_atoms: dict[str, frozenset[int]]
    cite: CiteFn


@dataclass
class HelperRegistry:
    """A benchmark's collection of registered helpers.

    `module_path` is the Lean module path holding the helpers and
    their supporting axioms (UF declarations, user-axiom mirrors,
    trust axioms).  When a helper from this registry fires, the
    verify temp file imports this module DIRECTLY and skips
    `emit_axiom_declarations` to avoid duplicate UF / axiom
    declarations.  Per-benchmark, e.g.:

        module_path = "SynthLean.Y2Corpus.floyd_warshall.Helpers"
    """
    module_path: str
    entries: list[HelperEntry] = field(default_factory=list)

    def find(self,
             sc_kind: str,
             loop_id: str,
             branch_idx: Optional[int],
             chosen_atoms: dict) -> Optional[HelperEntry]:
        """Return the first entry that applies, or None."""
        for e in self.entries:
            if not e.applies_to(sc_kind, loop_id, branch_idx):
                continue
            if not _required_atoms_present(e, chosen_atoms):
                continue
            return e
        return None

    def validate_synthlean_import(self,
                                  lean_root: Optional[str] = None) -> Optional[str]:
        """Check that `module_path` is imported from `SynthLean.lean`.

        Returns None if the import is present, or a warning message
        if it's missing.  Called once per `solve()` invocation when
        a Problem has `helper_registry` set; the result is printed
        as a warning to stderr if non-None.

        Rationale (community-validation finding F2, 2026-06-08):
        a missing `import SynthLean.Y2Corpus.<bench>.Helpers` line
        in `lean/SynthLean.lean` is the most common HelperRegistry
        footgun.  Without the import, `lake env lean <tmpfile>`
        can't find the helper module — every per-class dispatch
        fails with `unknown identifier <helper>` errors, but the
        synth-side wedge detector reports it as
        `needs-helpers` (looks like the helper wasn't matched,
        when actually it was matched but couldn't be loaded).
        This validator emits a clear error early.
        """
        import os
        if lean_root is None:
            # Default: relative to the running synth's CWD.
            # `lean/SynthLean.lean` is the canonical root.
            lean_root = os.path.join(os.getcwd(), "lean")
        synthlean_path = os.path.join(lean_root, "SynthLean.lean")
        if not os.path.isfile(synthlean_path):
            return (f"HelperRegistry validation: "
                    f"{synthlean_path} not found.  Run from the "
                    f"repo root or set lean_root explicitly.")
        try:
            with open(synthlean_path) as f:
                contents = f.read()
        except OSError as e:
            return f"HelperRegistry validation: couldn't read {synthlean_path}: {e}"
        expected = f"import {self.module_path}"
        if expected not in contents:
            return (
                f"HelperRegistry validation FAILED: "
                f"`{expected}` is not in `lean/SynthLean.lean`.\n"
                f"  Without this import, `lake env lean` cannot find "
                f"helpers in `{self.module_path}` — every per-class "
                f"dispatch will fail with `unknown identifier` errors "
                f"and synth will wedge with `needs-helpers`.\n"
                f"  Fix: append the line to `lean/SynthLean.lean`, "
                f"then `cd lean && lake build {self.module_path}`.\n"
                f"  See `problem.skill` 'Importing into the lake build' "
                f"for details."
            )
        return None


def _required_atoms_present(entry: HelperEntry, chosen_atoms: dict) -> bool:
    """Check that every required atom index is in the chosen subset.

    For τ-holes, `chosen_atoms[hole_id]` is a list of atom STRINGS
    (the actual selected atoms).  Required indices refer to the
    Problem.atoms[hole_id] master list.  This function doesn't have
    direct access to that master list, so the matcher caller is
    responsible for supplying chosen_atoms with the position info.

    Implementation: `chosen_atoms[hole_id]` is the list of selected
    atom strings.  The matcher uses the convention that
    `chosen_atoms` ALSO carries `__indices__:<hole_id>` keys giving
    the original indices.  See `try_helper_citation` for the
    convention.
    """
    for hole_id, required in entry.required_atoms.items():
        indices_key = f"__indices__:{hole_id}"
        if indices_key not in chosen_atoms:
            return False
        chosen_indices = chosen_atoms[indices_key]
        if not required.issubset(chosen_indices):
            return False
    return True


def try_helper_citation(problem: Any,
                        chosen_atoms: dict,
                        sc_kind: str,
                        loop_id: str,
                        branch_idx: Optional[int]) -> Optional[str]:
    """Look up a Tier-3 helper that discharges this obligation.

    Returns: Lean proof body string (everything after `:= by\\n  `)
    if a matching helper is registered; None otherwise.  None means
    fall through to the generic tactic chain.

    The `chosen_atoms` dict must include `__indices__:<hole_id>`
    keys giving the ORIGINAL atom indices (positions in
    `Problem.atoms[hole_id]`) of the chosen atoms — needed for the
    required-atoms subset check.  `_attach_indices` builds this
    augmented dict from a bare chosen_atoms.
    """
    registry = getattr(problem, "helper_registry", None)
    if registry is None:
        return None
    entry = registry.find(sc_kind, loop_id, branch_idx, chosen_atoms)
    if entry is None:
        return None
    hyp_for = _make_hyp_for(problem, chosen_atoms)
    try:
        return entry.cite(chosen_atoms, hyp_for)
    except Exception as e:
        # A `cite` failure is a registry bug — DON'T swallow
        # silently.  Raise so the caller / tests surface it.
        raise RuntimeError(
            f"Helper {entry.helper_name!r} cite failed: "
            f"{type(e).__name__}: {e}"
        ) from e


def _attach_indices(problem: Any, chosen_atoms: dict) -> dict:
    """Augment `chosen_atoms` with `__indices__:<hole_id>` entries.

    For each τ-hole, looks up each chosen atom string in
    `Problem.atoms[hole_id]` and records its original index.
    Returns a NEW dict (doesn't mutate input).

    Atom strings absent from the master list (shouldn't happen
    under normal flow) get index -1 — they won't satisfy any
    required-atom set, so the entry won't match.
    """
    out = dict(chosen_atoms)
    for hole_id, chosen in chosen_atoms.items():
        if not hole_id.startswith("tau@"):
            continue
        if not isinstance(chosen, list):
            continue
        master = problem.atoms.get(hole_id, [])
        # Atoms can be strings OR dicts (for transition atoms).
        # For τ holes they're always strings.
        master_to_idx = {a: i for i, a in enumerate(master)
                         if isinstance(a, str)}
        indices = frozenset(
            master_to_idx.get(a, -1) for a in chosen
            if isinstance(a, str)
        )
        out[f"__indices__:{hole_id}"] = indices
    return out


def _make_hyp_for(problem: Any, chosen_atoms: dict) -> HypForFn:
    """Build a `hyp_for(hole_id, orig_idx) → hyp_name` lookup.

    Translates "the atom at index X in Problem.atoms[hole_id]" to
    the hypothesis name the translator emits for that atom (e.g.,
    `h_tau_3` if it's the 4th selected atom in the chosen subset).

    The translator's convention: for a τ-hole with chosen subset
    [a, b, c, ...], it emits binders `(h_tau_0 : <a>) (h_tau_1 :
    <b>) ...` in subset order.  So:

      hyp_for(hole_id, orig_idx) =
        "h_tau_<position-of-master[orig_idx]-in-chosen[hole_id]>"

    Other holes (g@*, phi@*, s@*) currently aren't bound under
    `h_<name>_<i>` patterns; if a helper needs to cite them it
    must use the underlying var names directly.
    """
    def hyp_for(hole_id: str, orig_idx: int,
                *, role: str = "local",
                chain_k: Optional[int] = None) -> str:
        master = problem.atoms.get(hole_id, [])
        if orig_idx < 0 or orig_idx >= len(master):
            raise ValueError(
                f"hyp_for: atom index {orig_idx} out of range for "
                f"{hole_id!r} (len {len(master)})"
            )
        target = master[orig_idx]
        chosen = chosen_atoms.get(hole_id, [])
        for pos, atom in enumerate(chosen):
            if atom == target:
                if not hole_id.startswith("tau@"):
                    raise NotImplementedError(
                        f"hyp_for for non-τ hole {hole_id!r} not implemented"
                    )
                if role == "local":
                    if chain_k is not None:
                        raise ValueError(
                            f"hyp_for: chain_k={chain_k} given with "
                            f"role='local' — chain_k is only valid with "
                            f"role='chain'"
                        )
                    return f"h_tau_{pos}"
                if role == "enc":
                    if chain_k is not None:
                        raise ValueError(
                            f"hyp_for: chain_k={chain_k} given with "
                            f"role='enc' — chain_k is only valid with "
                            f"role='chain'"
                        )
                    return f"h_enc_tau_{pos}"
                if role == "chain":
                    if chain_k is None:
                        raise ValueError(
                            f"hyp_for: role='chain' requires chain_k"
                        )
                    # hole_id is `tau@<lid>`; strip prefix to get lid.
                    lid = hole_id[len("tau@"):]
                    return f"h_i{chain_k}_{lid}_tau_{pos}"
                raise ValueError(
                    f"hyp_for: unknown role={role!r} (expected "
                    f"'local', 'enc', or 'chain')"
                )
        raise ValueError(
            f"hyp_for: atom index {orig_idx} of {hole_id!r} not in "
            f"chosen subset — registry's required_atoms check should "
            f"have prevented this"
        )
    return hyp_for
