"""Expansion — walk the template, assign hole IDs, collect hole metadata.

The `expand` pass corresponds to POPL'10 §3.2's `Expand` function: walk
the flowgraph template and introduce fresh unknown symbols for each
hole.  In our IR representation we don't introduce new node types —
we just assign IDs to the existing nodes and return a list of `Hole`
records that downstream constraint generation iterates over.

Naming convention (filled by `expand`):

  - `tau@L0`, `phi@L0`, `g@L0`   — invariant / ranking / guard of loop L0
  - `s@B0`        for n=1        — single transition of SB block B0
  - `s@B0.k`      for k ∈ 0..n-1 — branch k of SB block B0 with n>1
  - `g@B0.k`      for k ∈ 0..n-1 — *explicit* guard of branch k (Phase
                                   3.I: independent guards per branch,
                                   coverage `⋁ g_i ≡ true` asserted as
                                   well-formedness in constraints.py)
  - `phi@PROC`                   — procedure-level ranking function;
                                   allocated only if `problem.atoms`
                                   contains any `_recur` transition
                                   atom (Phase 3.E.2)
  - `s_recur@R0`                 — recursive-call transition (Phase 3+)
"""
from __future__ import annotations
from dataclasses import dataclass

from .ir import SB, Loop, Seq, Recur, Template, Problem


@dataclass
class Hole:
    """A named unknown in the expanded scaffold."""
    id: str                      # e.g. "tau@L0" or "s@B0.1"
    kind: str                    # "tau" | "phi" | "g" | "s"
    owner: str                   # block ID this hole belongs to ("L0", "B0", …)


@dataclass
class ExpandedScaffold:
    """The result of expansion: the same template (now with IDs assigned)
    plus a flat list of holes for constraint generation."""
    template: Template
    holes: list[Hole]

    def holes_by_id(self) -> dict[str, Hole]:
        return {h.id: h for h in self.holes}


def expand(problem: Problem) -> ExpandedScaffold:
    """Assign hole IDs to template nodes (in-place) and return holes."""
    counters = {"L": 0, "B": 0, "R": 0}
    holes: list[Hole] = []

    def fresh(prefix: str) -> str:
        n = counters[prefix]
        counters[prefix] += 1
        return f"{prefix}{n}"

    def walk(node: Template) -> None:
        if isinstance(node, SB):
            if node.n < 1:
                raise ValueError(f"SB(n={node.n}): n must be ≥ 1")
            bid = fresh("B")
            node.block_id = bid
            if node.n == 1:
                # Phase 1.A flat naming.
                holes.append(Hole(id=f"s@{bid}", kind="s", owner=bid))
            else:
                # Phase 3.I: n branches, n *explicit* guards (no implicit
                # "else").  Each branch is an independent (guard, stmt)
                # pair drawn from Dgrd × Dexp.  Disjointedness of guards
                # is not enforced (POPL'10 §3.4 explicitly notes it is
                # not required for correctness); coverage `⋁ g_i ≡ true`
                # *is* enforced as a separate well-formedness constraint
                # in `constraints.py` so synthesized programs are total.
                for k in range(node.n):
                    holes.append(Hole(id=f"s@{bid}.{k}", kind="s", owner=bid))
                for k in range(node.n):
                    holes.append(Hole(id=f"g@{bid}.{k}", kind="g", owner=bid))

        elif isinstance(node, Loop):
            lid = fresh("L")
            node.loop_id = lid
            holes.append(Hole(id=f"tau@{lid}", kind="tau", owner=lid))
            holes.append(Hole(id=f"phi@{lid}", kind="phi", owner=lid))
            holes.append(Hole(id=f"g@{lid}",   kind="g",   owner=lid))
            # COST_INVS §1 — resource-bound invariant hole, allocated
            # only when the problem has a cost_target set.  Candidates
            # come from atoms[f"cost@{lid}"]; same numeric-hole shape
            # as phi.  No allocation when cost_target is None keeps
            # all existing benchmarks unaffected.
            if problem.cost_target is not None:
                holes.append(Hole(id=f"cost@{lid}",
                                  kind="cost", owner=lid))
            walk(node.body)

        elif isinstance(node, Seq):
            walk(node.left)
            walk(node.right)

        elif isinstance(node, Recur):
            rid = fresh("R")
            node.recur_id = rid
            # The hole's atom must be `_recur`-shaped — encoded in
            # constraints.py via _recur_body.
            holes.append(Hole(id=f"s@{rid}", kind="s", owner=rid))

        else:
            raise TypeError(f"unknown template node: {type(node).__name__}")

    walk(problem.template)

    # K.B.IMPL-1 (R1): validate break-atom placement.  `_break: True`
    # in a transition atom is only meaningful inside a Loop body;
    # outside, raise so typos / misplaced markers surface early.
    # Also reject unknown leading-underscore keys to catch
    # `_braek`-style typos.
    _validate_break_atoms(problem)

    # Phase 3.E.2: if any SB-branch atom is a recursive call, the
    # synthesizer needs a procedure-level ranking function to rule out
    # non-terminating choices.  Allocate a single `phi@PROC` hole; the
    # user supplies candidates in `problem.atoms["phi@PROC"]`.
    if _has_recur_atom(problem):
        holes.append(Hole(id="phi@PROC", kind="phi", owner="PROC"))

    return ExpandedScaffold(template=problem.template, holes=holes)


# K.B.IMPL-1: known leading-underscore atom-dict keys.  Atoms may use
# these reserved keys as flags.  Any other `_*` key in a transition
# atom raises (catches typos like `_braek`, `_recur_`).
_RESERVED_ATOM_FLAGS = frozenset({
    "_recur",   # Phase 3.E recursive-call marker.
    "_break",   # K.B.IMPL-1 break marker.
    # _recur carries metadata in sibling keys; document them too so
    # they aren't rejected as unknowns.
    "args",     # _recur sibling.
    "ret",      # _recur sibling.
})


def _validate_break_atoms(problem: Problem) -> None:
    """Walk the template, identify SBs INSIDE a Loop body, then check
    every transition atom in `problem.atoms`:

      - `_break: True` is only allowed when the owning SB is inside
        a Loop body.  Outside (top-level SB or in a chain pre-Loop /
        post-Loop SB), raise.
      - Any unknown `_<key>` in a transition atom raises (catches
        typos in flag names).

    Mutates nothing; raises ValueError on the first violation."""
    # Step 1: collect block_ids that are INSIDE a Loop body.
    inside_loop_blocks: set[str] = set()

    def collect(node: Template, inside: bool) -> None:
        if isinstance(node, SB):
            if inside and node.block_id is not None:
                inside_loop_blocks.add(node.block_id)
        elif isinstance(node, Loop):
            collect(node.body, True)
        elif isinstance(node, Seq):
            collect(node.left,  inside)
            collect(node.right, inside)
        # Recur has no children to walk.

    collect(problem.template, False)

    # Step 2: walk every atom in problem.atoms, validate.
    for hole_id, atom_list in problem.atoms.items():
        # Only s@... holes are transition atoms.
        if not hole_id.startswith("s@"):
            continue
        # Hole id can be `s@B0` (single-branch) or `s@B0.k` (branched).
        # Extract the owning block id.
        owner = hole_id.removeprefix("s@").split(".", 1)[0]
        for atom in atom_list:
            # Atoms can be dict (parallel) or list[dict] (SSA-sequential).
            atom_dicts = atom if isinstance(atom, list) else [atom]
            for d in atom_dicts:
                if not isinstance(d, dict):
                    continue
                for k in d.keys():
                    if k.startswith("_"):
                        if k not in _RESERVED_ATOM_FLAGS:
                            raise ValueError(
                                f"atom hole {hole_id!r}: unknown reserved "
                                f"key {k!r}.  Known flags: "
                                f"{sorted(_RESERVED_ATOM_FLAGS)}.")
                if d.get("_break") is True:
                    # owner must be a block-id inside a Loop.
                    # (Owner could be a recur-id R... — those aren't
                    # blocks; reject.)
                    if not owner.startswith("B") or owner not in inside_loop_blocks:
                        raise ValueError(
                            f"atom hole {hole_id!r}: _break: True is "
                            f"only valid inside a Loop body's SB. "
                            f"Owner {owner!r} is not inside a Loop.")

        # K.B.IMPL-2 (simplifying restriction): per hole, EITHER all
        # candidates carry `_break: True` OR none do.  No mixing.
        # This lets IMPL-2's emit_loop_body decide on a per-BRANCH
        # basis (not per-candidate) whether to skip the inductive +
        # ranking-decrease constraints.
        candidate_has_break = []
        for atom in atom_list:
            atom_dicts = atom if isinstance(atom, list) else [atom]
            has_break = any(
                isinstance(d, dict) and d.get("_break") is True
                for d in atom_dicts
            )
            candidate_has_break.append(has_break)
        if any(candidate_has_break) and not all(candidate_has_break):
            raise ValueError(
                f"atom hole {hole_id!r}: candidates mix break-marked "
                f"and non-break atoms (have_break = "
                f"{candidate_has_break}).  Per K.B.IMPL-2, every "
                f"candidate of a given hole must be either ALL break "
                f"or NONE break.  Split into two SB branches if you "
                f"need both options.")


def _has_recur_atom(problem: Problem) -> bool:
    """Detect any `_recur` transition atom in the user-supplied atom set."""
    for atom_list in problem.atoms.values():
        for atom in atom_list:
            if isinstance(atom, dict) and atom.get("_recur"):
                return True
    return False
