"""Constraint generator.

Walks the expanded scaffold and emits the synthesis condition
`sc = SafetyCond ∧ WellFormCond ∧ RankCond` (POPL'10 §3.3–3.5).
Phase 1.A encoding: each hole picks one atom from a finite candidate
set, mediated by single-hot Boolean indicator variables.

Encoding shape:

    pre_binding[v]   → Z3 Int for v at "before" the transition
    post_binding[v]  → Z3 Int for v at "after" the transition

    indicators[hole_id]  → list[BoolRef], one per candidate atom
    PbEq(…) == 1         → single-hot per hole

Predicate holes (`tau`, `g`) dispatch via `Or(b_k ∧ atom_k)`.
Numeric holes (`phi`) dispatch via a nested If chain.

Transition holes (`s`) accept two atom formats:

  * **Parallel** (`dict[str, str]`).  Every RHS is parsed against the
    pre-state binding.  Vars not in the dict are preserved (x' = x).
    Equivalent to POPL'10 §3.1's "expressions are over input variables
    only" rule.

  * **SSA / sequential** (`list[dict[str, str]]`).  Each entry is a
    single-key `{var: rhs}` mapping; later entries may reference
    earlier LHS variables, picking up their freshly-assigned value.
    Equivalent to PLDI'11's symbolic-execution version-map rule.
    Implemented by *symbolic substitution* at constraint-generation
    time: we maintain a Python-level binding that gets updated after
    each assignment, so the SSA fresh names never appear in the Z3
    formula — each post variable is bound by a single equation
    referencing only pre-state values (the intermediates are inlined
    away).  No extra existentials needed.

The variable list on each `TS()` (i.e. the keys of the atom dict or
the union of keys in the SSA list) fixes which output variables get
assigned, so POPL'10's `valid(s_i)` constraint is structurally
enforced and need not be asserted.

The decrease constraint uses `ϕ(unprimed) > ϕ(primed)` directly — no
ranking-tracker variable `r` is needed (the early Phase 0 spike found
that POPL'10's tracker is only a workaround for verifiers that can't
double-substitute a single unknown; Z3 can).
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Mapping

import z3

from .ir import SB, Loop, Seq, Recur, Problem, Template
from .expand import ExpandedScaffold
from .expr import parse_expr


Binding = Mapping[str, z3.ExprRef]
PredFn  = Callable[[Binding], z3.ExprRef]


@dataclass
class AtomRef:
    """A single τ-atom reference inside a safety body.

    Used by the CEGIS smart blocker (Phase 3.X) to identify *culprit*
    atoms — atoms that are currently selected and whose value at the
    counter-example violates the safety obligation.  Blocking on
    culprits is much stronger than blocking the entire indicator
    assignment, since it rules out an entire face of the τ cube.
    """
    hole_id: str
    atom_idx: int                # index into problem.atoms[hole_id]
    z3_atom: z3.ExprRef          # the atom Z3-translated at its binding
    is_consequent: bool          # True if atom is in the implication's RHS


@dataclass
class SafetyConstraint:
    """One safety / ranking constraint, with its body NOT wrapped in ForAll.

    `body` references both the indicator booleans (free at the top level)
    and the program variables in `quantified_vars`.  The intended meaning
    is `∀ quantified_vars . body`; the CEGIS solver in `solver.py` checks
    validity by substituting indicator values into `body`, negating, and
    asking Z3 whether the negation has a model (counter-example).

    `atom_refs` lists the τ atoms appearing in this body, tagged with
    their position (antecedent / consequent).  Used by the smart
    blocker — see `solver.py`.
    """
    body: z3.ExprRef
    quantified_vars: list[z3.ExprRef]
    atom_refs: list[AtomRef]
    kind: str = "safety"     # "safety" | "ranking-lb" | "ranking-decrease"
                             # | "cost-lb" | "cost-decrement" | "cost-budget"
                             # (COST_INVS §1)
    loop_id: str | None = None   # loop this constraint belongs to (for
                                 # ranking-* and safety; None for procedure
                                 # ranking and constraints not tied to a loop)
    branch_idx: int | None = None   # branch index for SB(n>1) loop bodies
                                    # (None for SB(n=1) or non-loop-body
                                    # constraints).  The Lean translator
                                    # uses this to pick the branch's
                                    # guard/trans atoms.


@dataclass
class ConstraintSystem:
    """All output of constraint generation, packaged for the CEGIS solver.

    `well_form` is satisfiable by Z3 directly (it constrains only the
    Boolean indicator variables).  `safety` is the list of
    universally-quantified validity obligations; the solver checks them
    one-by-one via the CEGIS pattern.
    """
    well_form: list[z3.ExprRef]
    safety:    list[SafetyConstraint]
    axioms:    list[z3.ExprRef]                 # universally-true premises (Phase 3.D)
    indicators: dict[str, list[z3.BoolRef]]    # hole_id → indicator vars
    pre_binding:  dict[str, z3.ExprRef]
    post_binding: dict[str, z3.ExprRef]
    hole_sizes: dict[str, int]                  # hole_id → atom count


def generate(problem: Problem, scaffold: ExpandedScaffold) -> ConstraintSystem:
    """Build the Z3 constraint system for `problem` over `scaffold`."""
    # ── Z3 variables: one pre and one post per program var. ──────────
    pre_binding:  dict[str, z3.ExprRef] = {
        v.name: _make_z3_var(v.name, v.type)         for v in problem.all_vars
    }
    post_binding: dict[str, z3.ExprRef] = {
        v.name: _make_z3_var(f"{v.name}_p", v.type)  for v in problem.all_vars
    }
    all_vars_z3 = list(pre_binding.values()) + list(post_binding.values())
    pre_vars_z3 = list(pre_binding.values())

    # ── Uninterpreted-function registry (Phase 3.D). ─────────────────
    uf: dict[str, z3.FuncDeclRef] = {}
    for fn_name, arg_types, ret_type in problem.uninterpreted:
        arg_sorts = [_type_sort(t) for t in arg_types]
        ret_sort  = _type_sort(ret_type)
        uf[fn_name] = z3.Function(fn_name, *arg_sorts, ret_sort)

    # ── Indicator booleans + single-hot well-formedness. ─────────────
    indicators: dict[str, list[z3.BoolRef]] = {}
    hole_sizes: dict[str, int] = {}
    well_form:  list[z3.ExprRef] = []
    safety:     list[SafetyConstraint] = []

    for hole in scaffold.holes:
        if hole.id not in problem.atoms:
            raise ValueError(
                f"Problem.atoms missing key {hole.id!r}. "
                f"Holes in scaffold: {[h.id for h in scaffold.holes]}. "
                f"Keys provided: {list(problem.atoms)}."
            )
        n = len(problem.atoms[hole.id])
        if n == 0:
            raise ValueError(f"Empty atom list for hole {hole.id!r}.")
        bs = [z3.Bool(f"b__{hole.id}__{k}") for k in range(n)]
        indicators[hole.id] = bs
        hole_sizes[hole.id] = n

        # Well-formedness:
        #   - tau holes are *conjunctive* (Phase 2 / plan §5.6 phase 1.B):
        #     each indicator independently selects an atom into the
        #     conjunction.  Empty subset → τ = True (typically too weak,
        #     so unsat — but allowed by the encoding).
        #   - All other holes are single-hot: exactly one atom chosen.
        if hole.kind != "tau":
            well_form.append(z3.PbEq([(b, 1) for b in bs], 1))

    # ── Hole instantiation helpers (closures over the tables). ───────
    # `current_refs` is a per-constraint accumulator: each safety
    # constraint resets it, then every call to tau_at appends the
    # τ-atom references that appear in this constraint.  When the
    # constraint is finalized, we capture the list into the
    # SafetyConstraint.atom_refs field.
    current_refs: list[AtomRef] = []

    def tau_at(loop_id: str, binding: Binding,
               is_consequent: bool) -> z3.ExprRef:
        hid = f"tau@{loop_id}"
        atoms = problem.atoms[hid]
        bs = indicators[hid]
        parts = []
        for k, (b, atom_str) in enumerate(zip(bs, atoms)):
            z3_a = parse_expr(atom_str, binding, uf)
            current_refs.append(AtomRef(
                hole_id=hid, atom_idx=k,
                z3_atom=z3_a, is_consequent=is_consequent,
            ))
            parts.append(z3.Implies(b, z3_a))
        return z3.And(parts)

    def g_at(loop_id: str, binding: Binding) -> z3.ExprRef:
        return _pred_hole(problem, indicators, f"g@{loop_id}", binding, uf)

    def phi_at(loop_id: str, binding: Binding) -> z3.ExprRef:
        return _term_hole(problem, indicators, f"phi@{loop_id}", binding, uf)

    # COST_INVS §1 — cost@L hole at a state binding.  None-safe:
    # returns None if the problem has no cost_target (no cost@*
    # holes allocated).  Callers check before emitting cost
    # obligations.
    def cost_at(loop_id: str, binding: Binding) -> z3.ExprRef | None:
        hid = f"cost@{loop_id}"
        if hid not in indicators:
            return None
        return _term_hole(problem, indicators, hid, binding, uf)

    def s_at(block_id: str,
             pre_b: Binding, post_b: Binding,
             branch: int | None = None) -> z3.ExprRef:
        hid = (f"s@{block_id}.{branch}" if branch is not None
               else f"s@{block_id}")
        return _trans_hole(problem, indicators, hid, pre_b, post_b, uf)

    has_phi_proc = "phi@PROC" in indicators

    def phi_proc_at(binding: Binding) -> z3.ExprRef:
        """Phase 3.E.2 procedure-level ranking function, evaluated
        under a binding restricted to procedure inputs."""
        return _term_hole(problem, indicators, "phi@PROC", binding, uf)

    def branch_paths(sb_node, pre_b: Binding, post_b: Binding):
        """Yield `(guard_z3 | None, transition_z3)` per branch of `sb_node`.

        Phase 3.I — independent guards per branch.  SB(n=1) yields one
        pair `(None, s@B…)` (the `None` signals "no guard"; the caller
        should omit it from the implication antecedent — an explicit
        `True` perturbs Z3's NRA heuristics, see lesson #5).  SB(n=k>1)
        yields k pairs, each `(g_i, s_i)` where the guards are
        *independent* — orthogonality is NOT enforced (POPL'10 §3.4
        notes it isn't required for correctness).  Coverage
        `⋁ g_i ≡ true` is asserted separately as well-formedness so
        synthesized programs are total.
        """
        bid = sb_node.block_id
        n = sb_node.n
        if n == 1:
            return [(None, s_at(bid, pre_b, post_b))]
        pairs = []
        for k in range(n):
            g_k = _pred_hole(problem, indicators, f"g@{bid}.{k}", pre_b, uf)
            s_k = s_at(bid, pre_b, post_b, branch=k)
            pairs.append((g_k, s_k))
        return pairs

    def branch_guards_only(sb_node, pre_b: Binding):
        """Return the list of branch guards at `pre_b` (no transitions).
        Used to build coverage constraints."""
        bid = sb_node.block_id
        return [_pred_hole(problem, indicators, f"g@{bid}.{k}", pre_b, uf)
                for k in range(sb_node.n)]

    # ── Pre/postcondition functions. ─────────────────────────────────
    Fpre:  PredFn = lambda b: parse_expr(problem.pre,  b, uf)
    Fpost: PredFn = lambda b: parse_expr(problem.post, b, uf)

    # ── Axioms (Phase 3.D).  Parsed once against the program-var pre-
    # binding extended with no extra vars — quantifiers in axiom bodies
    # open their own scopes via lambdas.  Axioms are universally-true
    # premises that the CEGIS verifier always includes.
    axioms_z3: list[z3.ExprRef] = [
        parse_expr(ax_str, pre_binding, uf) for ax_str in problem.axioms
    ]

    # ── Walk the linearized template, emitting safety + progress. ────
    #
    # `commit(body, vars, kind)` captures the τ atom-refs that
    # accumulated in `current_refs` while building `body` into the new
    # SafetyConstraint, then clears the accumulator for the next.
    def commit(body, vars, kind, loop_id: str | None = None,
               branch_idx: int | None = None):
        safety.append(SafetyConstraint(
            body=body,
            quantified_vars=vars,
            atom_refs=current_refs.copy(),
            kind=kind,
            loop_id=loop_id,
            branch_idx=branch_idx,
        ))
        current_refs.clear()

    Fpre_fn:  PredFn = lambda b: parse_expr(problem.pre,  b, uf)

    # Global procedure ranking lower bound (Phase 3.E.2).
    if has_phi_proc:
        body = z3.Implies(
            Fpre_fn(pre_binding),
            phi_proc_at(pre_binding) >= 0,
        )
        commit(body, pre_vars_z3, "ranking-proc-lb")

    # ── Bundled template walk (recursive — Phase 3.K). ──────────────
    #
    # `walk_template(t, pre_state, post_state, pre_fn, post_fn)` emits
    # the safety/ranking obligations for a (sub-)template operating
    # from `pre_state` to `post_state`.  `pre_fn(b)` is the formula
    # known at the entry state; `post_fn(b)` is the formula required
    # at the exit state.
    #
    # Bundling spans across Loops: the bundle's antecedent is always
    # `pre_fn(pre_state) ∧ ⋀ items-so-far`, where each item contributes
    # either a transition (SB / Recur) or an abstract transition (Loop:
    # τ_inner ∧ ¬g_inner at the Loop's exit state, plus frame equations
    # for vars not in the Loop body's modified set).  This is essential
    # for nested loops — the outer ranking decrease needs to relate
    # ϕ_outer(body_in) to ϕ_outer(body_out) across an inner Loop, which
    # requires preserving non-modified vars through the abstraction.
    #
    # At each Loop checkpoint we emit two kinds of obligation:
    #   1. Entry: bundle-so-far ⇒ τ_loop(state_at_loop_in).
    #   2. Inner body: inductive + LB + decrease (SB-body fast path
    #      directly, or Phase 3.K recursive walk_template for non-SB
    #      bodies — body uses fresh body_in / body_out bindings and a
    #      post_fn that conjoins τ_loop with the loop's ϕ-decrease).
    # At the end we emit:
    #   3. Final bundle: bundle-so-far ⇒ post_fn(post_state).
    #   4. Coverage and per-Recur decreases (per multi-branch SB / per
    #      Recur, with the full chain-to-that-item antecedent).
    def walk_template(template: Template,
                      pre_state:  Binding,
                      post_state: Binding,
                      pre_fn:     PredFn,
                      post_fn:    PredFn,
                      enclosing_loop_id: str | None = None) -> None:
        """Walk a template chain.  When `enclosing_loop_id` is set,
        ALSO emit a cost-decrement constraint for that loop using
        the body's state chain (COST_INVS §1.5 nested-loop case).

        Per-item body costs:
          SB(n=k)      → 1 per branch (per-path unit cost).
          Loop(inner)  → cost@L_inner(item_entry_state).
          Recur        → deferred (cost@PROC future slice).
        """
        items = _linearize(template)
        n_items = len(items)

        # Per-walk state chain.  states_local[0] = pre_state, [N] =
        # post_state, others fresh.
        states_local: list[dict[str, z3.ExprRef]] = [pre_state]
        for _ in range(1, n_items):
            sid = _next_state_id()
            states_local.append({
                v.name: _make_z3_var(f"{v.name}__state_{sid}", v.type)
                for v in problem.all_vars
            })
        states_local.append(post_state)
        all_vars_local = [v for s in states_local for v in s.values()]

        # chain_paths: Cartesian per-item paths through items[start..end).
        # Loops contribute one abstract transition each (no Cartesian
        # split — the Loop's effect is captured by τ + ¬g + frame_eqs
        # regardless of which τ-subset / g-atom is selected, since the
        # indicators thread through tau_at / g_at).
        def chain_paths_local(start: int, end: int):
            from itertools import product as _product
            per_item: list[list] = []
            # Snapshot current_refs BEFORE per_item construction so we
            # can capture only the refs added by Loop tau_at calls
            # below.  These refs must be re-registered per yielded
            # path — otherwise the FIRST commit captures+clears them
            # and subsequent paths' constraints get empty atom_refs.
            # That breaks `_extract_loop_id` (the helper short-circuit
            # gates on it), so e.g. sc14 of bench_max_matching_recur
            # silently lost its loop_id binding and the helper never
            # fired for the identity-branch Cartesian path.
            refs_before = list(current_refs)
            for k in range(start, end):
                it = items[k]
                it_in, it_out = states_local[k], states_local[k + 1]
                if isinstance(it, SB):
                    per_item.append(branch_paths(it, it_in, it_out))
                elif isinstance(it, Recur):
                    trans = _trans_hole(problem, indicators,
                                        f"s@{it.recur_id}",
                                        it_in, it_out, uf)
                    per_item.append([(None, trans)])
                elif isinstance(it, Loop):
                    lid_in = it.loop_id
                    tau_out = tau_at(lid_in, it_out, is_consequent=False)
                    modified = _modified_vars_of_template(it.body, problem)
                    frame_eqs = [
                        it_out[v.name] == it_in[v.name]
                        for v in problem.all_vars
                        if v.name not in modified
                    ]
                    # K.D.IMPL — if the Loop body has a break branch,
                    # the exit can have g_loop true (early exit), so we
                    # cannot assume ¬g_out.  τ alone (plus frame eqs)
                    # is what we know about the exit state.
                    if _has_break_branch(it.body, problem):
                        abstract_parts = [tau_out, *frame_eqs]
                    else:
                        not_g_out = z3.Not(g_at(lid_in, it_out))
                        abstract_parts = [tau_out, not_g_out, *frame_eqs]
                    abstract = (z3.And(*abstract_parts)
                                if len(abstract_parts) > 1
                                else abstract_parts[0])
                    per_item.append([(None, abstract)])
                else:
                    raise NotImplementedError(
                        f"Item type {type(it).__name__} cannot appear "
                        "inside a bundled chain."
                    )
            # Loop-tau refs accumulated during per_item build.
            refs_added_by_chain = current_refs[len(refs_before):]
            if not per_item:
                yield [], []
                return
            for combo in _product(*per_item):
                # Restore the chain's tau refs so each commit sees
                # them (commit clears current_refs after capture).
                current_refs[:] = refs_before + list(refs_added_by_chain)
                guards  = [g for g, _ in combo if g is not None]
                transes = [t for _, t in combo]
                yield guards, transes

        def emit_bundle_to(target_fn: PredFn,
                           target_state: dict, end_idx: int,
                           loop_id: str | None = None,
                           kind: str = "safety-bundle-post"):
            # Chain-bundle safety constraints have a DIFFERENT
            # structure than loop-inductive safety: they span
            # multiple program states (init + frame_eqs + loop
            # abstract transition + skip), with the loop's τ
            # appearing as an opaque transition rather than a
            # `pre ⇒ post` shape.  Two sub-shapes:
            #   - "safety-bundle-entry": pre-loop bundle whose
            #     target is the loop's τ.  Shape: Fpre ∧ <chain
            #     prefix> ⇒ τ_loop(target_state).
            #   - "safety-bundle-post": post-loop bundle whose
            #     target is Fpost.  Shape: Fpre ∧ <chain prefix>
            #     ∧ τ_exit ∧ ¬g ∧ frame_eqs ∧ <chain suffix>
            #     ⇒ Fpost.
            # They use DIFFERENT Lean translators; see
            # `synth.lean_backend.translate`.
            if loop_id is None:
                loops_in_segment = [
                    items[k].loop_id for k in range(end_idx)
                    if isinstance(items[k], Loop)
                ]
                if len(loops_in_segment) == 1:
                    loop_id = loops_in_segment[0]
            for guards, transes in chain_paths_local(0, end_idx):
                ant_parts = [pre_fn(states_local[0])]
                ant_parts.extend(guards)
                ant_parts.extend(transes)
                ant = (z3.And(*ant_parts) if len(ant_parts) > 1
                       else ant_parts[0])
                body = z3.Implies(ant, target_fn(target_state))
                commit(body, all_vars_local, kind,
                       loop_id=loop_id)

        # ── Centralized constraint-emission helpers ──────────────
        #
        # Lesson #27/#29: every well-formedness, coverage, and
        # ranking-decrease constraint that applies to an IR
        # construct (SB / Loop / Recur) lives in one helper.  Every
        # site that processes that construct calls the helper with
        # context-specific arguments.  Adding a new constraint kind
        # for a construct is a one-place change; failing to emit a
        # constraint at one of N contexts is structurally
        # impossible.

        def _and_path(parts: list) -> z3.ExprRef:
            if not parts:
                return z3.BoolVal(True)
            if len(parts) == 1:
                return parts[0]
            return z3.And(*parts)

        def emit_recur_decrease(hole_id: str,
                                atoms,
                                in_b: Binding,
                                paths_to_in_b,
                                branch_guard=None) -> None:
            """Per-procedure decrease for every `_recur` atom in
            `atoms` (= `problem.atoms[hole_id]`).

              `path ∧ branch_guard ∧ b_atom ∧ Fpre(args)
                ⇒ ϕ_proc(in_b) > ϕ_proc(args)`

            Called from `emit_sb_constraints` (per SB branch with
            its branch guard) and from the Recur-item case in the
            walk_template main loop (branch_guard=None).
            """
            if not has_phi_proc:
                return
            # `paths_to_in_b` may be a generator (`_paths_to_state(k)`);
            # the inner per-atom loop iterates it, so materialize once
            # at the top.  Otherwise the second atom onwards sees an
            # exhausted generator and no decrease constraint is
            # emitted for it — a real soundness bug if the first atom
            # is sound but a later one is degenerate.
            paths_list = list(paths_to_in_b)
            bs = indicators[hole_id]
            for atom_idx, atom in enumerate(atoms):
                if not (isinstance(atom, dict)
                        and atom.get("_recur")):
                    continue
                b_atom = bs[atom_idx]

                args_spec = atom.get("args", {})
                args_evaluated: dict[str, z3.ExprRef] = {}
                for v in problem.inputs:
                    if v.name in args_spec:
                        args_evaluated[v.name] = parse_expr(
                            args_spec[v.name], in_b, uf)
                    else:
                        args_evaluated[v.name] = in_b[v.name]
                fpre_args = parse_expr(problem.pre,
                                       args_evaluated, uf)
                decrease = (phi_proc_at(in_b)
                            > phi_proc_at(args_evaluated))

                for path in paths_list:
                    ant_parts = list(path)
                    if branch_guard is not None:
                        ant_parts.append(branch_guard)
                    ant_parts.append(b_atom)
                    ant_parts.append(fpre_args)
                    commit(z3.Implies(_and_path(ant_parts), decrease),
                           all_vars_local, "ranking-proc-decrease")

        def emit_sb_constraints(sb: SB,
                                in_b: Binding,
                                paths_to_in_b,
                                enclosing_loop_id: str | None = None) -> None:
            """All SB-context constraints: coverage (if n > 1) and
            per-branch per-procedure decrease (delegating to
            `emit_recur_decrease`).

            `enclosing_loop_id`: when the SB is the body of a Loop,
            pass the loop's id so the Lean translator can locate
            the SB inside the template (it walks loops, not SBs,
            so it needs the loop_id to descend).
            """
            paths_list = list(paths_to_in_b)

            if sb.n > 1:
                coverage = z3.Or(branch_guards_only(sb, in_b))
                for path in paths_list:
                    commit(z3.Implies(_and_path(path), coverage),
                           all_vars_local, "coverage",
                           loop_id=enclosing_loop_id)

            for branch_k in range(sb.n):
                if sb.n == 1:
                    hole_id = f"s@{sb.block_id}"
                    branch_guard = None
                else:
                    hole_id = f"s@{sb.block_id}.{branch_k}"
                    branch_guard = _pred_hole(
                        problem, indicators,
                        f"g@{sb.block_id}.{branch_k}", in_b, uf)
                emit_recur_decrease(hole_id,
                                    problem.atoms.get(hole_id, []),
                                    in_b, paths_list,
                                    branch_guard=branch_guard)

        def _paths_to_state(k: int):
            """Generator: antecedent-conjunct paths leading to state[k]."""
            for guards, transes in chain_paths_local(0, k):
                path = [pre_fn(states_local[0])]
                path.extend(guards)
                path.extend(transes)
                yield path

        def emit_loop_entry(item: Loop, in_b: Binding, idx: int) -> None:
            """Loop entry: bundle-so-far ⇒ τ_loop(in_b)."""
            lid = item.loop_id
            tau_cons = (lambda b, lid=lid:
                        tau_at(lid, b, is_consequent=True))
            emit_bundle_to(tau_cons, in_b, idx, loop_id=lid,
                           kind="safety-bundle-entry")
            # COST_INVS §1 (C) — cost-budget at loop entry:
            #   Fpre ∧ <chain prefix path> ⇒ cost@L(in_b) ≤ cost_target
            # cost_target is evaluated against the procedure's
            # pre-state (states_local[0]).  Only emitted when
            # cost_target is set AND this loop has a cost@L hole.
            if problem.cost_target is not None:
                cost_entry = cost_at(lid, in_b)
                if cost_entry is not None:
                    cost_target_z3 = parse_expr(
                        problem.cost_target, states_local[0], uf)
                    cost_cons = (lambda b, _ce=cost_entry,
                                 _ct=cost_target_z3:
                                 _ce <= _ct)
                    emit_bundle_to(cost_cons, in_b, idx, loop_id=lid,
                                   kind="cost-budget")

        def fresh_loop_body_bindings(lid: str):
            body_in = {
                v.name: _make_z3_var(
                    f"{v.name}__loopbody_{lid}_in_{_next_state_id()}",
                    v.type)
                for v in problem.all_vars
            }
            body_out = {
                v.name: _make_z3_var(
                    f"{v.name}__loopbody_{lid}_out_{_next_state_id()}",
                    v.type)
                for v in problem.all_vars
            }
            return body_in, body_out

        def emit_loop_body(item: Loop, body_in: Binding,
                           body_out: Binding) -> None:
            """Loop body inductive + Loop ranking-decrease.

            Dispatches on body shape:
              - SB → fast path: per-branch inductive + decrease so
                atom-class enumeration stays narrow.  Also delegates
                SB well-formedness to `emit_sb_constraints`.
              - non-SB → recursive `walk_template` with a `post_fn`
                that conjoins τ_outer with the ϕ_outer-decrease,
                so the sub-walk's bundled safety enforces both
                jointly.
            """
            lid = item.loop_id
            if isinstance(item.body, SB):
                body_vars = (list(body_in.values())
                             + list(body_out.values()))
                outer_pre_path = [
                    tau_at(lid, body_in, is_consequent=False),
                    g_at(lid, body_in),
                ]
                emit_sb_constraints(item.body, body_in,
                                    [outer_pre_path],
                                    enclosing_loop_id=lid)
                # For SB(n>1), branch_paths returns (guard, trans)
                # per branch in order; tag each emitted safety /
                # ranking-decrease constraint with its branch_idx
                # so the Lean translator can pick the right atoms.
                # For SB(n=1) (single branch), branch_idx stays None.
                multi_branch = (item.body.n > 1)
                sb_block = item.body.block_id
                for b_idx, (guard, trans) in enumerate(branch_paths(
                        item.body, body_in, body_out)):
                    # K.B.IMPL-2: identify if this branch is
                    # break-marked.  Per IMPL-1 validation,
                    # all candidates of the hole are uniformly
                    # break OR not — check the first.
                    if multi_branch:
                        s_hole = f"s@{sb_block}.{b_idx}"
                    else:
                        s_hole = f"s@{sb_block}"
                    branch_atoms = problem.atoms.get(s_hole, [])
                    is_break_branch = False
                    if branch_atoms:
                        first = branch_atoms[0]
                        first_dicts = (first if isinstance(first, list)
                                       else [first])
                        is_break_branch = any(
                            isinstance(d, dict) and d.get("_break") is True
                            for d in first_dicts
                        )
                    if is_break_branch:
                        # K.B.IMPL-3 + K.D.IMPL-1/2: emit break-bundle
                        # obligation with consequent depending on the
                        # Loop's context:
                        #   Top-level (no enclosing Loop): Fpost(body_out).
                        #   Nested (inside enclosing Loop): τ_enclosing
                        #     preserved at body_out — the inner break
                        #     exits to the enclosing's body, which still
                        #     must satisfy its invariant.
                        # Chain-with-no-enclosing (e.g., Loop >> SB)
                        # still uses Fpost here; that misses the chain
                        # tail's effect.  K.D.2.a deferred.
                        ant_parts = [
                            Fpre(body_in),
                            tau_at(lid, body_in, is_consequent=False),
                            g_at(lid, body_in),
                        ]
                        if guard is not None:
                            ant_parts.append(guard)
                        ant_parts.append(trans)
                        ant = z3.And(*ant_parts)
                        if enclosing_loop_id is not None:
                            # Nested: emit τ_enclosing at body_out
                            # (the post-break state, which is the
                            # enclosing loop's body's current state).
                            cons = tau_at(enclosing_loop_id, body_out,
                                          is_consequent=True)
                        else:
                            cons = Fpost(body_out)
                        bi = b_idx if multi_branch else None
                        commit(
                            z3.Implies(ant, cons),
                            body_vars,
                            "safety-bundle-post",
                            loop_id=lid, branch_idx=bi,
                        )
                        # Skip τ-preservation, ranking-decrease, and
                        # cost-decrement for break branches.
                        continue
                    # K.D-style Fpre propagation extended to the
                    # SB-body fast path (2026-06-08).  Input-variable
                    # facts are immutable across loop iterations
                    # (inputs are never written), so Fpre at body_in
                    # equals Fpre at the initial state.  Including
                    # Fpre here lets inner constraints rely on input
                    # facts without forcing the user to mirror them
                    # into τ.  Matches what the recursive walk_template
                    # path does (line ~746) and what the Lean
                    # translator emits as h_pre.  Soundness: this is
                    # a WEAKENING of the obligation (more
                    # antecedents = more hypotheses for the implication
                    # = more permissive), so any class previously
                    # accepted stays accepted; some previously-rejected
                    # classes may now be accepted (solution-count
                    # guard catches accidental over-permissiveness).
                    ant_parts = [
                        Fpre(body_in),
                        tau_at(lid, body_in, is_consequent=False),
                        g_at(lid,  body_in),
                    ]
                    if guard is not None:
                        ant_parts.append(guard)
                    ant_parts.append(trans)
                    ant = z3.And(*ant_parts)
                    cons = tau_at(lid, body_out, is_consequent=True)
                    bi = b_idx if multi_branch else None
                    commit(z3.Implies(ant, cons), body_vars, "safety",
                           loop_id=lid, branch_idx=bi)
                    commit(
                        z3.Implies(
                            ant,
                            phi_at(lid, body_in) > phi_at(lid, body_out)),
                        body_vars, "ranking-decrease",
                        loop_id=lid, branch_idx=bi,
                    )
                    # COST_INVS §1 (B) — cost-decrement:
                    #   τ ∧ g ∧ trans ⇒ cost@L(pre) ≥ body_cost + cost@L(post)
                    # First slice: body_cost = 1 for SB(n=1) bodies
                    # (one transition per iteration).  For SB(n>1) we
                    # take the same per-branch unit cost.
                    cost_pre  = cost_at(lid, body_in)
                    cost_post = cost_at(lid, body_out)
                    if cost_pre is not None and cost_post is not None:
                        commit(
                            z3.Implies(
                                ant,
                                cost_pre >= 1 + cost_post),
                            body_vars, "cost-decrement",
                            loop_id=lid, branch_idx=bi,
                        )
            else:
                # K.D.IMPL — propagate Fpre into the recursive walk.
                # Pre-condition facts about input vars are
                # immutable across loop iterations (inputs never
                # change), so Fpre evaluated at body_in is equal
                # to Fpre at the initial state.  Including Fpre
                # in pre_fn lets inner constraints rely on input
                # facts without forcing the user to carry them
                # in outer τ.
                outer_pre_fn = (lambda b, lid=lid:
                                z3.And(
                                    Fpre(b),
                                    tau_at(lid, b, is_consequent=False),
                                    g_at(lid, b)))
                outer_post_fn = (lambda b, lid=lid, bi=body_in:
                                 z3.And(
                                     tau_at(lid, b, is_consequent=True),
                                     phi_at(lid, bi) > phi_at(lid, b)))
                # COST_INVS §1.5: pass enclosing_loop_id so the
                # recursive walk emits the outer Loop's cost-decrement
                # using its body's state chain.
                walk_template(item.body, body_in, body_out,
                              outer_pre_fn, outer_post_fn,
                              enclosing_loop_id=lid)

        def emit_loop_lb(item: Loop, body_in: Binding) -> None:
            """Loop ranking lower bound: τ ⇒ ϕ ≥ 0."""
            lid = item.loop_id
            commit(
                z3.Implies(
                    tau_at(lid, body_in, is_consequent=False),
                    phi_at(lid, body_in) >= 0),
                list(body_in.values()),
                "ranking-lb",
                loop_id=lid,
            )
            # COST_INVS §1 (A) — cost lower bound: τ ⇒ cost@L ≥ 0.
            cost_body = cost_at(lid, body_in)
            if cost_body is not None:
                commit(
                    z3.Implies(
                        tau_at(lid, body_in, is_consequent=False),
                        cost_body >= 0),
                    list(body_in.values()),
                    "cost-lb",
                    loop_id=lid,
                )

        for idx, item in enumerate(items):
            in_b = states_local[idx]
            out_b = states_local[idx + 1]

            if isinstance(item, Loop):
                emit_loop_entry(item, in_b, idx)
                body_in, body_out = fresh_loop_body_bindings(
                    item.loop_id)
                emit_loop_body(item, body_in, body_out)
                emit_loop_lb(item, body_in)

            elif isinstance(item, (SB, Recur)):
                pass  # included in chain via chain_paths.

            elif isinstance(item, Seq):
                raise AssertionError(
                    "linearize() should have flattened Seq nodes"
                )

            else:
                raise TypeError(
                    f"unknown template node: {type(item).__name__}"
                )

        # 3. Final bundle: bundle-so-far ⇒ post_fn(post_state).
        emit_bundle_to(post_fn, states_local[n_items], n_items)

        # 4. Per-construct well-formedness + decrease — Lesson #29
        #    centralization.  Every SB and Recur in the items list
        #    delegates to the central helpers, with the per-context
        #    `_paths_to_state(k)` providing the upstream antecedents.
        for k, it in enumerate(items):
            if isinstance(it, SB):
                emit_sb_constraints(it, states_local[k],
                                    _paths_to_state(k))
            elif isinstance(it, Recur):
                hole_id = f"s@{it.recur_id}"
                emit_recur_decrease(hole_id, problem.atoms[hole_id],
                                    states_local[k],
                                    _paths_to_state(k),
                                    branch_guard=None)

        # 5. COST_INVS §1.5 — nested-loop cost-decrement.  When this
        #    walk is the body of an enclosing Loop with a cost@L
        #    hole, emit the per-path cost-decrement obligation
        #    spanning the body chain.
        if enclosing_loop_id is not None:
            cost_pre_outer  = cost_at(enclosing_loop_id, pre_state)
            cost_post_outer = cost_at(enclosing_loop_id, post_state)
            if cost_pre_outer is not None and cost_post_outer is not None:
                for path_guards, path_transes in chain_paths_local(0, n_items):
                    # Per-item body costs along this path.
                    body_cost: z3.ExprRef = z3.IntVal(0)
                    for k, it in enumerate(items):
                        if isinstance(it, SB):
                            body_cost = body_cost + 1
                        elif isinstance(it, Loop):
                            inner_cost = cost_at(it.loop_id,
                                                 states_local[k])
                            if inner_cost is not None:
                                body_cost = body_cost + inner_cost
                            # If inner has no cost@L hole, it's
                            # treated as 0-cost — caller error.
                        elif isinstance(it, Recur):
                            # Deferred: Recur cost@PROC.  Conservative:
                            # body_cost contribution = 0, but this
                            # under-estimates and may make the
                            # cost-budget unsoundly small.  Future
                            # slice handles this; for now,
                            # benchmarks with Recur inside a
                            # cost-bound Loop body are not supported.
                            pass
                    ant_parts = [pre_fn(pre_state)]
                    ant_parts.extend(path_guards)
                    ant_parts.extend(path_transes)
                    ant = z3.And(*ant_parts)
                    commit(
                        z3.Implies(
                            ant,
                            cost_pre_outer >= body_cost + cost_post_outer),
                        all_vars_local,
                        "cost-decrement",
                        loop_id=enclosing_loop_id,
                    )

    walk_template(problem.template, pre_binding, post_binding,
                  Fpre_fn, Fpost)

    return ConstraintSystem(
        well_form=well_form,
        safety=safety,
        axioms=axioms_z3,
        indicators=indicators,
        pre_binding=pre_binding,
        post_binding=post_binding,
        hole_sizes=hole_sizes,
    )


# ─────────────────────────────────────────────────────────────────────
# Hole dispatch helpers.
# ─────────────────────────────────────────────────────────────────────
def _pred_hole(problem, indicators, hid, binding, uf):
    """Single-hot predicate hole — exactly one atom is in (used for guards)."""
    atoms = problem.atoms[hid]
    bs = indicators[hid]
    return z3.Or([z3.And(b, parse_expr(a, binding, uf))
                  for b, a in zip(bs, atoms)])


def _conj_hole(problem, indicators, hid, binding, uf):
    """Conjunctive hole — any subset of atoms (used for invariants).

    Encoding: τ = ⋀_k (b_k ⇒ atom_k).  Each indicator independently
    selects its atom into the conjunction.  With no well-formedness
    constraint on the indicators, every subset of atoms is a possible
    invariant (including the empty set, which yields τ = True).
    """
    atoms = problem.atoms[hid]
    bs = indicators[hid]
    return z3.And([z3.Implies(b, parse_expr(a, binding, uf))
                   for b, a in zip(bs, atoms)])


def _term_hole(problem, indicators, hid, binding, uf):
    atoms = problem.atoms[hid]
    bs = indicators[hid]
    expr = parse_expr(atoms[-1], binding, uf)
    for k in range(len(atoms) - 2, -1, -1):
        expr = z3.If(bs[k], parse_expr(atoms[k], binding, uf), expr)
    return expr


def _trans_hole(problem, indicators, hid, pre_b, post_b, uf):
    atoms = problem.atoms[hid]
    bs = indicators[hid]
    parts = []
    for b, atom in zip(bs, atoms):
        parts.append(z3.And(b,
            _trans_body(atom, pre_b, post_b, hid, uf, problem)))
    return z3.Or(parts)


# Unique counter for recur-call argument/return Z3 var names.
_recur_counter = [0]


def _next_recur_id() -> str:
    n = _recur_counter[0]
    _recur_counter[0] += 1
    return str(n)


# Unique counter for fresh state-binding suffixes inside nested
# template walks (Phase 3.K).  Module-level so recursive
# walk_template invocations don't collide on names.
_state_counter = [0]


def _next_state_id() -> int:
    n = _state_counter[0]
    _state_counter[0] += 1
    return n


def _trans_body(atom, pre_b, post_b, hid, uf, problem):
    """Build the Z3 formula for one transition atom.

    `atom` is one of:
      - dict[str, str]              : parallel-assignment, RHS over pre values
      - list[dict[str, str]]        : SSA-ordered list of single-key dicts;
                                       RHS may reference earlier LHS
      - dict with "_recur" key      : recursive call (Phase 3.E, POPL'10 §5.3)
    """
    # Phase 3.E recursive call.
    if isinstance(atom, dict) and atom.get("_recur"):
        return _recur_body(atom, pre_b, post_b, hid, uf, problem)

    if isinstance(atom, dict):
        conjuncts = []
        for vname, post_var in post_b.items():
            if vname in atom:
                rhs = parse_expr(atom[vname], pre_b, uf)
                conjuncts.append(post_var == rhs)
            else:
                conjuncts.append(post_var == pre_b[vname])
        return z3.And(*conjuncts) if len(conjuncts) > 1 else conjuncts[0]

    if isinstance(atom, list):
        # SSA-style: walk in order, maintaining a Python-level binding
        # that records the most-recently-assigned value of each var.
        # Each post variable is bound by a single equation; SSA fresh
        # names do not appear in the Z3 formula — they are inlined.
        current = dict(pre_b)
        for entry in atom:
            if not (isinstance(entry, dict) and len(entry) == 1):
                raise ValueError(
                    f"SSA atom entries must be single-key dicts; "
                    f"hole {hid!r} got entry {entry!r}"
                )
            var, rhs_str = next(iter(entry.items()))
            if var not in current:
                raise ValueError(
                    f"SSA atom for hole {hid!r} assigns to {var!r}, "
                    f"which is not a declared program variable"
                )
            current[var] = parse_expr(rhs_str, current, uf)
        conjuncts = [post_var == current[vname]
                     for vname, post_var in post_b.items()]
        return z3.And(*conjuncts) if len(conjuncts) > 1 else conjuncts[0]

    raise TypeError(
        f"transition atom for hole {hid!r} must be dict or list of "
        f"single-key dicts; got {type(atom).__name__}"
    )


def _recur_body(atom, pre_b, post_b, hid, uf, problem):
    """Build the Z3 transition for a recursive procedure call.

    POPL'10 §5.3:  s_recur = s_args ∧ (Fpre(vin') ⇒ Fpost(vout'')) ∧ s_ret

    Fresh Z3 variables represent the call's inputs (vin') and outputs
    (vout'').  The induction hypothesis is asserted as a conjunct so
    the synthesizer can use the spec assumption when proving the body
    against the procedure's spec.  vin'/vout'' are universally
    quantified at the outer ForAll along with V.
    """
    suffix = _next_recur_id()
    # Fresh Z3 vars for the recursive call's inputs and outputs.
    args_z3: dict[str, z3.ExprRef] = {
        v.name: _make_z3_var(f"{v.name}__call_in_{suffix}", v.type)
        for v in problem.inputs
    }
    rets_z3: dict[str, z3.ExprRef] = {
        v.name: _make_z3_var(f"{v.name}__call_out_{suffix}", v.type)
        for v in problem.outputs
    }

    conjuncts: list[z3.ExprRef] = []

    # s_args: each procedure input gets a value computed from pre-state.
    # Missing entries default to the current value (preserved).
    args_spec = atom.get("args", {})
    for v in problem.inputs:
        if v.name in args_spec:
            rhs = parse_expr(args_spec[v.name], pre_b, uf)
        else:
            rhs = pre_b[v.name]
        conjuncts.append(args_z3[v.name] == rhs)

    # Induction hypothesis: Fpre(vin') ⇒ Fpost(vin', vout'').
    #   - Fpre references *inputs only* — evaluate under args_z3.
    #   - Fpost references inputs and outputs — evaluate under a binding
    #     where input names map to args_z3 and output names override
    #     to rets_z3.  This handles procedures (like rec_zero_array)
    #     where a var is both input and output: Fpost's reference to
    #     such a var should mean the *returned* value.
    fpre_binding: dict[str, z3.ExprRef] = dict(args_z3)
    fpost_binding: dict[str, z3.ExprRef] = dict(args_z3)
    for v in problem.outputs:
        fpost_binding[v.name] = rets_z3[v.name]
    fpre  = parse_expr(problem.pre,  fpre_binding,  uf)
    fpost = parse_expr(problem.post, fpost_binding, uf)
    conjuncts.append(z3.Implies(fpre, fpost))

    # s_ret: each var in `ret` gets a value computed from the call's
    # returns.  The expression is parsed under a binding where
    # procedure-output names map to the call's output Z3 vars, and
    # everything else (inputs, locals) refers to the *pre-state*
    # values.  This lets a `ret` expression do post-processing on the
    # returned values that also references original state — e.g.
    # `Update(A, n - 1, 0)` reads the returned A and uses the
    # original n to compute the update index.
    ret_spec    = atom.get("ret", {})
    ret_binding = dict(pre_b)
    for v in problem.outputs:
        ret_binding[v.name] = rets_z3[v.name]
    assigned: set[str] = set()
    for var_name, rhs_str in ret_spec.items():
        rhs = parse_expr(rhs_str, ret_binding, uf)
        conjuncts.append(post_b[var_name] == rhs)
        assigned.add(var_name)

    # Preserve any var (input, output, or local) NOT in `ret`.  For a
    # procedure where an input is also an output (e.g. an array
    # threaded through and modified by the call), the user is
    # expected to list it in `ret` so it gets the returned value;
    # otherwise it's preserved at its pre-state.
    for v in problem.all_vars:
        if v.name not in assigned:
            conjuncts.append(post_b[v.name] == pre_b[v.name])

    return z3.And(*conjuncts) if len(conjuncts) > 1 else conjuncts[0]


def _linearize(node: Template) -> list[Template]:
    if isinstance(node, Seq):
        return _linearize(node.left) + _linearize(node.right)
    return [node]


def _atom_lhs_vars(atom) -> set[str]:
    """LHS vars that an atom (transition or recur) may assign."""
    if isinstance(atom, dict) and atom.get("_recur"):
        # Recur: only `ret` keys land in the post-state.  Inputs/locals
        # not in `ret` are preserved (see _recur_body's preservation
        # rule).
        return set(atom.get("ret", {}).keys())
    if isinstance(atom, dict):
        return set(atom.keys())
    if isinstance(atom, list):
        return {next(iter(entry)) for entry in atom}
    return set()


def _has_break_branch(node: Template, problem: Problem) -> bool:
    """K.D.IMPL — detect whether `node` contains any SB branch whose
    transition atoms carry `_break: True`, considering only breaks
    that exit `node`'s ENCLOSING Loop (NOT breaks in nested inner
    Loops, which exit only the inner Loop).

    Used to relax the abstract Loop transition: a break-capable
    Loop's exit can have `g` still true.  Only direct-body breaks
    of THIS Loop count; an inner Loop's break is handled by that
    inner Loop's own abstract transition.
    """
    if isinstance(node, SB):
        bid = node.block_id
        if node.n == 1:
            hids = [f"s@{bid}"]
        else:
            hids = [f"s@{bid}.{k}" for k in range(node.n)]
        for hid in hids:
            for atom in problem.atoms.get(hid, []):
                atom_list = atom if isinstance(atom, list) else [atom]
                for entry in atom_list:
                    if isinstance(entry, dict) and entry.get("_break") is True:
                        return True
        return False
    if isinstance(node, Loop):
        # Do NOT recurse: inner Loop's break exits the inner Loop,
        # not this one.
        return False
    if isinstance(node, Seq):
        return (_has_break_branch(node.left, problem)
                or _has_break_branch(node.right, problem))
    if isinstance(node, Recur):
        return False
    return False


def _modified_vars_of_template(node: Template, problem: Problem) -> set[str]:
    """Conservative over-approximation of program vars that may be
    modified by `node`.  Used for frame preservation across abstract
    Loop transitions (Phase 3.K).
    """
    modified: set[str] = set()
    if isinstance(node, SB):
        bid = node.block_id
        if node.n == 1:
            hids = [f"s@{bid}"]
        else:
            hids = [f"s@{bid}.{k}" for k in range(node.n)]
        for hid in hids:
            for atom in problem.atoms.get(hid, []):
                modified |= _atom_lhs_vars(atom)
    elif isinstance(node, Loop):
        modified |= _modified_vars_of_template(node.body, problem)
    elif isinstance(node, Seq):
        modified |= _modified_vars_of_template(node.left, problem)
        modified |= _modified_vars_of_template(node.right, problem)
    elif isinstance(node, Recur):
        for atom in problem.atoms.get(f"s@{node.recur_id}", []):
            modified |= _atom_lhs_vars(atom)
    else:
        raise TypeError(f"unknown template node: {type(node).__name__}")
    return modified


def _type_sort(type_str: str) -> z3.SortRef:
    """Map a type string to a Z3 sort."""
    if type_str == "int":     return z3.IntSort()
    if type_str == "bool":    return z3.BoolSort()
    if type_str == "int[]":   return z3.ArraySort(z3.IntSort(), z3.IntSort())
    if type_str == "bool[]":  return z3.ArraySort(z3.IntSort(), z3.BoolSort())
    if type_str == "int[][]":
        # 2D as Array(Int, Array(Int, Int)).  Indexing `A[i][j]` is
        # `Select(Select(A, i), j)`; updating cell (i, j) to v is
        # `Store(A, i, Store(Select(A, i), j, v))` and is exposed
        # to the user as `Update(A, i, j, v)` (see expr.py).
        return z3.ArraySort(z3.IntSort(),
                            z3.ArraySort(z3.IntSort(), z3.IntSort()))
    raise ValueError(f"unsupported type {type_str!r}")


def _make_z3_var(name: str, type_str: str) -> z3.ExprRef:
    """Allocate a Z3 constant of the given type."""
    if type_str == "int":     return z3.Int(name)
    if type_str == "bool":    return z3.Bool(name)
    if type_str == "int[]":   return z3.Array(name, z3.IntSort(), z3.IntSort())
    if type_str == "bool[]":  return z3.Array(name, z3.IntSort(), z3.BoolSort())
    if type_str == "int[][]":
        return z3.Const(name, _type_sort(type_str))
    raise ValueError(f"unsupported var type {type_str!r}")
