"""Decoder — Z3 model → Solution (with pretty-printed pseudocode).

The model assigns one indicator to True per hole (single-hot).  We
look up the chosen atom and walk the template to emit pseudocode.
"""
from __future__ import annotations
from typing import Any

import z3

from .ir import SB, Loop, Seq, Recur, Problem, Template
from .expand import ExpandedScaffold
from .constraints import ConstraintSystem
from .result import Solution


def decode(
    model: z3.ModelRef,
    problem: Problem,
    scaffold: ExpandedScaffold,
    system: ConstraintSystem,
) -> Solution:
    """Read a Z3 model and produce a Solution."""
    choices: dict[str, Any] = {}            # int (single-hot) or list[int] (conj)
    atoms_chosen: dict[str, Any] = {}       # atom value or list-of-atoms

    for hid, bs in system.indicators.items():
        is_conj = hid.startswith("tau@")    # conjunctive holes
        if is_conj:
            idxs = [k for k, b in enumerate(bs)
                    if z3.is_true(model.eval(b, model_completion=True))]
            choices[hid] = idxs
            atoms_chosen[hid] = [problem.atoms[hid][k] for k in idxs]
        else:
            for k, b in enumerate(bs):
                v = model.eval(b, model_completion=True)
                if z3.is_true(v):
                    choices[hid] = k
                    atoms_chosen[hid] = problem.atoms[hid][k]
                    break
            else:
                raise RuntimeError(
                    f"decode: no indicator True for hole {hid!r} "
                    "(single-hot violated?)"
                )

    code = _pretty_print(problem, scaffold, atoms_chosen)
    score, components = _score(problem, atoms_chosen)
    return Solution(
        choices=choices,
        atoms=atoms_chosen,
        code=code,
        score=score,
        score_components=components,
    )


# ─────────────────────────────────────────────────────────────────────
# Pretty-printing.  Walks the template, substituting chosen atoms.
# ─────────────────────────────────────────────────────────────────────
def _pretty_print(problem: Problem, scaffold: ExpandedScaffold,
                  atoms: dict[str, Any]) -> str:
    lines: list[str] = []
    sig = ", ".join(f"{v.type} {v.name}" for v in problem.inputs)
    ret_t = problem.outputs[0].type if problem.outputs else "void"
    fname = "synth"
    lines.append(f"{ret_t} {fname}({sig}) {{")
    if problem.locals:
        # group by type to avoid `int v1, int v2, …`
        by_type: dict[str, list[str]] = {}
        for v in problem.locals:
            by_type.setdefault(v.type, []).append(v.name)
        for t, names in by_type.items():
            lines.append(f"    {t} {', '.join(names)};")
    _emit(problem.template, atoms, problem, lines, indent="    ")
    if problem.outputs:
        rets = ", ".join(v.name for v in problem.outputs)
        lines.append(f"    return {rets};")
    lines.append("}")

    # Proof annotations summary.
    proof_lines: list[str] = []
    for hid, atom in atoms.items():
        if hid.startswith("tau@"):
            proof_lines.append(
                f"  invariant {hid.split('@', 1)[1]}: {_format_tau(atom)}"
            )
        elif hid.startswith("phi@"):
            proof_lines.append(f"  ranking   {hid.split('@', 1)[1]}: {atom}")
        elif hid.startswith("cost@"):
            proof_lines.append(f"  cost      {hid.split('@', 1)[1]}: {atom}")

    if proof_lines:
        lines.append("")
        lines.append("// proof")
        lines.extend(proof_lines)
    return "\n".join(lines)


def _emit(node: Template, atoms: dict[str, Any], problem: Problem,
          lines: list[str], indent: str) -> None:
    if isinstance(node, SB):
        if node.n == 1:
            atom = atoms[f"s@{node.block_id}"]
            _emit_transition(atom, lines, indent, problem)
        else:
            # Phase 3.I: n explicit branches.  Render as chained
            # if/else-if/else-if with the synthesized guards.  No
            # implicit "else"; coverage `⋁ g_i ≡ true` is asserted as
            # well-formedness so some branch fires.
            for k in range(node.n):
                guard = atoms[f"g@{node.block_id}.{k}"]
                trans = atoms[f"s@{node.block_id}.{k}"]
                prefix = "if" if k == 0 else "else if"
                lines.append(f"{indent}{prefix} ({guard}) {{")
                _emit_transition(trans, lines, indent + "    ", problem)
                lines.append(f"{indent}}}")

    elif isinstance(node, Loop):
        lid = node.loop_id
        g   = atoms[f"g@{lid}"]
        tau = atoms[f"tau@{lid}"]
        phi = atoms[f"phi@{lid}"]
        lines.append(
            f"{indent}while ({g})   "
            f"// [τ={_format_tau(tau)}, ϕ={phi}]"
        )
        lines.append(f"{indent}{{")
        _emit(node.body, atoms, problem, lines, indent + "    ")
        lines.append(f"{indent}}}")

    elif isinstance(node, Seq):
        _emit(node.left,  atoms, problem, lines, indent)
        _emit(node.right, atoms, problem, lines, indent)

    elif isinstance(node, Recur):
        atom = atoms[f"s@{node.recur_id}"]
        _emit_transition(atom, lines, indent, problem)

    else:
        raise TypeError(f"unknown template node: {type(node).__name__}")


# ─────────────────────────────────────────────────────────────────────
# Scoring.  Default heuristic: α·atom_count + β·cost_proxy.
#   atom_count: number of "expression atoms" used across all holes
#               (simple proxy: count syntactic operators in the chosen
#               atom string for predicate/numeric holes, count number
#               of vars assigned in transitions).
#   cost_proxy: number of loop iterations approximated by a constant
#               per loop (no real cost model yet).
# Both weights default to 1.0; user can override later via a callback.
# ─────────────────────────────────────────────────────────────────────
def _score(problem: Problem, atoms: dict[str, Any],
           alpha: float = 1.0, beta: float = 0.5) -> tuple[float, dict[str, float]]:
    atom_count = 0
    n_loops = 0
    for hid, atom in atoms.items():
        if hid.startswith("tau@"):
            # Conjunctive τ: list of chosen atom strings.  Count each.
            n_loops += 1
            if isinstance(atom, list):
                atom_count += sum(_atom_complexity(a) for a in atom)
            elif isinstance(atom, str):
                # Shouldn't occur in Phase 2 (τ is always conjunctive),
                # but tolerate it.
                atom_count += _atom_complexity(atom)
            continue
        if isinstance(atom, dict):
            atom_count += len(atom)
        elif isinstance(atom, list):
            # SSA transition list — count assignments.
            atom_count += len(atom)
        elif isinstance(atom, str):
            atom_count += _atom_complexity(atom)
    cost_proxy = float(n_loops)
    total = alpha * atom_count + beta * cost_proxy
    return total, {
        "atom_count": float(atom_count),
        "cost_proxy": cost_proxy,
        "alpha":      alpha,
        "beta":       beta,
    }


def _emit_transition(atom, lines: list[str], indent: str,
                     problem=None, fname: str = "synth") -> None:
    """Render one transition atom as one or more assignment lines."""
    if not atom:
        lines.append(f"{indent}/* skip */")
        return
    if isinstance(atom, dict) and atom.get("_recur"):
        _emit_recur(atom, lines, indent, problem, fname)
        return
    # K.B.IMPL-5: recognize break-marked atoms.  Strip the `_break`
    # flag from the printed transition; append `break;` after.
    if isinstance(atom, dict):
        has_break = atom.get("_break") is True
        body_keys = [k for k in atom.keys() if not k.startswith("_")]
        if body_keys:
            lhs = ", ".join(body_keys)
            rhs = ", ".join(atom[k] for k in body_keys)
            lines.append(f"{indent}{lhs} := {rhs};")
        if has_break:
            lines.append(f"{indent}break;")
        return
    elif isinstance(atom, list):
        for entry in atom:
            var, rhs = next(iter(entry.items()))
            lines.append(f"{indent}{var} := {rhs};")
    else:
        raise TypeError(
            f"transition atom must be dict or list, "
            f"got {type(atom).__name__}"
        )


def _emit_recur(atom, lines: list[str], indent: str, problem, fname: str) -> None:
    """Render a recursive-call transition.

    Decoded shape (if `ret` is the identity mapping output_var → output_var):
        out_vars := fname(args);
    Otherwise, intermediate temp form:
        (tmp_out_vars) := fname(args);
        var := <ret_expr>; …
    """
    args_spec = atom.get("args", {})
    ret_spec  = atom.get("ret", {})
    input_args = ", ".join(args_spec.get(v.name, v.name) for v in problem.inputs)
    output_names = [v.name for v in problem.outputs]

    # Identity-mapping shortcut: every output var v gets exactly the
    # call's output v (no transformation).
    identity = (set(ret_spec.keys()) == set(output_names)
                and all(ret_spec[n].strip() == n for n in output_names))
    if identity:
        lhs = ", ".join(output_names)
        lines.append(f"{indent}{lhs} := {fname}({input_args});")
        return

    # General form: capture into temps, then apply ret mapping.
    tmp = ", ".join(f"_r_{n}" for n in output_names)
    lines.append(f"{indent}({tmp}) := {fname}({input_args});")
    # Apply ret mapping (substitute output_var refs with the temps).
    for v_name, rhs in ret_spec.items():
        rhs_subst = rhs
        for n in output_names:
            rhs_subst = rhs_subst.replace(n, f"_r_{n}")
        lines.append(f"{indent}{v_name} := {rhs_subst};")


def _atom_complexity(s: str) -> int:
    """Crude syntactic complexity: count tokens that aren't whitespace."""
    operators = "+-*/<>=!&|()"
    n = 0
    for ch in s:
        if ch in operators:
            n += 1
    return max(1, n)


def _format_tau(atom) -> str:
    """Render a conjunctive τ assignment (list of atom strings) or
    fall back to str() for single-hot atoms."""
    if isinstance(atom, list):
        if not atom:
            return "true"
        return " and ".join(f"({a})" for a in atom)
    return str(atom)
