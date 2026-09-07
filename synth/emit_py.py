"""Python source emitter (Phase 5.C).

Solution + Problem → a valid Python function.  Sibling of `emit_c.py`,
but the target is Python — which means:

  - No type declarations except optional type hints on the signature.
  - Parallel assignment is idiomatic: `x, y = y, x` (instead of the
    C emitter's temp-dance).
  - Array Update chains decode straight to `A[i] = v` statements;
    multi-index swaps become tuple assignments.
  - `Implies` / `ForAll` / `Exists` are NOT Python built-ins — they
    get translated to `(not P) or Q`, `all(... for ... in ...)`, and
    `any(...)` respectively.

Two emission modes:

  - **Default** (`runtime_check=False`): proof obligations appear as
    Python comments next to the relevant code (same shape as the C
    emitter's `/* invariant ... */` annotations).  The generated
    Python imports nothing special.

  - **`runtime_check=True`**: proof obligations are lowered into
    calls against the `synth.proof_runtime` library — `proof_pre`,
    `proof_post`, `proof_invariant`, `proof_decrease`,
    `proof_lower_bound`, `proof_coverage`.  A violation raises
    `ProofViolation` (an `AssertionError` subclass) at runtime,
    so the synthesized program self-checks its own correctness
    contract.  Useful as a debugging affordance for the LLM-driver
    loop: a quick runnable sanity layer before falling through to
    clang + the C runtime test.

Quantifier translation in `runtime_check` mode tries common
patterns:

  - `ForAll(lambda k: Implies(0 <= k and k < UB, body))`
        → `all(body_translated for k in range(UB))`
  - `ForAll(lambda p, q: Implies(0 <= p and p <= q and q < UB, body))`
        → `all(body_translated for p in range(UB) for q in range(p, UB))`
  - Other shapes fall back to an emitted comment plus a `proof_check`
    skipped with a TODO note.

Not yet supported:

  - `Recur` outside of the simple cases shared with `emit_c.py`'s
    recur path (single-int return, array in-place).  Mixed-output
    shapes degrade to a TODO comment.
"""
from __future__ import annotations
import ast
import re
from typing import Any

from .ir import SB, Loop, Seq, Recur, Problem, Template, Var
from .result import Solution


# ─────────────────────────────────────────────────────────────────────
# Entry point.
# ─────────────────────────────────────────────────────────────────────
def emit_py(solution: Solution,
            problem: Problem,
            fname: str = "synth",
            runtime_check: bool = False) -> str:
    """Render `solution` as a Python function `fname(...)`.

    If `runtime_check=True`, proof obligations are lowered into
    `synth.proof_runtime` calls.  Otherwise they're emitted as
    comments only.
    """
    lines: list[str] = []

    lines.append('"""Synthesized by Pragna-successor '
                 '(proof-theoretic synthesis).')
    lines.append('')
    lines.append(f"   pre  : {problem.pre}")
    lines.append(f"   post : {problem.post}")
    lines.append('"""')
    if runtime_check:
        lines.append("from synth.proof_runtime import (")
        lines.append("    proof_pre, proof_post, proof_invariant,")
        lines.append("    proof_decrease, proof_lower_bound, "
                     "proof_coverage,")
        lines.append(")")
    lines.append("")

    # Signature.
    ret_hint, params, ret_kind = _signature(problem)
    sig = f"def {fname}({', '.join(params)})"
    if ret_hint:
        sig += f" -> {ret_hint}"
    sig += ":"
    lines.append(sig)

    indent = "    "

    # Pre check.
    if runtime_check:
        pre_py = _py_expr(problem.pre)
        if pre_py is None:
            lines.append(f'{indent}# pre runtime check skipped '
                         f'(unsupported expression shape): '
                         f'{problem.pre}')
        else:
            lines.append(f'{indent}proof_pre({pre_py}, '
                         f'"Pre: {problem.pre}")')

    # Local init for int outputs that aren't already inputs (so they
    # have a definite value before any code path uses them).  Inputs
    # that are also outputs already have a value via the parameter.
    input_names = {v.name for v in problem.inputs}
    fresh_int_outs = [v for v in problem.outputs
                      if v.type == "int" and v.name not in input_names]
    int_outs = [v for v in problem.outputs if v.type == "int"]
    for v in fresh_int_outs:
        lines.append(f"{indent}{v.name} = 0")
    for v in problem.locals:
        default = "0" if v.type == "int" else "None"
        lines.append(f"{indent}{v.name} = {default}")
    if fresh_int_outs or problem.locals:
        lines.append("")

    # Body.
    _emit_node(problem.template, solution.atoms, problem,
               lines, indent, fname, runtime_check)

    # Post check.
    if runtime_check:
        post_py = _py_expr(problem.post)
        if post_py is None:
            lines.append(f'{indent}# post runtime check skipped '
                         f'(unsupported expression shape): '
                         f'{problem.post}')
        else:
            lines.append(f'{indent}proof_post({post_py}, '
                         f'"Post: {problem.post}")')

    # Return — Python passes ints by value, so any int output must
    # be returned even if it shares its name with an input.
    if ret_kind == "single_int":
        lines.append(f"{indent}return {int_outs[0].name}")
    elif ret_kind == "tuple":
        names = ", ".join(v.name for v in int_outs)
        lines.append(f"{indent}return ({names})")
    # array_inplace / none: no return statement.

    return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────────
# Signature.
# ─────────────────────────────────────────────────────────────────────
def _signature(problem: Problem) -> tuple[str, list[str], str]:
    """Compute (return-type hint, params, return kind).

    Python passes ints by value, so int outputs always need to be
    returned (single → bare value, multiple → tuple) regardless of
    whether they're also inputs.  Array outputs that are also inputs
    are modified in place; fresh array outputs are returned.

    Return-kind selection:
      - "single_int":   one int output      → `return <name>`
      - "tuple":        ≥ 2 int outputs (or int + something else)
                        → `return (<names>)`
      - "array_inplace": array output also an input; no return
      - "none":          no outputs at all
    """
    input_names = {v.name for v in problem.inputs}
    int_outs = [v for v in problem.outputs if v.type == "int"]
    fresh_arr_outs = [v for v in problem.outputs
                      if v.type.endswith("[]") and v.name not in input_names]

    params: list[str] = []
    for v in problem.inputs:
        params.append(f"{v.name}: {_py_type(v.type)}")
    for v in fresh_arr_outs:
        params.append(f"{v.name}: {_py_type(v.type)}")

    if len(int_outs) == 1:
        return _py_type("int"), params, "single_int"
    if len(int_outs) > 1:
        inner = ", ".join("int" for _ in int_outs)
        return f"tuple[{inner}]", params, "tuple"
    if fresh_arr_outs or any(v.type.endswith("[]")
                             for v in problem.outputs):
        return "None", params, "array_inplace"
    return "None", params, "none"


def _py_type(t: str) -> str:
    if t == "int":      return "int"
    if t == "int[]":    return "list[int]"
    if t == "int[][]":  return "list[list[int]]"
    if t == "bool":     return "bool"
    if t == "bool[]":   return "list[bool]"
    return "Any"


# ─────────────────────────────────────────────────────────────────────
# Node-level emission.
# ─────────────────────────────────────────────────────────────────────
def _emit_node(node: Template,
               atoms: dict[str, Any],
               problem: Problem,
               lines: list[str],
               indent: str,
               fname: str,
               runtime_check: bool) -> None:
    if isinstance(node, SB):
        _emit_sb(node, atoms, problem, lines, indent, fname, runtime_check)
    elif isinstance(node, Loop):
        _emit_loop(node, atoms, problem, lines, indent, fname,
                   runtime_check)
    elif isinstance(node, Seq):
        _emit_node(node.left,  atoms, problem, lines, indent, fname,
                   runtime_check)
        _emit_node(node.right, atoms, problem, lines, indent, fname,
                   runtime_check)
    elif isinstance(node, Recur):
        atom = atoms[f"s@{node.recur_id}"]
        _emit_transition(atom, lines, indent, problem, fname,
                         runtime_check)
    else:
        raise TypeError(f"unknown template node: {type(node).__name__}")


def _emit_sb(node: SB,
             atoms: dict[str, Any],
             problem: Problem,
             lines: list[str],
             indent: str,
             fname: str,
             runtime_check: bool) -> None:
    if node.n == 1:
        atom = atoms[f"s@{node.block_id}"]
        _emit_transition(atom, lines, indent, problem, fname,
                         runtime_check)
        return

    # Multi-branch: optional coverage check, then if/elif chain.
    guards = [atoms[f"g@{node.block_id}.{k}"] for k in range(node.n)]
    if runtime_check:
        args = ", ".join(_py_expr(g) for g in guards)
        lines.append(f'{indent}proof_coverage({args}, '
                     f'message="{node.block_id} branch coverage")')

    for k in range(node.n):
        trans = atoms[f"s@{node.block_id}.{k}"]
        prefix = "if" if k == 0 else "elif"
        lines.append(f"{indent}{prefix} {_py_expr(guards[k])}:")
        _emit_transition(trans, lines, indent + "    ", problem, fname,
                         runtime_check)


def _emit_loop(node: Loop,
               atoms: dict[str, Any],
               problem: Problem,
               lines: list[str],
               indent: str,
               fname: str,
               runtime_check: bool) -> None:
    lid = node.loop_id
    guard = atoms[f"g@{lid}"]
    tau   = atoms.get(f"tau@{lid}", [])
    phi   = atoms.get(f"phi@{lid}", "")

    inv_str = _format_tau(tau)
    if runtime_check:
        # Annotation comment then runtime checks at body top.
        lines.append(f"{indent}# invariant {lid}: {inv_str}")
        lines.append(f"{indent}# ranking   {lid}: {phi}")
    else:
        lines.append(f"{indent}# invariant {lid}: {inv_str}")
        lines.append(f"{indent}# ranking   {lid}: {phi}")

    lines.append(f"{indent}while {_py_expr(guard)}:")
    body_indent = indent + "    "

    if runtime_check:
        # τ at body entry, LB on φ, capture φ for the decrease check.
        for atom in (tau if isinstance(tau, list) else [tau]):
            atom_py = _py_expr(atom)
            if atom_py is None:
                lines.append(
                    f"{body_indent}# invariant runtime check skipped "
                    f"(unsupported quantifier shape): {atom}")
                continue
            lines.append(
                f'{body_indent}proof_invariant({atom_py}, '
                f'"{lid} invariant: {atom}")')
        if phi:
            lines.append(
                f'{body_indent}proof_lower_bound({_py_expr(phi)}, '
                f'"{lid} ranking LB")')
            lines.append(
                f"{body_indent}_phi_{lid}_prev = {_py_expr(phi)}")

    _emit_node(node.body, atoms, problem, lines, body_indent, fname,
               runtime_check)

    if runtime_check and phi:
        lines.append(
            f'{body_indent}proof_decrease({_py_expr(phi)}, '
            f'_phi_{lid}_prev, '
            f'"{lid} ranking decrease")')

    if runtime_check:
        # At loop exit, the invariant still holds (with ¬g).
        for atom in (tau if isinstance(tau, list) else [tau]):
            atom_py = _py_expr(atom)
            if atom_py is None:
                continue
            lines.append(
                f'{indent}proof_invariant({atom_py}, '
                f'"{lid} invariant (at exit): {atom}")')


# ─────────────────────────────────────────────────────────────────────
# Transitions.
# ─────────────────────────────────────────────────────────────────────
def _emit_transition(atom: Any,
                     lines: list[str],
                     indent: str,
                     problem: Problem,
                     fname: str,
                     runtime_check: bool) -> None:
    if isinstance(atom, dict) and atom.get("_recur"):
        _emit_recur_call(atom, problem, lines, indent, fname,
                         runtime_check)
        return
    if isinstance(atom, dict):
        # K.B.IMPL-5: strip the `_break` flag from the dict before
        # rendering; append `break` after the assignment.
        has_break = atom.get("_break") is True
        body = {k: v for k, v in atom.items() if not k.startswith("_")}
        if body:
            _emit_parallel_dict(body, lines, indent)
        elif not has_break:
            lines.append(f"{indent}pass  # skip")
        if has_break:
            lines.append(f"{indent}break")
        return
    if isinstance(atom, list):
        for entry in atom:
            for var, rhs in entry.items():
                _emit_assignment(var, rhs, lines, indent)
        return
    lines.append(f"{indent}# unknown atom shape: {atom!r}")


def _emit_parallel_dict(atom: dict,
                        lines: list[str],
                        indent: str) -> None:
    """Emit a parallel-assignment dict using Python's tuple assignment
    when there are multiple targets — naturally parallel semantics,
    no temp dance needed.

    Update-chain RHSes are handled separately (they decode to one or
    more `A[i] = v` statements).
    """
    update_items: list[tuple[str, str]] = []
    scalar_items: list[tuple[str, str]] = []
    for var, rhs in atom.items():
        if isinstance(rhs, str) and rhs.strip().startswith("Update("):
            update_items.append((var, rhs))
        else:
            scalar_items.append((var, rhs))

    # Updates first (they only modify their arrays; scalars after
    # see the post-update state — but our atoms don't typically rely
    # on this).
    for var, rhs in update_items:
        _emit_assignment(var, rhs, lines, indent)

    if not scalar_items:
        return

    # Python's tuple assignment naturally handles parallel semantics:
    #   x, y = y, x   ← evaluates RHS first, then assigns.
    # We can use it even when there are no LHS / RHS conflicts —
    # cleaner than emitting individual statements with temp dances.
    if len(scalar_items) == 1:
        var, rhs = scalar_items[0]
        _emit_assignment(var, rhs, lines, indent)
    else:
        lhs = ", ".join(var for var, _ in scalar_items)
        rhs = ", ".join(_py_expr(r) for _, r in scalar_items)
        lines.append(f"{indent}{lhs} = {rhs}")


def _emit_assignment(var: str,
                     rhs_str: str,
                     lines: list[str],
                     indent: str) -> None:
    rhs_strip = rhs_str.strip()
    if rhs_strip == var:
        return  # identity assignment: skip
    if rhs_strip.startswith("Update("):
        if _emit_update_chain(var, rhs_strip, lines, indent):
            return
    lines.append(f"{indent}{var} = {_py_expr(rhs_str)}")


# ─────────────────────────────────────────────────────────────────────
# Array Update chain → tuple-assignment of A[idx]s.
# ─────────────────────────────────────────────────────────────────────
def _emit_update_chain(target: str,
                       rhs_str: str,
                       lines: list[str],
                       indent: str) -> bool:
    try:
        tree = ast.parse(rhs_str, mode="eval")
    except SyntaxError:
        return False

    # Each chain entry is either a 1D update (single index) or 2D
    # update (row + col).  We render as `A[idx]` or `A[row][col]`.
    chain: list[tuple[list[ast.expr], ast.expr]] = []
    node = tree.body
    while (isinstance(node, ast.Call)
           and isinstance(node.func, ast.Name)
           and node.func.id == "Update"
           and len(node.args) in (3, 4)):
        if len(node.args) == 3:
            chain.append(([node.args[1]], node.args[2]))
        else:
            chain.append(([node.args[1], node.args[2]], node.args[3]))
        node = node.args[0]
    if not chain:
        return False
    if not isinstance(node, ast.Name) or node.id != target:
        return False

    chain.reverse()  # inner-first

    def _lhs(idxs: list[ast.expr]) -> str:
        return f"{target}" + "".join(f"[{ast.unparse(i)}]" for i in idxs)

    if len(chain) == 1:
        idxs, val = chain[0]
        lines.append(f"{indent}{_lhs(idxs)} = {ast.unparse(val)}")
        return True

    # Multi-write: tuple assignment — evaluates all RHS first, then
    # writes all LHS.  Python parallel semantics.
    lhs = ", ".join(_lhs(idxs) for idxs, _ in chain)
    rhs = ", ".join(ast.unparse(val) for _, val in chain)
    lines.append(f"{indent}{lhs} = {rhs}")
    return True


# ─────────────────────────────────────────────────────────────────────
# Recursive calls.
# ─────────────────────────────────────────────────────────────────────
def _emit_recur_call(atom: dict,
                     problem: Problem,
                     lines: list[str],
                     indent: str,
                     fname: str,
                     runtime_check: bool) -> None:
    args_spec = atom.get("args", {})
    ret_spec  = atom.get("ret", {})

    # Args in input order.
    call_args = []
    for v in problem.inputs:
        if v.name in args_spec:
            call_args.append(_py_expr(args_spec[v.name]))
        else:
            call_args.append(v.name)
    args_str = ", ".join(call_args)

    # Fpre-on-args wrap.
    fpre_at_args = problem.pre or "True"
    for v in sorted(problem.inputs, key=lambda x: -len(x.name)):
        repl = args_spec.get(v.name, v.name)
        fpre_at_args = re.sub(rf'\b{re.escape(v.name)}\b',
                              f"({repl})", fpre_at_args)
    trivial_pre = (problem.pre or "").strip().lower() in ("", "true", "1")

    if not trivial_pre:
        lines.append(f"{indent}if {_py_expr(fpre_at_args)}:")
        body_indent = indent + "    "
    else:
        body_indent = indent

    input_names = {v.name for v in problem.inputs}
    fresh_int_outs = [v for v in problem.outputs
                      if v.type == "int" and v.name not in input_names]
    fresh_arr_outs = [v for v in problem.outputs
                      if v.type.endswith("[]") and v.name not in input_names]
    in_place_arrays = [v for v in problem.outputs
                       if v.type.endswith("[]") and v.name in input_names]

    if (len(fresh_int_outs) == 1 and not fresh_arr_outs
            and not in_place_arrays):
        rv = fresh_int_outs[0].name
        identity = (set(ret_spec.keys()) == {rv}
                    and ret_spec.get(rv, "").strip() == rv)
        if identity:
            lines.append(f"{body_indent}{rv} = {fname}({args_str})")
        else:
            tmp = f"_r_{rv}"
            lines.append(f"{body_indent}{tmp} = {fname}({args_str})")
            for var, rhs in ret_spec.items():
                rhs_subst = re.sub(rf'\b{re.escape(rv)}\b', tmp, rhs)
                lines.append(f"{body_indent}{var} = {_py_expr(rhs_subst)}")
    elif (not fresh_int_outs) and (in_place_arrays or fresh_arr_outs):
        lines.append(f"{body_indent}{fname}({args_str})")
        for var, rhs in ret_spec.items():
            _emit_assignment(var, rhs, lines, body_indent)
    else:
        lines.append(f"{body_indent}# recur shape not yet supported "
                     f"in py emitter: {atom}")
        lines.append(f"{body_indent}pass")


# ─────────────────────────────────────────────────────────────────────
# Expression translation: synth-syntax → runtime-Python.
# ─────────────────────────────────────────────────────────────────────
def _py_expr(expr: Any) -> str:
    """Convert a synth-syntax expression string to Python.

    Most arithmetic, comparison, and boolean operators are already
    Python-compatible.  The transformations applied here:

      - `true` / `false`          →  `True` / `False`  (SMT-LIB style)
      - `Implies(P, Q)`           →  `((not (P)) or (Q))`
      - `ForAll(lambda v: ...)`   →  `all(... for v in <inferred-range>)`
      - `Exists(lambda v: ...)`   →  `any(... for v in <inferred-range>)`

    Returns the translated Python string, or `None` if the expression
    uses a construct that can't be runtime-evaluated (caller should
    fall back to emitting it as a comment).
    """
    if not isinstance(expr, str):
        return str(expr)
    # SMT-LIB / synth-DSL writes the trivial Pre / Post as `true` /
    # `false`; Python wants `True` / `False`.  Whole-word substitute
    # before AST parsing so `Name(id="true")` doesn't become an
    # unbound lookup at runtime.
    expr_norm = re.sub(r"\btrue\b", "True", expr)
    expr_norm = re.sub(r"\bfalse\b", "False", expr_norm)
    try:
        tree = ast.parse(expr_norm, mode="eval")
    except SyntaxError:
        return expr  # leave as-is

    try:
        new_tree = _RuntimeTranslator().visit(tree)
    except _Untranslatable:
        return None
    return ast.unparse(new_tree)


class _Untranslatable(Exception):
    """Raised by the AST translator when a construct can't be
    lowered to runtime-evaluable Python."""


class _RuntimeTranslator(ast.NodeTransformer):
    """Rewrite synth-syntax constructs into runtime-evaluable Python."""

    def visit_Call(self, node: ast.Call) -> ast.AST:
        # Handle quantifiers BEFORE recursing — we need the lambda
        # body intact to recognize the `Implies(<bounds>, body)`
        # pattern.  generic_visit would rewrite the Implies first
        # and lose the antecedent.
        if isinstance(node.func, ast.Name):
            fn = node.func.id
            if fn in ("ForAll", "Exists"):
                return self._lower_quantifier(fn, node)
            if fn == "Update":
                raise _Untranslatable(f"Update(...) inside a predicate")

        # For other calls (e.g., Implies, or arbitrary helpers like
        # `fib(k)`), recurse first then rewrite.
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == "Implies":
            if len(node.args) == 2:
                p, q = node.args
                return ast.BoolOp(
                    op=ast.Or(),
                    values=[ast.UnaryOp(op=ast.Not(), operand=p), q],
                )
        return node

    def _lower_quantifier(self, fn: str,
                          node: ast.Call) -> ast.AST:
        """`ForAll(lambda <vars>: Implies(<ant>, <cons>))` →
              `all(<cons> for v1 in range(0, UB) for v2 in range(0, UB) ...
                   if <ant>)`

        Strategy: rather than extract per-variable precise ranges
        (which fails for bilateral patterns like
        `0 ≤ p ≤ q < n ∧ q ≥ n-i ⇒ ...` where q has two lower
        bounds), iterate every variable over `range(0, UB)` and use
        the *original* antecedent as a comprehension filter.  UB is
        inferred from any `<var> < <expr>` or `<var> <= <expr>`
        pattern in the antecedent.

        This over-iterates (O(UB^|vars|) instead of just the valid
        bindings) but is always correct.  Acceptable cost for
        debugging-mode runtime checks; typical UB is a procedure
        input that's small at test time.
        """
        if len(node.args) != 1 or not isinstance(node.args[0], ast.Lambda):
            raise _Untranslatable(f"{fn} expects a lambda arg")
        lam = node.args[0]
        var_names = [a.arg for a in lam.args.args]
        body = lam.body

        if not (isinstance(body, ast.Call)
                and isinstance(body.func, ast.Name)
                and body.func.id == "Implies"
                and len(body.args) == 2):
            raise _Untranslatable(
                f"{fn} body is not `Implies(bounds, predicate)`; "
                f"can't infer iteration range")

        ant, cons = body.args
        ub = _find_iteration_bound(ant, var_names)
        if ub is None:
            raise _Untranslatable(
                f"{fn}'s antecedent has no numeric upper bound; "
                f"can't choose an iteration range")

        cons_translated = self.visit(cons)

        # Build generators.  All variables iterate over [0, UB);
        # the antecedent gates valid bindings on the LAST generator
        # (Python's comprehension semantics).
        generators = []
        for i, name in enumerate(var_names):
            gen = ast.comprehension(
                target=ast.Name(id=name, ctx=ast.Store()),
                iter=ast.Call(
                    func=ast.Name(id="range", ctx=ast.Load()),
                    args=[ast.Constant(value=0), ub],
                    keywords=[],
                ),
                ifs=[],
                is_async=0,
            )
            if i == len(var_names) - 1:
                gen.ifs = [ant]
            generators.append(gen)

        agg_name = "all" if fn == "ForAll" else "any"
        return ast.Call(
            func=ast.Name(id=agg_name, ctx=ast.Load()),
            args=[ast.GeneratorExp(
                elt=cons_translated, generators=generators)],
            keywords=[],
        )


def _find_iteration_bound(ant: ast.expr,
                          var_names: list[str]) -> ast.expr | None:
    """Scan the antecedent for any `<var> < <expr>` / `<var> <= <expr>`
    pattern where `<var>` is one of the quantified variables.  Return
    the first such `<expr>` (with `+1` added if `<=` rather than `<`).

    Used as the iteration upper bound — every quantified variable
    iterates over `[0, UB)`, and the antecedent filters out
    out-of-range bindings at runtime.
    """
    conjuncts: list[ast.expr] = []
    def walk(n: ast.expr) -> None:
        if isinstance(n, ast.BoolOp) and isinstance(n.op, ast.And):
            for v in n.values:
                walk(v)
        else:
            conjuncts.append(n)
    walk(ant)

    for c in conjuncts:
        if not isinstance(c, ast.Compare):
            continue
        operands = [c.left, *c.comparators]
        for i, op in enumerate(c.ops):
            left = operands[i]
            right = operands[i + 1]
            ln = left.id if isinstance(left, ast.Name) else None
            rn = right.id if isinstance(right, ast.Name) else None
            # `var < expr` or `var <= expr` (var on left, bound on right)
            if ln in var_names and rn not in var_names:
                if isinstance(op, ast.Lt):
                    return right
                if isinstance(op, ast.LtE):
                    return _add_one(right)
            # `expr > var` or `expr >= var` (bound on left, var on right)
            if rn in var_names and ln not in var_names:
                if isinstance(op, ast.Gt):
                    return left
                if isinstance(op, ast.GtE):
                    return _add_one(left)
    return None


def _add_one(node: ast.expr) -> ast.expr:
    """Build `<node> + 1` as an AST expression.  Used by
    `_find_iteration_bound` when the antecedent uses `<=` (the loop
    range needs `+1` since `range(stop)` is exclusive)."""
    return ast.BinOp(left=node, op=ast.Add(), right=ast.Constant(value=1))


# ─────────────────────────────────────────────────────────────────────
# Misc.
# ─────────────────────────────────────────────────────────────────────
def _format_tau(tau_atoms: Any) -> str:
    if isinstance(tau_atoms, list):
        if not tau_atoms:
            return "true"
        return " and ".join(f"({a})" for a in tau_atoms)
    return str(tau_atoms)
