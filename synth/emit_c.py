"""C source emitter for synthesized Solution objects.

Phase 5.A.  Maps the IR + chosen atoms to compilable C function
text.  Covers:

  - `int` and `int[]` (pointer-decayed) parameters and locals
  - `while` loops with proof-comment headers (invariant + ranking)
  - `if / else if / else if` chains for SB(n>1)
  - parallel assignment, SSA-list assignment
  - array `Update` (single-write and the nested-Update swap idiom,
    with temps captured before any writes)
  - pre/post conditions as a leading block comment

Not yet supported:

  - `Recur`: recursive-procedure C emission needs its own design
    (procedure boundary, recursive call site, etc.).
  - Compound integer overflow / sized integer types — emitted as
    plain `int`.

The emitter walks `problem.template` and substitutes chosen atoms
from `solution.atoms`.  It does NOT re-verify; the Solution is
assumed sound (the synthesizer's correctness guarantee).
"""
from __future__ import annotations
import ast
import re
from typing import Any

from .ir import SB, Loop, Seq, Recur, Problem, Template, Var
from .result import Solution


def emit_c(solution: Solution,
           problem: Problem,
           fname: str = "synth") -> str:
    """Render `solution` as a single C function `fname(...)`."""
    lines: list[str] = []

    # Top-of-file proof annotation: pre/post + per-loop invariants.
    lines.append("/*")
    lines.append(" * Synthesized by Pragna-successor "
                 "(proof-theoretic synthesis).")
    lines.append(f" *   pre  : {problem.pre}")
    lines.append(f" *   post : {problem.post}")
    lines.append(" */")

    # Signature + how outputs are conveyed.
    ret_type, params, ret_var, out_pointer_ints = _signature(problem)
    lines.append(f"{ret_type} {fname}({', '.join(params)})")
    lines.append("{")

    # Local declarations.  Combine:
    #   - problem.locals
    #   - int outputs that are NOT inputs and NOT already array params
    #     (these become return/out-pointer locals)
    extra_int_locals: list[str] = []
    input_names = {v.name for v in problem.inputs}
    for v in problem.outputs:
        if v.type == "int" and v.name not in input_names:
            extra_int_locals.append(v.name)
    by_type: dict[str, list[str]] = {}
    for v in problem.locals:
        by_type.setdefault(v.type, []).append(v.name)
    if extra_int_locals:
        by_type.setdefault("int", []).extend(extra_int_locals)
    if by_type:
        for t, names in by_type.items():
            # Initialize int locals to 0 — clang's
            # `-Wsometimes-uninitialized` can't see that the coverage
            # constraint `⋁ g_i ≡ true` makes every code path assign
            # them, so we declare with a default to keep the C valid
            # under -Werror.  Arrays (int *) keep their default
            # uninitialized state; the caller passes them in.
            if t == "int" or t == "bool":
                decl = ", ".join(f"{n} = 0" for n in names)
            else:
                decl = ", ".join(names)
            lines.append(f"    {_c_type(t)} {decl};")
        lines.append("")

    # Body.
    _emit_node(problem.template, solution.atoms, problem,
               lines, indent="    ", fname=fname)

    # Convey outputs.
    if out_pointer_ints:
        lines.append("")
        for v in out_pointer_ints:
            lines.append(f"    *{v}_out = {v};")
    if ret_var is not None:
        lines.append(f"    return {ret_var};")

    lines.append("}")
    return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────────
# Signature helpers.
# ─────────────────────────────────────────────────────────────────────
def _signature(
        problem: Problem
) -> tuple[str, list[str], str | None, list[str]]:
    """Decide return type and parameter list.

    Returns `(return_type, params, ret_var, out_pointer_ints)`:
      - `return_type` is "int" or "void".
      - `params` is the parameter list, ordered: inputs first, then
        array outputs that aren't already inputs (in-place modify),
        then `int *<name>_out` for non-input int outputs that aren't
        the single return value.
      - `ret_var` is the int-output name that's returned (or None for
        void functions).
      - `out_pointer_ints` is the list of non-input int outputs that
        become `int *<name>_out` pointer params — the caller observes
        their final values via `*x_out = x;` writes at function exit.

    Single int output not in inputs → return value.  Multi int outputs
    or "int that's also an input" → pointer-out params.
    """
    input_names  = {v.name for v in problem.inputs}
    fresh_int_outs  = [v for v in problem.outputs
                       if v.type == "int" and v.name not in input_names]
    fresh_arr_outs  = [v for v in problem.outputs
                       if v.type.endswith("[]") and v.name not in input_names]

    params: list[str] = [_c_param(v) for v in problem.inputs]

    # Array outputs that aren't already inputs come in as pointer
    # params (in-place modify, no special suffix).
    for v in fresh_arr_outs:
        params.append(_c_param(v))

    ret_var: str | None = None
    out_pointer_ints: list[str] = []
    if len(fresh_int_outs) == 1:
        ret_var = fresh_int_outs[0].name
    else:
        # Multi int output (or zero — meaning all outputs are arrays
        # or in-place inputs).  Use pointer-out params for the ints.
        for v in fresh_int_outs:
            params.append(f"int *{v.name}_out")
            out_pointer_ints.append(v.name)

    ret_type = "int" if ret_var is not None else "void"
    return ret_type, params, ret_var, out_pointer_ints


def _c_type(t: str) -> str:
    if t == "int":     return "int"
    if t == "int[]":   return "int *"
    if t == "bool":    return "int"
    if t == "bool[]":  return "int *"
    if t == "int[][]":
        # 2D arrays as row-pointer arrays: `int **A`.  Caller
        # allocates rows as separate `int rowN[]` arrays and a
        # top-level `int *A[]` whose entries are the row pointers.
        # `A[i][j]` works natively (chained subscripts).
        return "int **"
    raise ValueError(f"unsupported type for C emission: {t!r}")


def _c_param(v: Var) -> str:
    return f"{_c_type(v.type)} {v.name}"


# ─────────────────────────────────────────────────────────────────────
# Node-level emission.
# ─────────────────────────────────────────────────────────────────────
def _emit_node(node: Template,
               atoms: dict[str, Any],
               problem: Problem,
               lines: list[str],
               indent: str,
               fname: str) -> None:
    if isinstance(node, SB):
        _emit_sb(node, atoms, problem, lines, indent, fname)
    elif isinstance(node, Loop):
        _emit_loop(node, atoms, problem, lines, indent, fname)
    elif isinstance(node, Seq):
        _emit_node(node.left,  atoms, problem, lines, indent, fname)
        _emit_node(node.right, atoms, problem, lines, indent, fname)
    elif isinstance(node, Recur):
        atom = atoms[f"s@{node.recur_id}"]
        _emit_transition(atom, lines, indent, problem, fname)
    else:
        raise TypeError(f"unknown template node: {type(node).__name__}")


def _emit_sb(node: SB,
             atoms: dict[str, Any],
             problem: Problem,
             lines: list[str],
             indent: str,
             fname: str) -> None:
    if node.n == 1:
        atom = atoms[f"s@{node.block_id}"]
        _emit_transition(atom, lines, indent, problem, fname)
        return
    for k in range(node.n):
        guard = atoms[f"g@{node.block_id}.{k}"]
        trans = atoms[f"s@{node.block_id}.{k}"]
        prefix = "if" if k == 0 else "else if"
        lines.append(f"{indent}{prefix} ({_c_expr(guard)}) {{")
        _emit_transition(trans, lines, indent + "    ", problem, fname)
        lines.append(f"{indent}}}")


def _emit_loop(node: Loop,
               atoms: dict[str, Any],
               problem: Problem,
               lines: list[str],
               indent: str,
               fname: str) -> None:
    lid = node.loop_id
    guard = atoms[f"g@{lid}"]
    tau   = atoms.get(f"tau@{lid}", [])
    phi   = atoms.get(f"phi@{lid}", "")
    lines.append(f"{indent}/* invariant {lid}: {_format_tau(tau)} */")
    lines.append(f"{indent}/* ranking   {lid}: {phi} */")
    lines.append(f"{indent}while ({_c_expr(guard)}) {{")
    _emit_node(node.body, atoms, problem, lines, indent + "    ", fname)
    lines.append(f"{indent}}}")


# ─────────────────────────────────────────────────────────────────────
# Transition emission.
# ─────────────────────────────────────────────────────────────────────
def _emit_transition(atom: Any,
                     lines: list[str],
                     indent: str,
                     problem: Problem,
                     fname: str) -> None:
    if isinstance(atom, dict) and atom.get("_recur"):
        _emit_recur_call(atom, problem, lines, indent, fname)
        return
    if isinstance(atom, dict):
        # K.B.IMPL-5: strip the `_break` flag; append `break;`.
        has_break = atom.get("_break") is True
        body = {k: v for k, v in atom.items() if not k.startswith("_")}
        if body:
            _emit_parallel_dict(body, lines, indent)
        elif not has_break:
            lines.append(f"{indent}/* skip */")
        if has_break:
            lines.append(f"{indent}break;")
        return
    if isinstance(atom, list):
        # SSA list — sequential semantics, each step sees prior LHS
        # values; no temp dance needed.
        for entry in atom:
            for var, rhs in entry.items():
                _emit_assignment(var, rhs, lines, indent)
        return
    lines.append(f"{indent}/* unknown atom shape: {atom!r} */")


# ─────────────────────────────────────────────────────────────────────
# Recursive-call emission (Phase 5.B).
# ─────────────────────────────────────────────────────────────────────
def _emit_recur_call(atom: dict,
                     problem: Problem,
                     lines: list[str],
                     indent: str,
                     fname: str) -> None:
    """Emit a recursive call site for a `_recur` atom.

    Shape: `{"_recur": True, "args": {input_name: expr_str, ...},
              "ret": {var_name: expr_str_over_call_outputs, ...}}`

    Strategy:
      1. Build the argument list in `problem.inputs` order, applying
         the `args` overrides (missing keys default to the var's
         current pre-state value).
      2. Wrap the entire call+ret in `if (<Fpre@args>) { ... }`.  This
         is essential for pure `~`-style recursive templates (top-
         level Recur, no explicit base case): the synthesizer's
         "vacuous Fpre at base" trick proves correctness when the
         IH fires only on Fpre-satisfying args, but a raw recursive
         C call would infinite-recurse.  Wrapping makes the binary
         actually terminate.  (For SB(n=2)-with-base-case templates,
         the user's outer guard already implies Fpre@args, and the
         wrap is just a redundant runtime check.)
      3. Emit the call body, choosing between three output shapes:
           - Single fresh-int output: identity ret emits
             `result = fname(args);`; non-identity captures into a
             temp `int _r_result = fname(args);` then applies the
             ret mapping.
           - Array in-place (output also an input): `fname(args);`,
             then apply ret transformations via the standard
             assignment emitter (handles Update chains).
           - Mixed shape: fall back to a TODO comment.
    """
    args_spec = atom.get("args", {})
    ret_spec  = atom.get("ret", {})

    # Build call args in input order, with args_spec overrides.
    call_args = []
    for v in problem.inputs:
        if v.name in args_spec:
            call_args.append(_c_expr(args_spec[v.name]))
        else:
            call_args.append(v.name)
    args_str = ", ".join(call_args)

    # Compute Fpre@args by whole-word substitution.  Substitute longer
    # var names first so a var named e.g. `n2` isn't clobbered by a
    # substitution rule for `n`.
    fpre_at_args = problem.pre or "1"
    for v in sorted(problem.inputs, key=lambda x: -len(x.name)):
        repl = args_spec.get(v.name, v.name)
        fpre_at_args = re.sub(rf'\b{re.escape(v.name)}\b',
                              f"({repl})", fpre_at_args)
    guard_c = _c_expr(fpre_at_args)

    # If Pre is trivially true, skip the wrap to keep the C clean.
    trivial_pre = (problem.pre or "").strip().lower() in ("", "true", "1")

    if not trivial_pre:
        lines.append(f"{indent}if ({guard_c}) {{")
        body_indent = indent + "    "
    else:
        body_indent = indent

    # Determine output shape.
    input_names = {v.name for v in problem.inputs}
    fresh_int_outs = [v for v in problem.outputs
                      if v.type == "int" and v.name not in input_names]
    fresh_arr_outs = [v for v in problem.outputs
                      if v.type.endswith("[]") and v.name not in input_names]
    # An array that's both an input and an output is "in-place" and
    # already part of the call args (passed by pointer).
    in_place_arrays = [v for v in problem.outputs
                       if v.type.endswith("[]") and v.name in input_names]

    if len(fresh_int_outs) == 1 and not fresh_arr_outs and not in_place_arrays:
        # Single-int return.
        rv = fresh_int_outs[0].name
        identity = (set(ret_spec.keys()) == {rv}
                    and ret_spec.get(rv, "").strip() == rv)
        if identity:
            lines.append(f"{body_indent}{rv} = {fname}({args_str});")
        else:
            tmp = f"_r_{rv}"
            lines.append(f"{body_indent}int {tmp} = {fname}({args_str});")
            for var, rhs in ret_spec.items():
                rhs_subst = re.sub(rf'\b{re.escape(rv)}\b', tmp, rhs)
                lines.append(f"{body_indent}{var} = {_c_expr(rhs_subst)};")
    elif (not fresh_int_outs) and (in_place_arrays or fresh_arr_outs):
        # Array in-place (most common: `int *A` modified through the
        # call).  Plain call, then apply any `ret` transformations
        # via the assignment emitter (which handles Update chains).
        lines.append(f"{body_indent}{fname}({args_str});")
        for var, rhs in ret_spec.items():
            _emit_assignment(var, rhs, lines, body_indent)
    else:
        # Mixed / unsupported.
        lines.append(f"{body_indent}/* recur shape not yet supported "
                     f"in C emitter: {atom} */")

    if not trivial_pre:
        lines.append(f"{indent}}}")


def _emit_parallel_dict(atom: dict,
                        lines: list[str],
                        indent: str) -> None:
    """Emit a parallel-assignment dict, respecting parallel semantics.

    If any scalar RHS references any LHS var (other than as the array
    target inside a Update chain — that case is handled by
    `_emit_update_chain`'s own temp capture), use a temp dance to
    preserve the simultaneous-evaluation semantics.

    Mixed Update + scalar assignments: emit the Update-rhs entries
    first (they only modify their arrays), then the scalar entries
    with temps if needed.  Note: if a scalar RHS references an array
    that was just Update'd, the order matters — flagged as a known
    limitation; benchmarks in this repo don't trigger it.
    """
    lhs_set = set(atom.keys())
    update_items: list[tuple[str, str]] = []
    scalar_items: list[tuple[str, str]] = []
    for var, rhs in atom.items():
        (update_items if isinstance(rhs, str)
                         and rhs.strip().startswith("Update(")
                       else scalar_items).append((var, rhs))

    # Emit Update items first.  Each one's _emit_update_chain captures
    # its own array reads before any writes.
    for var, rhs in update_items:
        _emit_assignment(var, rhs, lines, indent)

    if not scalar_items:
        return

    scalar_lhs = {v for v, _ in scalar_items}
    needs_temps = (
        len(scalar_items) > 1
        and any(_expr_references_any(r, scalar_lhs)
                for _, r in scalar_items)
    )

    if needs_temps:
        # Capture each RHS into a temp BEFORE any writes.
        temp_map: dict[str, str] = {}
        for var, rhs in scalar_items:
            tmp = f"__t_{var}"
            temp_map[var] = tmp
            lines.append(f"{indent}int {tmp} = {_c_expr(rhs)};")
        for var, _ in scalar_items:
            lines.append(f"{indent}{var} = {temp_map[var]};")
    else:
        for var, rhs in scalar_items:
            _emit_assignment(var, rhs, lines, indent)


def _expr_references_any(rhs: Any, var_set: set[str]) -> bool:
    """True if `rhs` (a Python-expression string) references any var
    in `var_set`.  AST-based for whole-word match; falls back to regex
    if parsing fails."""
    if not isinstance(rhs, str):
        return False
    try:
        tree = ast.parse(rhs, mode="eval")
    except SyntaxError:
        for v in var_set:
            if re.search(rf"\b{re.escape(v)}\b", rhs):
                return True
        return False
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id in var_set:
            return True
    return False


def _emit_assignment(var: str,
                     rhs_str: str,
                     lines: list[str],
                     indent: str) -> None:
    """Emit `var := rhs_str` as one or more C statements."""
    rhs_strip = rhs_str.strip()
    # Identity assignment `x = x` — skip.  Common case: a recur's
    # `ret: {A: A}` for in-place array procedures.
    if rhs_strip == var:
        return
    if rhs_strip.startswith("Update("):
        if _emit_update_chain(var, rhs_strip, lines, indent):
            return
    lines.append(f"{indent}{var} = {_c_expr(rhs_str)};")


# ─────────────────────────────────────────────────────────────────────
# Array Update handling.
# ─────────────────────────────────────────────────────────────────────
def _emit_update_chain(target_var: str,
                       rhs_str: str,
                       lines: list[str],
                       indent: str) -> bool:
    """Try to emit `target_var := Update(... Update(target_var, i, v) ...,
    j, w)` as C statements.  Returns True on success; False if the
    rhs doesn't match the expected Update-chain pattern (falls back
    to the default scalar assignment, which will produce invalid C —
    that's a signal the pattern needs extension).
    """
    try:
        tree = ast.parse(rhs_str, mode="eval")
    except SyntaxError:
        return False

    # Walk outer-to-inner.  Each chain entry is a list of index
    # exprs (length 1 for 1D Update, length 2 for 2D
    # `Update(A, i, j, v)`) plus the val expression.
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
    if not isinstance(node, ast.Name) or node.id != target_var:
        return False

    # Inner-first emission order.
    chain.reverse()

    def _lhs(idxs: list[ast.expr]) -> str:
        return f"{target_var}" + "".join(
            f"[{ast.unparse(i)}]" for i in idxs)

    if len(chain) == 1:
        idxs, val = chain[0]
        lines.append(f"{indent}{_lhs(idxs)} = "
                     f"{_c_expr(ast.unparse(val))};")
        return True

    # Multi-write: capture every `target_var[expr]` read referenced
    # anywhere in any val expression BEFORE issuing any writes.  This
    # preserves the semantics of nested `Update` (each outer Update's
    # val reads the original array, not the after-inner-write array).
    seen: dict[str, str] = {}
    counter = [0]
    for _idx, val in chain:
        _collect_reads(val, target_var, seen, counter)

    for read_str, tmp in seen.items():
        lines.append(f"{indent}int {tmp} = {_c_expr(read_str)};")

    for idxs, val in chain:
        val_with_temps = _substitute_reads_str(
            ast.unparse(val), target_var, seen)
        lines.append(f"{indent}{_lhs(idxs)} = "
                     f"{_c_expr(val_with_temps)};")
    return True


def _collect_reads(node: ast.AST,
                   target_var: str,
                   seen: dict[str, str],
                   counter: list[int]) -> None:
    """Walk `node`, find every `target_var[expr]` Subscript, and
    register a fresh temp for each distinct read expression."""
    if isinstance(node, ast.Subscript):
        if (isinstance(node.value, ast.Name)
                and node.value.id == target_var):
            read_str = ast.unparse(node)
            if read_str not in seen:
                seen[read_str] = f"__t{counter[0]}"
                counter[0] += 1
            return  # don't recurse into the slot
    for child in ast.iter_child_nodes(node):
        _collect_reads(child, target_var, seen, counter)


def _substitute_reads_str(val_str: str,
                          target_var: str,
                          seen: dict[str, str]) -> str:
    """Replace `target_var[expr]` reads in `val_str` with the temp
    names recorded in `seen`.  Uses a single-pass AST rewrite so
    nested patterns are handled cleanly."""
    tree = ast.parse(val_str, mode="eval")

    class Repl(ast.NodeTransformer):
        def visit_Subscript(self, n: ast.Subscript):
            if (isinstance(n.value, ast.Name)
                    and n.value.id == target_var):
                read_str = ast.unparse(n)
                if read_str in seen:
                    return ast.copy_location(
                        ast.Name(id=seen[read_str], ctx=ast.Load()), n)
            self.generic_visit(n)
            return n

    new_tree = Repl().visit(tree)
    return ast.unparse(new_tree.body)


# ─────────────────────────────────────────────────────────────────────
# Expression conversion.
# ─────────────────────────────────────────────────────────────────────
def _c_expr(py_expr: Any) -> str:
    """Convert a Python-syntax expression string to C-syntax.

    Replaces Python keyword operators with their C equivalents
    (whole-word matches only, so a variable named `nor` isn't mauled).
    Other constructs (`Update`, `A[k]`, arithmetic, comparisons) are
    already C-compatible.
    """
    if not isinstance(py_expr, str):
        return str(py_expr)
    s = py_expr
    s = re.sub(r"\band\b", "&&", s)
    s = re.sub(r"\bor\b",  "||", s)
    s = re.sub(r"\bnot\b", "!",  s)
    return s


def _format_tau(tau_atoms: Any) -> str:
    """Render a conjunctive-τ choice (list of atom strings) for the
    proof comment.  Falls back to str() for unexpected shapes."""
    if isinstance(tau_atoms, list):
        if not tau_atoms:
            return "true"
        return " and ".join(f"({a})" for a in tau_atoms)
    return str(tau_atoms)
