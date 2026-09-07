"""Rust source emitter for synthesized Solution objects.

Phase 5.D.  Sibling of `emit_c.py` and `emit_py.py`.  Maps the IR
+ chosen atoms to compilable Rust function text.  Covers:

  - `int` (`i64`) and `int[]` parameters/locals
  - Mutable-vs-immutable slice borrows: an array that's both input
    and output → `&mut [i64]`; input-only → `&[i64]`; output-only
    → `&mut [i64]` (caller allocates)
  - Single int output not in inputs → return value
  - Multi int outputs → tuple return `(i64, i64, ...)` (Rust handles
    this natively — no C-style out-pointers needed)
  - `while` loops with proof-comment headers (invariant + ranking)
  - `if / else if` chains for SB(n>1)
  - parallel assignment, SSA-list assignment (Rust does NOT have
    multi-target tuple destructuring inline like Python's
    `a, b = b, a` — we use `std::mem::swap` for the simple swap
    case, else temp-dance)
  - array `Update` (single-write and nested-Update swap idiom,
    with temps captured before any writes)
  - recursive procedures (Phase 5.B-style Fpre guarding)

Not yet supported:

  - `int[][]` 2D arrays — same restriction as C emitter; the Python
    emitter handles 2D natively
  - Compound integer overflow — `i64` is large enough for the
    benchmarks; Rust panics on overflow in debug.  Build with
    `--release` if overflow becomes an issue.

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


def emit_rust(solution: Solution,
              problem: Problem,
              fname: str = "synth") -> str:
    """Render `solution` as a single Rust function `fname(...)`."""
    lines: list[str] = []

    # Top-of-file proof annotation.
    lines.append("// Synthesized by Pragna-successor "
                 "(proof-theoretic synthesis).")
    lines.append(f"//   pre  : {problem.pre}")
    lines.append(f"//   post : {problem.post}")

    # Allow non-snake_case names — many benchmarks use `A`, `X`, `Y`.
    lines.append("#[allow(non_snake_case, unused_assignments, "
                 "unused_mut, unused_variables, "
                 "clippy::needless_return, clippy::collapsible_if)]")

    # Signature.
    ret_type, params, ret_tuple = _signature(problem)
    if ret_type == "()":
        lines.append(f"pub fn {fname}({', '.join(params)}) {{")
    else:
        lines.append(f"pub fn {fname}({', '.join(params)}) -> "
                     f"{ret_type} {{")

    # Local declarations.  Combine:
    #   - problem.locals
    #   - int outputs that are NOT inputs (these become locals,
    #     returned at the end as tuple/single).
    input_names = {v.name for v in problem.inputs}
    extra_int_locals: list[Var] = [
        v for v in problem.outputs
        if v.type == "int" and v.name not in input_names
    ]
    all_locals = list(problem.locals) + extra_int_locals
    for v in all_locals:
        # Initialize int/bool locals to 0/false — analogous to
        # Phase 5.A's clang `-Wsometimes-uninitialized` workaround.
        # Rust would catch this as `use of possibly-uninitialized`,
        # so default-initialize.
        if v.type == "int":
            lines.append(f"    let mut {v.name}: i64 = 0;")
        elif v.type == "bool":
            lines.append(f"    let mut {v.name}: bool = false;")
        else:
            raise ValueError(f"unsupported local type for Rust: {v.type}")
    if all_locals:
        lines.append("")

    # Body.
    _emit_node(problem.template, solution.atoms, problem,
               lines, indent="    ", fname=fname)

    # Convey outputs.
    if ret_tuple is not None:
        lines.append("")
        lines.append(f"    {ret_tuple}")

    lines.append("}")
    return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────────
# Signature helpers.
# ─────────────────────────────────────────────────────────────────────
def _signature(problem: Problem) -> tuple[str, list[str], str | None]:
    """Decide return type and parameter list.

    Returns `(return_type, params, ret_tuple_expr)`:
      - `return_type` is "i64", "(i64, i64, ...)" or "()".
      - `params` is the parameter list.  Arrays that are both inputs
        and outputs become `&mut [i64]`; arrays only input become
        `&[i64]`; arrays only output become `&mut [i64]`.
      - `ret_tuple_expr` is the Rust expression to put at the
        function's tail (or None for void functions).
    """
    input_names = {v.name for v in problem.inputs}
    output_names = {v.name for v in problem.outputs}

    fresh_int_outs = [v for v in problem.outputs
                      if v.type == "int" and v.name not in input_names]
    int_in_and_out = [v for v in problem.outputs
                      if v.type == "int" and v.name in input_names]
    fresh_arr_outs = [v for v in problem.outputs
                      if v.type.endswith("[]") and v.name not in input_names]

    params: list[str] = []
    # Inputs first.  Determine mutability based on whether output too.
    for v in problem.inputs:
        if v.type == "int":
            # Python passes ints by value; Rust takes i64 by value.
            # If the int is ALSO an output, the body assigns to it,
            # so we need `mut` on the parameter binding.
            mut = "mut " if v.name in output_names else ""
            params.append(f"{mut}{v.name}: i64")
        elif v.type == "int[]":
            if v.name in output_names:
                params.append(f"{v.name}: &mut [i64]")
            else:
                params.append(f"{v.name}: &[i64]")
        elif v.type == "int[][]":
            # 2D:
            #   - input-only       → `&[&[i64]]`   (slice of slices).
            #   - input + output   → `&mut [Vec<i64>]`.  Rust's
            #     IndexMut on `&mut [Vec<i64>]` lets `A[i][j] = v`
            #     compile cleanly.  The caller passes a
            #     `&mut Vec<Vec<i64>>`'s slice view.
            if v.name in output_names:
                params.append(f"{v.name}: &mut [Vec<i64>]")
            else:
                params.append(f"{v.name}: &[&[i64]]")
        else:
            raise ValueError(f"unsupported input type for Rust: {v.type}")
    # Array outputs that aren't already inputs come in as mut slices.
    for v in fresh_arr_outs:
        if v.type == "int[][]":
            params.append(f"{v.name}: &mut [Vec<i64>]")
        else:
            params.append(f"{v.name}: &mut [i64]")

    # Return shape.
    # All int outputs (fresh + in-and-out) get returned by value.
    # In-and-out ints are returned because Rust passed them by value
    # in (i64), so the caller doesn't see mutations otherwise.
    all_int_outs = int_in_and_out + fresh_int_outs

    if not all_int_outs:
        return "()", params, None
    if len(all_int_outs) == 1:
        return "i64", params, all_int_outs[0].name
    inner = ", ".join("i64" for _ in all_int_outs)
    tup = ", ".join(v.name for v in all_int_outs)
    return f"({inner})", params, f"({tup})"


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
        lines.append(f"{indent}{prefix} {_rs_expr(guard)} {{")
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
    lines.append(f"{indent}// invariant {lid}: {_format_tau(tau)}")
    lines.append(f"{indent}// ranking   {lid}: {phi}")
    lines.append(f"{indent}while {_rs_expr(guard)} {{")
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
            lines.append(f"{indent}// skip")
        if has_break:
            lines.append(f"{indent}break;")
        return
    if isinstance(atom, list):
        for entry in atom:
            for var, rhs in entry.items():
                _emit_assignment(var, rhs, lines, indent)
        return
    lines.append(f"{indent}// unknown atom shape: {atom!r}")


# ─────────────────────────────────────────────────────────────────────
# Recursive-call emission.
# ─────────────────────────────────────────────────────────────────────
def _emit_recur_call(atom: dict,
                     problem: Problem,
                     lines: list[str],
                     indent: str,
                     fname: str) -> None:
    """Emit a recursive call site, wrapped in `if <Fpre@args>` so the
    binary doesn't infinite-recurse at the vacuous base case (the
    synthesizer's soundness depends on the IH firing only on Fpre-
    satisfying args; raw Rust recursion would loop forever)."""
    args_spec = atom.get("args", {})
    ret_spec  = atom.get("ret", {})

    # Build call args in input order with args_spec overrides.
    call_args = []
    for v in problem.inputs:
        if v.name in args_spec:
            call_args.append(_rs_expr(args_spec[v.name]))
        else:
            # For mutable slice borrows, pass through as a reborrow.
            if v.type == "int[]" and v.name in {o.name for o in problem.outputs}:
                call_args.append(v.name)
            else:
                call_args.append(v.name)
    args_str = ", ".join(call_args)

    # Fpre@args by whole-word substitution.
    fpre_at_args = problem.pre or "true"
    for v in sorted(problem.inputs, key=lambda x: -len(x.name)):
        repl = args_spec.get(v.name, v.name)
        fpre_at_args = re.sub(rf'\b{re.escape(v.name)}\b',
                              f"({repl})", fpre_at_args)
    guard_rs = _rs_expr(fpre_at_args)

    trivial_pre = (problem.pre or "").strip().lower() in ("", "true", "1")

    if not trivial_pre:
        lines.append(f"{indent}if {guard_rs} {{")
        body_indent = indent + "    "
    else:
        body_indent = indent

    input_names = {v.name for v in problem.inputs}
    fresh_int_outs = [v for v in problem.outputs
                      if v.type == "int" and v.name not in input_names]
    int_in_and_out = [v for v in problem.outputs
                      if v.type == "int" and v.name in input_names]
    fresh_arr_outs = [v for v in problem.outputs
                      if v.type.endswith("[]") and v.name not in input_names]
    in_place_arrays = [v for v in problem.outputs
                       if v.type.endswith("[]") and v.name in input_names]
    all_int_outs = int_in_and_out + fresh_int_outs

    if len(all_int_outs) == 1 and not fresh_arr_outs and not in_place_arrays:
        # Single-int return.
        rv = all_int_outs[0].name
        identity = (set(ret_spec.keys()) == {rv}
                    and ret_spec.get(rv, "").strip() == rv)
        if identity:
            lines.append(f"{body_indent}{rv} = {fname}({args_str});")
        else:
            tmp = f"_r_{rv}"
            lines.append(f"{body_indent}let {tmp}: i64 = "
                         f"{fname}({args_str});")
            for var, rhs in ret_spec.items():
                rhs_subst = re.sub(rf'\b{re.escape(rv)}\b', tmp, rhs)
                lines.append(f"{body_indent}{var} = {_rs_expr(rhs_subst)};")
    elif (not all_int_outs) and (in_place_arrays or fresh_arr_outs):
        # Array in-place (e.g., bubble_sort).
        lines.append(f"{body_indent}{fname}({args_str});")
        for var, rhs in ret_spec.items():
            _emit_assignment(var, rhs, lines, body_indent)
    else:
        lines.append(f"{body_indent}// recur shape not yet supported "
                     f"in Rust emitter: {atom}")

    if not trivial_pre:
        lines.append(f"{indent}}}")


# ─────────────────────────────────────────────────────────────────────
# Parallel-assignment dict.
# ─────────────────────────────────────────────────────────────────────
def _emit_parallel_dict(atom: dict,
                        lines: list[str],
                        indent: str) -> None:
    """Emit a parallel-assignment dict with parallel semantics.
    Mirrors emit_c.py's approach: capture temps if any scalar RHS
    references any LHS var."""
    update_items: list[tuple[str, str]] = []
    scalar_items: list[tuple[str, str]] = []
    for var, rhs in atom.items():
        (update_items if isinstance(rhs, str)
                         and rhs.strip().startswith("Update(")
                       else scalar_items).append((var, rhs))

    # Update items first (each captures its own array reads).
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
        temp_map: dict[str, str] = {}
        for var, rhs in scalar_items:
            tmp = f"__t_{var}"
            temp_map[var] = tmp
            lines.append(f"{indent}let {tmp}: i64 = {_rs_expr(rhs)};")
        for var, _ in scalar_items:
            lines.append(f"{indent}{var} = {temp_map[var]};")
    else:
        for var, rhs in scalar_items:
            _emit_assignment(var, rhs, lines, indent)


def _expr_references_any(rhs: Any, var_set: set[str]) -> bool:
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
    rhs_strip = rhs_str.strip()
    if rhs_strip == var:
        return
    if rhs_strip.startswith("Update("):
        if _emit_update_chain(var, rhs_strip, lines, indent):
            return
    lines.append(f"{indent}{var} = {_rs_expr(rhs_str)};")


# ─────────────────────────────────────────────────────────────────────
# Update chain handling.
# ─────────────────────────────────────────────────────────────────────
def _emit_update_chain(target_var: str,
                       rhs_str: str,
                       lines: list[str],
                       indent: str) -> bool:
    """Emit nested `Update` as Rust array writes.  Handles both 1D
    (3-arg) and 2D (4-arg `Update(A, i, j, v)` → `A[i][j] = v`).
    """
    try:
        tree = ast.parse(rhs_str, mode="eval")
    except SyntaxError:
        return False

    # Each chain entry: list of index AST nodes (1 for 1D, 2 for 2D)
    # plus the value expression.
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

    chain.reverse()

    def idx_rs(idx_node: ast.expr) -> str:
        return f"({_rs_expr(ast.unparse(idx_node))}) as usize"

    def _lhs(idxs: list[ast.expr]) -> str:
        return f"{target_var}" + "".join(
            f"[{idx_rs(i)}]" for i in idxs)

    if len(chain) == 1:
        idxs, val = chain[0]
        lines.append(f"{indent}{_lhs(idxs)} = "
                     f"{_rs_expr(ast.unparse(val))};")
        return True

    # Multi-write: capture every `target_var[expr]` read used in any
    # val BEFORE the writes (parallel-Update semantics).
    seen: dict[str, str] = {}
    counter = [0]
    for _idx, val in chain:
        _collect_reads(val, target_var, seen, counter)

    for read_str, tmp in seen.items():
        lines.append(f"{indent}let {tmp}: i64 = {_rs_expr(read_str)};")

    for idxs, val in chain:
        val_with_temps = _substitute_reads_str(
            ast.unparse(val), target_var, seen)
        lines.append(f"{indent}{_lhs(idxs)} = "
                     f"{_rs_expr(val_with_temps)};")
    return True


def _collect_reads(node: ast.AST,
                   target_var: str,
                   seen: dict[str, str],
                   counter: list[int]) -> None:
    if isinstance(node, ast.Subscript):
        if (isinstance(node.value, ast.Name)
                and node.value.id == target_var):
            read_str = ast.unparse(node)
            if read_str not in seen:
                seen[read_str] = f"__t{counter[0]}"
                counter[0] += 1
            return
    for child in ast.iter_child_nodes(node):
        _collect_reads(child, target_var, seen, counter)


def _substitute_reads_str(val_str: str,
                          target_var: str,
                          seen: dict[str, str]) -> str:
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
def _rs_expr(py_expr: Any) -> str:
    """Convert a Python-syntax expression string to Rust-syntax.

    Order matters: do the AST-based subscript cast FIRST (the input
    must still be valid Python syntax), then the boolean-operator
    substitutions (which produce `&&`/`||`/`!` — invalid Python).
    """
    if not isinstance(py_expr, str):
        return str(py_expr)

    # 1. AST rewrite: A[expr] → A[(expr) as usize].
    s = _cast_subscripts(py_expr)

    # 2. Boolean operators (whole-word).
    s = re.sub(r"\band\b", "&&", s)
    s = re.sub(r"\bor\b",  "||", s)
    s = re.sub(r"\bnot\b", "!",  s)

    return s


def _cast_subscripts(expr_str: str) -> str:
    """Rewrite `A[expr]` to `A[(expr) as usize]` for every Subscript
    in `expr_str`.  Uses Python's ast then dumps back."""
    try:
        tree = ast.parse(expr_str, mode="eval")
    except SyntaxError:
        return expr_str

    class CastSubscripts(ast.NodeTransformer):
        def visit_Subscript(self, n: ast.Subscript):
            self.generic_visit(n)
            slc = n.slice
            # Wrap in `(... as usize)` if not already an explicit
            # `as usize` cast.  We do this by wrapping the slice in a
            # Call to a sentinel — Python AST has no native `as` so
            # we emit using a placeholder and post-process the string.
            #
            # Simpler approach: render the slice via ast.unparse, wrap
            # textually, and substitute back as a Name node whose id
            # is the wrapped text.  Hacky but works for the
            # one-direction Python→Rust transpilation.
            inner = ast.unparse(slc)
            placeholder = f"({inner}) as usize"
            n.slice = ast.Name(id=placeholder, ctx=ast.Load())
            return n

    new_tree = CastSubscripts().visit(tree)
    out = ast.unparse(new_tree.body)
    return out


def _format_tau(tau_atoms: Any) -> str:
    if isinstance(tau_atoms, list):
        if not tau_atoms:
            return "true"
        return " and ".join(f"({a})" for a in tau_atoms)
    return str(tau_atoms)
