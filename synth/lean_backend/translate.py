"""IR atom strings → Lean theorem text.

Translates Python-syntax expression strings (as authored by the user
in `Problem.atoms`, `Problem.pre`, `Problem.post`) directly to Lean 4
syntax, then assembles them into theorems indexed by obligation kind.

Ring 1 Day 2 covers `ranking-lb` (loop ranking function ≥ 0).  Other
kinds (ranking-decrease, safety-inductive) follow the same shape and
will be added as we hit them.

Translation philosophy
----------------------
Stay at the atom-string level — never touch the Z3 expression.  This
preserves the user-authored predicate structure: each atom becomes a
NAMED hypothesis (`h_tau_0`, `h_tau_1`, ...) rather than disappearing
into a flat `And(...)` conjunction.  Trade-off: we re-walk the
Python AST rather than reusing `synth.expr`'s Z3 walker, but the
walks are independent translations to different target languages,
so sharing buys little.

For now we target a pure-core Lean (no mathlib).  All arithmetic is
over `Int`.  Array reads `A[i]` translate to function application
`A i` under the `Int → Int` encoding from `RESEARCH.LEAN.md` §3.3
(mathlib's nicer `Function.update` waits until Ring 2).
"""
from __future__ import annotations

import ast
from typing import Any

from ..ir import Problem, Template, SB, Loop, Seq, Recur
from ..result import Solution
from ..constraints import _has_break_branch


# ─────────────────────────────────────────────────────────────────────
# Python expression → Lean expression.
# ─────────────────────────────────────────────────────────────────────
def lean_expr(py_str: str) -> str:
    """Translate a Python-syntax expression string to Lean 4 syntax.

    Supported (in order of how Day 2 needs them):
      - Names, integer literals
      - Comparisons (==, !=, <, <=, >, >=) → (=, ≠, <, ≤, >, ≥)
      - BinOp (+ - * / %) → (+ - * / %)
      - UnaryOp (-x, not x) → (-x, ¬x)
      - BoolOp (and, or) → (∧, ∨)
      - `Implies(p, q)` → `p → q`
      - `ForAll(lambda x, y: body)` → `∀ x y, body`
      - `Exists(lambda x: body)` → `∃ x, body`
      - `Subscript A[i]` → `A i` (function-app under Int → Int)
      - `Update(A, i, v)` → `(store A i v)` (matches SynthLean.Basic
        `store`; mathlib's `Function.update` lands in Ring 2)
      - Python ternary `a if c else b` → `if c then a else b`
    """
    if not isinstance(py_str, str):
        return str(py_str)
    try:
        tree = ast.parse(py_str.strip(), mode="eval")
    except SyntaxError as e:
        raise ValueError(
            f"lean_expr: not a parseable Python expression: "
            f"{py_str!r} ({e})"
        ) from e
    return _walk(tree.body)


def _walk(node: ast.AST) -> str:
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            return "True" if node.value else "False"
        if isinstance(node.value, int):
            return str(node.value)
        if node.value is True:
            return "True"
        if node.value is False:
            return "False"
        raise ValueError(f"lean_expr: unsupported constant {node.value!r}")

    if isinstance(node, ast.Name):
        if node.id == "true":
            return "True"
        if node.id == "false":
            return "False"
        return node.id

    if isinstance(node, ast.UnaryOp):
        x = _walk(node.operand)
        if isinstance(node.op, ast.USub):
            return f"(-{x})"
        if isinstance(node.op, ast.Not):
            return f"(¬ {x})"
        raise ValueError(f"lean_expr: unsupported UnaryOp {node.op}")

    if isinstance(node, ast.BinOp):
        l = _walk(node.left)
        r = _walk(node.right)
        op = {
            ast.Add: "+",
            ast.Sub: "-",
            ast.Mult: "*",
            ast.Div: "/",
            ast.FloorDiv: "/",
            ast.Mod: "%",
        }.get(type(node.op))
        if op is None:
            raise ValueError(f"lean_expr: unsupported BinOp {node.op}")
        return f"({l} {op} {r})"

    if isinstance(node, ast.BoolOp):
        op = "∧" if isinstance(node.op, ast.And) else "∨"
        parts = [_walk(v) for v in node.values]
        return "(" + f" {op} ".join(parts) + ")"

    if isinstance(node, ast.Compare):
        # Chained comparison: a < b < c → (a < b) ∧ (b < c).
        result_parts: list[str] = []
        left = _walk(node.left)
        for op, comp in zip(node.ops, node.comparators):
            right = _walk(comp)
            op_str = {
                ast.Eq: "=",
                ast.NotEq: "≠",
                ast.Lt: "<",
                ast.LtE: "≤",
                ast.Gt: ">",
                ast.GtE: "≥",
            }.get(type(op))
            if op_str is None:
                raise ValueError(f"lean_expr: unsupported cmpop {op}")
            result_parts.append(f"({left} {op_str} {right})")
            left = right
        if len(result_parts) == 1:
            return result_parts[0]
        return "(" + " ∧ ".join(result_parts) + ")"

    if isinstance(node, ast.Subscript):
        a = _walk(node.value)
        idx_node = (node.slice.value
                    if isinstance(node.slice, ast.Index)
                    else node.slice)
        i = _walk(idx_node)
        # Under Int → Int encoding, A[i] is function application.
        # Indices are Int — no coercions needed.
        return f"({a} {i})"

    if isinstance(node, ast.IfExp):
        cond = _walk(node.test)
        a = _walk(node.body)
        b = _walk(node.orelse)
        return f"(if {cond} then {a} else {b})"

    if isinstance(node, ast.Call):
        return _walk_call(node)

    raise ValueError(
        f"lean_expr: unsupported AST node "
        f"{type(node).__name__}: {ast.unparse(node)!r}"
    )


def _walk_call(node: ast.Call) -> str:
    if not isinstance(node.func, ast.Name):
        raise ValueError(f"lean_expr: non-Name call func {ast.unparse(node)!r}")
    name = node.func.id

    if name == "Implies":
        if len(node.args) != 2:
            raise ValueError("Implies takes 2 args")
        p = _walk(node.args[0])
        q = _walk(node.args[1])
        return f"({p} → {q})"

    if name in ("ForAll", "Exists"):
        if len(node.args) != 1:
            raise ValueError(f"{name} takes 1 arg (a lambda)")
        lam = node.args[0]
        if not isinstance(lam, ast.Lambda):
            raise ValueError(f"{name}: arg must be a lambda")
        bound_names = [a.arg for a in lam.args.args]
        body = _walk(lam.body)
        quant = "∀" if name == "ForAll" else "∃"
        # K.A.3 — name-suffix convention matching synth/expr.py:
        #   `*_arr` → Int → Int (array of ints).
        #   `*_mat` → Int → Int → Int (2D array).
        #   otherwise → Int.
        # Each bound var gets its own typed binder so the emitted
        # Lean parses correctly when a UF expects function types.
        def _bind_type(nm: str) -> str:
            if nm.endswith("_arr"):
                return "Int → Int"
            if nm.endswith("_mat"):
                return "Int → Int → Int"
            return "Int"
        binders = " ".join(
            f"({nm} : {_bind_type(nm)})" for nm in bound_names
        )
        return f"({quant} {binders}, {body})"

    if name == "Update":
        if len(node.args) == 3:
            a = _walk(node.args[0])
            i = _walk(node.args[1])
            v = _walk(node.args[2])
            return f"(store {a} {i} {v})"
        if len(node.args) == 4:
            # 2D Update: `Update(A, i, j, v)` → `(store2d A i j v)`.
            # `store2d` is defined in `SynthLean/Basic.lean`.
            a = _walk(node.args[0])
            i = _walk(node.args[1])
            j = _walk(node.args[2])
            v = _walk(node.args[3])
            return f"(store2d {a} {i} {j} {v})"
        raise ValueError(f"Update: 3 or 4 args, got {len(node.args)}")

    # Uninterpreted function or unknown call — emit as Lean fn application.
    args = " ".join(_walk(a) for a in node.args)
    return f"({name} {args})"


# ─────────────────────────────────────────────────────────────────────
# Helpers shared across obligation kinds.
# ─────────────────────────────────────────────────────────────────────
def _state_binders(problem: Problem,
                   prime_set: set[str] | None = None,
                   post_skip_set: set[str] | None = None,
                   ) -> tuple[list[str], list[str], list[str]]:
    """Return `(int_names, arr_names, binder_lines)` for the program's
    state variables (inputs ∪ outputs ∪ locals, deduped).

    - `prime_set`: vars to bind also as `<name>'` (loop-exit / post-
      transition state).
    - `post_skip_set`: vars to bind also as `<name>_post` (FINAL state
      after a post-loop skip block rewrites a loop-modified var).
      Used for the array_rotate_left-style pattern.  Vars in
      post_skip_set are typically ALSO in prime_set (they have
      distinct loop-exit AND final values).

    Note: `arr_names` is the combined list of all array-typed vars
    (1D and 2D) for the caller's convenience.  Internally the binder
    lines split 1D and 2D since they have different Lean types.
    """
    seen: set[str] = set()
    int_names: list[str] = []
    arr1d_names: list[str] = []
    arr2d_names: list[str] = []
    for v in problem.inputs + problem.outputs + problem.locals:
        if v.name in seen:
            continue
        seen.add(v.name)
        if v.type == "int":
            int_names.append(v.name)
        elif v.type == "int[]":
            arr1d_names.append(v.name)
        elif v.type == "int[][]":
            arr2d_names.append(v.name)
    binders: list[str] = []
    if int_names:
        binders.append(f"({' '.join(int_names)} : Int)")
    if arr1d_names:
        binders.append(f"({' '.join(arr1d_names)} : Int → Int)")
    if arr2d_names:
        binders.append(f"({' '.join(arr2d_names)} : Int → Int → Int)")
    if prime_set:
        int_primes  = [f"{n}'" for n in int_names  if n in prime_set]
        arr1d_primes = [f"{n}'" for n in arr1d_names if n in prime_set]
        arr2d_primes = [f"{n}'" for n in arr2d_names if n in prime_set]
        if int_primes:
            binders.append(f"({' '.join(int_primes)} : Int)")
        if arr1d_primes:
            binders.append(f"({' '.join(arr1d_primes)} : Int → Int)")
        if arr2d_primes:
            binders.append(f"({' '.join(arr2d_primes)} : Int → Int → Int)")
    if post_skip_set:
        int_post  = [f"{n}_post" for n in int_names  if n in post_skip_set]
        arr1d_post = [f"{n}_post" for n in arr1d_names if n in post_skip_set]
        arr2d_post = [f"{n}_post" for n in arr2d_names if n in post_skip_set]
        if int_post:
            binders.append(f"({' '.join(int_post)} : Int)")
        if arr1d_post:
            binders.append(f"({' '.join(arr1d_post)} : Int → Int)")
        if arr2d_post:
            binders.append(f"({' '.join(arr2d_post)} : Int → Int → Int)")
    return int_names, arr1d_names + arr2d_names, binders


def _find_loop_body_block_id(template: Template, loop_id: str,
                             branch_idx: int | None = None) -> str:
    """Find the SB block that is the body of `Loop(loop_id)` and
    return its block_id.

    For SB(n=1): branch_idx must be None (no branch); returns the
    single block_id.

    For SB(n>1): branch_idx selects which branch's block_id to
    return.  Per-branch block ids follow the convention
    `<sb.block_id>.<branch_idx>` (see expand.py).
    """
    target_loop = _find_loop(template, loop_id)
    if target_loop is None:
        raise ValueError(f"loop {loop_id!r} not found in template")
    body = target_loop.body
    if not isinstance(body, SB):
        raise NotImplementedError(
            f"loop {loop_id!r}: body is {type(body).__name__}; only "
            f"SB loop bodies supported"
        )
    if body.n == 1:
        if branch_idx is not None and branch_idx != 0:
            raise ValueError(
                f"loop {loop_id!r}: SB body is single-branch but "
                f"branch_idx={branch_idx} requested"
            )
        return body.block_id
    if branch_idx is None:
        raise ValueError(
            f"loop {loop_id!r}: SB body has {body.n} branches; "
            f"caller must specify branch_idx"
        )
    if not (0 <= branch_idx < body.n):
        raise ValueError(
            f"loop {loop_id!r}: branch_idx={branch_idx} out of range "
            f"for SB(n={body.n})"
        )
    return f"{body.block_id}.{branch_idx}"


def _find_loop(template: Template, loop_id: str) -> Loop | None:
    if isinstance(template, Loop):
        if template.loop_id == loop_id:
            return template
        inner = _find_loop(template.body, loop_id)
        if inner is not None:
            return inner
    elif isinstance(template, Seq):
        for half in (template.left, template.right):
            found = _find_loop(half, loop_id)
            if found is not None:
                return found
    return None


def _top_level_loops(template: Template) -> list[Loop]:
    """Walk top-level chain (no recursion into Loop bodies)
    collecting Loop nodes in left-to-right order."""
    if isinstance(template, Loop):
        return [template]
    if isinstance(template, Seq):
        return _top_level_loops(template.left) + _top_level_loops(template.right)
    return []


def _find_top_level_multibranch_sb(template: Template):
    """Find an SB(n>1) at the TOP LEVEL of the template (not
    inside any Loop).  Used by `theorem_for_coverage` for
    procedure-level SB(n>1) coverage where `sc.loop_id is None`.

    Returns the first matching SB found via a left-to-right walk
    of top-level Seq chains; returns None if no such SB exists.
    Does NOT recurse into Loop bodies — those would have their
    own coverage constraints with non-None loop_ids.
    """
    if isinstance(template, SB):
        if template.n > 1:
            return template
        return None
    if isinstance(template, Seq):
        left = _find_top_level_multibranch_sb(template.left)
        if left is not None:
            return left
        return _find_top_level_multibranch_sb(template.right)
    # Loop / Recur / etc. — don't recurse.
    return None


def _lean_type(t: str) -> str:
    """Translate a `Problem.Var.type` / UF arg/return type to Lean
    syntax.  Returns the BARE type without surrounding parens — the
    caller is responsible for parenthesizing in contexts where the
    type might be an argument of a function-type expression."""
    if t == "int":     return "Int"
    if t == "bool":    return "Bool"
    if t == "int[]":   return "Int → Int"
    if t == "int[][]": return "Int → Int → Int"
    raise ValueError(f"_lean_type: unsupported {t!r}")


def _lean_arg_type(t: str) -> str:
    """Type as it should appear as an ARGUMENT in a function-type
    expression.  Function-type arguments need parens (else
    `Int → Int → Int → Int` parses as a flat 3-int curry rather
    than `(Int → Int) → Int → Int` we'd intend).
    """
    s = _lean_type(t)
    return f"({s})" if " → " in s else s


def _free_program_vars(axiom_py: str, problem: Problem) -> list:
    """Return the program-variable references in `axiom_py` that are
    NOT shadowed by a lambda binder.  Used by `emit_axiom_declarations`
    to quantify each axiom over the program vars it references (so
    file-level `axiom ...` declarations stay well-formed).
    """
    program_vars = {v.name: v for v in problem.inputs
                    + problem.outputs + problem.locals}
    seen: set[str] = set()
    out = []
    bound_stack: list[set[str]] = []

    class Visit(ast.NodeVisitor):
        def visit_Lambda(self, n: ast.Lambda) -> None:
            bound_stack.append({a.arg for a in n.args.args})
            self.generic_visit(n)
            bound_stack.pop()

        def visit_Name(self, n: ast.Name) -> None:
            if (n.id in program_vars
                    and not any(n.id in s for s in bound_stack)
                    and n.id not in seen):
                seen.add(n.id)
                out.append(program_vars[n.id])

    tree = ast.parse(axiom_py.strip(), mode="eval")
    Visit().visit(tree.body)
    return out


def emit_axiom_declarations(problem: Problem) -> str:
    """Emit Lean `axiom` declarations for the problem's uninterpreted
    functions and user-supplied axioms.

    Output shape:

        axiom paths : Int → Int → Int
        axiom user_axiom_0 : ∀ j : Int, j ≥ 0 → paths 0 j = 1
        ...

    Two well-formedness concerns:

    1. **Function-type arguments** (e.g., `int[]` for a UF over arrays)
       are parenthesized so the signature parses correctly:

         sum : (Int → Int) → Int → Int     ← right
         sum : Int → Int → Int → Int        ← wrong (3-int curry)

    2. **Free program-variable references** are wrapped in an outer
       ∀.  User axioms often reference program inputs by name (e.g.,
       sum_array's `sum(A, 0) == 0` references `A`).  At file-level
       axiom scope these are unbound; we add `∀ A : Int → Int, …`
       so the axiom is well-formed.  Lambda-bound vars are not
       quantified again.

    Returns the empty string when there are no UFs or axioms.
    """
    lines: list[str] = []
    for name, arg_types, ret_type in problem.uninterpreted:
        parts = [_lean_arg_type(t) for t in arg_types] + [_lean_type(ret_type)]
        typed = " → ".join(parts)
        lines.append(f"axiom {name} : {typed}")
    for idx, axiom_str in enumerate(problem.axioms):
        free = _free_program_vars(axiom_str, problem)
        body = lean_expr(axiom_str)
        if free:
            binders = " ".join(f"({v.name} : {_lean_type(v.type)})"
                               for v in free)
            body = f"∀ {binders}, {body}"
        lines.append(f"axiom user_axiom_{idx} : {body}")
    if not lines:
        return ""
    return "\n".join(lines) + "\n"


def _prime_expr(py_str: str, transitioned: set[str]) -> str:
    """Rewrite `py_str` so every Name reference to a transitioned var
    becomes the primed name (e.g., `N - i` with `transitioned={i}` →
    `N - i'`).  Returns the rewritten string in Python-AST form (it'll
    pass through `lean_expr` next)."""
    if not transitioned:
        return py_str
    tree = ast.parse(py_str.strip(), mode="eval")

    class Prime(ast.NodeTransformer):
        def visit_Name(self, n: ast.Name):
            if n.id in transitioned:
                # Use a placeholder identifier ending in "_PRIMED" which
                # lean_expr emits verbatim, then post-process.  Avoids
                # Python tokenizer rejecting `i'` as a single Name.
                return ast.copy_location(
                    ast.Name(id=f"{n.id}_PRIMED", ctx=n.ctx), n
                )
            return n

    new_tree = Prime().visit(tree)
    py_primed = ast.unparse(new_tree.body)
    return py_primed


def _post_expr(py_str: str, post_set: set[str]) -> str:
    """Rewrite `py_str` so every Name reference to a var in `post_set`
    becomes `<name>_post`.  Used to bind the FINAL (after post-loop
    skip) state of vars that the skip block rewrites for loop-modified
    vars (e.g., array_rotate_left's `A := Update(A, n-1, saved)` after
    the loop that rotates A).  The `_post` suffix is a plain identifier
    (no apostrophe placeholder dance needed)."""
    if not post_set:
        return py_str
    tree = ast.parse(py_str.strip(), mode="eval")

    class Post(ast.NodeTransformer):
        def visit_Name(self, n: ast.Name):
            if n.id in post_set:
                return ast.copy_location(
                    ast.Name(id=f"{n.id}_post", ctx=n.ctx), n
                )
            return n

    new_tree = Post().visit(tree)
    return ast.unparse(new_tree.body)


def _finalize_primes(lean_str: str) -> str:
    """Convert the `_PRIMED` suffix placeholders to Lean's `'` suffix."""
    import re
    return re.sub(r"\b(\w+)_PRIMED\b", r"\1'", lean_str)


# ─────────────────────────────────────────────────────────────────────
# Theorem assembly per obligation kind.
# ─────────────────────────────────────────────────────────────────────
def theorem_for_ranking_lb(problem: Problem,
                           solution: Solution,
                           loop_id: str,
                           theorem_name: str | None = None) -> str:
    """Emit a Lean theorem for the loop's ranking-LB obligation:

        τ(state) ∧ pre  ⇒  ϕ(state) ≥ 0

    Each chosen τ atom becomes a named hypothesis (`h_tau_0`, ...).
    `pre` becomes `h_pre`.  The conclusion is `ϕ ≥ 0`.

    Returns Lean source text (no surrounding namespace; caller drops
    it into a `.lean` file under `lean/SynthLean/`).
    """
    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    phi_atoms = solution.atoms.get(f"phi@{loop_id}", [])
    if not phi_atoms:
        raise ValueError(f"loop {loop_id}: solution has no phi")
    if isinstance(phi_atoms, list):
        if len(phi_atoms) != 1:
            raise ValueError(
                f"loop {loop_id}: expected single phi, got "
                f"{len(phi_atoms)} ({phi_atoms!r})"
            )
        phi_expr = phi_atoms[0]
    else:
        phi_expr = phi_atoms

    _, _, binders = _state_binders(problem)
    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for i, atom in enumerate(tau_atoms):
        binders.append(f"(h_tau_{i} : {lean_expr(atom)})")

    conclusion = f"{lean_expr(phi_expr)} ≥ 0"

    # Tactic: omega handles linear integer arithmetic and treats
    # nonlinear products as opaque variables — sufficient for our
    # ranking-LB obligations which reduce to `(x - k) ≥ 0 ← x ≥ k`
    # regardless of what `k` is structurally.
    tactic = "omega"

    name = theorem_name or f"{loop_id}_phi_lb"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    # Silence "unused variable" warnings — many τ atoms aren't load-
    # bearing for the ranking-LB obligation specifically (e.g.,
    # intsqrt's `v = i*i` doesn't constrain `phi = x - (i-1)²`), but
    # they're still part of the chosen invariant.  Day 4+ may use the
    # unused-variable info to attribute "which atom matters for which
    # obligation", but for now silence to keep CI logs clean.
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"  {tactic}\n"
    )


def theorem_for_ranking_decrease(problem: Problem,
                                 solution: Solution,
                                 loop_id: str,
                                 theorem_name: str | None = None,
                                 branch_idx: int | None = None) -> str:
    """Emit a Lean theorem for the loop's ranking-decrease obligation:

        τ(pre) ∧ guard(pre) ∧ trans(pre → post)  ⇒  ϕ(pre) > ϕ(post)

    The loop body must be a single `SB(n=1)` with a parallel-dict
    transition.  Variables on the transition's LHS get primed forms
    in the binders (`x'`, `i'`, ...); the post-state ϕ substitutes
    primed names for those vars.
    """
    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    phi_atoms = solution.atoms.get(f"phi@{loop_id}", [])
    if not phi_atoms:
        raise ValueError(f"loop {loop_id}: solution has no phi")
    phi_expr = phi_atoms[0] if isinstance(phi_atoms, list) else phi_atoms
    # For SB(n>1) loop bodies, the loop's per-loop guard `g@<loop_id>`
    # is OPTIONAL; the BRANCH guard `g@<body_id>.<branch_idx>` is the
    # one that fires.  When branch_idx is None (SB(n=1)), the
    # per-loop guard is used.  Otherwise the branch guard.
    if branch_idx is None:
        guard_atoms = solution.atoms.get(f"g@{loop_id}", [])
        if not guard_atoms:
            raise ValueError(f"loop {loop_id}: solution has no guard")
        guard_expr = (guard_atoms[0]
                      if isinstance(guard_atoms, list) else guard_atoms)
    else:
        # For SB(n>1) inside a Loop: we need BOTH the loop's guard
        # (i.e. g@L0, the while-condition) AND the branch guard
        # (g@B1.<i>).  Combine as a conjunction.
        loop_guards = solution.atoms.get(f"g@{loop_id}", [])
        loop_guard_expr = (loop_guards[0]
                           if isinstance(loop_guards, list) else loop_guards)
        # Branch guard from body's block_id with the branch suffix.
        sb_body_block = _find_loop_body_block_id(problem.template, loop_id,
                                                 branch_idx=branch_idx)
        branch_guards = solution.atoms.get(f"g@{sb_body_block}", [])
        if not branch_guards:
            raise ValueError(
                f"branch {sb_body_block}: solution has no branch guard"
            )
        branch_guard_expr = (branch_guards[0]
                             if isinstance(branch_guards, list)
                             else branch_guards)
        # Conjoin: (loop_guard) ∧ (branch_guard).  Use Python `and`
        # expression which lean_expr handles.
        if loop_guard_expr:
            guard_expr = (
                f"({loop_guard_expr}) and ({branch_guard_expr})"
            )
        else:
            guard_expr = branch_guard_expr

    # Find the loop body's SB block_id and pull its transition atom.
    body_id = _find_loop_body_block_id(problem.template, loop_id,
                                       branch_idx=branch_idx)
    trans_atom = solution.atoms.get(f"s@{body_id}")
    if trans_atom is None:
        raise ValueError(f"body {body_id}: solution has no transition")
    if not isinstance(trans_atom, dict):
        raise NotImplementedError(
            f"body {body_id}: transition is {type(trans_atom).__name__}; "
            f"Day 3 only supports parallel-dict transitions"
        )
    if trans_atom.get("_recur"):
        raise NotImplementedError(
            f"body {body_id}: recur transition not yet supported in "
            f"Lean backend"
        )

    transitioned: set[str] = set(trans_atom.keys())

    # Binders: pre-state vars + primed post-state vars (only for
    # transitioned names).
    _, _, binders = _state_binders(problem, prime_set=transitioned)

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for i, atom in enumerate(tau_atoms):
        binders.append(f"(h_tau_{i} : {lean_expr(atom)})")
    binders.append(f"(h_guard : {lean_expr(guard_expr)})")
    for var, rhs in trans_atom.items():
        # The RHS reads PRE-state values (parallel semantics), so we
        # do NOT prime its variable references.
        var_p = f"{var}'"
        binders.append(f"(h_trans_{var} : {var_p} = {lean_expr(rhs)})")

    # Conclusion: ϕ(pre) > ϕ(post).  ϕ(post) is ϕ with transitioned
    # vars primed.
    phi_pre  = lean_expr(phi_expr)
    phi_post = _finalize_primes(lean_expr(_prime_expr(phi_expr, transitioned)))
    conclusion = f"{phi_pre} > {phi_post}"

    # Tactic: omega handles linear obligations.  Nonlinear ϕ (e.g.,
    # intsqrt's `x - (i-1)²` vs `x - i²`) needs nlinarith or a manual
    # have-chain; those land in Day 4+ with mathlib.
    tactic = "omega"

    name = theorem_name or f"{loop_id}_phi_decrease"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"  {tactic}\n"
    )


# ---------- COST_INVS §2 wiring: cost-* translators ----------

# Tactic chain for cost-* obligations.  Tries cheap dispatchers
# first (omega for linear, ring_nf+omega for polynomial identity)
# then expensive nlinarith for nonlinear inequalities.  Cited
# lemmas in CostLemmas.lean are reachable via the `open` block
# at the top of the emitted theorem.
_COST_TACTIC_CHAIN = (
    "first | omega | (ring_nf; omega) | nlinarith | "
    "(simp only [mul_comm, mul_add, add_mul]; ring_nf; omega) | "
    "linarith"
)


def theorem_for_cost_lb(problem: Problem,
                        solution: Solution,
                        loop_id: str,
                        theorem_name: str | None = None) -> str:
    """COST_INVS §1 (A) — cost lower bound: τ ⇒ cost@L ≥ 0.

    Parallel to `theorem_for_ranking_lb`, with `cost@L` in place of
    `phi@L`.  Tactic chain handles linear + polynomial cases.
    """
    tau_atoms  = solution.atoms.get(f"tau@{loop_id}", [])
    cost_atoms = solution.atoms.get(f"cost@{loop_id}", [])
    if not cost_atoms:
        raise ValueError(f"loop {loop_id}: solution has no cost@L")
    cost_expr = (cost_atoms[0] if isinstance(cost_atoms, list)
                 else cost_atoms)

    _, _, binders = _state_binders(problem)
    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for i, atom in enumerate(tau_atoms):
        binders.append(f"(h_tau_{i} : {lean_expr(atom)})")

    conclusion = f"{lean_expr(cost_expr)} ≥ 0"
    name = theorem_name or f"{loop_id}_cost_lb"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\n"
        f"set_option linter.unusedSimpArgs false in\n"
        f"open SynthLean.CostLemmas in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"  {_COST_TACTIC_CHAIN}\n"
    )


def theorem_for_cost_decrement(problem: Problem,
                               solution: Solution,
                               loop_id: str,
                               theorem_name: str | None = None,
                               branch_idx: int | None = None) -> str:
    """COST_INVS §1 (B) — cost decrement for SB-bodied loops:

        τ(pre) ∧ guard(pre) ∧ trans(pre → post)
          ⇒  cost@L(pre) ≥ 1 + cost@L(post)

    First-slice limitation: handles only SB(n=1) / SB(n>1) loop
    bodies (body_cost = 1).  Nested-loop body cost composition
    (§1.5 case) NOT yet translatable — the cost-decrement for
    Loop(non-SB) body requires reconstructing the per-item body
    cost in atom terms over fresh intermediate state bindings,
    which is the next sub-slice (TODO).

    For SB(n=1), the translator follows `theorem_for_ranking_decrease`'s
    shape exactly, swapping `phi@L` for `cost@L` and the
    conclusion's inequality (`>` becomes `≥ 1 + ...`).
    """
    tau_atoms  = solution.atoms.get(f"tau@{loop_id}", [])
    cost_atoms = solution.atoms.get(f"cost@{loop_id}", [])
    if not cost_atoms:
        raise ValueError(f"loop {loop_id}: solution has no cost@L")
    cost_expr = (cost_atoms[0] if isinstance(cost_atoms, list)
                 else cost_atoms)
    if branch_idx is None:
        guard_atoms = solution.atoms.get(f"g@{loop_id}", [])
        if not guard_atoms:
            raise ValueError(f"loop {loop_id}: solution has no guard")
        guard_expr = (guard_atoms[0] if isinstance(guard_atoms, list)
                      else guard_atoms)
    else:
        loop_guards = solution.atoms.get(f"g@{loop_id}", [])
        loop_guard_expr = (loop_guards[0] if isinstance(loop_guards, list)
                           else loop_guards)
        sb_body_block = _find_loop_body_block_id(problem.template, loop_id,
                                                 branch_idx=branch_idx)
        branch_guards = solution.atoms.get(f"g@{sb_body_block}", [])
        if not branch_guards:
            raise ValueError(
                f"branch {sb_body_block}: solution has no branch guard")
        branch_guard_expr = (branch_guards[0]
                             if isinstance(branch_guards, list)
                             else branch_guards)
        if loop_guard_expr:
            guard_expr = f"({loop_guard_expr}) and ({branch_guard_expr})"
        else:
            guard_expr = branch_guard_expr

    body_id = _find_loop_body_block_id(problem.template, loop_id,
                                       branch_idx=branch_idx)
    trans_atom = solution.atoms.get(f"s@{body_id}")
    if trans_atom is None:
        raise ValueError(f"body {body_id}: solution has no transition")
    if not isinstance(trans_atom, dict):
        raise NotImplementedError(
            f"body {body_id}: transition is {type(trans_atom).__name__}; "
            f"cost-decrement only supports parallel-dict transitions"
        )
    if trans_atom.get("_recur"):
        raise NotImplementedError(
            f"body {body_id}: recur transition not yet supported by "
            f"cost-decrement translator"
        )

    transitioned: set[str] = set(trans_atom.keys())
    _, _, binders = _state_binders(problem, prime_set=transitioned)

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for i, atom in enumerate(tau_atoms):
        binders.append(f"(h_tau_{i} : {lean_expr(atom)})")
    binders.append(f"(h_guard : {lean_expr(guard_expr)})")
    for var, rhs in trans_atom.items():
        var_p = f"{var}'"
        binders.append(f"(h_trans_{var} : {var_p} = {lean_expr(rhs)})")

    cost_pre  = lean_expr(cost_expr)
    cost_post = _finalize_primes(
        lean_expr(_prime_expr(cost_expr, transitioned)))
    # body_cost = 1 in this first slice.
    conclusion = f"{cost_pre} ≥ 1 + ({cost_post})"

    name = theorem_name or f"{loop_id}_cost_decrement"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\n"
        f"set_option linter.unusedSimpArgs false in\n"
        f"open SynthLean.CostLemmas in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"  {_COST_TACTIC_CHAIN}\n"
    )


def _find_loop_node(template: Template, loop_id: str):
    """Find the Loop node in `template` whose loop_id matches, recursing
    into Loop bodies and Seq children."""
    if isinstance(template, Loop):
        if template.loop_id == loop_id:
            return template
        return _find_loop_node(template.body, loop_id)
    if isinstance(template, Seq):
        for sub in (template.left, template.right):
            found = _find_loop_node(sub, loop_id)
            if found is not None:
                return found
    return None


def theorem_for_cost_decrement_chain(problem: Problem,
                                     solution: Solution,
                                     loop_id: str,
                                     theorem_name: str | None = None
                                     ) -> str:
    """COST_INVS §1.5 Lean wiring — chain-aware cost-decrement for
    Loops with non-SB bodies (Seq containing inner Loops).

    Emits per-state binders for each item-boundary in the body chain,
    transition hypotheses per item (SB → trans + frame, Loop →
    τ_inner exit + ¬g_inner + frame), and concludes with:

        cost@L_outer(pre) ≥ body_cost(states) + cost@L_outer(post)

    where body_cost = Σ over body items of:
        SB        → 1
        Loop(L_in)→ cost@L_in evaluated at the inner loop's entry
                    state (i.e., the chain state JUST BEFORE the
                    inner Loop item).

    The tactic chain combines omega / ring_nf+omega / nlinarith,
    optionally citing CostLemmas's named identities for the
    quadratic polynomial cases (bubble_sort_cost shape).
    """
    # Find the outer Loop node by ID + its body items.
    outer_loop = _find_loop_node(problem.template, loop_id)
    if outer_loop is None:
        raise ValueError(
            f"cost-decrement-chain: loop {loop_id} not found in template"
        )
    body_items = _linearize(outer_loop.body)
    n_items = len(body_items)
    if n_items < 1:
        raise ValueError(
            f"cost-decrement-chain: loop {loop_id} body has no items"
        )

    # State chain: state[0] = body pre, state[k+1] = state after item k.
    chain_binders, state_to_name = _chain_state_binders(
        problem, n_items + 1
    )
    pre_state = state_to_name[0]
    post_state = state_to_name[n_items]

    binders = list(chain_binders)
    # Pre on inputs at state[0].
    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        renamed = _rename_state(problem.pre, pre_state)
        binders.append(f"(h_pre : {lean_expr(renamed)})")

    # Outer-loop τ at body pre-state.
    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    for i_a, atom in enumerate(tau_atoms):
        renamed = _rename_state(atom, pre_state)
        binders.append(f"(h_tau_outer_{i_a} : {lean_expr(renamed)})")

    # Outer-loop guard at body pre-state.
    g_atoms = solution.atoms.get(f"g@{loop_id}", [])
    if g_atoms:
        g_expr = g_atoms[0] if isinstance(g_atoms, list) else g_atoms
        renamed = _rename_state(g_expr, pre_state)
        binders.append(f"(h_g_outer : {lean_expr(renamed)})")

    # Per-item transition hypotheses.
    for k, item in enumerate(body_items):
        _emit_chain_item_hyps(
            item, state_to_name[k], state_to_name[k + 1],
            problem, solution, binders, suffix=f"item{k}",
        )

    # body_cost = Σ component costs.
    body_cost_terms: list[str] = []
    for k, item in enumerate(body_items):
        if isinstance(item, SB):
            body_cost_terms.append("1")
        elif isinstance(item, Loop):
            inner_lid = item.loop_id
            inner_cost = solution.atoms.get(f"cost@{inner_lid}", [])
            if not inner_cost:
                raise ValueError(
                    f"cost-decrement-chain: inner Loop {inner_lid} "
                    f"has no cost@L hole"
                )
            inner_cost_expr = (inner_cost[0]
                               if isinstance(inner_cost, list)
                               else inner_cost)
            # Inner cost evaluated at this Loop item's entry state =
            # state[k] (the chain state BEFORE the Loop transition
            # produces state[k+1]).
            renamed = _rename_state(inner_cost_expr, state_to_name[k])
            body_cost_terms.append(f"({lean_expr(renamed)})")
        else:
            raise NotImplementedError(
                f"cost-decrement-chain: item type {type(item).__name__} "
                f"not yet supported"
            )
    body_cost_str = " + ".join(body_cost_terms) if body_cost_terms else "0"

    # Outer cost@L evaluated at pre and post.
    cost_atoms = solution.atoms.get(f"cost@{loop_id}", [])
    if not cost_atoms:
        raise ValueError(f"loop {loop_id}: solution has no cost@L")
    cost_expr = (cost_atoms[0] if isinstance(cost_atoms, list)
                 else cost_atoms)
    cost_pre = lean_expr(_rename_state(cost_expr, pre_state))
    cost_post = lean_expr(_rename_state(cost_expr, post_state))

    conclusion = f"{cost_pre} ≥ ({body_cost_str}) + ({cost_post})"

    name = theorem_name or f"{loop_id}_cost_decrement_chain"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\n"
        f"set_option linter.unusedSimpArgs false in\n"
        f"open SynthLean.CostLemmas in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"  {_COST_TACTIC_CHAIN}\n"
    )


def theorem_for_safety_inductive(problem: Problem,
                                 solution: Solution,
                                 loop_id: str,
                                 theorem_name: str | None = None,
                                 branch_idx: int | None = None) -> str:
    """Emit a Lean theorem for the loop's safety-inductive obligation:

        τ(pre) ∧ guard(pre) ∧ trans(pre → post)  ⇒  τ(post)

    For SB(n>1) loop bodies, `branch_idx` selects which branch's
    guard + transition atoms to use; the emitted theorem covers
    just THAT branch's induction.  The synthesizer emits one
    safety constraint per branch, so per-branch translation is
    the natural fit.

    The conclusion is the conjunction of all chosen τ atoms with
    transitioned vars primed.  The tactic chain
    `subst_eqs; refine ⟨..⟩; all_goals first | omega | nlinarith`
    handles linear AND nonlinear conjuncts.

    Requires mathlib (`subst_eqs`, `nlinarith` are mathlib tactics).
    """
    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    if not tau_atoms:
        raise ValueError(f"loop {loop_id}: solution has no τ")
    # Guard: for SB(n=1), use the loop's guard.  For SB(n>1),
    # conjoin the loop's guard AND the branch's guard.
    loop_guards = solution.atoms.get(f"g@{loop_id}", [])
    if branch_idx is None:
        if not loop_guards:
            raise ValueError(f"loop {loop_id}: solution has no guard")
        guard_expr = (loop_guards[0]
                      if isinstance(loop_guards, list) else loop_guards)
    else:
        loop_guard_expr = (loop_guards[0]
                           if isinstance(loop_guards, list) and loop_guards
                           else (loop_guards or None))
        sb_body_block = _find_loop_body_block_id(problem.template, loop_id,
                                                 branch_idx=branch_idx)
        branch_guards = solution.atoms.get(f"g@{sb_body_block}", [])
        if not branch_guards:
            raise ValueError(
                f"branch {sb_body_block}: solution has no branch guard"
            )
        branch_guard_expr = (branch_guards[0]
                             if isinstance(branch_guards, list)
                             else branch_guards)
        if loop_guard_expr:
            guard_expr = (
                f"({loop_guard_expr}) and ({branch_guard_expr})"
            )
        else:
            guard_expr = branch_guard_expr

    body_id = _find_loop_body_block_id(problem.template, loop_id,
                                       branch_idx=branch_idx)
    trans_atom = solution.atoms.get(f"s@{body_id}")
    if trans_atom is None:
        raise ValueError(f"body {body_id}: solution has no transition")
    if not isinstance(trans_atom, dict):
        raise NotImplementedError(
            f"body {body_id}: transition is {type(trans_atom).__name__}; "
            f"Day 4 only supports parallel-dict transitions"
        )
    if trans_atom.get("_recur"):
        raise NotImplementedError(
            f"body {body_id}: recur transition not yet supported"
        )

    transitioned: set[str] = set(trans_atom.keys())
    _, _, binders = _state_binders(problem, prime_set=transitioned)

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for i, atom in enumerate(tau_atoms):
        binders.append(f"(h_tau_{i} : {lean_expr(atom)})")
    binders.append(f"(h_guard : {lean_expr(guard_expr)})")
    for var, rhs in trans_atom.items():
        var_p = f"{var}'"
        binders.append(f"(h_trans_{var} : {var_p} = {lean_expr(rhs)})")

    # Conclusion: ⋀ τ atoms with primed vars.
    primed_taus = [
        _finalize_primes(lean_expr(_prime_expr(atom, transitioned)))
        for atom in tau_atoms
    ]
    # Tactic chain: layered fallbacks per goal.
    #   - assumption: direct hypothesis match (handles `h_tau_k`
    #     conjuncts unchanged from pre-state).
    #   - omega: linear int arithmetic.
    #   - nlinarith: polynomial identities (handles sumi/mul-style
    #     inductive nonlinearity).
    #   - aesop: mathlib's general-purpose proof search.
    #   - The array-Store fallback: introduce binders, unfold
    #     store/store2d, split the resulting if-then-else into
    #     cases, then close each case with omega/aesop.  This is
    #     Day 7's response to the column-0-preservation conjunct
    #     pattern from grid_paths: position not on the updated
    #     cell ⇒ store2d ≡ A, then apply the pre-state hypothesis.
    # `(aesop; done)` (and similar) require the tactic to fully
    # close the goal; otherwise `first` moves to the next branch.
    # Without `done`, aesop's partial progress shadows the
    # array-Store fallback chain — see Day 7 trace.
    #
    # `solve_by_elim` recursively tries to apply each local
    # hypothesis (with discharged side-conditions via the side
    # tactic, here `omega`).  For `L i q = paths i q` with
    # `h_tau_7 : ∀q, 0 ≤ q ∧ q < j → L i q = paths i q` plus
    # `q ≤ j` and `q ≠ j` in context, solve_by_elim chains
    # `apply h_tau_7; omega`.
    # `simp_all` gets a set including user_axiom_* names so the
    # recurrence axioms (e.g., `sum(A, k+1) = sum(A, k) + A[k]` in
    # sum_array) are used as rewrites.  Without these in the simp
    # set, Lean can't reduce a goal like `sum A i + A i = sum A
    # (i+1)` (Day 11 sum_array trace).
    n_axioms = len(problem.axioms)
    _axiom_names = [f"user_axiom_{i}" for i in range(n_axioms)]
    _simp_set = ", ".join(["store", "store2d"] + _axiom_names)
    # Each fallback wrapped in `(... ; done)` so the branch only
    # claims success if the goal is fully closed; otherwise `first`
    # moves to the next alternative.  Without `done`, a partial-
    # progress branch can leave the goal in a worse state (Day 7,
    # Lesson #43).
    _simp_cfg = "(config := { failIfUnchanged := false })"
    _simp = f"simp_all {_simp_cfg} [{_simp_set}]"
    _GENERIC_TACTIC = (
        f"first "
        f"| assumption "
        f"| omega "
        f"| nlinarith "
        f"| ({_simp}; done) "
        f"| (aesop; done) "
        f"| ({_simp}; first | rfl | omega | nlinarith | (aesop; done)) "
        f"| (intros; {_simp}; "
        f"   first | omega | nlinarith | (aesop; done) "
        f"   | (split_ifs <;> first | omega | nlinarith "
        f"      | (solve_by_elim (config := {{maxDepth := 6}})) "
        f"      | aesop))"
    )
    if len(primed_taus) == 1:
        conclusion = primed_taus[0]
        tactic_body = (
            "  subst_eqs\n"
            f"  {_GENERIC_TACTIC}\n"
        )
    else:
        conclusion = " ∧ ".join(f"({p})" for p in primed_taus)
        markers = ", ".join(["?_"] * len(primed_taus))
        tactic_body = (
            "  subst_eqs\n"
            f"  refine ⟨{markers}⟩\n"
            f"  all_goals ({_GENERIC_TACTIC})\n"
        )

    name = theorem_name or f"{loop_id}_inductive"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"{tactic_body}"
    )


def theorem_for_break_bundle(problem: Problem,
                             solution: Solution,
                             loop_id: str,
                             theorem_name: str | None = None,
                             branch_idx: int | None = None,
                             enclosing_loop_id: str | None = None) -> str:
    """K.B.IMPL-4 / K.D.IMPL-4 — emit a Lean theorem for a
    break-branch's post-bundle obligation:

      Top-level Loop (no enclosing):
        Fpre ∧ τ(body_in) ∧ g(body_in) ∧ branch_guard ∧ trans
            ⇒ Fpost(body_out)

      Nested Loop (enclosing_loop_id != None) — K.D.2.b:
        Fpre ∧ τ(body_in) ∧ g(body_in) ∧ branch_guard ∧ trans
            ⇒ τ_enclosing(body_out)

    Same shape as `theorem_for_safety_inductive` but with the
    conclusion being either Fpost (top-level) or τ of the
    enclosing loop (nested), with vars primed where the
    transition modifies them.  branch_idx is required — break
    bundles always belong to a specific SB branch.
    """
    if branch_idx is None:
        raise ValueError(
            "theorem_for_break_bundle requires branch_idx"
        )
    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    # Allow empty τ — the break exit could be valid with no
    # invariant atoms.  In practice every loop has at least one.

    loop_guards = solution.atoms.get(f"g@{loop_id}", [])
    loop_guard_expr = (loop_guards[0]
                       if isinstance(loop_guards, list) and loop_guards
                       else (loop_guards or None))
    sb_body_block = _find_loop_body_block_id(problem.template, loop_id,
                                             branch_idx=branch_idx)
    branch_guards = solution.atoms.get(f"g@{sb_body_block}", [])
    if not branch_guards:
        raise ValueError(
            f"branch {sb_body_block}: solution has no branch guard"
        )
    branch_guard_expr = (branch_guards[0]
                         if isinstance(branch_guards, list)
                         else branch_guards)
    if loop_guard_expr:
        guard_expr = f"({loop_guard_expr}) and ({branch_guard_expr})"
    else:
        guard_expr = branch_guard_expr

    body_id = _find_loop_body_block_id(problem.template, loop_id,
                                       branch_idx=branch_idx)
    trans_atom = solution.atoms.get(f"s@{body_id}")
    if trans_atom is None:
        raise ValueError(f"body {body_id}: solution has no transition")
    if not isinstance(trans_atom, dict):
        raise NotImplementedError(
            f"body {body_id}: transition is {type(trans_atom).__name__}; "
            "break-bundle currently only supports parallel-dict atoms"
        )

    # The transition keys include any `_break` / `_recur` flags;
    # strip them when computing the set of vars actually written.
    transitioned: set[str] = {
        k for k in trans_atom.keys() if not k.startswith("_")
    }
    _, _, binders = _state_binders(problem, prime_set=transitioned)

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for i, atom in enumerate(tau_atoms):
        binders.append(f"(h_tau_{i} : {lean_expr(atom)})")
    binders.append(f"(h_guard : {lean_expr(guard_expr)})")
    for var, rhs in trans_atom.items():
        if var.startswith("_"):
            continue
        var_p = f"{var}'"
        binders.append(f"(h_trans_{var} : {var_p} = {lean_expr(rhs)})")

    # Conclusion depends on context:
    #   Top-level Loop (enclosing_loop_id is None): Fpost.
    #   Nested Loop: conjunction of τ_enclosing atoms.
    # Both with vars primed where transition modifies them.
    if enclosing_loop_id is not None:
        enc_tau = solution.atoms.get(f"tau@{enclosing_loop_id}", [])
        if not enc_tau:
            # Vacuous enclosing τ → trivially True.
            conclusion_src = "true"
        elif len(enc_tau) == 1:
            conclusion_src = enc_tau[0]
        else:
            conclusion_src = " and ".join(f"({a})" for a in enc_tau)
        primed_post = _finalize_primes(
            lean_expr(_prime_expr(conclusion_src, transitioned))
        )
    else:
        primed_post = _finalize_primes(
            lean_expr(_prime_expr(problem.post, transitioned))
        )

    n_axioms = len(problem.axioms)
    _axiom_names = [f"user_axiom_{i}" for i in range(n_axioms)]
    _simp_set = ", ".join(["store", "store2d"] + _axiom_names)
    _simp_cfg = "(config := { failIfUnchanged := false })"
    _simp = f"simp_all {_simp_cfg} [{_simp_set}]"
    _GENERIC_TACTIC = (
        f"first "
        f"| assumption "
        f"| omega "
        f"| nlinarith "
        f"| ({_simp}; done) "
        f"| (aesop; done) "
        f"| ({_simp}; first | rfl | omega | nlinarith | (aesop; done)) "
        f"| (intros; {_simp}; "
        f"   first | omega | nlinarith | (aesop; done))"
    )
    tactic_body = (
        "  subst_eqs\n"
        f"  {_GENERIC_TACTIC}\n"
    )

    name = theorem_name or f"{loop_id}_break_bundle_{branch_idx}"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{primed_post} := by\n"
        f"{tactic_body}"
    )


def theorem_for_coverage(problem: Problem,
                         solution: Solution,
                         loop_id: str,
                         theorem_name: str | None = None) -> str:
    """Emit a Lean theorem for the coverage obligation:

        Pre ∧ τ_loop ∧ g_loop  ⇒  ⋁ g_branch_i

    For a multi-branch SB(n>1) body of `Loop(loop_id)`, the coverage
    condition says: whenever the loop's body executes (loop guard
    holds with τ in scope), AT LEAST ONE branch's guard must hold —
    i.e., the SB's branch guards are jointly complete.

    Going through Lean (rather than Z3) sidesteps the
    quantifier-instantiation wedge on axiom-heavy problems where
    Z3's verifier carries UF axioms and can return UNKNOWN on the
    coverage check even when the proof is structurally linear (e.g.,
    majority_element coverage = `cnt = 0 ∨ cnt > 0` is trivial from
    `cnt ≥ 0` but Z3 stumbles on the bm_inv quantified τ atom).

    Only handles the case where the loop's body is a SB(n>1) (the
    sole multi-branch context that emits coverage constraints
    today).  Nested-SB-in-Loop-body NOT supported.
    """
    # When loop_id is None, this is a procedure-level SB(n>1)
    # coverage (e.g. tail-recursive `if found == 1 then recur else
    # return` shape).  No enclosing loop to look up; find the
    # top-level SB(n>1) directly in the template AND collect τ
    # atoms from any TOP-LEVEL Loops in the same chain (their
    # invariants are in scope at the SB's pre-state via the
    # chain-bundle path).
    if loop_id is None:
        sb_body = _find_top_level_multibranch_sb(problem.template)
        if sb_body is None:
            raise ValueError(
                "coverage: loop_id is None and no top-level "
                "SB(n>1) found in template"
            )
        # Collect τ atoms from every top-level Loop appearing
        # BEFORE this SB.  Their invariants hold at the SB's
        # pre-state via the chain-bundle composition.
        tau_atoms = []
        for top_loop in _top_level_loops(problem.template):
            tau_atoms.extend(
                solution.atoms.get(f"tau@{top_loop.loop_id}", [])
            )
        loop_guard_expr = None
    else:
        tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
        loop_guards = solution.atoms.get(f"g@{loop_id}", [])
        loop_guard_expr = (loop_guards[0]
                           if isinstance(loop_guards, list) and loop_guards
                           else (loop_guards or None))

        target_loop = _find_loop(problem.template, loop_id)
        if target_loop is None:
            raise ValueError(f"coverage: loop {loop_id!r} not found")
        sb_body = target_loop.body
        if not isinstance(sb_body, SB):
            raise NotImplementedError(
                f"coverage: loop body is {type(sb_body).__name__}; only "
                f"SB(n>1) bodies emit coverage constraints"
            )
    if sb_body.n <= 1:
        raise ValueError(
            f"coverage: SB(n={sb_body.n}) — should be n>1"
        )

    # Collect branch guards.
    branch_guard_exprs: list[str] = []
    for b_idx in range(sb_body.n):
        gs = solution.atoms.get(f"g@{sb_body.block_id}.{b_idx}", [])
        if not gs:
            raise ValueError(
                f"coverage: branch {b_idx} has no guard"
            )
        branch_guard_exprs.append(
            gs[0] if isinstance(gs, list) else gs
        )

    # No transitions for coverage — purely a τ + guard implication.
    _, _, binders = _state_binders(problem, prime_set=set())

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for i, atom in enumerate(tau_atoms):
        binders.append(f"(h_tau_{i} : {lean_expr(atom)})")
    if loop_guard_expr:
        binders.append(f"(h_g_loop : {lean_expr(loop_guard_expr)})")

    # Conclusion: disjunction of branch guards.
    branch_lean_exprs = [lean_expr(g) for g in branch_guard_exprs]
    if len(branch_lean_exprs) == 1:
        conclusion = branch_lean_exprs[0]
    else:
        conclusion = " ∨ ".join(f"({g})" for g in branch_lean_exprs)

    # Tactic chain: omega first (most coverage proofs are linear);
    # fall back to nlinarith / aesop / decide / split.
    n_axioms = len(problem.axioms)
    _axiom_names = [f"user_axiom_{i}" for i in range(n_axioms)]
    _simp_set = ", ".join(["store", "store2d"] + _axiom_names)
    _simp_cfg = "(config := { failIfUnchanged := false })"
    _simp = f"simp_all {_simp_cfg} [{_simp_set}]"
    _GENERIC = (
        f"first "
        f"| omega "
        f"| nlinarith "
        f"| (decide) "
        f"| ({_simp}; first | omega | nlinarith | (aesop; done) | decide) "
        f"| (aesop; done) "
        f"| (by_contra h; push_neg at h; omega)"
    )

    name = theorem_name or f"{loop_id}_coverage"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"  {_GENERIC}\n"
    )


def theorem_for_entry_bundle(problem: Problem,
                             solution: Solution,
                             loop_id: str,
                             theorem_name: str | None = None) -> str:
    """Emit a Lean theorem for the loop-entry bundle safety obligation:

        Fpre ∧ init_atoms  ⇒  τ_loop(at the loop's entry state)

    For templates shaped `SB(init) >> Loop(<loop_id>) >> ...`, the
    "entry bundle" verifies that the chosen τ holds when the loop
    first executes — i.e., after the init transition completes.

    Init's effect: each init atom is an equation `<var> = <rhs>`
    over the pre-state plus the assigned var.  We use prime
    convention: pre-state vars stay unprimed, post-init vars get
    primed names (`x'`).  The τ atoms in the goal reference primed
    vars (since they hold at the post-init / loop-entry state).
    """
    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    if not tau_atoms:
        raise ValueError(f"entry-bundle: loop {loop_id} has no τ atoms")

    # Find init block — the SB BEFORE the loop in the template.
    # Template iteration: walk Seq tree, find SB followed by Loop(loop_id).
    init_block_id = _find_init_block_id(problem.template, loop_id)
    if init_block_id is None:
        raise NotImplementedError(
            f"entry-bundle: no SB(init) block found before "
            f"Loop({loop_id})"
        )
    init_atom = solution.atoms.get(f"s@{init_block_id}", {})
    if not isinstance(init_atom, dict):
        raise NotImplementedError(
            "entry-bundle: init transition must be a parallel-dict atom"
        )
    if init_atom.get("_recur"):
        raise NotImplementedError(
            "entry-bundle: recur init transitions not supported"
        )

    transitioned: set[str] = set(init_atom.keys())
    _, _, binders = _state_binders(problem, prime_set=transitioned)

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    for var, rhs in init_atom.items():
        var_p = f"{var}'"
        binders.append(f"(h_init_{var} : {var_p} = {lean_expr(rhs)})")

    primed_taus = [
        _finalize_primes(lean_expr(_prime_expr(atom, transitioned)))
        for atom in tau_atoms
    ]
    if len(primed_taus) == 1:
        conclusion = primed_taus[0]
    else:
        conclusion = " ∧ ".join(f"({t})" for t in primed_taus)

    # Tactic chain: subst the init equations + dispatch each
    # conjunct via the standard fallback.
    n_axioms = len(problem.axioms)
    _axiom_names = [f"user_axiom_{i}" for i in range(n_axioms)]
    _simp_set = ", ".join(["store", "store2d"] + _axiom_names)
    _simp_cfg = "(config := { failIfUnchanged := false })"
    _simp = f"simp_all {_simp_cfg} [{_simp_set}]"
    _GENERIC = (
        f"first "
        f"| assumption "
        f"| omega "
        f"| nlinarith "
        f"| ({_simp}; done) "
        f"| (aesop; done) "
        f"| ({_simp}; first | rfl | omega | nlinarith | (aesop; done))"
    )
    if len(primed_taus) == 1:
        tactic_body = f"  subst_eqs\n  {_GENERIC}\n"
    else:
        refine_pat = ", ".join("?_" for _ in primed_taus)
        tactic_body = (
            f"  subst_eqs\n"
            f"  refine ⟨{refine_pat}⟩\n"
            f"  all_goals ({_GENERIC})\n"
        )

    name = theorem_name or f"{loop_id}_entry_bundle"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"{tactic_body}"
    )


def theorem_for_chain_bundle_chain(problem: Problem,
                                   solution: Solution,
                                   loop_id: str,
                                   theorem_name: str | None = None) -> str:
    """Multi-item-chain version of `theorem_for_chain_bundle`.

    For templates where the chain to the final goal (Fpost)
    traverses multiple loops, emit a theorem threading state
    through every item.  Goal is Fpost (or, for nested chains,
    the enclosing loop's τ at the iteration-end state).

    Currently only handles OUTERMOST chain-bundles
    (`enclosing_loop_id is None`).  Nested chain-bundles (FW
    L1 / L2's bundle-post) would need a different goal shape
    (`τ_enclosing at iteration-end state`) — raise
    NotImplementedError for now; tackle in a follow-up.
    """
    path = _linearize_path(problem.template, loop_id)
    if path is None:
        raise ValueError(
            f"chain-bundle-chain: loop {loop_id!r} not in template"
        )
    chain_items, target_idx, enclosing_loop_id = path

    # State count: len(chain) + 1.
    num_states = len(chain_items) + 1
    chain_binders, state_to_name = _chain_state_binders(
        problem, num_states
    )

    binders: list[str] = list(chain_binders)

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        pre_with_state = _rename_state(problem.pre, state_to_name[0])
        binders.append(f"(h_pre : {lean_expr(pre_with_state)})")

    # For NESTED case: emit enclosing τ + g hypotheses at state 0.
    # This is the body inductive of the enclosing loop — we're
    # PROVING τ_enclosing at iteration-end given τ_enclosing at
    # iteration-start (state 0) plus the guard fired.
    if enclosing_loop_id is not None:
        enc_tau_atoms = solution.atoms.get(f"tau@{enclosing_loop_id}", [])
        for ai, atom_str in enumerate(enc_tau_atoms):
            atom_lean = lean_expr(_rename_state(atom_str, state_to_name[0]))
            binders.append(f"(h_enc_tau_{ai} : {atom_lean})")
        enc_guard_atoms = solution.atoms.get(f"g@{enclosing_loop_id}", [])
        if enc_guard_atoms:
            g_str = (enc_guard_atoms[0]
                     if isinstance(enc_guard_atoms, list) else enc_guard_atoms)
            g_lean = lean_expr(_rename_state(g_str, state_to_name[0]))
            binders.append(f"(h_enc_g : {g_lean})")

    # Emit every chain item's transition hyps + frame eqs.
    for k in range(len(chain_items)):
        item = chain_items[k]
        in_names = state_to_name[k]
        out_names = state_to_name[k + 1]
        _emit_chain_item_hyps(
            item, in_names, out_names,
            problem, solution, binders, suffix=f"i{k}",
        )

    # Goal: for top-level chain, problem.post at state-N.  For
    # NESTED chain, τ_enclosing at state-N — the body inductive
    # of the enclosing loop.
    final_names = state_to_name[num_states - 1]
    if enclosing_loop_id is None:
        post_with_state = _rename_state(problem.post, final_names)
        conclusion = lean_expr(post_with_state)
    else:
        enc_tau_atoms = solution.atoms.get(f"tau@{enclosing_loop_id}", [])
        if not enc_tau_atoms:
            raise ValueError(
                f"chain-bundle-chain nested: enclosing {enclosing_loop_id!r}"
                f" has no τ atoms"
            )
        parts = [
            f"({lean_expr(_rename_state(atom, final_names))})"
            for atom in enc_tau_atoms
        ]
        conclusion = " ∧ ".join(parts)

    # Tactic chain.
    n_axioms = len(problem.axioms)
    _axiom_names = [f"user_axiom_{i}" for i in range(n_axioms)]
    _simp_set = ", ".join(["store", "store2d"] + _axiom_names)
    _simp_cfg = "(config := { failIfUnchanged := false })"
    _simp = f"simp_all {_simp_cfg} [{_simp_set}]"
    _GENERIC = (
        f"first "
        f"| assumption "
        f"| omega "
        f"| nlinarith "
        f"| ({_simp}; done) "
        f"| (aesop; done) "
        f"| ({_simp}; first | rfl | omega | nlinarith | (aesop; done))"
    )
    tactic_body = f"  subst_eqs\n  {_GENERIC}\n"

    name = theorem_name or f"{loop_id}_chain_bundle_chain"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"{tactic_body}"
    )


def theorem_for_entry_bundle_chain(problem: Problem,
                                   solution: Solution,
                                   loop_id: str,
                                   theorem_name: str | None = None) -> str:
    """Multi-item-chain version of `theorem_for_entry_bundle`.

    For templates where the path to `Loop(loop_id)` contains
    NON-SB items (other Loops as abstract transitions), emit a
    theorem that threads state through each chain item.

    Shape:

        Pre
        ∧ <chain items 0..target_idx>'s state transitions>
        ∧ (if enclosing_loop is not None: τ_enclosing ∧ g_enclosing
                                           at chain's first state)
        ⇒ τ_target(at state target_idx).

    Each chain item contributes:
      - SB(n=1): `h_<bid>_trans_<var>: <var>@out = <expr@in>`.
        Vars NOT in the trans get `h_<bid>_frame_<var>: <var>@out
        = <var>@in` for state continuity.
      - SB(n>1): NotImplementedError (would need branch-Cartesian
        expansion; not yet needed by current benchmarks).
      - Loop: abstract transition — τ_loop(out) + ¬g_loop(out)
        + frame eqs for vars NOT modified by the loop's body.

    State naming: state-k binders are `<var>_s<k> : <type>`.

    The translator's previous flat-chain function
    (`theorem_for_entry_bundle`) is kept for backward compat with
    SB-only chain benchmarks (kadane / majority / modexp); their
    cite lambdas use the `<var>'` naming.  Verify.py dispatches
    to this chain-aware function only when the chain has
    non-SB items between Pre and target.
    """
    path = _linearize_path(problem.template, loop_id)
    if path is None:
        raise ValueError(
            f"entry-bundle-chain: loop {loop_id!r} not in template"
        )
    chain_items, target_idx, enclosing_loop_id = path
    if target_idx == 0:
        raise NotImplementedError(
            f"entry-bundle-chain: loop {loop_id!r} is the first item — "
            f"no chain prefix to thread"
        )

    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    if not tau_atoms:
        raise ValueError(
            f"entry-bundle-chain: loop {loop_id} has no τ atoms"
        )

    # State count: target_idx + 1 states (state 0 = chain entry,
    # state target_idx = loop entry).  We emit binders for ALL
    # states from 0 to target_idx.
    num_states = target_idx + 1
    chain_binders, state_to_name = _chain_state_binders(
        problem, num_states
    )

    binders: list[str] = list(chain_binders)

    # h_pre at state 0 (rename Pre's vars to _s0 suffix).
    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        pre_with_state = _rename_state(problem.pre, state_to_name[0])
        binders.append(f"(h_pre : {lean_expr(pre_with_state)})")

    # Enclosing-loop hypotheses (if nested): τ_enclosing + g_enclosing
    # at state 0.  These represent "we're inside enclosing_loop's
    # current iteration".
    if enclosing_loop_id is not None:
        enc_tau = solution.atoms.get(f"tau@{enclosing_loop_id}", [])
        for i_a, atom in enumerate(enc_tau):
            renamed = _rename_state(atom, state_to_name[0])
            binders.append(
                f"(h_enc_tau_{i_a} : {lean_expr(renamed)})"
            )
        enc_g = solution.atoms.get(f"g@{enclosing_loop_id}", [])
        if enc_g:
            g_expr = enc_g[0] if isinstance(enc_g, list) else enc_g
            renamed = _rename_state(g_expr, state_to_name[0])
            binders.append(f"(h_enc_g : {lean_expr(renamed)})")

    # Emit each chain item's transition hyps + frame eqs.
    # State k → state k+1 is item chain_items[k]'s transition.
    for k in range(target_idx):
        item = chain_items[k]
        in_names = state_to_name[k]
        out_names = state_to_name[k + 1]
        _emit_chain_item_hyps(
            item, in_names, out_names,
            problem, solution, binders, suffix=f"i{k}",
        )

    # Goal: τ_target at state target_idx.
    target_names = state_to_name[target_idx]
    primed_taus = [
        lean_expr(_rename_state(atom, target_names))
        for atom in tau_atoms
    ]
    if len(primed_taus) == 1:
        conclusion = primed_taus[0]
    else:
        conclusion = " ∧ ".join(f"({t})" for t in primed_taus)

    # Tactic chain (same generic chain as flat version).
    n_axioms = len(problem.axioms)
    _axiom_names = [f"user_axiom_{i}" for i in range(n_axioms)]
    _simp_set = ", ".join(["store", "store2d"] + _axiom_names)
    _simp_cfg = "(config := { failIfUnchanged := false })"
    _simp = f"simp_all {_simp_cfg} [{_simp_set}]"
    _GENERIC = (
        f"first "
        f"| assumption "
        f"| omega "
        f"| nlinarith "
        f"| ({_simp}; done) "
        f"| (aesop; done) "
        f"| ({_simp}; first | rfl | omega | nlinarith | (aesop; done))"
    )
    if len(primed_taus) == 1:
        tactic_body = f"  subst_eqs\n  {_GENERIC}\n"
    else:
        refine_pat = ", ".join("?_" for _ in primed_taus)
        tactic_body = (
            f"  subst_eqs\n"
            f"  refine ⟨{refine_pat}⟩\n"
            f"  all_goals ({_GENERIC})\n"
        )

    name = theorem_name or f"{loop_id}_entry_bundle_chain"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{conclusion} := by\n"
        f"{tactic_body}"
    )


def _rename_state(expr_str: str, names: dict[str, str]) -> str:
    """Substitute program-var references in an expression string with
    state-suffixed names.

    Uses word-boundary regex to avoid partial replacements (e.g., `i`
    inside `is_sorted`).  This is a TEXT-level rewrite — fragile but
    matches the level the rest of the translator operates at.
    """
    import re
    out = expr_str
    # Sort by length descending so longer names get matched first
    # (avoids `i` clobbering `is_sorted`'s `i`).
    for var in sorted(names, key=len, reverse=True):
        new_name = names[var]
        if var == new_name:
            continue
        out = re.sub(r'\b' + re.escape(var) + r'\b', new_name, out)
    return out


def _emit_chain_item_hyps(item, in_names: dict[str, str],
                          out_names: dict[str, str],
                          problem: Problem, solution: Solution,
                          binders: list[str], suffix: str) -> None:
    """Emit binders for one chain item's contribution.

      - SB(n=1): h_<suffix>_trans_<var> for modified vars,
                 h_<suffix>_frame_<var> for unmodified.
      - SB(n>1): not yet supported in chains (rare; would need
                 Cartesian expansion of branch combinations).
      - Loop:    abstract transition: τ_loop_exit + ¬g_loop +
                 frame_eqs for vars NOT modified by loop body.
    """
    modified = _modified_vars_of_chain_item(item, problem, solution)
    if isinstance(item, SB):
        if item.n != 1:
            raise NotImplementedError(
                f"chain-item SB(n={item.n}) not supported in entry-"
                f"bundle-chain yet"
            )
        atom = solution.atoms.get(f"s@{item.block_id}", {})
        if not isinstance(atom, dict):
            raise NotImplementedError(
                f"chain-item SB({item.block_id}): non-dict atom"
            )
        # Transition hyps for modified vars.
        for var, rhs in atom.items():
            rhs_renamed = _rename_state(rhs, in_names)
            out_var = out_names[var]
            binders.append(
                f"(h_{suffix}_trans_{var} : "
                f"{out_var} = {lean_expr(rhs_renamed)})"
            )
        # Frame eqs for unmodified vars.
        for var in in_names:
            if var in modified:
                continue
            out_var = out_names[var]
            in_var = in_names[var]
            binders.append(
                f"(h_{suffix}_frame_{var} : {out_var} = {in_var})"
            )
    elif isinstance(item, Loop):
        lid = item.loop_id
        # τ_loop_exit at out state (the loop's "exit invariant").
        tau_atoms = solution.atoms.get(f"tau@{lid}", [])
        for i_a, atom in enumerate(tau_atoms):
            renamed = _rename_state(atom, out_names)
            binders.append(
                f"(h_{suffix}_{lid}_tau_{i_a} : "
                f"{lean_expr(renamed)})"
            )
        # ¬guard at out state — BUT only when the Loop does NOT have
        # a break branch.  Break-capable Loops can exit early with
        # the guard still true; assuming ¬g would be unsoundly
        # stronger than the Z3-side abstract transition (K.D.IMPL).
        if not _has_break_branch(item.body, problem):
            g_atoms = solution.atoms.get(f"g@{lid}", [])
            if g_atoms:
                g_expr = g_atoms[0] if isinstance(g_atoms, list) else g_atoms
                renamed = _rename_state(g_expr, out_names)
                binders.append(
                    f"(h_{suffix}_{lid}_not_g : ¬ ({lean_expr(renamed)}))"
                )
        # Frame eqs for vars NOT modified by loop body.
        for var in in_names:
            if var in modified:
                continue
            out_var = out_names[var]
            in_var = in_names[var]
            binders.append(
                f"(h_{suffix}_{lid}_frame_{var} : "
                f"{out_var} = {in_var})"
            )
    else:
        raise NotImplementedError(
            f"chain-item type {type(item).__name__} not supported "
            f"(SB and Loop only)"
        )


def _find_init_block_id(template: Template, loop_id: str) -> str | None:
    """Find the SB block_id of the SB sitting IMMEDIATELY BEFORE
    `Loop(loop_id)` in a `Seq`-linearized template.  Returns None
    if no such block exists.
    """
    # Linearize the template into items.
    items = _linearize(template)
    for i, item in enumerate(items):
        if isinstance(item, Loop) and item.loop_id == loop_id and i > 0:
            prev = items[i - 1]
            if isinstance(prev, SB):
                return prev.block_id
    return None


def _linearize(template: Template) -> list:
    """Flatten a Seq tree into a list of items (SBs, Loops, Recurs)."""
    if isinstance(template, Seq):
        return _linearize(template.left) + _linearize(template.right)
    return [template]


def _linearize_path(
    template: Template,
    target_loop_id: str,
) -> tuple[list, int, str | None] | None:
    """Locate `Loop(target_loop_id)` in `template` and return its
    enclosing-Seq chain.

    Returns `(chain_items, target_idx, enclosing_loop_id)`:
      - `chain_items` — the linearized Seq chain that DIRECTLY
        contains target_loop_id (could be the top-level template
        chain, or a nested Loop's body chain).
      - `target_idx` — position of target_loop in chain_items.
      - `enclosing_loop_id` — `loop_id` of the immediately
        enclosing Loop, or None if target is at top level.

    Examples:
      - merge_two_sorted (chained): `SB(B0) >> Loop(L0) >>
        Loop(L1) >> Loop(L2)`.  Target L1 → ([SB(B0), Loop(L0),
        Loop(L1), Loop(L2)], 2, None).
      - floyd_warshall (nested): outer body contains Loop(L1).
        Target L1 → (L0_body_chain, 1, "L0").

    Returns None if target_loop_id isn't found anywhere in the
    template.
    """
    items = _linearize(template)
    for idx, item in enumerate(items):
        if isinstance(item, Loop):
            if item.loop_id == target_loop_id:
                return (items, idx, None)
            # Recurse into body to look for the target deeper.
            inner = _linearize_path(item.body, target_loop_id)
            if inner is not None:
                inner_chain, inner_idx, inner_enc = inner
                # Replace the "no enclosing" None with the
                # immediately-enclosing loop_id.
                return (inner_chain, inner_idx,
                        inner_enc or item.loop_id)
    return None


def _chain_state_binders(
    problem: Problem,
    num_states: int,
) -> tuple[list[str], list[dict[str, str]]]:
    """Emit binders for `num_states` chain states.

    Naming scheme: var `v` at state `k` becomes `v_s<k>` in Lean.
    For uniform treatment, EVERY program var gets a per-state
    binder; frame equations between adjacent states are emitted
    separately by `_emit_chain_item_binders` for unmodified vars.

    Returns `(binders, state_to_name_map)`:
      - `binders`: list of Lean binder lines (one per state-type
        group, e.g. `(n_s0 i_s0 j_s0 : Int)`).
      - `state_to_name_map[k][var]` = Lean name of `var` at state
        `k`.

    Example: for problem with vars {n, i : Int}, A : Int → Int,
    num_states=3:
      binders = [
        "(n_s0 i_s0 : Int)", "(A_s0 : Int → Int)",
        "(n_s1 i_s1 : Int)", "(A_s1 : Int → Int)",
        "(n_s2 i_s2 : Int)", "(A_s2 : Int → Int)",
      ]
      state_to_name_map = [
        {n: "n_s0", i: "i_s0", A: "A_s0"},
        {n: "n_s1", i: "i_s1", A: "A_s1"},
        {n: "n_s2", i: "i_s2", A: "A_s2"},
      ]
    """
    seen: set[str] = set()
    int_names: list[str] = []
    arr1d_names: list[str] = []
    arr2d_names: list[str] = []
    for v in problem.inputs + problem.outputs + problem.locals:
        if v.name in seen:
            continue
        seen.add(v.name)
        if v.type == "int":
            int_names.append(v.name)
        elif v.type == "int[]":
            arr1d_names.append(v.name)
        elif v.type == "int[][]":
            arr2d_names.append(v.name)

    binders: list[str] = []
    state_to_name_map: list[dict[str, str]] = []
    for k in range(num_states):
        sk_int = [f"{n}_s{k}" for n in int_names]
        sk_a1d = [f"{n}_s{k}" for n in arr1d_names]
        sk_a2d = [f"{n}_s{k}" for n in arr2d_names]
        if sk_int:
            binders.append(f"({' '.join(sk_int)} : Int)")
        if sk_a1d:
            binders.append(f"({' '.join(sk_a1d)} : Int → Int)")
        if sk_a2d:
            binders.append(f"({' '.join(sk_a2d)} : Int → Int → Int)")
        # State k's var-name map.
        m: dict[str, str] = {}
        for n in int_names + arr1d_names + arr2d_names:
            m[n] = f"{n}_s{k}"
        state_to_name_map.append(m)
    return binders, state_to_name_map


def _modified_vars_of_chain_item(item, problem: Problem,
                                 solution: Solution) -> set[str]:
    """Vars modified by one chain item.  Mirrors
    `synth.constraints._modified_vars_of_template` but specialized
    for one item at a time (caller is iterating the chain).

      - SB(n=1): keys of its transition atom.
      - SB(n>1): union of keys across all branches' transition
        atoms.
      - Loop: recursively the modified vars of its body.
      - Recur: keys of its `_recur` atom.

    The chain-bundle / entry-bundle translators use this to
    decide which vars get a fresh primed name at the chain item's
    output state vs preserved by a frame equation.
    """
    if isinstance(item, SB):
        bid = item.block_id
        modified: set[str] = set()
        if item.n == 1:
            atom = solution.atoms.get(f"s@{bid}", {})
            if isinstance(atom, dict):
                modified |= set(atom.keys())
        else:
            for k in range(item.n):
                atom = solution.atoms.get(f"s@{bid}.{k}", {})
                if isinstance(atom, dict):
                    modified |= set(atom.keys())
        return modified
    if isinstance(item, Loop):
        # Lazy import to avoid cycle.
        from ..constraints import _modified_vars_of_template
        return _modified_vars_of_template(item.body, problem)
    if isinstance(item, Recur):
        atom = solution.atoms.get(f"s@{item.recur_id}", {})
        if isinstance(atom, dict):
            return set(atom.keys())
        return set()
    raise TypeError(f"unknown chain item: {type(item).__name__}")


def theorem_for_chain_bundle(problem: Problem,
                             solution: Solution,
                             loop_id: str,
                             theorem_name: str | None = None) -> str:
    """Emit a Lean theorem for the chain-bundle (post) safety
    obligation:

        Fpre ∧ τ_exit ∧ ¬g_exit ∧ skip_atoms  ⇒  Fpost

    For templates shaped `SB(init) >> Loop(<loop_id>) >> SB(skip)`
    (factorial-class).  Conventions:

      - Pre-state vars: unprimed.
      - Vars MODIFIED by the loop body: primed (`x'`) — these are
        the loop-exit values.  τ_exit and ¬g use the primed names.
      - Vars MODIFIED by skip (but NOT by the loop body): also
        primed; emitted as `h_skip_<var>: <var>' = <rhs>` where
        rhs is evaluated over the loop-exit state.
      - Vars MODIFIED only by init (but not loop / skip):
        currently NotImplementedError — init writes that escape
        the loop's overwrite need full state threading.

    Init's effect is DROPPED when its keys are fully covered by
    the loop's body (loop overwrites init); this is the
    factorial / fib pattern.  Otherwise NotImplementedError.

    The proof shape is benchmark-specific.  The generic tactic
    chain (omega + nlinarith + simp_all with user_axiom_* in
    scope) closes some cases; the rest dump for `.solved.lean`
    curation.
    """
    tau_atoms = solution.atoms.get(f"tau@{loop_id}", [])
    if not tau_atoms:
        raise ValueError(f"chain-bundle: loop {loop_id} has no τ atoms")
    guard_atoms = solution.atoms.get(f"g@{loop_id}", [])
    if not guard_atoms:
        raise ValueError(f"chain-bundle: loop {loop_id} has no guard")
    guard_expr = (guard_atoms[0]
                  if isinstance(guard_atoms, list) else guard_atoms)

    # For SB(n=1): single body block.  For SB(n>1): union of
    # branches' modified-var sets — the loop's abstract transition
    # may leave any of these fresh at exit (frame_eqs only preserve
    # vars NOT in this union).
    target_loop = _find_loop(problem.template, loop_id)
    if target_loop is None:
        raise ValueError(f"loop {loop_id!r} not found in template")
    sb_body = target_loop.body
    if not isinstance(sb_body, SB):
        # Non-SB loop body (Seq with nested Loops, etc. — Floyd-
        # Warshall etc.).  Use the conservative modified-vars walker
        # to compute the loop's modified set; skip the SB-specific
        # body-atom inspection.  The chain-bundle obligation only
        # needs modified_by_loop (for state-primer naming), not the
        # transition atoms themselves.
        from ..constraints import _modified_vars_of_template
        modified_by_loop = _modified_vars_of_template(sb_body, problem)
        # Continue below with the rest of the chain-bundle build.
        # (init/skip extraction, binders, goal.)
        # Use a sentinel here so the SB-specific code paths skip.
        _body_is_sb = False
    else:
        _body_is_sb = True
        modified_by_loop = set()
    if _body_is_sb and sb_body.n == 1:
        body_atom = solution.atoms.get(f"s@{sb_body.block_id}", {})
        if isinstance(body_atom, dict) and body_atom.get("_recur"):
            raise NotImplementedError(
                "chain-bundle: recur body not yet supported"
            )
        if isinstance(body_atom, dict):
            modified_by_loop = set(body_atom.keys())
    elif _body_is_sb:
        for b_idx in range(sb_body.n):
            branch_atom = solution.atoms.get(
                f"s@{sb_body.block_id}.{b_idx}", {}
            )
            if isinstance(branch_atom, dict) and branch_atom.get("_recur"):
                raise NotImplementedError(
                    "chain-bundle: recur branch not yet supported"
                )
            if isinstance(branch_atom, dict):
                modified_by_loop |= set(branch_atom.keys())

    # Walk the template to identify init / skip transition atoms.
    items = _linearize(problem.template)
    loop_idx = None
    for i, it in enumerate(items):
        if isinstance(it, Loop) and it.loop_id == loop_id:
            loop_idx = i
            break
    if loop_idx is None:
        raise ValueError(f"chain-bundle: loop {loop_id} not in template")
    init_atoms_dicts: list[dict] = []
    skip_atoms_dicts: list[dict] = []
    for i, it in enumerate(items):
        if i == loop_idx:
            continue
        if not isinstance(it, SB):
            continue
        sb_atom = solution.atoms.get(f"s@{it.block_id}", {})
        if not isinstance(sb_atom, dict):
            raise NotImplementedError(
                f"chain-bundle: non-dict atom for s@{it.block_id}"
            )
        if sb_atom.get("_recur"):
            raise NotImplementedError(
                f"chain-bundle: recur in chain SB s@{it.block_id}"
            )
        if i < loop_idx:
            init_atoms_dicts.append(sb_atom)
        else:
            skip_atoms_dicts.append(sb_atom)

    # Compose init writes: each pre-loop SB writes its keys.  Two
    # cases:
    #   (a) init keys ⊆ body.keys(): loop fully overwrites init's
    #       effect, init can be ignored for the FLAT theorem.
    #   (b) init keys ⊄ body.keys(): pre-loop SB writes a var
    #       (e.g., array_rotate_left's `saved`) that the loop
    #       doesn't touch.  The var keeps its init value through
    #       the loop; emit as `h_init_<var>` hypothesis mirroring
    #       the existing `h_skip_<var>` handling for post-loop
    #       writes.
    init_keys: set[str] = set()
    init_atom: dict[str, str] = {}
    for d in init_atoms_dicts:
        for k, v in d.items():
            init_keys.add(k)
            init_atom[k] = v
    init_extras = init_keys - modified_by_loop

    # Compose skip writes.  Two sub-cases:
    #   - skip writes a var NOT in modified_by_loop (e.g., fib's
    #     `f := a`): emit `h_skip_<var> : <var>' = <rhs>` with the
    #     primed name being the FINAL state.
    #   - skip writes a var ALSO in modified_by_loop (e.g.,
    #     array_rotate_left's `A := Update(A, n-1, saved)` after a
    #     loop that rotates A): the var has THREE values — pre-state
    #     (`var`), loop-exit (`var'`), final (`var_post`).  Emit
    #     `h_skip_<var> : <var>_post = <rhs over loop-exit state>`.
    #     Goal uses `<var>_post`; τ atoms / ¬g use `<var>'`.
    skip_atom: dict[str, str] = {}           # non-loop-modified
    skip_atom_loop_mod: dict[str, str] = {}  # loop-modified (NEW)
    for d in skip_atoms_dicts:
        for k, v in d.items():
            if k in modified_by_loop:
                skip_atom_loop_mod[k] = v
            else:
                skip_atom[k] = v
    skip_keys: set[str] = set(skip_atom.keys())
    post_skip_set: set[str] = set(skip_atom_loop_mod.keys())

    # Primed set: loop-modified PLUS skip-only-modified vars.
    # (Vars in post_skip_set are already in modified_by_loop, so the
    # primed binder bound them as `<var>'` = loop-exit state.)
    primed_set = modified_by_loop | skip_keys
    _, _, binders = _state_binders(
        problem,
        prime_set=primed_set,
        post_skip_set=post_skip_set,
    )

    if problem.pre and problem.pre.strip().lower() not in ("", "true"):
        binders.append(f"(h_pre : {lean_expr(problem.pre)})")
    # τ atoms at the EXIT (loop-modified primed; skip-modified NOT
    # primed here since skip hasn't run yet at the exit state).
    for i, atom in enumerate(tau_atoms):
        primed = _finalize_primes(
            lean_expr(_prime_expr(atom, modified_by_loop))
        )
        binders.append(f"(h_tau_{i} : {primed})")
    # ¬guard at exit (loop-modified primed):
    primed_guard = _finalize_primes(
        lean_expr(_prime_expr(guard_expr, modified_by_loop))
    )
    binders.append(f"(h_not_g : ¬ ({primed_guard}))")
    # Skip atoms (non-loop-modified): <var>' = <rhs over exit state>.
    # In the rhs, loop-modified var references should be primed
    # (since they're at the post-loop state); other refs stay
    # unprimed (pre-state, unchanged through loop).
    for var, rhs in skip_atom.items():
        var_p = f"{var}'"
        rhs_primed = _finalize_primes(
            lean_expr(_prime_expr(rhs, modified_by_loop))
        )
        binders.append(f"(h_skip_{var} : {var_p} = {rhs_primed})")
    # Skip atoms (loop-modified): <var>_post = <rhs over exit
    # state>.  RHS references are primed for loop-modified vars
    # (loop-exit state); unprimed elsewhere.  The LHS is the FINAL
    # state binder.
    for var, rhs in skip_atom_loop_mod.items():
        var_post = f"{var}_post"
        rhs_primed = _finalize_primes(
            lean_expr(_prime_expr(rhs, modified_by_loop))
        )
        binders.append(f"(h_skip_{var} : {var_post} = {rhs_primed})")
    # Init atoms: <var> = <rhs over pre-state>.  Pre-loop writes
    # to vars NOT modified by the loop (e.g., array_rotate_left's
    # `saved`).  The var keeps its init value through the loop
    # (since the loop doesn't touch it) and is referenced by the
    # post-loop block.  All RHS references are to pre-state vars,
    # so no priming.
    for var in sorted(init_extras):
        rhs = init_atom[var]
        rhs_lean = lean_expr(rhs)
        binders.append(f"(h_init_{var} : {var} = {rhs_lean})")

    # Goal: Fpost on the FINAL state.  For vars in post_skip_set
    # (loop-modified + skip-rewritten), substitute `<var>_post`.
    # For other vars in primed_set (loop-modified-only or
    # skip-only-not-loop-modified), substitute primed `<var>'`.
    primed_post = _finalize_primes(
        lean_expr(
            _prime_expr(
                _post_expr(problem.post, post_skip_set),
                primed_set - post_skip_set,
            )
        )
    )

    # Tactic chain: similar to safety_inductive but the typical shape
    # is "derive concrete value of loop counter from τ ∧ ¬g (omega),
    # then rewrite the recurrence atom".  No `subst_eqs` since the
    # transition hypotheses aren't here.
    n_axioms = len(problem.axioms)
    _axiom_names = [f"user_axiom_{i}" for i in range(n_axioms)]
    _simp_set = ", ".join(["store", "store2d"] + _axiom_names)
    _simp_cfg = "(config := { failIfUnchanged := false })"
    _simp = f"simp_all {_simp_cfg} [{_simp_set}]"
    _GENERIC_TACTIC = (
        f"first "
        f"| assumption "
        f"| omega "
        f"| nlinarith "
        f"| ({_simp}; done) "
        f"| (aesop; done) "
        f"| ({_simp}; first | rfl | omega | nlinarith | (aesop; done))"
    )
    tactic_body = f"  {_GENERIC_TACTIC}\n"

    name = theorem_name or f"{loop_id}_chain_bundle"
    indent = "    "
    binders_block = ("\n" + indent).join(binders) if binders else ""
    if binders_block:
        binders_block = "\n" + indent + binders_block + " :"
    else:
        binders_block = " :"
    return (
        f"set_option linter.unusedVariables false in\nset_option linter.unusedSimpArgs false in\n"
        f"theorem {name}{binders_block}\n"
        f"{indent}{primed_post} := by\n"
        f"{tactic_body}"
    )
