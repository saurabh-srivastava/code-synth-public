"""Expression parser — string → Z3.

Parses Python-syntax expression strings against a variable binding and
returns a Z3 expression.  Used to turn atom strings like
`"v + 2*i + 1"` or `"v == i*i && x >= (i-1)*(i-1) && i >= 1"` into Z3.

Supported syntax:

  - integer literals, variable references (must be in the binding)
  - arithmetic: `+`, `-`, `*`, `//` (integer division)
  - comparisons (including chained): `<`, `<=`, `==`, `!=`, `>=`, `>`
  - boolean: `and`, `or`, `not`  *and also*  `&&`, `||`, `!` via a
    pre-normalization pass for ergonomic atom strings
  - ternary: `e1 if cond else e2`
  - the literal identifiers `true` and `false`
  - array reads:  `A[i]`                       (Phase 3.A)
  - array writes / Z3 Store: `Update(A, i, v)` (Phase 3.C)
  - implication: `Implies(p, q)`               (Phase 3.B)
  - quantifiers:                               (Phase 3.B)
        `ForAll(lambda k: body)`
        `Exists(lambda k, j: body)`            (multi-var lambda OK)

  Quantifier variables default to `IntSort`.  The lambda body is parsed
  under a binding extended with the bound variables.

Uninterpreted-function calls are looked up in an optional `uf` registry
(Phase 3.D): `uf` maps function names to `z3.FuncDeclRef`s.  Calls to
names not in `uf` and not in the built-in set raise ValueError.
"""
from __future__ import annotations
import ast
import re
from typing import Mapping
import z3

Binding   = Mapping[str, z3.ExprRef]
UFunctionRegistry = Mapping[str, z3.FuncDeclRef]


def parse_expr(s: str,
               binding: Binding,
               uf: UFunctionRegistry | None = None) -> z3.ExprRef:
    """Parse `s` as a Python expression and translate to Z3 under `binding`.

    `binding` maps variable names to Z3 expressions (Int / Bool / Array
    refs).  `uf`, if given, maps uninterpreted-function names to their
    Z3 FuncDeclRefs.
    """
    if uf is None:
        uf = {}
    normalized = _normalize(s)
    try:
        tree = ast.parse(normalized, mode="eval")
    except SyntaxError as e:
        raise ValueError(f"could not parse expression {s!r}: {e}") from e
    return _translate(tree.body, binding, uf)


# ─────────────────────────────────────────────────────────────────────
# Surface conveniences: accept `&&`, `||`, `!` in atom strings even
# though Python doesn't.  Rewrites to `and`, `or`, `not` (taking care
# not to touch `!=` or `==`).
# ─────────────────────────────────────────────────────────────────────
_NORM_RE = [
    (re.compile(r"&&"),                          " and "),
    (re.compile(r"\|\|"),                        " or "),
    # `!` only when not followed by `=`.  Use a lookahead.
    (re.compile(r"!(?!=)"),                      " not "),
]


def _normalize(s: str) -> str:
    out = s
    for rx, repl in _NORM_RE:
        out = rx.sub(repl, out)
    return out


# ─────────────────────────────────────────────────────────────────────
# AST → Z3 translation.
# ─────────────────────────────────────────────────────────────────────
def _translate(node: ast.AST,
               binding: Binding,
               uf: UFunctionRegistry) -> z3.ExprRef:
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node.value, int):
            return z3.IntVal(node.value)
        raise ValueError(f"unsupported literal: {node.value!r}")

    if isinstance(node, ast.Name):
        if node.id == "true":
            return z3.BoolVal(True)
        if node.id == "false":
            return z3.BoolVal(False)
        if node.id in binding:
            return binding[node.id]
        raise ValueError(f"unbound variable {node.id!r}; "
                         f"known: {sorted(binding)}")

    if isinstance(node, ast.BinOp):
        l = _translate(node.left, binding, uf)
        r = _translate(node.right, binding, uf)
        op = type(node.op).__name__
        if op == "Add":      return l + r
        if op == "Sub":      return l - r
        if op == "Mult":     return l * r
        if op == "FloorDiv": return l / r            # Z3 `/` on Int = integer div
        if op == "Div":      return l / r            # Z3 maps both to int division
        if op == "Mod":      return l % r
        raise ValueError(f"unsupported binop: {op}")

    if isinstance(node, ast.UnaryOp):
        x = _translate(node.operand, binding, uf)
        op = type(node.op).__name__
        if op == "USub": return -x
        if op == "UAdd": return x
        if op == "Not":  return z3.Not(x)
        raise ValueError(f"unsupported unaryop: {op}")

    if isinstance(node, ast.BoolOp):
        args = [_translate(a, binding, uf) for a in node.values]
        op = type(node.op).__name__
        if op == "And": return z3.And(*args) if len(args) > 1 else args[0]
        if op == "Or":  return z3.Or(*args)  if len(args) > 1 else args[0]
        raise ValueError(f"unsupported boolop: {op}")

    if isinstance(node, ast.Compare):
        # Chained comparisons: a < b <= c  →  And(a<b, b<=c).
        comparators = [node.left] + list(node.comparators)
        parts: list[z3.ExprRef] = []
        for left, op, right in zip(comparators[:-1], node.ops, comparators[1:]):
            l = _translate(left,  binding, uf)
            r = _translate(right, binding, uf)
            on = type(op).__name__
            if   on == "Lt":    parts.append(l <  r)
            elif on == "LtE":   parts.append(l <= r)
            elif on == "Gt":    parts.append(l >  r)
            elif on == "GtE":   parts.append(l >= r)
            elif on == "Eq":    parts.append(l == r)
            elif on == "NotEq": parts.append(l != r)
            else: raise ValueError(f"unsupported cmpop: {on}")
        return parts[0] if len(parts) == 1 else z3.And(*parts)

    if isinstance(node, ast.IfExp):
        c = _translate(node.test,   binding, uf)
        t = _translate(node.body,   binding, uf)
        e = _translate(node.orelse, binding, uf)
        return z3.If(c, t, e)

    if isinstance(node, ast.Subscript):
        arr = _translate(node.value, binding, uf)
        # Python ≥3.9: node.slice is the index expression directly.
        # Python <3.9 wraps it in ast.Index — unwrap only in that case.
        idx_node = node.slice.value if isinstance(node.slice, ast.Index) else node.slice
        idx = _translate(idx_node, binding, uf)
        return z3.Select(arr, idx)

    if isinstance(node, ast.Call):
        return _translate_call(node, binding, uf)

    raise ValueError(f"unsupported expression node: {type(node).__name__}")


def _translate_call(node: ast.Call,
                    binding: Binding,
                    uf: UFunctionRegistry) -> z3.ExprRef:
    """Translate a function-call node.  Recognised names:
        ForAll, Exists  — quantifiers, one lambda argument
        Implies         — Boolean implication
        Update          — array store
    Other named calls fall through to `uf` lookup (uninterpreted functions).
    """
    if not isinstance(node.func, ast.Name):
        raise ValueError("only named function calls supported")
    name = node.func.id

    if name in ("ForAll", "Exists"):
        if len(node.args) != 1 or not isinstance(node.args[0], ast.Lambda):
            raise ValueError(f"{name} takes exactly one lambda argument, "
                             f"got {ast.dump(node)}")
        lam = node.args[0]
        ext = dict(binding)
        bvars: list[z3.ExprRef] = []
        for arg in lam.args.args:
            # §K.A.3 — name-suffix convention for non-Int bound vars:
            #   `*_arr` → ArraySort(Int, Int)        (int[]).
            #   `*_mat` → ArraySort(Int, ArraySort)  (int[][]).
            #   otherwise → IntSort  (existing default).
            # Lets axioms quantify over array-valued UF arguments.
            nm = arg.arg
            if nm.endswith("_arr"):
                bv = z3.Const(nm, z3.ArraySort(z3.IntSort(), z3.IntSort()))
            elif nm.endswith("_mat"):
                bv = z3.Const(nm, z3.ArraySort(
                    z3.IntSort(),
                    z3.ArraySort(z3.IntSort(), z3.IntSort())))
            else:
                bv = z3.Int(nm)
            ext[nm] = bv
            bvars.append(bv)
        body = _translate(lam.body, ext, uf)
        ctor = z3.ForAll if name == "ForAll" else z3.Exists
        # Phase 3.X.3 auto-trigger inference: pass UF applications that
        # contain bound variables as `patterns=`.  Z3's default
        # auto-pattern selection can be either too eager (multi-
        # instantiation) or too conservative; supplying the obvious
        # UF triggers explicitly cuts instantiation time on
        # axiom-heavy benchmarks (Fibonacci recurrence, etc.).
        uf_decls = set(uf.values())
        triggers = _auto_triggers(body, bvars, uf_decls)
        if triggers:
            return ctor(bvars, body, patterns=triggers)
        return ctor(bvars, body)

    if name == "Implies":
        if len(node.args) != 2:
            raise ValueError("Implies takes exactly two arguments")
        p = _translate(node.args[0], binding, uf)
        q = _translate(node.args[1], binding, uf)
        return z3.Implies(p, q)

    if name == "Update":
        # 1D: Update(A, i, v) → Store(A, i, v).
        # 2D: Update(A, i, j, v) → Store(A, i, Store(Select(A, i), j, v)).
        if len(node.args) == 3:
            a = _translate(node.args[0], binding, uf)
            i = _translate(node.args[1], binding, uf)
            v = _translate(node.args[2], binding, uf)
            return z3.Store(a, i, v)
        if len(node.args) == 4:
            a = _translate(node.args[0], binding, uf)
            i = _translate(node.args[1], binding, uf)
            j = _translate(node.args[2], binding, uf)
            v = _translate(node.args[3], binding, uf)
            return z3.Store(a, i, z3.Store(z3.Select(a, i), j, v))
        raise ValueError("Update takes 3 args (1D: array, index, value) "
                         "or 4 args (2D: array, row, col, value); got "
                         f"{len(node.args)}")

    # Uninterpreted function lookup.
    if name in uf:
        args = [_translate(a, binding, uf) for a in node.args]
        return uf[name](*args)

    raise ValueError(
        f"unknown function {name!r} in expression; "
        f"register it via Problem.uninterpreted "
        f"(known UFs: {sorted(uf)})"
    )


def _auto_triggers(body: z3.ExprRef,
                   bvars: list[z3.ExprRef],
                   uf_decls: set) -> list[z3.ExprRef]:
    """Auto-detect single-pattern triggers for a quantified body.

    Returns each UF application in `body` that contains **all** of the
    bound variables from `bvars`.  These become single-element patterns
    passed to `z3.ForAll(…, patterns=[…])`.  An empty result means we
    fall back to Z3's default auto-pattern.

    Z3 requires every quantifier pattern to mention every bound
    variable — otherwise it raises "invalid pattern" (e.g.,
    `ForAll i j k. sp(D, i, k, k)` would miss j).  Filtering to
    all-vars-present patterns avoids the error.  When NO single
    UF application covers all bvars (which is common for axioms
    that recurse over multiple sub-paths, like Floyd-Warshall's
    `sp(D, i, k, k) + sp(D, k, j, k)`), we return empty and let
    Z3 pick its own multi-pattern.
    """
    bvar_ids = {bv.get_id() for bv in bvars}
    found: list[z3.ExprRef] = []
    seen_id: set[int] = set()
    seen_returned: set[int] = set()

    stack = [body]
    while stack:
        e = stack.pop()
        eid = e.get_id()
        if eid in seen_id:
            continue
        seen_id.add(eid)
        # Skip non-application nodes (e.g., nested QuantifierRef
        # bodies, bound variables): `.num_args()` asserts is_app.
        # We just don't walk into those for trigger inference;
        # Z3's own multi-pattern selection handles nested
        # quantifiers fine without our help.
        if not z3.is_app(e):
            continue
        if e.num_args() > 0:
            try:
                d = e.decl()
            except Exception:
                d = None
            if (d is not None and d in uf_decls
                    and _contains_all_bvars(e, bvar_ids)):
                if eid not in seen_returned:
                    found.append(e)
                    seen_returned.add(eid)
        for c in e.children():
            stack.append(c)
    return found


def _contains_all_bvars(expr: z3.ExprRef, bvar_ids: set[int]) -> bool:
    """True iff `expr` mentions every bound variable in `bvar_ids`."""
    if not bvar_ids:
        return True
    seen_bvars: set[int] = set()
    stack = [expr]
    seen: set[int] = set()
    while stack:
        e = stack.pop()
        eid = e.get_id()
        if eid in seen:
            continue
        seen.add(eid)
        if eid in bvar_ids:
            seen_bvars.add(eid)
            if seen_bvars == bvar_ids:
                return True
        for c in e.children():
            stack.append(c)
    return False


def _contains_bvar(expr: z3.ExprRef, bvar_ids: set[int]) -> bool:
    stack = [expr]
    seen: set[int] = set()
    while stack:
        e = stack.pop()
        eid = e.get_id()
        if eid in seen:
            continue
        seen.add(eid)
        if eid in bvar_ids:
            return True
        for c in e.children():
            stack.append(c)
    return False
