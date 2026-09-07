"""Surface parsers — textual template grammar and JSON Problem loader.

Two surfaces lower into the same `ir.Problem`:

  * Textual flowgraph grammar, e.g. `"SB ; LOOP { SB } ; SB"`:

        T   ::= ATOM (';' T)*
        ATOM ::= 'SB'  ['(' n=INT ')']
              |  'LOOP' '{' T '}'
              |  'REC'                              (Phase 3+)

  * JSON Problem loader (LLM-facing).  Top-level keys:

        template  : str           — textual flowgraph
        inputs    : list[{name: type}]
        outputs   : list[{name: type}]
        locals    : list[{name: type}]              (optional)
        pre       : str
        post      : str
        atoms     : { hole_id: [atom, …] }
                    atoms are strings for tau/phi/g and dicts for s
        max_solutions       : int                   (optional)
        solver_timeout_ms   : int                   (optional)
"""
from __future__ import annotations
import json
import re
from pathlib import Path
from typing import Any

from .ir import SB, Loop, Seq, Recur, Var, Problem, Template


# ─────────────────────────────────────────────────────────────────────
# Textual flowgraph parser — recursive descent.
# ─────────────────────────────────────────────────────────────────────
_TOKEN_RE = re.compile(
    r"\s*(?:"
    r"(?P<kw>SB|LOOP|REC)"
    r"|(?P<num>\d+)"
    r"|(?P<sym>[(){};,=]|n=)"
    r")"
)


class _Lexer:
    def __init__(self, src: str):
        self.src = src
        self.pos = 0

    def _scan(self) -> tuple[str, str] | None:
        m = _TOKEN_RE.match(self.src, self.pos)
        if not m:
            if self.pos < len(self.src) and not self.src[self.pos:].isspace():
                raise ValueError(f"unexpected char at {self.pos!r}: "
                                 f"{self.src[self.pos:self.pos+10]!r}")
            return None
        self.pos = m.end()
        for k in ("kw", "num", "sym"):
            v = m.group(k)
            if v is not None:
                return (k, v)
        return None

    def peek(self) -> tuple[str, str] | None:
        save = self.pos
        tok = self._scan()
        self.pos = save
        return tok

    def next(self) -> tuple[str, str] | None:
        return self._scan()

    def expect(self, sym: str) -> None:
        tok = self.next()
        if tok is None or tok[1] != sym:
            raise ValueError(f"expected {sym!r}, got {tok!r}")


def parse_template(src: str) -> Template:
    """Parse a textual flowgraph into an IR template."""
    lx = _Lexer(src)
    t = _parse_seq(lx)
    if lx.peek() is not None:
        raise ValueError(f"unconsumed input at offset {lx.pos}: "
                         f"{src[lx.pos:lx.pos+20]!r}")
    return t


def _parse_seq(lx: _Lexer) -> Template:
    left = _parse_atom(lx)
    while True:
        tok = lx.peek()
        if tok is None or tok[1] != ";":
            return left
        lx.next()                       # consume ';'
        right = _parse_atom(lx)
        left = Seq(left, right)


def _parse_atom(lx: _Lexer) -> Template:
    tok = lx.next()
    if tok is None:
        raise ValueError("unexpected end of input")
    kind, val = tok
    if kind != "kw":
        raise ValueError(f"expected SB/LOOP/REC, got {val!r}")

    if val == "SB":
        n = 1
        if lx.peek() == ("sym", "("):
            lx.next()                   # '('
            # accept either bare INT or `n=INT`
            tok2 = lx.next()
            if tok2 == ("sym", "n="):
                tok2 = lx.next()
            if tok2 is None or tok2[0] != "num":
                raise ValueError(f"expected SB count, got {tok2!r}")
            n = int(tok2[1])
            lx.expect(")")
        return SB(n=n)

    if val == "LOOP":
        lx.expect("{")
        body = _parse_seq(lx)
        lx.expect("}")
        return Loop(body=body)

    if val == "REC":
        return Recur()

    raise ValueError(f"unreachable: {val!r}")


# ─────────────────────────────────────────────────────────────────────
# JSON Problem loader.
# ─────────────────────────────────────────────────────────────────────
def load_problem_json(path: str | Path) -> Problem:
    """Load a Problem from a JSON file."""
    p = Path(path)
    data = json.loads(p.read_text())
    return problem_from_dict(data)


def problem_from_dict(data: dict[str, Any]) -> Problem:
    """Build a Problem from a dict (already-parsed JSON)."""
    def _vars(field: str, role: str) -> list[Var]:
        return [
            Var(name=list(d.keys())[0],
                type=list(d.values())[0],
                role=role)
            for d in data.get(field, [])
        ]

    return Problem(
        template = parse_template(data["template"]),
        inputs   = _vars("inputs",  "input"),
        outputs  = _vars("outputs", "output"),
        locals   = _vars("locals",  "local"),
        pre      = data.get("pre",  "true"),
        post     = data.get("post", "true"),
        atoms    = data.get("atoms", {}),
        max_solutions     = data.get("max_solutions",     10),
        solver_timeout_ms = data.get("solver_timeout_ms", 60_000),
    )
