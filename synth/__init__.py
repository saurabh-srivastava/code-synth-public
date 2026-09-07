"""synth — proof-theoretic program synthesizer (POPL'10 + PLDI'11 line).

Phase 1.A scope: single-hole, single-atom encoding over a Python eDSL.
See DESIGN.md and CLAUDE.md at repo root for design and decisions.
"""

from .ir import Problem, SB, Loop, Seq, Recur, Var
from .result import SolveResult, NoSolution, Timeout, Solution
from .solver import solve
from .emit_c import emit_c
from .emit_py import emit_py
from .emit_rust import emit_rust

__all__ = [
    "Problem", "SB", "Loop", "Seq", "Recur", "Var",
    "SolveResult", "NoSolution", "Timeout", "Solution",
    "solve",
    "emit_c",
    "emit_py",
    "emit_rust",
]
