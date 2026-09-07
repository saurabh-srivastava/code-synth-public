"""bresenham_full — Phase 3.O variant with the full quantified post.

Same algorithm as `bresenham.py`, but the post is the classical
Bresenham pixel-correctness statement:

    ∀k. 0 ≤ k < dx  ⇒  -dx ≤ 2·dy·k - 2·A[k]·dx ≤ dx

(each plotted pixel A[k] is within dx of the integer-scaled ideal
line `dy·k/dx`).  This forces τ to carry:
  (a) the algebraic invariant `v == 2·dy·x - 2·dx·y - dx + 2·dy`
      linking the error term to the geometry,
  (b) the v-range bounds `2·dy - 2·dx ≤ v ≤ 2·dy` (which combined
      with (a) give the pixel bound for the just-plotted index),
  (c) the carried-prefix quantified atom for already-plotted pixels.

Tractability is the open question — the inductive constraint has all
τ atoms in BOTH position so Phase 3.L's monotonicity fast path
doesn't apply, and the quantified atom adds Z3 instantiation cost
on top of the bilinear arithmetic.

Spec:
    Pre  : dx ≥ dy ∧ dy ≥ 0
    Post : ForAll(k: 0 ≤ k < dx ⇒ 2·dy·k - dx ≤ 2·A[k]·dx
                                      ≤ 2·dy·k + dx)
"""
from synth import Problem, SB, Loop, Var, solve


PROBLEM = Problem(
    template = SB(n=1) >> Loop(SB(n=1) >> SB(n=2) >> SB(n=1)),
    inputs   = [Var("dx", "int", "input"),
                Var("dy", "int", "input"),
                Var("A",  "int[]", "input")],
    outputs  = [Var("A",  "int[]", "output")],
    locals   = [Var("x", "int", "local"),
                Var("y", "int", "local"),
                Var("v", "int", "local")],
    pre      = "dx >= dy and dy >= 0",
    post     = ("ForAll(lambda k: Implies(0 <= k and k < dx, "
                "2*dy*k - dx <= 2*A[k]*dx and "
                "2*A[k]*dx <= 2*dy*k + dx))"),

    atoms = {
        "s@B0": [
            {"x": "0", "y": "0", "v": "2*dy - dx"},
        ],
        "tau@L0": [
            "v == 2*dy*x - 2*dx*y - dx + 2*dy",
            "x <= dx",
            "dy >= 0",
            "dx >= dy",
            "v <= 2*dy",
            "v >= 2*dy - 2*dx",
            ("ForAll(lambda p: Implies(0 <= p and p < x, "
             "2*dy*p - dx <= 2*A[p]*dx and "
             "2*A[p]*dx <= 2*dy*p + dx))"),
        ],
        "g@L0":   ["x < dx"],
        "phi@L0": ["dx - x"],
        "s@B1":   [{"A": "Update(A, x, y)"}],
        "g@B2.0": ["v < 0"],
        "s@B2.0": [{"v": "v + 2*dy"}],
        "g@B2.1": ["v >= 0"],
        "s@B2.1": [{"v": "v + 2*dy - 2*dx", "y": "y + 1"}],
        "s@B3":   [{"x": "x + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 600_000,
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = solve(PROBLEM)
    elapsed = time.monotonic() - t
    print(f"wall: {elapsed:.1f}s")
    if not result:
        print(f"FAILED: {result.reason}")
        for h in getattr(result, "hints", []):
            print(f"  hint: {h}")
        raise SystemExit(1)
    print(f"Found {len(result.solutions)} solution(s).\n")
    for n, sol in enumerate(result.solutions):
        print(f"── solution #{n} (score={sol.score:g}) ──")
        print(sol.code)
        print()
