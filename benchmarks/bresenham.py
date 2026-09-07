"""bresenham — Phase 3.O: Bresenham's line-drawing algorithm.

Draws a discrete line from (0, 0) to (dx, dy) with slope ≤ 1
(precondition `dx >= dy >= 0`).  The plotted y-coordinate at each x
is recorded in `A[0..dx-1]`.

    x := 0;
    y := 0;
    v := 2*dy - dx;
    while (x < dx) {
        A[x] := y;
        if (v < 0)  v := v + 2*dy;
        else        { y := y + 1; v := v + 2*dy - 2*dx; }
        x := x + 1;
    }
    // post: x == dx  (basic termination — full quantified pixel-
    //                 correctness post is a follow-up; see notes)

Algebraic invariant
-------------------
The error term `v` satisfies, before each x-iteration:

    v == 2*dy*x - 2*dx*y - dx + 2*dy

This is exactly the published Bresenham invariant in integer form
(scaled by 2 to avoid fractions).  Proof by induction:

  Init: v = 2*dy - dx; x = 0, y = 0.  Plug in: 0 - 0 - dx + 2*dy
        = 2*dy - dx. ✓
  Step branch 0 (v < 0): v_new = v + 2*dy; x_new = x+1; y_new = y.
        2*dy*(x+1) - 2*dx*y - dx + 2*dy
          = 2*dy*x + 2*dy - 2*dx*y - dx + 2*dy
          = (2*dy*x - 2*dx*y - dx + 2*dy) + 2*dy
          = v + 2*dy.  ✓
  Step branch 1 (v ≥ 0): v_new = v + 2*dy - 2*dx; x_new = x+1;
                          y_new = y+1.
        2*dy*(x+1) - 2*dx*(y+1) - dx + 2*dy
          = (2*dy*x - 2*dx*y - dx + 2*dy) + 2*dy - 2*dx
          = v + 2*dy - 2*dx.  ✓

The τ atoms below are intentionally minimal — exactly the conjuncts
that the proof obligations need.  No quantified pixel-correctness
atom yet (that would add `∀p. 0 ≤ p < x ⇒ |2*A[p]*dx - 2*dy*p| ≤ dx`
which compounds bilinear + array + ∀; tractability TBD as a
follow-up).

Spec:
    Pre  : dx >= dy ∧ dy >= 0
    Post : x == dx  (loop terminates as expected)
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
    # Strong post: loop terminates AND the algebraic invariant holds
    # at exit (with x = dx).  The algebraic relation is the heart of
    # Bresenham's correctness — it's what links `v` to the pixel
    # coordinates.  Forcing it into the post makes the synthesizer
    # carry it as a τ atom (otherwise the trivial τ `0 ≤ x ≤ dx`
    # suffices to prove termination alone).
    post     = "x == dx and v == 2*dy*dx - 2*dx*y - dx + 2*dy",

    atoms = {
        # SB0: x, y, v init.
        "s@B0": [
            {"x": "0", "y": "0", "v": "2*dy - dx"},
        ],
        # Loop invariant.
        "tau@L0": [
            "v == 2*dy*x - 2*dx*y - dx + 2*dy",   # algebraic
            "0 <= x",
            "x <= dx",
            "dy >= 0",
            "dx >= dy",
        ],
        "g@L0":   ["x < dx"],
        "phi@L0": ["dx - x"],
        # SB1: A[x] := y.
        "s@B1":   [{"A": "Update(A, x, y)"}],
        # SB2 (n=2): conditional v / y update.
        "g@B2.0": ["v < 0"],
        "s@B2.0": [{"v": "v + 2*dy"}],
        "g@B2.1": ["v >= 0"],
        "s@B2.1": [{"v": "v + 2*dy - 2*dx", "y": "y + 1"}],
        # SB3: x := x + 1.
        "s@B3":   [{"x": "x + 1"}],
    },
    max_solutions = 1,
    expected_solutions = 1,
    expected_lean_hits = 0,
    solver_timeout_ms = 300_000,
)


if __name__ == "__main__":
    result = solve(PROBLEM)
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
