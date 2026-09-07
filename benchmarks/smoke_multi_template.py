"""Multi-template smoke benchmark — two algorithms for s = 1+2+...+N.

Validates the `synth.multi_template.multi_template_solve` harness:
runs N variants in parallel subprocesses and aggregates results.

Two variants, same spec (Pre `N >= 0`, Post `2*s == N*(N+1)`):

  - VARIANT_COUNT_UP   — `i := 0; while i < N: i += 1; s += i`.
                          Standard count-up loop.  Invariant
                          `2*s == i*(i+1)`, ϕ = N - i.

  - VARIANT_COUNT_DOWN — `i := N; while i > 0: s += i; i -= 1`.
                          Count-down loop.  Different invariant
                          `2*s == (N - i)*(N + i + 1)`, ϕ = i.

Both compute the same s but follow distinct algorithm strategies.
Both should synth in ~1-2s independently, so the harness's
parallel total wall ≈ max(variant times), not their sum.

Architecture notes in RESEARCH.md §I.
"""
from synth import Problem, SB, Loop, Var
from synth.multi_template import multi_template_solve


def _common() -> dict:
    """Shared problem parts — copied into each variant."""
    return dict(
        inputs   = [Var("N", "int", "input")],
        outputs  = [Var("s", "int", "output")],
        locals   = [Var("i", "int", "local")],
        pre      = "N >= 0",
        post     = "2*s == N*(N + 1)",
    )


VARIANT_COUNT_UP = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    atoms = {
        "tau@L0": [
            "2*s == i*(i + 1)",
            "0 <= i",
            "i <= N",
        ],
        "g@L0":   ["i < N"],
        "phi@L0": ["N - i"],
        "s@B0":   [{"s": "0", "i": "0"}],
        "s@B1":   [{"s": "s + i + 1", "i": "i + 1"}],
        "s@B2":   [{"s": "s"}],   # finalize: identity.
    },
    **_common(),
)


VARIANT_COUNT_DOWN = Problem(
    template = SB() >> Loop(SB()) >> SB(),
    atoms = {
        # Count down: at iteration with current i, s holds the partial
        # sum of i+1 .. N, so the invariant is:
        #     2*s == (N - i)*(N + i + 1)
        # At i = N: 2*s == 0    → s = 0     ✓
        # At i = 0: 2*s == N*(N+1) → s = N(N+1)/2 (the post) ✓
        "tau@L0": [
            "2*s == (N - i)*(N + i + 1)",
            "0 <= i",
            "i <= N",
        ],
        "g@L0":   ["i > 0"],
        "phi@L0": ["i"],
        "s@B0":   [{"s": "0", "i": "N"}],
        "s@B1":   [{"s": "s + i", "i": "i - 1"}],
        "s@B2":   [{"s": "s"}],   # finalize: identity.
    },
    **_common(),
)


if __name__ == "__main__":
    import time
    t = time.monotonic()
    result = multi_template_solve(
        variants=[
            ("count_up",   VARIANT_COUNT_UP),
            ("count_down", VARIANT_COUNT_DOWN),
        ],
        parallel=True,
    )
    wall = time.monotonic() - t
    print(f"Total wall: {wall:.1f}s")
    print()
    print("=== Multi-template exploration table ===")
    print(f"{'#':<3} {'variant':<15} {'status':<14} {'wall':>8} {'score':>8}")
    print("-" * 60)
    for k, v in enumerate(result.variants):
        score = f"{v.score:.2f}" if v.score is not None else "—"
        print(f"{k:<3} {v.name:<15} {v.status:<14} "
              f"{v.elapsed_s:>6.1f}s {score:>8}")
    print()
    if result.best:
        print(f"Best variant: {result.best.name} "
              f"(score {result.best.score:.2f})")
    else:
        print("No variant succeeded.")
