"""slp_gamma_probe.py — focus on Strassen's γ-side min SLP.

Strassen's 4 output combiners:
  c00 = m0 + m3 - m4 + m6
  c01 = m2 + m4
  c10 = m1 + m3
  c11 = m0 - m1 + m2 + m5

Heun count: 8 binary adds (no sharing).  Our smoke test found
L=6 UNSAT, L=7 unknown.  Settle whether the true min is 7 or 8.
"""
import sys
import time
sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/karstadt_schwartz_2x2')
from slp_forms import min_slp, STRASSEN_OUTPUT, encode_slp_for_forms
from z3 import sat, unsat, set_param

D = 7  # 7 base inputs (m_0..m_6)


def check_L(L, timeout_s):
    set_param("parallel.enable", True)
    solver, _, _, _ = encode_slp_for_forms(STRASSEN_OUTPUT, L, D)
    solver.set("timeout", timeout_s * 1000)
    t0 = time.monotonic()
    r = solver.check()
    elapsed = time.monotonic() - t0
    return str(r), elapsed


def main():
    print("Strassen γ min-SLP probe.")
    print(f"  Targets: {STRASSEN_OUTPUT}")
    print()

    # L=7 with 1800s budget.
    print(f"L=7 (1800s budget):")
    verdict, elapsed = check_L(7, 1800)
    print(f"  Verdict: {verdict}  ({elapsed:.2f}s)")
    sys.stdout.flush()

    # L=8 (sanity SAT).
    print(f"\nL=8 (sanity, 600s budget):")
    verdict, elapsed = check_L(8, 600)
    print(f"  Verdict: {verdict}  ({elapsed:.2f}s)")


if __name__ == "__main__":
    main()
