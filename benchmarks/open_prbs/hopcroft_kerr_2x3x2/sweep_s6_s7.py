"""sweep_s6_s7.py — continue speculation sweep at S6, S7 (skipping
S5 which wedged with 6 parametric extras)."""
import sys
sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/hopcroft_kerr_2x3x2')
from sweep_speculations import run_speculation, a_mapping_for_cols, b_mapping_for_rows


def main():
    print("Continuation: S6, S7.\n")

    a01 = a_mapping_for_cols([0, 1])
    b01 = b_mapping_for_rows([0, 1])
    out_a0 = [0, 3]
    out_b0 = [0, 1]
    out_a2 = [2, 5]
    out_b2 = [4, 5]

    results = []

    # S6: 2 outer products (one per col 0 and col 2) + 2 extras = K=10.
    results.append(("S6: 2×Outer(k=0,2) + 2",
                    run_speculation(
                        "S6",
                        [("outer_2x1_1x2", out_a0, out_b0),
                         ("outer_2x1_1x2", out_a2, out_b2)], 2,
                        timeout_s=120)))

    # S7 baseline: Strassen + 4 extras = K=11 (known SAT).
    results.append(("S7: Strassen(k=0,1) + 4 (K=11 sanity)",
                    run_speculation(
                        "S7", [("strassen_2x2", a01, b01)], 4,
                        timeout_s=120)))

    # S8: 3 outer products covering 3 col×row pairs, no extras.
    # 3 × 4 = 12 mults = naive baseline.  Sanity.
    out_a1 = [1, 4]
    out_b1 = [2, 3]
    results.append(("S8: 3×Outer (no extras, K=12 sanity)",
                    run_speculation(
                        "S8",
                        [("outer_2x1_1x2", out_a0, out_b0),
                         ("outer_2x1_1x2", out_a1, out_b1),
                         ("outer_2x1_1x2", out_a2, out_b2)], 0,
                        timeout_s=120)))

    # S9: 3 outer products + sharing via -1 extras... actually can't
    # have -1 extras.  Skip; would need a different framing.

    # S10: Strassen + 1 outer-product (col 2) + 0 extras = K=11 (Hopcroft-Kerr exact).
    results.append(("S10: Strassen(k=0,1) + Outer(k=2) + 0",
                    run_speculation(
                        "S10",
                        [("strassen_2x2", a01, b01),
                         ("outer_2x1_1x2", out_a2, out_b2)], 0,
                        timeout_s=120)))

    # S11: Strassen + 1 outer-product (col 2) - try at K=10 by adding -1 extras (subtract).
    # Can't subtract.  But we can search WITHOUT the outer product and try to find K=10
    # via Strassen + 3 cross-block extras... that's S1.

    # S12: Naive-2x2 (cols 0,1) + Outer (col 2) = 8 + 4 = 12 (sanity, equivalent to naive).
    results.append(("S12: Naive 2×2 + Outer(col2) (K=12 sanity)",
                    run_speculation(
                        "S12",
                        [("naive_2x2", a01, b01),
                         ("outer_2x1_1x2", out_a2, out_b2)], 0,
                        timeout_s=120)))

    print("\n" + "=" * 70)
    print(f"{'Speculation':<46} {'Verdict':<10} {'Time':>10}")
    print("=" * 70)
    for name, (verdict, t) in results:
        print(f"{name:<46} {verdict:<10} {t:>8.2f}s")


if __name__ == "__main__":
    main()
