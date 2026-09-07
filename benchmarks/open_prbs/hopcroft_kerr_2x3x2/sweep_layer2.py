"""sweep_layer2.py — second-layer speculation sweep using
the flat boolean encoding (avoids NIA wedge).

Retries S5 and adds new speculations:
  S5':  1 Outer-product + 6 extras = K=10  (was TIMEOUT with NIA)
  Z1:  Naive 2×2 + 1 Outer + 0 extras = K=12 (sanity SAT)
  Z2:  Strassen + 2 Outers + 0 extras = K=15 (sanity SAT, over-K)
  Z3:  Strassen + 3 extras + LARGER coefficient space — same as S1.
  Z4:  2 Strassens overlapping... no canonical way; skip.
  Z5:  K=11 baseline at K_extra=4 with flat encoding (sanity for new enc).
  Z6:  K=10 with NO library + 10 extras = direct (likely wedges; bg runs it).
"""
import sys
sys.path.insert(0, '/Users/saurabh/code/synthesizer/benchmarks/open_prbs/hopcroft_kerr_2x3x2')
from sweep_speculations import run_speculation, a_mapping_for_cols, b_mapping_for_rows


def main():
    print("Layer-2 sweep (flat boolean encoding).\n")
    a01 = a_mapping_for_cols([0, 1])
    b01 = b_mapping_for_rows([0, 1])
    out_a0 = [0, 3]; out_b0 = [0, 1]
    out_a1 = [1, 4]; out_b1 = [2, 3]
    out_a2 = [2, 5]; out_b2 = [4, 5]

    results = []

    # Retry S5 with flat encoding.
    results.append(("S5': 1 Outer(col 2) + 6 extras (K=10)",
                    run_speculation(
                        "S5'", [("outer_2x1_1x2", out_a2, out_b2)], 6,
                        timeout_s=600)))

    # Sanity: K=11 baseline with new encoding.
    results.append(("Z5: Strassen + 4 extras (K=11, sanity)",
                    run_speculation(
                        "Z5", [("strassen_2x2", a01, b01)], 4,
                        timeout_s=120)))

    # Z1: Naive 2×2 + Outer (k=2) + 0 extras (K=12 sanity)
    results.append(("Z1: Naive2x2 + Outer(k=2) + 0  (K=12)",
                    run_speculation(
                        "Z1",
                        [("naive_2x2", a01, b01),
                         ("outer_2x1_1x2", out_a2, out_b2)], 0,
                        timeout_s=60)))

    # Z2: K=11 via Strassen + Outer (Hopcroft-Kerr canonical) sanity.
    results.append(("Z2: Strassen + Outer(k=2) + 0  (K=11 HK)",
                    run_speculation(
                        "Z2",
                        [("strassen_2x2", a01, b01),
                         ("outer_2x1_1x2", out_a2, out_b2)], 0,
                        timeout_s=60)))

    # Z3: 2 outer-products on cols 0 and 2 + 3 extras = K=11.
    results.append(("Z3: 2 Outer + 3 extras  (K=11)",
                    run_speculation(
                        "Z3",
                        [("outer_2x1_1x2", out_a0, out_b0),
                         ("outer_2x1_1x2", out_a2, out_b2)], 3,
                        timeout_s=120)))

    # Z4: 2 outer-products on cols 0 and 2 + 1 extra = K=9 (UNSAT expected
    # since K=9 < 11 and there's likely no way).
    results.append(("Z4: 2 Outer + 1 extra (K=9, below pub)",
                    run_speculation(
                        "Z4",
                        [("outer_2x1_1x2", out_a0, out_b0),
                         ("outer_2x1_1x2", out_a2, out_b2)], 1,
                        timeout_s=60)))

    print("\n" + "=" * 70)
    print(f"{'Speculation':<46} {'Verdict':<10} {'Time':>10}")
    print("=" * 70)
    for name, (verdict, t) in results:
        print(f"{name:<46} {verdict:<10} {t:>8.2f}s")


if __name__ == "__main__":
    main()
