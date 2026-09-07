# HumanEval+ — veri-synthesis triage (164 problems)

**Updated**: 2026-05-28.  **Source**: `evalplus/humanevalplus`
(HuggingFace).  **Method**: triage-only; no synthesis attempted.
**Branch**: `humaneval`.

## Rubric

| Tier | Meaning | What's needed |
| --- | --- | --- |
| 🟢 **GREEN**  | Drop-in ready today | Standard imperative `int` / `int[]` / `int[][]` shape; template + atoms + helpers all expressible.  Implementation cost: per-benchmark authoring effort (~1-3 hours for small problems; ~1-2 sessions for L1.6-class ones with helpers). |
| 🟡 **YELLOW** | Ready with substantial proof engineering | Same type surface but needs Tier-1 helper authoring like Slice 2.C / GS / kadane: nested loops, complex invariants, recursive-UF step axioms.  Implementation cost: ~1-3 focused sessions per benchmark. |
| 🟠 **ORANGE** | Needs minor framework extension | Small typing addition (string as `int[]` with ASCII, fixed-point reals, tuple as multi-output) OR small translator extension OR small atom-language addition.  Implementation cost: ~1 framework session + benchmark authoring. |
| 🔴 **RED**    | Needs major framework work | New data structure (`set<int>`, `dict<int,int>`, ragged 2D), graph IR, or new IR construct (variable-length output, BFS/queue primitive).  Implementation cost: multi-session framework push first. |
| ⚫ **BLACK**   | Out of scope under current direction | Genuine string/NLP semantics (`split`, `replace`, regex, case ops), file I/O, hashlib, `eval()`, randomness.  These need a string-as-symbolic-value model the project hasn't committed to. |

**Counting principles**:
  - **String inputs/outputs** with parsing semantics (`split`,
    `replace`, `lower`, `isalpha`, etc.) → BLACK.  Even if the
    spec is precise, the operations themselves don't have a
    natural axiomatization without a string theory.
  - **String as char-array** (`int[]` of ASCII) is feasible
    for problems that only need length + per-character
    comparison (palindrome, bracket balance, digit-string
    arithmetic) → ORANGE.
  - **Floats** (`List[float]`, `float` return) → ORANGE.  We
    don't have a Real sort; could add via fixed-point or
    rational encoding.
  - **Tuple returns** → already supported via multi-output
    (treat as ORANGE if not yet exercised; we have
    intdiv-style 2-output patterns).
  - **Dict / Set** → RED.  No data structure today.
  - **Ragged 2D** (`List[List[int]]` with rows of varying
    length) → RED.  We have rectangular `int[][]` only.

## Summary table

| Tier | Count | % |
| --- | --- | --- |
| 🟢 GREEN  | 47  | 28.7% |
| 🟡 YELLOW | 19  | 11.6% |
| 🟠 ORANGE | 32  | 19.5% |
| 🔴 RED    | 10  |  6.1% |
| ⚫ BLACK   | 56  | 34.1% |
| **Total** | 164 | 100%  |

**Headline**: **40% reachable today** (GREEN + YELLOW = 66
problems) with existing framework + per-benchmark proof
engineering.  Another ~20% (ORANGE = 32) opens up with small
framework additions (string-as-int[], fixed-point reals,
digit-string arithmetic) — push the reachable count to **~60%
(98 problems)**.  The remaining 34% is genuine string / NLP /
dict / hash / eval territory and is not worth pursuing within
the current project direction.

## What would maximize coverage with bounded framework work

1. **ASCII-string-as-`int[]`** (~15 problems): unblocks
   palindrome, bracket balance, digit counting, char
   filtering, length-based predicates.  Modeling each
   string op as an axiom over the int-array of code points;
   needs a few core string primitives (`length`, indexing,
   slicing-via-window-iteration, `chr`/`ord` as identity).
   Estimated framework cost: 1 session for the int[] mapping
   + axiom library; ~1-2 days.

2. **Fixed-point or rational `Real`** (~10 problems): floats
   in HumanEval are mostly small fractions.  Encode as
   `(numerator: int, denom: int)` pair or `int * 10^k` fixed-
   point.  Many spec-checks become integer divisibility
   checks.  Estimated framework cost: 1-2 sessions.

3. **Variable-length output `int[]`** (~8 problems): output
   length depends on input.  Could be modeled with an output
   array + a length variable; declares output values only
   `0 ≤ k < len_out`.  Estimated framework cost: 1 session.

4. **Tuple return** (~5 problems): already feasible via
   multi-output; just need to validate the pattern on a
   couple of HumanEval-style benchmarks.

## Methodology caveats

- Triage is based on canonical solution shape, not on the
  underlying mathematical content.  Some YELLOW ratings
  could turn out to be RED if the spec needs an axiom that
  isn't tractable.
- GREEN does NOT mean "easy" — it means "no framework
  blockers."  A GREEN problem may still need 1-3 hours of
  authoring effort.
- Many problems with simple algorithmic content
  (e.g., #36 `fizz_buzz`) are rated ORANGE because the spec
  requires digit-string arithmetic.  These could be GREEN
  under a "digit extraction" axiom library.
- The triage does NOT use HumanEval+'s extended tests for
  rating — only the canonical solution + docstring.

---

## Per-problem triage

Each entry: `HE/N` + signature + rating + rationale (1-2
sentences pointing at the blocker if not GREEN).  Rationale
is per-problem; cross-cutting patterns are captured above.

### HE/0 — has_close_elements(numbers: List[float], threshold: float) -> bool 🟠 ORANGE
List of floats with absolute-difference threshold.  Floats are the blocker.  Algorithm itself is a sorted-adjacent-pair scan — would be GREEN under fixed-point Real.

### HE/1 — separate_paren_groups(paren_string: str) -> List[str] ⚫ BLACK
String parsing with variable-count string output.  Requires both string semantics and ragged list-of-strings output.

### HE/2 — truncate_number(number: float) -> float 🟠 ORANGE
Float decomposition.  `number - int(number)` is trivial under any Real encoding.

### HE/3 — below_zero(operations: List[int]) -> bool 🟢 GREEN
Running sum with early-exit on negative.  Single loop, `int[]` input, bool output.  Standard.

### HE/4 — mean_absolute_deviation(numbers: List[float]) -> float 🟠 ORANGE
Floats + averaging.  Under fixed-point Real becomes integer arithmetic with a denominator.

### HE/5 — intersperse(numbers: List[int], delimeter: int) -> List[int] 🟠 ORANGE
Output length is `2*len(numbers)-1` — deterministic from input but variable.  Needs variable-length output array support.

### HE/6 — parse_nested_parens(paren_string: str) -> List[int] ⚫ BLACK
String split + nested-paren depth.  Multiple strings + string parsing.

### HE/7 — filter_by_substring(strings: List[str], substring: str) -> List[str] ⚫ BLACK
String container, substring containment.  Pure string semantics.

### HE/8 — sum_product(numbers: List[int]) -> Tuple[int, int] 🟢 GREEN
Simple loop computing sum and product simultaneously.  Tuple return = 2 outputs.  Standard.

### HE/9 — rolling_max(numbers: List[int]) -> List[int] 🟢 GREEN
Same-length output of running maximum.  Single loop.  Standard.

### HE/10 — make_palindrome(string: str) -> str ⚫ BLACK
String reversal + concatenation.  Pure string semantics.

### HE/11 — string_xor(a: str, b: str) -> str 🟠 ORANGE
Strings of '0'/'1' XORed.  Trivial if strings are `int[]` of binary digits.

### HE/12 — longest(strings: List[str]) -> Optional[str] ⚫ BLACK
List of strings + Optional.  String semantics.

### HE/13 — greatest_common_divisor(a: int, b: int) -> int 🟢 GREEN
Tail-recursive Euclidean.  We have `Recur` + ranking; this is a textbook fit.

### HE/14 — all_prefixes(string: str) -> List[str] ⚫ BLACK
List of strings of varying lengths.  Even with string-as-int[], the output is ragged.

### HE/15 — string_sequence(n: int) -> str ⚫ BLACK
Output is a formatted string with spaces.  Pure string output construction.

### HE/16 — count_distinct_characters(string: str) -> int 🔴 RED
Set-based distinct count + case-folding.  Set is the blocker.

### HE/17 — parse_music(music_string: str) -> List[int] ⚫ BLACK
Tokenized string with 2-char tokens.  String parsing.

### HE/18 — how_many_times(string: str, substring: str) -> int 🟠 ORANGE
Substring count.  Under string-as-int[] becomes a nested-loop array-match — feasible.

### HE/19 — sort_numbers(numbers: str) -> str ⚫ BLACK
Word-to-number string mapping + sort by value + rejoin.  Pure string.

### HE/20 — find_closest_elements(numbers: List[float]) -> Tuple[float, float] 🟠 ORANGE
Floats.  Adjacent-pair scan after sorting — straightforward under Real encoding.

### HE/21 — rescale_to_unit(numbers: List[float]) -> List[float] 🟠 ORANGE
Floats + scaling.  Under fixed-point Real becomes an integer scaling op.

### HE/22 — filter_integers(values: List[Any]) -> List[int] ⚫ BLACK
Dynamic typing (`List[Any]`).  No way to model heterogeneous types in our IR.

### HE/23 — strlen(string: str) -> int 🟠 ORANGE
Length of a string.  Trivial under string-as-int[]; no native string op needed.

### HE/24 — largest_divisor(n: int) -> int 🟢 GREEN
Loop testing `n % i == 0` for divisors.  Standard.

### HE/25 — factorize(n: int) -> List[int] 🟠 ORANGE
Prime factorization.  Output length is variable (depends on n's factorization).  YELLOW under variable-length output; ORANGE because the structure is otherwise tractable.

### HE/26 — remove_duplicates(numbers: List[int]) -> List[int] 🔴 RED
Uses dict for frequency counting.  Could rephrase as O(n²) scan but the spec implies the dict semantics.

### HE/27 — flip_case(string: str) -> str ⚫ BLACK
Per-character case flip.  Even under string-as-int[], the case op is char-class-specific.

### HE/28 — concatenate(strings: List[str]) -> str ⚫ BLACK
List-of-strings concatenation.

### HE/29 — filter_by_prefix(strings: List[str], prefix: str) -> List[str] ⚫ BLACK
Pure string semantics.

### HE/30 — get_positive(l: list) 🟢 GREEN
Filter positive ints into output array.  Variable-length output but we can pre-allocate `len(l)` and track the count.

### HE/31 — is_prime(n) 🟢 GREEN
Loop testing divisors up to sqrt(n).  Standard (existing intsqrt-style benchmark).

### HE/32 — find_zero(xs: list) (Newton's method) 🔴 RED
Newton's method for polynomial root, with float convergence.  Multi-blocker: floats + iteration with convergence tolerance.

### HE/33 — sort_third(l: list) 🟡 YELLOW
Sort the subset of indices divisible by 3, leave others.  Complex spec; needs sub-array-sort sub-algorithm.

### HE/34 — unique(l: list) 🔴 RED
Sorted unique.  Uses Python set; needs set primitive or expensive O(n²) re-modeling.

### HE/35 — max_element(l: list) 🟢 GREEN
Single-pass max.  Standard.

### HE/36 — fizz_buzz(n: int) 🟠 ORANGE
Count digit '7' in numbers divisible by 11 or 13.  Digit extraction over int — needs digit-arithmetic axioms (could be a small library).

### HE/37 — sort_even(l: list) 🟡 YELLOW
Same pattern as HE/33 but for even indices.  Sub-array-sort.

### HE/38 — decode_cyclic(s: str) -> str ⚫ BLACK
String permutation in 3-char groups.  String semantics.

### HE/39 — prime_fib(n: int) 🔴 RED
Miller-Rabin primality with random witnesses + Fibonacci iteration.  Randomness + complex primality check.

### HE/40 — triples_sum_to_zero(l: list) 🟢 GREEN
Triple-nested loop testing index distinctness and sum.  Standard, brute-force shape.

### HE/41 — car_race_collision(n: int) 🟢 GREEN
Closed form `n**2`.  Trivial (acyclic).

### HE/42 — incr_list(l: list) 🟢 GREEN
Map +1 over array.  Standard (existing increment_array benchmark).

### HE/43 — pairs_sum_to_zero(l) 🟢 GREEN
Double-nested loop, distinctness check.  Standard.

### HE/44 — change_base(x: int, base: int) -> str 🟠 ORANGE
Repeated `x % base` and `x //= base` building a digit string.  Output is a digit string — encode as `int[]` of digits.

### HE/45 — triangle_area(a, h) 🟠 ORANGE
`a * h / 2` — float division.  Under Real encoding, trivial.

### HE/46 — fib4(n: int) 🟢 GREEN
4-step recurrence with iterative computation.  Existing `fib` pattern with one extra term.

### HE/47 — median(l: list) 🟡 YELLOW
Sort + odd/even index extraction.  Need a sort sub-algorithm (we have bubble/insertion/selection); median selection is a 1-line follow-up.

### HE/48 — is_palindrome(text: str) 🟠 ORANGE
Reverse + compare.  Trivial under string-as-int[].

### HE/49 — modp(n: int, p: int) -> int 🟢 GREEN
Repeated squaring for 2^n mod p.  Existing `modular_exponentiation` benchmark covers this pattern exactly.

### HE/50 — decode_shift(s: str) -> str ⚫ BLACK
Caesar cipher with chr/ord.  String semantics with char arithmetic.

### HE/51 — remove_vowels(text) ⚫ BLACK
Per-char vowel filter into string output.  String semantics.

### HE/52 — below_threshold(l: list, t: int) 🟢 GREEN
All-loop with comparison.  Standard.

### HE/53 — add(x: int, y: int) 🟢 GREEN
`x + y`.  Trivial.

### HE/54 — same_chars(s0: str, s1: str) 🔴 RED
Set equality of character sets.  Set is the blocker.

### HE/55 — fib(n: int) 🟢 GREEN
Iterative Fibonacci.  Existing benchmark.

### HE/56 — correct_bracketing(brackets: str) `<>` 🟠 ORANGE
Bracket balance with counter.  Trivial under string-as-int[] with `'<' == open`, `'>' == close`.

### HE/57 — monotonic(l: list) 🟢 GREEN
Single loop with two flags (inc, dec).  Standard.

### HE/58 — common(l1: list, l2: list) 🔴 RED
Set intersection of two lists.  Set is the blocker.

### HE/59 — largest_prime_factor(n: int) 🟡 YELLOW
Sieve of Eratosthenes + reverse scan.  Two-phase algorithm with boolean array; needs Tier-1 helpers for the sieve invariant.

### HE/60 — sum_to_n(n: int) 🟢 GREEN
Closed form `n*(n+1)/2`.  Trivial.

### HE/61 — correct_bracketing(brackets: str) `()` 🟠 ORANGE
Same as HE/56 with different bracket chars.

### HE/62 — derivative(xs: list) 🟢 GREEN
Map `xs[i] * i` for i ≥ 1.  Standard.

### HE/63 — fibfib(n: int) 🟢 GREEN
3-step recurrence.  Same shape as `fib4`.

### HE/64 — vowels_count(s) ⚫ BLACK
Vowel-set membership over characters.  String semantics.

### HE/65 — circular_shift(x, shift) -> str 🟠 ORANGE
Digit-string rotation.  Under digit-arithmetic axioms, doable; output is a string.

### HE/66 — digitSum(s) ⚫ BLACK
Sum of uppercase ASCII codes in a string.  String semantics + case detection.

### HE/67 — fruit_distribution(s, n) ⚫ BLACK
Parse "5 apples and 6 oranges" from a string.  Pure string parsing.

### HE/68 — pluck(arr) 🟢 GREEN
Find smallest even with smallest index.  Single-pass min-with-index + filter.  Standard.

### HE/69 — search(lst) 🔴 RED
Dict frequency count + max.  Dict is the blocker.

### HE/70 — strange_sort_list(lst) 🟡 YELLOW
Sort + alternate min/max picking.  Needs sort sub-algorithm + two-pointer alternation.

### HE/71 — triangle_area(a, b, c) 🟠 ORANGE
Heron's formula with sqrt.  Floats + square root.

### HE/72 — will_it_fly(q, w) 🟢 GREEN
Palindrome + sum threshold.  Standard.

### HE/73 — smallest_change(arr) 🟢 GREEN
Count mismatches between array and its reverse.  Standard.

### HE/74 — total_match(lst1, lst2) ⚫ BLACK
List of strings, total char count.  String semantics.

### HE/75 — is_multiply_prime(a) 🟡 YELLOW
Check if `a` is product of exactly 3 primes.  Sieve + factorization counting; Tier-1 helpers needed.

### HE/76 — is_simple_power(x, n) 🟢 GREEN
Loop testing if `x = n^k`.  Standard.

### HE/77 — iscube(a) 🟠 ORANGE
Integer cube test via floating-point cube root.  Without floats, can be done as a loop testing cubes; reduces to GREEN.  ORANGE because the canonical uses float.

### HE/78 — hex_key(num) ⚫ BLACK
Count prime hex digits in a hex string.  String semantics.

### HE/79 — decimal_to_binary(decimal) -> str 🟠 ORANGE
Binary conversion with "db" prefix/suffix.  Output is a string but content is digits.

### HE/80 — is_happy(s) ⚫ BLACK
3-consecutive-char distinctness over a string.  String semantics (or ORANGE under string-as-int[]).

### HE/81 — numerical_letter_grade(grades) ⚫ BLACK
Float-keyed grade lookup with string output.  Floats + strings.

### HE/82 — prime_length(string) 🟠 ORANGE
`is_prime(len(s))`.  Trivial under any string length encoding.

### HE/83 — starts_one_ends(n) 🟢 GREEN
Closed form `18 * 10^(n-2)`.  Trivial.

### HE/84 — solve(N) -> str 🟠 ORANGE
Sum of decimal digits then convert to binary string.  Needs digit-arithmetic axioms.

### HE/85 — add(lst) 🟢 GREEN
Sum even elements at odd indices.  Single-loop with index parity check.

### HE/86 — anti_shuffle(s) ⚫ BLACK
Sort characters within each word.  String semantics.

### HE/87 — get_row(lst, x) -> List[Tuple[int, int]] 🔴 RED
Ragged 2D list + variable-count tuple output.  Multi-blocker.

### HE/88 — sort_array(array) 🟡 YELLOW
Sort in reversing order based on parity of endpoints.  Needs sort + conditional reverse.

### HE/89 — encrypt(s) ⚫ BLACK
Caesar shift by 4.  String + char arithmetic.

### HE/90 — next_smallest(lst) 🟢 GREEN
Sort + first-non-min lookup.  Standard.

### HE/91 — is_bored(S) ⚫ BLACK
Sentence delimiting on `.!?` + starts-with-"I ".  String semantics.

### HE/92 — any_int(x, y, z) 🟢 GREEN
Three-int equality test (x = y+z etc.).  Trivial under int-only signature (the float-rejection branch is dynamic-typing — we accept the int version).

### HE/93 — encode(message) ⚫ BLACK
Case-swap + vowel-shift over a string.  String semantics.

### HE/94 — skjkasdkd(lst) 🟡 YELLOW
Find largest prime in list + sum its digits.  Two-phase: prime finding + digit-sum.  YELLOW under digit-arithmetic axioms.

### HE/95 — check_dict_case(dict) ⚫ BLACK
Dict iteration + string case predicates.  Multi-blocker.

### HE/96 — count_up_to(n) 🟡 YELLOW
Sieve of Eratosthenes returning list of primes.  Same shape as HE/59.

### HE/97 — multiply(a, b) 🟢 GREEN
Last-digit product via `% 10`.  Standard.

### HE/98 — count_upper(s) ⚫ BLACK
Uppercase-vowel count at even indices.  String semantics.

### HE/99 — closest_integer(value) ⚫ BLACK
Parse float string + round.  String + floats.

### HE/100 — make_a_pile(n) 🟢 GREEN
Build sequence `[n, n+2, n+4, ...]` of length n.  Standard.

### HE/101 — words_string(s) ⚫ BLACK
Split string on commas/spaces.  String semantics.

### HE/102 — choose_num(x, y) 🟢 GREEN
Return largest even in `[x, y]`.  Simple branching.

### HE/103 — rounded_avg(n, m) -> str 🟠 ORANGE
Average + binary string with "0b" prefix.  Digit-string output.

### HE/104 — unique_digits(x) 🟠 ORANGE
Filter integers with all-odd digits, sort.  Needs digit-arithmetic axioms.

### HE/105 — by_length(arr) ⚫ BLACK
Filter 1-9 ints, sort reverse, map to word strings.  String output mapping.

### HE/106 — f(n) 🟢 GREEN
Compute array where index is `i!` if even else `1+2+...+i`.  Conditional accumulation per index.

### HE/107 — even_odd_palindrome(n) 🟡 YELLOW
Count even/odd integer palindromes in `[1, n]`.  Needs digit-reversal axiom or a custom is-palindrome-on-int predicate.

### HE/108 — count_nums(arr) 🟠 ORANGE
Count elements whose signed-digit sum is > 0.  Digit-arithmetic.

### HE/109 — move_one_ball(arr) 🟡 YELLOW
Check if array is a cyclic shift of its sorted version.  Sort + cyclic-equality check.

### HE/110 — exchange(lst1, lst2) 🟠 ORANGE
Return "YES"/"NO" string based on parity counts.  ORANGE because of string-literal return; the count logic is GREEN.

### HE/111 — histogram(test) ⚫ BLACK
Dict of word counts + max-count filter.  Dict + string.

### HE/112 — reverse_delete(s, c) ⚫ BLACK
Filter chars + palindrome check + tuple return.  String semantics.

### HE/113 — odd_count(lst) ⚫ BLACK
Substitute count into a template string per input.  String semantics.

### HE/114 — minSubArraySum(nums) 🟡 YELLOW
Kadane-variant for minimum.  Existing `kadane_max_subarray` pattern; same Tier-1 helper class needed.

### HE/115 — max_fill(grid, capacity) 🟢 GREEN
2D `int[][]` grid + ceiling-division per row, sum.  Standard 2D loop (existing `matrix_init` pattern).

### HE/116 — sort_array(arr) (by bit count) 🟡 YELLOW
Sort by `popcount(x)` then by decimal value.  Needs popcount axiom or per-bit reasoning.

### HE/117 — select_words(s, n) ⚫ BLACK
String split + consonant count per word.  String semantics.

### HE/118 — get_closest_vowel(word) ⚫ BLACK
Find rightmost vowel between two consonants.  String + char-class predicates.

### HE/119 — match_parens(lst) ⚫ BLACK
Two string concats + balance check.  String semantics (could be ORANGE under string-as-int[]).

### HE/120 — maximum(arr, k) 🟡 YELLOW
Sort + top-k.  Standard sort + slice; needs sort sub-algorithm.

### HE/121 — solution(lst) 🟢 GREEN
Sum odd elements at even indices.  Single-loop with parity checks.

### HE/122 — add_elements(arr, k) 🟠 ORANGE
Sum elements with ≤ 2 decimal digits (`|x| < 100`).  Digit-count axiom.

### HE/123 — get_odd_collatz(n) 🟡 YELLOW
Collatz sequence's odd terms, sorted.  Termination is the Collatz conjecture — needs ranking that we can't easily provide; would need an explicit iteration bound from spec.

### HE/124 — valid_date(date) ⚫ BLACK
Date-string format validation.  String parsing.

### HE/125 — split_words(txt) ⚫ BLACK
Whitespace/comma split + fallback char-counting.  String semantics.

### HE/126 — is_sorted(lst) 🟡 YELLOW
Sorted check + ≤2 duplicates.  Dict-free re-modeling possible but needs sort comparison axiom.

### HE/127 — intersection(interval1, interval2) -> str 🟠 ORANGE
Interval intersection + prime length check; "YES"/"NO" output.  ORANGE for the string return; core logic is GREEN.

### HE/128 — prod_signs(arr) 🟢 GREEN
Sum of |x| times product of sign(x).  Standard.

### HE/129 — minPath(grid, k) 🔴 RED
2D grid + BFS-like neighbor-min + repeating pattern.  Graph IR + BFS = multi-day framework work.

### HE/130 — tri(n) 🟡 YELLOW
Tribonacci-like recurrence with index-parity branching.  Needs mixed integer/rational `1 + n/2` — under fixed-point Real, YELLOW.

### HE/131 — digits(n) 🟠 ORANGE
Product of odd digits.  Digit-arithmetic.

### HE/132 — is_nested(string) ⚫ BLACK
Bracket nesting depth ≥ 2 anywhere.  String semantics (ORANGE under string-as-int[]; but the algorithm is non-trivial).

### HE/133 — sum_squares(lst) 🟠 ORANGE
Ceil each + sum of squares.  Float ceil — under Real encoding, ORANGE; under integer-only spec, GREEN.

### HE/134 — check_if_last_char_is_a_letter(txt) ⚫ BLACK
Last-char alpha + space check.  String + char-class.

### HE/135 — can_arrange(arr) 🟢 GREEN
Largest index where `arr[i] < arr[i-1]`.  Reverse-scan single loop.

### HE/136 — largest_smallest_integers(lst) 🟢 GREEN
Max-negative + min-positive.  Two single-pass filters.

### HE/137 — compare_one(a, b) ⚫ BLACK
Mixed int/float/string input with comma-as-decimal-separator parsing.  Dynamic typing + string.

### HE/138 — is_equal_to_sum_even(n) 🟢 GREEN
Closed form `n ≥ 8 ∧ n % 2 == 0`.  Trivial.

### HE/139 — special_factorial(n) 🟢 GREEN
Brazilian factorial: product of factorials.  Single accumulator loop.

### HE/140 — fix_spaces(text) ⚫ BLACK
Multi-space replacement.  String semantics.

### HE/141 — file_name_check(file_name) ⚫ BLACK
Filename-format validation with extension whitelist.  String parsing.

### HE/142 — sum_squares(lst) 🟢 GREEN
Index-conditional squaring/cubing/summing.  Single loop with branches on `i % 3`, `i % 4`.

### HE/143 — words_in_sentence(sentence) ⚫ BLACK
Filter words by prime length, rejoin.  String semantics.

### HE/144 — simplify(x, n) ⚫ BLACK
Fraction strings like "1/5".  String parsing.

### HE/145 — order_by_points(nums) 🟡 YELLOW
Stable sort by signed-digit sum.  Needs digit-arithmetic + stable sort.

### HE/146 — specialFilter(nums) 🟠 ORANGE
Count integers > 10 with first/last digit odd.  Digit-arithmetic.

### HE/147 — get_max_triples(n) 🟡 YELLOW
Count triples (i,j,k) with `a[i] + a[j] + a[k] ≡ 0 (mod 3)` where `a[i] = i² - i + 1`.  Closed-form counting argument — needs combinatorial reasoning.

### HE/148 — bf(planet1, planet2) ⚫ BLACK
Planet-name string lookup + slice + tuple of strings.  String semantics.

### HE/149 — sorted_list_sum(lst) ⚫ BLACK
Filter even-length strings, sort.  String semantics.

### HE/150 — x_or_y(n, x, y) 🟢 GREEN
Return x if prime(n) else y.  Uses existing is_prime pattern.

### HE/151 — double_the_difference(lst) 🟢 GREEN
Sum of squares of positive odd integers.  Single-loop filter+square (ignoring the float-rejection branch).

### HE/152 — compare(game, guess) 🟢 GREEN
Element-wise absolute difference.  Standard map.

### HE/153 — Strongest_Extension(class_name, extensions) ⚫ BLACK
List-of-strings + per-string case counting + max + concat.  String semantics.

### HE/154 — cycpattern_check(a, b) ⚫ BLACK
Rotation-substring search.  String semantics.

### HE/155 — even_odd_count(num) 🟠 ORANGE
Count even/odd digits of integer.  Digit-arithmetic.

### HE/156 — int_to_mini_roman(number) ⚫ BLACK
Integer to lowercase Roman numeral string.  String construction.

### HE/157 — right_angle_triangle(a, b, c) 🟢 GREEN
`a² + b² == c²` for any ordering.  Standard.

### HE/158 — find_max(words) ⚫ BLACK
List-of-strings + per-string distinct-char count + max.  String + set semantics.

### HE/159 — eat(number, need, remaining) 🟢 GREEN
Branch on `need vs remaining`, two-int output.  Standard.

### HE/160 — do_algebra(operator, operand) ⚫ BLACK
Evaluate string-built arithmetic expression with `eval()`.  String semantics + meta-execution.

### HE/161 — solve(s) ⚫ BLACK
Char-by-char case-swap or reverse if no letters.  String semantics.

### HE/162 — string_to_md5(text) ⚫ BLACK
Cryptographic hash.  Out of scope (no axiomatization of MD5).

### HE/163 — generate_integers(a, b) 🟢 GREEN
Even digits between `a` and `b` capped at 10.  Standard.

---

## What's next

This triage is **read-only classification**.  No synthesis was
attempted on any of these.  A natural follow-up push would be:

1. **Pick 5-10 GREEN problems** and author them end-to-end to
   validate the rating (~1-2 sessions).  Likely candidates:
   HE/3 (below_zero), HE/13 (gcd), HE/49 (modp — analog of
   existing modexp), HE/60 (sum_to_n), HE/97 (multiply unit
   digit), HE/121 (sum odd at even index), HE/150 (x_or_y).
2. **Implement the string-as-`int[]` extension** — biggest
   coverage win per session of framework work.  Unblocks
   ~15 ORANGE problems including HE/11, HE/18, HE/23, HE/48,
   HE/56, HE/61, HE/82 (palindrome / bracket balance / length
   predicates).
3. **Implement fixed-point Real** — unblocks ~10 ORANGE
   problems (HE/0, HE/2, HE/4, HE/20, HE/21, HE/45, HE/71, ...).
4. **Variable-length output array** — unblocks HE/5, HE/25,
   HE/30, HE/100 and similar.

Total reachable with ~3 framework sessions + per-benchmark
authoring: ~90 of 164 (~55%).  The remaining ~75 are genuine
string/NLP/dict territory that the project hasn't committed
to modeling.
