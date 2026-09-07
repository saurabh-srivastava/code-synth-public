# benchmarks/open_prbs

Per-problem directories tracking candidates from `OPEN_PRBS.md`
— algorithms whose published "best known" has an open gap below
it.

Directory structure (per problem):

```
benchmarks/open_prbs/<problem_name>/
├── problem.py         (main searchable artifact)
├── REPORT.md          (background, results, references)
├── <helper files>     (verifications, discrims, sub-searches)
└── ...
```

`REPORT.md` for each problem covers:

  - (a) background and context (why important)
  - (b) known results from the literature
  - (c) replications / confirmations the synthesizer finds
  - (d) NEW RESULTS the synthesizer discovers (publishable or
        interesting variants)
  - (e) NEGATIVE results (things tried that failed)
  - (f) references

Excluded from the default quick / slow regression suites
(`tests/regression.py`); each `problem.py` is runnable
standalone.

## Active problems

| Problem | Status | Highlight |
| --- | --- | --- |
| `karatsuba_gf2/` | active | R(3) = 6 and R(4) = 9 over GF(2) Z3-kernel-confirmed; n=5+ in progress |

## Branch policy

These benchmarks live on `experimental/open-prbs-*` branches
until they validate end-to-end + survive a regression.  Merging
to main means we're committed to the direction.  Until then,
each branch can be dropped.
