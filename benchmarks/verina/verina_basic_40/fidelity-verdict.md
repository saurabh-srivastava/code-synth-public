# SpecGen fidelity — verina_basic_40

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_40_secondSmallest
  pre  soundness    XX 0/6
  pre  completeness XX 1/4
  post soundness    OK 6/6
  post completeness OK 19/19
  errors: 9 (first: pre_sound {'A': [5, 3, 1, 4, 2], 'n': 5}: TypeError: <lambda>() missing 1 required positional argument: 'q')
```
