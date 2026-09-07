# SpecGen fidelity — verina_basic_51

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_51_BinarySearch
  pre  soundness    XX 0/5
  pre  completeness XX 0/1
  post soundness    OK 5/5
  post completeness OK 15/15
  errors: 6 (first: pre_sound {'A': [1, 3, 5, 7, 9], 'key': 5, 'n': 5}: TypeError: <lambda>() missing 1 required positional argument: 'q')
```
