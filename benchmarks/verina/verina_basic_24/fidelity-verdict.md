# SpecGen fidelity — verina_basic_24

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_24_firstEvenOddDifference
  pre  soundness    OK 5/5
  pre  completeness OK 1/1
  post soundness    XX 0/5
  post completeness XX 0/15
  errors: 20 (first: post_sound {'A': [2, 3, 4, 5], 'n': 4}: NameError: name 'fe' is not defined)
```
