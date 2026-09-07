# SpecGen fidelity — verina_basic_10

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_10_isGreater
  pre  soundness    XX 4/7
  pre  completeness OK 1/1
  post soundness    XX 0/7
  post completeness XX 1/7
  errors: 11 (first: post_sound {'n': 6, 'A': [1, 2, 3, 4, 5]}: NameError: name 't' is not defined)
```
