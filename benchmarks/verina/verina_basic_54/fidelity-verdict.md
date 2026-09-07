# SpecGen fidelity — verina_basic_54

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_54_CanyonSearch
  pre  soundness    XX 0/5
  pre  completeness OK 1/1
  post soundness    XX 0/5
  post completeness XX 0/15
  errors: 25 (first: pre_sound {'A': [1, 3, 5], 'B': [2, 4, 6], 'n': 3}: NameError: name 'm' is not defined)
```
