# SpecGen fidelity — verina_basic_20

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_20_uniqueProduct
  pre  soundness    OK 7/7
  pre  completeness OK 0/0
  post soundness    XX 0/7
  post completeness XX 0/21
  errors: 28 (first: post_sound {'A': [2, 3, 2, 4], 'n': 4}: NameError: name 'uprod' is not defined)
```
