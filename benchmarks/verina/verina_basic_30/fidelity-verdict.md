# SpecGen fidelity — verina_basic_30

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_30_elementWiseModulo
  pre  soundness    OK 3/3
  pre  completeness XX 0/1
  post soundness    XX 0/3
  post completeness OK 7/7
  errors: 2 (first: post_sound {'A': [10, 20, 30], 'B': [3, 7, 5], 'R': [10, 20, 30], 'n': 3}: ZeroDivisionError: integer modulo by zero)
```
