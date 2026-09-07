# SpecGen fidelity — verina_basic_86

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_86_rotate
  pre  soundness    OK 6/6
  pre  completeness OK 1/1
  post soundness    XX 5/6
  post completeness XX 10/12
  errors: 3 (first: post_sound {'A': [], 'offset': 5, 'n': 0}: ZeroDivisionError: integer modulo by zero)
```
