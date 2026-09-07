# SpecGen fidelity — verina_basic_28

VERINA's own test-based spec soundness/completeness check (specgen_check.py) on the ported spec vs VERINA's concrete tests:

```
[GAP] verina_basic_28_isPrime
  pre  soundness    OK 8/8
  pre  completeness OK 1/1
  post soundness    XX 0/8
  post completeness XX 0/8
  errors: 16 (first: post_sound {'n': 2}: ZeroDivisionError: integer modulo by zero)
```
