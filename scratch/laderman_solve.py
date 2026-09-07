"""Solve for the correct output coefficients in Laderman's 23-product
3x3 matrix multiplication.

WRITTEN: 2026-05-18 — Phase X.S edge-of-open verification.
USED FOR: benchmarks/stretch/strassen_3x3_laderman.py

CONTEXT
-------
The initial draft of strassen_3x3_laderman.py had placeholder
formulas for 6 of the 9 output cells (c21, c22, c23, c31, c32,
c33), because the author didn't have Laderman 1976 to hand and
couldn't reconstruct all 9 from memory.  Rather than guess or
search the literature, this script SOLVES for the correct
integer coefficients directly from the 23 m_i product
expressions.

STRATEGY
--------
Each m_i is a bilinear product `(α_pq a_pq) × (β_rs b_rs)` of
linear combinations of the a's and b's.  Expanded, each m_i is
a vector in the 81-dimensional basis {a_pq * b_rs}.  Each
output c_ij is the known 3-term sum `a_i1*b_1j + a_i2*b_2j +
a_i3*b_3j`, also a vector in the same basis.

If Laderman's 23 products span a subspace containing all 9
c_ij's (which they must, since the algorithm is correct), we
can solve M^T x = c_ij for an integer-coefficient x (where M
is the 23×81 matrix of m_i basis-coefficients).  SymPy's
`solve` finds the integer solution.

OUTPUT
------
Prints each c_ij as a sum of m_i's with integer coefficients.
Numerically verified across 100 random integer trials (in
benchmarks/stretch/strassen_3x3_laderman.py inline).  Found:

  c11 = m6 + m14 + m19
  c12 = m1 + m4 + m5 + m6 + m12 + m14 + m15
  c13 = m6 + m7 + m9 + m10 + m14 + m16 + m18
  c21 = m2 + m3 + m4 + m6 + m14 + m16 + m17
  c22 = m2 + m4 + m5 + m6 + m20
  c23 = m14 + m16 + m17 + m18 + m21
  c31 = m6 + m7 + m8 + m11 + m12 + m13 + m14
  c32 = m12 + m13 + m14 + m15 + m22
  c33 = m6 + m7 + m8 + m9 + m23

The original draft had 6 of these WRONG (c13, c21, c22, c23,
c32, c33); this script's output replaced them.

RE-RUNNING
----------
  cd /Users/saurabh/code/synthesizer
  .venv/bin/python scratch/laderman_solve.py

Takes ~10 seconds (sympy + numpy linear algebra over the
81-dim basis).  Dependencies: sympy, numpy in .venv.

GENERALIZING
------------
The same approach works for any bilinear algorithm: enumerate
the n_in × n_in basis of input-products, encode each m_i as a
vector in that basis, solve M^T x = c_ij for each output.
Future use: Toom-3, Strassen 2x2 variants, 3x3 boolean matmul.
"""

import sympy as sp

# 9x9 = 81 basis terms a_pq * b_rs, but only 9*3 = 27 nontrivial
# c_ij dot products use 3 each.  We use the full 81 basis to express
# each m_i.

a = sp.symbols('a11 a12 a13 a21 a22 a23 a31 a32 a33')
b = sp.symbols('b11 b12 b13 b21 b22 b23 b31 b32 b33')
A = dict(zip(['a11','a12','a13','a21','a22','a23','a31','a32','a33'], a))
B = dict(zip(['b11','b12','b13','b21','b22','b23','b31','b32','b33'], b))

# Laderman 23 products (from current benchmark file — m1..m23).
M = {}
M[1]  = (A['a11']+A['a12']+A['a13']-A['a21']-A['a22']-A['a32']-A['a33'])*B['b22']
M[2]  = (A['a11']-A['a21'])*(B['b22']-B['b12'])
M[3]  = A['a22']*(-B['b11']+B['b12']+B['b21']-B['b22']-B['b23']-B['b31']+B['b33'])
M[4]  = (-A['a11']+A['a21']+A['a22'])*(B['b11']-B['b12']+B['b22'])
M[5]  = (A['a21']+A['a22'])*(-B['b11']+B['b12'])
M[6]  = A['a11']*B['b11']
M[7]  = (-A['a11']+A['a31']+A['a32'])*(B['b11']-B['b13']+B['b23'])
M[8]  = (-A['a11']+A['a31'])*(B['b13']-B['b23'])
M[9]  = (A['a31']+A['a32'])*(-B['b11']+B['b13'])
M[10] = (A['a11']+A['a12']+A['a13']-A['a22']-A['a23']-A['a31']-A['a32'])*B['b23']
M[11] = A['a32']*(-B['b11']+B['b13']+B['b21']-B['b22']-B['b23']-B['b31']+B['b32'])
M[12] = (-A['a13']+A['a32']+A['a33'])*(B['b22']+B['b31']-B['b32'])
M[13] = (A['a13']-A['a33'])*(B['b22']-B['b32'])
M[14] = A['a13']*B['b31']
M[15] = (A['a32']+A['a33'])*(-B['b31']+B['b32'])
M[16] = (-A['a13']+A['a22']+A['a23'])*(B['b23']+B['b31']-B['b33'])
M[17] = (A['a13']-A['a23'])*(B['b23']-B['b33'])
M[18] = (A['a22']+A['a23'])*(-B['b31']+B['b33'])
M[19] = A['a12']*B['b21']
M[20] = A['a23']*B['b32']
M[21] = A['a21']*B['b13']
M[22] = A['a31']*B['b12']
M[23] = A['a33']*B['b33']

# Expand each m_i; collect coefficients on the 81 basis terms.
basis = []
for ai in a:
    for bj in b:
        basis.append(ai * bj)
basis_idx = {term: i for i, term in enumerate(basis)}

def vec(expr):
    """Return the coefficient vector of `expr` in the basis."""
    poly = sp.expand(expr)
    v = [0] * len(basis)
    if poly.is_Add:
        terms = poly.args
    else:
        terms = [poly]
    for t in terms:
        # Each term should be coef * a_pq * b_rs.
        c = sp.Integer(1)
        ab = []
        if t.is_Mul:
            for factor in t.args:
                if factor.is_number:
                    c *= factor
                else:
                    ab.append(factor)
        else:
            ab = [t]
        # Now ab is a product of an a and a b.
        if len(ab) == 2:
            term = ab[0] * ab[1]
            if term in basis_idx:
                v[basis_idx[term]] += int(c)
            else:
                # Maybe the order is swapped.
                term2 = ab[1] * ab[0]
                if term2 in basis_idx:
                    v[basis_idx[term2]] += int(c)
                else:
                    print(f"WARN: term {term} not in basis")
        else:
            print(f"WARN: skipping term {t}")
    return v

# Build M as a matrix: rows = m_i, columns = basis.
import numpy as np
M_mat = np.array([vec(M[i]) for i in range(1, 24)], dtype=int)

# Each c_ij target vector.
def c_vec(i, j):
    expr = A[f'a{i}1']*B[f'b1{j}'] + A[f'a{i}2']*B[f'b2{j}'] + A[f'a{i}3']*B[f'b3{j}']
    return vec(expr)

# Solve M^T @ x = c_ij (over rationals; check integer solutions).
from sympy import Matrix
M_sym = Matrix(M_mat.tolist()).T  # 81 x 23
print(f"M^T shape: {M_sym.shape}")

for i in (1, 2, 3):
    for j in (1, 2, 3):
        cv = c_vec(i, j)
        cv_sym = Matrix(cv)
        # Solve M_sym * x = cv_sym.  Use linear_eq_to_matrix or solve.
        x = sp.symbols(f'x1:24')
        eqs = []
        for r in range(M_sym.rows):
            row_expr = sum(M_sym[r, k] * x[k] for k in range(23))
            eqs.append(row_expr - cv_sym[r])
        sol = sp.solve(eqs, x, dict=True)
        if not sol:
            print(f"c{i}{j}: NO SOLUTION")
        else:
            soln = sol[0]
            coefs = [soln.get(x[k], 0) for k in range(23)]
            # Map any free parameters (if underdetermined) to 0.
            free_syms = set()
            for c in coefs:
                free_syms |= c.free_symbols
            if free_syms:
                # Substitute free symbols with 0 to get a particular solution.
                subst = {s: 0 for s in free_syms}
                coefs = [c.subs(subst) for c in coefs]
            # Build readable expression.
            terms = []
            for k in range(23):
                cc = int(coefs[k])
                if cc == 0:
                    continue
                if cc == 1:
                    terms.append(f"m{k+1}")
                elif cc == -1:
                    terms.append(f"- m{k+1}")
                else:
                    terms.append(f"{cc:+d}*m{k+1}")
            formula = " + ".join(terms).replace("+ -", "- ")
            print(f"c{i}{j} = {formula}")
