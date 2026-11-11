"""Floating-point check of Theorems 1 and 2 and of the odd-cycle remark."""
import numpy as np
from scipy.linalg import eigh

def gap_walk(n, k, w):
    A = np.zeros((n, n))
    for i in range(n):
        A[i, (i + 1) % n] = A[(i + 1) % n, i] = 1
    A[0, k] += w; A[k, 0] += w
    D = np.diag(A.sum(1)); L = D - A
    ev = eigh(L, D, eigvals_only=True)
    return ev[1]

def gap_mh(n, k, w):
    A = np.zeros((n, n))
    for i in range(n):
        A[i, (i + 1) % n] = A[(i + 1) % n, i] = 1
    A[0, k] += w; A[k, 0] += w
    d = A.sum(1)
    K = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i != j and A[i, j] > 0:
                K[i, j] = A[i, j] / max(d[i], d[j])
        K[i, i] = 1 - K[i].sum()
    assert np.allclose(K, K.T) and (K >= -1e-15).all()
    ev = np.sort(np.linalg.eigvalsh(np.eye(n) - K))
    return ev[1]

worst_eq = 0; strict_ok = 0; bound_ok = 0; mh_ok = 0; cases = 0
for n in range(4, 41, 2):
    m = n // 2; a = 1 - np.cos(np.pi / m); th = 2 * np.pi / n
    for k in range(2, m + 1):
        for w in (0.01, 0.3, 1, 7, 500):
            cases += 1
            g = gap_walk(n, k, w)
            if k == m:
                worst_eq = max(worst_eq, abs(g - a))
            else:
                t = np.cos(np.pi * k / n)
                ub = a / (1 + 2 * w * t * t / (n + w))
                strict_ok += g < a - 1e-12
                bound_ok += g <= ub + 1e-12
            b = w / (2 + w); al = np.pi * k / n
            ubm = a - 4 * b / n * (a * a * np.cos(al) ** 2 + np.sin(th) ** 2 * np.sin(al) ** 2)
            gm = gap_mh(n, k, w)
            mh_ok += (gm <= ubm + 1e-12) and (gm < a - 1e-12)
print("cases", cases, "antipodal max |gap-a|", worst_eq)
print("nonantipodal strict", strict_ok, "bound holds", bound_ok, "MH bound+strict", mh_ok)
# odd cycles: strict bound for every chord
odd = 0; oddn = 0
for n in range(5, 30, 2):
    a = 1 - np.cos(2 * np.pi / n)
    for k in range(2, n // 2 + 1):
        for w in (0.3, 1, 7):
            oddn += 1
            t = np.cos(np.pi * k / n)
            odd += gap_walk(n, k, w) <= a / (1 + 2 * w * t * t / (n + w)) + 1e-12
print("odd cycles bound holds", odd, "of", oddn)
