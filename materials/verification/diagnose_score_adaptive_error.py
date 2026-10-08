"""Numerical diagnostics, not certification of uniform asymptotic estimates."""
from fractions import Fraction
import numpy as np

from centered_permanent_coefficients import carousel
from diagnose_paired_scaling_edit_bound import resolvent


def xi(u):
    n = len(u)
    eye = np.eye(n)
    rl = np.linalg.inv(eye-u@u.T)
    rr = np.linalg.inv(eye-u.T@u)
    ql, qr = rl-eye, rr-eye
    odd = u@rr
    dl, dr = np.diag(ql), np.diag(qr)
    tr = np.trace(ql)
    return ((tr*tr+tr+2*np.trace(ql@ql))/(2*n)
            -0.75*(dl@dl+dr@dr)
            -(np.sum(ql**3)+np.sum(qr**3))/3
            +2*np.sum(odd**3)/3
            -(dl@ql@dl+dr@qr@dr)/2+dl@odd@dr)


def potentials(c):
    n = len(c)
    x, y = np.zeros(n), np.zeros(n)
    for iteration in range(20000):
        x = -np.log(c@np.exp(y))
        y = -np.log(c.T@np.exp(x))
        if iteration % 5 == 0:
            scaled = np.exp(x[:, None]+y[None, :])*c
            err = max(np.max(abs(scaled.sum(axis=0)-1)),
                      np.max(abs(scaled.sum(axis=1)-1)))
            if err < 2e-13:
                break
    else:
        raise RuntimeError("No converged scaling; do not accept approximate output")
    gauge = (y.sum()-x.sum())/(2*n)
    return x+gauge, y-gauge, scaled, err


def diagnostic(rows):
    s = np.array(rows, dtype=float)
    n = len(s)
    largest = int(max(abs(s.sum(axis=1))))
    c = (s+np.ones((n, n))-np.eye(n))/(n-1)
    x, y, scaled, error = potentials(c)
    k = s/n
    eye = np.eye(n)
    r = np.linalg.inv(eye+k@k)
    a = s.sum(axis=1)/(n-1)
    capacity_difference = abs(x.sum()+y.sum()-a@r@a)
    v = -k@k@np.linalg.inv(eye-k@k)
    w = k@np.linalg.inv(eye-k@k)
    ell = (eye+np.ones((n, n))+s)/n
    f = eye-np.linalg.inv(eye+ell)
    reference_f = v+w+np.ones((n, n))/(2*n)+eye/n
    core_difference = abs(xi(scaled-np.ones((n, n))/n)-xi(k))
    return {"n": n, "max_score": largest,
            "score_energy/n": round(float(np.sum(s.sum(axis=1)**2)/n), 6),
            "capacity_ratio": float(n*n*capacity_difference/(largest+1)),
            "inclusion_ratio": float(n*n*np.max(abs(f-reference_f))/(largest+1)),
            "core_ratio": float(n*n*core_difference/(largest+1)),
            "scaling_residual": float(error)}


if __name__ == "__main__":
    total = 0
    exact = 0
    maxima = [0.0, 0.0, 0.0]
    for n in (17, 33, 65, 129):
        for kind in ("regular", "disjoint", "small_hub", "sqrt_hub"):
            rows = [row[:] for row in carousel(n)]
            if kind == "regular":
                edges = []
            elif kind == "disjoint":
                edges = [(i, i+1) for i in range(0, n-1, 2)]
            else:
                power = 0.25 if kind == "small_hub" else 0.5
                edges = [(0, j) for j in range(1, int(n**power)+1)]
            for i, j in edges:
                rows[i][j] *= -1
                rows[j][i] *= -1
            # Include both deleting the exceptional hub and retaining it.
            for deleted in ((), (0, 2, 4), (1, 3, 5)):
                keep = [i for i in range(n) if i not in deleted]
                sample = [[rows[i][j] for j in keep] for i in keep]
                result = diagnostic(sample)
                print(kind, "deleted", len(deleted), result, flush=True)
                for j, key in enumerate(("capacity_ratio", "inclusion_ratio", "core_ratio")):
                    maxima[j] = max(maxima[j], result[key])
                total += 1
                if n == 17:
                    m = len(sample)
                    _, rr = resolvent(sample)
                    b = [Fraction(sum(row), m) for row in sample]
                    theta = sum(b[i]*rr[i][j]*b[j] for i in range(m) for j in range(m))
                    energy = sum(sum(row)**2 for row in sample)
                    excess = theta-Fraction(int(m % 2 == 0), m)
                    largest = max(abs(sum(row)) for row in sample)
                    assert theta >= Fraction(energy, m*m)
                    assert excess >= 0
                    assert largest**2 <= 1+m*m*excess
                    exact += 1
    print("Numerical diagnostics completed:", total, "samples", flush=True)
    print("Observed ratio maxima (not universal constants):", maxima, flush=True)
    print("Exact rational score-loss inequalities:", exact, "passed", flush=True)
