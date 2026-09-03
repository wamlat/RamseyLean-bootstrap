"""Exact Python port of RamseyLean/Analysis/FixedPointInterval.lean.

Intervals are pairs (lo, hi) of Python ints (arbitrary precision, like Lean ℤ),
denoting [lo/scale, hi/scale] in ℝ with scale = 10^12.

Lean's `/` on ℤ (with Mathlib) is Int.ediv (Euclidean division):
  a / b = floor(a/b) for b > 0, ceil(a/b) for b < 0
(verified by #eval: (-7:ℤ)/2 = -4, 7/(-2) = -3, (-7)/(-2) = 4).
Python's // is floor division; they agree for b > 0.  We implement ediv
for all signs to be bit-exact.
"""

scale = 10**12

def ediv(a: int, b: int) -> int:
    """Lean (Mathlib) Int division: Euclidean (remainder in [0,|b|)).

    For b > 0 this is floor(a/b) (= Python //).
    For b < 0 it is ceil(a/b) = -floor(a/(-b)) = -(a // (-b)).
    """
    if b == 0:
        raise ZeroDivisionError
    if b > 0:
        return a // b
    return -(a // (-b))

def point(z: int):
    return (z, z)

def add(I, J):
    return (I[0] + J[0], I[1] + J[1])

def neg(I):
    return (-I[1], -I[0])

def min4(a, b, c, d):
    return min(min(a, b), min(c, d))

def max4(a, b, c, d):
    return max(max(a, b), max(c, d))

def down(z: int) -> int:
    return ediv(z, scale)

def up(z: int) -> int:
    return -ediv(-z, scale)

def mul(I, J):
    p1 = I[0] * J[0]; p2 = I[0] * J[1]; p3 = I[1] * J[0]; p4 = I[1] * J[1]
    return (down(min4(p1, p2, p3, p4)), up(max4(p1, p2, p3, p4)))

def mulNonneg(I, J):
    return (down(I[0] * J[0]), up(I[1] * J[1]))

def inv(I):
    return (ediv(scale * scale, I[1]), -ediv(-(scale * scale), I[0]))

def downNat(z: int, k: int) -> int:
    return ediv(z, k)

def upNat(z: int, k: int) -> int:
    return -ediv(-z, k)

def divNat(I, k: int):
    return (downNat(I[0], k), upNat(I[1], k))

def mulNat(I, k: int):
    return (I[0] * k, I[1] * k)

def abs_(I):
    return (0, max(abs(I[0]), abs(I[1])))

def pow_(I, n: int):
    r = point(scale)
    for _ in range(n):
        r = mul(r, I)          # pow I (n+1) = mul (pow I n) I
    return r

_factorial_cache = [1]
def factorial(n: int) -> int:
    while len(_factorial_cache) <= n:
        _factorial_cache.append(_factorial_cache[-1] * len(_factorial_cache))
    return _factorial_cache[n]

def sumTerms(f, n: int):
    acc = point(0)
    for i in range(n):
        acc = add(acc, f(i))
    return acc

def expPoly(n: int, I):
    return sumTerms(lambda i: divNat(pow_(I, i), factorial(i)), n)

def expError(n: int, I):
    return divNat(mulNat(pow_(abs_(I), n), n + 1), factorial(n) * n)

def exp(n: int, I):
    Plo = expPoly(n, point(I[0]))
    Elo = expError(n, point(I[0]))
    Phi = expPoly(n, point(I[1]))
    Ehi = expError(n, point(I[1]))
    return (Plo[0] - Elo[1], Phi[1] + Ehi[1])

def logSeries(n: int, I):
    return sumTerms(lambda i: divNat(pow_(I, 2 * i + 1), 2 * i + 1), n)

def logError(n: int, I):
    numerator = pow_(abs_(I), 2 * n + 1)
    denominator = add(point(scale), neg(pow_(I, 2)))
    return mulNonneg(numerator, inv(denominator))

def logArgument(z: int):
    return mul(point(z - scale), inv(point(z + scale)))

def log(n: int, I):
    Zlo = logArgument(I[0])
    Plo = logSeries(n, Zlo)
    Elo = logError(n, Zlo)
    Zhi = logArgument(I[1])
    Phi = logSeries(n, Zhi)
    Ehi = logError(n, Zhi)
    return mulNat((Plo[0] - Elo[1], Phi[1] + Ehi[1]), 2)

# ---- safety predicates (mirroring Lean; used as assertions in the checker) ----

def nonneg(I) -> bool:
    return 0 <= I[0]

def positive(I) -> bool:
    return 0 < I[0]

def expSafe(n: int, I) -> bool:
    return 0 < n and abs(I[0]) <= scale and abs(I[1]) <= scale

def logSafe(n: int, I) -> bool:
    Zlo = logArgument(I[0])
    Zhi = logArgument(I[1])
    Nlo = pow_(abs_(Zlo), 2 * n + 1)
    Nhi = pow_(abs_(Zhi), 2 * n + 1)
    Dlo = add(point(scale), neg(pow_(Zlo, 2)))
    Dhi = add(point(scale), neg(pow_(Zhi, 2)))
    Dloi = inv(Dlo)
    Dhii = inv(Dhi)
    return (0 < n and 0 < I[0]
            and 0 < I[0] + scale and 0 < I[1] + scale
            and positive(Dlo) and positive(Dhi) and nonneg(Nlo) and nonneg(Nhi)
            and nonneg(Dloi) and nonneg(Dhii))
