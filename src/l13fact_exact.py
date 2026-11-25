"""Zero-float exact arithmetic engine for L13FACT-COGENTIC-CERT-1.0.

Implements pure-integer and exact-Fraction primitives corresponding to the
Google Cogentic unconditional L_N[1/3, 105] Las Vegas GNFS architecture:
- 13-base deterministic Miller-Rabin primality (< 3,317,044,064,679,887,385,961,981),
- Exact Lagrange-Gauss 2D lattice reduction & smooth modular ratio splitting,
- Exact Bareiss integer determinant & adjugate for mod-N polynomial lattices,
- Exact F_3[X] polynomial arithmetic & Rabin irreducibility testing,
- Exact Z[X]/(f_tilde) & (Z/3^(2^k)Z)[X]/(f_tilde) arithmetic,
- Deterministic 3-adic Newton-Hensel algebraic square root extraction (Lemma 5.2),
- Exact Legendre / Jacobi symbol & F_2 Gaussian elimination over degree-1 characters.

NO floating-point operations, `float`, `math.log`, or `math.sqrt` appear anywhere
in this module.
"""

from __future__ import annotations

from fractions import Fraction
import math
from typing import Dict, List, Optional, Sequence, Tuple


class CertificateError(ValueError):
    """Raised whenever any exact mathematical or structural check fails."""


# Deterministic 13-base Miller-Rabin bound (Sorenson & Webster 2017):
# Valid for all 2 <= n < 3_317_044_064_679_887_385_961_981.
MR_DETERMINISTIC_LIMIT = 3_317_044_064_679_887_385_961_981
MR_BASES_13 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)


def is_prime_exact(n: int) -> bool:
    """Exact deterministic primality test for integers < MR_DETERMINISTIC_LIMIT."""
    if not isinstance(n, int) or isinstance(n, bool):
        raise CertificateError("Primality argument must be an exact integer")
    if n >= MR_DETERMINISTIC_LIMIT:
        raise CertificateError(
            f"Primality argument {n} exceeds deterministic 13-base Miller-Rabin limit"
        )
    if n < 2:
        return False
    for p in MR_BASES_13:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES_13:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def exact_factor_trial(n: int) -> Dict[int, int]:
    """Exact integer factorization for modest certificate integers (n <= 10^14)."""
    if n <= 0:
        raise CertificateError("Factorization requires a positive integer")
    if n == 1:
        return {}
    if is_prime_exact(n):
        return {n: 1}
    rem = n
    fac: Dict[int, int] = {}
    d = 2
    while d * d <= rem:
        if rem % d == 0:
            e = 0
            while rem % d == 0:
                rem //= d
                e += 1
            fac[d] = e
            if rem > 1 and is_prime_exact(rem):
                fac[rem] = fac.get(rem, 0) + 1
                rem = 1
                break
        d += 1 if d == 2 else 2
        if d > 10_000_000 and rem > 1:
            raise CertificateError("Integer exceeds bounded exact trial-factorization cap")
    if rem > 1:
        fac[rem] = fac.get(rem, 0) + 1
    return fac


def legendre_symbol(a: int, p: int) -> int:
    """Exact Legendre symbol (a/p) in {-1, 0, 1} for odd prime p."""
    if p <= 2 or not is_prime_exact(p):
        raise CertificateError(f"Legendre modulus {p} must be an odd prime")
    r = a % p
    if r == 0:
        return 0
    val = pow(r, (p - 1) // 2, p)
    return 1 if val == 1 else -1


def mod_inv_exact(a: int, m: int) -> int:
    """Exact modular inverse of a mod m, raising CertificateError if not coprime."""
    if m <= 1:
        raise CertificateError(f"Modulus {m} must be > 1")
    if math.gcd(a, m) != 1:
        raise CertificateError(f"Element {a} is not invertible modulo {m}")
    return pow(a % m, -1, m)


# ---------------------------------------------------------------------------
# 1. Exact Bareiss Determinant, Adjugate, and 2D Lagrange-Gauss Reduction
# ---------------------------------------------------------------------------

def mat_det_bareiss(mat: Sequence[Sequence[int]]) -> int:
    """Exact fraction-free Bareiss determinant for an n x n integer matrix."""
    n = len(mat)
    if n == 0:
        return 1
    for row in mat:
        if len(row) != n:
            raise CertificateError("Matrix must be square for determinant")
    A = [list(row) for row in mat]
    sign = 1
    prev_pivot = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            swap_row = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    swap_row = i
                    break
            if swap_row is None:
                return 0
            A[k], A[swap_row] = A[swap_row], A[k]
            sign = -sign
        pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = A[i][j] * pivot - A[i][k] * A[k][j]
                if num % prev_pivot != 0:
                    raise CertificateError("Internal Bareiss divisibility invariant violated")
                A[i][j] = num // prev_pivot
            A[i][k] = 0
        prev_pivot = pivot
    return sign * A[n - 1][n - 1]


def mat_mul_int(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> List[List[int]]:
    """Exact integer matrix multiplication."""
    if not A or not B:
        raise CertificateError("Empty matrix multiplication")
    rows = len(A)
    inner = len(A[0])
    if len(B) != inner:
        raise CertificateError("Incompatible matrix dimensions")
    cols = len(B[0])
    out: List[List[int]] = []
    for i in range(rows):
        row_out = []
        for j in range(cols):
            s = 0
            for k in range(inner):
                s += A[i][k] * B[k][j]
            row_out.append(s)
        out.append(row_out)
    return out


def lagrange_gauss_2d(w1: Tuple[int, int], w2: Tuple[int, int]) -> Tuple[Tuple[int, int], Tuple[int, int]]:
    """Exact zero-float 2D Lagrange-Gauss reduction (Proposition 2.3(1)).

    Returns (v1, v2) with ||v1||^2 <= ||v2||^2 and 2*|<v1, v2>| <= ||v1||^2.
    """
    v1 = (int(w1[0]), int(w1[1]))
    v2 = (int(w2[0]), int(w2[1]))
    n1 = v1[0] * v1[0] + v1[1] * v1[1]
    n2 = v2[0] * v2[0] + v2[1] * v2[1]
    if n1 == 0 or n2 == 0:
        raise CertificateError("Zero basis vector in Lagrange-Gauss reduction")
    if n1 > n2:
        v1, v2 = v2, v1
        n1, n2 = n2, n1
    for _ in range(10_000):
        dot = v1[0] * v2[0] + v1[1] * v2[1]
        # Nearest integer k = floor((2*dot + n1) / (2*n1))
        k = (2 * dot + n1) // (2 * n1)
        v2p = (v2[0] - k * v1[0], v2[1] - k * v1[1])
        n2p = v2p[0] * v2p[0] + v2p[1] * v2p[1]
        if n2p >= n1:
            return v1, v2p
        v1, v2 = v2p, v1
        n1, n2 = n2p, n1
    raise CertificateError("Lagrange-Gauss reduction iteration cap exceeded")


def lll_check_exact(basis_cols: Sequence[Sequence[int]]) -> bool:
    """Verify exact (3/4)-LLL reduction over Q (Fraction) on column basis [b_1, ..., b_n]."""
    n = len(basis_cols)
    if n == 0:
        return False
    # Convert columns to vectors b[0..n-1]
    b: List[List[Fraction]] = [[Fraction(basis_cols[r][c]) for r in range(n)] for c in range(n)]
    bstar: List[List[Fraction]] = []
    mu: List[List[Fraction]] = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    norm2: List[Fraction] = []

    for j in range(n):
        v = list(b[j])
        for m in range(j):
            dot = sum(b[j][k] * bstar[m][k] for k in range(n))
            if norm2[m] == 0:
                return False
            mu[j][m] = Fraction(
                dot.numerator * norm2[m].denominator,
                dot.denominator * norm2[m].numerator,
            )
            if abs(mu[j][m]) > Fraction(1, 2):
                return False
            for k in range(n):
                v[k] -= mu[j][m] * bstar[m][k]
        bstar.append(v)
        nj = sum(x * x for x in v)
        if nj == 0:
            return False
        norm2.append(nj)

    for j in range(n - 1):
        lhs = norm2[j + 1]
        rhs = (Fraction(3, 4) - mu[j + 1][j] * mu[j + 1][j]) * norm2[j]
        if lhs < rhs:
            return False
    return True


# ---------------------------------------------------------------------------
# 2. Exact Polynomial Arithmetic over F_p[X] and Z[X] / (m, f_tilde)
# ---------------------------------------------------------------------------

def poly_trim(p: Sequence[int]) -> List[int]:
    out = list(p)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_mod_p(p: Sequence[int], mod: int) -> List[int]:
    return poly_trim([c % mod for c in p])


def poly_add_mod(a: Sequence[int], b: Sequence[int], mod: int) -> List[int]:
    n = max(len(a), len(b))
    res = []
    for i in range(n):
        va = a[i] if i < len(a) else 0
        vb = b[i] if i < len(b) else 0
        res.append((va + vb) % mod)
    return poly_trim(res)


def poly_sub_mod(a: Sequence[int], b: Sequence[int], mod: int) -> List[int]:
    n = max(len(a), len(b))
    res = []
    for i in range(n):
        va = a[i] if i < len(a) else 0
        vb = b[i] if i < len(b) else 0
        res.append((va - vb) % mod)
    return poly_trim(res)


def poly_mul_mod(a: Sequence[int], b: Sequence[int], mod: int) -> List[int]:
    res = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca % mod == 0:
            continue
        for j, cb in enumerate(b):
            res[i + j] = (res[i + j] + ca * cb) % mod
    return poly_trim(res)


def poly_rem_monic_mod(a: Sequence[int], f_monic: Sequence[int], mod: int) -> List[int]:
    """Exact remainder of a(X) mod f_monic(X) over Z/mod Z (f_monic must have leading coeff 1)."""
    d = len(f_monic) - 1
    if d < 1 or f_monic[-1] % mod != 1 % mod:
        raise CertificateError("Modulus polynomial must be monic of degree >= 1")
    r = [c % mod for c in a]
    while len(r) > d:
        lead = r.pop() % mod
        if lead != 0:
            offset = len(r) - d
            for i in range(d):
                r[offset + i] = (r[offset + i] - lead * f_monic[i]) % mod
    return poly_trim(r)


def poly_pow_mod_monic(base: Sequence[int], exp: int, f_monic: Sequence[int], mod: int) -> List[int]:
    """Exact modular exponentiation base(X)^exp mod (mod, f_monic(X))."""
    if exp < 0:
        raise CertificateError("Negative exponent in polynomial power")
    res = [1 % mod]
    cur = poly_rem_monic_mod(base, f_monic, mod)
    e = exp
    while e > 0:
        if e & 1:
            res = poly_rem_monic_mod(poly_mul_mod(res, cur, mod), f_monic, mod)
        cur = poly_rem_monic_mod(poly_mul_mod(cur, cur, mod), f_monic, mod)
        e >>= 1
    return res


def poly_gcd_fp(a: Sequence[int], b: Sequence[int], p: int) -> List[int]:
    """Exact monic GCD in F_p[X] for prime p."""
    x = poly_mod_p(a, p)
    y = poly_mod_p(b, p)
    while not (len(y) == 1 and y[0] == 0):
        # polynomial division in F_p[X]
        inv_lead = mod_inv_exact(y[-1], p)
        r = list(x)
        dy = len(y) - 1
        while len(r) >= len(y) and not (len(r) == 1 and r[0] == 0):
            factor = (r[-1] * inv_lead) % p
            shift = len(r) - len(y)
            for i in range(dy + 1):
                r[shift + i] = (r[shift + i] - factor * y[i]) % p
            r = poly_trim(r)
        x, y = y, r
    if len(x) == 1 and x[0] == 0:
        return [0]
    inv_lead = mod_inv_exact(x[-1], p)
    return poly_trim([(c * inv_lead) % p for c in x])


def is_monic_irreducible_f3(h: Sequence[int]) -> bool:
    """Exact Rabin irreducibility test for monic h(X) in F_3[X] (Section 2.1)."""
    hp = poly_mod_p(h, 3)
    d = len(hp) - 1
    if d < 1 or hp[-1] != 1:
        return False
    # Check X^(3^d) == X mod h(X)
    x_poly = [0, 1]
    x_pow = poly_pow_mod_monic(x_poly, 3 ** d, hp, 3)
    if poly_sub_mod(x_pow, x_poly, 3) != [0]:
        return False
    # Check gcd(X^(3^(d/ell)) - X, h) == 1 for every prime ell | d
    fac = exact_factor_trial(d)
    for ell in fac:
        xp = poly_pow_mod_monic(x_poly, 3 ** (d // ell), hp, 3)
        diff = poly_sub_mod(xp, x_poly, 3)
        g = poly_gcd_fp(diff, hp, 3)
        if g != [1]:
            return False
    return True


def poly_mul_exact_z(a: Sequence[int], b: Sequence[int]) -> List[int]:
    """Exact polynomial multiplication in Z[X]."""
    res = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0:
            continue
        for j, cb in enumerate(b):
            res[i + j] += ca * cb
    return poly_trim(res)


def poly_rem_monic_z(a: Sequence[int], f_monic: Sequence[int]) -> List[int]:
    """Exact remainder of a(X) mod monic f_monic(X) in Z[X]."""
    d = len(f_monic) - 1
    if d < 1 or f_monic[-1] != 1:
        raise CertificateError("Modulus polynomial in Z[X] must be monic of degree >= 1")
    r = list(a)
    while len(r) > d:
        lead = r.pop()
        if lead != 0:
            offset = len(r) - d
            for i in range(d):
                r[offset + i] -= lead * f_monic[i]
    return poly_trim(r)


def poly_eval_mod(p: Sequence[int], x: int, mod: int) -> int:
    """Exact Horner evaluation of p(x) mod mod."""
    acc = 0
    for c in reversed(p):
        acc = (acc * x + c) % mod
    return acc


def poly_deriv_z(p: Sequence[int]) -> List[int]:
    """Exact formal derivative p'(X) in Z[X]."""
    if len(p) <= 1:
        return [0]
    return poly_trim([i * p[i] for i in range(1, len(p))])


def eval_binary_form(coeffs: Sequence[int], a: int, b: int) -> int:
    """Exact homogeneous evaluation f(a, b) = sum_{i=0}^d c_i a^i b^(d-i)."""
    d = len(coeffs) - 1
    total = 0
    a_pow = 1
    b_pows = [1] * (d + 1)
    for k in range(1, d + 1):
        b_pows[k] = b_pows[k - 1] * b
    for i, ci in enumerate(coeffs):
        total += ci * a_pow * b_pows[d - i]
        a_pow *= a
    return total


def build_monic_f_tilde(coeffs: Sequence[int]) -> List[int]:
    """Compute monic f_tilde(X) = c_d^(d-1) * f(X / c_d, 1) in Z[X]."""
    d = len(coeffs) - 1
    if d < 1 or coeffs[-1] == 0:
        raise CertificateError("Binary form must have degree >= 1 and nonzero leading coefficient")
    cd = coeffs[-1]
    out: List[int] = []
    for i in range(d):
        out.append(coeffs[i] * (cd ** (d - 1 - i)))
    out.append(1)
    return out


# ---------------------------------------------------------------------------
# 3. Deterministic 3-Adic Newton-Hensel Square Root Lifting (Lemma 5.2)
# ---------------------------------------------------------------------------

def balanced_mod(x: int, mod: int) -> int:
    """Unique balanced representative in [-(mod-1)//2, (mod-1)//2] for odd mod."""
    r = x % mod
    if 2 * r > mod:
        r -= mod
    return r


def adic3_newton_hensel_sqrt(
    gamma_poly: Sequence[int],
    f_tilde: Sequence[int],
    k_steps: int,
) -> Tuple[List[int], List[Dict[str, object]]]:
    """Deterministic 3-adic Newton-Hensel square root in Z[X]/(f_tilde) (Lemma 5.2).

    Requires:
    - f_tilde monic of odd degree d >= 3,
    - h_0 = f_tilde mod 3 irreducible over F_3,
    - gamma_poly mod (3, h_0) is a nonzero square in F_{3^d}^x.

    Returns (beta_hat, trace) where beta_hat(X)^2 == gamma_poly(X) (mod f_tilde)
    in Z[X], and `trace` records each quadratic lifting step k = 0..k_steps.
    """
    d = len(f_tilde) - 1
    if d < 3 or d % 2 == 0 or f_tilde[-1] != 1:
        raise CertificateError("f_tilde must be monic of odd degree d >= 3")
    h0 = poly_mod_p(f_tilde, 3)
    if not is_monic_irreducible_f3(h0):
        raise CertificateError("f_tilde mod 3 must be irreducible over F_3")

    gamma_red = poly_rem_monic_z(gamma_poly, f_tilde)
    alpha0 = poly_mod_p(gamma_red, 3)
    if alpha0 == [0]:
        raise CertificateError("Gamma is divisible by 3; not a unit in F_{3^d}^x")

    q_field = 3 ** d
    if (q_field + 1) % 4 != 0:
        raise CertificateError("Odd degree invariant 4 | (3^d + 1) violated")

    # Euler square test in F_{3^d}^x
    euler = poly_pow_mod_monic(alpha0, (q_field - 1) // 2, h0, 3)
    if euler != [1]:
        raise CertificateError("Gamma is not a square in F_{3^d}^x (NOT_SQUARE)")

    beta = poly_pow_mod_monic(alpha0, (q_field + 1) // 4, h0, 3)
    two_beta = poly_mul_mod([2], beta, 3)
    gamma_inv = poly_pow_mod_monic(two_beta, q_field - 2, h0, 3)

    # Verify base case k = 0
    if poly_rem_monic_mod(poly_mul_mod(beta, beta, 3), h0, 3) != alpha0:
        raise CertificateError("Base F_{3^d} square root verification failed")
    if poly_rem_monic_mod(poly_mul_mod(two_beta, gamma_inv, 3), h0, 3) != [1]:
        raise CertificateError("Base F_{3^d} inverse verification failed")

    trace: List[Dict[str, object]] = [
        {"k": 0, "exp3": 1, "beta_mod": list(beta), "gamma_mod": list(gamma_inv)}
    ]

    for k in range(k_steps):
        mod_k = 3 ** (2 ** k)
        mod_next = 3 ** (2 ** (k + 1))

        # gamma_{k+1} = gamma_k * (2 - 2 * beta_k * gamma_k) mod (3^(2^k), f_tilde)
        prod_bg = poly_rem_monic_mod(poly_mul_mod(beta, gamma_inv, mod_k), f_tilde, mod_k)
        two_bg = poly_mul_mod([2], prod_bg, mod_k)
        factor = poly_sub_mod([2], two_bg, mod_k)
        gamma_next = poly_rem_monic_mod(poly_mul_mod(gamma_inv, factor, mod_k), f_tilde, mod_k)

        # beta_{k+1} = (beta_k + (Gamma - beta_k^2) * gamma_{k+1}) mod (3^(2^(k+1)), f_tilde)
        beta_sq = poly_rem_monic_mod(poly_mul_mod(beta, beta, mod_next), f_tilde, mod_next)
        diff = poly_sub_mod(poly_mod_p(gamma_red, mod_next), beta_sq, mod_next)
        corr = poly_rem_monic_mod(poly_mul_mod(diff, gamma_next, mod_next), f_tilde, mod_next)
        beta_next = poly_add_mod(beta, corr, mod_next)

        beta = beta_next
        gamma_inv = gamma_next
        trace.append(
            {
                "k": k + 1,
                "exp3": 2 ** (k + 1),
                "beta_mod": list(beta),
                "gamma_mod": list(gamma_inv),
            }
        )

    final_mod = 3 ** (2 ** k_steps)
    beta_hat = poly_trim([balanced_mod(c, final_mod) for c in beta])
    sq_exact = poly_rem_monic_z(poly_mul_exact_z(beta_hat, beta_hat), f_tilde)
    if sq_exact != gamma_red:
        raise CertificateError(
            "Balanced 3-adic lift failed global exact identity beta_hat^2 == Gamma (mod f_tilde)"
        )
    return beta_hat, trace


# ---------------------------------------------------------------------------
# 4. Exact F_2 Gaussian Elimination (Nullspace Basis)
# ---------------------------------------------------------------------------

def f2_right_nullspace(rows: Sequence[Sequence[int]]) -> List[List[int]]:
    """Deterministic F_2 right-nullspace basis of an m x n binary matrix."""
    if not rows:
        return []
    m = len(rows)
    n = len(rows[0])
    A = [[int(v) & 1 for v in r] for r in rows]
    pivots: List[Tuple[int, int]] = []
    r_idx = 0
    for c in range(n):
        piv = None
        for r in range(r_idx, m):
            if A[r][c] == 1:
                piv = r
                break
        if piv is None:
            continue
        A[r_idx], A[piv] = A[piv], A[r_idx]
        for r in range(m):
            if r != r_idx and A[r][c] == 1:
                for k in range(c, n):
                    A[r][k] ^= A[r_idx][k]
        pivots.append((r_idx, c))
        r_idx += 1
        if r_idx == m:
            break
    pivot_cols = {c for _, c in pivots}
    free_cols = [c for c in range(n) if c not in pivot_cols]
    basis: List[List[int]] = []
    for fc in free_cols:
        vec = [0] * n
        vec[fc] = 1
        for pr, pc in pivots:
            if A[pr][fc] == 1:
                vec[pc] = 1
        basis.append(vec)
    return basis
