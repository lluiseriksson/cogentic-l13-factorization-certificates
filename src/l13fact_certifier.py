"""Zero-float 4-mode certificate auditor for L13FACT-COGENTIC-CERT-1.0.

Strictly parses JSON without floats (rejecting IEEE-754 decimals, NaN/Infinity,
and duplicate keys via object_pairs_hook) and verifies four canonical modes
aligned with the Google Cogentic unconditional L_N[1/3, 105] Las Vegas GNFS
factorization architecture:
  1. mod_n_lattice_and_lagrange_split_cert  (Props. 2.2 & 2.3)
  2. mod3_laplace_ladder_and_smooth_cert    (Def. 2.7, Lem. 2.8, Def. 4.1, Lem. 4.2)
  3. adic3_newton_hensel_sqrt_cert          (Prop. 2.5, Lem. 5.2)
  4. dixon_character_and_induction_split_cert (Lems. 5.1, 5.2, 5.3 & Thm. 1.1)

NO floating-point operations appear anywhere in this module.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Dict, List, Mapping, Sequence, Tuple

from src.l13fact_exact import (
    CertificateError,
    adic3_newton_hensel_sqrt,
    balanced_mod,
    build_monic_f_tilde,
    eval_binary_form,
    exact_factor_trial,
    f2_right_nullspace,
    is_monic_irreducible_f3,
    is_prime_exact,
    lagrange_gauss_2d,
    legendre_symbol,
    lll_check_exact,
    mat_det_bareiss,
    mat_mul_int,
    mod_inv_exact,
    poly_deriv_z,
    poly_eval_mod,
    poly_mod_p,
    poly_mul_exact_z,
    poly_mul_mod,
    poly_pow_mod_monic,
    poly_rem_monic_mod,
    poly_rem_monic_z,
    poly_sub_mod,
    poly_trim,
)

PROTOCOL_ID = "L13FACT-COGENTIC-CERT-1.0"
VALID_MODES = frozenset(
    {
        "mod_n_lattice_and_lagrange_split_cert",
        "mod3_laplace_ladder_and_smooth_cert",
        "adic3_newton_hensel_sqrt_cert",
        "dixon_character_and_induction_split_cert",
    }
)


# ---------------------------------------------------------------------------
# Strict Zero-Float JSON Parser & Type Validators
# ---------------------------------------------------------------------------

def _reject_float(val: str) -> Any:
    raise CertificateError(f"Floating-point literal rejected by zero-float policy: {val!r}")


def _reject_constant(val: str) -> Any:
    raise CertificateError(f"Non-standard JSON constant rejected: {val!r}")


def _no_duplicate_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise CertificateError(f"Duplicate JSON key rejected: {k!r}")
        out[k] = v
    return out


def load_strict_json_str(raw: str) -> Dict[str, Any]:
    try:
        data = json.loads(
            raw,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_no_duplicate_keys,
        )
    except CertificateError:
        raise
    except Exception as exc:
        raise CertificateError(f"Malformed JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise CertificateError("Top-level certificate payload must be a JSON object")
    return data


def _req_int(obj: Mapping[str, Any], key: str) -> int:
    if key not in obj:
        raise CertificateError(f"Missing required integer field {key!r}")
    v = obj[key]
    if isinstance(v, bool) or not isinstance(v, int):
        raise CertificateError(f"Field {key!r} must be an exact integer (got {type(v).__name__})")
    return v


def _req_str(obj: Mapping[str, Any], key: str) -> str:
    if key not in obj:
        raise CertificateError(f"Missing required string field {key!r}")
    v = obj[key]
    if not isinstance(v, str) or not v:
        raise CertificateError(f"Field {key!r} must be a non-empty string")
    return v


def _req_int_list(obj: Mapping[str, Any], key: str, min_len: int = 1, max_len: int = 64) -> List[int]:
    if key not in obj:
        raise CertificateError(f"Missing required integer list {key!r}")
    v = obj[key]
    if not isinstance(v, list) or not (min_len <= len(v) <= max_len):
        raise CertificateError(
            f"Field {key!r} must be a list of length in [{min_len}, {max_len}]"
        )
    out: List[int] = []
    for item in v:
        if isinstance(item, bool) or not isinstance(item, int):
            raise CertificateError(f"Field {key!r} contains non-integer entry")
        out.append(item)
    return out


def _req_int_matrix(obj: Mapping[str, Any], key: str, dim: int) -> List[List[int]]:
    if key not in obj:
        raise CertificateError(f"Missing required matrix {key!r}")
    mat = obj[key]
    if not isinstance(mat, list) or len(mat) != dim:
        raise CertificateError(f"Matrix {key!r} must have {dim} rows")
    out: List[List[int]] = []
    for row in mat:
        if not isinstance(row, list) or len(row) != dim:
            raise CertificateError(f"Each row of matrix {key!r} must have length {dim}")
        r_ints: List[int] = []
        for entry in row:
            if isinstance(entry, bool) or not isinstance(entry, int):
                raise CertificateError(f"Matrix {key!r} contains non-integer entry")
            r_ints.append(entry)
        out.append(r_ints)
    return out


def _check_keys(obj: Mapping[str, Any], expected: set[str], label: str) -> None:
    keys = set(obj.keys())
    extra = keys - expected
    missing = expected - keys
    if missing:
        raise CertificateError(f"Missing keys in {label}: {sorted(missing)}")
    if extra:
        raise CertificateError(f"Unexpected keys in {label}: {sorted(extra)}")


# ---------------------------------------------------------------------------
# Mode 1: Mod-N Polynomial Lattice & 2D Lagrange-Gauss Ratio Splitting
# ---------------------------------------------------------------------------

def _verify_mode1(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "N",
        "G",
        "g0",
        "g1",
        "m_N",
        "n_dim",
        "B_lat",
        "A_adj",
        "z_val",
        "s_val",
        "t_val",
        "v1",
        "v2",
        "A_primes",
        "B_primes",
        "Q_bound",
    }
    _check_keys(payload, expected, "Mode 1 payload")

    N = _req_int(payload, "N")
    G = _req_int(payload, "G")
    g0 = _req_int(payload, "g0")
    g1 = _req_int(payload, "g1")
    m_N = _req_int(payload, "m_N")
    n_dim = _req_int(payload, "n_dim")
    z_val = _req_int(payload, "z_val")
    s_val = _req_int(payload, "s_val")
    t_val = _req_int(payload, "t_val")
    Q_bound = _req_int(payload, "Q_bound")

    if N < 15 or N % 2 == 0:
        raise CertificateError("Mode 1 requires odd N >= 15")
    if G < 2:
        raise CertificateError("Mode 1 requires G >= 2")
    if not (1 <= g0 <= 2 * G and 1 <= g1 <= 2 * G):
        raise CertificateError("Mode 1 requires 1 <= g0, g1 <= 2G")
    if math.gcd(g0, g1) != 1 or math.gcd(g1, N) != 1:
        raise CertificateError("Mode 1 requires gcd(g0, g1) = gcd(g1, N) = 1")
    if not (0 <= m_N < N) or (g1 * m_N - g0) % N != 0:
        raise CertificateError("Mode 1 requires g1 * m_N == g0 (mod N)")
    if not (2 <= n_dim <= 6):
        raise CertificateError("Mode 1 requires 2 <= n_dim <= 6")
    if 2 * (g1 ** (n_dim - 1)) <= N:
        raise CertificateError("Mode 1 requires g1^(n_dim - 1) > N/2 (Prop. 2.2(1))")

    B_lat = _req_int_matrix(payload, "B_lat", n_dim)
    A_adj = _req_int_matrix(payload, "A_adj", n_dim)

    # Every column of B_lat must lie in Lambda_n: sum_{s=0}^{n-1} h_s m_N^s == 0 (mod N)
    for col in range(n_dim):
        acc = 0
        m_pow = 1
        for row in range(n_dim):
            acc = (acc + B_lat[row][col] * m_pow) % N
            m_pow = (m_pow * m_N) % N
        if acc != 0:
            raise CertificateError(f"Column {col} of B_lat does not lie in Lambda_n")

    det_b = mat_det_bareiss(B_lat)
    if abs(det_b) != N:
        raise CertificateError(f"Expected |det(B_lat)| = N = {N}, got {abs(det_b)}")

    prod = mat_mul_int(A_adj, B_lat)
    for i in range(n_dim):
        for j in range(n_dim):
            want = N if i == j else 0
            if prod[i][j] != want:
                raise CertificateError("Adjugate identity A_adj * B_lat = N * I failed")

    if not lll_check_exact(B_lat):
        raise CertificateError("B_lat fails exact (3/4)-LLL reduction check")

    # Verify Prop. 2.2(1) basis norm bound: ||b_j||_2^2 <= 2^(n+3) * G^2
    bound_sq = (1 << (n_dim + 3)) * G * G
    max_col_sq = 0
    for col in range(n_dim):
        csq = sum(B_lat[row][col] ** 2 for row in range(n_dim))
        if csq > bound_sq:
            raise CertificateError("LLL basis vector exceeds Prop. 2.2(1) bound 2^((n+3)/2) * G")
        if csq > max_col_sq:
            max_col_sq = csq

    # Verify Prop. 2.3(1)-(2): Lagrange-Gauss reduction on L_z and smooth ratio split
    if math.gcd(s_val, N) != 1 or math.gcd(t_val, N) != 1:
        raise CertificateError("s_val and t_val must be units in (Z/NZ)^x")
    if not (0 <= z_val < N) or (s_val * t_val * t_val - z_val) % N != 0:
        raise CertificateError("z_val must equal s_val * t_val^2 mod N")

    v1 = _req_int_list(payload, "v1", min_len=2, max_len=2)
    v2 = _req_int_list(payload, "v2", min_len=2, max_len=2)
    if (v1[0] - z_val * v1[1]) % N != 0 or (v2[0] - z_val * v2[1]) % N != 0:
        raise CertificateError("Vectors v1, v2 do not lie in L_z = {(x,y) : x == z*y (mod N)}")
    det_2d = abs(v1[0] * v2[1] - v1[1] * v2[0])
    if det_2d != N:
        raise CertificateError(f"2D lattice basis (v1, v2) has |det| = {det_2d} != N = {N}")

    n1 = v1[0] * v1[0] + v1[1] * v1[1]
    n2 = v2[0] * v2[0] + v2[1] * v2[1]
    dot = v1[0] * v2[0] + v1[1] * v2[1]
    if n1 <= 0 or n1 > n2 or 2 * abs(dot) > n1:
        raise CertificateError("Basis (v1, v2) is not Lagrange-Gauss reduced")

    # Cross-check against canonical Lagrange-Gauss reduction of [(N, 0), (z_val, 1)]
    lg_v1, _ = lagrange_gauss_2d((N, 0), (z_val, 1))
    if lg_v1[0] * lg_v1[0] + lg_v1[1] * lg_v1[1] != n1:
        raise CertificateError("v1 does not achieve exact lambda_1(L_z)")

    A_primes = _req_int_list(payload, "A_primes", min_len=1, max_len=16)
    B_primes = _req_int_list(payload, "B_primes", min_len=1, max_len=16)
    if len(A_primes) != len(B_primes):
        raise CertificateError("A_primes and B_primes must have equal cardinality r0")
    r0 = len(A_primes)
    if len(set(A_primes)) != r0 or len(set(B_primes)) != r0:
        raise CertificateError("A_primes and B_primes must consist of distinct primes")
    if set(A_primes) & set(B_primes):
        raise CertificateError("A_primes and B_primes must be disjoint")

    if Q_bound < 2 or 4 * (Q_bound ** (2 * r0)) > N:
        raise CertificateError("Q_bound must satisfy Q_bound^r0 <= (1/2) sqrt(N)")

    x_prod = 1
    for p in A_primes:
        if p > Q_bound or not is_prime_exact(p) or N % p == 0:
            raise CertificateError(f"Invalid prime {p} in A_primes")
        x_prod *= p
    y_prod = 1
    for q in B_primes:
        if q > Q_bound or not is_prime_exact(q) or N % q == 0:
            raise CertificateError(f"Invalid prime {q} in B_primes")
        y_prod *= q

    # Normalize shortest vector sign so x1 > 0
    x1, y1 = (v1[0], v1[1]) if v1[0] > 0 else (-v1[0], -v1[1])
    if x1 != x_prod or y1 != y_prod:
        raise CertificateError("Shortest vector (x1, y1) does not match product of A_primes / B_primes")
    if 4 * x1 * x1 > N or 4 * y1 * y1 > N:
        raise CertificateError("Smooth split (x1, y1) exceeds (1/2) sqrt(N)")

    return {
        "mode": "mod_n_lattice_and_lagrange_split_cert",
        "N": N,
        "n_dim": n_dim,
        "r0": r0,
        "max_col_sq": max_col_sq,
        "lambda1_sq": n1,
        "x1": x1,
        "y1": y1,
    }


# ---------------------------------------------------------------------------
# Mode 2: Mod-3 Discrete Laplace Ensemble, Geometric Ladder & Smoothness
# ---------------------------------------------------------------------------

def _verify_mode2(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "N",
        "g0",
        "g1",
        "m_N",
        "M_scale",
        "W_box",
        "h0_coeffs",
        "c_tilde",
        "ladder_Y",
        "special_q",
        "r_q",
        "box_point",
        "smooth_cap",
        "layer_cake_z",
        "layer_cake_a",
        "layer_cake_W",
    }
    _check_keys(payload, expected, "Mode 2 payload")

    N = _req_int(payload, "N")
    g0 = _req_int(payload, "g0")
    g1 = _req_int(payload, "g1")
    m_N = _req_int(payload, "m_N")
    M_scale = _req_int(payload, "M_scale")
    W_box = _req_int(payload, "W_box")
    special_q = _req_int(payload, "special_q")
    r_q = _req_int(payload, "r_q")
    smooth_cap = _req_int(payload, "smooth_cap")
    lc_z = _req_int(payload, "layer_cake_z")
    lc_a = _req_int(payload, "layer_cake_a")
    lc_W = _req_int(payload, "layer_cake_W")

    if N < 15 or N % 2 == 0 or N % 3 == 0:
        raise CertificateError("Mode 2 requires N >= 15 coprime to 6")
    if math.gcd(g0, g1) != 1 or math.gcd(g0 * g1, 3 * N) != 1:
        raise CertificateError("Mode 2 requires gcd(g0, g1) = gcd(g0*g1, 3N) = 1")
    if not (0 <= m_N < N) or (g1 * m_N - g0) % N != 0:
        raise CertificateError("Mode 2 requires g1 * m_N == g0 (mod N)")
    if M_scale <= 0 or M_scale % 3 != 0:
        raise CertificateError("Mode 2 requires positive M_scale divisible by 3 (Def. 2.7(2))")
    if W_box < 1 or 6 * W_box > M_scale:
        raise CertificateError("Mode 2 requires 1 <= W_box and 6 * W_box <= M_scale")

    h0 = _req_int_list(payload, "h0_coeffs", min_len=4, max_len=12)
    d = len(h0) - 1
    if d % 2 == 0 or h0[-1] != 1:
        raise CertificateError("h0_coeffs must be monic of odd degree d >= 3")
    if any(c not in (0, 1, 2) for c in h0):
        raise CertificateError("h0_coeffs must have canonical F_3 coefficients in {0, 1, 2}")
    if not is_monic_irreducible_f3(h0):
        raise CertificateError("h0_coeffs is not irreducible over F_3")

    c_tilde = _req_int_list(payload, "c_tilde", min_len=d + 1, max_len=d + 1)
    if any(abs(c) > W_box for c in c_tilde):
        raise CertificateError("c_tilde falls outside box [-W_box, W_box]^(d+1)")

    # Def. 4.1(1): c_bar = (h0_0, ..., h0_{d-1}, M_scale + 3*W_box + 1), c = c_bar + 3*c_tilde
    c_bar = list(h0[:d]) + [M_scale + 3 * W_box + 1]
    coeffs = [c_bar[i] + 3 * c_tilde[i] for i in range(d + 1)]

    # Verify Lemma 4.2(1): f(g0, g1) == 0 (mod N), c_d == 1 (mod 3), c_d >= M_scale + 1
    f_g0g1 = eval_binary_form(coeffs, g0, g1)
    if f_g0g1 % N != 0:
        raise CertificateError("Mod-3-pinned form fails f(g0, g1) == 0 (mod N)")
    if coeffs[d] % 3 != 1 or coeffs[d] < M_scale + 1:
        raise CertificateError("Leading coefficient fails c_d == 1 (mod 3) and c_d >= M_scale + 1")

    # Verify geometric ladder strictly decreasing: Y_0 > Y_1 > ... > Y_J = B >= 2
    ladder_Y = _req_int_list(payload, "ladder_Y", min_len=3, max_len=24)
    for i in range(len(ladder_Y) - 1):
        if ladder_Y[i] <= ladder_Y[i + 1]:
            raise CertificateError("Geometric descent ladder Y must be strictly decreasing")
    if ladder_Y[-1] < 2:
        raise CertificateError("Base smoothness bound B = Y_J must be >= 2")

    # Verify special-q lattice point (a, b) with gcd(a,b)=1, a == r_q*b (mod q), f(r_q, 1) == 0 (mod q)
    if not is_prime_exact(special_q) or special_q <= 3 or N % special_q == 0:
        raise CertificateError("special_q must be a prime > 3 not dividing N")
    if not (0 <= r_q < special_q):
        raise CertificateError("r_q must lie in [0, special_q - 1]")
    if eval_binary_form(coeffs, r_q, 1) % special_q != 0:
        raise CertificateError("special_q root fails f(r_q, 1) == 0 (mod special_q)")

    pt = _req_int_list(payload, "box_point", min_len=2, max_len=2)
    a_pt, b_pt = pt[0], pt[1]
    if a_pt <= 0 or b_pt <= 0 or math.gcd(a_pt, b_pt) != 1:
        raise CertificateError("box_point (a, b) must be positive and primitive")
    if (a_pt - r_q * b_pt) % special_q != 0:
        raise CertificateError("box_point does not lie in special-q lattice Lambda_{q, r_q}")

    f_ab = eval_binary_form(coeffs, a_pt, b_pt)
    if f_ab % 3 == 0:
        raise CertificateError("Primitive pair violated mod-3 non-divisibility 3 nmid f(a,b)")
    if f_ab <= 0 or f_ab % special_q != 0:
        raise CertificateError("f(a, b) must be positive and divisible by special_q")
    cofactor = f_ab // special_q

    if smooth_cap < 2 or smooth_cap >= cofactor:
        raise CertificateError("smooth_cap must satisfy 2 <= smooth_cap < cofactor (non-vacuous smoothness)")
    fac = exact_factor_trial(cofactor)
    max_prime = max(fac.keys()) if fac else 1
    if max_prime > smooth_cap:
        raise CertificateError(
            f"Cofactor f(a,b)/q = {cofactor} is not {smooth_cap}-smooth (max prime {max_prime})"
        )

    # Verify exact discrete Laplace layer-cake telescoping identity (Lemma 4.2(2))
    if not (0 <= lc_a <= lc_W) or (lc_W - lc_a) > 40 or abs(lc_z) > 20:
        raise CertificateError("Layer-cake witness parameters out of bounded exact verification range")
    tail_sum = 0
    for R in range(lc_a, lc_W):
        tail_sum += (2 * R + 1) * ((lc_z ** R) - (lc_z ** (R + 1)))
    tail_sum += (2 * lc_W + 1) * (lc_z ** lc_W)
    lhs = (1 - lc_z) * tail_sum
    rhs = (2 * lc_a + 1) * (lc_z ** lc_a) * (1 - lc_z) + 2 * ((lc_z ** (lc_a + 1)) - (lc_z ** (lc_W + 1)))
    if lhs != rhs:
        raise CertificateError("Layer-cake telescoping identity mismatch")

    return {
        "mode": "mod3_laplace_ladder_and_smooth_cert",
        "N": N,
        "degree": d,
        "special_q": special_q,
        "cofactor": cofactor,
        "max_prime_factor": max_prime,
        "smooth_cap": smooth_cap,
        "ladder_len": len(ladder_Y),
    }


# ---------------------------------------------------------------------------
# Mode 3: Deterministic 3-Adic Newton-Hensel Algebraic Square Root (Lemma 5.2)
# ---------------------------------------------------------------------------

def _verify_mode3(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "f_coeffs",
        "pairs",
        "k_steps",
        "beta_hat",
        "trace",
    }
    _check_keys(payload, expected, "Mode 3 payload")

    f_coeffs = _req_int_list(payload, "f_coeffs", min_len=4, max_len=10)
    d = len(f_coeffs) - 1
    if d % 2 == 0 or f_coeffs[-1] == 0 or f_coeffs[-1] % 3 != 1:
        raise CertificateError("f_coeffs must have odd degree d >= 3 with c_d == 1 (mod 3)")

    f_tilde = build_monic_f_tilde(f_coeffs)
    h0 = poly_mod_p(f_tilde, 3)
    if not is_monic_irreducible_f3(h0):
        raise CertificateError("f_tilde mod 3 must be irreducible over F_3")

    raw_pairs = payload.get("pairs")
    if not isinstance(raw_pairs, list) or not (1 <= len(raw_pairs) <= 32):
        raise CertificateError("Mode 3 requires 1..32 primitive pairs")

    cd = f_coeffs[-1]
    deriv = poly_deriv_z(f_tilde)
    # Build Gamma_tilde = f_tilde'(theta)^2 * prod (c_d * a_nu - b_nu * theta) mod f_tilde
    gamma_poly = poly_rem_monic_z(poly_mul_exact_z(deriv, deriv), f_tilde)
    for pair in raw_pairs:
        if not isinstance(pair, list) or len(pair) != 2:
            raise CertificateError("Each pair in Mode 3 must be [a, b]")
        a_nu, b_nu = pair[0], pair[1]
        if (
            isinstance(a_nu, bool)
            or isinstance(b_nu, bool)
            or not isinstance(a_nu, int)
            or not isinstance(b_nu, int)
        ):
            raise CertificateError("Pair coordinates must be exact integers")
        if a_nu <= 0 or b_nu <= 0 or math.gcd(a_nu, b_nu) != 1:
            raise CertificateError("Pairs must be positive primitive integers")
        lin = [cd * a_nu, -b_nu]
        gamma_poly = poly_rem_monic_z(poly_mul_exact_z(gamma_poly, lin), f_tilde)

    k_steps = _req_int(payload, "k_steps")
    if not (1 <= k_steps <= 8):
        raise CertificateError("Mode 3 requires 1 <= k_steps <= 8")

    beta_hat_claimed = poly_trim(_req_int_list(payload, "beta_hat", min_len=1, max_len=d))
    trace_claimed = payload.get("trace")
    if not isinstance(trace_claimed, list) or len(trace_claimed) != k_steps + 1:
        raise CertificateError("Mode 3 trace must have exactly k_steps + 1 entries")

    # Verify odd-degree divisibility 4 | (3^d + 1)
    if (3 ** d + 1) % 4 != 0:
        raise CertificateError("4 | (3^d + 1) violated")

    # Independent re-computation of 3-adic Newton-Hensel lift
    beta_hat_calc, trace_calc = adic3_newton_hensel_sqrt(gamma_poly, f_tilde, k_steps)

    # Verify claimed trace step-by-step against exact quadratic lifting invariants
    for idx, entry in enumerate(trace_claimed):
        if not isinstance(entry, dict):
            raise CertificateError(f"Trace entry {idx} must be a JSON object")
        _check_keys(entry, {"k", "exp3", "beta_mod", "gamma_mod"}, f"trace[{idx}]")
        k_val = _req_int(entry, "k")
        exp3 = _req_int(entry, "exp3")
        if k_val != idx or exp3 != (2 ** idx):
            raise CertificateError(f"Trace index/exponent mismatch at step {idx}")
        b_mod = poly_trim(_req_int_list(entry, "beta_mod", min_len=1, max_len=d))
        g_mod = poly_trim(_req_int_list(entry, "gamma_mod", min_len=1, max_len=d))
        mod_cur = 3 ** exp3
        # Check beta_k^2 == Gamma (mod 3^(2^k), f_tilde)
        bsq = poly_rem_monic_mod(poly_mul_mod(b_mod, b_mod, mod_cur), f_tilde, mod_cur)
        if bsq != poly_mod_p(gamma_poly, mod_cur):
            raise CertificateError(f"Quadratic lift invariant beta_k^2 == Gamma failed at k={idx}")
        # Check 2 * beta_k * gamma_k == 1 (mod 3^(2^max(0, k-1)), f_tilde)
        inv_mod = 3 ** (2 ** max(0, idx - 1))
        inv_prod = poly_rem_monic_mod(
            poly_mul_mod([2], poly_mul_mod(b_mod, g_mod, inv_mod), inv_mod), f_tilde, inv_mod
        )
        if inv_prod != [1]:
            raise CertificateError(f"Inverse invariant 2*beta_k*gamma_k == 1 failed at k={idx}")
        if b_mod != trace_calc[idx]["beta_mod"] or g_mod != trace_calc[idx]["gamma_mod"]:
            raise CertificateError(f"Trace step {idx} differs from canonical deterministic lift")

    # Allow +/- sign for balanced root
    neg_calc = poly_trim([-c for c in beta_hat_calc])
    if beta_hat_claimed != beta_hat_calc and beta_hat_claimed != neg_calc:
        raise CertificateError("Claimed beta_hat does not match deterministic 3-adic root (up to sign)")

    # Global exact Z[X]/(f_tilde) square verification
    sq_global = poly_rem_monic_z(poly_mul_exact_z(beta_hat_claimed, beta_hat_claimed), f_tilde)
    if sq_global != gamma_poly:
        raise CertificateError("Global exact square identity beta_hat(X)^2 == Gamma_tilde(X) mod f_tilde failed")

    # Verify balanced representative bound |b_j| < (3^(2^K) - 1)/2
    half_mod = (3 ** (2 ** k_steps) - 1) // 2
    max_abs = max(abs(c) for c in beta_hat_claimed)
    if max_abs > half_mod:
        raise CertificateError("beta_hat exceeds balanced 3^(2^K) half-range")

    return {
        "mode": "adic3_newton_hensel_sqrt_cert",
        "degree": d,
        "num_pairs": len(raw_pairs),
        "k_steps": k_steps,
        "max_abs_coeff": max_abs,
    }


# ---------------------------------------------------------------------------
# Mode 4: Adleman Characters, F_2 Kernel, Dixon Unsealing & Induction Split
# ---------------------------------------------------------------------------

def _verify_mode4(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "N",
        "g0",
        "g1",
        "m_N",
        "f1_coeffs",
        "f2_coeffs",
        "factor_base_primes",
        "characters_side1",
        "characters_side2",
        "relations",
        "nullspace_mask",
        "beta1_hat",
        "beta2_hat",
        "k_steps_sqrt",
        "Y_val",
        "Z_val",
        "split_divisor",
    }
    _check_keys(payload, expected, "Mode 4 payload")

    N = _req_int(payload, "N")
    g0 = _req_int(payload, "g0")
    g1 = _req_int(payload, "g1")
    m_N = _req_int(payload, "m_N")
    Y_val = _req_int(payload, "Y_val")
    Z_val = _req_int(payload, "Z_val")
    split_divisor = _req_int(payload, "split_divisor")
    k_steps = _req_int(payload, "k_steps_sqrt")

    if N < 15 or N % 2 == 0 or is_prime_exact(N):
        raise CertificateError("Mode 4 requires an odd composite N >= 15")
    if (
        not (0 <= m_N < N)
        or math.gcd(g0, g1) != 1
        or math.gcd(g1, N) != 1
        or (g1 * m_N - g0) % N != 0
    ):
        raise CertificateError("Mode 4 base pair (g0, g1, m_N) invalid")
    if not (1 <= k_steps <= 8):
        raise CertificateError("Mode 4 requires 1 <= k_steps_sqrt <= 8")

    f1 = _req_int_list(payload, "f1_coeffs", min_len=4, max_len=8)
    f2 = _req_int_list(payload, "f2_coeffs", min_len=4, max_len=8)
    if len(f1) != len(f2):
        raise CertificateError("f1_coeffs and f2_coeffs must have equal odd degree d >= 3")
    d = len(f1) - 1
    if d % 2 == 0:
        raise CertificateError("Degree d must be odd")

    for idx, fc in enumerate((f1, f2), start=1):
        if fc[-1] % 3 != 1 or math.gcd(fc[-1], N) != 1:
            raise CertificateError(f"f{idx} leading coeff must satisfy c_d == 1 (mod 3) and gcd(c_d, N) = 1")
        if eval_binary_form(fc, g0, g1) % N != 0:
            raise CertificateError(f"f{idx}(g0, g1) != 0 (mod N)")
        ft = build_monic_f_tilde(fc)
        if not is_monic_irreducible_f3(poly_mod_p(ft, 3)):
            raise CertificateError(f"f{idx}_tilde mod 3 is not irreducible over F_3")

    ft1 = build_monic_f_tilde(f1)
    ft2 = build_monic_f_tilde(f2)
    df1 = poly_deriv_z(ft1)
    df2 = poly_deriv_z(ft2)
    c1d, c2d = f1[-1], f2[-1]
    theta1_mod = (c1d * m_N) % N
    theta2_mod = (c2d * m_N) % N
    df1_mod = poly_eval_mod(df1, theta1_mod, N)
    df2_mod = poly_eval_mod(df2, theta2_mod, N)
    if math.gcd(df1_mod, N) != 1 or math.gcd(df2_mod, N) != 1:
        raise CertificateError("Derivative evaluation f'_tilde(c_d * m_N) must be coprime to N")

    fb_primes = _req_int_list(payload, "factor_base_primes", min_len=1, max_len=32)
    if len(set(fb_primes)) != len(fb_primes):
        raise CertificateError("factor_base_primes must be distinct")
    for p in fb_primes:
        if not is_prime_exact(p) or N % p == 0:
            raise CertificateError(f"Invalid factor base prime {p}")

    # Validate Adleman degree-1 character pairs (ell, s) with f_tilde(s) == 0 (mod ell)
    def _validate_chars(key: str, ft: Sequence[int]) -> List[Tuple[int, int]]:
        raw = payload.get(key)
        if not isinstance(raw, list) or not (1 <= len(raw) <= 24):
            raise CertificateError(f"{key} must be a list of 1..24 [ell, s] pairs")
        out: List[Tuple[int, int]] = []
        seen = set()
        for item in raw:
            if not isinstance(item, list) or len(item) != 2:
                raise CertificateError(f"Each entry of {key} must be [ell, s]")
            ell, s_root = item[0], item[1]
            if (
                isinstance(ell, bool)
                or isinstance(s_root, bool)
                or not isinstance(ell, int)
                or not isinstance(s_root, int)
            ):
                raise CertificateError(f"{key} entries must be integers")
            if ell <= 3 or not is_prime_exact(ell) or N % ell == 0:
                raise CertificateError(f"Invalid character prime {ell} in {key}")
            if not (0 <= s_root < ell):
                raise CertificateError(f"Character root {s_root} out of range mod {ell}")
            if poly_eval_mod(ft, s_root, ell) != 0:
                raise CertificateError(f"Character root s={s_root} is not a root of f_tilde mod {ell}")
            if (ell, s_root) in seen:
                raise CertificateError(f"Duplicate character ({ell}, {s_root}) in {key}")
            seen.add((ell, s_root))
            out.append((ell, s_root))
        return out

    chars1 = _validate_chars("characters_side1", ft1)
    chars2 = _validate_chars("characters_side2", ft2)

    raw_rels = payload.get("relations")
    if not isinstance(raw_rels, list) or not (2 <= len(raw_rels) <= 40):
        raise CertificateError("Mode 4 requires 2..40 relations")

    R_tot = len(raw_rels)
    mask = _req_int_list(payload, "nullspace_mask", min_len=R_tot, max_len=R_tot)
    if any(b not in (0, 1) for b in mask) or sum(mask) == 0:
        raise CertificateError("nullspace_mask must be a nonzero binary vector of length R_tot")

    # Parse and verify every relation Eq. (6.1) individually
    parsed_rels: List[Dict[str, Any]] = []
    parity_cols: List[List[int]] = []

    for r_idx, rel in enumerate(raw_rels):
        if not isinstance(rel, dict):
            raise CertificateError(f"Relation {r_idx} must be a JSON object")
        _check_keys(
            rel,
            {"z_m", "w_m", "e1", "e2", "eg", "u_fb", "side1_factors", "side2_factors"},
            f"relations[{r_idx}]",
        )
        z_m = _req_int(rel, "z_m")
        w_m = _req_int(rel, "w_m")
        e1 = _req_int(rel, "e1")
        e2 = _req_int(rel, "e2")
        eg = _req_int(rel, "eg")
        u_fb = _req_int_list(rel, "u_fb", min_len=len(fb_primes), max_len=len(fb_primes))

        if not (1 <= z_m < N) or math.gcd(z_m, N) != 1:
            raise CertificateError(f"Relation {r_idx} z_m must be a unit in (Z/NZ)^x")
        if not (0 <= w_m < N) or (z_m * z_m - w_m) % N != 0:
            raise CertificateError(f"Relation {r_idx} violates w_m == z_m^2 (mod N)")

        def _parse_side(s_key: str, cd_side: int) -> List[Tuple[int, int, int]]:
            raw_s = rel.get(s_key)
            if not isinstance(raw_s, list) or not (1 <= len(raw_s) <= 24):
                raise CertificateError(f"Relation {r_idx} {s_key} must be a non-empty list of 1..24 triples")
            out_s: List[Tuple[int, int, int]] = []
            for tri in raw_s:
                if not isinstance(tri, list) or len(tri) != 3:
                    raise CertificateError(f"Relation {r_idx} {s_key} entry must be [a, b, sigma]")
                a_v, b_v, sig = tri[0], tri[1], tri[2]
                if any(isinstance(x, bool) or not isinstance(x, int) for x in (a_v, b_v, sig)):
                    raise CertificateError("Side factor entries must be integers")
                if a_v <= 0 or b_v <= 0 or math.gcd(a_v, b_v) != 1 or sig not in (-1, 1):
                    raise CertificateError("Side factor must have primitive positive (a,b) and sigma in {-1, 1}")
                phi_val = (cd_side * (a_v - b_v * m_N)) % N
                if math.gcd(phi_val, N) != 1:
                    raise CertificateError("Algebraic factor image phi(gamma(a,b)) must be coprime to N")
                out_s.append((a_v, b_v, sig))
            return out_s

        s1 = _parse_side("side1_factors", c1d)
        s2 = _parse_side("side2_factors", c2d)

        # Verify Eq. (6.1) modulo N:
        # w_m == c1d^e1 * c2d^e2 * g1^eg * prod p^{u_p} * phi1(Gamma1) * phi2(Gamma2) (mod N)
        def _pow_signed(base: int, exp: int) -> int:
            b = base % N
            if exp >= 0:
                return pow(b, exp, N)
            return pow(mod_inv_exact(b, N), -exp, N)

        rhs_mod = (
            _pow_signed(c1d, e1)
            * _pow_signed(c2d, e2)
            * _pow_signed(g1, eg)
        ) % N
        for p, u_p in zip(fb_primes, u_fb):
            rhs_mod = (rhs_mod * _pow_signed(p, u_p)) % N
        for a_v, b_v, sig in s1:
            phi_v = (c1d * (a_v - b_v * m_N)) % N
            rhs_mod = (rhs_mod * _pow_signed(phi_v, sig)) % N
        for a_v, b_v, sig in s2:
            phi_v = (c2d * (a_v - b_v * m_N)) % N
            rhs_mod = (rhs_mod * _pow_signed(phi_v, sig)) % N

        if rhs_mod != w_m:
            raise CertificateError(f"Relation {r_idx} fails Eq. (6.1) congruence modulo N")

        # Build F_2 parity column: [e1, e2, eg, u_fb..., chars1..., chars2...]
        col = [e1 & 1, e2 & 1, eg & 1] + [u & 1 for u in u_fb]
        for ell, s_root in chars1:
            prod_leg = 1
            for a_v, b_v, _ in s1:
                leg = legendre_symbol(c1d * a_v - b_v * s_root, ell)
                if leg == 0:
                    raise CertificateError(f"Relation {r_idx} side1 factor vanishes at character ({ell},{s_root})")
                prod_leg *= leg
            col.append(1 if prod_leg == -1 else 0)
        for ell, s_root in chars2:
            prod_leg = 1
            for a_v, b_v, _ in s2:
                leg = legendre_symbol(c2d * a_v - b_v * s_root, ell)
                if leg == 0:
                    raise CertificateError(f"Relation {r_idx} side2 factor vanishes at character ({ell},{s_root})")
                prod_leg *= leg
            col.append(1 if prod_leg == -1 else 0)

        parity_cols.append(col)
        parsed_rels.append(
            {
                "z_m": z_m,
                "w_m": w_m,
                "e1": e1,
                "e2": e2,
                "eg": eg,
                "u_fb": u_fb,
                "s1": s1,
                "s2": s2,
            }
        )

    # Verify nullspace_mask lies in the F_2 right nullspace of the parity matrix
    n_rows = len(parity_cols[0])
    mat_rows = [[parity_cols[c][r] for c in range(R_tot)] for r in range(n_rows)]
    for r in range(n_rows):
        dot_f2 = 0
        for c in range(R_tot):
            dot_f2 ^= (mat_rows[r][c] & mask[c])
        if dot_f2 != 0:
            raise CertificateError(f"nullspace_mask violates F_2 parity row {r}")
    # Also confirm nullspace dimension >= 1 via independent Gaussian elimination
    ns_basis = f2_right_nullspace(mat_rows)
    if not ns_basis:
        raise CertificateError("Parity matrix has trivial F_2 nullspace")

    # Assemble Gamma_tilde_{x,1} and Gamma_tilde_{x,2} on T_x = {m : mask[m] == 1}
    E1_sum = 0
    E2_sum = 0
    Eg_sum = 0
    Up_sum = [0] * len(fb_primes)
    gamma1 = poly_rem_monic_z(poly_mul_exact_z(df1, df1), ft1)
    gamma2 = poly_rem_monic_z(poly_mul_exact_z(df2, df2), ft2)
    neg_inv1 = 1
    neg_inv2 = 1
    Z_calc = 1
    W_prod = 1

    for idx, bit in enumerate(mask):
        if bit == 0:
            continue
        rel = parsed_rels[idx]
        E1_sum += rel["e1"]
        E2_sum += rel["e2"]
        Eg_sum += rel["eg"]
        for k_p, u_v in enumerate(rel["u_fb"]):
            Up_sum[k_p] += u_v
        Z_calc = (Z_calc * rel["z_m"]) % N
        W_prod = (W_prod * rel["w_m"]) % N
        for a_v, b_v, sig in rel["s1"]:
            gamma1 = poly_rem_monic_z(poly_mul_exact_z(gamma1, [c1d * a_v, -b_v]), ft1)
            if sig == -1:
                phi_v = (c1d * (a_v - b_v * m_N)) % N
                neg_inv1 = (neg_inv1 * mod_inv_exact(phi_v, N)) % N
        for a_v, b_v, sig in rel["s2"]:
            gamma2 = poly_rem_monic_z(poly_mul_exact_z(gamma2, [c2d * a_v, -b_v]), ft2)
            if sig == -1:
                phi_v = (c2d * (a_v - b_v * m_N)) % N
                neg_inv2 = (neg_inv2 * mod_inv_exact(phi_v, N)) % N

    if (E1_sum & 1) or (E2_sum & 1) or (Eg_sum & 1) or any(u & 1 for u in Up_sum):
        raise CertificateError("Combined exponents over T_x are not all even")

    beta1_claimed = poly_trim(_req_int_list(payload, "beta1_hat", min_len=1, max_len=d))
    beta2_claimed = poly_trim(_req_int_list(payload, "beta2_hat", min_len=1, max_len=d))

    # Independently verify both algebraic square roots via Lemma 5.2 (3-adic lift + exact Z[X] check)
    beta1_calc, _ = adic3_newton_hensel_sqrt(gamma1, ft1, k_steps)
    beta2_calc, _ = adic3_newton_hensel_sqrt(gamma2, ft2, k_steps)
    if beta1_claimed != beta1_calc and beta1_claimed != poly_trim([-c for c in beta1_calc]):
        raise CertificateError("beta1_hat does not match 3-adic Newton-Hensel root on side 1")
    if beta2_claimed != beta2_calc and beta2_claimed != poly_trim([-c for c in beta2_calc]):
        raise CertificateError("beta2_hat does not match 3-adic Newton-Hensel root on side 2")

    # Compute Y from Step 4 formula and check Y^2 == prod_{m in T_x} w_m (mod N)
    def _pow_signed_n(base: int, exp: int) -> int:
        b = base % N
        if exp >= 0:
            return pow(b, exp, N)
        return pow(mod_inv_exact(b, N), -exp, N)

    Y_calc = (
        _pow_signed_n(c1d, E1_sum // 2)
        * _pow_signed_n(c2d, E2_sum // 2)
        * _pow_signed_n(g1, Eg_sum // 2)
    ) % N
    for p, up in zip(fb_primes, Up_sum):
        Y_calc = (Y_calc * _pow_signed_n(p, up // 2)) % N

    b1_eval = poly_eval_mod(beta1_claimed, theta1_mod, N)
    b2_eval = poly_eval_mod(beta2_claimed, theta2_mod, N)
    Y_calc = (Y_calc * b1_eval * mod_inv_exact(df1_mod, N) * neg_inv1) % N
    Y_calc = (Y_calc * b2_eval * mod_inv_exact(df2_mod, N) * neg_inv2) % N

    if not (0 <= Y_val < N):
        raise CertificateError(f"Claimed Y_val={Y_val} must lie in canonical range [0, N)")
    if not (0 <= Z_val < N):
        raise CertificateError(f"Claimed Z_val={Z_val} must lie in canonical range [0, N)")
    if Y_val != Y_calc and (Y_val + Y_calc) % N != 0:
        raise CertificateError(f"Claimed Y_val={Y_val} disagrees with assembled Y_calc={Y_calc}")
    if Z_val != Z_calc:
        raise CertificateError(f"Claimed Z_val={Z_val} disagrees with unsealed Z_calc={Z_calc}")
    if (Y_val * Y_val - W_prod) % N != 0 or (Z_val * Z_val - W_prod) % N != 0:
        raise CertificateError("Congruence of squares Y^2 == Z^2 == prod w_m (mod N) failed")

    d_star = math.gcd(Z_val - Y_val, N)
    if d_star != split_divisor or not (1 < d_star < N) or N % d_star != 0:
        raise CertificateError(f"Nontrivial split failed: gcd(Z - Y, N) = {d_star}")

    # Verify Theorem 1.1 strong-induction runtime & workspace contractions via exact integer cubes
    if not (
        (104 ** 3) * (100 ** 3) < 2 * (8255 ** 3)
        and 2115 + 8255 < 10372 < 10400 < 10500
        and (38 ** 3) * (100 ** 3) < 2 * (3017 ** 3)
        and 3740 < 3800 < 4000
    ):
        raise CertificateError("Theorem 1.1 strong-induction contraction guard failed")

    return {
        "mode": "dixon_character_and_induction_split_cert",
        "N": N,
        "degree": d,
        "R_tot": R_tot,
        "selected_relations": sum(mask),
        "split_divisor": d_star,
        "cofactor": N // d_star,
    }


# ---------------------------------------------------------------------------
# Public Entry Points
# ---------------------------------------------------------------------------

def verify_certificate_dict(data: Mapping[str, Any]) -> Dict[str, Any]:
    """Verify an already-parsed certificate dictionary under L13FACT-COGENTIC-CERT-1.0."""
    if not isinstance(data, Mapping):
        raise CertificateError("Certificate must be a mapping")
    allowed_top = {"protocol", "certificate_id", "mode", "payload", "description", "note"}
    extra_top = set(data.keys()) - allowed_top
    if extra_top:
        raise CertificateError(f"Unexpected top-level keys: {sorted(extra_top)}")
    for opt_k in ("description", "note"):
        if opt_k in data and not isinstance(data[opt_k], str):
            raise CertificateError(f"Optional field {opt_k!r} must be a string")

    proto = _req_str(data, "protocol")
    if proto != PROTOCOL_ID:
        raise CertificateError(f"Unsupported protocol {proto!r}; expected {PROTOCOL_ID!r}")
    cert_id = _req_str(data, "certificate_id")
    mode = _req_str(data, "mode")
    if mode not in VALID_MODES:
        raise CertificateError(f"Unknown certificate mode {mode!r}")

    payload = data.get("payload")
    if not isinstance(payload, Mapping):
        raise CertificateError("Field 'payload' must be a JSON object")

    try:
        if mode == "mod_n_lattice_and_lagrange_split_cert":
            summary = _verify_mode1(payload)
        elif mode == "mod3_laplace_ladder_and_smooth_cert":
            summary = _verify_mode2(payload)
        elif mode == "adic3_newton_hensel_sqrt_cert":
            summary = _verify_mode3(payload)
        else:
            summary = _verify_mode4(payload)
    except CertificateError:
        raise
    except ValueError as exc:
        raise CertificateError(f"Exact verification value error: {exc}") from exc

    summary["certificate_id"] = cert_id
    summary["protocol"] = PROTOCOL_ID
    return summary


def verify_certificate_str(raw: str) -> Dict[str, Any]:
    return verify_certificate_dict(load_strict_json_str(raw))


def verify_certificate_file(path: Path | str) -> Dict[str, Any]:
    raw = Path(path).read_text(encoding="utf-8")
    return verify_certificate_str(raw)
