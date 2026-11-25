"""Comprehensive 74-test suite for L13FACT-COGENTIC-CERT-1.0.

Includes:
  - 1 aggregate canonical 16-certificate replay,
  - 3 raw-JSON zero-float / NaN / duplicate-key parser tests,
  - 2 exact arithmetic soundness regressions (Sorenson-Webster 12-base SPRP & non-square 3-adic Euler test),
  - 68 parametrized live adversarial forgery tests (12 schema/parser + 13 Mode 1 + 14 Mode 2 + 13 Mode 3 + 16 Mode 4),
    each asserting an exact regex match on the intended CertificateError branch.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import pytest

from src.l13fact_certifier import (
    PROTOCOL_ID,
    verify_certificate_dict,
    verify_certificate_file,
    verify_certificate_str,
)
from src.l13fact_exact import (
    CertificateError,
    adic3_newton_hensel_sqrt,
    is_prime_exact,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(name: str) -> dict:
    return json.loads((CERT_DIR / f"{name}.cert.json").read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# 1. Canonical Replay + Raw JSON Guards + Soundness Regressions (6 tests)
# ---------------------------------------------------------------------------

def test_all_16_canonical_certificates_verify() -> None:
    files = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(files) == 16
    for f in files:
        res = verify_certificate_file(f)
        assert res["protocol"] == PROTOCOL_ID


def test_raw_json_rejects_float_literal() -> None:
    raw = '{"protocol": "L13FACT-COGENTIC-CERT-1.0", "certificate_id": "x", "mode": "adic3_newton_hensel_sqrt_cert", "payload": {"k": 1.5}}'
    with pytest.raises(CertificateError, match="Floating-point literal rejected"):
        verify_certificate_str(raw)


def test_raw_json_rejects_nan_constant() -> None:
    raw = '{"protocol": "L13FACT-COGENTIC-CERT-1.0", "certificate_id": "x", "mode": "adic3_newton_hensel_sqrt_cert", "payload": {"k": NaN}}'
    with pytest.raises(CertificateError, match="Non-standard JSON constant rejected"):
        verify_certificate_str(raw)


def test_raw_json_rejects_duplicate_keys() -> None:
    raw = '{"protocol": "L13FACT-COGENTIC-CERT-1.0", "protocol": "L13FACT-COGENTIC-CERT-1.0"}'
    with pytest.raises(CertificateError, match="Duplicate JSON key rejected"):
        verify_certificate_str(raw)


def test_regression_13base_mr_rejects_12base_sorenson_webster_sprp() -> None:
    # 318665857834031151167461 = 399165290221 * 798330580441 (12-base SPRP)
    assert is_prime_exact(318665857834031151167461) is False
    with pytest.raises(CertificateError, match="exceeds deterministic 13-base Miller-Rabin limit"):
        is_prime_exact(3_317_044_064_679_887_385_961_981)


def test_regression_3adic_rejects_nonsquare_in_f3d() -> None:
    # X^3 + 2X + 1 is irreducible over F_3; constant 2 is a nonsquare in F_{3^3}^x since (27-1)/2 = 13 is odd
    with pytest.raises(CertificateError, match="not a square in F_\\{3\\^d\\}\\^x"):
        adic3_newton_hensel_sqrt([2], [1, 2, 0, 1], 2)


# ---------------------------------------------------------------------------
# 2. 64 Live Adversarial Forgeries (Exact Branch Assertions)
# ---------------------------------------------------------------------------

def _build_68_forgeries() -> list[tuple[str, dict, str]]:
    m1 = _load("m1_lattice_lagrange_n10403_d3")
    m2 = _load("m2_mod3_laplace_n323_d3")
    m3 = _load("m3_adic3_sqrt_d3_p2_k3")
    m4 = _load("m4_dixon_split_n323_17x19")

    cases: list[tuple[str, dict, str]] = []

    def add(name: str, base: dict, mutator, regex: str) -> None:
        c = copy.deepcopy(base)
        mutator(c)
        cases.append((name, c, regex))

    # --- Schema / Top-Level (12) ---
    add("S01_bad_protocol", m1, lambda c: c.__setitem__("protocol", "WRONG-1.0"), "Unsupported protocol")
    add("S02_empty_cert_id", m1, lambda c: c.__setitem__("certificate_id", ""), "non-empty string")
    add("S03_unknown_mode", m1, lambda c: c.__setitem__("mode", "fake_mode"), "Unknown certificate mode")
    add("S04_extra_top_key", m1, lambda c: c.__setitem__("rogue", 1), "Unexpected top-level keys")
    add("S05_bad_description_type", m1, lambda c: c.__setitem__("description", 123), "Optional field 'description' must be a string")
    add("S06_bad_note_type", m1, lambda c: c.__setitem__("note", ["x"]), "Optional field 'note' must be a string")
    add("S07_payload_not_dict", m1, lambda c: c.__setitem__("payload", [1, 2]), "must be a JSON object")
    add("S08_missing_protocol", m1, lambda c: c.pop("protocol"), "Missing required string field 'protocol'")
    add("S09_bool_as_int", m1, lambda c: c["payload"].__setitem__("N", True), "must be an exact integer")
    add("S10_float_in_dict", m1, lambda c: c["payload"].__setitem__("G", 50.0), "must be an exact integer")
    add("S11_missing_payload_key", m1, lambda c: c["payload"].pop("m_N"), "Missing keys in Mode 1 payload")
    add("S12_extra_payload_key", m1, lambda c: c["payload"].__setitem__("junk", 0), "Unexpected keys in Mode 1 payload")

    # --- Mode 1 Forgeries (13) ---
    add("M1_01_even_N", m1, lambda c: c["payload"].__setitem__("N", 10402), "requires odd N >= 15")
    add("M1_02_bad_g_range", m1, lambda c: c["payload"].__setitem__("g0", 200), "1 <= g0, g1 <= 2G")
    add("M1_03_noncoprime_g", m1, lambda c: (c["payload"].__setitem__("g0", 80), c["payload"].__setitem__("g1", 82)), "gcd\\(g0, g1\\)")
    add("M1_04_bad_mN", m1, lambda c: c["payload"].__setitem__("m_N", (c["payload"]["m_N"] + 1) % c["payload"]["N"]), "g1 \\* m_N == g0")
    add("M1_05_small_g1_power", m1, lambda c: (c["payload"].__setitem__("g1", 5), c["payload"].__setitem__("m_N", (c["payload"]["g0"] * pow(5, -1, c["payload"]["N"])) % c["payload"]["N"])), "g1\\^\\(n_dim - 1\\) > N/2")
    add("M1_06_col_outside_lambda", m1, lambda c: c["payload"]["B_lat"][0].__setitem__(0, c["payload"]["B_lat"][0][0] + 1), "does not lie in Lambda_n")
    add("M1_07_wrong_det", m1, lambda c: c["payload"].__setitem__("B_lat", [[c["payload"]["B_lat"][r][j] * (2 if j == 0 else 1) for j in range(3)] for r in range(3)]), "Expected \\|det\\(B_lat\\)\\|")
    add("M1_08_wrong_adjugate", m1, lambda c: c["payload"]["A_adj"][0].__setitem__(0, c["payload"]["A_adj"][0][0] + 1), "Adjugate identity")
    add("M1_09_bad_z_val", m1, lambda c: c["payload"].__setitem__("z_val", (c["payload"]["z_val"] + 1) % c["payload"]["N"]), "z_val must equal s_val")
    add("M1_10_v1_outside_Lz", m1, lambda c: c["payload"]["v1"].__setitem__(0, c["payload"]["v1"][0] + 1), "do not lie in L_z")
    add("M1_11_overlapping_primes", m1, lambda c: c["payload"].__setitem__("B_primes", [2, 7]), "must be disjoint")
    add("M1_12_composite_in_A", m1, lambda c: c["payload"].__setitem__("A_primes", [4, 5]), "Invalid prime 4 in A_primes")
    add("M1_13_Q_bound_too_large", m1, lambda c: c["payload"].__setitem__("Q_bound", 60), "Q_bound\\^r0 <= \\(1/2\\) sqrt\\(N\\)")

    # --- Mode 2 Forgeries (13) ---
    add("M2_01_N_div_3", m2, lambda c: c["payload"].__setitem__("N", 321), "coprime to 6")
    add("M2_02_M_not_div_3", m2, lambda c: c["payload"].__setitem__("M_scale", 181), "divisible by 3")
    add("M2_03_W_too_large", m2, lambda c: c["payload"].__setitem__("W_box", 40), "6 \\* W_box <= M_scale")
    add("M2_04_even_degree_h0", m2, lambda c: c["payload"].__setitem__("h0_coeffs", [1, 0, 1, 0, 1]), "monic of odd degree")
    add("M2_05_reducible_h0", m2, lambda c: c["payload"].__setitem__("h0_coeffs", [0, 2, 0, 1]), "not irreducible over F_3")
    add("M2_06_c_tilde_oob", m2, lambda c: c["payload"]["c_tilde"].__setitem__(0, 99), "outside box")
    add("M2_07_f_g0g1_nonzero", m2, lambda c: c["payload"]["c_tilde"].__setitem__(0, c["payload"]["c_tilde"][0] + 1), "f\\(g0, g1\\) == 0")
    add("M2_08_nondecreasing_ladder", m2, lambda c: c["payload"].__setitem__("ladder_Y", [200, 90, 95, 19]), "strictly decreasing")
    add("M2_09_composite_special_q", m2, lambda c: c["payload"].__setitem__("special_q", 21), "must be a prime > 3")
    add("M2_10_bad_rq", m2, lambda c: c["payload"].__setitem__("r_q", (c["payload"]["r_q"] + 1) % c["payload"]["special_q"]), "f\\(r_q, 1\\) == 0")
    add("M2_11_nonprimitive_box_pt", m2, lambda c: c["payload"].__setitem__("box_point", [2 * c["payload"]["box_point"][0], 2 * c["payload"]["box_point"][1]]), "positive and primitive")
    add("M2_12_point_not_in_lattice", m2, lambda c: c["payload"]["box_point"].__setitem__(0, c["payload"]["box_point"][0] + 1), "special-q lattice")
    add("M2_13_cofactor_not_smooth", m2, lambda c: c["payload"].__setitem__("smooth_cap", 2), "is not 2-smooth")
    add("M2_14_vacuous_smooth_cap", m2, lambda c: c["payload"].__setitem__("smooth_cap", 10**9), "non-vacuous smoothness")

    # --- Mode 3 Forgeries (13) ---
    add("M3_01_even_degree", m3, lambda c: c["payload"].__setitem__("f_coeffs", [1, 1, 0, 0, 1]), "odd degree d >= 3")
    add("M3_02_cd_mod3_bad", m3, lambda c: c["payload"]["f_coeffs"].__setitem__(-1, 2), "c_d == 1 \\(mod 3\\)")
    add("M3_03_reducible_mod3", m3, lambda c: c["payload"].__setitem__("f_coeffs", [0, 1, 0, 1]), "irreducible over F_3")
    add("M3_04_empty_pairs", m3, lambda c: c["payload"].__setitem__("pairs", []), "1\\.\\.32 primitive pairs")
    add("M3_05_nonprimitive_pair", m3, lambda c: c["payload"]["pairs"].__setitem__(0, [4, 2]), "positive primitive")
    add("M3_06_k_steps_zero", m3, lambda c: c["payload"].__setitem__("k_steps", 0), "1 <= k_steps <= 8")
    add("M3_07_k_steps_dos", m3, lambda c: c["payload"].__setitem__("k_steps", 20), "1 <= k_steps <= 8")
    add("M3_08_trace_truncated", m3, lambda c: c["payload"]["trace"].pop(), "exactly k_steps \\+ 1 entries")
    add("M3_09_trace_bad_exp3", m3, lambda c: c["payload"]["trace"][1].__setitem__("exp3", 3), "index/exponent mismatch")
    add("M3_10_trace_corrupt_beta", m3, lambda c: c["payload"]["trace"][1]["beta_mod"].__setitem__(0, (c["payload"]["trace"][1]["beta_mod"][0] + 1) % 9), "beta_k\\^2 == Gamma failed")
    add("M3_11_trace_corrupt_gamma", m3, lambda c: c["payload"]["trace"][1]["gamma_mod"].__setitem__(0, (c["payload"]["trace"][1]["gamma_mod"][0] + 1) % 3), "2\\*beta_k\\*gamma_k == 1 failed")
    add("M3_12_corrupt_beta_hat", m3, lambda c: c["payload"]["beta_hat"].__setitem__(0, c["payload"]["beta_hat"][0] + 1), "does not match deterministic 3-adic root")
    add("M3_13_nonsquare_pairs", m3, lambda c: c["payload"]["pairs"].pop(), "not a square|failed global exact identity")

    # --- Mode 4 Forgeries (13) ---
    add("M4_01_prime_N", m4, lambda c: c["payload"].__setitem__("N", 317), "odd composite N >= 15")
    add("M4_02_degree_mismatch", m4, lambda c: c["payload"]["f2_coeffs"].append(0), "equal odd degree")
    add("M4_03_bad_fb_prime", m4, lambda c: c["payload"].__setitem__("factor_base_primes", [2, 3, 4]), "Invalid factor base prime")
    add("M4_04_bad_char_root", m4, lambda c: c["payload"]["characters_side1"][0].__setitem__(1, (c["payload"]["characters_side1"][0][1] + 1) % c["payload"]["characters_side1"][0][0]), "not a root of f_tilde")
    add("M4_05_dup_character", m4, lambda c: c["payload"]["characters_side1"].append(list(c["payload"]["characters_side1"][0])), "Duplicate character")
    add("M4_06_zero_nullspace_mask", m4, lambda c: c["payload"].__setitem__("nullspace_mask", [0] * len(c["payload"]["relations"])), "nonzero binary vector")
    add("M4_07_bad_wm_square", m4, lambda c: c["payload"]["relations"][0].__setitem__("w_m", (c["payload"]["relations"][0]["w_m"] + 1) % c["payload"]["N"]), "w_m == z_m\\^2")
    add("M4_08_eq61_broken", m4, lambda c: c["payload"]["relations"][0].__setitem__("e1", c["payload"]["relations"][0]["e1"] + 1), "fails Eq\\. \\(6\\.1\\)")
    add("M4_09_bad_nullspace_mask", m4, lambda c: c["payload"].__setitem__("nullspace_mask", [1] + [0] * (len(c["payload"]["relations"]) - 1)), "violates F_2 parity row")
    add("M4_10_corrupt_beta1", m4, lambda c: c["payload"]["beta1_hat"].__setitem__(0, c["payload"]["beta1_hat"][0] + 1), "does not match 3-adic Newton-Hensel root on side 1")
    add("M4_11_corrupt_Y", m4, lambda c: c["payload"].__setitem__("Y_val", (c["payload"]["Y_val"] + 1) % c["payload"]["N"]), "Claimed Y_val")
    add("M4_12_corrupt_Z", m4, lambda c: c["payload"].__setitem__("Z_val", (c["payload"]["Z_val"] + 1) % c["payload"]["N"]), "Claimed Z_val")
    add("M4_13_wrong_split_divisor", m4, lambda c: c["payload"].__setitem__("split_divisor", 1), "Nontrivial split failed")
    add("M4_14_empty_algebraic_sides", m4, lambda c: c["payload"]["relations"][0].__setitem__("side1_factors", []), "non-empty list of 1\\.\\.24 triples")
    add("M4_15_out_of_range_mN", m4, lambda c: c["payload"].__setitem__("m_N", c["payload"]["m_N"] + c["payload"]["N"]), "base pair \\(g0, g1, m_N\\) invalid")
    add("M4_16_out_of_range_Y", m4, lambda c: c["payload"].__setitem__("Y_val", c["payload"]["Y_val"] + c["payload"]["N"]), "canonical range \\[0, N\\)")

    assert len(cases) == 68
    return cases


FORGERIES = _build_68_forgeries()


@pytest.mark.parametrize("name,cert,expected_regex", FORGERIES, ids=[c[0] for c in FORGERIES])
def test_adversarial_forgery_rejected(name: str, cert: dict, expected_regex: str) -> None:
    with pytest.raises(CertificateError, match=expected_regex):
        verify_certificate_dict(cert)
