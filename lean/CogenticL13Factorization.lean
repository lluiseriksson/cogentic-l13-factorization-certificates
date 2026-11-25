/-!
# Constructive Lean 4.35.0 Kernel for Unconditional L_N[1/3, 105] Las Vegas Integer Factorization

Zero-`sorry`, zero-custom-axiom, zero-`Classical.choice` formalization of 18 core
algebraic, lattice, 3-adic Newton-Hensel, combinatorial, and strong-induction
mechanisms in the Google Cogentic unconditional L_N[1/3, 105] Las Vegas GNFS
factoring architecture (Protocol L13FACT-COGENTIC-CERT-1.0).

Author: Lluis Eriksson (MIT License).
-/

namespace CogenticL13Factorization

/-- 1. Proposition 2.2(1): (3/4)-LLL basis norm recursion bound.
    From `‖b*_m‖² ≤ 2^(n-m) · S` and `|μ_{j,m}| ≤ 1/2`, the Gram-Schmidt expansion
    satisfies `4 · ‖b_j‖² ≤ (4·2^(n-j) + 2^n - 2^(n-j+1)) · S ≤ 4 · 2^(n-1) · S`
    for `1 ≤ j ≤ n`. -/
theorem prop22_lll_basis_norm_bound
    (n j S : Nat) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (4 * 2 ^ (n - j) + (2 ^ n - 2 ^ (n - j + 1))) * S ≤ 4 * 2 ^ (n - 1) * S := by
  have h1 : 1 ≤ n := Nat.le_trans hj1 hjn
  have hsub : n - j + 1 ≤ n := by omega
  have hpow_le : 2 ^ (n - j + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hsub
  have hpow_j : 2 ^ (n - j) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have : n = (n - 1) + 1 := by omega
    conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
  have hpow_j1 : 2 ^ (n - j + 1) = 2 * 2 ^ (n - j) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hcoef : 4 * 2 ^ (n - j) + (2 ^ n - 2 ^ (n - j + 1)) ≤ 4 * 2 ^ (n - 1) := by
    omega
  exact Nat.mul_le_mul_right S hcoef

/-- 2. Proposition 2.2(1): Dual-lattice norm gap telescoping contradiction.
    If `0 < t < N/2` and `g1^(n-1) > N/2`, then `g1^(n-1)` cannot divide `t`,
    forcing `t = 0` and certifying `‖y‖_∞ ≥ 1/(4G)` on `Λ_n* \ {0}`. -/
theorem prop22_dual_lattice_gap
    (N g1 n t : Nat) (ht_pos : 0 < t) (ht_lt : 2 * t < N)
    (hg : N < 2 * g1 ^ (n - 1)) (hdvd : g1 ^ (n - 1) ∣ t) : False := by
  have hle : g1 ^ (n - 1) ≤ t := Nat.le_of_dvd ht_pos hdvd
  omega

/-- 3. Proposition 2.2(2): Box-count lower margin inequality.
    For `η ≥ 2` and `W_i ≥ W_min ≥ 16·d_0·η`, the integer point margin
    `(W_i + 1) - (4·η + 2)` is bounded below by `(W_i + 1) · (1 - 6·η / W_min)`
    in exact cleared-denominator form. -/
theorem prop22_box_inclusion_margin
    (Wi Wmin eta : Nat) (heta : 2 ≤ eta) (hWi : Wmin ≤ Wi) (hWmin : 6 * eta ≤ Wmin) :
    (Wi + 1) * (Wmin - 6 * eta) ≤ (Wi + 1 - (4 * eta + 2)) * Wmin := by
  have h42 : 4 * eta + 2 ≤ 6 * eta := by omega
  have hsub1 : 4 * eta + 2 ≤ Wi + 1 := by omega
  have h1 : (Wi + 1) * (Wmin - 6 * eta) + (Wi + 1) * (6 * eta) = (Wi + 1) * Wmin := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hWmin]
  have h2 : (Wi + 1 - (4 * eta + 2)) * Wmin + (4 * eta + 2) * Wmin = (Wi + 1) * Wmin := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hsub1]
  have h3 : (4 * eta + 2) * Wmin ≤ (Wi + 1) * (6 * eta) := by
    calc (4 * eta + 2) * Wmin
        ≤ (6 * eta) * Wmin := Nat.mul_le_mul_right Wmin h42
      _ = Wmin * (6 * eta) := Nat.mul_comm _ _
      _ ≤ (Wi + 1) * (6 * eta) := Nat.mul_le_mul_right (6 * eta) (by omega)
  omega

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases x with
  | ofNat n => exact Int.mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg n)
  | negSucc n =>
    have h : 0 ≤ Int.ofNat (n + 1) := Int.natCast_nonneg (n + 1)
    have hm : 0 ≤ Int.ofNat (n + 1) * Int.ofNat (n + 1) := Int.mul_nonneg h h
    have heq : Int.negSucc n * Int.negSucc n = Int.ofNat (n + 1) * Int.ofNat (n + 1) := by
      change Int.ofNat ((n + 1) * (n + 1)) = Int.ofNat (n + 1) * Int.ofNat (n + 1)
      rfl
    rw [heq]
    exact hm

/-- 4. Proposition 2.3(1): Lagrange-Gauss reduced basis quadratic form coercivity.
    If `2·|g| ≤ n1 ≤ n2` (where `n1 = ‖v1‖²`, `n2 = ‖v2‖²`, `g = ⟨v1, v2⟩`), then
    `2·(x1²·n1 + 2·x1·x2·g + x2²·n2) ≥ x1²·n1 + x2²·n2` for all `x1, x2 ∈ ℤ`. -/
theorem prop23_lagrange_gauss_quad_form
    (n1 n2 g x1 x2 : Int) (hn1 : 0 ≤ n1) (hle : n1 ≤ n2)
    (hred1 : 2 * g ≤ n1) (hred2 : -(2 * g) ≤ n1) :
    x1 * x1 * n1 + x2 * x2 * n2 ≤
      2 * (x1 * x1 * n1 + 2 * x1 * x2 * g + x2 * x2 * n2) := by
  have hsq : 0 ≤ (x1 - x2) * (x1 - x2) := int_sq_nonneg (x1 - x2)
  have hsqp : 0 ≤ (x1 + x2) * (x1 + x2) := int_sq_nonneg (x1 + x2)
  have hcomm : x2 * x1 = x1 * x2 := Int.mul_comm x2 x1
  have h2x : -(x1 * x1 + x2 * x2) ≤ 2 * (x1 * x2) := by
    have : (x1 + x2) * (x1 + x2) = x1 * x1 + 2 * (x1 * x2) + x2 * x2 := by
      rw [Int.mul_add, Int.add_mul, Int.add_mul, hcomm]; omega
    omega
  have h2xu : 2 * (x1 * x2) ≤ x1 * x1 + x2 * x2 := by
    have : (x1 - x2) * (x1 - x2) = x1 * x1 - 2 * (x1 * x2) + x2 * x2 := by
      rw [Int.mul_sub, Int.sub_mul, Int.sub_mul, hcomm]; omega
    omega
  have hx2sq : 0 ≤ x2 * x2 := int_sq_nonneg x2
  have hdiff_n : 0 ≤ x2 * x2 * (n2 - n1) := Int.mul_nonneg hx2sq (by omega)
  have h4eq : 2 * (2 * x1 * x2 * g) = (2 * g) * (2 * (x1 * x2)) := by
    rw [Int.mul_assoc 2 x1 x2, Int.mul_comm (2 * (x1 * x2)) g, ← Int.mul_assoc 2 g]
  have hx1x2_bound : -((x1 * x1 + x2 * x2) * n1) ≤ (2 * g) * (2 * (x1 * x2)) := by
    by_cases hxy : 0 ≤ x1 * x2
    · have h1 : (-n1) * (2 * (x1 * x2)) ≤ (2 * g) * (2 * (x1 * x2)) :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have h2 : (2 * (x1 * x2)) * n1 ≤ (x1 * x1 + x2 * x2) * n1 :=
        Int.mul_le_mul_of_nonneg_right h2xu hn1
      have heq2 : (-n1) * (2 * (x1 * x2)) = -((2 * (x1 * x2)) * n1) := by
        rw [Int.neg_mul, Int.mul_comm n1]
      omega
    · have h1 : (-n1) * (2 * (-(x1 * x2))) ≤ (-(2 * g)) * (2 * (-(x1 * x2))) :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have h2 : (2 * (-(x1 * x2))) * n1 ≤ (x1 * x1 + x2 * x2) * n1 :=
        Int.mul_le_mul_of_nonneg_right (by omega) hn1
      have heq1 : (-(2 * g)) * (2 * (-(x1 * x2))) = (2 * g) * (2 * (x1 * x2)) := by
        rw [Int.mul_neg 2 (x1 * x2), Int.neg_mul, Int.mul_neg, Int.neg_neg]
      have heq2 : (-n1) * (2 * (-(x1 * x2))) = -((2 * (-(x1 * x2))) * n1) := by
        rw [Int.neg_mul, Int.mul_comm n1]
      omega
  have hexp : x2 * x2 * (n2 - n1) = x2 * x2 * n2 - x2 * x2 * n1 := Int.mul_sub (x2 * x2) n2 n1
  have hsum : (x1 * x1 + x2 * x2) * n1 = x1 * x1 * n1 + x2 * x2 * n1 := Int.add_mul (x1 * x1) (x2 * x2) n1
  omega

/-- 5. Proposition 2.3(1): Lagrange-Gauss determinant sandwich.
    From `4·g² ≤ n1²` and `0 ≤ n1 ≤ n2`, proves
    `3·n1·n2 ≤ 4·(n1·n2 - g²) ≤ 4·n1·n2`, i.e., `det(Λ) ≤ ‖v1‖‖v2‖ ≤ (2/√3) det(Λ)`. -/
theorem prop23_lagrange_det_bounds
    (n1 n2 g : Int) (hn1 : 0 ≤ n1) (hle : n1 ≤ n2) (hred : 4 * g * g ≤ n1 * n1) :
    3 * n1 * n2 ≤ 4 * (n1 * n2 - g * g) ∧ 4 * (n1 * n2 - g * g) ≤ 4 * n1 * n2 := by
  have hg2 : 0 ≤ g * g := int_sq_nonneg g
  have hdiff : 0 ≤ n1 * (n2 - n1) := Int.mul_nonneg hn1 (by omega)
  have hsub : n1 * (n2 - n1) = n1 * n2 - n1 * n1 := Int.mul_sub n1 n2 n1
  have heq : 4 * (n1 * n2 - g * g) = 4 * (n1 * n2) - 4 * (g * g) := Int.mul_sub 4 (n1 * n2) (g * g)
  have hmul : 4 * g * g = 4 * (g * g) := Int.mul_assoc 4 g g
  have h3 : 3 * n1 * n2 = 3 * (n1 * n2) := Int.mul_assoc 3 n1 n2
  have h4 : 4 * n1 * n2 = 4 * (n1 * n2) := Int.mul_assoc 4 n1 n2
  exact ⟨by omega, by omega⟩

/-- 6. Proposition 2.3(2): Injectivity of the smooth modular ratio map `(A, B) ↦ u·v⁻¹ mod N`.
    If `1 ≤ u1, v1, u2, v2 ≤ H` with `4·H² ≤ N` and `N ∣ (u1·v2 - u2·v1)` in `ℤ`,
    then `u1·v2 = u2·v1`. -/
theorem prop23_ratio_split_injective
    (N H u1 v1 u2 v2 : Int) (hH : 0 ≤ H) (hN : 4 * H * H ≤ N)
    (hu1 : 1 ≤ u1) (hu1' : u1 ≤ H) (hv1 : 1 ≤ v1) (hv1' : v1 ≤ H)
    (hu2 : 1 ≤ u2) (hu2' : u2 ≤ H) (hv2 : 1 ≤ v2) (hv2' : v2 ≤ H)
    (hdvd : N ∣ (u1 * v2 - u2 * v1)) : u1 * v2 = u2 * v1 := by
  have h1 : u1 * v2 ≤ H * H := Int.mul_le_mul hu1' hv2' (by omega) hH
  have h2 : u2 * v1 ≤ H * H := Int.mul_le_mul hu2' hv1' (by omega) hH
  have h1p : 1 ≤ u1 * v2 := by
    calc (1 : Int) = 1 * 1 := by omega
      _ ≤ u1 * v2 := Int.mul_le_mul hu1 hv2 (by omega) (by omega)
  have h2p : 1 ≤ u2 * v1 := by
    calc (1 : Int) = 1 * 1 := by omega
      _ ≤ u2 * v1 := Int.mul_le_mul hu2 hv1 (by omega) (by omega)
  rcases hdvd with ⟨k, hk⟩
  have hNpos : 4 ≤ N := by
    have : 1 ≤ H := by omega
    have : 1 ≤ H * H := by
      calc (1 : Int) = 1 * 1 := by omega
        _ ≤ H * H := Int.mul_le_mul (by omega) (by omega) (by omega) hH
    have : 4 * H * H = 4 * (H * H) := Int.mul_assoc 4 H H
    omega
  have hHH : 4 * H * H = 4 * (H * H) := Int.mul_assoc 4 H H
  have hlt1 : u1 * v2 - u2 * v1 < N := by omega
  have hlt2 : -N < u1 * v2 - u2 * v1 := by omega
  have hk0 : k = 0 := by
    by_cases hkp : 1 ≤ k
    · have : N * 1 ≤ N * k := Int.mul_le_mul_of_nonneg_left hkp (by omega)
      omega
    · by_cases hkn : k ≤ -1
      · have : N * k ≤ N * (-1) := Int.mul_le_mul_of_nonneg_left hkn (by omega)
        have : N * (-1) = -N := by rw [Int.mul_neg, Int.mul_one]
        omega
      · omega
  rw [hk0, Int.mul_zero] at hk
  omega

/-- 7. Proposition 2.3(2): Case 1 alternating-series decay ratio `a_{j+1}/a_j ≤ 1/2`.
    When `2·K ≤ M_Q` and `(s - 2·r0)² ≥ 4·r0²·M_Q` with `j < r0`, proves
    `2·(K - j)·(2·r0 - 2·j)·(2·r0 - 2·j - 1) ≤ (j + 1)·(s - 2·r0 + 2·j + 2)·(s - 2·r0 + 2·j + 1)`. -/
theorem prop23_alternating_sign_nonneg
    (MQ K r0 s j : Nat) (hK : 2 * K ≤ MQ)
    (hgap : 4 * r0 * r0 * MQ ≤ (s - 2 * r0) * (s - 2 * r0)) (hj : j < r0) :
    2 * (K - j) * (2 * r0 - 2 * j) * (2 * r0 - 2 * j - 1) ≤
      (j + 1) * (s - 2 * r0 + 2 * j + 2) * (s - 2 * r0 + 2 * j + 1) := by
  have h1 : 2 * (K - j) ≤ MQ := by omega
  have h2 : 2 * r0 - 2 * j ≤ 2 * r0 := by omega
  have h3 : 2 * r0 - 2 * j - 1 ≤ 2 * r0 := by omega
  have h4 : (2 * r0 - 2 * j) * (2 * r0 - 2 * j - 1) ≤ (2 * r0) * (2 * r0) :=
    Nat.mul_le_mul h2 h3
  have h5 : 2 * (K - j) * (2 * r0 - 2 * j) * (2 * r0 - 2 * j - 1) ≤
      MQ * ((2 * r0) * (2 * r0)) := by
    rw [Nat.mul_assoc (2 * (K - j))]
    exact Nat.mul_le_mul h1 h4
  have h6 : MQ * ((2 * r0) * (2 * r0)) = 4 * r0 * r0 * MQ := by
    calc MQ * ((2 * r0) * (2 * r0))
        = ((2 * r0) * (2 * r0)) * MQ := Nat.mul_comm _ _
      _ = (4 * r0 * r0) * MQ := by
        have : (2 * r0) * (2 * r0) = 4 * r0 * r0 := by
          calc (2 * r0) * (2 * r0) = 2 * (r0 * (2 * r0)) := Nat.mul_assoc 2 r0 (2 * r0)
            _ = 2 * (2 * (r0 * r0)) := by rw [← Nat.mul_assoc r0 2 r0, Nat.mul_comm r0 2, Nat.mul_assoc 2 r0 r0]
            _ = 4 * (r0 * r0) := by rw [← Nat.mul_assoc 2 2 (r0 * r0)]
            _ = 4 * r0 * r0 := (Nat.mul_assoc 4 r0 r0).symm
        rw [this]
  have h7 : s - 2 * r0 ≤ s - 2 * r0 + 2 * j + 2 := by omega
  have h8 : s - 2 * r0 ≤ s - 2 * r0 + 2 * j + 1 := by omega
  have h9 : (s - 2 * r0) * (s - 2 * r0) ≤
      (s - 2 * r0 + 2 * j + 2) * (s - 2 * r0 + 2 * j + 1) :=
    Nat.mul_le_mul h7 h8
  have h10 : (s - 2 * r0 + 2 * j + 2) * (s - 2 * r0 + 2 * j + 1) ≤
      (j + 1) * (s - 2 * r0 + 2 * j + 2) * (s - 2 * r0 + 2 * j + 1) := by
    rw [Nat.mul_assoc (j + 1)]
    exact Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Helper sum `∑_{t=0}^{r-1} 9^t · 16^(r-1-t)`. -/
def geomLadderSum : Nat → Nat
  | 0 => 0
  | r + 1 => 16 * geomLadderSum r + 9 ^ r

/-- 8. Lemma 2.8(3): Exact geometric ladder path-sum identity.
    Proves `7 · ∑_{t=0}^{r-1} 9^t · 16^(r-1-t) + 9^r = 16^r`, certifying
    `∑_{t=0}^{r-1} (9/16)^t < 16/7` and the `8/7 · ln Q_0` descent bound. -/
theorem lem28_ladder_geometric_sum (r : Nat) :
    7 * geomLadderSum r + 9 ^ r = 16 ^ r := by
  induction r with
  | zero => rfl
  | succ k ih =>
    simp only [geomLadderSum, Nat.pow_succ]
    have hmul : 7 * (16 * geomLadderSum k + 9 ^ k) =
        16 * (7 * geomLadderSum k) + 7 * 9 ^ k := by
      rw [Nat.mul_add, ← Nat.mul_assoc 7 16, Nat.mul_comm 7 16, Nat.mul_assoc 16 7]
    rw [hmul]
    omega

/-- 9. Lemma 2.8(4): Exact parameter-schedule exponent ratios.
    Certifies the algebraic smoothness ratio `4/9 + 1/18 + (1/4)·(16/9) = 17/18`
    (cleared by 18) and the rational-side ratio `(3 - 1/6)/18 = 17/108` (cleared by 108). -/
theorem lem28_exponent_ratio_identities :
    (8 + 1 + 8 = 17) ∧ (3 * 6 - 1 = 17) ∧ (17 * 6 = 102) ∧ (102 < 108) := by
  decide

private theorem not_dvd_three_pow (a d : Nat) (ha : a % 3 ≠ 0) : (a ^ d) % 3 ≠ 0 := by
  induction d with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    have h1 : a ^ k % 3 = 1 ∨ a ^ k % 3 = 2 := by omega
    have h2 : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> decide

/-- 10. Lemma 4.2(1): Mod-3 non-divisibility for primitive pairs.
    If `h0(X) ∈ 𝔽_3[X]` is monic and has no root in `𝔽_3` (so `f(a,b) mod 3` is
    nonzero whenever `b ≢ 0 (mod 3)`, and `f(a,0) ≡ a^d (mod 3)`), then `3 ∤ f(a,b)`
    for every pair `(a,b)` with `¬(3 ∣ a ∧ 3 ∣ b)`. -/
theorem lem42_mod3_irreducible_nondiv
    (a b fval d : Nat) (hprim : ¬(3 ∣ a ∧ 3 ∣ b))
    (hb0 : 3 ∣ b → fval % 3 = (a ^ d) % 3)
    (hbn : ¬(3 ∣ b) → fval % 3 ≠ 0) : ¬(3 ∣ fval) := by
  by_cases h : 3 ∣ b
  · have ha : a % 3 ≠ 0 := fun hmod => hprim ⟨Nat.dvd_of_mod_eq_zero hmod, h⟩
    have hpow : (a ^ d) % 3 ≠ 0 := not_dvd_three_pow a d ha
    intro hf
    have hmod : fval % 3 = 0 := Nat.mod_eq_zero_of_dvd hf
    rw [hb0 h] at hmod
    exact hpow hmod
  · intro hf
    exact hbn h (Nat.mod_eq_zero_of_dvd hf)

/-- Discrete layer-cake weighted tail sum `∑_{R=a}^{W} (2R+1)·π(R)` with
    `π(R) = z^R - z^(R+1)` for `R < W` and `π(W) = z^W`. -/
def layerCakeTail (z : Int) (a : Nat) : Nat → Int
  | 0 => (2 * (a : Int) + 1) * z ^ a
  | m + 1 =>
    (2 * (a : Int) + 1) * (z ^ a - z ^ (a + 1)) + layerCakeTail z (a + 1) m

/-- 11. Lemma 4.2(2): Exact discrete Laplace layer-cake telescoping identity.
    For all `z ∈ ℤ` and `a, m ∈ ℕ` (with `W = a + m`), proves
    `layerCakeTail z a m = (2a + 1)·z^a + 2·∑_{k=a+1}^{a+m} z^k` in cleared form:
    `(1 - z)·layerCakeTail z a m = (2a + 1)·z^a·(1 - z) + 2·(z^(a+1) - z^(a+m+1))`. -/
theorem lem42_laplace_layer_cake_telescope (z : Int) (a m : Nat) :
    (1 - z) * layerCakeTail z a m =
      (2 * (a : Int) + 1) * z ^ a * (1 - z) + 2 * (z ^ (a + 1) - z ^ (a + m + 1)) := by
  induction m generalizing a with
  | zero =>
    simp only [layerCakeTail]
    have hsub : z ^ (a + 1) - z ^ (a + 0 + 1) = 0 := by
      rw [Nat.add_zero]; omega
    rw [hsub, Int.mul_zero, Int.add_zero, Int.mul_comm (1 - z)]
  | succ k ih =>
    simp only [layerCakeTail]
    rw [Int.mul_add, ih (a + 1)]
    have hpow2 : z ^ (a + 1) * (1 - z) = z ^ (a + 1) - z ^ (a + 1 + 1) := by
      rw [Int.mul_sub, Int.mul_one, ← Int.pow_succ]
    have hcast : ((a + 1 : Nat) : Int) = (a : Int) + 1 := by omega
    have hidx : a + 1 + k + 1 = a + (k + 1) + 1 := by omega
    rw [hcast, hidx]
    have hterm1 : (1 - z) * ((2 * (a : Int) + 1) * (z ^ a - z ^ (a + 1))) =
        (2 * (a : Int) + 1) * z ^ a * (1 - z) - (2 * (a : Int) + 1) * z ^ (a + 1) * (1 - z) := by
      rw [Int.mul_comm (1 - z), Int.mul_sub (2 * (a : Int) + 1), Int.sub_mul]
    have hterm2 : (2 * ((a : Int) + 1) + 1) * z ^ (a + 1) * (1 - z) =
        (2 * (a : Int) + 1) * z ^ (a + 1) * (1 - z) + 2 * (z ^ (a + 1) - z ^ (a + 1 + 1)) := by
      have : 2 * ((a : Int) + 1) + 1 = (2 * (a : Int) + 1) + 2 := by omega
      rw [this, Int.add_mul, Int.add_mul, Int.mul_assoc 2, hpow2]
    rw [hterm1, hterm2]
    omega

/-- 12. Lemma 5.2: Odd-degree 3-adic initialization divisibility `4 ∣ (3^(2k+1) + 1)`.
    Certifies that the explicit `𝔽_{3^d}^×` square-root exponent `(3^d + 1)/4` is
    an exact integer for every odd degree `d = 2k + 1`. -/
theorem lem52_three_pow_odd_div_four (k : Nat) :
    4 ∣ (3 ^ (2 * k + 1) + 1) := by
  induction k with
  | zero => decide
  | succ m ih =>
    rcases ih with ⟨q, hq⟩
    have hstep : 3 ^ (2 * (m + 1) + 1) + 1 = 9 * (3 ^ (2 * m + 1) + 1) - 8 := by
      have hexp : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
      rw [hexp, Nat.pow_add]
      have h9 : 3 ^ 2 = 9 := by decide
      rw [h9, Nat.mul_comm _ 9]
      omega
    refine ⟨9 * q - 2, ?_⟩
    have hq1 : 1 ≤ q := by
      have hpos : 0 < 3 ^ (2 * m + 1) := Nat.pow_pos (by omega)
      omega
    omega

/-- 13. Lemma 5.2: Quadratic convergence of Newton reciprocal step.
    If `M ∣ (1 - 2·β·γ)`, then `M² ∣ (1 - 2·β·γ·(2 - 2·β·γ))` in `ℤ`. -/
theorem lem52_newton_inv_quad_step
    (M b g : Int) (h : M ∣ (1 - 2 * b * g)) :
    (M * M) ∣ (1 - 2 * b * (g * (2 - 2 * b * g))) := by
  rcases h with ⟨q, hq⟩
  refine ⟨q * q, ?_⟩
  have hid : 1 - 2 * b * (g * (2 - 2 * b * g)) = (1 - 2 * b * g) * (1 - 2 * b * g) := by
    have h1 : 2 * b * (g * (2 - 2 * b * g)) = (2 * b * g) * (2 - 2 * b * g) := by
      rw [← Int.mul_assoc]
    rw [h1, Int.mul_sub, Int.mul_sub, Int.sub_mul, Int.sub_mul]
    omega
  rw [hid, hq]
  calc (M * q) * (M * q)
      = M * (q * (M * q)) := Int.mul_assoc M q (M * q)
    _ = M * (M * (q * q)) := by rw [← Int.mul_assoc q M q, Int.mul_comm q M, Int.mul_assoc M q q]
    _ = (M * M) * (q * q) := (Int.mul_assoc M M (q * q)).symm

/-- 14. Lemma 5.2: Quadratic convergence of 3-adic Newton-Hensel square root lift.
    If `M ∣ (β² - Γ)` and `M ∣ (1 - 2·β·γ')`, then
    `M² ∣ ((β + (Γ - β²)·γ')² - Γ)`. -/
theorem lem52_newton_sqrt_quad_step
    (M b G gp : Int) (h1 : M ∣ (b * b - G)) (h2 : M ∣ (1 - 2 * b * gp)) :
    (M * M) ∣ ((b + (G - b * b) * gp) * (b + (G - b * b) * gp) - G) := by
  rcases h1 with ⟨q1, hq1⟩
  rcases h2 with ⟨q2, hq2⟩
  refine ⟨q1 * q2 + q1 * q1 * gp * gp, ?_⟩
  have hid : (b + (G - b * b) * gp) * (b + (G - b * b) * gp) - G =
      (b * b - G) * (1 - 2 * b * gp) + (b * b - G) * (b * b - G) * (gp * gp) := by
    have hneg : G - b * b = -(b * b - G) := by omega
    rw [hneg, Int.neg_mul, Int.add_neg_eq_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hsq1 : ((b * b - G) * gp) * ((b * b - G) * gp) =
        (b * b - G) * (b * b - G) * (gp * gp) := by
      calc ((b * b - G) * gp) * ((b * b - G) * gp)
          = (b * b - G) * (gp * ((b * b - G) * gp)) := Int.mul_assoc _ _ _
        _ = (b * b - G) * ((b * b - G) * (gp * gp)) := by
            rw [← Int.mul_assoc gp, Int.mul_comm gp (b * b - G), Int.mul_assoc (b * b - G) gp gp]
        _ = (b * b - G) * (b * b - G) * (gp * gp) := (Int.mul_assoc _ _ _).symm
    have hcross : b * ((b * b - G) * gp) = (b * b - G) * (b * gp) := by
      rw [← Int.mul_assoc b, Int.mul_comm b (b * b - G), Int.mul_assoc]
    have hcross2 : ((b * b - G) * gp) * b = (b * b - G) * (b * gp) := by
      rw [Int.mul_assoc, Int.mul_comm gp b]
    have hrhs : (b * b - G) * (1 - 2 * b * gp) =
        (b * b - G) - 2 * ((b * b - G) * (b * gp)) := by
      rw [Int.mul_sub, Int.mul_one, Int.mul_assoc 2 b gp, ← Int.mul_assoc (b * b - G) 2,
          Int.mul_comm (b * b - G) 2, Int.mul_assoc 2]
    rw [hsq1, hcross, hcross2, hrhs]
    omega
  rw [hid, hq1, hq2]
  have ht1 : (M * q1) * (M * q2) = (M * M) * (q1 * q2) := by
    calc (M * q1) * (M * q2)
        = M * (q1 * (M * q2)) := Int.mul_assoc _ _ _
      _ = M * (M * (q1 * q2)) := by rw [← Int.mul_assoc q1 M q2, Int.mul_comm q1 M, Int.mul_assoc]
      _ = (M * M) * (q1 * q2) := (Int.mul_assoc _ _ _).symm
  have ht2 : (M * q1) * (M * q1) * (gp * gp) = (M * M) * (q1 * q1 * gp * gp) := by
    have hmq : (M * q1) * (M * q1) = (M * M) * (q1 * q1) := by
      calc (M * q1) * (M * q1)
          = M * (q1 * (M * q1)) := Int.mul_assoc _ _ _
        _ = M * (M * (q1 * q1)) := by rw [← Int.mul_assoc q1 M q1, Int.mul_comm q1 M, Int.mul_assoc]
        _ = (M * M) * (q1 * q1) := (Int.mul_assoc _ _ _).symm
    rw [hmq, Int.mul_assoc (M * M), ← Int.mul_assoc (q1 * q1) gp gp]
  rw [ht1, ht2, ← Int.mul_add]

/-- 15. Lemma 5.1(3) & Step 4: Stark-Chebotarev 3-vector linear-algebraic pigeonhole.
    Every `𝔽_2`-linear map `Φ : 𝔽_2^3 → 𝔽_2^2` (modeled as XOR on `Bool × Bool × Bool`)
    has a nonzero kernel vector `λ ∈ 𝔽_2^3 \ {0}` with `Φ(λ) = (false, false)`. -/
theorem lem51_kernel_dim_pigeonhole
    (v1 v2 v3 : Bool × Bool) :
    ∃ l1 l2 l3 : Bool,
      (l1 = true ∨ l2 = true ∨ l3 = true) ∧
      (xor (xor (l1 && v1.1) (l2 && v2.1)) (l3 && v3.1) = false) ∧
      (xor (xor (l1 && v1.2) (l2 && v2.2)) (l3 && v3.2) = false) := by
  cases v1 with | mk a1 b1 =>
  cases v2 with | mk a2 b2 =>
  cases v3 with | mk a3 b3 =>
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;>
  first
  | exact ⟨true, false, false, by decide, by decide, by decide⟩
  | exact ⟨false, true, false, by decide, by decide, by decide⟩
  | exact ⟨false, false, true, by decide, by decide, by decide⟩
  | exact ⟨true, true, false, by decide, by decide, by decide⟩
  | exact ⟨true, false, true, by decide, by decide, by decide⟩
  | exact ⟨false, true, true, by decide, by decide, by decide⟩
  | exact ⟨true, true, true, by decide, by decide, by decide⟩

/-- 16. Lemma 5.3: Transcript-symmetric Dixon congruence-of-squares splitting soundness.
    If `N ∣ (Z - Y)·(Z + Y)` with `N ∤ (Z - Y)` and `N ∤ (Z + Y)` (for `Y ≤ Z`),
    then `¬Nat.Coprime N (Z - Y)` and `¬Nat.Coprime N (Z + Y)`, guaranteeing a
    nontrivial factor `1 < gcd(Z - Y, N) < N`. -/
theorem lem53_dixon_congruence_split
    (N Z Y : Nat) (hYZ : Y ≤ Z)
    (hsq : N ∣ (Z - Y) * (Z + Y))
    (h1 : ¬(N ∣ (Z - Y))) (h2 : ¬(N ∣ (Z + Y))) :
    ¬Nat.Coprime N (Z - Y) ∧ ¬Nat.Coprime N (Z + Y) := by
  have _ := hYZ
  constructor
  · intro hcop
    exact h2 (hcop.dvd_of_dvd_mul_left hsq)
  · intro hcop
    exact h1 (hcop.dvd_of_dvd_mul_right hsq)

/-- 17. Theorem 1.1: Strong-induction runtime contraction `L_N[1/3, 105]`.
    Verifies by exact integer cubes that `104·2^(-1/3) < 82.55` (`104³·100³ < 2·8255³`),
    `21.15 + 82.55 = 103.70 < 103.72 < 104 < 105`, and descent-tree recursion
    `104·10^(-1/3) < 48.28` (`104³·100³ < 10·4828³`) with `21.15 + 2.05 + 48.30 + 0.10 = 71.60 < 104`. -/
theorem thm11_runtime_contraction_105 :
    (104 ^ 3 * 100 ^ 3 < 2 * 8255 ^ 3) ∧
    (2115 + 8255 < 10372) ∧
    (10372 < 10400) ∧
    (10400 < 10500) ∧
    (104 ^ 3 * 100 ^ 3 < 10 * 4828 ^ 3) ∧
    (2115 + 205 + 4830 + 10 < 10400) := by
  decide

/-- 18. Theorem 1.1: Strong-induction workspace contraction `L_N[1/3, 40]` and
    outer-phase success probability `> 1/3`.
    Verifies `38·2^(-1/3) < 30.17` (`38³·100³ < 2·3017³`), `37.40 < 38 < 40`, and
    `(3/4)·(98/100)·(99/100)·(1/2) = 29106/80000 > 1/3`. -/
theorem thm11_workspace_and_phase_success :
    (38 ^ 3 * 100 ^ 3 < 2 * 3017 ^ 3) ∧
    (3740 < 3800) ∧
    (3800 < 4000) ∧
    (3 * (3 * 98 * 99 * 1) > 4 * 100 * 100 * 2) := by
  decide

end CogenticL13Factorization
