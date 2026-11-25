import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions

/-!
# Sharp Perron truncation for twisted Chebyshev sums

At a half-integer cutoff, summing the reciprocal distance to nearby integers saves a
factor of the cutoff in the Perron truncation error. The bounds are uniform in the
Dirichlet character and also apply to the ordinary Chebyshev function.
-/

noncomputable section

open Finset MeasureTheory Set Filter Asymptotics Complex
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.PrimeDistribution

private lemma sum_inv_abs_halfInteger_le (N : ℕ) (hN : 2 ≤ N) :
    let x : ℝ := (N : ℝ) + 1 / 2
    ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ ≤ 4 * (1 + Real.log ((N : ℝ) + 1)) := by
  intro x
  have hsplit : Finset.Icc 1 (2 * N + 1) =
      Finset.Icc 1 N ∪ Finset.Icc (N + 1) (2 * N + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (2 * N + 1)) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hleft : ∑ n ∈ Finset.Icc 1 N, |x - (n : ℝ)|⁻¹ ≤ 2 * (1 + Real.log N) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, |x - (n : ℝ)|⁻¹ ≤
        ∑ n ∈ Finset.Icc 1 N, 2 * ((N + 1 - n : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := Finset.mem_Icc.mp hn
      have hpos : (0 : ℝ) < ((N + 1 - n : ℕ) : ℝ) / 2 := by
        have : 1 ≤ N + 1 - n := by omega
        positivity
      have hge : ((N + 1 - n : ℕ) : ℝ) / 2 ≤ |x - (n : ℝ)| := by
        have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn'.2
        have hcast : ((N + 1 - n : ℕ) : ℝ) = (N : ℝ) + 1 - (n : ℝ) := by
          have : n ≤ N + 1 := by omega
          rw [Nat.cast_sub this]; push_cast; ring
        rw [abs_of_pos (by dsimp [x]; linarith), hcast]
        dsimp [x]; linarith
      calc |x - (n : ℝ)|⁻¹ ≤ (((N + 1 - n : ℕ) : ℝ) / 2)⁻¹ :=
            inv_anti₀ hpos hge
        _ = 2 * ((N + 1 - n : ℕ) : ℝ)⁻¹ := by ring
    have hbij : ∑ n ∈ Finset.Icc 1 N, ((N + 1 - n : ℕ) : ℝ)⁻¹ =
        ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ := by
      refine Finset.sum_bij (fun n _ => N + 1 - n) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
      · intro n₁ hn₁ n₂ hn₂ heq; simp only [Finset.mem_Icc] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk
        exact ⟨N + 1 - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n _; rfl
    have hharm : ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ ≤ 1 + Real.log N := by
      simpa [Nat.floor_natCast] using sum_inv_le_one_add_log (x := (N : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N))
    rw [← Finset.mul_sum, hbij] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hharm zero_le_two)
  have hright : ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), |x - (n : ℝ)|⁻¹ ≤
      2 * (1 + Real.log ((N : ℝ) + 1)) := by
    have h1 : ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), |x - (n : ℝ)|⁻¹ ≤
        ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), 2 * ((n - N : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := Finset.mem_Icc.mp hn
      have hpos : (0 : ℝ) < ((n - N : ℕ) : ℝ) / 2 := by
        have : 1 ≤ n - N := by omega
        positivity
      have hge : ((n - N : ℕ) : ℝ) / 2 ≤ |x - (n : ℝ)| := by
        have hnR : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn'.1
        have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
          rw [Nat.cast_sub (by omega)]
        rw [abs_of_neg (by dsimp [x]; linarith), hcast]
        dsimp [x]; linarith
      calc |x - (n : ℝ)|⁻¹ ≤ (((n - N : ℕ) : ℝ) / 2)⁻¹ :=
            inv_anti₀ hpos hge
        _ = 2 * ((n - N : ℕ) : ℝ)⁻¹ := by ring
    have hbij : ∑ n ∈ Finset.Icc (N + 1) (2 * N + 1), ((n - N : ℕ) : ℝ)⁻¹ =
        ∑ k ∈ Finset.Icc 1 (N + 1), (k : ℝ)⁻¹ := by
      refine Finset.sum_bij (fun n _ => n - N) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
      · intro n₁ hn₁ n₂ hn₂ heq; simp only [Finset.mem_Icc] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk
        exact ⟨N + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n _; rfl
    have hharm : ∑ k ∈ Finset.Icc 1 (N + 1), (k : ℝ)⁻¹ ≤ 1 + Real.log ((N : ℝ) + 1) := by
      have h1 := sum_inv_le_one_add_log (x := ((N + 1 : ℕ) : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N + 1))
      rw [Nat.floor_natCast, Nat.cast_add, Nat.cast_one] at h1
      exact h1
    rw [← Finset.mul_sum, hbij] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hharm zero_le_two)
  have hlog_le : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by linarith)
  linarith

/-- At a half integer the truncated Perron integral for a character twist of the
von Mangoldt function has an error uniform in both the character and its modulus. -/
theorem perron_twist_halfInteger_error_le {q : ℕ} (χ : DirichletCharacter ℂ q) {N : ℕ} (hN : 2 ≤ N)
    {c T : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) (hT : 2 ≤ T) :
    let x : ℝ := (N : ℝ) + 1 / 2
    ‖dirichletContourIntegral (fun n : ℕ => χ n * (Λ n : ℂ)) x c T - psiChar x χ‖ ≤
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) +
        (64 / Real.pi) * (x * (Real.log (2 * x)) ^ 2 / T) := by
  intro x
  have hx_pos : 0 < x := by positivity
  have hc_pos : 0 < c := by linarith
  have hT_pos : 0 < T := by linarith
  have ha := LSeriesSummable_twist_vonMangoldt χ hc1
  have hex := perron_truncated_explicit hx_pos hc_pos hT_pos ha
  have hfl2 : ⌊2 * x⌋₊ = 2 * N + 1 := by
    have h2x : 2 * x = ((2 * N + 1 : ℕ) : ℝ) := by dsimp [x]; push_cast; ring
    rw [h2x, Nat.floor_natCast]
  have hx_nonint : ∀ n : ℕ, (n : ℝ) ≠ x := by
    intro n hn
    rcases le_or_gt n N with hle | hgt
    · have : (n : ℝ) ≤ N := by exact_mod_cast hle
      dsimp [x] at hn; linarith
    · have : (N + 1 : ℝ) ≤ n := by exact_mod_cast hgt
      dsimp [x] at hn; linarith
  have hhit0 : (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      if (n : ℝ) = x then ‖χ n * (Λ n : ℂ)‖ * (1 / 2 + c / (Real.pi * T)) else 0) = 0 :=
    Finset.sum_eq_zero fun n _ => ite_eq_right (hx_nonint n)
  have htsum_bd := tsum_norm_LSeries_term_twist_le χ hc1
  have hnear_bd : (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
        ‖χ n * (Λ n : ℂ)‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
      else 0) ≤ (64 / Real.pi) * (x * (Real.log (2 * x)) ^ 2 / T) := by
    rw [hfl2]
    have hlog2x_ge1 : 1 ≤ Real.log (2 * x) := by
      have h5 : (5 : ℝ) ≤ 2 * x := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        dsimp [x]; linarith
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    have hterm_le : ∑ n ∈ Finset.Icc 1 (2 * N + 1),
        (if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
          ‖χ n * (Λ n : ℂ)‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
        else 0) ≤
        (Real.log (2 * x) * (8 * x / (Real.pi * T))) *
          ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn_mem := Finset.mem_Icc.mp hn
      split_ifs with hcond
      · have hnorm_Λ : ‖χ n * (Λ n : ℂ)‖ ≤ Real.log (2 * x) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          apply (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one (n : ZMod q))).trans
          have hle_log : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_mem.1
          have hn_le2x : (n : ℝ) ≤ 2 * x := by
            have h2N : ((2 * N + 1 : ℕ) : ℝ) = 2 * x := by dsimp [x]; push_cast; ring
            rw [← h2N]; exact_mod_cast hn_mem.2
          exact hle_log.trans (Real.log_le_log hn_pos hn_le2x)
        have h2c : (2 : ℝ) ^ c ≤ 4 := by
          calc (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hc2
            _ = 4 := by norm_num
        have hmul_eq : 2 ^ c * (2 * x) / (Real.pi * T * |x - (n : ℝ)|) =
            (2 ^ c * (2 * x) / (Real.pi * T)) * |x - (n : ℝ)|⁻¹ := by ring
        rw [hmul_eq]
        have hpos_x : 0 ≤ 2 * x / (Real.pi * T) := by positivity
        have hpow_le : 2 ^ c * (2 * x) / (Real.pi * T) ≤ 8 * x / (Real.pi * T) := by
          calc 2 ^ c * (2 * x) / (Real.pi * T)
              ≤ 4 * (2 * x) / (Real.pi * T) := by gcongr
            _ = 8 * x / (Real.pi * T) := by ring
        calc ‖χ n * (Λ n : ℂ)‖ * ((2 ^ c * (2 * x) / (Real.pi * T)) * |x - (n : ℝ)|⁻¹)
            ≤ Real.log (2 * x) * ((8 * x / (Real.pi * T)) * |x - (n : ℝ)|⁻¹) := by gcongr
          _ = (Real.log (2 * x) * (8 * x / (Real.pi * T))) * |x - (n : ℝ)|⁻¹ := by ring
      · positivity
    have hsum_inv := sum_inv_abs_halfInteger_le N hN
    have h_N1_le : (N : ℝ) + 1 ≤ 2 * x := by dsimp [x]; linarith
    have h4_le : 4 * (1 + Real.log ((N : ℝ) + 1)) ≤ 8 * Real.log (2 * x) := by
      have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * x) :=
        Real.log_le_log (by positivity) h_N1_le
      linarith [hlog2x_ge1]
    calc (∑ n ∈ Finset.Icc 1 (2 * N + 1),
          if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
            ‖χ n * (Λ n : ℂ)‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
          else 0)
        ≤ (Real.log (2 * x) * (8 * x / (Real.pi * T))) *
            ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ := hterm_le
      _ ≤ (Real.log (2 * x) * (8 * x / (Real.pi * T))) * (8 * Real.log (2 * x)) := by
          dsimp only at hsum_inv
          exact mul_le_mul_of_nonneg_left (hsum_inv.trans h4_le) (by positivity)
      _ = (64 / Real.pi) * (x * (Real.log (2 * x)) ^ 2 / T) := by ring
  have hterm1 : (x ^ c / (Real.pi * T * Real.log 2)) *
        ∑' n : ℕ, ‖LSeries.term (fun k : ℕ => χ k * (Λ k : ℂ)) (c : ℂ) n‖ ≤
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc (x ^ c / (Real.pi * T * Real.log 2)) *
          ∑' n : ℕ, ‖LSeries.term (fun k : ℕ => χ k * (Λ k : ℂ)) (c : ℂ) n‖
        ≤ (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) := by gcongr
      _ = (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) := by
          have hc0 : c - 1 ≠ 0 := sub_ne_zero.mpr hc1.ne'
          field_simp [hT_pos.ne', hlog2_pos.ne', hc0]
  unfold psiChar
  linarith [hex, hhit0, hnear_bd, hterm1]

/-- The rectangular contour bound with the sharp half-integer truncation error. -/
theorem norm_psiChar_le_of_rect_zeroFree_sharp {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1)
    {N : ℕ} (hN : 2 ≤ N) {σ₀ c T B_vert B_horiz : ℝ} (hσ : 0 < σ₀) (hσc : σ₀ ≤ c) (hc : 1 < c)
    (hc2 : c ≤ 2) (hT : 2 ≤ T) (hB_vert : 0 ≤ B_vert) (hB_horiz : 0 ≤ B_horiz)
    (hnonzero : ∀ s ∈ Set.Icc σ₀ c ×ℂ Set.Icc (-T) T, DirichletCharacter.LFunction χ s ≠ 0)
    (hvert : ∀ t ∈ Set.Icc (-T) T,
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert)
    (htop : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (T : ℂ) * I) /
        DirichletCharacter.LFunction χ ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz)
    (hbot : ∀ u ∈ Set.Icc σ₀ c,
      ‖-deriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((-T : ℝ) : ℂ) * I) /
        DirichletCharacter.LFunction χ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz) :
    let x : ℝ := N + 1 / 2
    ‖psiChar x χ‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c +
        ((4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) +
          (64 / Real.pi) * (x * (Real.log (2 * x)) ^ 2 / T)) := by
  intro x
  have hx : 1 ≤ x := by dsimp [x]; linarith [show (2 : ℝ) ≤ N by exact_mod_cast hN]
  have hshift := norm_dirichletContourIntegral_twist_le hχ hx hσ hσc hc (by linarith : 0 < T)
    hB_vert hB_horiz hnonzero hvert htop hbot
  have herror := perron_twist_halfInteger_error_le χ hN hc hc2 hT
  dsimp only at herror
  let Iχ := dirichletContourIntegral (fun n : ℕ => χ n * (Λ n : ℂ)) x c T
  have htri := norm_sub_le Iχ (Iχ - psiChar x χ)
  rw [sub_sub_cancel] at htri
  exact htri.trans (add_le_add hshift herror)

private lemma rpow_sqrt_log_mul_exp_neg_le {m : ℕ} {γ u : ℝ} (hγ : 0 < γ) (_hu : 1 ≤ u) :
    (Real.sqrt (Real.log u)) ^ m * Real.exp (-2 * γ * Real.sqrt (Real.log u)) ≤
      ((m.factorial : ℝ) / γ ^ m) * Real.exp (-γ * Real.sqrt (Real.log u)) := by
  let y : ℝ := Real.sqrt (Real.log u)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hpow : (γ * y) ^ m / (m.factorial : ℝ) ≤ Real.exp (γ * y) := by
    have hexp := Real.sum_le_exp_of_nonneg (mul_nonneg hγ.le hy) (m + 1)
    have hsingle : (γ * y) ^ m / (m.factorial : ℝ) ≤
        ∑ k ∈ Finset.range (m + 1), (γ * y) ^ k / (k.factorial : ℝ) :=
      Finset.single_le_sum (fun k _ => div_nonneg (pow_nonneg (mul_nonneg hγ.le hy) k)
        (Nat.cast_nonneg _)) (Finset.mem_range.mpr (Nat.lt_succ_self m))
    exact hsingle.trans hexp
  have hy_bd : y ^ m ≤ ((m.factorial : ℝ) / γ ^ m) * Real.exp (γ * y) := by
    rw [mul_pow] at hpow
    rw [div_le_iff₀ (by positivity)] at hpow
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hγ m)]
    linarith
  calc y ^ m * Real.exp (-2 * γ * y)
      ≤ (((m.factorial : ℝ) / γ ^ m) * Real.exp (γ * y)) * Real.exp (-2 * γ * y) :=
        mul_le_mul_of_nonneg_right hy_bd (Real.exp_pos _).le
    _ = ((m.factorial : ℝ) / γ ^ m) * (Real.exp (γ * y) * Real.exp (-2 * γ * y)) := by ring
    _ = ((m.factorial : ℝ) / γ ^ m) * Real.exp (-γ * y) := by
        rw [← Real.exp_add]; congr 2; ring

/-- The explicit coefficient from the four truncated Perron errors. -/
def perronRectangleConstant (d D : ℝ) : ℝ :=
  let M₁ : ℝ := (Real.sqrt 2 / Real.pi) * (D * 8) * ((Nat.factorial 3 : ℝ) / (d/16) ^ 3)
  let M₂ : ℝ := ((2 : ℝ) / Real.pi) * (D * 4) * Real.exp 1 * ((Nat.factorial 2 : ℝ) / (d/16) ^ 2)
  let M₃ : ℝ := (4 / (Real.pi * Real.log 2)) * Real.exp 1 * ((Nat.factorial 4 : ℝ) / (d/16) ^ 4)
  let M₄ : ℝ := (64 / Real.pi) * 4 * ((Nat.factorial 4 : ℝ) / (d/16) ^ 4)
  M₁+M₂+M₃+M₄+1

theorem perronRectangleConstant_pos {d D : ℝ} (hd : 0<d) (hD : 0<D) :
    0<perronRectangleConstant d D := by
  unfold perronRectangleConstant
  positivity

/-- With contour height `exp (sqrt (log x))`, the shifted contour and the two
sharp Perron errors together admit an exponential saving in `sqrt (log x)`. -/
theorem perron_rectangle_error_le_explicit {d C_vert_k : ℝ} (hcZ_pos : 0 < d)
    (hcZ_le : d ≤ 1 / 8) (hCv_pos : 0 < C_vert_k) :
    ∀ x' : ℝ, Real.exp 16 ≤ x' →
      let sL := Real.sqrt (Real.log x')
      let T := Real.exp sL
      let c_line := 1 + 1 / Real.log x'
      let L_T := Real.log (T + 3)
      let σ₀ := 1 - d / L_T
      let B_bound := C_vert_k * L_T ^ 2
      ((Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀) +
            ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line) +
          ((4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2)) +
            (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T)) ≤
        perronRectangleConstant d C_vert_k * x' * Real.exp (-(d / 16) * sL) := by
  let c_pnt : ℝ := d / 16
  have hc_pnt_pos : 0 < c_pnt := by positivity
  have hc_pnt_le : c_pnt ≤ 1 / 128 := by dsimp [c_pnt]; linarith
  let X₀ : ℝ := Real.exp 16
  have hX₀_ge : 4 ≤ X₀ := by
    have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9]
    exact hexp2.trans (Real.exp_le_exp.mpr (by norm_num))
  let M₁ : ℝ := (Real.sqrt 2 / Real.pi) * (C_vert_k * 8) * ((Nat.factorial 3 : ℝ) / c_pnt ^ 3)
  let M₂ : ℝ := ((2 : ℝ) / Real.pi) * (C_vert_k * 4) * Real.exp 1 * ((Nat.factorial 2 : ℝ) / c_pnt ^ 2)
  let M₃ : ℝ := (4 / (Real.pi * Real.log 2)) * Real.exp 1 * ((Nat.factorial 4 : ℝ) / c_pnt ^ 4)
  let M₄ : ℝ := (64 / Real.pi) * 4 * ((Nat.factorial 4 : ℝ) / c_pnt ^ 4)
  intro x' hN_ge
  have hx'_ge4 : 4 ≤ x' := hX₀_ge.trans hN_ge
  have hx'_pos : 0 < x' := by linarith
  have hlog_ge16 : 16 ≤ Real.log x' := by
    rw [Real.le_log_iff_exp_le hx'_pos]
    exact hN_ge
  have hsqrt_ge4 : 4 ≤ Real.sqrt (Real.log x') := by
    rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  let sL : ℝ := Real.sqrt (Real.log x')
  have hsL_ge4 : 4 ≤ sL := hsqrt_ge4
  have hlog_eq_sq : Real.log x' = sL ^ 2 := (Real.sq_sqrt (by linarith)).symm
  let T : ℝ := Real.exp sL
  have hT_ge3 : 3 ≤ T := by
    have h1 : Real.exp 2 ≤ T := Real.exp_le_exp.mpr (by linarith)
    have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9]
    linarith
  have hT_pos : 0 < T := Real.exp_pos sL
  let c_line : ℝ := 1 + 1 / Real.log x'
  have hc1 : 1 < c_line := by
    dsimp [c_line]; linarith [one_div_pos.mpr (by linarith : 0 < Real.log x')]
  have hc2 : c_line ≤ 2 := by
    dsimp [c_line]
    have : 1 / Real.log x' ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    linarith
  let L_T : ℝ := Real.log (T + 3)
  have hLT_le : L_T ≤ 2 * sL := by
    have hT3 : T + 3 ≤ 2 * T := by linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
    calc L_T ≤ Real.log (2 * T) := Real.log_le_log (by positivity) hT3
      _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) hT_pos.ne'
      _ = Real.log 2 + sL := by dsimp [T]; rw [Real.log_exp]
      _ ≤ 2 * sL := by linarith
  have hLT_ge1 : 1 ≤ L_T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  let σ₀ : ℝ := 1 - d / L_T
  have hσ0_ge : 1 / 2 ≤ σ₀ := by
    have h1 : d / L_T ≤ 1 / 8 := (div_le_self hcZ_pos.le hLT_ge1).trans hcZ_le
    dsimp [σ₀]; linarith
  have hσ0_pos : 0 < σ₀ := by linarith
  have hσ0_lt1 : σ₀ < 1 := by dsimp [σ₀]; linarith [div_pos hcZ_pos (by linarith : 0 < L_T)]
  let B_bound : ℝ := C_vert_k * L_T ^ 2
  have hB_nn : 0 ≤ B_bound := by positivity
  have h_xc : x' ^ c_line = Real.exp 1 * x' := by
    dsimp [c_line]
    rw [Real.rpow_add hx'_pos, Real.rpow_one, Real.rpow_def_of_pos hx'_pos,
      mul_div_cancel₀ 1 (by linarith : Real.log x' ≠ 0)]
    ring
  have h_inv_T : T⁻¹ ≤ Real.exp (-2 * c_pnt * sL) := by
    dsimp [T]
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by nlinarith only [hc_pnt_le, hsL_ge4])
  have hB_le : B_bound ≤ 4 * C_vert_k * sL ^ 2 := by
    have hsq : L_T ^ 2 ≤ (2 * sL) ^ 2 := pow_le_pow_left₀ (by linarith) hLT_le 2
    calc B_bound = C_vert_k * L_T ^ 2 := rfl
      _ ≤ C_vert_k * (2 * sL) ^ 2 := mul_le_mul_of_nonneg_left hsq hCv_pos.le
      _ = 4 * C_vert_k * sL ^ 2 := by ring
  have h_term1 : (Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀) ≤
      M₁ * x' * Real.exp (-c_pnt * sL) := by
    have hlog_T : Real.log (1 + T / σ₀) ≤ 2 * sL := by
      have h1 : 1 + T / σ₀ ≤ 4 * T := by
        have hdiv : T / σ₀ ≤ 2 * T := by
          rw [div_le_iff₀ hσ0_pos]
          calc T = T * 1 := (mul_one T).symm
            _ ≤ T * (2 * σ₀) := mul_le_mul_of_nonneg_left (by linarith [hσ0_ge]) hT_pos.le
            _ = 2 * T * σ₀ := by ring
        linarith
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have hlog2 : Real.log 2 ≤ 1 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
        norm_num; linarith
      calc Real.log (1 + T / σ₀) ≤ Real.log (4 * T) := Real.log_le_log (by positivity) h1
        _ = Real.log 4 + Real.log T := Real.log_mul (by norm_num) hT_pos.ne'
        _ = Real.log 4 + sL := by dsimp [T]; rw [Real.log_exp]
        _ ≤ 2 * sL := by linarith
    have hxσ : x' ^ σ₀ ≤ x' * Real.exp (-2 * c_pnt * sL) := by
      rw [Real.rpow_def_of_pos hx'_pos]
      have heq : Real.log x' * σ₀ = Real.log x' - (d / L_T) * Real.log x' := by
        dsimp [σ₀]; ring
      rw [heq, Real.exp_sub, Real.exp_log hx'_pos, div_eq_mul_inv, ← Real.exp_neg]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx'_pos.le
      have hdiv : 2 * c_pnt * sL ≤ (d / L_T) * Real.log x' := by
        rw [hlog_eq_sq, div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < L_T)]
        have h8 : 2 * c_pnt * (2 * sL) ≤ d * sL := by
          calc 2 * c_pnt * (2 * sL) = (1 / 4 : ℝ) * (d * sL) := by dsimp [c_pnt]; ring
            _ ≤ 1 * (d * sL) := mul_le_mul_of_nonneg_right (by norm_num)
                (mul_nonneg hcZ_pos.le (by linarith))
            _ = d * sL := one_mul _
        calc 2 * c_pnt * sL * L_T ≤ 2 * c_pnt * sL * (2 * sL) :=
              mul_le_mul_of_nonneg_left hLT_le (by positivity)
          _ = (2 * c_pnt * (2 * sL)) * sL := by ring
          _ ≤ (d * sL) * sL := mul_le_mul_of_nonneg_right h8 (by linarith)
          _ = d * sL ^ 2 := by ring
      linarith
    have hrpow : sL ^ 3 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 3 : ℝ) / c_pnt ^ 3) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 3) hc_pnt_pos (by linarith : 1 ≤ x')
    have hlog_T_nn : 0 ≤ Real.log (1 + T / σ₀) :=
      Real.log_nonneg (by linarith [div_pos hT_pos hσ0_pos])
    have hfac1 : (Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ ≤
        (Real.sqrt 2 / Real.pi) * (4 * C_vert_k * sL ^ 2) * (x' * Real.exp (-2 * c_pnt * sL)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB_le (by positivity)) hxσ (by positivity) (by positivity)
    calc (Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀)
        ≤ ((Real.sqrt 2 / Real.pi) * (4 * C_vert_k * sL ^ 2) *
            (x' * Real.exp (-2 * c_pnt * sL))) * (2 * sL) :=
          mul_le_mul hfac1 hlog_T hlog_T_nn (by positivity)
      _ = (Real.sqrt 2 / Real.pi) * (C_vert_k * 8) * x' * (sL ^ 3 * Real.exp (-2 * c_pnt * sL)) := by ring
      _ ≤ (Real.sqrt 2 / Real.pi) * (C_vert_k * 8) * x' *
            (((Nat.factorial 3 : ℝ) / c_pnt ^ 3) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = M₁ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₁]; ring
  have h_term2 : ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line ≤
      M₂ * x' * Real.exp (-c_pnt * sL) := by
    have hc_diff : c_line - σ₀ ≤ 2 := by
      have h1 : 1 / Real.log x' ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      have h2 : d / L_T ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      dsimp [c_line, σ₀]; linarith
    have hrpow : sL ^ 2 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 2 : ℝ) / c_pnt ^ 2) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 2) hc_pnt_pos (by linarith : 1 ≤ x')
    have h_prefix : (c_line - σ₀) / Real.pi * B_bound ≤ 2 / Real.pi * (4 * C_vert_k * sL ^ 2) :=
      mul_le_mul (div_le_div_of_nonneg_right hc_diff Real.pi_pos.le) hB_le hB_nn (by positivity)
    calc ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line
        = (c_line - σ₀) / Real.pi * B_bound * (Real.exp 1 * x') * T⁻¹ := by rw [h_xc]; ring
      _ ≤ 2 / Real.pi * (4 * C_vert_k * sL ^ 2) * (Real.exp 1 * x') * Real.exp (-2 * c_pnt * sL) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h_prefix (by positivity)) h_inv_T (by positivity) (by positivity)
      _ = (2 / Real.pi) * (C_vert_k * 4) * Real.exp 1 * x' * (sL ^ 2 * Real.exp (-2 * c_pnt * sL)) := by ring
      _ ≤ (2 / Real.pi) * (C_vert_k * 4) * Real.exp 1 * x' *
            (((Nat.factorial 2 : ℝ) / c_pnt ^ 2) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = M₂ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₂]; ring
  have h_term3 : (4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2)) ≤
      M₃ * x' * Real.exp (-c_pnt * sL) := by
    have hc_sq : (c_line - 1) ^ 2 = (sL ^ 4)⁻¹ := by
      dsimp [c_line]; rw [add_sub_cancel_left, one_div, hlog_eq_sq, inv_pow, ← pow_mul]
    have hrpow : sL ^ 4 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 4) hc_pnt_pos (by linarith : 1 ≤ x')
    have h_eq : x' ^ c_line / (T * (c_line - 1) ^ 2) = Real.exp 1 * x' * sL ^ 4 * T⁻¹ := by
      rw [h_xc, hc_sq, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hcoeff3 : 0 ≤ (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' := by positivity
    calc (4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2))
        = (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' * (sL ^ 4 * T⁻¹) := by rw [h_eq]; ring
      _ ≤ (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' * (sL ^ 4 * Real.exp (-2 * c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_inv_T (by positivity)) hcoeff3
      _ ≤ (4 / (Real.pi * Real.log 2)) * Real.exp 1 * x' *
            (((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow hcoeff3
      _ = M₃ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₃]; ring
  have h_term4 : (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T) ≤
      M₄ * x' * Real.exp (-c_pnt * sL) := by
    have hlog2x_le : Real.log (2 * x') ≤ 2 * sL ^ 2 := by
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]; linarith only [Real.exp_one_gt_d9]
      have h1_sL : 1 ≤ sL ^ 2 := by nlinarith only [hsL_ge4]
      rw [Real.log_mul (by norm_num) hx'_pos.ne', hlog_eq_sq]
      linarith only [hlog2, h1_sL]
    have hsq2x : (Real.log (2 * x')) ^ 2 ≤ 4 * sL ^ 4 := by
      calc (Real.log (2 * x')) ^ 2 ≤ (2 * sL ^ 2) ^ 2 :=
            pow_le_pow_left₀ (Real.log_nonneg (by linarith only [hx'_ge4])) hlog2x_le 2
        _ = 4 * sL ^ 4 := by ring
    have hrpow : sL ^ 4 * Real.exp (-2 * c_pnt * sL) ≤
        ((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL) :=
      rpow_sqrt_log_mul_exp_neg_le (m := 4) hc_pnt_pos (by linarith : 1 ≤ x')
    have h_eq : x' * (Real.log (2 * x')) ^ 2 / T = x' * (Real.log (2 * x')) ^ 2 * T⁻¹ := by ring
    calc (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T)
        ≤ (64 / Real.pi) * (x' * (4 * sL ^ 4) * Real.exp (-2 * c_pnt * sL)) := by
          rw [h_eq]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul_of_nonneg_left hsq2x hx'_pos.le) h_inv_T (by positivity) (by positivity))
            (by positivity)
      _ = (64 / Real.pi) * 4 * x' * (sL ^ 4 * Real.exp (-2 * c_pnt * sL)) := by ring
      _ ≤ (64 / Real.pi) * 4 * x' * (((Nat.factorial 4 : ℝ) / c_pnt ^ 4) * Real.exp (-c_pnt * sL)) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = M₄ * x' * Real.exp (-c_pnt * sL) := by dsimp [M₄]; ring
  calc ((Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀) +
            ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line) +
          ((4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2)) +
            (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T))
      ≤ (M₁ * x' * Real.exp (-c_pnt * sL) + M₂ * x' * Real.exp (-c_pnt * sL)) +
          (M₃ * x' * Real.exp (-c_pnt * sL) + M₄ * x' * Real.exp (-c_pnt * sL)) :=
        add_le_add (add_le_add h_term1 h_term2) (add_le_add h_term3 h_term4)
    _ = (M₁ + M₂ + M₃ + M₄) * (x' * Real.exp (-c_pnt * sL)) := by ring
    _ ≤ (M₁ + M₂ + M₃ + M₄ + 1) * (x' * Real.exp (-c_pnt * sL)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
    _ = (M₁ + M₂ + M₃ + M₄ + 1) * x' * Real.exp (-c_pnt * sL) := by ring

/-- With contour height `exp (sqrt (log x))`, the shifted contour and the two
sharp Perron errors together admit an exponential saving in `sqrt (log x)`. -/
theorem perron_rectangle_error_le_exp {d C_vert_k : ℝ} (hcZ_pos : 0 < d)
    (hcZ_le : d ≤ 1 / 8) (hCv_pos : 0 < C_vert_k) :
    ∃ C > 0, ∀ x' : ℝ, Real.exp 16 ≤ x' →
      let sL := Real.sqrt (Real.log x')
      let T := Real.exp sL
      let c_line := 1 + 1 / Real.log x'
      let L_T := Real.log (T + 3)
      let σ₀ := 1 - d / L_T
      let B_bound := C_vert_k * L_T ^ 2
      ((Real.sqrt 2 / Real.pi) * B_bound * x' ^ σ₀ * Real.log (1 + T / σ₀) +
            ((c_line - σ₀) / (Real.pi * T)) * B_bound * x' ^ c_line) +
          ((4 / (Real.pi * Real.log 2)) * (x' ^ c_line / (T * (c_line - 1) ^ 2)) +
            (64 / Real.pi) * (x' * (Real.log (2 * x')) ^ 2 / T)) ≤
        C * x' * Real.exp (-(d / 16) * sL) :=
  ⟨_,perronRectangleConstant_pos hcZ_pos hCv_pos,
    perron_rectangle_error_le_explicit hcZ_pos hcZ_le hCv_pos⟩

end AnalyticNumberTheory.PrimeDistribution
