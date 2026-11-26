import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.DirichletSeries.Perron

/-! # Sharp truncation of Perron's formula at half-integers -/

noncomputable section

open Finset Complex
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.DirichletSeries

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

/-- At a half-integer cutoff the near terms in Perron's truncation error cost
only one logarithm times the largest coefficient up to twice the cutoff. -/
theorem perron_halfInteger_error_le {a : ℕ → ℂ} {N : ℕ} (hN : 2 ≤ N)
    {c T A : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) (hT : 2 ≤ T)
    (ha : LSeriesSummable a (c : ℂ)) (hA : 0 ≤ A)
    (hcoeff : ∀ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖ ≤ A) :
    let x : ℝ := (N : ℝ) + 1 / 2
    ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤
      (x ^ c / (Real.pi * T * Real.log 2)) * ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ +
      (64 / Real.pi) * (x * A * Real.log (2 * x) / T) := by
  intro x
  have hx_pos : 0 < x := by positivity
  have hc_pos : 0 < c := by linarith
  have hT_pos : 0 < T := by linarith
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
      if (n : ℝ) = x then ‖a n‖ * (1 / 2 + c / (Real.pi * T)) else 0) = 0 :=
    Finset.sum_eq_zero fun n _ => ite_eq_right (hx_nonint n)
  have hnear_bd : (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊,
      if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
        ‖a n‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
      else 0) ≤ (64 / Real.pi) * (x * A * Real.log (2 * x) / T) := by
    rw [hfl2]
    have hlog2x_ge1 : 1 ≤ Real.log (2 * x) := by
      have h5 : (5 : ℝ) ≤ 2 * x := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        dsimp [x]; linarith
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    have hterm_le : ∑ n ∈ Finset.Icc 1 (2 * N + 1),
        (if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
          ‖a n‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
        else 0) ≤
        (A * (8 * x / (Real.pi * T))) *
          ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      split_ifs with hcond
      · have hnA := hcoeff n hn
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
        calc ‖a n‖ * ((2 ^ c * (2 * x) / (Real.pi * T)) * |x - (n : ℝ)|⁻¹)
            ≤ A * ((8 * x / (Real.pi * T)) * |x - (n : ℝ)|⁻¹) := by gcongr
          _ = (A * (8 * x / (Real.pi * T))) * |x - (n : ℝ)|⁻¹ := by ring
      · positivity
    have hsum_inv := sum_inv_abs_halfInteger_le N hN
    have h_N1_le : (N : ℝ) + 1 ≤ 2 * x := by dsimp [x]; linarith
    have h4_le : 4 * (1 + Real.log ((N : ℝ) + 1)) ≤ 8 * Real.log (2 * x) := by
      have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * x) :=
        Real.log_le_log (by positivity) h_N1_le
      linarith [hlog2x_ge1]
    calc (∑ n ∈ Finset.Icc 1 (2 * N + 1),
          if x / 2 ≤ n ∧ (n : ℝ) ≠ x then
            ‖a n‖ * (2 ^ c * (2 * x) / (Real.pi * T * |x - n|))
          else 0)
        ≤ (A * (8 * x / (Real.pi * T))) *
            ∑ n ∈ Finset.Icc 1 (2 * N + 1), |x - (n : ℝ)|⁻¹ := hterm_le
      _ ≤ (A * (8 * x / (Real.pi * T))) * (8 * Real.log (2 * x)) := by
          dsimp only at hsum_inv
          exact mul_le_mul_of_nonneg_left (hsum_inv.trans h4_le) (by positivity)
      _ = (64 / Real.pi) * (x * A * Real.log (2 * x) / T) := by ring
  linarith [hex, hhit0, hnear_bd]

/-- The half-integer estimate for logarithmically bounded coefficients and a
quadratic bound on the absolute series near the line of convergence. -/
theorem perron_halfInteger_log_error_le {a : ℕ → ℂ} {N : ℕ} (hN : 2 ≤ N)
    {c T : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) (hT : 2 ≤ T)
    (ha : LSeriesSummable a (c : ℂ))
    (hseries : ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ ≤ 4 / (c - 1) ^ 2)
    (hcoeff : ∀ n ∈ Finset.Icc 1 (2 * N + 1), ‖a n‖ ≤ Real.log (2 * ((N : ℝ) + 1/2))) :
    let x : ℝ := (N : ℝ) + 1 / 2
    ‖dirichletContourIntegral a x c T - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤
      (4 / (Real.pi * Real.log 2)) * (x ^ c / (T * (c - 1) ^ 2)) +
      (64 / Real.pi) * (x * (Real.log (2*x)) ^ 2 / T) := by
  intro x
  have hx : 0 < x := by positivity
  have hlog : 0 ≤ Real.log (2*x) := Real.log_nonneg (by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) N])
  have h := perron_halfInteger_error_le hN hc1 hc2 hT ha hlog hcoeff
  change ‖_ - _‖ ≤ (x ^ c / _) * _ + (64 / Real.pi) * (x * Real.log (2*x) * Real.log (2*x) / T) at h
  have hfar := mul_le_mul_of_nonneg_left hseries
    (show 0 ≤ x ^ c / (Real.pi * T * Real.log 2) by positivity)
  calc
    _ ≤ _ := h
    _ ≤ (x ^ c / (Real.pi * T * Real.log 2)) * (4 / (c - 1) ^ 2) +
        (64 / Real.pi) * (x * Real.log (2*x) * Real.log (2*x) / T) := add_le_add hfar le_rfl
    _ = _ := by
      field_simp [Real.pi_ne_zero, (Real.log_pos one_lt_two).ne', (by linarith : T ≠ 0),
        sub_ne_zero.mpr hc1.ne']
      <;> ring

end AnalyticNumberTheory.DirichletSeries
