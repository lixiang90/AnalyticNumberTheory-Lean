import AnalyticNumberTheory.DirichletSeries.LogPerron
import AnalyticNumberTheory.DirichletSeries.HigherPerron
import AnalyticNumberTheory.DirichletSeries.OrdinaryAbel
import AnalyticNumberTheory.AnalyticTools.Summation.Abel

/-! # Logarithmic smoothing of ordinary arithmetic sums -/

noncomputable section

open Complex Finset Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.DirichletSeries

/-- First logarithmic mean of the coefficients of an ordinary Dirichlet
series. An integer at the cutoff has weight zero. -/
def logWeightedSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (Real.log (x/n) : ℂ)

/-- The logarithmic Riesz mean of integral order `k` of arithmetic coefficients. -/
def powerLogWeightedSum (k : ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((Real.log (x/n) : ℂ)^k / k.factorial)

@[simp] theorem powerLogWeightedSum_one (a : ℕ → ℂ) (x : ℝ) :
    powerLogWeightedSum 1 a x = logWeightedSum a x := by
  simp [powerLogWeightedSum, logWeightedSum]

/-- An ordinary logarithmic mean of any positive order is the absolute
vertical integral against `x^s/s^(k+1)`, for every positive real cutoff. -/
theorem powerLogWeightedSum_eq_perron {k : ℕ} (hk : 0 < k) {a : ℕ → ℂ} {x σ : ℝ}
    (hx : 0 < x) (hσ : 0 < σ) (h : LSeriesSummable a (σ : ℂ)) :
    powerLogWeightedSum k a x =
      (∫ t : ℝ, LSeries a ((σ : ℂ)+t*I) * (x : ℂ)^((σ : ℂ)+t*I) / (((σ : ℂ)+t*I)^(k+1))) /
        (2*Real.pi) := by
  let F := DirichletFrequency.logarithmic
  have H := F.powerLogPerron_formula (fun n => a (n+1)) hk hσ
    ((DirichletFrequency.logarithmic_absConvergesAt a _).mpr h) (Real.log x)
  have hi (t : ℝ) :
      F.sum (fun n => a (n+1)) ((σ : ℂ)+t*I) * powerLogPerronKernel k σ (Real.log x) t =
        LSeries a ((σ : ℂ)+t*I) * (x : ℂ)^((σ : ℂ)+t*I) / (((σ : ℂ)+t*I)^(k+1)) := by
    have ht : LSeriesSummable a ((σ : ℂ)+t*I) := h.of_re_le_re (by simp)
    rw [DirichletFrequency.logarithmic_sum, ht.dirichletSum_eq_LSeries, powerLogPerronKernel,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
      mul_comm ((σ : ℂ)+t*I), mul_div_assoc]
  have hS (N : ℕ) : ∑ n ∈ range N, a (n+1) * (((Real.log x-F n : ℝ) : ℂ)^k / k.factorial) =
      ∑ n ∈ Icc 1 N, a n * ((Real.log (x/n) : ℂ)^k / k.factorial) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, sum_Icc_succ_top (Nat.succ_pos N), ih, Real.log_div hx.ne' (by positivity)]
      rfl
  dsimp only [F] at H hi hS
  rw [DirichletFrequency.logarithmic_count_log hx, hS, integral_congr_ae (ae_of_all _ hi)] at H
  exact H.symm

/-- Ordinary logarithmic Perron inversion, with kernel `x^s / s²`. -/
theorem logWeightedSum_eq_perron {a : ℕ → ℂ} {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ)
    (h : LSeriesSummable a (σ : ℂ)) :
    logWeightedSum a x =
      (∫ t : ℝ, LSeries a ((σ : ℂ)+t*I) * (x : ℂ)^((σ : ℂ)+t*I) / (((σ : ℂ)+t*I)^2))/(2*Real.pi) := by
  simpa only [powerLogWeightedSum_one] using powerLogWeightedSum_eq_perron (k := 1) (by decide) hx hσ h

/-- The first logarithmic mean is the integral of the inclusive coefficient
sum against `dt/t`. This finite identity holds even at integer endpoints. -/
theorem logWeightedSum_eq_integral {a : ℕ → ℂ} {x : ℝ} (hx : 1 ≤ x) :
    logWeightedSum a x = ∫ t : ℝ in 1..x, coeffPartialSum a ⌊t⌋₊ / (t : ℂ) := by
  have hp {t : ℝ} (ht : t ∈ Set.Icc 1 x) : 0 < t := zero_lt_one.trans_le ht.1
  have hlog (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun u : ℝ => (Real.log u : ℂ)) ((t⁻¹ : ℝ) : ℂ) t :=
    (Real.hasDerivAt_log (hp ht).ne').ofReal_comp
  have hcont : ContinuousOn (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) (Set.Icc 1 x) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_inv₀.mono (fun _ ht => (hp ht).ne'))
  have H := abel_summation_Icc_one_hasDerivAt a hx hlog hcont
  have hsum : logWeightedSum a x = (∑ n ∈ Icc 1 ⌊x⌋₊, a n)*(Real.log x : ℂ) -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n*(Real.log n : ℂ) := by
    rw [logWeightedSum, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (mem_Icc.mp hn).1)
    rw [Real.log_div (zero_lt_one.trans_le hx).ne' hn', Complex.ofReal_sub, mul_sub]
  rw [hsum, H, sub_sub_cancel]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [Complex.ofReal_inv, div_eq_mul_inv]
  rfl

/-- Exact recovery by a logarithmic finite difference. The remainder is
supported on the short interval `x < n ≤ y`. -/
theorem logWeightedSum_sub_eq_short_sum (a : ℕ → ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    logWeightedSum a y - logWeightedSum a x =
      coeffPartialSum a ⌊x⌋₊ * (Real.log (y/x) : ℂ) +
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, a n * (Real.log (y/n) : ℂ) := by
  let b := fun n : ℕ => a n*(Real.log (y/n) : ℂ)
  have hsplit := sum_Ioc_consecutive b (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono hxy)
  rw [← Icc_add_one_left_eq_Ioc, zero_add, ← Icc_add_one_left_eq_Ioc (a := 0), zero_add] at hsplit
  unfold logWeightedSum
  rw [show (∑ n ∈ Icc 1 ⌊y⌋₊, a n * (Real.log (y/n) : ℂ)) = _ from hsplit.symm,
    add_sub_right_comm, coeffPartialSum, sum_mul, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (mem_Icc.mp hn).1)
  dsimp only [b]
  rw [Real.log_div (hx.trans_le hxy).ne' hn', Real.log_div hx.ne' hn',
    Real.log_div (hx.trans_le hxy).ne' hx.ne']
  push_cast
  ring

/-- The short-interval remainder of logarithmic desmoothing is at most
`log(y/x)` times the total absolute coefficient mass on that interval. -/
theorem norm_logWeightedSum_sub_sub_le (a : ℕ → ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖logWeightedSum a y - logWeightedSum a x - coeffPartialSum a ⌊x⌋₊*(Real.log (y/x) : ℂ)‖ ≤
      (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, ‖a n‖) * Real.log (y/x) := by
  rw [logWeightedSum_sub_eq_short_sum a hx hxy, add_sub_cancel_left, sum_mul]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun n hn => ?_
  obtain ⟨hnx,hny⟩ := mem_Ioc.mp hn
  have hnx' : x < n := (Nat.floor_lt hx.le).mp hnx
  have hny' : (n : ℝ) ≤ y := (Nat.le_floor_iff (hx.trans_le hxy).le).mp hny
  have hn₀ := hx.trans hnx'
  have hratio : 1 ≤ y/n := (one_le_div hn₀).mpr hny'
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hratio)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.log_le_log (zero_lt_one.trans_le hratio) (div_le_div_of_nonneg_left (hx.trans_le hxy).le hx hnx'.le)

end AnalyticNumberTheory.DirichletSeries
