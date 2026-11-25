import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A lower bound for a positive Dirichlet series from its summatory function

Linear mass throughout an interval contributes logarithmically to the
harmonic sum. At an abscissa just to the right of one this gives a
lower bound for the full Dirichlet series.
-/

open Real Filter MeasureTheory Finset
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DirichletSeries

set_option maxHeartbeats 700000 in
/-- A lower bound on the partial sums on `[Y,X]` implies a logarithmic lower
bound for the harmonic sum up to `X`. -/
theorem harmonic_sum_ge_of_linear_mass {f : ℕ → ℝ} (hf : ∀ n,0≤f n) {Y X v : ℝ}
    (hY : 1≤Y) (hX : Y≤X)
    (h : ∀ t∈Set.Icc Y X, v*t ≤ ∑ n∈Icc 1 ⌊t⌋₊,f n) :
    v*log (X/Y) ≤ ∑ n∈Icc 1 ⌊X⌋₊,f n/(n:ℝ) := by
  let S (t : ℝ) := ∑n∈Icc 1 ⌊t⌋₊,f n
  have h1 := hY.trans hX
  have hY0 := zero_lt_one.trans_le hY
  have hX0 := hY0.trans_le hX
  have hS (t : ℝ) : 0≤S t := sum_nonneg (fun n _ => hf n)
  have hi (a b : ℝ) (ha : 1≤a) (hab : a≤b) : IntervalIntegrable (fun t => S t/t^2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hg : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc a b) :=
      (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (zero_lt_one.trans_le (ha.trans ht.1)).ne')
    simpa [S,div_eq_mul_inv,mul_comm] using integrableOn_mul_sum_Icc (m:=1) f
      (zero_le_one.trans ha) (hg.integrableOn_compact isCompact_Icc)
  have hdInv (t : ℝ) (ht : t∈Set.Icc 1 X) : HasDerivAt (fun y : ℝ => y⁻¹) (-(t^2)⁻¹) t :=
    hasDerivAt_inv (zero_lt_one.trans_le ht.1).ne'
  have hcInv : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc 1 X) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (zero_lt_one.trans_le ht.1).ne')
  have hAb := abel_summation_Icc_one_hasDerivAt (𝕜:=ℝ) f (f:=fun t : ℝ => t⁻¹)
    (f':=fun t : ℝ => -(t^2)⁻¹) (x:=X) h1 hdInv hcInv.neg
  change ∑ n∈Icc 1 ⌊X⌋₊,f n*(n:ℝ)⁻¹ = S X*X⁻¹-∫ t in (1:ℝ)..X,S t*(-(t^2)⁻¹) at hAb
  simp only [mul_neg,intervalIntegral.integral_neg,sub_neg_eq_add,←div_eq_mul_inv] at hAb
  have hn : 0≤∫ t in (1:ℝ)..Y,S t/t^2 := intervalIntegral.integral_nonneg hY (fun t _ => div_nonneg (hS _) (sq_nonneg _))
  have hh : v*log (X/Y) ≤ ∫ t in Y..X,S t/t^2 := by
    rw [← integral_inv_of_pos hY0 hX0,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hX
      (continuousOn_const.mul (continuousOn_id.inv₀ (fun t (ht : t∈Set.uIcc Y X) =>
        (hY0.trans_le ((Set.uIcc_of_le hX) ▸ ht).1).ne'))).intervalIntegrable (hi Y X hY hX)
    intro t ht
    have htp := hY0.trans_le ht.1
    rw [le_div_iff₀ (sq_pos_of_pos htp)]
    calc v*t⁻¹*t^2 = v*t := by field_simp
         _ ≤ _ := h t ht
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 1 Y le_rfl hY) (hi Y X hY hX)] at hAb
  linarith [div_nonneg (hS X) hX0.le]

/-- A series of nonnegative coefficients at `1+u` dominates the smoothed
harmonic mass on any finite range. -/
theorem dirichlet_value_ge_of_linear_mass {f : ℕ → ℝ} (hf : ∀ n,0≤f n) {Y X v u V : ℝ}
    (hY : 1≤Y) (hX : Y≤X) (hu : 0≤u)
    (hV : HasSum (fun n : ℕ => f n*(n:ℝ)^(-(1+u))) V)
    (h : ∀ t∈Set.Icc Y X,v*t ≤ ∑n∈Icc 1 ⌊t⌋₊,f n) :
    v*log (X/Y)*X^(-u) ≤ V := by
  have hX0 := zero_lt_one.trans_le (hY.trans hX)
  calc _ ≤ (∑n∈Icc 1 ⌊X⌋₊, f n/(n:ℝ))*X^(-u) :=
             mul_le_mul_of_nonneg_right (harmonic_sum_ge_of_linear_mass hf hY hX h) (rpow_nonneg hX0.le _)
       _ = ∑n∈Icc 1 ⌊X⌋₊,(f n/n)*X^(-u) := sum_mul ..
       _ ≤ ∑n∈Icc 1 ⌊X⌋₊,f n*(n:ℝ)^(-(1+u)) := by
             apply sum_le_sum; intro n hn
             have hn0 : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
             have hnX : (n:ℝ)≤X := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hX0.le)
             rw [show -(1+u)=(-1)+(-u) by ring,rpow_add hn0,rpow_neg_one,div_eq_mul_inv,← mul_assoc]
             exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hn0 hnX (neg_nonpos.mpr hu)) (mul_nonneg (hf n) (inv_nonneg.mpr hn0.le))
       _ ≤ V := by
             rw [← hV.tsum_eq]
             exact hV.summable.sum_le_tsum _ (fun n _ => mul_nonneg (hf n) (rpow_nonneg (Nat.cast_nonneg _) _))

end AnalyticNumberTheory.DirichletSeries
