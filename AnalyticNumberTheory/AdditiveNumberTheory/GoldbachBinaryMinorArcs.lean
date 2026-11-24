import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Mean square of the binary Goldbach minor-arc integrals

On the shifted fundamental interval, Bessel's inequality bounds the sum over
target integers by the fourth moment on the minor arcs. Vaughan's uniform
bound removes two powers, and Parseval controls the remaining second moment.
-/

noncomputable section
open Finset MeasureTheory Filter
open scoped Classical
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Bessel's inequality for the additive characters on a shifted unit interval.
The coefficient convention agrees with the circle-method representation integral. -/
theorem sum_sq_integral_e_neg_le (F : ℝ → ℂ) (a : ℝ)
    (hF : MemLp F 2 (volume.restrict (Set.Ioc a (a+1)))) (S : Finset ℕ) :
    ∑ n ∈ S, ‖∫ x in a..a+1, F x * e (-x*n)‖^2 ≤ ∫ x in a..a+1, ‖F x‖^2 := by
  have ha : a < a+1 := by linarith
  have hp := hasSum_sq_fourierCoeffOn ha hF
  have hc (n : ℕ) : fourierCoeffOn ha F (n:ℤ) = ∫ x in a..a+1, F x * e (-x*n) := by
    rw [fourierCoeffOn_eq_integral F _ ha]
    simp only [add_sub_cancel_left, one_div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [smul_eq_mul, fourier_coe_apply, e, mul_comm (F x)]
    congr 2
    push_cast
    ring
  simp_rw [← hc]
  have hinj : Function.Injective (Nat.cast : ℕ → ℤ) := Nat.cast_injective
  let emb : ℕ ↪ ℤ := ⟨_,hinj⟩
  have h := hp.summable.sum_le_tsum (S.map emb) (fun i _ => sq_nonneg _)
  rw [hp.tsum_eq] at h
  simpa [emb,Finset.sum_map] using h

/-- Mean-square minor-arc estimate for binary Goldbach, on any finite set
of integer targets. The major and minor arcs use the prime-sum cutoff N. -/
theorem sum_sq_goldbachBinary_minorArcIntegral_le {N : ℕ} (hN : 2 ≤ N)
    {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2*P ≤ Q) (S : Finset ℕ) :
    ∑ n ∈ S, ‖minorArcIntegral (fun α => primeExpSum N α ^ 2 * e (-α*n)) P Q‖^2 ≤
      (10000 * (N * P ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (4 / 5 : ℝ) +
        (N : ℝ) ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) * (Real.log N)^4)^2 *
        (Chebyshev.psi N * Real.log N) := by
  let a : ℝ := -(1/Q)
  let U := minorArcs P Q
  let Z := primeExpSum N
  let B : ℝ := 10000 * (N * P ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (4 / 5 : ℝ) +
        (N : ℝ) ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) * (Real.log N)^4
  let F := U.indicator (fun x => Z x ^ 2)
  have ha : a ≤ a+1 := by linarith
  have hU : MeasurableSet U := measurableSet_minorArcs P Q
  have hsub : U ⊆ Set.Icc a (a+1) := by
    simpa only [a,sub_eq_neg_add] using minorArcs_subset_Icc P Q
  have hZ := continuous_primeExpSum N
  have hx : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hb (x : ℝ) (hx' : x ∈ U) : ‖Z x‖ ≤ B := norm_primeExpSum_le_on_minorArcs hx hP hPQ hx'
  have hF : MemLp F 2 (volume.restrict (Set.Ioc a (a+1))) := by
    apply MemLp.of_bound ((hZ.pow 2).measurable.indicator hU).aestronglyMeasurable ((6*N:ℝ)^2)
    exact .of_forall fun x => by
      by_cases hu : x ∈ U
      · simpa [F,hu,norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_primeExpSum_le (Nat.cast_nonneg N) x) 2
      · simp [hu]
  have he (n : ℕ) : minorArcIntegral (fun x => Z x^2*e (-x*n)) P Q =
      ∫ x in a..a+1, F x * e (-x*n) := by
    rw [intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc]
    have hfun : (fun x => F x * e (-x*n)) = U.indicator (fun x => Z x^2*e (-x*n)) := by
      ext x
      by_cases hx : x ∈ U <;> simp [F,hx]
    rw [hfun,setIntegral_indicator hU,Set.inter_eq_right.mpr hsub]
    rfl
  change (∑ n ∈ S, ‖minorArcIntegral (fun x => Z x^2*e (-x*n)) P Q‖^2) ≤ B^2*_
  simp_rw [he]
  refine (sum_sq_integral_e_neg_le F a hF S).trans ?_
  have hnorm (x : ℝ) : ‖F x‖^2 ≤ B^2*‖Z x‖^2 := by
    by_cases hu : x ∈ U
    · simp only [F,Set.indicator_of_mem hu,norm_pow]
      rw [sq (‖Z x‖^2)]
      gcongr
      exact hb x hu
    · simp [F,hu,mul_nonneg (sq_nonneg B) (sq_nonneg ‖Z x‖)]
  have hInt : IntervalIntegrable (fun x => ‖F x‖^2) volume a (a+1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    exact hF.integrable_norm_pow (by norm_num)
  have hInt' : IntervalIntegrable (fun x => B^2*‖Z x‖^2) volume a (a+1) :=
    (continuous_const.mul (hZ.norm.pow 2)).intervalIntegrable _ _
  have hper : Function.Periodic (fun x => ‖Z x‖^2) 1 := by
    intro x; simp [Z,periodic_primeExpSum N x]
  calc
    _ ≤ ∫ x in a..a+1, B^2*‖Z x‖^2 := intervalIntegral.integral_mono ha hInt hInt' hnorm
    _ = B^2 * ∫ x in (0:ℝ)..1, ‖Z x‖^2 := by rw [intervalIntegral.integral_const_mul,intervalIntegral_periodic_add hper]
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_sq_primeExpSum_le (by linarith : (1:ℝ) ≤ N)) (sq_nonneg _)

end AnalyticNumberTheory.AdditiveNumberTheory
