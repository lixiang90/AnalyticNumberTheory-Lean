import AnalyticNumberTheory.ExponentialSums.SmoothedPrimeSums
import AnalyticNumberTheory.PrimeDistribution.ChebyshevShortMass

/-! # From logarithmically smoothed prime sums to a sharp cutoff -/

noncomputable section
open Complex Finset Real
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- Recover a sharp prime sum from two larger logarithmic means. The only
arithmetic error is the Chebyshev mass of the interval (x,y]. -/
theorem norm_primeExpSum_le_logSmoothed_difference {x y : ℝ} (hx : 0 < x) (hxy : x < y) (α : ℝ) :
    ‖primeExpSum x α‖ ≤ (‖logSmoothedPrimeExpSum y α‖ + ‖logSmoothedPrimeExpSum x α‖)/Real.log (y/x) +
      (Chebyshev.psi y - Chebyshev.psi x) := by
  let w := Real.log (y/x)
  let F := logSmoothedPrimeExpSum y α - logSmoothedPrimeExpSum x α
  let z := primeExpSum x α * (w : ℂ)
  have hw : 0 < w := Real.log_pos ((one_lt_div hx).mpr hxy)
  have herr : ‖F-z‖ ≤ (Chebyshev.psi y-Chebyshev.psi x)*w :=
    norm_logSmoothedPrimeExpSum_difference hx hxy.le α
  have hz : ‖z‖ = ‖primeExpSum x α‖ * w := by dsimp only [z]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
  have htriangle : ‖z‖ ≤ (Chebyshev.psi y-Chebyshev.psi x)*w +
      (‖logSmoothedPrimeExpSum y α‖ + ‖logSmoothedPrimeExpSum x α‖) := by
    have h := norm_le_norm_sub_add z F
    rw [norm_sub_rev z F] at h
    exact h.trans (add_le_add herr (norm_sub_le ..))
  rw [hz] at htriangle
  change _ ≤ _ / w + _
  calc
    _ ≤ (‖logSmoothedPrimeExpSum y α‖ + ‖logSmoothedPrimeExpSum x α‖ + (Chebyshev.psi y-Chebyshev.psi x)*w)/w :=
      (le_div_iff₀ hw).mpr (by linarith only [htriangle])
    _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hw.ne']

/-- If all smoothed sums on [x,2x] are bounded by M ≥ 1+log x, the sharp
sum at x is at most 8 sqrt(x (1+log x) M). This holds for every real phase. -/
theorem norm_primeExpSum_le_of_logSmoothed_bound {x α M : ℝ} (hx : 1 ≤ x) (hM : 1+Real.log x ≤ M)
    (hbound : ∀ y ∈ Set.Icc x (2*x), ‖logSmoothedPrimeExpSum y α‖ ≤ M) :
    ‖primeExpSum x α‖ ≤ 8*Real.sqrt (x*(1+Real.log x)*M) := by
  let L := 1+Real.log x
  let Z := Real.sqrt (x*L*M)
  let H := Z/L
  have hx₀ := zero_lt_one.trans_le hx
  have hL₁ : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hL := zero_lt_one.trans_le hL₁
  have hM₀ := hL.trans_le hM
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hZsq : Z^2 = x*L*M := Real.sq_sqrt (by positivity)
  have hH : 0 < H := div_pos hZ hL
  have hHL : H*L = Z := div_mul_cancel₀ _ hL.ne'
  have hH₁ : 1 ≤ H := by
    apply (one_le_div hL).mpr
    have hLM : L ≤ x*M := hM.trans (le_mul_of_one_le_left hM₀.le hx)
    have hs := mul_le_mul_of_nonneg_left hLM hL.le
    nlinarith only [hs,hZsq,hZ,hL]
  by_cases hHx : x ≤ H
  · have hxZ : x ≤ Z := hHx.trans ((le_mul_of_one_le_right hH.le hL₁).trans_eq hHL)
    exact (norm_primeExpSum_le hx₀.le α).trans (by change 6*x ≤ 8*Z; linarith only [hxZ,hZ])
  let y := x+H
  have hxy : x < y := by dsimp only [y]; linarith only [hH]
  have hy := hx₀.trans hxy
  have hy₂ : y ≤ 2*x := by dsimp only [y]; linarith only [lt_of_not_ge hHx]
  have hEndpoint := add_le_add (hbound y ⟨hxy.le,hy₂⟩) (hbound x ⟨le_rfl,by linarith⟩)
  have hw : H/(2*x) ≤ Real.log (y/x) := by
    calc
      _ ≤ H/y := div_le_div_of_nonneg_left hH.le hy hy₂
      _ = 1-(y/x)⁻¹ := by dsimp only [y]; rw [inv_div]; field_simp; ring
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos (div_pos hy hx₀)
  have hnorm : (‖logSmoothedPrimeExpSum y α‖+‖logSmoothedPrimeExpSum x α‖)/Real.log (y/x) ≤ 4*Z := by
    calc
      _ ≤ (M+M)/(H/(2*x)) := div_le_div₀ (by positivity) hEndpoint (by positivity) hw
      _ = 4*Z := by
        dsimp only [H]
        field_simp
        nlinarith only [hZsq]
  have hlog : Real.log y ≤ 2*L := by
    have h := Real.log_le_log hy hy₂
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx₀.ne'] at h
    dsimp only [L]
    linarith only [h,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),Real.log_nonneg hx]
  have hshort : Chebyshev.psi y-Chebyshev.psi x ≤ 4*Z := by
    apply (psi_sub_le_length_mul_log hx hxy.le).trans
    calc
      _ ≤ (2*H)*(2*L) := mul_le_mul (by dsimp only [y]; linarith only [hH₁]) hlog
        (Real.log_nonneg (hx.trans hxy.le)) (by positivity)
      _ = 4*Z := by linarith only [hHL]
  exact (norm_primeExpSum_le_logSmoothed_difference hx₀ hxy α).trans ((add_le_add hnorm hshort).trans_eq (by ring))

end AnalyticNumberTheory.ExponentialSums
