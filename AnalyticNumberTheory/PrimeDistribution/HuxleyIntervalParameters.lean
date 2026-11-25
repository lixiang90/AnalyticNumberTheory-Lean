import AnalyticNumberTheory.PrimeDistribution.VinogradovKorobovWidth
/-!
# Height choice at the seven-twelfths threshold

The deficit in the density margin is
`(log x)^(2/3) (log log x)^(a+1/3)`. Its product with the
Vinogradov–Korobov width has order `(log log x)^a`.
-/
noncomputable section
open Filter Real
namespace AnalyticNumberTheory.PrimeDistribution

/-- The exponential correction to a pure interval of length `x^(7/12)`. -/
def huxleyIntervalCorrection (a x : ℝ) : ℝ :=
  (Real.log x)^(2/3:ℝ)*(Real.log (Real.log x))^(a+1/3)

/-- The cutoff lies comfortably inside the admissible height range, while
the final saving absorbs fixed powers of the logarithm. -/
theorem huxley_interval_parameters {a : ℝ} (ha : 1<a) {c : ℝ} (hc : 0<c) :
    ∀ᶠ x : ℝ in atTop,
      let L := Real.log x
      let l := Real.log L
      let E := l^a
      let F := huxleyIntervalCorrection a x
      16≤L ∧ 1≤l ∧ 0<vinogradovKorobovDenom x ∧
      F=vinogradovKorobovDenom x*E ∧ F≤L/2 ∧ 48*l≤c*E/2 ∧ 2*(1+c)*E≤F := by
  have hs := Real.tendsto_log_atTop.eventually ((isLittleO_log_rpow_rpow_atTop (a+1/3) (by norm_num : (0:ℝ)<1/3)).bound (by norm_num : (0:ℝ)<1/2))
  have hl := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have he := ((tendsto_rpow_atTop (by linarith : 0<a-1)).comp hl).eventually_ge_atTop (96/c)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 16,hl.eventually_ge_atTop 1,hs,he,
    tendsto_vinogradovKorobovDenom.eventually_ge_atTop (2*(1+c))] with x hL hl hsmall hbig hd
  let L := Real.log x
  let l := Real.log L
  change 16≤L at hL
  change 1≤l at hl
  change 96/c ≤ l^(a-1) at hbig
  have hLp : 0<L := by linarith
  have hlp : 0<l := by linarith
  have hE : 0≤l^a := Real.rpow_nonneg hlp.le _
  have eqF : huxleyIntervalCorrection a x = vinogradovKorobovDenom x*l^a := by
    change L^(2/3:ℝ)*l^(a+1/3) = (L^(2/3:ℝ)*l^(1/3:ℝ))*l^a
    rw [Real.rpow_add hlp]; ring
  have hsm : l^(a+1/3) ≤ 1/2*L^(1/3:ℝ) := by
    change ‖l^(a+1/3)‖ ≤ (1/2)*‖L^(1/3:ℝ)‖ at hsmall
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hlp.le (a+1/3)),abs_of_nonneg (Real.rpow_nonneg hLp.le (1/3:ℝ))] using hsmall
  have hprod : L^(2/3:ℝ)*L^(1/3:ℝ)=L := by rw [←Real.rpow_add hLp]; norm_num
  have hpow : l*l^(a-1)=l^a := by
    calc l*l^(a-1) = l^(1+(a-1)) := by rw [Real.rpow_add hlp,Real.rpow_one]
         _ = _ := by congr 1; ring
  refine ⟨hL,hl,by linarith,eqF,?_,?_,?_⟩
  · change L^(2/3:ℝ)*l^(a+1/3) ≤ L/2
    linarith only [mul_le_mul_of_nonneg_left hsm (Real.rpow_nonneg hLp.le (2/3:ℝ)),hprod]
  · have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hc).mp hbig) hlp.le
    nlinarith only [hh,congrArg (fun q : ℝ => c*q) hpow]
  · rw [eqF]
    exact mul_le_mul_of_nonneg_right hd hE

end AnalyticNumberTheory.PrimeDistribution
