import AnalyticNumberTheory.PrimeDistribution.VinogradovKorobovWidth

/-!
# The truncation scale in the Vinogradov–Korobov prime number theorem

Balancing the truncation height against the zero-free width gives
`(log x)^(3/5)/(log log x)^(1/5)` as the exponential error scale.
-/
noncomputable section
open Real Filter
namespace AnalyticNumberTheory.PrimeDistribution

/-- Exponent of the error in the Vinogradov–Korobov prime number theorem. -/
def vinogradovKorobovErrorScale (x : ℝ) : ℝ :=
  (Real.log x)^(3/5:ℝ)/(Real.log (Real.log x))^(1/5:ℝ)

private theorem scale_sandwich {x : ℝ} (hL : 1≤Real.log x) (hl : 1≤Real.log (Real.log x)) :
    (Real.log x)^(2/5:ℝ)≤vinogradovKorobovErrorScale x ∧
      vinogradovKorobovErrorScale x≤(Real.log x)^(3/5:ℝ) := by
  let L := Real.log x
  let l := Real.log L
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hlp : 0<l := zero_lt_one.trans_le hl
  have hll : l≤L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hlp _)).mpr
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlp.le hll (by norm_num : (0:ℝ)≤1/5))
      (Real.rpow_nonneg hLp.le (2/5:ℝ))).trans_eq
    rw [←Real.rpow_add hLp,show (2/5:ℝ)+1/5=3/5 by norm_num]
  · exact div_le_self (Real.rpow_nonneg hLp.le _) (Real.one_le_rpow hl (by norm_num))

theorem tendsto_vinogradovKorobovErrorScale : Tendsto vinogradovKorobovErrorScale atTop atTop := by
  apply tendsto_atTop_mono' _ _ ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/5)).comp Real.tendsto_log_atTop)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with x hL hl
  exact (scale_sandwich hL hl).1

/-- The error scale dominates any fixed multiple of log log x and is at most
an arbitrarily small fixed fraction of log x. -/
theorem vinogradovKorobov_error_parameters {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    ∀ᶠ x : ℝ in atTop, let v := vinogradovKorobovErrorScale x
      1≤Real.log (Real.log x) ∧ 4≤Real.log x ∧ 1≤v ∧
      A*Real.log (Real.log x)≤v ∧ B*v≤Real.log x ∧
      v*vinogradovKorobovDenom (Real.exp v)≤Real.log x := by
  have h₁ := Real.tendsto_log_atTop.eventually ((isLittleO_log_rpow_atTop
    (by norm_num : (0:ℝ)<2/5)).bound (inv_pos.mpr hA))
  have h₂ := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/5)).comp Real.tendsto_log_atTop).eventually_ge_atTop B
  filter_upwards [h₁,h₂,Real.tendsto_log_atTop.eventually_ge_atTop 4,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    tendsto_vinogradovKorobovErrorScale.eventually_ge_atTop 1] with x h₁ h₂ hL hl hv
  let L := Real.log x
  let l := Real.log L
  let v := vinogradovKorobovErrorScale x
  change 4≤L at hL
  change 1≤l at hl
  have hlp : 0<l := by linarith
  have hLp : 0<L := by linarith
  have hvp : 0<v := zero_lt_one.trans_le hv
  have hbounds := scale_sandwich (by change 1≤L; linarith) hl
  change ‖l‖≤A⁻¹*‖L^(2/5:ℝ)‖ at h₁
  change B≤L^(2/5:ℝ) at h₂
  rw [Real.norm_of_nonneg hlp.le,Real.norm_of_nonneg (Real.rpow_nonneg hLp.le _),←div_eq_inv_mul] at h₁
  refine ⟨hl,hL,hv,((le_div_iff₀ hA).mp h₁).trans_eq' (mul_comm l A) |>.trans hbounds.1,?_,?_⟩
  · apply (mul_le_mul_of_nonneg_left hbounds.2 hB.le).trans
    apply (mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hLp.le _)).trans_eq
    rw [←Real.rpow_add hLp,show (2/5:ℝ)+3/5=1 by norm_num,Real.rpow_one]
  · have hvL : v≤L := hbounds.2.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤L)
        (by norm_num : (3/5:ℝ)≤1)).trans_eq (Real.rpow_one _))
    have hlog := Real.log_le_log hvp hvL
    change v*(((Real.log (Real.exp v))^(2/3:ℝ))*(Real.log (Real.log (Real.exp v)))^(1/3:ℝ))≤L
    rw [Real.log_exp]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Real.log_nonneg hv) hlog (by norm_num : (0:ℝ)≤1/3))
      (Real.rpow_nonneg hvp.le (2/3:ℝ))) hvp.le).trans_eq
    rw [←mul_assoc,show v*v^(2/3:ℝ)=v^(5/3:ℝ) by nth_rw 1 [←Real.rpow_one v]; rw [←Real.rpow_add hvp]; norm_num]
    change (L^(3/5:ℝ)/l^(1/5:ℝ))^(5/3:ℝ)*l^(1/3:ℝ)=L
    rw [Real.div_rpow (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hlp.le _),
      ←Real.rpow_mul hLp.le,←Real.rpow_mul hlp.le,show (3/5:ℝ)*(5/3)=1 by norm_num,
      show (1/5:ℝ)*(5/3)=1/3 by norm_num,Real.rpow_one,div_mul_cancel₀ _ (Real.rpow_pos_of_pos hlp _).ne']

end AnalyticNumberTheory.PrimeDistribution
