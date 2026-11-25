import AnalyticNumberTheory.PrimeDistribution.VinogradovKorobovWidth
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik

/-!
# Consequences of the Vinogradov–Korobov width

On a sufficiently high half-line the classical width dominates
`c (log t)^(-3/4)`. This supplies the super-logarithmic hypothesis
used by short-interval density arguments.
-/
noncomputable section
open Real Filter Complex
namespace AnalyticNumberTheory.PrimeDistribution

/-- A zero-free half-strip with Vinogradov–Korobov width gives the hypothesis
formulated at individual zeros. -/
theorem vinogradovKorobov_of_nonvanishing {c : ℝ} (hc : 0<c)
    (h : ∀ᶠ T : ℝ in atTop, ∀ σ t : ℝ, T≤|t| → 1-c/vinogradovKorobovDenom |t|≤σ →
      riemannZeta ((σ:ℂ)+t*I)≠0) : VinogradovKorobovZeroFreeHypothesis := by
  obtain ⟨U,hU⟩ := eventually_atTop.mp (h.and (tendsto_vinogradovKorobovDenom.eventually_ge_atTop 1))
  refine ⟨c,hc,U,?_⟩
  intro z hz _ _ hzu
  have hD : 0<vinogradovKorobovDenom |z.im| := zero_lt_one.trans_le (hU _ hzu).2
  have hβ : z.re<1-c/vinogradovKorobovDenom |z.im| := lt_of_not_ge (fun he =>
    (hU U le_rfl).1 z.re z.im hzu he (by rwa [Complex.re_add_im]))
  exact (div_le_iff₀ hD).mp (show c/vinogradovKorobovDenom |z.im|≤1-z.re by linarith)

/-- Vinogradov–Korobov width implies the super-logarithmic zero-free
hypothesis in the short-interval prime number theorem. -/
theorem superLogZeroFree_of_vinogradovKorobov (hz : VinogradovKorobovZeroFreeHypothesis) :
    SuperLogZeroFreeHypothesis := by
  obtain ⟨c,hc,U,hU⟩ := hz
  let δ (t : ℝ) := c*(Real.log t)^(-(3/4):ℝ)
  have h₁ := Real.tendsto_log_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop (1/3:ℝ) (by norm_num : (0:ℝ)<1/12)).bound (by norm_num : (0:ℝ)<1))
  have h₂ := Real.tendsto_log_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/8)).bound (by norm_num : (0:ℝ)<1))
  have hL := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  have hall : ∀ᶠ T : ℝ in atTop, U≤T ∧ 2≤T ∧ 1≤Real.log (Real.log T) ∧
      1≤Real.log T ∧ vinogradovKorobovDenom T ≤ (Real.log T)^(3/4:ℝ) ∧
      Real.log (Real.log T)≤(Real.log T)^(1/8:ℝ) := by
    filter_upwards [eventually_ge_atTop U,eventually_ge_atTop (2:ℝ),hL,Real.tendsto_log_atTop.eventually_ge_atTop 1,h₁,h₂] with T hu ht hl hL h₁ h₂
    change 1≤Real.log (Real.log T) at hl
    have hLp : 0<Real.log T := by linarith
    have hlp : 0<Real.log (Real.log T) := by linarith
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hlp.le _),abs_of_nonneg (Real.rpow_nonneg hLp.le _),one_mul] at h₁
    simp only [Real.norm_eq_abs,abs_of_pos hlp,abs_of_nonneg (Real.rpow_nonneg hLp.le _),one_mul] at h₂
    refine ⟨hu,ht,hl,hL,?_,h₂⟩
    calc
      vinogradovKorobovDenom T ≤ (Real.log T)^(2/3:ℝ)*(Real.log T)^(1/12:ℝ) :=
        mul_le_mul_of_nonneg_left h₁ (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [←Real.rpow_add hLp]; norm_num
  obtain ⟨T₀,h₀⟩ := eventually_atTop.mp hall
  refine ⟨δ,T₀,(h₀ _ le_rfl).2.1,?_,?_,?_,?_⟩
  · intro T hT
    have hL : 0<Real.log T := by linarith [(h₀ T hT).2.2.2.1]
    exact mul_pos hc (Real.rpow_pos_of_pos hL _)
  · intro t ht u _ htu
    have ht₀ : 0<t := by linarith [(h₀ t ht).2.1]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith [(h₀ t ht).2.2.2.1])
      (Real.log_le_log ht₀ htu) (by norm_num)) hc.le
  · apply tendsto_atTop.2
    intro b
    have ht := ((tendsto_const_mul_atTop_of_pos hc).mpr ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp Real.tendsto_log_atTop)).eventually_ge_atTop b
    filter_upwards [hall,ht] with T h hb
    have hlp : 0<Real.log (Real.log T) := by linarith [h.2.2.1]
    have hLp : 0<Real.log T := by linarith [h.2.2.2.1]
    apply hb.trans
    apply (le_div_iff₀ hlp).mpr
    apply (mul_le_mul_of_nonneg_left h.2.2.2.2.2 (by positivity : 0≤c*(Real.log T)^(1/8:ℝ))).trans_eq
    dsimp only [δ]
    rw [mul_assoc,←Real.rpow_add hLp,show (1/8:ℝ)+1/8=1/4 by norm_num,
      show (1/4:ℝ)= -(3/4)+1 by norm_num,Real.rpow_add hLp,Real.rpow_one,mul_assoc]
  · intro z hzero h₀' h₁ hT
    obtain ⟨hu,_,hl,hL,hd,_⟩ := h₀ _ hT
    have hp : 0<Real.log |z.im| := by linarith
    have hh := (hU z hzero h₀' h₁ hu).trans (mul_le_mul_of_nonneg_left hd (by linarith : 0≤1-z.re))
    have hb := (div_le_iff₀ (Real.rpow_pos_of_pos hp (3/4:ℝ))).mpr hh
    dsimp only [δ]; rw [Real.rpow_neg hp.le,←div_eq_mul_inv]; linarith

end AnalyticNumberTheory.PrimeDistribution
