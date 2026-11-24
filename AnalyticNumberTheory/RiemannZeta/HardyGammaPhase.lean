import AnalyticNumberTheory.RiemannZeta.HardyOscillation
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Gamma phase on the critical line

Stirling's formula approximates the phase of the real Gamma factor uniformly
to order `1/t`. Both phases take values on the unit circle.
-/

open Complex Real Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.RiemannZeta

private theorem gammaReal_critical_ne (t : ℝ) : Gammaℝ (1/2+(t:ℂ)*I) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (by simp)

/-- Unit complex factor converting zeta on the critical line to Hardy's real function. -/
noncomputable def hardyGammaUnit (t : ℝ) : ℂ :=
  Gammaℝ (1/2+(t:ℂ)*I) / (‖Gammaℝ (1/2+(t:ℂ)*I)‖:ℝ)

theorem norm_hardyGammaUnit (t : ℝ) : ‖hardyGammaUnit t‖ = 1 := by
  rw [hardyGammaUnit, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (gammaReal_critical_ne t))]

theorem hardyZ_eq_gammaUnit_mul_zeta (t : ℝ) :
    (hardyZ t:ℂ) = hardyGammaUnit t * riemannZeta (1/2+(t:ℂ)*I) := by
  have hne : (1/2+(t:ℂ)*I) ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num at this
  rw [ofReal_hardyZ, hardyGammaUnit, riemannZeta_def_of_ne_zero hne]
  let G := Gammaℝ (1/2+(t:ℂ)*I)
  let Λ := completedRiemannZeta (1/2+(t:ℂ)*I)
  change Λ/(‖G‖:ℂ) = G/(‖G‖:ℂ)*(Λ/G)
  have hG : G ≠ 0 := gammaReal_critical_ne t
  field_simp

private theorem phase_error (u : ℝ) (hu : 1 ≤ u) :
    let z := ((1/4:ℝ):ℂ)+(u:ℂ)*I
    |u*(Real.log ‖z‖-Real.log u) -
      (1/4)*(z.arg-π/2) + (stirlingRemainder z).im| ≤ 2/u := by
  let z := ((1/4:ℝ):ℂ)+(u:ℂ)*I
  have hu0 : 0 < u := by linarith
  have hzn : ‖z‖^2 = (1/4:ℝ)^2+u^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; simp [z]; ring
  have huz : u ≤ ‖z‖ := by simpa [z] using Complex.im_le_norm z
  have hzpos := hu0.trans_le huz
  have hlog : 0 ≤ Real.log ‖z‖-Real.log u := sub_nonneg.mpr (Real.log_le_log hu0 huz)
  have he : u*(Real.log ‖z‖-Real.log u) ≤ (1/4)/u := by
    rw [← Real.log_div hzpos.ne' hu0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hzpos hu0)
    have h' := mul_le_mul_of_nonneg_left h hu0.le
    have hratio : u*(‖z‖/u-1) = ‖z‖-u := by field_simp
    rw [hratio] at h'
    apply h'.trans
    rw [le_div_iff₀ hu0]
    nlinarith [sq_nonneg (‖z‖-u)]
  have harg : z.arg-π/2 = -Real.arctan ((1/4)/u) := by
    change ((((1/4:ℝ):ℂ)+(u:ℂ)*I).arg)-π/2 = _
    rw [arg_add_mul_I_of_pos hu0]
    ring
  have ha := Real.arctan_le_self (show 0 ≤ (1/4:ℝ)/u by positivity)
  have ha0 := Real.arctan_nonneg.mpr (show 0 ≤ (1/4:ℝ)/u by positivity)
  have hr := norm_stirlingRemainder_strip_le (σ₁ := 1/4) (σ₂ := 1/4) (σ := 1/4) (t := u)
    (by exact ⟨le_rfl,le_rfl⟩) (by rwa [abs_of_pos hu0])
  change ‖stirlingRemainder z‖ ≤ _ at hr
  rw [abs_of_pos hu0] at hr
  norm_num at hr
  have hi := (Complex.abs_im_le_norm (stirlingRemainder z)).trans hr
  rw [abs_le] at hi
  change |u*(Real.log ‖z‖-Real.log u) - (1/4)*(z.arg-π/2) + (stirlingRemainder z).im| ≤ _
  rw [harg, abs_le]
  rw [show (21/4:ℝ)/(12*u) = (7/16:ℝ)/u by ring] at hi
  simp only [div_eq_mul_inv] at ha ha0 he hi ⊢
  constructor <;> linarith only [hi.1,hi.2,he,ha,ha0,mul_nonneg hu0.le hlog, inv_pos.mpr hu0]

private theorem exp_normalized (v : ℂ) :
    Complex.exp v / (‖Complex.exp v‖:ℝ) = Complex.exp ((v.im:ℂ)*I) := by
  rw [Complex.norm_exp, Complex.ofReal_exp]
  rw [← Complex.exp_sub]
  congr 1
  exact sub_eq_iff_eq_add.mpr (by rw [add_comm, Complex.re_add_im])

private theorem hardyGammaUnit_eq_exp (t : ℝ) (ht : 2 ≤ t) :
    ∃ δ : ℝ, |δ| ≤ 4/t ∧ hardyGammaUnit t = Complex.exp (((hardyPhase t+δ:ℝ):ℂ)*I) := by
  let u := t/2
  let z := ((1/4:ℝ):ℂ)+(u:ℂ)*I
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hzr : z.re = 1/4 := by simp [z]
  have hzi : z.im = u := by simp [z]
  have hz : z ∈ Complex.slitPlane := Or.inl (by rw [hzr]; norm_num)
  let δ := u*(Real.log ‖z‖-Real.log u)-(1/4)*(z.arg-π/2)+(stirlingRemainder z).im
  have hd : |δ| ≤ 2/u := phase_error u hu
  refine ⟨δ, hd.trans_eq (by dsimp [u]; ring), ?_⟩
  have heq : (1/2+(t:ℂ)*I)/2 = z := by dsimp [z,u]; push_cast; ring
  let v := -(Real.log π:ℂ)*z + Complex.log z*(z-1/2) -z+stirlingRemainder z
  have hgamma : Gammaℝ (1/2+(t:ℂ)*I) = (√(2*π):ℂ)*Complex.exp v := by
    rw [Gammaℝ, neg_div, heq, complex_gamma_eq_stirling hz, Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hz),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), ← Complex.ofReal_log Real.pi_pos.le]
    dsimp [v]
    rw [show -(Real.log π:ℂ)*z+Complex.log z*(z-1/2)-z+stirlingRemainder z =
        (Real.log π:ℂ)*(-z)+(Complex.log z*(z-1/2))+(-z+stirlingRemainder z) by ring,
      Complex.exp_add ((Real.log π:ℂ)*(-z)+(Complex.log z*(z-1/2))) (-z+stirlingRemainder z),
      Complex.exp_add ((Real.log π:ℂ)*(-z)) (Complex.log z*(z-1/2))]
    ring
  have hroot := Real.sqrt_pos.mpr (show 0 < 2*π by positivity)
  rw [hardyGammaUnit, hgamma, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hroot, Complex.ofReal_mul,
    mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hroot.ne'), exp_normalized]
  congr 2
  have hlog : Real.log u = Real.log t-Real.log 2 := Real.log_div (by linarith) (by norm_num)
  have hlog2 := Real.log_mul (show (2:ℝ)≠0 by norm_num) Real.pi_ne_zero
  dsimp only [v]
  simp only [Complex.add_im,Complex.sub_im,Complex.mul_im, Complex.neg_im,Complex.neg_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_ofNat_im, Complex.div_ofNat_re, Complex.one_re, Complex.one_im, Complex.log_re,
    Complex.log_im, hzr, hzi, zero_div, sub_zero]
  dsimp only [hardyPhase,δ]
  rw [hlog,hlog2]
  dsimp only [u]
  apply congrArg Complex.ofReal
  ring

/-- Uniform Stirling approximation to the complex multiplier in Hardy's function. -/
theorem norm_hardyGammaUnit_sub_exp_le {t : ℝ} (ht : 2 ≤ t) :
    ‖hardyGammaUnit t - Complex.exp ((hardyPhase t:ℂ)*I)‖ ≤ 4/t := by
  obtain ⟨δ,hδ,h⟩ := hardyGammaUnit_eq_exp t ht
  rw [h, Complex.ofReal_add, add_mul, Complex.exp_add,
    show ∀ z w : ℂ, z*w-z = z*(w-1) by intros; ring, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm,Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := δ)).trans (by simpa only [Real.norm_eq_abs] using hδ)

end AnalyticNumberTheory.RiemannZeta
