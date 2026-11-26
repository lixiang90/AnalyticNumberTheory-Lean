import AnalyticNumberTheory.PrimeDistribution.SelbergArgumentIntegrals
import AnalyticNumberTheory.RiemannZeta.IntegratedArgument

/-! # Littlewood's bounds for the argument of zeta and its integral under RH -/

noncomputable section

open Complex Filter Set Asymptotics
open scoped Topology
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

private theorem littlewood_cutoff {t : ℝ} (ht : 1 < t) (h : 8 ≤ Real.log (Real.log t)) :
    let u := Real.log (Real.log t)/4
    2 ≤ u ∧ Real.exp (4*u) = Real.log t ∧ 1 ≤ Real.log t/u ∧ 1 ≤ Real.log t/u^2 := by
  dsimp only
  let u := Real.log (Real.log t)/4
  have hu : 2 ≤ u := by dsimp [u]; linarith
  have hu₀ := two_pos.trans_le hu
  have he : Real.exp (4*u) = Real.log t := by
    rw [show 4*u = Real.log (Real.log t) by dsimp [u]; ring, Real.exp_log (Real.log_pos ht)]
  have huE : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hsq : u^2 ≤ Real.log t := calc
    u^2 ≤ (Real.exp u)^2 := pow_le_pow_left₀ hu₀.le huE 2
    _ = Real.exp (u+u) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (4*u) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.log t := he
  exact ⟨hu, he, (one_le_div hu₀).mpr (by nlinarith only [hsq, hu, sq_nonneg (u-1)]),
    (one_le_div (sq_pos_of_pos hu₀)).mpr hsq⟩

private theorem off_ordinate_argument_bounds (hRH : RiemannHypothesisProp) :
    ∃ A B : ℝ, ∀ {t : ℝ}, 4 ≤ t → 8 ≤ Real.log (Real.log t) → ¬ IsZeroOrdinate t →
      |argumentSApprox t| ≤ A*(Real.log t/Real.log (Real.log t)) ∧
      |horizontalLogMean riemannZeta t| ≤ B*(Real.log t/Real.log (Real.log t)^2) := by
  obtain ⟨C, hC, HC⟩ := selberg_horizontal_logDeriv_integrals hRH
  refine ⟨4*((1/Real.pi)*(Real.pi+C)), 16*((3/2)*Real.log 2+C), ?_⟩
  intro t ht h hno
  let L := Real.log (Real.log t)
  let u := L/4
  have hL : 0 < L := by dsimp only [L]; linarith
  obtain ⟨hu, he, h₁, h₂⟩ := littlewood_cutoff (by linarith : 1 < t) h
  obtain ⟨hI, hR⟩ := HC ht hu he.le hno
  change 1 ≤ Real.log t/u at h₁
  change 1 ≤ Real.log t/u^2 at h₂
  have hπ := le_mul_of_one_le_right Real.pi_pos.le h₁
  have hlog := le_mul_of_one_le_right (show 0 ≤ (3/2 : ℝ)*Real.log 2 by positivity) h₂
  have habs (a b : ℝ) : |a-b| ≤ |a|+|b| := by simpa only [Real.norm_eq_abs] using norm_sub_le a b
  constructor
  · rw [argumentSApprox, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1/Real.pi)]
    apply (mul_le_mul_of_nonneg_left (habs _ _) (by positivity : 0 ≤ 1/Real.pi)).trans
    have harg (z : ℂ) : |z.arg| ≤ Real.pi := abs_le.mpr ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩
    apply (mul_le_mul_of_nonneg_left (add_le_add ((harg _).trans hπ) hI)
      (by positivity : 0 ≤ 1/Real.pi)).trans_eq
    change 1/Real.pi*(Real.pi*(Real.log t/u)+C*(Real.log t/u)) = _*(Real.log t/L)
    dsimp only [u]
    field_simp [hL.ne', Real.pi_ne_zero]
  · rw [horizontalLogMean_zeta_eq_real_moment (by linarith) hno]
    apply (habs _ _).trans
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (3/2 : ℝ))]
    apply (add_le_add ((mul_le_mul_of_nonneg_left (abs_log_norm_zeta_two_le t)
      (by norm_num : 0 ≤ (3/2 : ℝ))).trans hlog) hR).trans_eq
    change 3/2*Real.log 2*(Real.log t/u^2)+C*(Real.log t/u^2) = _*(Real.log t/L^2)
    dsimp only [u]
    field_simp [hL.ne']
    ring

private theorem le_of_right_limit_off_ordinates {f g : ℝ → ℝ} {y T : ℝ}
    (hf : Tendsto f (𝓝[>] T) (𝓝 y)) (hg : ContinuousAt g T)
    (h : ∀ t, T < t → ¬ IsZeroOrdinate t → f t ≤ g t) : y ≤ g T := by
  obtain ⟨δ, hδ, hno⟩ := exists_right_nhd_no_zero_ordinate T
  apply le_of_tendsto_of_tendsto hf (hg.tendsto.mono_left nhdsWithin_le_nhds)
  change ∀ᶠ t in 𝓝[>] T, f t ≤ g t
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun t ht hgt => h t hgt (hno t ⟨hgt, ?_⟩)⟩
  rw [Real.dist_eq, abs_lt] at ht
  linarith [ht.2]

/-- Littlewood's two bounds under RH hold simultaneously at all sufficiently large heights,
including ordinates of zeros with the right-limit convention for the argument. -/
theorem littlewood_argument_bounds_of_rh (hRH : RiemannHypothesisProp) :
    ∃ A B : ℝ, ∀ᶠ t : ℝ in atTop,
      |argumentS t| ≤ A*(Real.log t/Real.log (Real.log t)) ∧
      |integratedArgument t| ≤ B*(Real.log t/Real.log (Real.log t)^2) := by
  obtain ⟨A, B, H⟩ := off_ordinate_argument_bounds hRH
  let D := |Real.pi*integratedArgument 8-horizontalLogMean riemannZeta 8-argZetaPrimitive 8| +
    Real.pi^2/(6*Real.log 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨A, (B+16*D)/Real.pi, ?_⟩
  obtain ⟨T, hT⟩ := tendsto_atTop_atTop.mp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop) 8
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_ge_atTop T] with t ht htT
  have h : 8 ≤ Real.log (Real.log t) := hT t htT
  let L := Real.log (Real.log t)
  have ht₀ : 0 < t := by linarith
  have ht₁ : 1 < t := by linarith
  have hlog := Real.log_pos ht₁
  have hL : 0 < L := by dsimp only [L]; linarith
  have hcont := Real.continuousAt_log ht₀.ne'
  have hcont₂ := (Real.continuousAt_log hlog.ne').comp hcont
  have harg : |argumentS t| ≤ A*(Real.log t/L) := by
    apply le_of_right_limit_off_ordinates (f := fun x => |argumentSApprox x|)
      (g := fun x => A*(Real.log x/Real.log (Real.log x)))
      (argumentSApprox_tendsto_argumentS ht₀).abs (continuousAt_const.mul (hcont.div hcont₂ hL.ne'))
    intro x hx hno
    exact (H (by linarith) (hT x (htT.trans hx.le)) hno).1
  have hmean : |horizontalLogMean riemannZeta t| ≤ B*(Real.log t/L^2) := by
    apply le_of_right_limit_off_ordinates (f := fun x => |horizontalLogMean riemannZeta x|)
      (g := fun x => B*(Real.log x/Real.log (Real.log x)^2))
      ((continuousAt_zeta_horizontalLogMean ht).abs.tendsto.mono_left nhdsWithin_le_nhds)
      (continuousAt_const.mul (hcont.div (hcont₂.pow 2) (pow_ne_zero _ hL.ne')))
    intro x hx hno
    exact (H (by linarith) (hT x (htT.trans hx.le)) hno).2
  obtain ⟨_, _, _, hscale⟩ := littlewood_cutoff ht₁ h
  have h₁₆ : 1 ≤ 16*(Real.log t/L^2) := by
    change 1 ≤ Real.log t/(L/4)^2 at hscale
    convert hscale using 1
    field_simp [hL.ne']
    ring
  have hinc := integratedArgument_increment (a := 8) le_rfl ht
  have heq : Real.pi*integratedArgument t =
      horizontalLogMean riemannZeta t + (Real.pi*integratedArgument 8 -
        horizontalLogMean riemannZeta 8 - argZetaPrimitive 8 + argZetaPrimitive t) := by linarith only [hinc]
  have hrest : |Real.pi*integratedArgument 8-horizontalLogMean riemannZeta 8-
      argZetaPrimitive 8+argZetaPrimitive t| ≤ D :=
    (abs_add_le _ _).trans (add_le_add le_rfl (abs_argZetaPrimitive_le t))
  refine ⟨harg, ?_⟩
  have hb := (abs_add_le _ _).trans (add_le_add hmean hrest)
  rw [← heq, abs_mul, abs_of_pos Real.pi_pos] at hb
  change |integratedArgument t| ≤ (B+16*D)/Real.pi*(Real.log t/L^2)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ Real.pi_pos).mpr (by
    have hd := le_mul_of_one_le_right hD h₁₆
    linarith only [hb, hd])

/-- Under RH the Riemann–von Mangoldt argument S(t) is O(log t / log log t). -/
theorem argumentS_isBigO_log_div_loglog_of_rh (hRH : RiemannHypothesisProp) :
    argumentS =O[atTop] fun t : ℝ => Real.log t/Real.log (Real.log t) := by
  obtain ⟨A, _, H⟩ := littlewood_argument_bounds_of_rh hRH
  apply IsBigO.of_bound A
  filter_upwards [H, eventually_ge_atTop (2 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with t h ht hL
  change 1 ≤ Real.log (Real.log t) at hL
  simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.log_nonneg (one_le_two.trans ht))
    (zero_le_one.trans hL))] using h.1

/-- Under RH the first integral of the zeta argument is O(log t / (log log t)²). -/
theorem integratedArgument_isBigO_log_div_loglog_sq_of_rh (hRH : RiemannHypothesisProp) :
    integratedArgument =O[atTop] fun t : ℝ => Real.log t/Real.log (Real.log t)^2 := by
  obtain ⟨_, B, H⟩ := littlewood_argument_bounds_of_rh hRH
  apply IsBigO.of_bound B
  filter_upwards [H, eventually_ge_atTop (2 : ℝ)] with t h ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.log_nonneg (one_le_two.trans ht))
    (sq_nonneg _))] using h.2

end AnalyticNumberTheory.PrimeDistribution
