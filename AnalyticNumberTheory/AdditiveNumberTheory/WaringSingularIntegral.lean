import AnalyticNumberTheory.AdditiveNumberTheory.LinearPhaseIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The oscillatory integral for Waring's problem

The normalized integral over one variable decays like `|β|^(-1/k)`.
This makes the Fourier integral in `s` variables absolutely convergent for `s > k`.
-/

namespace AnalyticNumberTheory.AdditiveNumberTheory

open MeasureTheory Set Real Filter
open scoped Topology

/-- The continuous counterpart of a Weyl sum, with positive Fourier phase. -/
noncomputable def waringOscillatoryIntegral (k : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, e (β * u ^ k)

theorem norm_waringOscillatoryIntegral_le_one (k : ℕ) (β : ℝ) :
    ‖waringOscillatoryIntegral k β‖ ≤ 1 := by
  calc
    _ ≤ ∫ u in (0 : ℝ)..1, ‖e (β * u ^ k)‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = _ := by simp [norm_e]

/-- Integrating by parts against a decreasing nonnegative weight costs at
most twice its initial value when the complex primitive has modulus one. -/
private theorem norm_weighted_derivative_le {a b : ℝ} (hab : a ≤ b)
    (g g' : ℝ → ℝ) (f f' : ℝ → ℂ)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hgi : IntervalIntegrable g' volume a b) (hfi : IntervalIntegrable f' volume a b)
    (hgn : ∀ x ∈ uIcc a b, 0 ≤ g x) (hgn' : ∀ x ∈ uIcc a b, g' x ≤ 0)
    (hfn : ∀ x, ‖f x‖ = 1) : ‖∫ x in a..b, (g x : ℂ) * f' x‖ ≤ 2 * g a := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (fun x hx => (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hg x hx)).hasDerivWithinAt)
    (fun x hx => (hf x hx).hasDerivWithinAt)
    ⟨Complex.ofRealCLM.integrable_comp hgi.1, Complex.ofRealCLM.integrable_comp hgi.2⟩ hfi
  have hdiff : ‖∫ x in a..b, (g' x : ℂ) * f x‖ ≤ g a - g b := by
    calc
      _ ≤ ∫ x in a..b, ‖(g' x : ℂ) * f x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, -g' x := intervalIntegral.integral_congr fun x hx => by
        simp [hfn, abs_of_nonpos (hgn' x hx)]
      _ = _ := by rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt hg hgi]; ring
  change (∫ x in a..b, (g x : ℂ) * f' x) = _ at hparts
  rw [hparts]
  calc
    _ ≤ ‖(g b : ℂ) * f b - (g a : ℂ) * f a‖ + ‖∫ x in a..b, (g' x : ℂ) * f x‖ := norm_sub_le _ _
    _ ≤ (‖(g b : ℂ) * f b‖ + ‖(g a : ℂ) * f a‖) + (g a - g b) := add_le_add (norm_sub_le _ _) hdiff
    _ = _ := by simp [hfn, abs_of_nonneg (hgn a left_mem_uIcc), abs_of_nonneg (hgn b right_mem_uIcc)]; ring

/-- Over `[1,B]` the integral with unit-sized frequency has a bound independent of `B`.
The weight `x^(-m)` cancels the derivative of the power phase `x^(m+1)`. -/
private theorem norm_integral_power_tail_le (m : ℕ) {B σ : ℝ} (hB : 1 ≤ B) (hσ : 1 ≤ |σ|) :
    ‖∫ x in (1 : ℝ)..B, e (σ * x ^ (m + 1))‖ ≤ 2 := by
  let f (x : ℝ) := e (σ * x ^ (m + 1))
  let c : ℂ := (2 * Real.pi * Complex.I) * (σ : ℂ) * ((m + 1 : ℕ) : ℂ)
  let g (x : ℝ) := x ^ (-(m : ℝ))
  let g' (x : ℝ) := -(m : ℝ) * x ^ (-(m : ℝ) - 1)
  let f' (x : ℝ) := c * (x : ℂ) ^ m * f x
  have hpos (x : ℝ) (hx : x ∈ uIcc 1 B) : 0 < x := by rw [uIcc_of_le hB] at hx; exact zero_lt_one.trans_le hx.1
  have hg (x : ℝ) (hx : x ∈ uIcc 1 B) : HasDerivAt g (g' x) x :=
    Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')
  have hf (x : ℝ) : HasDerivAt f (f' x) x := by
    have h := (hasDerivAt_e (σ * x ^ (m + 1))).scomp x ((hasDerivAt_pow (m + 1) x).const_mul σ)
    apply h.congr_deriv
    simp [f', c, f, Algebra.smul_def]
    push_cast
    ring
  have hgi : IntervalIntegrable g' volume 1 B := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => Or.inl (hpos x hx).ne')
  have hfi : IntervalIntegrable f' volume 1 B := by
    have hcf : Continuous f := continuous_e.comp (by fun_prop : Continuous (fun x : ℝ => σ * x ^ (m + 1)))
    exact ((continuous_const.mul (Complex.continuous_ofReal.pow _)).mul hcf).intervalIntegrable _ _
  have h := norm_weighted_derivative_le hB g g' f f' hg (fun x _ => hf x) hgi hfi
    (fun x hx => Real.rpow_nonneg (hpos x hx).le _)
    (fun x hx => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
      (Real.rpow_nonneg (hpos x hx).le _)) (fun x => norm_e _)
  have heq : (∫ x in (1 : ℝ)..B, (g x : ℂ) * f' x) = c * ∫ x in (1 : ℝ)..B, f x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos x hx).ne'
    simp [g, f', hx0, mul_comm, mul_left_comm, mul_assoc]
  rw [heq, norm_mul] at h
  have hc : 1 ≤ ‖c‖ := by
    simp only [c, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg Real.pi_pos.le, Complex.norm_ofNat, Complex.norm_natCast]
    have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith [Real.two_le_pi]) hσ) hm
  calc
    _ ≤ ‖c‖ * ‖∫ x in (1 : ℝ)..B, f x‖ := le_mul_of_one_le_left (norm_nonneg _) hc
    _ ≤ 2 := by simpa [g] using h

/-- Rescaling the phase and integrating by parts on the rescaled tail give
`|v(β)| ≤ 3 |β|^(-1/k)` for `|β| ≥ 1`. -/
theorem norm_waringOscillatoryIntegral_le_rpow {k : ℕ} (hk : 0 < k) {β : ℝ} (hβ : 1 ≤ |β|) :
    ‖waringOscillatoryIntegral k β‖ ≤ 3 * |β| ^ (-(1 / (k : ℝ))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let k := m + 1
  have hkR : 0 < (k : ℝ) := by dsimp [k]; positivity
  have hβpos := zero_lt_one.trans_le hβ
  let B := |β| ^ (1 / (k : ℝ))
  let σ := β / |β|
  have hB : 1 ≤ B := Real.one_le_rpow hβ (by positivity)
  have hσ : |σ| = 1 := by simp [σ, abs_div, div_self hβpos.ne']
  have hBk : B ^ k = |β| := by
    rw [← Real.rpow_mul_natCast hβpos.le, one_div_mul_cancel hkR.ne', Real.rpow_one]
  have hscale : waringOscillatoryIntegral k β = B⁻¹ • ∫ x in (0 : ℝ)..B, e (σ * x ^ k) := by
    convert intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
      (fun x : ℝ => e (σ * x ^ k)) (zero_lt_one.trans_le hB).ne' using 1
    · refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [mul_pow, hBk, σ, ← mul_assoc, div_mul_cancel₀ β hβpos.ne']
    · simp
  have hc : Continuous (fun x : ℝ => e (σ * x ^ k)) := continuous_e.comp (by fun_prop : Continuous (fun x : ℝ => σ * x ^ k))
  have hbound : ‖∫ x in (0 : ℝ)..B, e (σ * x ^ k)‖ ≤ 3 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 B)]
    exact (norm_add_le _ _).trans ((add_le_add (norm_waringOscillatoryIntegral_le_one k σ)
      (norm_integral_power_tail_le m hB hσ.ge)).trans (by norm_num))
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hB)),
    Real.rpow_neg hβpos.le, mul_comm (3 : ℝ)]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (zero_le_one.trans hB))

theorem stronglyMeasurable_waringOscillatoryIntegral (k : ℕ) : StronglyMeasurable (waringOscillatoryIntegral k) := by
  have h : Continuous (fun p : ℝ × ℝ => e (p.1 * p.2 ^ k)) :=
    continuous_e.comp (continuous_fst.mul (continuous_snd.pow _))
  change StronglyMeasurable (fun β : ℝ => ∫ u in (0 : ℝ)..1, e (β * u ^ k))
  simpa only [intervalIntegral.integral_of_le zero_le_one] using
    h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))

/-- Absolute integrability of the `s`th power of the one-variable Fourier factor. -/
theorem integrable_waringOscillatoryIntegral_pow {k s : ℕ} (hk : 0 < k) (hks : k < s) :
    Integrable (fun β : ℝ => waringOscillatoryIntegral k β ^ s) := by
  let F (β : ℝ) := waringOscillatoryIntegral k β ^ s
  have hm : StronglyMeasurable F := (stronglyMeasurable_waringOscillatoryIntegral k).pow s
  let G (β : ℝ) := 3 ^ s * |β| ^ (-(s : ℝ) / k)
  have hbound (β : ℝ) (hβ : 1 ≤ |β|) : ‖F β‖ ≤ G β := by
    simp only [F, norm_pow]
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_waringOscillatoryIntegral_le_rpow hk hβ) s).trans_eq ?_
    simp only [G, mul_pow, ← Real.rpow_mul_natCast (abs_nonneg _)]
    congr 2
    ring
  have hexp : -(s : ℝ) / k < -1 := (div_lt_iff₀ (Nat.cast_pos.mpr hk)).mpr (by exact_mod_cast (by omega : -(s : ℤ) < -1 * k))
  have hpos : IntegrableOn G (Ioi 1) := by
    apply IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul (3 ^ s)) _ measurableSet_Ioi
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    simp [G, abs_of_nonneg (zero_le_one.trans hx1.le)]
  have hneg : IntegrableOn G (Iio (-1)) := by
    have hpos' : IntegrableOn G (Ioi (-(-1 : ℝ))) := by simpa using hpos
    simpa only [G, abs_neg] using (IntegrableOn.comp_neg_Iio hpos')
  have hFpos : IntegrableOn F (Ioi 1) := hpos.mono' hm.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => hbound x ((le_of_lt hx).trans (le_abs_self _)))
  have hFneg : IntegrableOn F (Iio (-1)) := hneg.mono' hm.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Iio fun x hx => hbound x (by
      have : x < -1 := hx
      linarith [neg_le_abs x]))
  have hmid : IntegrableOn F (Icc (-1) 1) := by
    refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simpa [F] using pow_le_one₀ (norm_nonneg _) (norm_waringOscillatoryIntegral_le_one k x) (n := s)
  have h := (hFneg.union hmid).union hFpos
  rwa [Iio_union_Icc_eq_Iic (by norm_num : (-1 : ℝ) ≤ 1), Iic_union_Ioi, integrableOn_univ] at h

/-- The Fourier singular integral at a real output level, with unit cutoff in each variable. -/
noncomputable def waringSingularIntegral (s k : ℕ) (t : ℝ) : ℂ :=
  ∫ β : ℝ, waringOscillatoryIntegral k β ^ s * e (-β * t)

/-- Absolute convergence of the Fourier integrand with the output phase at level `t`. -/
theorem integrable_waringSingularIntegrand {k s : ℕ} (hk : 0 < k) (hks : k < s) (t : ℝ) :
    Integrable (fun β : ℝ => waringOscillatoryIntegral k β ^ s * e (-β * t)) := by
  apply (integrable_waringOscillatoryIntegral_pow hk hks).norm.mono'
  · exact ((stronglyMeasurable_waringOscillatoryIntegral k).pow s |>.mul
      (continuous_e.comp (continuous_neg.mul continuous_const)).stronglyMeasurable).aestronglyMeasurable
  · exact .of_forall fun β => by simp [norm_e]

end AnalyticNumberTheory.AdditiveNumberTheory
