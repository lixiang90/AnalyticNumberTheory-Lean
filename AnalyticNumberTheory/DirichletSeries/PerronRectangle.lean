import AnalyticNumberTheory.DirichletSeries.Perron
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Rectangular contour shifts for ordinary Perron integrals -/

noncomputable section

open MeasureTheory Set Complex

namespace AnalyticNumberTheory.DirichletSeries

private lemma integral_inv_sqrt_sq_add_sq_le {σ₀ T : ℝ} (hσ : 0 < σ₀) (hT : 0 < T) :
    ∫ t in (-T)..T, (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ ≤
      2 * Real.sqrt 2 * Real.log (1 + T / σ₀) := by
  have hc_sqrt : Continuous fun t : ℝ => (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ := by
    refine Continuous.inv₀ (Continuous.sqrt (continuous_const.add (continuous_pow 2))) fun t => ?_
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc_abs : Continuous fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|) :=
    continuous_const.div (continuous_const.add continuous_abs) fun t =>
      (add_pos_of_pos_of_nonneg hσ (abs_nonneg t)).ne'
  have hmono : ∫ t in (-T)..T, (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ ≤
      ∫ t in (-T)..T, Real.sqrt 2 / (σ₀ + |t|) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hc_sqrt.intervalIntegrable _ _)
      (hc_abs.intervalIntegrable _ _) fun t _ => ?_
    have hsq_le : (σ₀ + |t|) ^ 2 ≤ 2 * (σ₀ ^ 2 + t ^ 2) := by
      have h1 : 2 * σ₀ * |t| ≤ σ₀ ^ 2 + |t| ^ 2 := by nlinarith [sq_nonneg (σ₀ - |t|)]
      rw [sq_abs] at h1
      nlinarith [sq_abs t]
    have hle : σ₀ + |t| ≤ Real.sqrt 2 * Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
      calc σ₀ + |t| = Real.sqrt ((σ₀ + |t|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (2 * (σ₀ ^ 2 + t ^ 2)) := Real.sqrt_le_sqrt hsq_le
        _ = Real.sqrt 2 * Real.sqrt (σ₀ ^ 2 + t ^ 2) := Real.sqrt_mul zero_le_two _
    have hden_pos : 0 < Real.sqrt (σ₀ ^ 2 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hden2_pos : 0 < σ₀ + |t| := by positivity
    rw [inv_eq_one_div, div_le_div_iff₀ hden_pos hden2_pos]
    linarith
  have heven : ∫ t in (-T)..T, Real.sqrt 2 / (σ₀ + |t|) =
      2 * ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) := by
    have hi_left : IntervalIntegrable (fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|)) volume (-T) 0 :=
      hc_abs.intervalIntegrable _ _
    have hi_right : IntervalIntegrable (fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|)) volume 0 T :=
      hc_abs.intervalIntegrable _ _
    have hadd := (intervalIntegral.integral_add_adjacent_intervals hi_left hi_right).symm
    have hleft : ∫ t in (-T)..0, Real.sqrt 2 / (σ₀ + |t|) =
        ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) := by
      have hcomp := intervalIntegral.integral_comp_neg (fun t : ℝ => Real.sqrt 2 / (σ₀ + |t|))
        (a := 0) (b := T)
      simp only [neg_zero, abs_neg] at hcomp
      rw [← hcomp]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hT.le] at ht
      rw [abs_of_nonneg ht.1]
    have hright : ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + |t|) =
        ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hT.le] at ht
      rw [abs_of_nonneg ht.1]
    rw [hadd, hleft, hright]
    ring
  have heval : ∫ t in (0 : ℝ)..T, Real.sqrt 2 / (σ₀ + t) = Real.sqrt 2 * Real.log (1 + T / σ₀) := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun u : ℝ => Real.sqrt 2 * Real.log (σ₀ + u)) (Real.sqrt 2 / (σ₀ + t)) t := by
      intro t ht
      rw [Set.uIcc_of_le hT.le] at ht
      have hpos : σ₀ + t ≠ 0 := (add_pos_of_pos_of_nonneg hσ ht.1).ne'
      have hsub : HasDerivAt (fun u : ℝ => σ₀ + u) 1 t := (hasDerivAt_id' t).const_add σ₀
      refine (((Real.hasDerivAt_log hpos).comp t hsub).const_mul (Real.sqrt 2)).congr_deriv ?_
      ring
    have hc_pos : ContinuousOn (fun t : ℝ => Real.sqrt 2 / (σ₀ + t)) (Set.uIcc 0 T) := by
      rw [Set.uIcc_of_le hT.le]
      exact continuousOn_const.div (continuousOn_const.add continuousOn_id) fun t ht =>
        (add_pos_of_pos_of_nonneg hσ ht.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_pos.intervalIntegrable]
    rw [add_zero, ← mul_sub, ← Real.log_div (by linarith) hσ.ne']
    congr 2
    field_simp [hσ.ne']
  exact hmono.trans_eq (by rw [heven, heval]; ring)

/-- Bound the three oriented sides of a shifted Perron rectangle by their boundary majorants. -/
theorem norm_shifted_perron_sides_le {G : ℂ → ℂ} {x σ₀ c T B_vert B_horiz : ℝ}
    (hx : 0 < x) (hσ : 0 < σ₀) (hσc : σ₀ ≤ c) (hT : 0 < T)
    (hB_vert : 0 ≤ B_vert) (_hB_horiz : 0 ≤ B_horiz)
    (hcont_vert : ContinuousOn (fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T))
    (hcont_top : ContinuousOn (fun u : ℝ => G ((u : ℂ) + (T : ℂ) * I)) (Set.Icc σ₀ c))
    (hcont_bot : ContinuousOn (fun u : ℝ => G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) (Set.Icc σ₀ c))
    (hbound_vert : ∀ t ∈ Set.Icc (-T) T,
      ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert * x ^ σ₀ / Real.sqrt (σ₀ ^ 2 + t ^ 2))
    (hbound_top : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz * x ^ c / T)
    (hbound_bot : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz * x ^ c / T) :
    ‖(1 / (2 * Real.pi * I)) *
        (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
          (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
          (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)))‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c := by
  have hint_vert : IntervalIntegrable (fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le (by linarith)]
  have hint_top : IntervalIntegrable (fun u : ℝ => G ((u : ℂ) + (T : ℂ) * I)) volume σ₀ c := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hσc]
  have hint_bot : IntervalIntegrable (fun u : ℝ => G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
      volume σ₀ c := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hσc]
  have hnorm_vert : ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤
      2 * Real.sqrt 2 * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) (by linarith : -T ≤ T)
    have hsqrt_cont : Continuous fun t : ℝ => B_vert * x ^ σ₀ * (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ :=
      continuous_const.mul ((Continuous.sqrt (continuous_const.add (continuous_pow 2))).inv₀
        fun t => (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos hσ) (sq_nonneg t))).ne')
    have h2 : ∫ t in (-T)..T, ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t in (-T)..T, B_vert * x ^ σ₀ * (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ := by
      refine intervalIntegral.integral_mono_on (by linarith) hint_vert.norm
        (hsqrt_cont.intervalIntegrable _ _) fun t ht => ?_
      simpa [div_eq_mul_inv] using hbound_vert t ht
    rw [intervalIntegral.integral_const_mul (μ := volume) (B_vert * x ^ σ₀) (fun t : ℝ => (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹)] at h2
    calc ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖
        ≤ B_vert * x ^ σ₀ * ∫ t in (-T)..T, (Real.sqrt (σ₀ ^ 2 + t ^ 2))⁻¹ := h1.trans h2
      _ ≤ B_vert * x ^ σ₀ * (2 * Real.sqrt 2 * Real.log (1 + T / σ₀)) := by
          gcongr
          exact integral_inv_sqrt_sq_add_sq_le hσ hT
      _ = 2 * Real.sqrt 2 * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) := by ring
  have hnorm_top : ‖∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)‖ ≤ (c - σ₀) * (B_horiz * x ^ c / T) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hσc).trans ?_
    refine (intervalIntegral.integral_mono_on hσc hint_top.norm (by simp) hbound_top).trans_eq ?_
    simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hnorm_bot : ‖∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
      (c - σ₀) * (B_horiz * x ^ c / T) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hσc).trans ?_
    refine (intervalIntegral.integral_mono_on hσc hint_bot.norm (by simp) hbound_bot).trans_eq ?_
    simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hnorm_coeff : ‖(1 / (2 * Real.pi * I) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    simp only [one_div, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    norm_num
  have htri : ‖I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
        (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
        (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
      ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖ +
        ‖∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)‖ +
        ‖∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
    have hI : ‖I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I))‖ =
        ‖∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have h1 := norm_sub_le
      (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) + ∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I))
      (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
    have h2 := norm_add_le
      (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)))
      (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I))
    linarith
  rw [norm_mul, hnorm_coeff]
  calc (2 * Real.pi)⁻¹ *
        ‖I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
          (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
          (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖
      ≤ (2 * Real.pi)⁻¹ *
          (2 * Real.sqrt 2 * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
            (c - σ₀) * (B_horiz * x ^ c / T) +
            (c - σ₀) * (B_horiz * x ^ c / T)) := by
        gcongr
        linarith
    _ = (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
          ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c := by
        field_simp [Real.pi_pos.ne', hT.ne']
        ring

/-- Shift Perron's integral across a rectangle on which its Dirichlet series
has a holomorphic continuation. The vertical and horizontal costs can be estimated
separately. Only agreement on the original integration line is required. -/
theorem norm_dirichletContourIntegral_le_of_rectangle {a : ℕ → ℂ} {F : ℂ → ℂ}
    {x σ₀ c T B_vert B_horiz : ℝ} (hx : 1 ≤ x) (hσ : 0 < σ₀) (hσc : σ₀ ≤ c)
    (hT : 0 < T) (hB_vert : 0 ≤ B_vert) (hB_horiz : 0 ≤ B_horiz)
    (hF : DifferentiableOn ℂ F (Set.Icc σ₀ c ×ℂ Set.Icc (-T) T))
    (hright : ∀ t : ℝ, LSeries a ((c : ℂ) + (t : ℂ) * I) = F ((c : ℂ) + (t : ℂ) * I))
    (hvert : ∀ t ∈ Set.Icc (-T) T, ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert)
    (htop : ∀ u ∈ Set.Icc σ₀ c, ‖F ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz)
    (hbot : ∀ u ∈ Set.Icc σ₀ c, ‖F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz) :
    ‖dirichletContourIntegral a x c T‖ ≤
      (Real.sqrt 2 / Real.pi) * B_vert * x ^ σ₀ * Real.log (1 + T / σ₀) +
        ((c - σ₀) / (Real.pi * T)) * B_horiz * x ^ c := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  let G : ℂ → ℂ := fun s => F s * (x : ℂ) ^ s / s
  have hdiff_G : DifferentiableOn ℂ G (Set.Icc σ₀ c ×ℂ Set.Icc (-T) T) := by
    refine (hF.mul (differentiableOn_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx_pos.ne')))).div
      differentiableOn_id ?_
    intro s hs hzero
    have hre := hs.1.1
    simp [hzero] at hre
    linarith
  let z : ℂ := (σ₀ : ℂ) + ((-T : ℝ) : ℂ) * I
  let w : ℂ := (c : ℂ) + (T : ℂ) * I
  have hrect_eq : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) =
      Set.Icc σ₀ c ×ℂ Set.Icc (-T) T := by
    have hzre : z.re = σ₀ := by simp [z]
    have hzim : z.im = -T := by simp [z]
    have hwre : w.re = c := by simp [w]
    have hwim : w.im = T := by simp [w]
    rw [hzre, hzim, hwre, hwim, Set.uIcc_of_le hσc, Set.uIcc_of_le (by linarith)]
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G z w
    (by rwa [hrect_eq])
  simp only [show z.re = σ₀ by simp [z], show z.im = -T by simp [z],
    show w.re = c by simp [w], show w.im = T by simp [w], smul_eq_mul] at hcauchy
  have hright_eq :
      (1 / (2 * Real.pi * I)) * (I * ∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) =
        dirichletContourIntegral
          a x c T := by
    rw [← dirichletContourIntegral_eq_div_two_pi_mul_I]
    refine congrArg (fun z : ℂ => (1 / (2 * Real.pi * I)) * (I * z)) ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    change F _ * _ / _ = LSeries a _ * _ / _
    rw [hright t]
  have hshifted_eq :
      dirichletContourIntegral
          a x c T =
        (1 / (2 * Real.pi * I)) *
          (I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
            (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
            (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
    have halg : I * (∫ t in (-T)..T, G ((c : ℂ) + (t : ℂ) * I)) =
        I * (∫ t in (-T)..T, G ((σ₀ : ℂ) + (t : ℂ) * I)) +
          (∫ u in σ₀..c, G ((u : ℂ) + (T : ℂ) * I)) -
          (∫ u in σ₀..c, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
      linear_combination hcauchy
    rw [← hright_eq, halg]
  have hcont_G : ContinuousOn G (Set.Icc σ₀ c ×ℂ Set.Icc (-T) T) := hdiff_G.continuousOn
  have hcont_vert : ContinuousOn (fun t : ℝ => G ((σ₀ : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
    refine hcont_G.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      fun t ht => ?_
    refine ⟨?_, ?_⟩
    · simp [hσc]
    · simpa using ht
  have hcont_top : ContinuousOn (fun u : ℝ => G ((u : ℂ) + (T : ℂ) * I)) (Set.Icc σ₀ c) := by
    refine hcont_G.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      fun u hu => ?_
    refine ⟨?_, ?_⟩
    · simpa using hu
    · simp [hT.le]
  have hcont_bot : ContinuousOn (fun u : ℝ => G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) (Set.Icc σ₀ c) := by
    refine hcont_G.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      fun u hu => ?_
    refine ⟨?_, ?_⟩
    · simpa using hu
    · simp [hT.le]
  have hbound_vert : ∀ t ∈ Set.Icc (-T) T,
      ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ B_vert * x ^ σ₀ / Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
    intro t ht
    have hnorm_s : ‖(σ₀ : ℂ) + (t : ℂ) * I‖ = Real.sqrt (σ₀ ^ 2 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      simp [pow_two]
    have hnorm_x : ‖(x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I)‖ = x ^ σ₀ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp
    dsimp [G]
    rw [norm_div, norm_mul, hnorm_s, hnorm_x]
    gcongr
    exact hvert t ht
  have hbound_top : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + (T : ℂ) * I)‖ ≤ B_horiz * x ^ c / T := by
    intro u hu
    have hnorm_s : T ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := by
      have him : ((u : ℂ) + (T : ℂ) * I).im = T := by simp
      calc T = |((u : ℂ) + (T : ℂ) * I).im| := by rw [him, abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hnorm_x : ‖(x : ℂ) ^ ((u : ℂ) + (T : ℂ) * I)‖ ≤ x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le hx hu.2
    dsimp [G]
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul (htop u hu) hnorm_x (norm_nonneg _) hB_horiz) hT hnorm_s
  have hbound_bot : ∀ u ∈ Set.Icc σ₀ c,
      ‖G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B_horiz * x ^ c / T := by
    intro u hu
    have hnorm_s : T ≤ ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := by
      have him : ((u : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
      calc T = |((u : ℂ) + ((-T : ℝ) : ℂ) * I).im| := by rw [him, abs_neg, abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hnorm_x : ‖(x : ℂ) ^ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le hx hu.2
    dsimp [G]
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul (hbot u hu) hnorm_x (norm_nonneg _) hB_horiz) hT hnorm_s
  rw [hshifted_eq]
  exact norm_shifted_perron_sides_le hx_pos hσ hσc hT hB_vert hB_horiz
    hcont_vert hcont_top hcont_bot hbound_vert hbound_top hbound_bot

end AnalyticNumberTheory.DirichletSeries
