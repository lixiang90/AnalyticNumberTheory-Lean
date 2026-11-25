import AnalyticNumberTheory.AnalyticTools.SymmetricIntegrals
import AnalyticNumberTheory.DirichletSeries.Perron
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # A uniform bound for the truncated Perron kernel

Pairing the integrals at positive and negative heights controls the
oscillatory part uniformly as the argument approaches the jump at one.
-/
noncomputable section
open MeasureTheory Set Filter
open Complex (I)
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletSeries

private lemma continuous_trig_div_sq {c a b α : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ ↦
      (a * Real.cos (α * t) + b * t * Real.sin (α * t)) / (c ^ 2 + t ^ 2) := by
  have hcos : Continuous fun t : ℝ ↦ Real.cos (α * t) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin : Continuous fun t : ℝ ↦ Real.sin (α * t) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hnum : Continuous fun t : ℝ ↦ a * Real.cos (α * t) + b * t * Real.sin (α * t) :=
    (continuous_const.mul hcos).add ((continuous_const.mul continuous_id).mul hsin)
  have hden : Continuous fun t : ℝ ↦ c ^ 2 + t ^ 2 :=
    continuous_const.add (continuous_id.pow 2)
  exact hnum.div hden fun t ↦ by positivity

private lemma continuous_trig_div_sq' {c a b α : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ ↦
      (a * Real.sin (α * t) + b * t * Real.cos (α * t)) / (c ^ 2 + t ^ 2) := by
  have hcos : Continuous fun t : ℝ ↦ Real.cos (α * t) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin : Continuous fun t : ℝ ↦ Real.sin (α * t) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hnum : Continuous fun t : ℝ ↦ a * Real.sin (α * t) + b * t * Real.cos (α * t) :=
    (continuous_const.mul hsin).add ((continuous_const.mul continuous_id).mul hcos)
  have hden : Continuous fun t : ℝ ↦ c ^ 2 + t ^ 2 :=
    continuous_const.add (continuous_id.pow 2)
  exact hnum.div hden fun t ↦ by positivity

private lemma perronKernel_eq_real_cos_sin {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) :
    perronKernel y c T =
      (((y ^ c / Real.pi) *
        ∫ t in (0 : ℝ)..T,
          (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) / (c ^ 2 + t ^ 2) :
          ℝ) : ℂ) := by
  let α : ℝ := Real.log y
  let f : ℝ → ℝ := fun t ↦ (c * Real.cos (α * t) + t * Real.sin (α * t)) / (c ^ 2 + t ^ 2)
  let g : ℝ → ℝ := fun t ↦ (c * Real.sin (α * t) - t * Real.cos (α * t)) / (c ^ 2 + t ^ 2)
  have hden_pos : ∀ t : ℝ, 0 < c ^ 2 + t ^ 2 := fun t ↦ by positivity
  have hf_cont : Continuous f := by
    simpa [f] using (continuous_trig_div_sq (a := c) (b := 1) (α := α) hc)
  have hg_cont : Continuous g := by
    have h := continuous_trig_div_sq' (a := c) (b := -1) (α := α) hc
    refine h.congr fun t ↦ ?_
    dsimp [g]
    ring
  have hf_even : ∀ t : ℝ, f (-t) = f t := fun t ↦ by
    dsimp [f]
    simp only [mul_neg, Real.cos_neg, Real.sin_neg, neg_sq]
    ring
  have hg_odd : ∀ t : ℝ, g (-t) = -g t := fun t ↦ by
    dsimp [g]
    simp only [mul_neg, Real.cos_neg, Real.sin_neg, neg_sq]
    ring
  have hpt : ∀ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) =
        ((y ^ c : ℝ) : ℂ) * (((f t : ℝ) : ℂ) + ((g t : ℝ) : ℂ) * I) := by
    intro t
    have hyc0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hpow : (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) =
        ((y ^ c : ℝ) : ℂ) * ((Real.cos (α * t) : ℂ) + (Real.sin (α * t) : ℂ) * I) := by
      rw [Complex.cpow_add _ _ hyc0, Complex.ofReal_cpow hy.le c]
      congr 1
      rw [Complex.cpow_def_of_ne_zero hyc0, ← Complex.ofReal_log hy.le]
      have harg : (Real.log y : ℂ) * ((t : ℂ) * I) = (((α * t : ℝ) : ℂ) * I) := by
        dsimp [α]; push_cast; ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hct0 : (c : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hinv : ((c : ℂ) + (t : ℂ) * I)⁻¹ =
        ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) + ((-t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
      rw [inv_eq_one_div, div_eq_iff hct0]
      symm
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
          Complex.add_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re]
        have hd0 : c ^ 2 + t ^ 2 ≠ 0 := (hden_pos t).ne'
        field_simp [hd0]
        ring
      · simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.mul_re,
          Complex.add_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im]
        ring
    rw [div_eq_mul_inv, hpow, hinv]
    apply Complex.ext
    · simp only [f, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.mul_im, Complex.add_im]
      ring
    · simp only [g, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.mul_re, Complex.add_re]
      ring
  have hint_eq :
      (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) =
        ((y ^ c : ℝ) : ℂ) *
          (((∫ t in (-T)..T, f t : ℝ) : ℂ) + ((∫ t in (-T)..T, g t : ℝ) : ℂ) * I) := by
    have hcongr :
        (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) =
          ((y ^ c : ℝ) : ℂ) * ∫ t in (-T)..T, (((f t : ℝ) : ℂ) + ((g t : ℝ) : ℂ) * I) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ ↦ hpt t
    rw [hcongr]
    congr 1
    have hf_c : IntervalIntegrable (fun t : ℝ ↦ (f t : ℂ)) volume (-T) T :=
      (Complex.continuous_ofReal.comp hf_cont).intervalIntegrable (-T) T
    have hg_c : IntervalIntegrable (fun t : ℝ ↦ ((g t : ℂ) * I)) volume (-T) T :=
      ((Complex.continuous_ofReal.comp hg_cont).mul continuous_const).intervalIntegrable (-T) T
    rw [intervalIntegral.integral_add hf_c hg_c]
    congr 1
    · exact intervalIntegral.integral_ofReal
    · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  rw [perronKernel, hint_eq, integral_odd_real_zero hg_odd T, integral_even_real_eq_two_mul hf_cont
    hf_even T]
  dsimp [f, α]
  push_cast
  rw [zero_mul, add_zero]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi0]

private lemma integral_cos_div_le_pi_div_two {α c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    |∫ t in (0 : ℝ)..T, c * Real.cos (α * t) / (c ^ 2 + t ^ 2)| ≤ Real.pi / 2 := by
  have hden_pos : ∀ t : ℝ, 0 < c ^ 2 + t ^ 2 := fun t ↦ by positivity
  have hcont1 : Continuous fun t : ℝ ↦ c * Real.cos (α * t) / (c ^ 2 + t ^ 2) := by
    have h := continuous_trig_div_sq (a := c) (b := 0) (α := α) hc
    refine h.congr fun t ↦ ?_
    ring
  have hcont2 : Continuous fun t : ℝ ↦ c / (c ^ 2 + t ^ 2) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) fun t ↦ (hden_pos t).ne'
  have hnorm_le :
      |∫ t in (0 : ℝ)..T, c * Real.cos (α * t) / (c ^ 2 + t ^ 2)| ≤
        ∫ t in (0 : ℝ)..T, |c * Real.cos (α * t) / (c ^ 2 + t ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hT.le
  have hmono :
      (∫ t in (0 : ℝ)..T, |c * Real.cos (α * t) / (c ^ 2 + t ^ 2)|) ≤
        ∫ t in (0 : ℝ)..T, c / (c ^ 2 + t ^ 2) := by
    refine intervalIntegral.integral_mono_on hT.le
      (hcont1.abs.intervalIntegrable 0 T) (hcont2.intervalIntegrable 0 T) fun t _ ↦ ?_
    rw [abs_div, abs_mul, abs_of_pos hc, abs_of_pos (hden_pos t)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right hc.le (Real.abs_cos_le_one _)) (hden_pos t).le
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u : ℝ ↦ Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
    intro t _
    have hsub : HasDerivAt (fun u : ℝ ↦ u / c) (1 / c) t := by
      simpa using (hasDerivAt_id' t).div_const c
    have hcomp := (Real.hasDerivAt_arctan (t / c)).comp t hsub
    refine hcomp.congr_deriv ?_
    have hden_sub : 1 + (t / c) ^ 2 ≠ 0 := by positivity
    field_simp [hc.ne', hden_sub]
  have hint_eq : ∫ t in (0 : ℝ)..T, c / (c ^ 2 + t ^ 2) = Real.arctan (T / c) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont2.intervalIntegrable 0 T)
    simpa [zero_div, Real.arctan_zero] using h
  have harctan : Real.arctan (T / c) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two (T / c)).le
  exact (hnorm_le.trans hmono).trans (hint_eq.le.trans harctan)

private lemma integral_sin_div_pos_le_four {a c T : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
    |∫ t in (0 : ℝ)..T, t * Real.sin (a * t) / (c ^ 2 + t ^ 2)| ≤ 4 := by
  have hden_pos : ∀ t : ℝ, 0 < c ^ 2 + t ^ 2 := fun t ↦ by positivity
  let f : ℝ → ℝ := fun t ↦ t * Real.sin (a * t) / (c ^ 2 + t ^ 2)
  have hf_cont : Continuous f := by
    have h := continuous_trig_div_sq (a := 0) (b := 1) (α := a) hc
    refine h.congr fun t ↦ ?_
    dsimp [f]
    ring
  let u : ℝ := min T (1 / a)
  have hu_pos : 0 < u := lt_min hT (one_div_pos.mpr ha)
  have hu_le_T : u ≤ T := min_le_left T (1 / a)
  have hu_le_inv : u ≤ 1 / a := min_le_right T (1 / a)
  have hsplit :
      ∫ t in (0 : ℝ)..T, f t = (∫ t in (0 : ℝ)..u, f t) + ∫ t in u..T, f t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable 0 u) (hf_cont.intervalIntegrable u T)).symm
  have hpart1 : |∫ t in (0 : ℝ)..u, f t| ≤ 1 := by
    have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := f) hu_pos.le
    have h2 : (∫ t in (0 : ℝ)..u, |f t|) ≤ ∫ _ in (0 : ℝ)..u, a := by
      refine intervalIntegral.integral_mono_on hu_pos.le
        (hf_cont.abs.intervalIntegrable 0 u) intervalIntegrable_const fun t ht ↦ ?_
      dsimp [f]
      rw [abs_div, abs_mul, abs_of_nonneg ht.1, abs_of_pos (hden_pos t)]
      have hsin : |Real.sin (a * t)| ≤ a * t := by
        calc
          |Real.sin (a * t)| ≤ |a * t| := Real.abs_sin_le_abs
          _ = a * t := abs_of_nonneg (mul_nonneg ha.le ht.1)
      have hsq : t ^ 2 ≤ c ^ 2 + t ^ 2 := le_add_of_nonneg_left (sq_nonneg c)
      calc
        t * |Real.sin (a * t)| / (c ^ 2 + t ^ 2)
            ≤ t * (a * t) / (c ^ 2 + t ^ 2) := by
          have ht0 : 0 ≤ t := ht.1
          gcongr
        _ = a * (t ^ 2 / (c ^ 2 + t ^ 2)) := by ring
        _ ≤ a * 1 := by gcongr; exact (div_le_one (hden_pos t)).mpr hsq
        _ = a := mul_one a
    have hconst : (∫ _ in (0 : ℝ)..u, a) = u * a := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    have hua : u * a ≤ 1 := by
      calc
        u * a ≤ (1 / a) * a := mul_le_mul_of_nonneg_right hu_le_inv ha.le
        _ = 1 := one_div_mul_cancel ha.ne'
    exact (h1.trans h2).trans (hconst.le.trans hua)
  have hpart2 : |∫ t in u..T, f t| ≤ 3 := by
    by_cases hTu : T ≤ 1 / a
    · have hu_eq : u = T := min_eq_left hTu
      rw [hu_eq, intervalIntegral.integral_same, abs_zero]
      norm_num
    · have hinv_lt : 1 / a < T := lt_of_not_ge hTu
      have hu_eq : u = 1 / a := min_eq_right hinv_lt.le
      have huT : u ≤ T := hu_le_T
      let φ : ℝ → ℝ := fun t ↦ t / (c ^ 2 + t ^ 2)
      let φ' : ℝ → ℝ := fun t ↦ (c ^ 2 - t ^ 2) / (c ^ 2 + t ^ 2) ^ 2
      let ψ : ℝ → ℝ := fun t ↦ -Real.cos (a * t) / a
      let ψ' : ℝ → ℝ := fun t ↦ Real.sin (a * t)
      have hφ : ∀ t ∈ Set.uIcc u T, HasDerivAt φ (φ' t) t := by
        intro t _
        have hden_deriv : HasDerivAt (fun s : ℝ ↦ c ^ 2 + s ^ 2) (2 * t) t := by
          have h := (hasDerivAt_pow 2 t).const_add (c ^ 2)
          refine h.congr_deriv ?_
          ring
        have hdiv := (hasDerivAt_id' t).div hden_deriv (hden_pos t).ne'
        refine hdiv.congr_deriv ?_
        dsimp [φ']
        ring
      have hψ : ∀ t ∈ Set.uIcc u T, HasDerivAt ψ (ψ' t) t := by
        intro t _
        have hlin : HasDerivAt (fun s : ℝ ↦ a * s) a t := by
          simpa using (hasDerivAt_id' t).const_mul a
        have hcos : HasDerivAt (fun s : ℝ ↦ Real.cos (a * s)) (-Real.sin (a * t) * a) t :=
          (Real.hasDerivAt_cos (a * t)).comp t hlin
        have hscaled := (hcos.neg).div_const a
        refine hscaled.congr_deriv ?_
        dsimp [ψ']
        field_simp [ha.ne']
      have hφ'_cont : Continuous φ' :=
        (continuous_const.sub (continuous_id.pow 2)).div
          ((continuous_const.add (continuous_id.pow 2)).pow 2) fun t ↦
            pow_ne_zero 2 (hden_pos t).ne'
      have hψ'_cont : Continuous ψ' :=
        Real.continuous_sin.comp (continuous_const.mul continuous_id)
      have hψ_cont : Continuous ψ :=
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).neg).div_const a
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hφ hψ
        (hφ'_cont.intervalIntegrable u T) (hψ'_cont.intervalIntegrable u T)
      have hf_eq : ∫ t in u..T, f t = ∫ t in u..T, φ t * ψ' t := by
        refine intervalIntegral.integral_congr fun t _ ↦ ?_
        dsimp [f, φ, ψ']
        ring
      rw [hf_eq, hibp]
      have hbd_val : ∀ t : ℝ, u ≤ t → |φ t * ψ t| ≤ 1 := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le hu_pos ht
        have hφ_le : |φ t| ≤ a := by
          dsimp [φ]
          rw [abs_of_nonneg (div_nonneg ht_pos.le (hden_pos t).le)]
          have h1 : t / (c ^ 2 + t ^ 2) ≤ t / t ^ 2 :=
            div_le_div_of_nonneg_left ht_pos.le (sq_pos_of_pos ht_pos)
              (le_add_of_nonneg_left (sq_nonneg c))
          have h2 : t / t ^ 2 = 1 / t := by
            field_simp [ht_pos.ne']
          have h3 : 1 / t ≤ 1 / u := one_div_le_one_div_of_le hu_pos ht
          have h4 : 1 / u = a := by rw [hu_eq, one_div_one_div]
          exact h1.trans (h2 ▸ h3.trans_eq h4)
        have hψ_le : |ψ t| ≤ 1 / a := by
          dsimp [ψ]
          rw [abs_div, abs_neg, abs_of_pos ha]
          exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) ha.le
        rw [abs_mul]
        calc
          |φ t| * |ψ t| ≤ a * (1 / a) := mul_le_mul hφ_le hψ_le (abs_nonneg _) ha.le
          _ = 1 := mul_one_div_cancel ha.ne'
      have hrem : |∫ t in u..T, φ' t * ψ t| ≤ 1 := by
        have hcont_rem : Continuous fun t : ℝ ↦ φ' t * ψ t := hφ'_cont.mul hψ_cont
        have hcont_invsq : ContinuousOn (fun t : ℝ ↦ (1 / a) * (t ^ 2)⁻¹) (Set.Icc u T) := by
          refine ContinuousOn.mul continuousOn_const
            (ContinuousOn.inv₀ (continuous_id.pow 2).continuousOn fun t ht ↦ ?_)
          exact pow_ne_zero 2 (lt_of_lt_of_le hu_pos ht.1).ne'
        have hint_invsq : IntervalIntegrable (fun t : ℝ ↦ (1 / a) * (t ^ 2)⁻¹) volume u T :=
          hcont_invsq.intervalIntegrable_of_Icc huT
        have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun t ↦ φ' t * ψ t) huT
        have h2 : (∫ t in u..T, |φ' t * ψ t|) ≤ ∫ t in u..T, (1 / a) * (t ^ 2)⁻¹ := by
          refine intervalIntegral.integral_mono_on huT
            (hcont_rem.abs.intervalIntegrable u T) hint_invsq fun t ht ↦ ?_
          have ht_pos : 0 < t := lt_of_lt_of_le hu_pos ht.1
          have hφ'_le : |φ' t| ≤ (t ^ 2)⁻¹ := by
            dsimp [φ']
            rw [abs_div, abs_of_pos (pow_pos (hden_pos t) 2)]
            have hnum : |c ^ 2 - t ^ 2| ≤ c ^ 2 + t ^ 2 := by
              rw [abs_sub_le_iff]
              constructor <;> linarith [sq_nonneg c, sq_nonneg t]
            calc
              |c ^ 2 - t ^ 2| / (c ^ 2 + t ^ 2) ^ 2
                  ≤ (c ^ 2 + t ^ 2) / (c ^ 2 + t ^ 2) ^ 2 := by gcongr
              _ = (c ^ 2 + t ^ 2)⁻¹ := by
                  have hd0 : c ^ 2 + t ^ 2 ≠ 0 := (hden_pos t).ne'
                  field_simp [hd0]
              _ ≤ (t ^ 2)⁻¹ :=
                  inv_anti₀ (sq_pos_of_pos ht_pos) (le_add_of_nonneg_left (sq_nonneg c))
          have hψ_le : |ψ t| ≤ 1 / a := by
            dsimp [ψ]
            rw [abs_div, abs_neg, abs_of_pos ha]
            exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) ha.le
          rw [abs_mul]
          calc
            |φ' t| * |ψ t| ≤ (t ^ 2)⁻¹ * (1 / a) := mul_le_mul hφ'_le hψ_le (abs_nonneg _)
              (inv_nonneg.mpr (sq_nonneg t))
            _ = (1 / a) * (t ^ 2)⁻¹ := mul_comm _ _
        have hderiv_inv : ∀ t ∈ Set.uIcc u T,
            HasDerivAt (fun s : ℝ ↦ (1 / a) * (-s⁻¹)) ((1 / a) * (t ^ 2)⁻¹) t := by
          intro t ht
          rw [Set.uIcc_of_le huT] at ht
          have ht0 : t ≠ 0 := (lt_of_lt_of_le hu_pos ht.1).ne'
          have hinv := (hasDerivAt_inv ht0).neg.const_mul (1 / a)
          refine hinv.congr_deriv ?_
          ring
        have hint_val :
            ∫ t in u..T, (1 / a) * (t ^ 2)⁻¹ = (1 / a) * (-T⁻¹) - (1 / a) * (-u⁻¹) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_inv hint_invsq
        have hle_one : (1 / a) * (-T⁻¹) - (1 / a) * (-u⁻¹) ≤ 1 := by
          have hT_neg : 0 < T⁻¹ := inv_pos.mpr hT
          have hu_inv : u⁻¹ = a := by rw [hu_eq, one_div, inv_inv]
          calc
            (1 / a) * (-T⁻¹) - (1 / a) * (-u⁻¹)
                = (1 / a) * (u⁻¹ - T⁻¹) := by ring
            _ ≤ (1 / a) * u⁻¹ := by gcongr; linarith
            _ = 1 := by rw [hu_inv]; exact one_div_mul_cancel ha.ne'
        exact (h1.trans h2).trans (hint_val.le.trans hle_one)
      have htri : |φ T * ψ T - φ u * ψ u - ∫ t in u..T, φ' t * ψ t| ≤
          |φ T * ψ T| + |φ u * ψ u| + |∫ t in u..T, φ' t * ψ t| := by
        calc
          |φ T * ψ T - φ u * ψ u - ∫ t in u..T, φ' t * ψ t|
              ≤ |φ T * ψ T - φ u * ψ u| + |∫ t in u..T, φ' t * ψ t| := abs_sub _ _
          _ ≤ (|φ T * ψ T| + |φ u * ψ u|) + |∫ t in u..T, φ' t * ψ t| :=
              add_le_add (abs_sub _ _) le_rfl
          _ = |φ T * ψ T| + |φ u * ψ u| + |∫ t in u..T, φ' t * ψ t| := rfl
      linarith [htri, hbd_val T huT, hbd_val u le_rfl, hrem]
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith [hpart1, hpart2])

private lemma integral_sin_div_le_four {α c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    |∫ t in (0 : ℝ)..T, t * Real.sin (α * t) / (c ^ 2 + t ^ 2)| ≤ 4 := by
  rcases lt_trichotomy α 0 with hneg | rfl | hpos
  · have hpos : 0 < -α := neg_pos.mpr hneg
    have heq :
        (∫ t in (0 : ℝ)..T, t * Real.sin (α * t) / (c ^ 2 + t ^ 2)) =
          -∫ t in (0 : ℝ)..T, t * Real.sin ((-α) * t) / (c ^ 2 + t ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      rw [show α * t = -((-α) * t) by ring, Real.sin_neg]
      ring
    rw [heq, abs_neg]
    exact integral_sin_div_pos_le_four hpos hc hT
  · simp
  · exact integral_sin_div_pos_le_four hpos hc hT

/-- Uniform Perron kernel upper bound `‖perronKernel y c T‖ ≤ 2 * y ^ c`, valid for all `y > 0`,
`c > 0`, and `T > 0`, with no dependence on `T` or `y = 1` proximity. -/
theorem norm_perronKernel_le_two_mul_rpow {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T‖ ≤ 2 * y ^ c := by
  rw [perronKernel_eq_real_cos_sin hy hc]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (div_pos (Real.rpow_pos_of_pos hy c) Real.pi_pos)]
  let f₁ : ℝ → ℝ := fun t ↦ c * Real.cos (Real.log y * t) / (c ^ 2 + t ^ 2)
  let f₂ : ℝ → ℝ := fun t ↦ t * Real.sin (Real.log y * t) / (c ^ 2 + t ^ 2)
  have hf₁ : Continuous f₁ := by
    have h := continuous_trig_div_sq (a := c) (b := 0) (α := Real.log y) hc
    refine h.congr fun t ↦ ?_
    dsimp [f₁]; ring
  have hf₂ : Continuous f₂ := by
    have h := continuous_trig_div_sq (a := 0) (b := 1) (α := Real.log y) hc
    refine h.congr fun t ↦ ?_
    dsimp [f₂]; ring
  have heq_sum :
      (∫ t in (0 : ℝ)..T, (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) /
          (c ^ 2 + t ^ 2)) =
        (∫ t in (0 : ℝ)..T, f₁ t) + ∫ t in (0 : ℝ)..T, f₂ t := by
    rw [← intervalIntegral.integral_add (hf₁.intervalIntegrable 0 T) (hf₂.intervalIntegrable 0 T)]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    dsimp [f₁, f₂]
    ring
  have hint_le :
      |∫ t in (0 : ℝ)..T, (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) /
          (c ^ 2 + t ^ 2)| ≤
        Real.pi / 2 + 4 := by
    rw [heq_sum]
    exact (abs_add_le _ _).trans (add_le_add (integral_cos_div_le_pi_div_two hc hT)
      (integral_sin_div_le_four hc hT))
  have hpi_le : (Real.pi / 2 + 4) / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  calc
    y ^ c / Real.pi *
        |∫ t in (0 : ℝ)..T, (c * Real.cos (Real.log y * t) + t * Real.sin (Real.log y * t)) /
          (c ^ 2 + t ^ 2)|
        ≤ y ^ c / Real.pi * (Real.pi / 2 + 4) :=
      mul_le_mul_of_nonneg_left hint_le (div_nonneg (Real.rpow_pos_of_pos hy c).le Real.pi_pos.le)
    _ = ((Real.pi / 2 + 4) / Real.pi) * y ^ c := by ring
    _ ≤ 2 * y ^ c := mul_le_mul_of_nonneg_right hpi_le (Real.rpow_pos_of_pos hy c).le

end AnalyticNumberTheory.DirichletSeries
