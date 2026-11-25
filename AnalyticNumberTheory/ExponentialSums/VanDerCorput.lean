import AnalyticNumberTheory.AnalyticTools.Summation.Poisson
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# van der Corput Method and Exponent Pairs

This file develops the van der Corput method for exponential sums and the formal theory of
exponent pairs:

- The **Kusmin–Landau lemma** (`kusmin_landau`, `kusmin_landau_Ioc`, and `2 / θ` bounds) for
  monotone first differences bounded away from integers.
- The **van der Corput first derivative test** (`vanDerCorput_first_deriv`) and
  **van der Corput second derivative test** (`vanDerCorput_second_deriv`).
- First- and second-derivative oscillatory integral bounds (`vanDerCorput_integral_first_deriv`,
  `vanDerCorput_integral_second_deriv`).
- The **Weyl–van der Corput A-process** (`vanDerCorput_weyl_differencing` and
  `vanDerCorput_A_process_step`).
- The **van der Corput B-process** via truncated Poisson summation and stationary phase reduction
  (`vanDerCorput_B_poisson_reduction`, `vanDerCorput_B_second_deriv_from_poisson`,
  `vanDerCorput_B_process_of_stationaryPhase`).
- The formal `ExponentPair` structure and `IsExponentPair` inductive predicate, with base pairs
  `(0, 1)` and `(1/2, 1/2)`, transformations `processA`, `processB`, and `convexComb`, and
  derived classical exponent pairs `(1/6, 2/3)`, `(1/14, 11/14)`, `(2/7, 4/7)`, `(2/9, 11/18)`,
  and `(11/30, 8/15)`.
-/

noncomputable section

open Complex Finset MeasureTheory Set
open scoped BigOperators Topology
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.ExponentialSums

private abbrev vdcE (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * (α : ℂ) * Complex.I)

private lemma vdcE_add (α β : ℝ) : vdcE (α + β) = vdcE α * vdcE β := by
  simp only [vdcE, Complex.ofReal_add, ← Complex.exp_add]
  congr 1; ring

private lemma vdcE_neg (α : ℝ) : vdcE (-α) = (vdcE α)⁻¹ := by
  simp only [vdcE, Complex.ofReal_neg, ← Complex.exp_neg]
  congr 1; ring

private lemma vdcE_sub (α β : ℝ) : vdcE (α - β) = vdcE α * (vdcE β)⁻¹ := by
  rw [sub_eq_add_neg, vdcE_add, vdcE_neg]

private lemma vdcE_intCast (n : ℤ) : vdcE (n : ℝ) = 1 := by
  simp only [vdcE, Complex.ofReal_intCast]
  rw [show 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I = (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

private lemma vdcE_add_int (α : ℝ) (n : ℤ) : vdcE (α + n) = vdcE α := by
  rw [vdcE_add, vdcE_intCast, mul_one]

private lemma norm_vdcE (α : ℝ) : ‖vdcE α‖ = 1 := by
  have h : 2 * (Real.pi : ℂ) * (α : ℂ) * Complex.I = ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [vdcE, h, Complex.norm_exp_ofReal_mul_I]

private lemma star_vdcE (α : ℝ) : star (vdcE α) = vdcE (-α) := by
  simp only [vdcE, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

section KusminLandau

private lemma cot_eq_cos_div_sin (x : ℝ) : Real.cot x = Real.cos x / Real.sin x :=
  Real.cot_eq_cos_div_sin x

private lemma cot_strict_antitone_sub {x y : ℝ} (hx0 : 0 < x) (hxy : x ≤ y) (hy : y < Real.pi) :
    Real.cot y ≤ Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, ← sub_nonneg]
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (lt_of_le_of_lt hxy hy)
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hx0 hxy) hy
  have hdiff : Real.cos x / Real.sin x - Real.cos y / Real.sin y =
      Real.sin (y - x) / (Real.sin x * Real.sin y) := by
    rw [Real.sin_sub]
    field_simp [hsx.ne', hsy.ne']
  rw [hdiff]
  refine div_nonneg ?_ (mul_pos hsx hsy).le
  exact Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hxy) (by linarith)

private lemma cexp_sub_one_inv_eq_cot {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Complex.exp (2 * Real.pi * (δ : ℂ) * Complex.I) - 1)⁻¹ =
      (-(1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) * Real.cot (Real.pi * δ) : ℝ) * Complex.I := by
  let φ : ℝ := Real.pi * δ
  have hφ0 : 0 < φ := mul_pos Real.pi_pos hδ0
  have hφ1 : φ < Real.pi := mul_lt_of_lt_one_right Real.pi_pos hδ1
  have hsin_pos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ1
  have hexp : Complex.exp (2 * Real.pi * (δ : ℂ) * Complex.I) =
      (Real.cos (2 * φ) : ℂ) + (Real.sin (2 * φ) : ℂ) * Complex.I := by
    have harg : (2 * Real.pi * (δ : ℂ) * Complex.I : ℂ) = ((2 * φ : ℝ) : ℂ) * Complex.I := by
      dsimp only [φ]; push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply inv_eq_of_mul_eq_one_right
  rw [hexp]
  have hφ_eq : Real.pi * δ = φ := rfl
  rw [hφ_eq]
  have h1re : (1 : ℂ).re = 1 := rfl
  have h1im : (1 : ℂ).im = 0 := rfl
  apply Complex.ext
  · simp only [h1re, h1im, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, add_zero,
      sub_self, mul_one]
    rw [Real.cos_two_mul, Real.sin_two_mul, Real.cot_eq_cos_div_sin]
    field_simp [hsin_pos.ne']
    linarith [Real.sin_sq_add_cos_sq φ]
  · simp only [h1re, h1im, Complex.mul_im, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_im, Complex.add_im, Complex.mul_re, mul_zero, sub_zero, add_zero,
      sub_self, mul_one]
    rw [Real.cos_two_mul, Real.sin_two_mul, Real.cot_eq_cos_div_sin]
    field_simp [hsin_pos.ne']
    calc (2 * Real.cos φ ^ 2 - 1 - 1) * (-(2 * 0 * Real.sin φ) - Real.cos φ) +
            -(Real.sin φ * (0 + 2 * Real.cos φ * Real.sin φ))
        = 2 * Real.cos φ * (1 - (Real.sin φ ^ 2 + Real.cos φ ^ 2)) := by ring
      _ = 2 * 0 * Real.sin φ := by rw [Real.sin_sq_add_cos_sq]; ring

private lemma norm_cexp_sub_one_inv {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖(Complex.exp (2 * Real.pi * (δ : ℂ) * Complex.I) - 1)⁻¹‖ =
      1 / (2 * Real.sin (Real.pi * δ)) := by
  rw [cexp_sub_one_inv_eq_cot hδ0 hδ1]
  have hφ0 : 0 < Real.pi * δ := mul_pos Real.pi_pos hδ0
  have hφ1 : Real.pi * δ < Real.pi := mul_lt_of_lt_one_right Real.pi_pos hδ1
  have hsin_pos : 0 < Real.sin (Real.pi * δ) := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ1
  have hsq :
      ‖(-(1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) * Real.cot (Real.pi * δ) : ℝ) * Complex.I‖ ^ 2 =
        (1 / (2 * Real.sin (Real.pi * δ))) ^ 2 := by
    have hz : (-(1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) * Real.cot (Real.pi * δ) : ℝ) * Complex.I =
        ((-1 / 2 : ℝ) : ℂ) + (((-((1 / 2 : ℝ) * Real.cot (Real.pi * δ)) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hz, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I, Real.cot_eq_cos_div_sin]
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * δ)
    field_simp [hsin_pos.ne']
    nlinarith [hsc]
  have h1 : 0 ≤ ‖(-(1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) * Real.cot (Real.pi * δ) : ℝ) * Complex.I‖ :=
    norm_nonneg _
  have h2 : 0 ≤ 1 / (2 * Real.sin (Real.pi * δ)) := by positivity
  nlinarith

private lemma norm_cexp_sub_one_inv_add_one {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖(Complex.exp (2 * Real.pi * (δ : ℂ) * Complex.I) - 1)⁻¹ + 1‖ =
      1 / (2 * Real.sin (Real.pi * δ)) := by
  rw [cexp_sub_one_inv_eq_cot hδ0 hδ1]
  have hφ0 : 0 < Real.pi * δ := mul_pos Real.pi_pos hδ0
  have hφ1 : Real.pi * δ < Real.pi := mul_lt_of_lt_one_right Real.pi_pos hδ1
  have hsin_pos : 0 < Real.sin (Real.pi * δ) := Real.sin_pos_of_pos_of_lt_pi hφ0 hφ1
  have hsq :
      ‖(-(1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) * Real.cot (Real.pi * δ) : ℝ) * Complex.I + 1‖ ^ 2 =
        (1 / (2 * Real.sin (Real.pi * δ))) ^ 2 := by
    have hz : (-(1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) * Real.cot (Real.pi * δ) : ℝ) * Complex.I + 1 =
        ((1 / 2 : ℝ) : ℂ) + (((-((1 / 2 : ℝ) * Real.cot (Real.pi * δ)) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hz, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I, Real.cot_eq_cos_div_sin]
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * δ)
    field_simp [hsin_pos.ne']
    nlinarith [hsc]
  have h1 : 0 ≤ ‖(-(1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) * Real.cot (Real.pi * δ) : ℝ) * Complex.I + 1‖ :=
    norm_nonneg _
  have h2 : 0 ≤ 1 / (2 * Real.sin (Real.pi * δ)) := by positivity
  nlinarith

private lemma sum_Ico_weight_diff {a b : ℕ} (hab : a < b) (c : ℕ → ℂ) (z : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico a b, c n * (z (n + 1) - z n)) + z b =
      (c (b - 1) + 1) * z b - c a * z a -
        ∑ n ∈ Finset.Ico a (b - 1), (c (n + 1) - c n) * z (n + 1) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp; ring
  | succ b hab ih =>
    have hIco1 : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hb_not1 : b ∉ Finset.Ico a b := by simp
    have hIco2 : Finset.Ico a b = insert (b - 1) (Finset.Ico a (b - 1)) := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hb_not2 : b - 1 ∉ Finset.Ico a (b - 1) := by simp
    rw [hIco1, Finset.sum_insert hb_not1]
    have hih : (∑ n ∈ Finset.Ico a b, c n * (z (n + 1) - z n)) =
        (c (b - 1) + 1) * z b - c a * z a -
          ∑ n ∈ Finset.Ico a (b - 1), (c (n + 1) - c n) * z (n + 1) - z b :=
      eq_sub_of_add_eq ih
    rw [hih, show b + 1 - 1 = b by omega, hIco2, Finset.sum_insert hb_not2]
    have hb1 : b - 1 + 1 = b := by omega
    rw [hb1]
    ring

private lemma one_le_cot_half_pi_mul {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) :
    1 ≤ Real.cot (Real.pi * θ / 2) := by
  have hx0 : 0 < Real.pi * θ / 2 := by positivity
  have hx_le : Real.pi * θ / 2 ≤ Real.pi / 4 := by nlinarith [Real.pi_pos]
  have hx_lt : Real.pi * θ / 2 < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin (Real.pi * θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have htan : Real.tan (Real.pi * θ / 2) ≤ Real.tan (Real.pi / 4) :=
    Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos], hx_lt⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hx_le
  rw [Real.tan_pi_div_four, Real.tan_eq_sin_div_cos] at htan
  have hcos_pos : 0 < Real.cos (Real.pi * θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx_lt⟩
  rw [Real.cot_eq_cos_div_sin, one_le_div hsin_pos]
  exact (div_le_one hcos_pos).mp htan

/-- For `0 < θ ≤ 1 / 2`, `Real.cot (π * θ / 2) ≤ 1 / θ`. -/
theorem cot_half_pi_mul_le_inv {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) :
    Real.cot (Real.pi * θ / 2) ≤ 1 / θ := by
  have hx0 : 0 ≤ Real.pi * θ / 2 := by positivity
  have hx_le : Real.pi * θ / 2 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hx0 hx_le
  have hsin_eq : 2 / Real.pi * (Real.pi * θ / 2) = θ := by
    field_simp [Real.pi_ne_zero]
  rw [hsin_eq] at hsin
  rw [Real.cot_eq_cos_div_sin]
  calc Real.cos (Real.pi * θ / 2) / Real.sin (Real.pi * θ / 2)
      ≤ 1 / Real.sin (Real.pi * θ / 2) := div_le_div_of_nonneg_right (Real.cos_le_one _) (hθ0.le.trans hsin)
    _ ≤ 1 / θ := one_div_le_one_div_of_le hθ0 hsin

private theorem kusmin_landau_mono {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) {m : ℤ} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hmono : MonotoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico a b))
    (hbd : ∀ n ∈ Finset.Ico a b,
      (m : ℝ) + θ ≤ f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ∧
        f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ≤ (m : ℝ) + 1 - θ) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.cot (Real.pi * θ / 2) := by
  change ‖∑ n ∈ Finset.Icc a b, vdcE (f (n : ℝ))‖ ≤ Real.cot (Real.pi * θ / 2)
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp only [Finset.Icc_self, Finset.sum_singleton, norm_vdcE]
    exact one_le_cot_half_pi_mul hθ0 hθ1
  let δ : ℕ → ℝ := fun n => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) - (m : ℝ)
  have hδ_bd : ∀ n ∈ Finset.Ico a b, θ ≤ δ n ∧ δ n ≤ 1 - θ := fun n hn => by
    have := hbd n hn
    dsimp only [δ]
    constructor <;> linarith
  have hδ_01 : ∀ n ∈ Finset.Ico a b, 0 < δ n ∧ δ n < 1 := fun n hn =>
    ⟨lt_of_lt_of_le hθ0 (hδ_bd n hn).1, lt_of_le_of_lt (hδ_bd n hn).2 (by linarith)⟩
  let c : ℕ → ℂ := fun n => (vdcE (δ n) - 1)⁻¹
  have hc_term : ∀ n ∈ Finset.Ico a b,
      c n * (vdcE (f ((n + 1 : ℕ) : ℝ)) - vdcE (f (n : ℝ))) = vdcE (f (n : ℝ)) := by
    intro n hn
    have hsplit : f ((n + 1 : ℕ) : ℝ) = f (n : ℝ) + δ n + (m : ℝ) := by
      dsimp only [δ]; ring
    have hexp_diff : vdcE (f ((n + 1 : ℕ) : ℝ)) - vdcE (f (n : ℝ)) =
        vdcE (f (n : ℝ)) * (vdcE (δ n) - 1) := by
      rw [hsplit, vdcE_add_int, vdcE_add]; ring
    have hne : vdcE (δ n) - 1 ≠ 0 := by
      intro hz
      have hnorm : ‖(vdcE (δ n) - 1)⁻¹‖ = 0 := by rw [hz, inv_zero, norm_zero]
      have hnorm' := norm_cexp_sub_one_inv (hδ_01 n hn).1 (hδ_01 n hn).2
      change ‖(vdcE (δ n) - 1)⁻¹‖ = 1 / (2 * Real.sin (Real.pi * δ n)) at hnorm'
      have hsin_pos : 0 < Real.sin (Real.pi * δ n) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hδ_01 n hn).1)
          (mul_lt_of_lt_one_right Real.pi_pos (hδ_01 n hn).2)
      linarith [show (0 : ℝ) < 1 / (2 * Real.sin (Real.pi * δ n)) by positivity]
    rw [hexp_diff]
    calc c n * (vdcE (f (n : ℝ)) * (vdcE (δ n) - 1))
        = (c n * (vdcE (δ n) - 1)) * vdcE (f (n : ℝ)) := by ring
      _ = 1 * vdcE (f (n : ℝ)) := by rw [inv_mul_cancel₀ hne]
      _ = vdcE (f (n : ℝ)) := one_mul _
  have hsum_split :
      ∑ n ∈ Finset.Icc a b, vdcE (f (n : ℝ)) =
        (c (b - 1) + 1) * vdcE (f (b : ℝ)) - c a * vdcE (f (a : ℝ)) -
          ∑ n ∈ Finset.Ico a (b - 1), (c (n + 1) - c n) * vdcE (f ((n + 1 : ℕ) : ℝ)) := by
    have hIcc : Finset.Icc a b = insert b (Finset.Ico a b) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_insert (by simp), add_comm (vdcE (f (b : ℝ)))]
    have hcongr : ∑ n ∈ Finset.Ico a b, vdcE (f (n : ℝ)) =
        ∑ n ∈ Finset.Ico a b, c n * (vdcE (f ((n + 1 : ℕ) : ℝ)) - vdcE (f (n : ℝ))) :=
      Finset.sum_congr rfl fun n hn => (hc_term n hn).symm
    rw [hcongr]
    exact sum_Ico_weight_diff hlt c (fun n => vdcE (f (n : ℝ)))
  have ha_mem : a ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩
  have hb1_mem : b - 1 ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hnorm_b : ‖(c (b - 1) + 1) * vdcE (f (b : ℝ))‖ =
      1 / (2 * Real.sin (Real.pi * δ (b - 1))) := by
    rw [norm_mul, norm_vdcE, mul_one]
    exact norm_cexp_sub_one_inv_add_one (hδ_01 (b - 1) hb1_mem).1 (hδ_01 (b - 1) hb1_mem).2
  have hnorm_a : ‖c a * vdcE (f (a : ℝ))‖ =
      1 / (2 * Real.sin (Real.pi * δ a)) := by
    rw [norm_mul, norm_vdcE, mul_one]
    exact norm_cexp_sub_one_inv (hδ_01 a ha_mem).1 (hδ_01 a ha_mem).2
  have hnorm_diff : ∀ n ∈ Finset.Ico a (b - 1),
      ‖(c (n + 1) - c n) * vdcE (f ((n + 1 : ℕ) : ℝ))‖ =
        (1 / 2 : ℝ) * (Real.cot (Real.pi * δ n) - Real.cot (Real.pi * δ (n + 1))) := by
    intro n hn
    simp only [Finset.mem_Ico] at hn
    have hn_mem : n ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨hn.1, by omega⟩
    have hn1_mem : n + 1 ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    rw [norm_mul, norm_vdcE, mul_one]
    have hc1 := cexp_sub_one_inv_eq_cot (hδ_01 (n + 1) hn1_mem).1 (hδ_01 (n + 1) hn1_mem).2
    have hc0 := cexp_sub_one_inv_eq_cot (hδ_01 n hn_mem).1 (hδ_01 n hn_mem).2
    change c (n + 1) = _ at hc1
    change c n = _ at hc0
    have hsub_eq : c (n + 1) - c n =
        (((1 / 2 : ℝ) * (Real.cot (Real.pi * δ n) - Real.cot (Real.pi * δ (n + 1))) : ℝ) : ℂ) *
          Complex.I := by
      rw [hc1, hc0]
      push_cast
      ring
    rw [hsub_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hδ_le : δ n ≤ δ (n + 1) := by
      have hm_le := hmono (show n ∈ Set.Ico a b from ⟨hn.1, by omega⟩)
        (show n + 1 ∈ Set.Ico a b from ⟨by omega, by omega⟩) (Nat.le_succ n)
      dsimp only [δ]
      linarith
    have hcot_le := cot_strict_antitone_sub (mul_pos Real.pi_pos (hδ_01 n hn_mem).1)
      (mul_le_mul_of_nonneg_left hδ_le Real.pi_pos.le)
      (mul_lt_of_lt_one_right Real.pi_pos (hδ_01 (n + 1) hn1_mem).2)
    rw [abs_of_nonneg (by linarith)]
  have htelescoping :
      ∑ n ∈ Finset.Ico a (b - 1),
          (1 / 2 : ℝ) * (Real.cot (Real.pi * δ n) - Real.cot (Real.pi * δ (n + 1))) =
        (1 / 2 : ℝ) * (Real.cot (Real.pi * δ a) - Real.cot (Real.pi * δ (b - 1))) := by
    rw [← Finset.mul_sum]
    congr 1
    let gcot : ℕ → ℝ := fun n => Real.cot (Real.pi * δ n)
    have hbij : ∑ n ∈ Finset.Ico a (b - 1), (gcot n - gcot (n + 1)) =
        ∑ j ∈ Finset.range (b - 1 - a), (gcot (a + j) - gcot (a + (j + 1))) := by
      refine Finset.sum_bij (fun n _ => n - a) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Ico] at hn; simp only [Finset.mem_range]; omega
      · intro n₁ hn₁ n₂ hn₂ heq; simp only [Finset.mem_Ico] at hn₁ hn₂; omega
      · intro j hj; simp only [Finset.mem_range] at hj; exact ⟨a + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn
        simp only [Finset.mem_Ico] at hn
        rw [show a + (n - a) = n by omega, show a + (n - a + 1) = n + 1 by omega]
    rw [hbij, Finset.sum_range_sub' (fun j => gcot (a + j)) (b - 1 - a), add_zero,
      show a + (b - 1 - a) = b - 1 by omega]
  have hnorm_sum :
      ‖∑ n ∈ Finset.Icc a b, vdcE (f (n : ℝ))‖ ≤
        1 / (2 * Real.sin (Real.pi * δ (b - 1))) + 1 / (2 * Real.sin (Real.pi * δ a)) +
          (1 / 2 : ℝ) * (Real.cot (Real.pi * δ a) - Real.cot (Real.pi * δ (b - 1))) := by
    rw [hsum_split]
    calc ‖(c (b - 1) + 1) * vdcE (f (b : ℝ)) - c a * vdcE (f (a : ℝ)) -
            ∑ n ∈ Finset.Ico a (b - 1), (c (n + 1) - c n) * vdcE (f ((n + 1 : ℕ) : ℝ))‖
        ≤ ‖(c (b - 1) + 1) * vdcE (f (b : ℝ)) - c a * vdcE (f (a : ℝ))‖ +
            ‖∑ n ∈ Finset.Ico a (b - 1), (c (n + 1) - c n) * vdcE (f ((n + 1 : ℕ) : ℝ))‖ :=
          norm_sub_le _ _
      _ ≤ (‖(c (b - 1) + 1) * vdcE (f (b : ℝ))‖ + ‖c a * vdcE (f (a : ℝ))‖) +
            ∑ n ∈ Finset.Ico a (b - 1), ‖(c (n + 1) - c n) * vdcE (f ((n + 1 : ℕ) : ℝ))‖ :=
          add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
      _ = 1 / (2 * Real.sin (Real.pi * δ (b - 1))) + 1 / (2 * Real.sin (Real.pi * δ a)) +
            (1 / 2 : ℝ) * (Real.cot (Real.pi * δ a) - Real.cot (Real.pi * δ (b - 1))) := by
          rw [hnorm_b, hnorm_a, Finset.sum_congr rfl hnorm_diff, htelescoping]
  have hid_a : 1 / (2 * Real.sin (Real.pi * δ a)) + (1 / 2 : ℝ) * Real.cot (Real.pi * δ a) =
      (1 / 2 : ℝ) * Real.cot (Real.pi * δ a / 2) := by
    have hsin_a : 0 < Real.sin (Real.pi * δ a) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hδ_01 a ha_mem).1)
        (mul_lt_of_lt_one_right Real.pi_pos (hδ_01 a ha_mem).2)
    have hsin_half : 0 < Real.sin (Real.pi * δ a / 2) :=
      Real.sin_pos_of_pos_of_lt_pi
        (div_pos (mul_pos Real.pi_pos (hδ_01 a ha_mem).1) two_pos)
        (by nlinarith [Real.pi_pos, (hδ_01 a ha_mem).2])
    have hsin2 : Real.sin (Real.pi * δ a) =
        2 * Real.sin (Real.pi * δ a / 2) * Real.cos (Real.pi * δ a / 2) := by
      simpa [show 2 * (Real.pi * δ a / 2) = Real.pi * δ a by ring] using
        Real.sin_two_mul (Real.pi * δ a / 2)
    have hcos2 : Real.cos (Real.pi * δ a) = 2 * Real.cos (Real.pi * δ a / 2) ^ 2 - 1 := by
      simpa [show 2 * (Real.pi * δ a / 2) = Real.pi * δ a by ring] using
        Real.cos_two_mul (Real.pi * δ a / 2)
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, hsin2, hcos2]
    have hcos_half : Real.cos (Real.pi * δ a / 2) ≠ 0 := by
      intro hc
      rw [hc, mul_zero] at hsin2
      linarith
    field_simp [hsin_half.ne', hcos_half]
    ring
  have hid_b : 1 / (2 * Real.sin (Real.pi * δ (b - 1))) -
        (1 / 2 : ℝ) * Real.cot (Real.pi * δ (b - 1)) =
      (1 / 2 : ℝ) * Real.tan (Real.pi * δ (b - 1) / 2) := by
    have hsin_b : 0 < Real.sin (Real.pi * δ (b - 1)) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hδ_01 (b - 1) hb1_mem).1)
        (mul_lt_of_lt_one_right Real.pi_pos (hδ_01 (b - 1) hb1_mem).2)
    have hcos_half : 0 < Real.cos (Real.pi * δ (b - 1) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, (hδ_01 (b - 1) hb1_mem).1],
        by nlinarith [Real.pi_pos, (hδ_01 (b - 1) hb1_mem).2]⟩
    have hsin2 : Real.sin (Real.pi * δ (b - 1)) =
        2 * Real.sin (Real.pi * δ (b - 1) / 2) * Real.cos (Real.pi * δ (b - 1) / 2) := by
      simpa [show 2 * (Real.pi * δ (b - 1) / 2) = Real.pi * δ (b - 1) by ring] using
        Real.sin_two_mul (Real.pi * δ (b - 1) / 2)
    have hcos2 : Real.cos (Real.pi * δ (b - 1)) = 1 - 2 * Real.sin (Real.pi * δ (b - 1) / 2) ^ 2 := by
      have h := Real.cos_two_mul (Real.pi * δ (b - 1) / 2)
      rw [show 2 * (Real.pi * δ (b - 1) / 2) = Real.pi * δ (b - 1) by ring] at h
      linarith [Real.sin_sq_add_cos_sq (Real.pi * δ (b - 1) / 2)]
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, hsin2, hcos2]
    have hsin_half : Real.sin (Real.pi * δ (b - 1) / 2) ≠ 0 := by
      intro hs
      rw [hs, mul_zero, zero_mul] at hsin2
      linarith
    field_simp [hsin_half, hcos_half.ne']
    ring
  have hcot_a : Real.cot (Real.pi * δ a / 2) ≤ Real.cot (Real.pi * θ / 2) :=
    cot_strict_antitone_sub (by positivity) (by nlinarith [Real.pi_pos, (hδ_bd a ha_mem).1])
      (by nlinarith [Real.pi_pos, (hδ_01 a ha_mem).2])
  have htan_b : Real.tan (Real.pi * δ (b - 1) / 2) ≤ Real.cot (Real.pi * θ / 2) := by
    have hle : Real.pi * δ (b - 1) / 2 ≤ Real.pi / 2 - Real.pi * θ / 2 := by
      nlinarith [Real.pi_pos, (hδ_bd (b - 1) hb1_mem).2]
    have htan_le := Real.strictMonoOn_tan.monotoneOn
      ⟨by nlinarith [Real.pi_pos, (hδ_01 (b - 1) hb1_mem).1],
        by nlinarith [Real.pi_pos, (hδ_01 (b - 1) hb1_mem).2]⟩
      ⟨by nlinarith [Real.pi_pos, hθ1], by nlinarith [Real.pi_pos, hθ0]⟩ hle
    rw [Real.tan_pi_div_two_sub,
      show (Real.tan (Real.pi * θ / 2))⁻¹ = Real.cot (Real.pi * θ / 2) by
        rw [Real.tan_eq_sin_div_cos, inv_div, ← Real.cot_eq_cos_div_sin]] at htan_le
    exact htan_le
  calc ‖∑ n ∈ Finset.Icc a b, vdcE (f (n : ℝ))‖
      ≤ (1 / 2 : ℝ) * Real.cot (Real.pi * δ a / 2) +
          (1 / 2 : ℝ) * Real.tan (Real.pi * δ (b - 1) / 2) := by
        linarith [hnorm_sum, hid_a, hid_b]
    _ ≤ (1 / 2 : ℝ) * Real.cot (Real.pi * θ / 2) +
          (1 / 2 : ℝ) * Real.cot (Real.pi * θ / 2) := by gcongr
    _ = Real.cot (Real.pi * θ / 2) := by ring

/-- **Kusmin–Landau lemma** on `Finset.Icc a b` (`a ≤ b`): if the first differences
`f (n + 1) - f n` are monotone (either nondecreasing or nonincreasing) on `[a, b)` and satisfy
`m + θ ≤ f (n + 1) - f n ≤ m + 1 - θ` for some `m : ℤ` and `0 < θ ≤ 1 / 2`, then
`‖∑_{n ∈ Icc a b} exp(2πi f(n))‖ ≤ cot(π θ / 2)`. -/
theorem kusmin_landau {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) {m : ℤ} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hmono : MonotoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico a b) ∨
      AntitoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico a b))
    (hbd : ∀ n ∈ Finset.Ico a b,
      (m : ℝ) + θ ≤ f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ∧
        f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ≤ (m : ℝ) + 1 - θ) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.cot (Real.pi * θ / 2) := by
  rcases hmono with hm | ha
  · exact kusmin_landau_mono hab hθ0 hθ1 hm hbd
  · let g : ℝ → ℝ := fun t => -f t
    have hg_mono : MonotoneOn (fun n : ℕ => g ((n + 1 : ℕ) : ℝ) - g (n : ℝ)) (Set.Ico a b) := by
      intro n₁ hn₁ n₂ hn₂ h12
      have h := ha hn₁ hn₂ h12
      dsimp only [g]
      linarith
    have hg_bd : ∀ n ∈ Finset.Ico a b,
        ((-(m + 1) : ℤ) : ℝ) + θ ≤ g ((n + 1 : ℕ) : ℝ) - g (n : ℝ) ∧
          g ((n + 1 : ℕ) : ℝ) - g (n : ℝ) ≤ ((-(m + 1) : ℤ) : ℝ) + 1 - θ := by
      intro n hn
      have h := hbd n hn
      dsimp only [g]
      simp only [Int.cast_neg, Int.cast_add, Int.cast_one]
      constructor <;> linarith
    have hconj :
        ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ =
          ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * (g (n : ℝ) : ℂ) * Complex.I)‖ := by
      have hs : ∑ n ∈ Finset.Icc a b, vdcE (g (n : ℝ)) =
          starRingEnd ℂ (∑ n ∈ Finset.Icc a b, vdcE (f (n : ℝ))) := by
        simp only [map_sum, ← Complex.star_def, star_vdcE, g]
      change ‖∑ n ∈ Finset.Icc a b, vdcE (f (n : ℝ))‖ = ‖∑ n ∈ Finset.Icc a b, vdcE (g (n : ℝ))‖
      rw [hs, Complex.norm_conj]
    rw [hconj]
    exact kusmin_landau_mono hab hθ0 hθ1 hg_mono hg_bd

/-- **Kusmin–Landau lemma** (`1 / θ` and `2 / θ` form) on `Finset.Icc a b`. -/
theorem kusmin_landau_le_inv {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) {m : ℤ} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hmono : MonotoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico a b) ∨
      AntitoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico a b))
    (hbd : ∀ n ∈ Finset.Ico a b,
      (m : ℝ) + θ ≤ f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ∧
        f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ≤ (m : ℝ) + 1 - θ) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / θ :=
  (kusmin_landau hab hθ0 hθ1 hmono hbd).trans (cot_half_pi_mul_le_inv hθ0 hθ1)

/-- **Kusmin–Landau lemma** on `Finset.Ioc M (M + N)` (`2 / θ` bound, valid for all `N`). -/
theorem kusmin_landau_Ioc {f : ℝ → ℝ} (M N : ℕ) {m : ℤ} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hmono : MonotoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico (M + 1) (M + N)) ∨
      AntitoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico (M + 1) (M + N)))
    (hbd : ∀ n ∈ Finset.Ico (M + 1) (M + N),
      (m : ℝ) + θ ≤ f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ∧
        f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ≤ (m : ℝ) + 1 - θ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / θ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; positivity
  have hIoc : Finset.Ioc M (M + N) = Finset.Icc (M + 1) (M + N) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc]
  have h1 := kusmin_landau_le_inv (by omega : M + 1 ≤ M + N) hθ0 hθ1 hmono hbd
  linarith [show (1 / θ : ℝ) ≤ 2 / θ by gcongr; norm_num]

end KusminLandau

section DerivativeTests

private lemma diff_mono_of_deriv_mono {f f' : ℝ → ℝ} {a b : ℕ}
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (a : ℝ) (b : ℝ))) :
    MonotoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico a b) := by
  intro n₁ hn₁ n₂ hn₂ h12
  simp only [Set.mem_Ico] at hn₁ hn₂
  have hle : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h12
  let g : ℝ → ℝ := fun t => f ((n₂ : ℝ) + t) - f ((n₁ : ℝ) + t)
  have hg_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt g (f' ((n₂ : ℝ) + t) - f' ((n₁ : ℝ) + t)) t := by
    intro t ht
    have h2 : HasDerivAt (fun s => f ((n₂ : ℝ) + s)) (f' ((n₂ : ℝ) + t)) t := by
      have hd := hderiv ((n₂ : ℝ) + t) ⟨by
          have ha2 : (a : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast (by omega : a ≤ n₂)
          linarith [ht.1],
        by
          have hb2 : (n₂ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hn₂.2
          linarith [ht.2]⟩
      have hlin : HasDerivAt (fun s : ℝ => (n₂ : ℝ) + s) 1 t :=
        ((hasDerivAt_const t (n₂ : ℝ)).add (hasDerivAt_id t)).congr_deriv (zero_add 1)
      simpa [Function.comp_def] using hd.comp t hlin
    have h1 : HasDerivAt (fun s => f ((n₁ : ℝ) + s)) (f' ((n₁ : ℝ) + t)) t := by
      have hd := hderiv ((n₁ : ℝ) + t) ⟨by
          have ha1 : (a : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast (by omega : a ≤ n₁)
          linarith [ht.1],
        by
          have hb1 : (n₁ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hn₁.2
          linarith [ht.2]⟩
      have hlin : HasDerivAt (fun s : ℝ => (n₁ : ℝ) + s) 1 t :=
        ((hasDerivAt_const t (n₁ : ℝ)).add (hasDerivAt_id t)).congr_deriv (zero_add 1)
      simpa [Function.comp_def] using hd.comp t hlin
    exact h2.sub h1
  have hg_mono : MonotoneOn g (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hg_deriv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hg_deriv t htI).deriv]
    have h1m : (n₁ : ℝ) + t ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      have ha1 : (a : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast (by omega : a ≤ n₁)
      have hb1 : (n₁ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hn₁.2
      exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
    have h2m : (n₂ : ℝ) + t ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      have ha2 : (a : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast (by omega : a ≤ n₂)
      have hb2 : (n₂ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hn₂.2
      exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
    exact sub_nonneg.mpr (hmono h1m h2m (by linarith))
  have hg01 := hg_mono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  dsimp only [g] at hg01
  simp only [Nat.cast_add, Nat.cast_one, add_zero] at hg01 ⊢
  linarith

private lemma diff_bounds_of_deriv {f f' : ℝ → ℝ} {a b : ℕ} {m : ℤ} {θ : ℝ}
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' t) t)
    (hbd : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), (m : ℝ) + θ ≤ f' t ∧ f' t ≤ (m : ℝ) + 1 - θ) :
    ∀ n ∈ Finset.Ico a b,
      (m : ℝ) + θ ≤ f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ∧
        f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) ≤ (m : ℝ) + 1 - θ := by
  intro n hn
  simp only [Finset.mem_Ico] at hn
  have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hcont : ContinuousOn f (Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
    intro t ht
    have htI : t ∈ Set.Icc (a : ℝ) (b : ℝ) :=
      ⟨le_trans (by exact_mod_cast hn.1) ht.1, le_trans ht.2 (by exact_mod_cast hn.2)⟩
    exact (hderiv t htI).continuousAt.continuousWithinAt
  have hdiff : ∀ t ∈ Set.Ioo (n : ℝ) ((n + 1 : ℕ) : ℝ), HasDerivAt f (f' t) t := fun t ht =>
    hderiv t ⟨le_trans (by exact_mod_cast hn.1) ht.1.le,
      le_trans ht.2.le (by exact_mod_cast hn.2)⟩
  obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont hdiff
  have hξI : ξ ∈ Set.Icc (a : ℝ) (b : ℝ) :=
    ⟨le_trans (by exact_mod_cast hn.1) hξ.1.le, le_trans hξ.2.le (by exact_mod_cast hn.2)⟩
  have hdiff_eq : f ((n + 1 : ℕ) : ℝ) - f (n : ℝ) = f' ξ := by
    have hden : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
    rw [hden, div_one] at hEq
    exact hEq.symm
  rw [hdiff_eq]
  exact hbd ξ hξI

/-- General **van der Corput first derivative test** modulo `1`: if `f` is differentiable on
`[a, b]` with monotone derivative `f'` satisfying `m + θ ≤ f'(t) ≤ m + 1 - θ` (`0 < θ ≤ 1 / 2`),
then `‖∑_{n ∈ Icc a b} exp(2πi f(n))‖ ≤ 2 / θ`. -/
theorem vanDerCorput_first_deriv_mod_one {f f' : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) {m : ℤ} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (a : ℝ) (b : ℝ)) ∨
      AntitoneOn f' (Set.Icc (a : ℝ) (b : ℝ)))
    (hbd : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), (m : ℝ) + θ ≤ f' t ∧ f' t ≤ (m : ℝ) + 1 - θ) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / θ := by
  have hdiff_bd := diff_bounds_of_deriv hderiv hbd
  rcases hmono with hm | ha
  · exact (kusmin_landau_le_inv hab hθ0 hθ1 (Or.inl (diff_mono_of_deriv_mono hderiv hm))
      hdiff_bd).trans (by gcongr; norm_num)
  · have hanti : AntitoneOn (fun n : ℕ => f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)) (Set.Ico a b) := by
      have hneg := diff_mono_of_deriv_mono (f := fun t => -f t) (f' := fun t => -f' t)
        (fun t ht => (hderiv t ht).neg) (fun t₁ h1 t₂ h2 h12 => neg_le_neg (ha h1 h2 h12))
      intro n₁ hn₁ n₂ hn₂ h12
      have h := hneg hn₁ hn₂ h12
      dsimp only at h
      linarith
    exact (kusmin_landau_le_inv hab hθ0 hθ1 (Or.inr hanti) hdiff_bd).trans (by gcongr; norm_num)

/-- **van der Corput first derivative test**: if `f` is `C¹` on `[a, b]` with monotone derivative
`f'` satisfying `λ₁ ≤ |f'(t)| ≤ 1 / 2` (`0 < λ₁`), then
`‖∑_{n ∈ Ioc a b} exp(2πi f(n))‖ ≤ 2 / λ₁`. -/
theorem vanDerCorput_first_deriv {f f' : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) {lam₁ : ℝ}
    (hlam0 : 0 < lam₁) (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc (a : ℝ) (b : ℝ)))
    (hmono : MonotoneOn f' (Set.Icc (a : ℝ) (b : ℝ)) ∨
      AntitoneOn f' (Set.Icc (a : ℝ) (b : ℝ)))
    (hbd : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), lam₁ ≤ |f' t| ∧ |f' t| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      2 / lam₁ := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp; positivity
  have hlam_half : lam₁ ≤ 1 / 2 :=
    (hbd (a : ℝ) (Set.left_mem_Icc.mpr (by exact_mod_cast hab))).1.trans
      (hbd (a : ℝ) (Set.left_mem_Icc.mpr (by exact_mod_cast hab))).2
  have hne0 : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), f' t ≠ 0 := fun t ht =>
    abs_pos.mp (lt_of_lt_of_le hlam0 (hbd t ht).1)
  have hsign : (∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), lam₁ ≤ f' t ∧ f' t ≤ 1 / 2) ∨
      (∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), -1 / 2 ≤ f' t ∧ f' t ≤ -lam₁) := by
    by_cases ha_pos : 0 < f' (a : ℝ)
    · left
      intro t ht
      have ht_pos : 0 < f' t := by
        by_contra hle
        have hle0 : f' t ≤ 0 := not_lt.mp hle
        have hmem_neg : f' t < 0 := lt_of_le_of_ne hle0 (hne0 t ht)
        obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' ht.1
          (hf'_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨hmem_neg.le, ha_pos.le⟩
        exact hne0 c (Set.Icc_subset_Icc_right ht.2 hc) hc0
      have hbt := hbd t ht
      rw [abs_of_pos ht_pos] at hbt
      exact hbt
    · right
      intro t ht
      have ha_neg : f' (a : ℝ) < 0 :=
        lt_of_le_of_ne (not_lt.mp ha_pos) (hne0 (a : ℝ) (Set.left_mem_Icc.mpr (by exact_mod_cast hab)))
      have ht_neg : f' t < 0 := by
        by_contra hle
        have hge0 : 0 ≤ f' t := not_lt.mp hle
        have ht_pos : 0 < f' t := lt_of_le_of_ne hge0 (hne0 t ht).symm
        obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc ht.1
          (hf'_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨ha_neg.le, ht_pos.le⟩
        exact hne0 c (Set.Icc_subset_Icc_right ht.2 hc) hc0
      have hbt := hbd t ht
      rw [abs_of_neg ht_neg] at hbt
      constructor <;> linarith
  have hIoc : Finset.Ioc a b = Finset.Icc (a + 1) b := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc]
  have hsub : Set.Icc ((a + 1 : ℕ) : ℝ) (b : ℝ) ⊆ Set.Icc (a : ℝ) (b : ℝ) :=
    Set.Icc_subset_Icc_left (by exact_mod_cast Nat.le_succ a)
  have hderiv' : ∀ t ∈ Set.Icc ((a + 1 : ℕ) : ℝ) (b : ℝ), HasDerivAt f (f' t) t :=
    fun t ht => hderiv t (hsub ht)
  have hmono' : MonotoneOn f' (Set.Icc ((a + 1 : ℕ) : ℝ) (b : ℝ)) ∨
      AntitoneOn f' (Set.Icc ((a + 1 : ℕ) : ℝ) (b : ℝ)) :=
    hmono.imp (fun hm => hm.mono hsub) (fun ha => ha.mono hsub)
  rcases hsign with hpos | hneg
  · exact vanDerCorput_first_deriv_mod_one (by omega : a + 1 ≤ b) (m := 0) hlam0 hlam_half
      hderiv' hmono' fun t ht => by
        have h := hpos t (hsub ht)
        push_cast
        constructor <;> linarith
  · exact vanDerCorput_first_deriv_mod_one (by omega : a + 1 ≤ b) (m := -1) hlam0 hlam_half
      hderiv' hmono' fun t ht => by
        have h := hneg t (hsub ht)
        push_cast
        constructor <;> linarith

private lemma filter_monotone_interval {g : ℝ → ℝ} {a b : ℕ}
    (hg : MonotoneOn g (Set.Icc (a : ℝ) (b : ℝ))) (P : ℝ → Prop) [DecidablePred P]
    (hconv : ∀ x y z : ℝ, x ≤ y → y ≤ z → P x → P z → P y) :
    ∀ S : Finset ℕ, S = (Finset.Ioc a b).filter (fun n : ℕ => P (g (n : ℝ))) →
      S = ∅ ∨ ∃ u v : ℕ, u ≤ v ∧ a < u ∧ v ≤ b ∧ S = Finset.Icc u v := by
  intro S hS
  by_cases hne : S.Nonempty
  · right
    let u := S.min' hne
    let v := S.max' hne
    have hu : u ∈ S := Finset.min'_mem S hne
    have hv : v ∈ S := Finset.max'_mem S hne
    have huv : u ≤ v := Finset.min'_le S v hv
    have hu_ioc : u ∈ Finset.Ioc a b := by
      rw [hS] at hu; exact (Finset.mem_filter.mp hu).1
    have hv_ioc : v ∈ Finset.Ioc a b := by
      rw [hS] at hv; exact (Finset.mem_filter.mp hv).1
    have hau : a < u := (Finset.mem_Ioc.mp hu_ioc).1
    have hvb : v ≤ b := (Finset.mem_Ioc.mp hv_ioc).2
    refine ⟨u, v, huv, hau, hvb, ?_⟩
    ext n
    constructor
    · intro hn
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S n hn, Finset.le_max' S n hn⟩
    · intro hn
      simp only [Finset.mem_Icc] at hn
      rw [hS, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have huP : P (g (u : ℝ)) := by rw [hS] at hu; exact (Finset.mem_filter.mp hu).2
      have hvP : P (g (v : ℝ)) := by rw [hS] at hv; exact (Finset.mem_filter.mp hv).2
      have hgu : g (u : ℝ) ≤ g (n : ℝ) := hg ⟨by exact_mod_cast (by omega : a ≤ u),
        by exact_mod_cast (by omega : u ≤ b)⟩ ⟨by exact_mod_cast (by omega : a ≤ n),
        by exact_mod_cast (by omega : n ≤ b)⟩ (by exact_mod_cast hn.1)
      have hgv : g (n : ℝ) ≤ g (v : ℝ) := hg ⟨by exact_mod_cast (by omega : a ≤ n),
        by exact_mod_cast (by omega : n ≤ b)⟩ ⟨by exact_mod_cast (by omega : a ≤ v),
        by exact_mod_cast (by omega : v ≤ b)⟩ (by exact_mod_cast hn.2)
      exact hconv _ _ _ hgu hgv huP hvP
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hne

private lemma vanDerCorput_second_deriv_pos {f f' f'' : ℝ → ℝ} {a b : ℕ}
    (hab : a + 1 ≤ b) {lam₂ c : ℝ} (hlam0 : 0 < lam₂) (hc : 1 ≤ c)
    (hf : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), lam₂ ≤ f'' t ∧ f'' t ≤ c * lam₂) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      (20 * c + 20) * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ))) := by
  let N : ℝ := (b : ℝ) - a
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hsqrt_pos : 0 < lam₂ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hlam0 _
  have hinv_sqrt_pos : 0 < lam₂ ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hlam0 _
  have hsum_ge2 : 2 ≤ N * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ)) := by
    have hprod : lam₂ ^ (1 / 2 : ℝ) * lam₂ ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hlam0]
      simp
    have hsq : 0 ≤ (lam₂ ^ (1 / 2 : ℝ) - lam₂ ^ (-(1 / 2 : ℝ))) ^ 2 := sq_nonneg _
    have ham : 2 ≤ lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ)) := by nlinarith [hprod, hsq]
    have hN_mul : lam₂ ^ (1 / 2 : ℝ) ≤ N * lam₂ ^ (1 / 2 : ℝ) :=
      le_mul_of_one_le_left hsqrt_pos.le hN1
    linarith
  by_cases hbig : 1 / 16 ≤ lam₂
  · have hsqrt_ge : 1 / 4 ≤ lam₂ ^ (1 / 2 : ℝ) := by
      calc (1 / 4 : ℝ) = (1 / 16 : ℝ) ^ (1 / 2 : ℝ) := by
            rw [show (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ 2 by norm_num,
              ← Real.rpow_natCast (1 / 4 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ lam₂ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hbig (by norm_num)
    have htriv : ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ))‖ ≤ N := by
      calc ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ))‖
          ≤ ∑ _n ∈ Finset.Ioc a b, (1 : ℝ) := (norm_sum_le _ _).trans_eq (by simp [norm_vdcE])
        _ = N := by simp [N, Nat.card_Ioc, Nat.cast_sub (by omega : a ≤ b)]
    have hN_le : N ≤ 4 * (N * lam₂ ^ (1 / 2 : ℝ)) := by nlinarith [hN1, hsqrt_ge]
    calc ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ))‖
        ≤ N := htriv
      _ ≤ 4 * (N * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ))) := by linarith [hinv_sqrt_pos]
      _ ≤ (20 * c + 20) * (N * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ))) := by
          gcongr; linarith
  have hsmall : lam₂ < 1 / 16 := not_le.mp hbig
  let δ : ℝ := lam₂ ^ (1 / 2 : ℝ)
  have hδ_pos : 0 < δ := hsqrt_pos
  have hδ_lt : δ < 1 / 4 := by
    calc δ = lam₂ ^ (1 / 2 : ℝ) := rfl
      _ < (1 / 16 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_lt_rpow hlam0.le hsmall (by norm_num)
      _ = 1 / 4 := by
          rw [show (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ 2 by norm_num,
            ← Real.rpow_natCast (1 / 4 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hδ_half : δ ≤ 1 / 2 := by linarith
  have hf'_mono : StrictMonoOn f' (Set.Icc (a : ℝ) (b : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hf' t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    have htI : t ∈ Set.Icc (a : ℝ) (b : ℝ) := interior_subset ht
    rw [(hf' t htI).deriv]
    exact lt_of_lt_of_le hlam0 (hf'' t htI).1
  have hf'_mvt_lb : ∀ {x y : ℝ}, (a : ℝ) ≤ x → x ≤ y → y ≤ (b : ℝ) →
      lam₂ * (y - x) ≤ f' y - f' x := by
    intro x y hx hxy hy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    have hcont : ContinuousOn f' (Set.Icc x y) := fun t ht =>
      (hf' t ⟨hx.trans ht.1, ht.2.trans hy⟩).continuousAt.continuousWithinAt
    have hdiff : ∀ t ∈ Set.Ioo x y, HasDerivAt f' (f'' t) t := fun t ht =>
      hf' t ⟨hx.trans ht.1.le, ht.2.le.trans hy⟩
    obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f' f'' hlt hcont hdiff
    have hξI : ξ ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨hx.trans hξ.1.le, hξ.2.le.trans hy⟩
    have hlb : lam₂ ≤ (f' y - f' x) / (y - x) := hEq ▸ (hf'' ξ hξI).1
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hlb
  have hf'_mvt_ub : f' (b : ℝ) - f' (a : ℝ) ≤ c * lam₂ * N := by
    have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : a < b)
    have hcont : ContinuousOn f' (Set.Icc (a : ℝ) (b : ℝ)) := fun t ht =>
      (hf' t ht).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f' f'' hlt hcont fun t ht =>
      hf' t ⟨ht.1.le, ht.2.le⟩
    have hξI : ξ ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨hξ.1.le, hξ.2.le⟩
    have hub : (f' (b : ℝ) - f' (a : ℝ)) / ((b : ℝ) - a) ≤ c * lam₂ := hEq ▸ (hf'' ξ hξI).2
    exact (div_le_iff₀ (sub_pos.mpr hlt)).mp hub
  let Kset := Finset.Icc ⌊f' (a : ℝ)⌋ ⌈f' (b : ℝ)⌉
  have hmaps_K : ∀ n ∈ Finset.Ioc a b, round (f' (n : ℝ)) ∈ Kset := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hfa : f' (a : ℝ) ≤ f' (n : ℝ) := hf'_mono.monotoneOn
      (Set.left_mem_Icc.mpr (by exact_mod_cast (by omega : a ≤ b)))
      ⟨by exact_mod_cast (by omega : a ≤ n), by exact_mod_cast hn.2⟩ (by exact_mod_cast (by omega : a ≤ n))
    have hfb : f' (n : ℝ) ≤ f' (b : ℝ) := hf'_mono.monotoneOn
      ⟨by exact_mod_cast (by omega : a ≤ n), by exact_mod_cast hn.2⟩
      (Set.right_mem_Icc.mpr (by exact_mod_cast (by omega : a ≤ b))) (by exact_mod_cast hn.2)
    have hr_lo : f' (n : ℝ) - 1 / 2 < (round (f' (n : ℝ)) : ℝ) := sub_half_lt_round _
    have hr_hi : (round (f' (n : ℝ)) : ℝ) ≤ f' (n : ℝ) + 1 / 2 := round_le_add_half _
    have hfl : (⌊f' (a : ℝ)⌋ : ℝ) ≤ f' (a : ℝ) := Int.floor_le _
    have hcl : f' (b : ℝ) ≤ (⌈f' (b : ℝ)⌉ : ℝ) := Int.le_ceil _
    simp only [Kset, Finset.mem_Icc]
    constructor
    · exact Int.lt_add_one_iff.mp ((Int.cast_lt (R := ℝ)).mp (by push_cast; linarith))
    · exact Int.lt_add_one_iff.mp ((Int.cast_lt (R := ℝ)).mp (by push_cast; linarith))
  have hfiber :
      ∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ)) =
        ∑ k ∈ Kset, ∑ n ∈ (Finset.Ioc a b).filter (fun (n : ℕ) => round (f' (n : ℝ)) = k),
          vdcE (f (n : ℝ)) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps_K _
  have hk_bound : ∀ k ∈ Kset,
      ‖∑ n ∈ (Finset.Ioc a b).filter (fun (n : ℕ) => round (f' (n : ℝ)) = k),
          vdcE (f (n : ℝ))‖ ≤
        2 * δ / lam₂ + 1 + 4 / δ := by
    intro k _
    let Sk : Finset ℕ := (Finset.Ioc a b).filter (fun (n : ℕ) => round (f' (n : ℝ)) = k)
    let Sk_mid : Finset ℕ :=
      (Finset.Ioc a b).filter (fun (n : ℕ) => round (f' (n : ℝ)) = k ∧ |f' (n : ℝ) - k| < δ)
    let Sk_lo : Finset ℕ :=
      (Finset.Ioc a b).filter (fun (n : ℕ) => round (f' (n : ℝ)) = k ∧ f' (n : ℝ) ≤ (k : ℝ) - δ)
    let Sk_hi : Finset ℕ :=
      (Finset.Ioc a b).filter (fun (n : ℕ) => round (f' (n : ℝ)) = k ∧ (k : ℝ) + δ ≤ f' (n : ℝ))
    have hpart : Sk = Sk_mid ∪ (Sk_lo ∪ Sk_hi) := by
      ext n
      simp only [Sk, Sk_mid, Sk_lo, Sk_hi, Finset.mem_filter, Finset.mem_union, abs_lt]
      constructor
      · rintro ⟨hn, hk⟩
        by_cases h1 : (k : ℝ) - δ < f' (n : ℝ)
        · by_cases h2 : f' (n : ℝ) < (k : ℝ) + δ
          · left; exact ⟨hn, hk, by linarith, by linarith⟩
          · right; right; exact ⟨hn, hk, not_lt.mp h2⟩
        · right; left; exact ⟨hn, hk, not_lt.mp h1⟩
      · rintro (⟨hn, hk, _⟩ | ⟨hn, hk, _⟩ | ⟨hn, hk, _⟩) <;> exact ⟨hn, hk⟩
    have hdisj1 : Disjoint Sk_mid (Sk_lo ∪ Sk_hi) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Sk_mid, Sk_lo, Sk_hi, Finset.mem_filter, Finset.mem_union, abs_lt] at hn1 hn2
      rcases hn2 with ⟨_, _, hle⟩ | ⟨_, _, hge⟩ <;> linarith [hn1.2.2]
    have hdisj2 : Disjoint Sk_lo Sk_hi := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Sk_lo, Sk_hi, Finset.mem_filter] at hn1 hn2
      linarith [hn1.2.2, hn2.2.2]
    have hmid_bd : ‖∑ n ∈ Sk_mid, vdcE (f (n : ℝ))‖ ≤ 2 * δ / lam₂ + 1 := by
      by_cases hne : Sk_mid.Nonempty
      · let u := Sk_mid.min' hne
        let v := Sk_mid.max' hne
        have hu : u ∈ Sk_mid := Finset.min'_mem Sk_mid hne
        have hv_mem : v ∈ Sk_mid := Finset.max'_mem Sk_mid hne
        have hv : v ∈ Sk_mid := hv_mem
        simp only [Sk_mid, Finset.mem_filter, Finset.mem_Ioc] at hu hv
        have huv : u ≤ v := Finset.min'_le Sk_mid v hv_mem
        have hmvt := @hf'_mvt_lb (u : ℝ) (v : ℝ) (by exact_mod_cast (by omega : a ≤ u))
          (by exact_mod_cast huv) (by exact_mod_cast hv.1.2)
        have hdiff_lt : f' (v : ℝ) - f' (u : ℝ) < 2 * δ := by
          rw [abs_lt] at hu hv
          linarith [hu.2.2.1, hv.2.2.2]
        have hlen_R : (v : ℝ) - u < 2 * δ / lam₂ := by
          rw [lt_div_iff₀ hlam0]
          linarith
        have hsub_Icc : Sk_mid ⊆ Finset.Icc u v := fun n hn =>
          Finset.mem_Icc.mpr ⟨Finset.min'_le Sk_mid n hn, Finset.le_max' Sk_mid n hn⟩
        have hcard : (Sk_mid.card : ℝ) ≤ (v : ℝ) - u + 1 := by
          have : Sk_mid.card ≤ v - u + 1 := (Finset.card_le_card hsub_Icc).trans (by rw [Nat.card_Icc]; omega)
          have hcast : ((v - u + 1 : ℕ) : ℝ) = (v : ℝ) - u + 1 := by
            rw [Nat.cast_add, Nat.cast_sub huv, Nat.cast_one]
          exact (Nat.cast_le.mpr this).trans_eq hcast
        calc ‖∑ n ∈ Sk_mid, vdcE (f (n : ℝ))‖
            ≤ ∑ _n ∈ Sk_mid, (1 : ℝ) := (norm_sum_le _ _).trans_eq (by simp [norm_vdcE])
          _ = (Sk_mid.card : ℝ) := by simp
          _ ≤ (v : ℝ) - u + 1 := hcard
          _ ≤ 2 * δ / lam₂ + 1 := by linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, norm_zero]
        positivity
    have hlo_bd : ‖∑ n ∈ Sk_lo, vdcE (f (n : ℝ))‖ ≤ 2 / δ := by
      have hconv : ∀ x y z : ℝ, x ≤ y → y ≤ z →
          (round x = k ∧ x ≤ (k : ℝ) - δ) → (round z = k ∧ z ≤ (k : ℝ) - δ) →
          (round y = k ∧ y ≤ (k : ℝ) - δ) := by
        intro x y z hxy hyz hx hz
        rw [round_eq_iff] at hx hz ⊢
        refine ⟨⟨hx.1.1.trans hxy, lt_of_le_of_lt hyz hz.1.2⟩, hyz.trans hz.2⟩
      rcases filter_monotone_interval hf'_mono.monotoneOn _ hconv Sk_lo rfl with
        h0 | ⟨u, v, huv, hau, hvb, hEq⟩
      · rw [h0, Finset.sum_empty, norm_zero]; positivity
      · rw [hEq]
        have hsub : Set.Icc (u : ℝ) (v : ℝ) ⊆ Set.Icc (a : ℝ) (b : ℝ) :=
          Set.Icc_subset_Icc (by exact_mod_cast (by omega : a ≤ u)) (by exact_mod_cast hvb)
        refine vanDerCorput_first_deriv_mod_one huv hδ_pos hδ_half (m := k - 1)
          (fun t ht => hf t (hsub ht)) (Or.inl (hf'_mono.monotoneOn.mono hsub)) fun t ht => ?_
        have hut : u ≤ v := huv
        have hu_mem : u ∈ Sk_lo := by rw [hEq]; exact Finset.left_mem_Icc.mpr huv
        have hv_mem : v ∈ Sk_lo := by rw [hEq]; exact Finset.right_mem_Icc.mpr huv
        simp only [Sk_lo, Finset.mem_filter] at hu_mem hv_mem
        have hfu : f' (u : ℝ) ≤ f' t := hf'_mono.monotoneOn (hsub (Set.left_mem_Icc.mpr (by exact_mod_cast huv)))
          (hsub ht) ht.1
        have hfv : f' t ≤ f' (v : ℝ) := hf'_mono.monotoneOn (hsub ht)
          (hsub (Set.right_mem_Icc.mpr (by exact_mod_cast huv))) ht.2
        have hru := (round_eq_iff.mp hu_mem.2.1).1
        push_cast
        constructor <;> linarith [hδ_lt, hv_mem.2.2]
    have hhi_bd : ‖∑ n ∈ Sk_hi, vdcE (f (n : ℝ))‖ ≤ 2 / δ := by
      have hconv : ∀ x y z : ℝ, x ≤ y → y ≤ z →
          (round x = k ∧ (k : ℝ) + δ ≤ x) → (round z = k ∧ (k : ℝ) + δ ≤ z) →
          (round y = k ∧ (k : ℝ) + δ ≤ y) := by
        intro x y z hxy hyz hx hz
        rw [round_eq_iff] at hx hz ⊢
        refine ⟨⟨hx.1.1.trans hxy, lt_of_le_of_lt hyz hz.1.2⟩, hx.2.trans hxy⟩
      rcases filter_monotone_interval hf'_mono.monotoneOn _ hconv Sk_hi rfl with
        h0 | ⟨u, v, huv, hau, hvb, hEq⟩
      · rw [h0, Finset.sum_empty, norm_zero]; positivity
      · rw [hEq]
        have hsub : Set.Icc (u : ℝ) (v : ℝ) ⊆ Set.Icc (a : ℝ) (b : ℝ) :=
          Set.Icc_subset_Icc (by exact_mod_cast (by omega : a ≤ u)) (by exact_mod_cast hvb)
        refine vanDerCorput_first_deriv_mod_one huv hδ_pos hδ_half (m := k)
          (fun t ht => hf t (hsub ht)) (Or.inl (hf'_mono.monotoneOn.mono hsub)) fun t ht => ?_
        have hu_mem : u ∈ Sk_hi := by rw [hEq]; exact Finset.left_mem_Icc.mpr huv
        have hv_mem : v ∈ Sk_hi := by rw [hEq]; exact Finset.right_mem_Icc.mpr huv
        simp only [Sk_hi, Finset.mem_filter] at hu_mem hv_mem
        have hfu : f' (u : ℝ) ≤ f' t := hf'_mono.monotoneOn (hsub (Set.left_mem_Icc.mpr (by exact_mod_cast huv)))
          (hsub ht) ht.1
        have hfv : f' t ≤ f' (v : ℝ) := hf'_mono.monotoneOn (hsub ht)
          (hsub (Set.right_mem_Icc.mpr (by exact_mod_cast huv))) ht.2
        have hrv := (round_eq_iff.mp hv_mem.2.1).2
        constructor <;> linarith [hδ_lt, hu_mem.2.2]
    change ‖∑ n ∈ Sk, vdcE (f (n : ℝ))‖ ≤ 2 * δ / lam₂ + 1 + 4 / δ
    rw [hpart, Finset.sum_union hdisj1, Finset.sum_union hdisj2]
    calc ‖∑ n ∈ Sk_mid, vdcE (f (n : ℝ)) +
            (∑ n ∈ Sk_lo, vdcE (f (n : ℝ)) + ∑ n ∈ Sk_hi, vdcE (f (n : ℝ)))‖
        ≤ ‖∑ n ∈ Sk_mid, vdcE (f (n : ℝ))‖ +
            (‖∑ n ∈ Sk_lo, vdcE (f (n : ℝ))‖ + ‖∑ n ∈ Sk_hi, vdcE (f (n : ℝ))‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ (2 * δ / lam₂ + 1) + (2 / δ + 2 / δ) := add_le_add hmid_bd (add_le_add hlo_bd hhi_bd)
      _ = 2 * δ / lam₂ + 1 + 4 / δ := by ring
  have hK_card : (Kset.card : ℝ) ≤ c * lam₂ * N + 4 := by
    have hcard_int : Kset.card ≤ (⌈f' (b : ℝ)⌉ + 1 - ⌊f' (a : ℝ)⌋).toNat := by
      dsimp only [Kset]
      rw [Int.card_Icc]
    have hcard_R : (Kset.card : ℝ) ≤ (⌈f' (b : ℝ)⌉ : ℝ) + 1 - (⌊f' (a : ℝ)⌋ : ℝ) := by
      have hle : (Kset.card : ℤ) ≤ ⌈f' (b : ℝ)⌉ + 1 - ⌊f' (a : ℝ)⌋ := by
        have h1 : ⌊f' (a : ℝ)⌋ ≤ ⌈f' (b : ℝ)⌉ + 1 := by
          have hfab : f' (a : ℝ) ≤ f' (b : ℝ) := hf'_mono.monotoneOn
            (Set.left_mem_Icc.mpr (by exact_mod_cast (by omega : a ≤ b)))
            (Set.right_mem_Icc.mpr (by exact_mod_cast (by omega : a ≤ b)))
            (by exact_mod_cast (by omega : a ≤ b))
          have h1' : (⌊f' (a : ℝ)⌋ : ℝ) ≤ f' (a : ℝ) := Int.floor_le _
          have h2' : f' (b : ℝ) ≤ (⌈f' (b : ℝ)⌉ : ℝ) := Int.le_ceil _
          exact (Int.cast_le (R := ℝ)).mp (by push_cast; linarith)
        omega
      exact_mod_cast hle
    have hceil_lt : (⌈f' (b : ℝ)⌉ : ℝ) < f' (b : ℝ) + 1 := Int.ceil_lt_add_one _
    have hfloor_gt : f' (a : ℝ) - 1 < (⌊f' (a : ℝ)⌋ : ℝ) := Int.sub_one_lt_floor _
    linarith [hf'_mvt_ub]
  have hδ_inv : δ⁻¹ = lam₂ ^ (-(1 / 2 : ℝ)) := by
    dsimp only [δ]
    rw [← Real.rpow_neg hlam0.le]
  have hδ_div : δ / lam₂ = lam₂ ^ (-(1 / 2 : ℝ)) := by
    dsimp only [δ]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one lam₂, ← Real.rpow_add hlam0]
    norm_num
  have hinner_eq : 2 * δ / lam₂ + 1 + 4 / δ = 6 * lam₂ ^ (-(1 / 2 : ℝ)) + 1 := by
    rw [mul_div_assoc, hδ_div, show 4 / δ = 4 * δ⁻¹ from div_eq_mul_inv 4 δ, hδ_inv]
    ring
  have hlam_le_sqrt : lam₂ ≤ lam₂ ^ (1 / 2 : ℝ) := by
    have h1 : lam₂ ≤ 1 := hsmall.le.trans (by norm_num)
    have hpow1 : lam₂ ^ (1 : ℝ) ≤ lam₂ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hlam0 h1 (by norm_num)
    simpa [Real.rpow_one] using hpow1
  calc ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ))‖
      ≤ ∑ k ∈ Kset,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun (n : ℕ) => round (f' (n : ℝ)) = k),
            vdcE (f (n : ℝ))‖ := by
        rw [hfiber]; exact norm_sum_le _ _
    _ ≤ ∑ _k ∈ Kset, (2 * δ / lam₂ + 1 + 4 / δ) := Finset.sum_le_sum hk_bound
    _ = (Kset.card : ℝ) * (6 * lam₂ ^ (-(1 / 2 : ℝ)) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, hinner_eq]
    _ ≤ (c * lam₂ * N + 4) * (6 * lam₂ ^ (-(1 / 2 : ℝ)) + 1) := by
        gcongr
    _ = 6 * c * N * (lam₂ * lam₂ ^ (-(1 / 2 : ℝ))) + c * N * lam₂ +
          24 * lam₂ ^ (-(1 / 2 : ℝ)) + 4 := by ring
    _ ≤ 6 * c * N * lam₂ ^ (1 / 2 : ℝ) + c * N * lam₂ ^ (1 / 2 : ℝ) +
          24 * lam₂ ^ (-(1 / 2 : ℝ)) + 2 * (N * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ))) := by
        have hmul : lam₂ * lam₂ ^ (-(1 / 2 : ℝ)) = lam₂ ^ (1 / 2 : ℝ) := by
          conv_lhs => (lhs; rw [← Real.rpow_one lam₂])
          rw [← Real.rpow_add hlam0]
          norm_num
        rw [hmul]
        have hcn : c * N * lam₂ ≤ c * N * lam₂ ^ (1 / 2 : ℝ) := by gcongr
        linarith [hsum_ge2, hcn]
    _ = (7 * c + 2) * (N * lam₂ ^ (1 / 2 : ℝ)) + 26 * lam₂ ^ (-(1 / 2 : ℝ)) := by ring
    _ ≤ (20 * c + 20) * (N * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ))) := by
        have h1 : 7 * c + 2 ≤ 20 * c + 20 := by linarith
        have h2 : (26 : ℝ) ≤ 20 * c + 20 := by linarith
        nlinarith [mul_pos (show 0 < N by linarith) hsqrt_pos, hinv_sqrt_pos]

/-- **van der Corput second derivative test**: if `f` is `C²` on `[a, b]` (`a + 1 ≤ b`) with
`λ₂ ≤ |f''(t)| ≤ c * λ₂` (`0 < λ₂`, `1 ≤ c`), then
`‖∑_{n ∈ Ioc a b} exp(2πi f(n))‖ ≤ (20 * c + 20) * ((b - a) * λ₂^(1/2) + λ₂^(-1/2))`. -/
theorem vanDerCorput_second_deriv {f f' f'' : ℝ → ℝ} {a b : ℕ}
    (hab : a + 1 ≤ b) {lam₂ c : ℝ} (hlam0 : 0 < lam₂) (hc : 1 ≤ c)
    (hf : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt f' (f'' t) t)
    (hf''_cont : ContinuousOn f'' (Set.Icc (a : ℝ) (b : ℝ)))
    (hbd : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), lam₂ ≤ |f'' t| ∧ |f'' t| ≤ c * lam₂) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      (20 * c + 20) * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-(1 / 2 : ℝ))) := by
  have hne0 : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), f'' t ≠ 0 := fun t ht =>
    abs_pos.mp (lt_of_lt_of_le hlam0 (hbd t ht).1)
  have hle_ab : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : a ≤ b)
  by_cases ha_pos : 0 < f'' (a : ℝ)
  · refine vanDerCorput_second_deriv_pos hab hlam0 hc hf hf' fun t ht => ?_
    have ht_pos : 0 < f'' t := by
      by_contra hle
      have hlt0 : f'' t < 0 := lt_of_le_of_ne (not_lt.mp hle) (hne0 t ht)
      obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_Icc' ht.1
        (hf''_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨hlt0.le, ha_pos.le⟩
      exact hne0 ξ (Set.Icc_subset_Icc_right ht.2 hξ) hξ0
    simpa [abs_of_pos ht_pos] using hbd t ht
  · have ha_neg : f'' (a : ℝ) < 0 :=
      lt_of_le_of_ne (not_lt.mp ha_pos) (hne0 (a : ℝ) (Set.left_mem_Icc.mpr hle_ab))
    let gf : ℝ → ℝ := fun t => -f t
    let gf' : ℝ → ℝ := fun t => -f' t
    let gf'' : ℝ → ℝ := fun t => -f'' t
    have hconj :
        ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ =
          ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (gf (n : ℝ) : ℂ) * Complex.I)‖ := by
      have hs : ∑ n ∈ Finset.Ioc a b, vdcE (gf (n : ℝ)) =
          starRingEnd ℂ (∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ))) := by
        simp only [gf, map_sum, ← Complex.star_def, star_vdcE]
      change ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ))‖ = ‖∑ n ∈ Finset.Ioc a b, vdcE (gf (n : ℝ))‖
      rw [hs, Complex.norm_conj]
    rw [hconj]
    have hgf : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt gf (gf' t) t := fun t ht => (hf t ht).neg
    have hgf' : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt gf' (gf'' t) t := fun t ht => (hf' t ht).neg
    refine vanDerCorput_second_deriv_pos hab hlam0 hc hgf hgf' fun t ht => ?_
    have ht_neg : f'' t < 0 := by
      by_contra hle
      have hgt0 : 0 < f'' t := lt_of_le_of_ne (not_lt.mp hle) (hne0 t ht).symm
      obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_Icc ht.1
        (hf''_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨ha_neg.le, hgt0.le⟩
      exact hne0 ξ (Set.Icc_subset_Icc_right ht.2 hξ) hξ0
    simpa [gf'', abs_of_neg ht_neg] using hbd t ht

end DerivativeTests

section OscillatoryIntegrals

private lemma vanDerCorput_integral_first_deriv_mono_pos {F F' F'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    {m : ℝ} (hm : 0 < m)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.Icc a b, HasDerivAt F' (F'' t) t)
    (hF''_cont : ContinuousOn F'' (Set.Icc a b))
    (hmono : (∀ t ∈ Set.Icc a b, 0 ≤ F'' t) ∨ (∀ t ∈ Set.Icc a b, F'' t ≤ 0))
    (hpos : ∀ t ∈ Set.Icc a b, m ≤ F' t) :
    ‖∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I)‖ ≤ 4 / m := by
  have hF'_ne : ∀ t ∈ Set.Icc a b, (F' t : ℂ) ≠ 0 := fun t ht =>
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hm (hpos t ht)).ne'
  have hF'_cont : ContinuousOn F' (Set.Icc a b) := fun t ht =>
    (hF' t ht).continuousAt.continuousWithinAt
  let u : ℝ → ℂ := fun t => (Complex.I * (F' t : ℂ))⁻¹
  let u' : ℝ → ℂ := fun t => -(Complex.I * (F'' t : ℂ)) / (Complex.I * (F' t : ℂ)) ^ 2
  let v : ℝ → ℂ := fun t => Complex.exp ((F t : ℂ) * Complex.I)
  let v' : ℝ → ℂ := fun t => Complex.I * (F' t : ℂ) * Complex.exp ((F t : ℂ) * Complex.I)
  have hu : ∀ t ∈ Set.uIcc a b, HasDerivAt u (u' t) t := fun t ht => by
    rw [Set.uIcc_of_le hab] at ht
    have h1 : HasDerivAt (fun x => Complex.I * (F' x : ℂ)) (Complex.I * (F'' t : ℂ)) t :=
      (hF' t ht).ofReal_comp.const_mul Complex.I
    have hne : Complex.I * (F' t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (hF'_ne t ht)
    exact h1.inv hne
  have hv : ∀ t ∈ Set.uIcc a b, HasDerivAt v (v' t) t := fun t ht => by
    rw [Set.uIcc_of_le hab] at ht
    have h1 : HasDerivAt (fun x => (F x : ℂ) * Complex.I) ((F' t : ℂ) * Complex.I) t :=
      (hF t ht).ofReal_comp.mul_const Complex.I
    convert h1.cexp using 1
    dsimp only [v']; ring
  have hu' : IntervalIntegrable u' volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hnum : ContinuousOn (fun t => -(Complex.I * (F'' t : ℂ))) (Set.Icc a b) :=
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hF''_cont)).neg
    have hden : ContinuousOn (fun t => (Complex.I * (F' t : ℂ)) ^ 2) (Set.Icc a b) :=
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hF'_cont)).pow 2
    exact (hnum.div hden fun t ht =>
      pow_ne_zero 2 (mul_ne_zero Complex.I_ne_zero (hF'_ne t ht))).integrableOn_Icc
  have hv' : IntervalIntegrable v' volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    refine ContinuousOn.integrableOn_Icc ?_
    have hFc : ContinuousOn F (Set.Icc a b) := fun t ht =>
      (hF t ht).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hF'_cont)).mul
      (Complex.continuous_exp.comp_continuousOn ((Complex.continuous_ofReal.comp_continuousOn hFc).mul
        continuousOn_const))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hlhs : ∫ t in a..b, u t * v' t = ∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    have hne : Complex.I * (F' t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (hF'_ne t ht)
    dsimp only [u, v']
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hlhs] at hibp
  rw [hibp]
  have hbd_end : ‖u b * v b - u a * v a‖ ≤ 2 / m := by
    have hua : ‖u a * v a‖ ≤ 1 / m := by
      have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
      rw [norm_mul, show v a = Complex.exp ((F a : ℝ) * Complex.I) from rfl,
        Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hm (hpos a ha_mem)),
        one_div]
      exact inv_anti₀ hm (hpos a ha_mem)
    have hub : ‖u b * v b‖ ≤ 1 / m := by
      have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
      rw [norm_mul, show v b = Complex.exp ((F b : ℝ) * Complex.I) from rfl,
        Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hm (hpos b hb_mem)),
        one_div]
      exact inv_anti₀ hm (hpos b hb_mem)
    calc ‖u b * v b - u a * v a‖ ≤ ‖u b * v b‖ + ‖u a * v a‖ := norm_sub_le _ _
      _ ≤ 1 / m + 1 / m := add_le_add hub hua
      _ = 2 / m := by ring
  have hnorm_int : ‖∫ t in a..b, u' t * v t‖ ≤ 2 / m := by
    have hnorm_le : ‖∫ t in a..b, u' t * v t‖ ≤ ∫ t in a..b, ‖u' t * v t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have hfun_eq : ∀ t ∈ Set.uIcc a b, ‖u' t * v t‖ = |F'' t| / F' t ^ 2 := fun t ht => by
      rw [Set.uIcc_of_le hab] at ht
      rw [norm_mul, show v t = Complex.exp ((F t : ℝ) * Complex.I) from rfl,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      dsimp only [u']
      rw [norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    have hcongr : ∫ t in a..b, ‖u' t * v t‖ = ∫ t in a..b, |F'' t| / F' t ^ 2 :=
      intervalIntegral.integral_congr hfun_eq
    have hcalc : ∫ t in a..b, |F'' t| / F' t ^ 2 ≤ 2 / m := by
      have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
      have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
      rcases hmono with hnonneg | hnonpos
      · have hEq : ∀ t ∈ Set.uIcc a b, |F'' t| / F' t ^ 2 = F'' t / F' t ^ 2 := fun t ht => by
          rw [Set.uIcc_of_le hab] at ht
          rw [abs_of_nonneg (hnonneg t ht)]
        rw [intervalIntegral.integral_congr hEq]
        have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun x => -(F' x)⁻¹) (F'' t / F' t ^ 2) t :=
          fun t ht => by
            rw [Set.uIcc_of_le hab] at ht
            have hne : F' t ≠ 0 := (lt_of_lt_of_le hm (hpos t ht)).ne'
            convert ((hF' t ht).inv hne).neg using 1
            simp [div_eq_mul_inv]
        have hint : IntervalIntegrable (fun t => F'' t / F' t ^ 2) volume a b := by
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
          exact (hF''_cont.div (hF'_cont.pow 2) fun t ht =>
            pow_ne_zero 2 (lt_of_lt_of_le hm (hpos t ht)).ne').integrableOn_Icc
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
        have h1 : (F' a)⁻¹ ≤ 1 / m := one_div m ▸ inv_anti₀ hm (hpos a ha_mem)
        have h2 : 0 ≤ (F' b)⁻¹ := inv_nonneg.mpr (hm.le.trans (hpos b hb_mem))
        have h12 : 1 / m ≤ 2 / m := by
          rw [div_le_div_iff_of_pos_right hm]; norm_num
        linarith
      · have hEq : ∀ t ∈ Set.uIcc a b, |F'' t| / F' t ^ 2 = -(F'' t / F' t ^ 2) := fun t ht => by
          rw [Set.uIcc_of_le hab] at ht
          rw [abs_of_nonpos (hnonpos t ht), neg_div]
        rw [intervalIntegral.integral_congr hEq]
        have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun x => (F' x)⁻¹) (-(F'' t / F' t ^ 2)) t :=
          fun t ht => by
            rw [Set.uIcc_of_le hab] at ht
            have hne : F' t ≠ 0 := (lt_of_lt_of_le hm (hpos t ht)).ne'
            convert (hF' t ht).inv hne using 1
            simp [div_eq_mul_inv]
        have hint : IntervalIntegrable (fun t => -(F'' t / F' t ^ 2)) volume a b := by
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
          exact (hF''_cont.div (hF'_cont.pow 2) fun t ht =>
            pow_ne_zero 2 (lt_of_lt_of_le hm (hpos t ht)).ne').neg.integrableOn_Icc
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
        have h1 : (F' b)⁻¹ ≤ 1 / m := one_div m ▸ inv_anti₀ hm (hpos b hb_mem)
        have h2 : 0 ≤ (F' a)⁻¹ := inv_nonneg.mpr (hm.le.trans (hpos a ha_mem))
        have h12 : 1 / m ≤ 2 / m := by
          rw [div_le_div_iff_of_pos_right hm]; norm_num
        linarith
    exact hnorm_le.trans (hcongr ▸ hcalc)
  calc ‖u b * v b - u a * v a - ∫ t in a..b, u' t * v t‖
      ≤ ‖u b * v b - u a * v a‖ + ‖∫ t in a..b, u' t * v t‖ := norm_sub_le _ _
    _ ≤ 2 / m + 2 / m := add_le_add hbd_end hnorm_int
    _ = 4 / m := by ring

/-- **van der Corput first derivative integral bound**: if `F` is `C²` on `[a, b]` (`a ≤ b`) with
monotone `F'` and `|F'(t)| ≥ m > 0` on `[a, b]`, then
`‖∫ t in a..b, Complex.exp (F t * I)‖ ≤ 4 / m`. -/
theorem vanDerCorput_integral_first_deriv {F F' F'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    {m : ℝ} (hm : 0 < m)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.Icc a b, HasDerivAt F' (F'' t) t)
    (hF''_cont : ContinuousOn F'' (Set.Icc a b))
    (hmono : (∀ t ∈ Set.Icc a b, 0 ≤ F'' t) ∨ (∀ t ∈ Set.Icc a b, F'' t ≤ 0))
    (hbd : ∀ t ∈ Set.Icc a b, m ≤ |F' t|) :
    ‖∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I)‖ ≤ 4 / m := by
  have hF'_cont : ContinuousOn F' (Set.Icc a b) := fun t ht =>
    (hF' t ht).continuousAt.continuousWithinAt
  have hne0 : ∀ t ∈ Set.Icc a b, F' t ≠ 0 := fun t ht =>
    abs_pos.mp (lt_of_lt_of_le hm (hbd t ht))
  by_cases ha_pos : 0 < F' a
  · refine vanDerCorput_integral_first_deriv_mono_pos hab hm hF hF' hF''_cont hmono fun t ht => ?_
    have ht_pos : 0 < F' t := by
      by_contra hle
      have hlt0 : F' t < 0 := lt_of_le_of_ne (not_lt.mp hle) (hne0 t ht)
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' ht.1 (hF'_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨hlt0.le, ha_pos.le⟩
      exact hne0 c ⟨hc.1, hc.2.trans ht.2⟩ hc0
    simpa [abs_of_pos ht_pos] using hbd t ht
  · have ha_neg : F' a < 0 := lt_of_le_of_ne (not_lt.mp ha_pos) (hne0 a (Set.left_mem_Icc.mpr hab))
    let GF : ℝ → ℝ := fun t => -F t
    let GF' : ℝ → ℝ := fun t => -F' t
    let GF'' : ℝ → ℝ := fun t => -F'' t
    have hconj :
        ‖∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I)‖ =
          ‖∫ t in a..b, Complex.exp ((GF t : ℂ) * Complex.I)‖ := by
      have h1 : ∫ t in a..b, Complex.exp ((GF t : ℂ) * Complex.I) =
          starRingEnd ℂ (∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I)) := by
        rw [← intervalIntegral.intervalIntegral_conj]
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [← Complex.exp_conj]
        simp [GF, Complex.conj_ofReal]
      rw [h1, Complex.norm_conj]
    rw [hconj]
    have hGF : ∀ t ∈ Set.Icc a b, HasDerivAt GF (GF' t) t := fun t ht => (hF t ht).neg
    have hGF' : ∀ t ∈ Set.Icc a b, HasDerivAt GF' (GF'' t) t := fun t ht => (hF' t ht).neg
    have hmono' : (∀ t ∈ Set.Icc a b, 0 ≤ GF'' t) ∨ (∀ t ∈ Set.Icc a b, GF'' t ≤ 0) :=
      hmono.symm.imp (fun h t ht => neg_nonneg.mpr (h t ht)) (fun h t ht => neg_nonpos.mpr (h t ht))
    refine vanDerCorput_integral_first_deriv_mono_pos hab hm hGF hGF' hF''_cont.neg hmono' fun t ht => ?_
    have ht_neg : F' t < 0 := by
      by_contra hle
      have hgt0 : 0 < F' t := lt_of_le_of_ne (not_lt.mp hle) (hne0 t ht).symm
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc ht.1 (hF'_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨ha_neg.le, hgt0.le⟩
      exact hne0 c ⟨hc.1, hc.2.trans ht.2⟩ hc0
    simpa [GF', abs_of_neg ht_neg] using hbd t ht

/-- **van der Corput second derivative integral bound**: if `F` is `C²` on `[a, b]` (`a ≤ b`) with
`r ≤ |F''(t)|` (`0 < r`), then `‖∫ t in a..b, Complex.exp (F t * I)‖ ≤ 8 / Real.sqrt r`. -/
theorem vanDerCorput_integral_second_deriv {F F' F'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    {r : ℝ} (hr : 0 < r)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.Icc a b, HasDerivAt F' (F'' t) t)
    (hF''_cont : ContinuousOn F'' (Set.Icc a b))
    (hbd : ∀ t ∈ Set.Icc a b, r ≤ |F'' t|) :
    ‖∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I)‖ ≤ 8 / Real.sqrt r := by
  have hne0 : ∀ t ∈ Set.Icc a b, F'' t ≠ 0 := fun t ht =>
    abs_pos.mp (lt_of_lt_of_le hr (hbd t ht))
  have hsign : (∀ t ∈ Set.Icc a b, r ≤ F'' t) ∨ (∀ t ∈ Set.Icc a b, F'' t ≤ -r) := by
    by_cases ha_pos : 0 < F'' a
    · left
      intro t ht
      have ht_pos : 0 < F'' t := by
        by_contra hle
        have hlt0 : F'' t < 0 := lt_of_le_of_ne (not_lt.mp hle) (hne0 t ht)
        obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' ht.1 (hF''_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨hlt0.le, ha_pos.le⟩
        exact hne0 c ⟨hc.1, hc.2.trans ht.2⟩ hc0
      simpa [abs_of_pos ht_pos] using hbd t ht
    · right
      intro t ht
      have ha_neg : F'' a < 0 := lt_of_le_of_ne (not_lt.mp ha_pos) (hne0 a (Set.left_mem_Icc.mpr hab))
      have ht_neg : F'' t < 0 := by
        by_contra hle
        have hgt0 : 0 < F'' t := lt_of_le_of_ne (not_lt.mp hle) (hne0 t ht).symm
        obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc ht.1 (hF''_cont.mono (Set.Icc_subset_Icc_right ht.2)) ⟨ha_neg.le, hgt0.le⟩
        exact hne0 c ⟨hc.1, hc.2.trans ht.2⟩ hc0
      have h := hbd t ht
      rw [abs_of_neg ht_neg] at h
      linarith
  have hF_int : IntervalIntegrable (fun t => Complex.exp ((F t : ℂ) * Complex.I)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hFc : ContinuousOn F (Set.Icc a b) := fun t ht => (hF t ht).continuousAt.continuousWithinAt
    exact (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hFc).mul continuousOn_const)).integrableOn_Icc
  let δ : ℝ := 2 / Real.sqrt r
  have hδ : 0 < δ := by positivity
  have hδ_val : 2 * δ + 8 / (r * δ) = 8 / Real.sqrt r := by
    dsimp only [δ]
    have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    field_simp [(Real.sqrt_pos.mpr hr).ne']
    nlinarith [hs]
  suffices hpos_case : ∀ {G G' G'' : ℝ → ℝ},
      (∀ t ∈ Set.Icc a b, HasDerivAt G (G' t) t) →
      (∀ t ∈ Set.Icc a b, HasDerivAt G' (G'' t) t) →
      ContinuousOn G'' (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, r ≤ G'' t) →
      ‖∫ t in a..b, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ 8 / Real.sqrt r by
    rcases hsign with hp | hn
    · exact hpos_case hF hF' hF''_cont hp
    · let GF : ℝ → ℝ := fun t => -F t
      let GF' : ℝ → ℝ := fun t => -F' t
      let GF'' : ℝ → ℝ := fun t => -F'' t
      have hconj :
          ‖∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I)‖ =
            ‖∫ t in a..b, Complex.exp ((GF t : ℂ) * Complex.I)‖ := by
        have h1 : ∫ t in a..b, Complex.exp ((GF t : ℂ) * Complex.I) =
            starRingEnd ℂ (∫ t in a..b, Complex.exp ((F t : ℂ) * Complex.I)) := by
          rw [← intervalIntegral.intervalIntegral_conj]
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [← Complex.exp_conj]
          simp [GF, Complex.conj_ofReal]
        rw [h1, Complex.norm_conj]
      rw [hconj]
      have hGF : ∀ t ∈ Set.Icc a b, HasDerivAt GF (GF' t) t := fun t ht => (hF t ht).neg
      have hGF' : ∀ t ∈ Set.Icc a b, HasDerivAt GF' (GF'' t) t := fun t ht => (hF' t ht).neg
      exact hpos_case hGF hGF' hF''_cont.neg (fun t ht => by dsimp only [GF'']; linarith [hn t ht])
  intro G G' G'' hG hG' hG''_cont hG''_lb
  have hG'_cont : ContinuousOn G' (Set.Icc a b) := fun t ht =>
    (hG' t ht).continuousAt.continuousWithinAt
  have hG'_mvt : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ b → r * (y - x) ≤ G' y - G' x := by
    intro x y hx hxy hy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    have hcont : ContinuousOn G' (Set.Icc x y) := hG'_cont.mono (Set.Icc_subset_Icc hx hy)
    obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope G' G'' hlt hcont
      (fun t ht => hG' t ⟨hx.trans ht.1.le, ht.2.le.trans hy⟩)
    have hlb : r ≤ (G' y - G' x) / (y - x) := hEq ▸ hG''_lb ξ ⟨hx.trans hξ.1.le, hξ.2.le.trans hy⟩
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hlb
  have hG_int : ∀ {u v : ℝ}, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable (fun t => Complex.exp ((G t : ℂ) * Complex.I)) volume u v := by
    intro u v hu huv hv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv]
    have hGc : ContinuousOn G (Set.Icc u v) := fun t ht =>
      (hG t ⟨hu.trans ht.1, ht.2.trans hv⟩).continuousAt.continuousWithinAt
    exact (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hGc).mul continuousOn_const)).integrableOn_Icc
  have htriv_int : ∀ {u v : ℝ}, a ≤ u → u ≤ v → v ≤ b →
      ‖∫ t in u..v, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ v - u := by
    intro u v hu huv hv
    calc ‖∫ t in u..v, Complex.exp ((G t : ℂ) * Complex.I)‖
        ≤ ∫ t in u..v, ‖Complex.exp ((G t : ℂ) * Complex.I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm huv
      _ = ∫ _t in u..v, (1 : ℝ) := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [show (G t : ℂ) * Complex.I = ((G t : ℝ) : ℂ) * Complex.I from rfl,
            Complex.norm_exp_ofReal_mul_I]
      _ = v - u := by simp
  have houter_int : ∀ {u v : ℝ}, a ≤ u → u ≤ v → v ≤ b →
      (∀ t ∈ Set.Icc u v, r * δ ≤ |G' t|) →
      ‖∫ t in u..v, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ 4 / (r * δ) := by
    intro u v hu huv hv hbd'
    have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hu hv
    exact vanDerCorput_integral_first_deriv huv (mul_pos hr hδ) (fun t ht => hG t (hsub ht))
      (fun t ht => hG' t (hsub ht)) (hG''_cont.mono hsub)
      (Or.inl fun t ht => hr.le.trans (hG''_lb t (hsub ht))) hbd'
  by_cases hpos_a : 0 ≤ G' a
  · let u := min b (a + δ)
    have hau : a ≤ u := le_min hab (by linarith)
    have hub : u ≤ b := min_le_left _ _
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hG_int le_rfl hau hub)
      (hG_int hau hub le_rfl)
    rw [← hsplit]
    have h1 : ‖∫ t in a..u, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ δ :=
      (htriv_int le_rfl hau hub).trans (by linarith [min_le_right b (a + δ)])
    have h2 : ‖∫ t in u..b, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ 4 / (r * δ) := by
      rcases eq_or_lt_of_le hub with heq | hlt
      · simp [heq]; positivity
      · have hua : u = a + δ := by
          have : a + δ ≤ b := by
            by_contra hcon
            have : u = b := min_eq_left (not_le.mp hcon).le
            linarith
          exact min_eq_right this
        refine houter_int hau hub le_rfl fun t ht => ?_
        have hlb : r * δ ≤ G' t := by
          have hmvt := hG'_mvt le_rfl (by linarith [ht.1, hua]) ht.2
          nlinarith [ht.1, hua]
        exact hlb.trans (le_abs_self _)
    calc ‖(∫ t in a..u, _) + (∫ t in u..b, _)‖ ≤ ‖∫ t in a..u, _‖ + ‖∫ t in u..b, _‖ :=
          norm_add_le _ _
      _ ≤ δ + 4 / (r * δ) := add_le_add h1 h2
      _ ≤ 2 * δ + 8 / (r * δ) := by
          have h8 : 8 / (r * δ) = 2 * (4 / (r * δ)) := by ring
          nlinarith [hδ, show (0 : ℝ) ≤ 4 / (r * δ) by positivity]
      _ = 8 / Real.sqrt r := hδ_val
  · by_cases hneg_b : G' b ≤ 0
    · let u := max a (b - δ)
      have hau : a ≤ u := le_max_left _ _
      have hub : u ≤ b := max_le hab (by linarith)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (hG_int le_rfl hau hub)
        (hG_int hau hub le_rfl)
      rw [← hsplit]
      have h2 : ‖∫ t in u..b, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ δ :=
        (htriv_int hau hub le_rfl).trans (by linarith [le_max_right a (b - δ)])
      have h1 : ‖∫ t in a..u, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ 4 / (r * δ) := by
        rcases eq_or_lt_of_le hau with heq | hlt
        · simp [← heq]; positivity
        · have hub' : u = b - δ := by
            have : a ≤ b - δ := by
              by_contra hcon
              have : u = a := max_eq_left (not_le.mp hcon).le
              linarith
            exact max_eq_right this
          refine houter_int le_rfl hau hub fun t ht => ?_
          have hub_t : G' t ≤ -(r * δ) := by
            have hmvt := hG'_mvt ht.1 (by linarith [ht.2, hub']) le_rfl
            nlinarith [ht.2, hub']
          exact (by linarith : r * δ ≤ -G' t).trans (neg_le_abs _)
      calc ‖(∫ t in a..u, _) + (∫ t in u..b, _)‖ ≤ ‖∫ t in a..u, _‖ + ‖∫ t in u..b, _‖ :=
            norm_add_le _ _
        _ ≤ 4 / (r * δ) + δ := add_le_add h1 h2
        _ ≤ 2 * δ + 8 / (r * δ) := by
          have h8 : 8 / (r * δ) = 2 * (4 / (r * δ)) := by ring
          nlinarith [hδ, show (0 : ℝ) ≤ 4 / (r * δ) by positivity]
        _ = 8 / Real.sqrt r := hδ_val
    · have ha_neg : G' a < 0 := not_le.mp hpos_a
      have hb_pos : 0 < G' b := not_le.mp hneg_b
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hG'_cont ⟨ha_neg.le, hb_pos.le⟩
      let u := max a (c - δ)
      let v := min b (c + δ)
      have hau : a ≤ u := le_max_left _ _
      have huc : u ≤ c := max_le hc.1 (by linarith)
      have hcv : c ≤ v := le_min hc.2 (by linarith)
      have hvb : v ≤ b := min_le_left _ _
      have huv : u ≤ v := huc.trans hcv
      have hsplit_all :
          ∫ t in a..b, Complex.exp ((G t : ℂ) * Complex.I) =
            (∫ t in a..u, Complex.exp ((G t : ℂ) * Complex.I)) +
              (∫ t in u..v, Complex.exp ((G t : ℂ) * Complex.I)) +
              (∫ t in v..b, Complex.exp ((G t : ℂ) * Complex.I)) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals (hG_int le_rfl (hau.trans huv) hvb)
          (hG_int (hau.trans huv) hvb le_rfl)]
        congr 1
        exact (intervalIntegral.integral_add_adjacent_intervals (hG_int le_rfl hau (huv.trans hvb))
          (hG_int hau huv hvb)).symm
      rw [hsplit_all]
      have h1 : ‖∫ t in a..u, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ 4 / (r * δ) := by
        rcases eq_or_lt_of_le hau with heq | _
        · simp [← heq]; positivity
        · have hu_eq : u = c - δ := max_eq_right (by
            by_contra hcon
            have : u = a := max_eq_left (not_le.mp hcon).le
            linarith)
          refine houter_int le_rfl hau (huc.trans hc.2) fun t ht => ?_
          have hmvt := hG'_mvt ht.1 (ht.2.trans huc) hc.2
          have hle_neg : G' t ≤ -(r * δ) := by nlinarith [ht.2, hu_eq, hc0, hr]
          exact (by linarith : r * δ ≤ -G' t).trans (neg_le_abs _)
      have h2 : ‖∫ t in u..v, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ 2 * δ :=
        (htriv_int hau huv hvb).trans (by linarith [le_max_right a (c - δ), min_le_right b (c + δ)])
      have h3 : ‖∫ t in v..b, Complex.exp ((G t : ℂ) * Complex.I)‖ ≤ 4 / (r * δ) := by
        rcases eq_or_lt_of_le hvb with heq | _
        · simp [heq]; positivity
        · have hv_eq : v = c + δ := min_eq_right (by
            by_contra hcon
            have : v = b := min_eq_left (not_le.mp hcon).le
            linarith)
          refine houter_int (hc.1.trans hcv) hvb le_rfl fun t ht => ?_
          have hmvt := hG'_mvt hc.1 (hcv.trans ht.1) ht.2
          have hge_pos : r * δ ≤ G' t := by nlinarith [ht.1, hv_eq, hc0, hr]
          exact hge_pos.trans (le_abs_self _)
      calc ‖(∫ t in a..u, _) + (∫ t in u..v, _) + (∫ t in v..b, _)‖
          ≤ ‖(∫ t in a..u, _) + (∫ t in u..v, _)‖ + ‖∫ t in v..b, _‖ := norm_add_le _ _
        _ ≤ (‖∫ t in a..u, _‖ + ‖∫ t in u..v, _‖) + ‖∫ t in v..b, _‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ ≤ 4 / (r * δ) + 2 * δ + 4 / (r * δ) := by linarith
        _ = 2 * δ + 8 / (r * δ) := by ring
        _ = 8 / Real.sqrt r := hδ_val

end OscillatoryIntegrals

section ProcessAAndProcessB

/-- **Weyl–van der Corput differencing inequality** (fundamental inequality for Process A):
for any `f : ℝ → ℝ`, `M N : ℕ`, and integer shift parameter `H ≥ 1`,
`H * ‖∑_{n ∈ Ioc M (M + N)} e(f(n))‖² ≤ (N + H) * ((N + H) + 2 * ∑_{r=1}^{H-1} (1 - r/H) * ‖∑_{n ∈ Ioc M (M + N - r)} e(f(n+r) - f(n))‖)`. -/
theorem vanDerCorput_weyl_differencing (f : ℝ → ℝ) (M N H : ℕ) (hH : 1 ≤ H) :
    (H : ℝ) * ‖∑ n ∈ Finset.Ioc M (M + N), Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      ((N : ℝ) + H) *
        (((N : ℝ) + H) +
          2 * ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
            ‖∑ n ∈ Finset.Ioc M (M + N - r),
              Complex.exp (2 * Real.pi * ((f ((n + r : ℕ) : ℝ) - f (n : ℝ) : ℝ) : ℂ) * Complex.I)‖) := by
  let extSum : ℤ → ℂ := fun n =>
    if (M : ℤ) < n ∧ n ≤ (M + N : ℤ) then vdcE (f (n : ℝ)) else 0
  have hS_eq :
      ∑ n ∈ Finset.Ioc M (M + N), vdcE (f (n : ℝ)) =
        ∑ n ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), extSum n := by
    refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_Ioc] at hn ⊢; omega
    · intro n₁ _ n₂ _ h; exact Int.ofNat.inj h
    · intro z hz
      simp only [Finset.mem_Ioc] at hz
      refine ⟨z.toNat, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      simp [extSum, show (M : ℤ) < (n : ℤ) ∧ (n : ℤ) ≤ (M + N : ℤ) by omega]
  let BigI := Finset.Ioc ((M : ℤ) - H + 1) (M + N : ℤ)
  have hHS_eq :
      (H : ℂ) * ∑ n ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), extSum n =
        ∑ n ∈ BigI, ∑ h ∈ Finset.range H, extSum (n + (h : ℤ)) := by
    have hswap :
        ∑ n ∈ BigI, ∑ h ∈ Finset.range H, extSum (n + (h : ℤ)) =
          ∑ h ∈ Finset.range H, ∑ n ∈ BigI, extSum (n + (h : ℤ)) := Finset.sum_comm
    rw [hswap]
    have hinner : ∀ h ∈ Finset.range H,
        ∑ n ∈ BigI, extSum (n + (h : ℤ)) = ∑ n ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), extSum n := by
      intro h hh
      simp only [Finset.mem_range] at hh
      have hsplit : ∑ n ∈ BigI, extSum (n + (h : ℤ)) =
          ∑ k ∈ Finset.Ioc ((M : ℤ) - H + 1 + h) (M + N + h : ℤ), extSum k := by
        refine Finset.sum_bij (fun n _ => n + h) ?_ ?_ ?_ ?_
        · intro n hn; simp only [BigI, Finset.mem_Ioc] at hn ⊢; omega
        · intro n₁ _ n₂ _ heq; omega
        · intro k hk
          simp only [Finset.mem_Ioc] at hk
          refine ⟨k - h, Finset.mem_Ioc.mpr (by omega), by omega⟩
        · intro n _; rfl
      rw [hsplit]
      symm
      refine Finset.sum_subset (fun k hk => ?_) (fun k hk hnot => ?_)
      · simp only [Finset.mem_Ioc] at hk ⊢; omega
      · simp only [Finset.mem_Ioc] at hk hnot
        have : ¬ ((M : ℤ) < k ∧ k ≤ (M + N : ℤ)) := by omega
        simp [extSum, this]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcs :
      (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), extSum n‖ ^ 2 ≤
        (BigI.card : ℝ) * ∑ n ∈ BigI, ‖∑ h ∈ Finset.range H, extSum (n + (h : ℤ))‖ ^ 2 := by
    have h1 : ‖(H : ℂ) * ∑ n ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), extSum n‖ ^ 2 =
        (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), extSum n‖ ^ 2 := by
      rw [norm_mul, Complex.norm_natCast, mul_pow]
    rw [← h1, hHS_eq]
    calc ‖∑ n ∈ BigI, ∑ h ∈ Finset.range H, extSum (n + (h : ℤ))‖ ^ 2
        ≤ (∑ n ∈ BigI, ‖∑ h ∈ Finset.range H, extSum (n + (h : ℤ))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (BigI.card : ℝ) * ∑ n ∈ BigI, ‖∑ h ∈ Finset.range H, extSum (n + (h : ℤ))‖ ^ 2 := by
          simpa using sq_sum_le_card_mul_sum_sq (s := BigI)
            (f := fun n => ‖∑ h ∈ Finset.range H, extSum (n + (h : ℤ))‖)
  have hBigI_card : (BigI.card : ℝ) ≤ (N : ℝ) + H := by
    have hcard : BigI.card ≤ N + H := by
      dsimp only [BigI]
      rw [Int.card_Ioc]
      omega
    exact_mod_cast hcard
  have hexp_sum :
      ∑ n ∈ BigI, ‖∑ h ∈ Finset.range H, extSum (n + (h : ℤ))‖ ^ 2 =
        (∑ n ∈ BigI, ∑ h ∈ Finset.range H, ‖extSum (n + (h : ℤ))‖ ^ 2) +
          2 * (∑ r ∈ Finset.Ico 1 H, (H - r : ℝ) *
            (∑ n ∈ Finset.Ioc M (M + N - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))).re) := by
    have hsq_term : ∀ n ∈ BigI,
        (‖∑ h ∈ Finset.range H, extSum (n + (h : ℤ))‖ ^ 2 : ℝ) =
          (∑ h ∈ Finset.range H, ‖extSum (n + (h : ℤ))‖ ^ 2) +
            2 * ∑ r ∈ Finset.Ico 1 H, ∑ h ∈ Finset.range (H - r),
              (extSum (n + ((h + r : ℕ) : ℤ)) * star (extSum (n + (h : ℤ)))).re := by
      intro n _
      rw [← Complex.normSq_eq_norm_sq]
      have hre0 : Complex.normSq (∑ h ∈ Finset.range H, extSum (n + (h : ℤ))) =
          ((starRingEnd ℂ (∑ h ∈ Finset.range H, extSum (n + (h : ℤ)))) *
            (∑ h ∈ Finset.range H, extSum (n + (h : ℤ)))).re := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      rw [hre0]
      have hre : ((starRingEnd ℂ (∑ h ∈ Finset.range H, extSum (n + (h : ℤ)))) *
            (∑ h ∈ Finset.range H, extSum (n + (h : ℤ)))).re =
          ∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
            (extSum (n + (h₁ : ℤ)) * star (extSum (n + (h₂ : ℤ)))).re := by
        rw [map_sum, Finset.sum_mul]
        simp only [Finset.mul_sum, Complex.re_sum, ← Complex.star_def]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h₁ _ => Finset.sum_congr rfl fun h₂ _ => ?_
        rw [mul_comm]
      have hsplit_pairs :
          ∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
              (extSum (n + (h₁ : ℤ)) * star (extSum (n + (h₂ : ℤ)))).re =
            (∑ h ∈ Finset.range H, ‖extSum (n + (h : ℤ))‖ ^ 2) +
              2 * ∑ r ∈ Finset.Ico 1 H, ∑ h ∈ Finset.range (H - r),
                (extSum (n + ((h + r : ℕ) : ℤ)) * star (extSum (n + (h : ℤ)))).re := by
        let fpair : ℕ × ℕ → ℝ := fun p =>
          (extSum (n + (p.1 : ℤ)) * star (extSum (n + (p.2 : ℤ)))).re
        have hdiag : ∀ h ∈ Finset.range H, fpair (h, h) = ‖extSum (n + (h : ℤ))‖ ^ 2 := fun h _ => by
          dsimp only [fpair]
          rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
            Complex.ofReal_re, Complex.normSq_eq_norm_sq]
        have hsymm : ∀ h₁ h₂ : ℕ, fpair (h₂, h₁) = fpair (h₁, h₂) := fun h₁ h₂ => by
          dsimp only [fpair]
          have hst : extSum (n + (h₂ : ℤ)) * star (extSum (n + (h₁ : ℤ))) =
              star (extSum (n + (h₁ : ℤ)) * star (extSum (n + (h₂ : ℤ)))) := by
            simp [mul_comm]
          rw [hst, Complex.star_def, Complex.conj_re]
        let S := Finset.range H ×ˢ Finset.range H
        let Sdiag := S.filter (fun p => p.1 = p.2)
        let Sup := S.filter (fun p => p.2 < p.1)
        let Slo := S.filter (fun p => p.1 < p.2)
        have hpart : S = Sdiag ∪ (Sup ∪ Slo) := by
          ext p
          simp only [Sdiag, Sup, Slo, Finset.mem_filter, Finset.mem_union]
          rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
          · have h1 : p.1 ≠ p.2 := hlt.ne
            have h2 : ¬ p.2 < p.1 := hlt.not_gt
            tauto
          · have h1 : ¬ p.2 < p.1 := by omega
            have h2 : ¬ p.1 < p.2 := by omega
            tauto
          · have h1 : p.1 ≠ p.2 := hgt.ne'
            have h2 : ¬ p.1 < p.2 := hgt.not_gt
            tauto
        have hd1 : Disjoint Sdiag (Sup ∪ Slo) := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [Sdiag, Sup, Slo, Finset.mem_filter, Finset.mem_union] at h1 h2
          omega
        have hd2 : Disjoint Sup Slo := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [Sup, Slo, Finset.mem_filter] at h1 h2
          omega
        have hS_eq : ∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H, fpair (h₁, h₂) =
            ∑ p ∈ S, fpair p :=
          (Finset.sum_product' (Finset.range H) (Finset.range H) (fun h₁ h₂ => fpair (h₁, h₂))).symm
        rw [hS_eq, hpart, Finset.sum_union hd1, Finset.sum_union hd2]
        have hdiag_sum : ∑ p ∈ Sdiag, fpair p = ∑ h ∈ Finset.range H, ‖extSum (n + (h : ℤ))‖ ^ 2 := by
          refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
          · intro p hp; simp only [Sdiag, S, Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
          · intro p₁ hp₁ p₂ hp₂ heq
            simp only [Sdiag, Finset.mem_filter] at hp₁ hp₂
            exact Prod.ext heq (by omega)
          · intro h hh
            refine ⟨(h, h), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hh, hh⟩, rfl⟩, rfl⟩
          · intro p hp
            simp only [Sdiag, S, Finset.mem_filter, Finset.mem_product] at hp
            rw [show p = (p.1, p.1) from Prod.ext rfl hp.2.symm]
            exact hdiag p.1 hp.1.1
        have hlo_eq_up : ∑ p ∈ Slo, fpair p = ∑ p ∈ Sup, fpair p := by
          refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
          · intro p hp
            simp only [Slo, Sup, S, Finset.mem_filter, Finset.mem_product] at hp ⊢
            exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
          · intro p₁ _ p₂ _ heq; exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
          · intro p hp
            simp only [Slo, Sup, S, Finset.mem_filter, Finset.mem_product] at hp ⊢
            exact ⟨(p.2, p.1), ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
          · intro p _; exact (hsymm p.1 p.2).symm
        have hup_eq : ∑ p ∈ Sup, fpair p =
            ∑ r ∈ Finset.Ico 1 H, ∑ h ∈ Finset.range (H - r), fpair (h + r, h) := by
          rw [Finset.sum_sigma' (Finset.Ico 1 H) (fun r => Finset.range (H - r))
            (fun r h => fpair (h + r, h))]
          refine Finset.sum_bij (fun p _ => ⟨p.1 - p.2, p.2⟩) ?_ ?_ ?_ ?_
          · intro p hp
            simp only [Sup, S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
            refine Finset.mem_sigma.mpr ?_
            dsimp only
            exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Finset.mem_range.mpr (by omega)⟩
          · intro p₁ hp₁ p₂ hp₂ heq
            simp only [Sup, Finset.mem_filter] at hp₁ hp₂
            have h1 : p₁.1 - p₁.2 = p₂.1 - p₂.2 := congrArg Sigma.fst heq
            have h2 : p₁.2 = p₂.2 := congrArg Sigma.snd heq
            exact Prod.ext (by omega) h2
          · intro ⟨r, h⟩ hq
            simp only [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hq
            refine ⟨(h + r, h), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
                Finset.mem_range.mpr (by omega)⟩, by omega⟩, ?_⟩
            dsimp only
            rw [Nat.add_sub_cancel_left]
          · intro p hp
            simp only [Sup, Finset.mem_filter] at hp
            congr 1; exact Prod.ext (by dsimp only; omega) rfl
        rw [hdiag_sum, hlo_eq_up, hup_eq]
        ring
      rw [hre, hsplit_pairs]
    rw [Finset.sum_congr rfl hsq_term, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [Finset.mem_Ico] at hr
    rw [Finset.sum_comm]
    have hshift_r : ∀ h ∈ Finset.range (H - r),
        ∑ n ∈ BigI, (extSum (n + ((h + r : ℕ) : ℤ)) * star (extSum (n + (h : ℤ)))).re =
          (∑ k ∈ Finset.Ioc M (M + N - r), vdcE (f ((k + r : ℕ) : ℝ) - f (k : ℝ))).re := by
      intro h hh
      simp only [Finset.mem_range] at hh
      simp only [← Complex.re_sum]
      congr 1
      have hreidx :
          ∑ n ∈ BigI, extSum (n + ((h + r : ℕ) : ℤ)) * star (extSum (n + (h : ℤ))) =
            ∑ k ∈ Finset.Ioc ((M : ℤ) - H + 1 + h) (M + N + h : ℤ),
              extSum (k + (r : ℤ)) * star (extSum k) := by
        refine Finset.sum_bij (fun n _ => n + (h : ℤ)) ?_ ?_ ?_ ?_
        · intro n hn; simp only [BigI, Finset.mem_Ioc] at hn ⊢; omega
        · intro n₁ _ n₂ _ heq; omega
        · intro k hk
          simp only [Finset.mem_Ioc] at hk
          refine ⟨k - (h : ℤ), Finset.mem_Ioc.mpr (by omega), by omega⟩
        · intro n _; congr 2; push_cast; ring
      rw [hreidx]
      have hsub : Finset.Ioc (M : ℤ) ((M + N : ℤ) - r) ⊆
          Finset.Ioc ((M : ℤ) - H + 1 + h) (M + N + h : ℤ) := by
        intro k hk; simp only [Finset.mem_Ioc] at hk ⊢; omega
      have hEq1 :
          ∑ k ∈ Finset.Ioc ((M : ℤ) - H + 1 + h) (M + N + h : ℤ),
              extSum (k + (r : ℤ)) * star (extSum k) =
            ∑ k ∈ Finset.Ioc (M : ℤ) ((M + N : ℤ) - r),
              extSum (k + (r : ℤ)) * star (extSum k) := by
        symm
        refine Finset.sum_subset hsub fun k hk hnot => ?_
        simp only [Finset.mem_Ioc] at hk hnot
        by_cases hk_mem : (M : ℤ) < k ∧ k ≤ (M + N : ℤ)
        · have hkr : ¬ ((M : ℤ) < k + (r : ℤ) ∧ k + (r : ℤ) ≤ (M + N : ℤ)) := by omega
          simp [extSum, hkr]
        · simp [extSum, hk_mem]
      rw [hEq1]
      refine Finset.sum_bij (fun k _ => k.toNat) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Ioc] at hk ⊢; omega
      · intro k₁ hk₁ k₂ hk₂ heq
        simp only [Finset.mem_Ioc] at hk₁ hk₂
        omega
      · intro k hk
        simp only [Finset.mem_Ioc] at hk
        refine ⟨(k : ℤ), Finset.mem_Ioc.mpr (by omega), by simp⟩
      · intro k hk
        simp only [Finset.mem_Ioc] at hk
        have h1 : (M : ℤ) < k ∧ k ≤ (M + N : ℤ) := by omega
        have h2 : (M : ℤ) < k + (r : ℤ) ∧ k + (r : ℤ) ≤ (M + N : ℤ) := by omega
        simp only [extSum, h1, h2, and_self, ↓reduceIte, star_vdcE, ← vdcE_add]
        congr 1
        have hk_cast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
          have : (k.toNat : ℤ) = k := by omega
          exact_mod_cast this
        rw [Nat.cast_add, hk_cast]
        push_cast
        ring
    rw [Finset.sum_congr rfl hshift_r, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Nat.cast_sub hr.2.le]
  have hdiag_bd : ∑ n ∈ BigI, ∑ h ∈ Finset.range H, ‖extSum (n + (h : ℤ))‖ ^ 2 ≤
      (H : ℝ) * (N : ℝ) := by
    rw [Finset.sum_comm]
    have hinner : ∀ h ∈ Finset.range H,
        ∑ n ∈ BigI, ‖extSum (n + (h : ℤ))‖ ^ 2 ≤ (N : ℝ) := by
      intro h hh
      simp only [Finset.mem_range] at hh
      have hreidx : ∑ n ∈ BigI, ‖extSum (n + (h : ℤ))‖ ^ 2 =
          ∑ k ∈ Finset.Ioc ((M : ℤ) - H + 1 + h) (M + N + h : ℤ), ‖extSum k‖ ^ 2 := by
        refine Finset.sum_bij (fun n _ => n + (h : ℤ)) ?_ ?_ ?_ ?_
        · intro n hn; simp only [BigI, Finset.mem_Ioc] at hn ⊢; omega
        · intro n₁ _ n₂ _ heq; omega
        · intro k hk; simp only [Finset.mem_Ioc] at hk; refine ⟨k - (h : ℤ), Finset.mem_Ioc.mpr (by omega), by omega⟩
        · intro n _; rfl
      rw [hreidx]
      have hsub : Finset.Ioc (M : ℤ) (M + N : ℤ) ⊆
          Finset.Ioc ((M : ℤ) - H + 1 + h) (M + N + h : ℤ) := by
        intro k hk; simp only [Finset.mem_Ioc] at hk ⊢; omega
      have hEq : ∑ k ∈ Finset.Ioc ((M : ℤ) - H + 1 + h) (M + N + h : ℤ), ‖extSum k‖ ^ 2 =
          ∑ k ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), ‖extSum k‖ ^ 2 := by
        symm
        refine Finset.sum_subset hsub fun k hk hnot => ?_
        simp only [Finset.mem_Ioc] at hk hnot
        have : ¬ ((M : ℤ) < k ∧ k ≤ (M + N : ℤ)) := by omega
        simp [extSum, this]
      rw [hEq]
      exact le_of_eq (calc
        ∑ k ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), ‖extSum k‖ ^ 2
          = ∑ _k ∈ Finset.Ioc (M : ℤ) (M + N : ℤ), (1 : ℝ) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            simp only [Finset.mem_Ioc] at hk
            simp [extSum, hk, norm_vdcE]
        _ = (N : ℝ) := by
            have hcard : (Finset.Ioc (M : ℤ) (M + N : ℤ)).card = N := by
              rw [Int.card_Ioc]; omega
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard])
    calc ∑ h ∈ Finset.range H, ∑ n ∈ BigI, ‖extSum (n + (h : ℤ))‖ ^ 2
        ≤ ∑ _h ∈ Finset.range H, (N : ℝ) := Finset.sum_le_sum hinner
      _ = (H : ℝ) * (N : ℝ) := by simp
  have hH_pos : (0 : ℝ) < H := by positivity
  have hmain_sq :
      (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ioc M (M + N), vdcE (f (n : ℝ))‖ ^ 2 ≤
        ((N : ℝ) + H) * ((H : ℝ) * ((N : ℝ) + H) +
          2 * (H : ℝ) * ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
            ‖∑ n ∈ Finset.Ioc M (M + N - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖) := by
    rw [hS_eq]
    refine hcs.trans ?_
    refine mul_le_mul hBigI_card ?_ (by positivity) (by positivity)
    rw [hexp_sum]
    have hre_le :
        ∑ r ∈ Finset.Ico 1 H, ((H : ℝ) - r) *
            (∑ n ∈ Finset.Ioc M (M + N - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))).re ≤
          (H : ℝ) * ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
            ‖∑ n ∈ Finset.Ioc M (M + N - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      simp only [Finset.mem_Ico] at hr
      have hfac : (H : ℝ) * (1 - (r : ℝ) / H) = (H : ℝ) - r := by
        field_simp [hH_pos.ne']
      rw [← mul_assoc, hfac]
      exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by
        have : (r : ℝ) ≤ H := by exact_mod_cast hr.2.le
        linarith)
    have hN_le : (H : ℝ) * (N : ℝ) ≤ (H : ℝ) * ((N : ℝ) + H) := by gcongr; linarith
    linarith [hdiag_bd, hre_le, hN_le]
  have hdiv := (div_le_div_iff_of_pos_right hH_pos).mpr hmain_sq
  have h1 : ((H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ioc M (M + N), vdcE (f (n : ℝ))‖ ^ 2) / (H : ℝ) =
      (H : ℝ) * ‖∑ n ∈ Finset.Ioc M (M + N), vdcE (f (n : ℝ))‖ ^ 2 := by
    field_simp [hH_pos.ne']
  have h2 : (((N : ℝ) + H) * ((H : ℝ) * ((N : ℝ) + H) +
        2 * (H : ℝ) * ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
          ‖∑ n ∈ Finset.Ioc M (M + N - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖)) / (H : ℝ) =
      ((N : ℝ) + H) * (((N : ℝ) + H) +
        2 * ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
          ‖∑ n ∈ Finset.Ioc M (M + N - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖) := by
    field_simp [hH_pos.ne']
  change (H : ℝ) * ‖∑ n ∈ Finset.Ioc M (M + N), vdcE (f (n : ℝ))‖ ^ 2 ≤ _
  linarith [hdiv, h1, h2]

private lemma vanDerCorput_A_process_step_algebra
    {C₁ k l lam₁ a H S : ℝ}
    (hC₁ : 1 ≤ C₁) (hk0 : 0 ≤ k) (hlam_pos : 0 < lam₁) (ha_pos : 0 < a) (hH_pos : 0 < H)
    (hS_nn : 0 ≤ S)
    (hH_ge_half : a ^ ((k + 1 - l) / (k + 1)) * lam₁ ^ (-k / (k + 1)) / 2 ≤ H)
    (hH_le_Hreal : H ≤ a ^ ((k + 1 - l) / (k + 1)) * lam₁ ^ (-k / (k + 1)))
    (hsq_S : S ^ 2 ≤ 4 * a ^ 2 / H + 4 * C₁ * a * (H * lam₁ / a) ^ k * a ^ l) :
    S ≤ 4 * Real.sqrt C₁ * (lam₁ ^ (k / (2 * k + 2)) * a ^ ((k + l + 1) / (2 * k + 2)) +
      a ^ (1 / 2 : ℝ)) := by
  let Hreal : ℝ := a ^ ((k + 1 - l) / (k + 1)) * lam₁ ^ (-k / (k + 1))
  have hHreal_pos : 0 < Hreal :=
    mul_pos (Real.rpow_pos_of_pos ha_pos _) (Real.rpow_pos_of_pos hlam_pos _)
  have hk1_ne : k + 1 ≠ 0 := by linarith only [hk0]
  have hmon1 : a ^ 2 / Hreal = lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1)) := by
    dsimp only [Hreal]
    rw [div_eq_mul_inv, mul_inv, ← Real.rpow_neg ha_pos.le, ← Real.rpow_neg hlam_pos.le]
    calc a ^ 2 * (a ^ (-((k + 1 - l) / (k + 1))) * lam₁ ^ (-(-k / (k + 1))))
        = lam₁ ^ (k / (k + 1)) * (a ^ (2 : ℝ) * a ^ (-((k + 1 - l) / (k + 1)))) := by
          rw [← Real.rpow_natCast a 2]
          have hnegk : -(-k / (k + 1)) = k / (k + 1) := by ring
          rw [hnegk]
          ring
      _ = lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1)) := by
          rw [← Real.rpow_add ha_pos]
          congr 2
          field_simp [hk1_ne]
          ring
  have hmon2 : a * (Hreal * lam₁ / a) ^ k * a ^ l =
      lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1)) := by
    have hratio : Hreal * lam₁ / a =
        a ^ (-l / (k + 1)) * lam₁ ^ (1 / (k + 1)) := by
      dsimp only [Hreal]
      have hexp_a : (k + 1 - l) / (k + 1) + (-1 : ℝ) = -l / (k + 1) := by
        field_simp [hk1_ne]; ring
      have hexp_lam : -k / (k + 1) + (1 : ℝ) = 1 / (k + 1) := by
        field_simp [hk1_ne]; ring
      calc (a ^ ((k + 1 - l) / (k + 1)) * lam₁ ^ (-k / (k + 1))) * lam₁ / a
          = (a ^ ((k + 1 - l) / (k + 1)) * a ^ (-1 : ℝ)) *
              (lam₁ ^ (-k / (k + 1)) * lam₁ ^ (1 : ℝ)) := by
            rw [Real.rpow_neg_one, Real.rpow_one, div_eq_mul_inv]; ring
        _ = a ^ (-l / (k + 1)) * lam₁ ^ (1 / (k + 1)) := by
            rw [← Real.rpow_add ha_pos, hexp_a, ← Real.rpow_add hlam_pos, hexp_lam]
    rw [hratio, Real.mul_rpow (Real.rpow_nonneg ha_pos.le _) (Real.rpow_nonneg hlam_pos.le _),
      ← Real.rpow_mul ha_pos.le, ← Real.rpow_mul hlam_pos.le]
    have hexp_tot : (1 : ℝ) + (-l / (k + 1) * k) + l = (k + l + 1) / (k + 1) := by
      field_simp [hk1_ne]; ring
    calc a * (a ^ (-l / (k + 1) * k) * lam₁ ^ (1 / (k + 1) * k)) * a ^ l
        = lam₁ ^ (k / (k + 1)) * (a ^ (1 : ℝ) * a ^ (-l / (k + 1) * k) * a ^ l) := by
          rw [Real.rpow_one, show (1 / (k + 1) * k : ℝ) = k / (k + 1) by ring]; ring
      _ = lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1)) := by
          rw [← Real.rpow_add ha_pos, ← Real.rpow_add ha_pos, hexp_tot]
  have hterm1 : 4 * a ^ 2 / H ≤ 8 * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) := by
    have hdiv : a ^ 2 / H ≤ 2 * (a ^ 2 / Hreal) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hH_pos hHreal_pos]
      calc a ^ 2 * Hreal = a ^ 2 * (2 * (Hreal / 2)) := by ring
        _ ≤ a ^ 2 * (2 * H) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH_ge_half zero_le_two) (sq_nonneg _)
        _ = 2 * a ^ 2 * H := by ring
    rw [hmon1] at hdiv
    have h4 : 4 * (a ^ 2 / H) = 4 * a ^ 2 / H := by ring
    linarith only [hdiv, h4]
  have hterm2 : 4 * C₁ * a * (H * lam₁ / a) ^ k * a ^ l ≤
      4 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) := by
    have hH_rpow : (H * lam₁ / a) ^ k ≤ (Hreal * lam₁ / a) ^ k := by
      refine Real.rpow_le_rpow (div_nonneg (mul_nonneg hH_pos.le hlam_pos.le) ha_pos.le) ?_ hk0
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hH_le_Hreal hlam_pos.le) ha_pos.le
    have hc4_nn : 0 ≤ 4 * C₁ * a := mul_nonneg (mul_nonneg zero_le_four (by linarith only [hC₁])) ha_pos.le
    calc 4 * C₁ * a * (H * lam₁ / a) ^ k * a ^ l
        ≤ 4 * C₁ * a * (Hreal * lam₁ / a) ^ k * a ^ l := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH_rpow hc4_nn)
            (Real.rpow_nonneg ha_pos.le _)
      _ = 4 * C₁ * (a * (Hreal * lam₁ / a) ^ k * a ^ l) := by ring
      _ = 4 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) := by rw [hmon2]
  have hS_sq : S ^ 2 ≤ 16 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) := by
    have hposM : 0 ≤ lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1)) :=
      mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.rpow_nonneg ha_pos.le _)
    have hcomb : (8 + 4 * C₁) * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) ≤
        16 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC₁]) hposM
    calc S ^ 2
        ≤ 4 * a ^ 2 / H + 4 * C₁ * a * (H * lam₁ / a) ^ k * a ^ l := hsq_S
      _ ≤ 8 * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) +
            4 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) :=
          add_le_add hterm1 hterm2
      _ = (8 + 4 * C₁) * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) := by ring
      _ ≤ 16 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) := hcomb
  have hroot := Real.sqrt_le_sqrt hS_sq
  have h16C : 0 ≤ 16 * C₁ := by linarith only [hC₁]
  have hlamk_nn : 0 ≤ lam₁ ^ (k / (k + 1)) := Real.rpow_nonneg hlam_pos.le _
  have hexp1 : k / (k + 1) * (1 / 2) = k / (2 * k + 2) := by
    rw [div_mul_div_comm, mul_one, show (k + 1) * 2 = 2 * k + 2 by ring]
  have hexp2 : (k + l + 1) / (k + 1) * (1 / 2) = (k + l + 1) / (2 * k + 2) := by
    rw [div_mul_div_comm, mul_one, show (k + 1) * 2 = 2 * k + 2 by ring]
  have hrhs_eq :
      Real.sqrt (16 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1)))) =
        4 * Real.sqrt C₁ * (lam₁ ^ (k / (2 * k + 2)) * a ^ ((k + l + 1) / (2 * k + 2))) := by
    calc Real.sqrt (16 * C₁ * (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))))
        = Real.sqrt (16 * C₁) *
            Real.sqrt (lam₁ ^ (k / (k + 1)) * a ^ ((k + l + 1) / (k + 1))) :=
          Real.sqrt_mul h16C _
      _ = (Real.sqrt 16 * Real.sqrt C₁) *
            (Real.sqrt (lam₁ ^ (k / (k + 1))) * Real.sqrt (a ^ ((k + l + 1) / (k + 1)))) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16) C₁, Real.sqrt_mul hlamk_nn _]
      _ = (4 * Real.sqrt C₁) *
            ((lam₁ ^ (k / (k + 1))) ^ (1 / 2 : ℝ) * (a ^ ((k + l + 1) / (k + 1))) ^ (1 / 2 : ℝ)) := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq zero_le_four,
            Real.sqrt_eq_rpow (lam₁ ^ (k / (k + 1))),
            Real.sqrt_eq_rpow (a ^ ((k + l + 1) / (k + 1)))]
      _ = 4 * Real.sqrt C₁ * (lam₁ ^ (k / (2 * k + 2)) * a ^ ((k + l + 1) / (2 * k + 2))) := by
          rw [← Real.rpow_mul hlam_pos.le, ← Real.rpow_mul ha_pos.le, hexp1, hexp2]
  have hS_le :
      S ≤ 4 * Real.sqrt C₁ * (lam₁ ^ (k / (2 * k + 2)) * a ^ ((k + l + 1) / (2 * k + 2))) := by
    have hsq_norm : Real.sqrt (S ^ 2) = S := Real.sqrt_sq hS_nn
    exact hsq_norm ▸ hroot.trans_eq hrhs_eq
  exact hS_le.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg ha_pos.le _))
    (mul_nonneg zero_le_four (Real.sqrt_nonneg C₁)))

/-- Analytic **Weyl–van der Corput A-process step**: if `(k, l)` (`0 ≤ k ≤ 1/2 ≤ l ≤ 1`) bounds
the differenced sums `∑_{n ∈ Ioc a (a + d - r)} e(f(n + r) - f(n))` by `C₁ * (r * λ₁ / a)^k * a^l`
for `1 ≤ r < H`, and `‖S‖ ≤ d ≤ a`, then optimizing `H` yields the `(k/(2k+2), (k+l+1)/(2k+2))`
exponent pair estimate. -/
theorem vanDerCorput_A_process_step {f : ℝ → ℝ} {a d : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d) (hda : d ≤ a)
    {lam₁ C₁ k l : ℝ} (hlam : 1 / 2 < lam₁) (hC₁ : 1 ≤ C₁)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 2) (hl0 : 1 / 2 ≤ l) (_hl1 : l ≤ 1)
    (hdiff : ∀ r : ℕ, 1 ≤ r →
      ‖∑ n ∈ Finset.Ioc a (a + d - r),
        Complex.exp (2 * Real.pi * ((f ((n + r : ℕ) : ℝ) - f (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        C₁ * ((r : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l) :
    ‖∑ n ∈ Finset.Ioc a (a + d), Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      4 * Real.sqrt C₁ * (lam₁ ^ (k / (2 * k + 2)) * (a : ℝ) ^ ((k + l + 1) / (2 * k + 2)) +
        (a : ℝ) ^ (1 / 2 : ℝ)) := by
  let Snorm := ‖∑ n ∈ Finset.Ioc a (a + d), vdcE (f (n : ℝ))‖
  have ha_pos : (0 : ℝ) < a := by positivity
  have hd_pos : (0 : ℝ) < d := by positivity
  have hda_R : (d : ℝ) ≤ a := by exact_mod_cast hda
  have hlam_pos : 0 < lam₁ := by linarith
  let Hreal : ℝ := (a : ℝ) ^ ((k + 1 - l) / (k + 1)) * lam₁ ^ (-k / (k + 1))
  have hHreal_pos : 0 < Hreal := by positivity
  have htriv : Snorm ≤ (a : ℝ) := by
    calc Snorm ≤ (d : ℝ) := by
          dsimp only [Snorm]
          refine (norm_sum_le _ _).trans_eq ?_
          simp [norm_vdcE, Nat.card_Ioc]
      _ ≤ a := hda_R
  have hC_ge : 1 ≤ Real.sqrt C₁ := by simpa using Real.sqrt_le_sqrt hC₁
  have hM_nonneg : 0 ≤ lam₁ ^ (k / (2 * k + 2)) * (a : ℝ) ^ ((k + l + 1) / (2 * k + 2)) := by
    positivity
  have ha_half_nonneg : 0 ≤ (a : ℝ) ^ (1 / 2 : ℝ) := by positivity
  by_cases hH_lt1 : Hreal < 1
  · have ha_sq : (a : ℝ) ^ 2 ≤ lam₁ ^ (k / (k + 1)) * (a : ℝ) ^ ((k + l + 1) / (k + 1)) := by
      have h1 : (1 : ℝ) < lam₁ ^ (k / (k + 1)) * (a : ℝ) ^ ((l - k - 1) / (k + 1)) := by
        have hinv : Hreal⁻¹ = (a : ℝ) ^ ((l - k - 1) / (k + 1)) * lam₁ ^ (k / (k + 1)) := by
          dsimp only [Hreal]
          rw [mul_inv, ← Real.rpow_neg ha_pos.le, ← Real.rpow_neg hlam_pos.le]
          congr 1 <;> congr 1 <;> ring
        rw [mul_comm, ← hinv]
        exact one_lt_inv_iff₀.mpr ⟨hHreal_pos, hH_lt1⟩
      have ha2_pos : 0 < (a : ℝ) ^ 2 := by positivity
      calc (a : ℝ) ^ 2 = (a : ℝ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (a : ℝ) ^ 2 * (lam₁ ^ (k / (k + 1)) * (a : ℝ) ^ ((l - k - 1) / (k + 1))) :=
            mul_le_mul_of_nonneg_left h1.le ha2_pos.le
        _ = lam₁ ^ (k / (k + 1)) * ((a : ℝ) ^ (2 : ℝ) * (a : ℝ) ^ ((l - k - 1) / (k + 1))) := by
            rw [← Real.rpow_natCast (a : ℝ) 2]; ring
        _ = lam₁ ^ (k / (k + 1)) * (a : ℝ) ^ ((k + l + 1) / (k + 1)) := by
            rw [← Real.rpow_add ha_pos]
            congr 2
            field_simp [show (k + 1 : ℝ) ≠ 0 by positivity]
            ring
    have ha_root := Real.sqrt_le_sqrt ha_sq
    rw [Real.sqrt_sq ha_pos.le, Real.sqrt_mul (by positivity),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hlam_pos.le, ← Real.rpow_mul ha_pos.le] at ha_root
    have hk1_ne0 : k + 1 ≠ 0 := by positivity
    have hexp1 : k / (k + 1) * (1 / 2) = k / (2 * k + 2) := by field_simp [hk1_ne0]
    have hexp2 : (k + l + 1) / (k + 1) * (1 / 2) = (k + l + 1) / (2 * k + 2) := by
      field_simp [hk1_ne0]
    rw [hexp1, hexp2] at ha_root
    calc Snorm ≤ (a : ℝ) := htriv
      _ ≤ lam₁ ^ (k / (2 * k + 2)) * (a : ℝ) ^ ((k + l + 1) / (2 * k + 2)) := ha_root
      _ ≤ 4 * Real.sqrt C₁ * (lam₁ ^ (k / (2 * k + 2)) * (a : ℝ) ^ ((k + l + 1) / (2 * k + 2)) +
            (a : ℝ) ^ (1 / 2 : ℝ)) := by nlinarith
  have hHreal_ge1 : 1 ≤ Hreal := not_lt.mp hH_lt1
  let H : ℕ := ⌊Hreal⌋₊
  have hH1 : 1 ≤ H := Nat.floor_pos.mpr hHreal_ge1
  have hH_pos : (0 : ℝ) < H := by positivity
  have hH_le_Hreal : (H : ℝ) ≤ Hreal := Nat.floor_le hHreal_pos.le
  have hH_ge_half : Hreal / 2 ≤ (H : ℝ) := by
    have hlt : Hreal < (H : ℝ) + 1 := Nat.lt_floor_add_one Hreal
    have h1 : (1 : ℝ) ≤ H := by exact_mod_cast hH1
    linarith
  by_cases hH_gt : (a : ℝ) < (H : ℝ)
  · have ha_lt_H : (a : ℝ) < Hreal := hH_gt.trans_le hH_le_Hreal
    have ha_pow : (a : ℝ) ^ ((k + 1 - l) / (k + 1)) ≤ (a : ℝ) := by
      conv_rhs => rw [← Real.rpow_one (a : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ha) (by
        rw [div_le_one (by positivity)]; linarith)
    have hlam_pow : lam₁ ^ (-k / (k + 1)) ≤ 2 := by
      have : lam₁ ^ (-k / (k + 1)) = (lam₁⁻¹) ^ (k / (k + 1)) := by
        rw [Real.inv_rpow hlam_pos.le, ← Real.rpow_neg hlam_pos.le]
        congr 1; ring
      rw [this]
      have hinv2 : lam₁⁻¹ ≤ 2 := by rw [inv_le_comm₀ hlam_pos two_pos]; linarith
      calc (lam₁⁻¹) ^ (k / (k + 1)) ≤ (2 : ℝ) ^ (k / (k + 1)) :=
            Real.rpow_le_rpow (by positivity) hinv2 (by positivity)
        _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by
            rw [div_le_one (by positivity)]; linarith)
        _ = 2 := Real.rpow_one 2
    have ha_l_lt2 : (a : ℝ) ^ (l / (k + 1)) < 2 := by
      have hH_ub : Hreal ≤ (a : ℝ) ^ ((k + 1 - l) / (k + 1)) * 2 :=
        mul_le_mul_of_nonneg_left hlam_pow (by positivity)
      have ha_mul : (a : ℝ) ^ ((k + 1 - l) / (k + 1)) * (a : ℝ) ^ (l / (k + 1)) = (a : ℝ) := by
        rw [← Real.rpow_add ha_pos]
        have hexp : (k + 1 - l) / (k + 1) + l / (k + 1) = 1 := by
          field_simp [show (k + 1 : ℝ) ≠ 0 by positivity]; ring
        rw [hexp, Real.rpow_one]
      have ha_lt_mul : (a : ℝ) ^ ((k + 1 - l) / (k + 1)) * (a : ℝ) ^ (l / (k + 1)) <
          (a : ℝ) ^ ((k + 1 - l) / (k + 1)) * 2 := by
        rw [ha_mul]
        exact ha_lt_H.trans_le hH_ub
      exact lt_of_mul_lt_mul_left ha_lt_mul (by positivity)
    have hthird_le : (1 / 3 : ℝ) ≤ l / (k + 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    have ha_third_lt2 : (a : ℝ) ^ (1 / 3 : ℝ) < 2 :=
      lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ha) hthird_le) ha_l_lt2
    have ha_lt8 : (a : ℝ) < 8 := by
      have hpow : ((a : ℝ) ^ (1 / 3 : ℝ)) ^ 3 < 2 ^ 3 :=
        pow_lt_pow_left₀ ha_third_lt2 (by positivity) (by norm_num)
      have hcube : ((a : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (a : ℝ) := by
        rw [← Real.rpow_natCast ((a : ℝ) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul ha_pos.le]
        norm_num
      linarith
    have ha_lt9 : (a : ℝ) < 3 ^ 2 := by linarith
    have ha_sqrt_lt3 : (a : ℝ) ^ (1 / 2 : ℝ) < 3 := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.sqrt_lt' (by norm_num)).mpr ha_lt9
    have ha_eq_sq : (a : ℝ) = (a : ℝ) ^ (1 / 2 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add ha_pos]; norm_num
    have ha_le_3sqrt : (a : ℝ) ≤ 3 * (a : ℝ) ^ (1 / 2 : ℝ) := by
      calc (a : ℝ) = (a : ℝ) ^ (1 / 2 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) := ha_eq_sq
        _ ≤ 3 * (a : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right ha_sqrt_lt3.le ha_half_nonneg
    calc Snorm ≤ (a : ℝ) := htriv
      _ ≤ 3 * (a : ℝ) ^ (1 / 2 : ℝ) := ha_le_3sqrt
      _ ≤ 4 * Real.sqrt C₁ * (lam₁ ^ (k / (2 * k + 2)) * (a : ℝ) ^ ((k + l + 1) / (2 * k + 2)) +
            (a : ℝ) ^ (1 / 2 : ℝ)) := by nlinarith
  · have hH_le_a : (H : ℝ) ≤ (a : ℝ) := not_lt.mp hH_gt
    have hvd := vanDerCorput_weyl_differencing f a d H hH1
    have hsum_diff :
        ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
            ‖∑ n ∈ Finset.Ioc a (a + d - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖ ≤
          (H : ℝ) * (C₁ * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l) := by
      calc ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
              ‖∑ n ∈ Finset.Ioc a (a + d - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖
          ≤ ∑ r ∈ Finset.Ico 1 H, 1 * (C₁ * ((r : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l) := by
            refine Finset.sum_le_sum fun r hr => ?_
            simp only [Finset.mem_Ico] at hr
            have h1 : 1 - (r : ℝ) / H ≤ 1 := by
              have : 0 ≤ (r : ℝ) / H := by positivity
              linarith
            have h2 : 0 ≤ 1 - (r : ℝ) / H := by
              have : (r : ℝ) / H ≤ 1 := (div_le_one hH_pos).mpr (by exact_mod_cast hr.2.le)
              linarith
            exact mul_le_mul h1 (hdiff r hr.1) (norm_nonneg _) zero_le_one
        _ ≤ ∑ _r ∈ Finset.Ico 1 H, (C₁ * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l) := by
            refine Finset.sum_le_sum fun r hr => ?_
            simp only [Finset.mem_Ico] at hr
            rw [one_mul]
            gcongr
            exact_mod_cast hr.2.le
        _ ≤ (H : ℝ) * (C₁ * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l) := by
            simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
            gcongr
            exact_mod_cast Nat.sub_le H 1
    have hdH : (d : ℝ) + (H : ℝ) ≤ 2 * (a : ℝ) := by linarith
    have hsq_S : Snorm ^ 2 ≤
        4 * (a : ℝ) ^ 2 / H + 4 * C₁ * (a : ℝ) * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l := by
      have hmul : (H : ℝ) * Snorm ^ 2 ≤
          (2 * (a : ℝ)) * (2 * (a : ℝ) + 2 * (H : ℝ) * (C₁ * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l)) := by
        calc (H : ℝ) * Snorm ^ 2
            ≤ ((d : ℝ) + H) * (((d : ℝ) + H) +
                2 * ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
                  ‖∑ n ∈ Finset.Ioc a (a + d - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖) := hvd
          _ ≤ (2 * (a : ℝ)) * (2 * (a : ℝ) +
                2 * ((H : ℝ) * (C₁ * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l))) := by
              have hnonneg : 0 ≤ (d : ℝ) + (H : ℝ) +
                  2 * ∑ r ∈ Finset.Ico 1 H, (1 - (r : ℝ) / H) *
                    ‖∑ n ∈ Finset.Ioc a (a + d - r), vdcE (f ((n + r : ℕ) : ℝ) - f (n : ℝ))‖ := by
                refine add_nonneg (by positivity) (mul_nonneg zero_le_two (Finset.sum_nonneg fun r hr => ?_))
                simp only [Finset.mem_Ico] at hr
                have hle1 : (r : ℝ) / H ≤ 1 := (div_le_one hH_pos).mpr (by exact_mod_cast hr.2.le)
                exact mul_nonneg (by linarith) (norm_nonneg _)
              exact mul_le_mul hdH (add_le_add hdH (mul_le_mul_of_nonneg_left hsum_diff zero_le_two))
                hnonneg (by positivity)
          _ = (2 * (a : ℝ)) * (2 * (a : ℝ) +
                2 * (H : ℝ) * (C₁ * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l)) := by ring
      have hdiv := (div_le_div_iff_of_pos_right hH_pos).mpr hmul
      have h1 : ((H : ℝ) * Snorm ^ 2) / H = Snorm ^ 2 := by field_simp [hH_pos.ne']
      have h2 : ((2 * (a : ℝ)) * (2 * (a : ℝ) +
            2 * (H : ℝ) * (C₁ * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l))) / H =
          4 * (a : ℝ) ^ 2 / H + 4 * C₁ * (a : ℝ) * ((H : ℝ) * lam₁ / (a : ℝ)) ^ k * (a : ℝ) ^ l := by
        field_simp [hH_pos.ne']
        ring
      linarith
    exact vanDerCorput_A_process_step_algebra hC₁ hk0 hlam_pos ha_pos hH_pos (norm_nonneg _)
      hH_ge_half hH_le_Hreal hsq_S

end ProcessAAndProcessB

section ProcessBPoissonAndStationaryPhase

private def clamp01 (u : ℝ) : ℝ := max 0 (min 1 u)

private lemma clamp01_of_nonpos {u : ℝ} (hu : u ≤ 0) : clamp01 u = 0 := by
  simp only [clamp01, min_eq_right (hu.trans zero_le_one), max_eq_left hu]

private lemma clamp01_of_ge_one {u : ℝ} (hu : 1 ≤ u) : clamp01 u = 1 := by
  simp only [clamp01, min_eq_left hu, max_eq_right zero_le_one]

private lemma clamp01_mem_Icc {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : clamp01 u = u := by
  simp only [clamp01, min_eq_right hu.2, max_eq_right hu.1]

private lemma clamp01_bounds (u : ℝ) : 0 ≤ clamp01 u ∧ clamp01 u ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private def quinticStep (u : ℝ) : ℝ :=
  10 * clamp01 u ^ 3 - 15 * clamp01 u ^ 4 + 6 * clamp01 u ^ 5

private def quinticStepDeriv (u : ℝ) : ℝ :=
  30 * clamp01 u ^ 2 * (1 - clamp01 u) ^ 2

private def quinticStepDeriv2 (u : ℝ) : ℝ :=
  60 * clamp01 u * (1 - clamp01 u) * (1 - 2 * clamp01 u)

private lemma continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01
  fun_prop

private lemma continuous_quinticStep : Continuous quinticStep := by
  unfold quinticStep
  have := continuous_clamp01
  fun_prop

private lemma continuous_quinticStepDeriv : Continuous quinticStepDeriv := by
  unfold quinticStepDeriv
  have := continuous_clamp01
  fun_prop

private lemma continuous_quinticStepDeriv2 : Continuous quinticStepDeriv2 := by
  unfold quinticStepDeriv2
  have := continuous_clamp01
  fun_prop

private lemma quinticStep_of_nonpos {u : ℝ} (hu : u ≤ 0) : quinticStep u = 0 := by
  simp [quinticStep, clamp01_of_nonpos hu]

private lemma quinticStep_of_ge_one {u : ℝ} (hu : 1 ≤ u) : quinticStep u = 1 := by
  simp [quinticStep, clamp01_of_ge_one hu]; norm_num

private lemma quinticStepDeriv_of_nonpos {u : ℝ} (hu : u ≤ 0) : quinticStepDeriv u = 0 := by
  simp [quinticStepDeriv, clamp01_of_nonpos hu]

private lemma quinticStepDeriv_of_ge_one {u : ℝ} (hu : 1 ≤ u) : quinticStepDeriv u = 0 := by
  simp [quinticStepDeriv, clamp01_of_ge_one hu]

private lemma quinticStep_bounds (u : ℝ) :
    0 ≤ quinticStep u ∧ quinticStep u ≤ 1 ∧ 0 ≤ quinticStepDeriv u ∧
      quinticStepDeriv u ≤ 2 ∧ |quinticStepDeriv2 u| ≤ 16 := by
  obtain ⟨h0, h1⟩ := clamp01_bounds u
  set c := clamp01 u
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hpos : 0 ≤ c ^ 3 * (6 * (c - 1) ^ 2 + 3 * (1 - c) + 1) := by
      have : 0 ≤ 6 * (c - 1) ^ 2 + 3 * (1 - c) + 1 := by positivity
      exact mul_nonneg (pow_nonneg h0 3) this
    have heq : quinticStep u = c ^ 3 * (6 * (c - 1) ^ 2 + 3 * (1 - c) + 1) := by
      dsimp only [quinticStep, c]; ring
    linarith
  · have hnonneg : 0 ≤ (1 - c) ^ 3 * (1 + 3 * c + 6 * c ^ 2) := by
      have : 0 ≤ 1 + 3 * c + 6 * c ^ 2 := by positivity
      exact mul_nonneg (pow_nonneg (by linarith) 3) this
    have heq : 1 - quinticStep u = (1 - c) ^ 3 * (1 + 3 * c + 6 * c ^ 2) := by
      dsimp only [quinticStep, c]; ring
    linarith
  · unfold quinticStepDeriv; positivity
  · have hcc : c * (1 - c) ≤ 1 / 4 := by nlinarith [sq_nonneg (c - 1 / 2)]
    have hnonneg : 0 ≤ c * (1 - c) := mul_nonneg h0 (by linarith)
    have hsq : (c * (1 - c)) ^ 2 ≤ (1 / 4) ^ 2 := by nlinarith
    have heq : quinticStepDeriv u = 30 * (c * (1 - c)) ^ 2 := by
      dsimp only [quinticStepDeriv, c]; ring
    linarith
  · have hcc : c * (1 - c) ≤ 1 / 4 := by nlinarith [sq_nonneg (c - 1 / 2)]
    have hnonneg : 0 ≤ c * (1 - c) := mul_nonneg h0 (by linarith)
    have hlin : |1 - 2 * c| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [show quinticStepDeriv2 u = 60 * (c * (1 - c)) * (1 - 2 * c) by
      dsimp only [quinticStepDeriv2, c]; ring, abs_mul, abs_mul]
    have h60 : |(60 : ℝ)| = 60 := by norm_num
    have hcc_abs : |c * (1 - c)| = c * (1 - c) := abs_of_nonneg hnonneg
    rw [h60, hcc_abs]
    calc 60 * (c * (1 - c)) * |1 - 2 * c| ≤ 60 * (1 / 4) * 1 := by gcongr
      _ ≤ 16 := by norm_num

private lemma hasDerivAt_quinticStep (u : ℝ) :
    HasDerivAt quinticStep (quinticStepDeriv u) u := by
  let poly : ℝ → ℝ := fun x => 10 * x ^ 3 - 15 * x ^ 4 + 6 * x ^ 5
  have hpoly : ∀ x : ℝ, HasDerivAt poly (30 * x ^ 2 * (1 - x) ^ 2) x := fun x => by
    have h1 := ((hasDerivAt_pow 3 x).const_mul 10).sub ((hasDerivAt_pow 4 x).const_mul 15)
    have h2 := h1.add ((hasDerivAt_pow 5 x).const_mul 6)
    convert h2 using 1
    ring
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · have hev : quinticStep =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hu0) fun x hx => quinticStep_of_nonpos hx.le
    rw [quinticStepDeriv_of_nonpos hu0.le]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
  · have hleft : HasDerivWithinAt quinticStep 0 (Set.Iic 0) 0 := by
      have hev : quinticStep =ᶠ[𝓝[Set.Iic 0] 0] fun _ => (0 : ℝ) :=
        eventually_nhdsWithin_of_forall fun x hx => quinticStep_of_nonpos hx
      exact (hasDerivWithinAt_const 0 _ 0).congr_of_eventuallyEq hev (quinticStep_of_nonpos le_rfl)
    have hright : HasDerivWithinAt quinticStep 0 (Set.Ici 0) 0 := by
      have hIcc : Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := Icc_mem_nhdsGE zero_lt_one
      have hev : quinticStep =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] poly :=
        Filter.eventually_of_mem hIcc fun x hx => by simp [quinticStep, poly, clamp01_mem_Icc hx]
      have hd : HasDerivWithinAt poly 0 (Set.Ici 0) 0 := by
        simpa using (hpoly 0).hasDerivWithinAt
      exact hd.congr_of_eventuallyEq hev (by simp [quinticStep, poly, clamp01_of_nonpos le_rfl])
    rw [quinticStepDeriv_of_nonpos le_rfl, ← hasDerivWithinAt_univ, ← Set.Iic_union_Ici]
    exact hleft.union hright
  · rcases lt_trichotomy u 1 with hu1 | rfl | hu1
    · have hev : quinticStep =ᶠ[𝓝 u] poly :=
        Filter.eventually_of_mem (Ioo_mem_nhds hu0 hu1) fun x hx => by
          simp [quinticStep, poly, clamp01_mem_Icc (Set.Ioo_subset_Icc_self hx)]
      have heq_d : quinticStepDeriv u = 30 * u ^ 2 * (1 - u) ^ 2 := by
        simp [quinticStepDeriv, clamp01_mem_Icc ⟨hu0.le, hu1.le⟩]
      rw [heq_d]
      exact (hpoly u).congr_of_eventuallyEq hev
    · have hleft : HasDerivWithinAt quinticStep 0 (Set.Iic 1) 1 := by
        have hIcc : Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Iic (1 : ℝ)] 1 := Icc_mem_nhdsLE zero_lt_one
        have hev : quinticStep =ᶠ[𝓝[Set.Iic (1 : ℝ)] 1] poly :=
          Filter.eventually_of_mem hIcc fun x hx => by simp [quinticStep, poly, clamp01_mem_Icc hx]
        have hd : HasDerivWithinAt poly 0 (Set.Iic 1) 1 := by
          simpa using (hpoly 1).hasDerivWithinAt
        exact hd.congr_of_eventuallyEq hev (by simp [quinticStep, poly, clamp01_of_ge_one le_rfl])
      have hright : HasDerivWithinAt quinticStep 0 (Set.Ici 1) 1 := by
        have hev : quinticStep =ᶠ[𝓝[Set.Ici 1] 1] fun _ => (1 : ℝ) :=
          eventually_nhdsWithin_of_forall fun x hx => quinticStep_of_ge_one hx
        exact (hasDerivWithinAt_const 1 _ 1).congr_of_eventuallyEq hev (quinticStep_of_ge_one le_rfl)
      rw [quinticStepDeriv_of_ge_one le_rfl, ← hasDerivWithinAt_univ, ← Set.Iic_union_Ici (a := (1 : ℝ))]
      exact hleft.union hright
    · have hev : quinticStep =ᶠ[𝓝 u] fun _ => (1 : ℝ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hu1) fun x hx => quinticStep_of_ge_one hx.le
      rw [quinticStepDeriv_of_ge_one hu1.le]
      exact (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq hev

private lemma hasDerivAt_quinticStepDeriv (u : ℝ) :
    HasDerivAt quinticStepDeriv (quinticStepDeriv2 u) u := by
  let poly' : ℝ → ℝ := fun x => 30 * x ^ 2 * (1 - x) ^ 2
  have hpoly' : ∀ x : ℝ, HasDerivAt poly' (60 * x * (1 - x) * (1 - 2 * x)) x := fun x => by
    have h1 : HasDerivAt (fun y : ℝ => 30 * y ^ 2) (30 * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul 30
    have hb : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1
      · ext y; rfl
      · norm_num
    have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ 2) (2 * (1 - x) * (-1)) x :=
      (hb.pow 2).congr_deriv (by simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one])
    exact (h1.mul h2).congr_deriv (by ring)
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · have hev : quinticStepDeriv =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hu0) fun x hx => quinticStepDeriv_of_nonpos hx.le
    have h0 : quinticStepDeriv2 u = 0 := by simp [quinticStepDeriv2, clamp01_of_nonpos hu0.le]
    rw [h0]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
  · have hleft : HasDerivWithinAt quinticStepDeriv 0 (Set.Iic 0) 0 := by
      have hev : quinticStepDeriv =ᶠ[𝓝[Set.Iic 0] 0] fun _ => (0 : ℝ) :=
        eventually_nhdsWithin_of_forall fun x hx => quinticStepDeriv_of_nonpos hx
      exact (hasDerivWithinAt_const 0 _ 0).congr_of_eventuallyEq hev (quinticStepDeriv_of_nonpos le_rfl)
    have hright : HasDerivWithinAt quinticStepDeriv 0 (Set.Ici 0) 0 := by
      have hIcc : Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := Icc_mem_nhdsGE zero_lt_one
      have hev : quinticStepDeriv =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] poly' :=
        Filter.eventually_of_mem hIcc fun x hx => by
          simp [quinticStepDeriv, poly', clamp01_mem_Icc hx]
      have hd : HasDerivWithinAt poly' 0 (Set.Ici 0) 0 := by
        simpa using (hpoly' 0).hasDerivWithinAt
      exact hd.congr_of_eventuallyEq hev (by simp [quinticStepDeriv, poly', clamp01_of_nonpos le_rfl])
    have h0 : quinticStepDeriv2 0 = 0 := by simp [quinticStepDeriv2, clamp01_of_nonpos le_rfl]
    rw [h0, ← hasDerivWithinAt_univ, ← Set.Iic_union_Ici]
    exact hleft.union hright
  · rcases lt_trichotomy u 1 with hu1 | rfl | hu1
    · have hev : quinticStepDeriv =ᶠ[𝓝 u] poly' :=
        Filter.eventually_of_mem (Ioo_mem_nhds hu0 hu1) fun x hx => by
          simp [quinticStepDeriv, poly', clamp01_mem_Icc (Set.Ioo_subset_Icc_self hx)]
      have heq_d2 : quinticStepDeriv2 u = 60 * u * (1 - u) * (1 - 2 * u) := by
        simp [quinticStepDeriv2, clamp01_mem_Icc ⟨hu0.le, hu1.le⟩]
      rw [heq_d2]
      exact (hpoly' u).congr_of_eventuallyEq hev
    · have hleft : HasDerivWithinAt quinticStepDeriv 0 (Set.Iic 1) 1 := by
        have hIcc : Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Iic (1 : ℝ)] 1 := Icc_mem_nhdsLE zero_lt_one
        have hev : quinticStepDeriv =ᶠ[𝓝[Set.Iic (1 : ℝ)] 1] poly' :=
          Filter.eventually_of_mem hIcc fun x hx => by
            simp [quinticStepDeriv, poly', clamp01_mem_Icc hx]
        have hd : HasDerivWithinAt poly' 0 (Set.Iic 1) 1 := by
          simpa using (hpoly' 1).hasDerivWithinAt
        exact hd.congr_of_eventuallyEq hev (by simp [quinticStepDeriv, poly', clamp01_of_ge_one le_rfl])
      have hright : HasDerivWithinAt quinticStepDeriv 0 (Set.Ici 1) 1 := by
        have hev : quinticStepDeriv =ᶠ[𝓝[Set.Ici 1] 1] fun _ => (0 : ℝ) :=
          eventually_nhdsWithin_of_forall fun x hx => quinticStepDeriv_of_ge_one hx
        exact (hasDerivWithinAt_const 1 _ (0 : ℝ)).congr_of_eventuallyEq hev (quinticStepDeriv_of_ge_one le_rfl)
      have h0 : quinticStepDeriv2 1 = 0 := by simp [quinticStepDeriv2, clamp01_of_ge_one le_rfl]
      rw [h0, ← hasDerivWithinAt_univ, ← Set.Iic_union_Ici (a := (1 : ℝ))]
      exact hleft.union hright
    · have hev : quinticStepDeriv =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hu1) fun x hx => quinticStepDeriv_of_ge_one hx.le
      have h0 : quinticStepDeriv2 u = 0 := by simp [quinticStepDeriv2, clamp01_of_ge_one hu1.le]
      rw [h0]
      exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev

/-- Smooth `C^2` bump function supported on `[a + 1/4, b + 3/4]` and equal to `1` on
`[a + 3/4, b + 1/4]`. -/
def vdcBump (a b : ℤ) (t : ℝ) : ℝ :=
  quinticStep (2 * (t - ((a : ℝ) + 1 / 4))) * quinticStep (2 * (((b : ℝ) + 3 / 4) - t))

private def vdcBumpDeriv (a b : ℤ) (t : ℝ) : ℝ :=
  2 * quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4))) *
      quinticStep (2 * (((b : ℝ) + 3 / 4) - t)) -
    quinticStep (2 * (t - ((a : ℝ) + 1 / 4))) *
      (2 * quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t)))

private def vdcBumpDeriv2 (a b : ℤ) (t : ℝ) : ℝ :=
  4 * quinticStepDeriv2 (2 * (t - ((a : ℝ) + 1 / 4))) *
      quinticStep (2 * (((b : ℝ) + 3 / 4) - t)) -
    8 * quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4))) *
      quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t)) +
    quinticStep (2 * (t - ((a : ℝ) + 1 / 4))) *
      (4 * quinticStepDeriv2 (2 * (((b : ℝ) + 3 / 4) - t)))

/-- Continuity of the cutoff used in truncated Poisson summation. -/
theorem continuous_vdcBump (a b : ℤ) : Continuous (vdcBump a b) := by
  unfold vdcBump
  have hc := continuous_quinticStep
  fun_prop

private lemma continuous_vdcBumpDeriv (a b : ℤ) : Continuous (vdcBumpDeriv a b) := by
  unfold vdcBumpDeriv
  have hc0 := continuous_quinticStep
  have hc1 := continuous_quinticStepDeriv
  fun_prop

private lemma continuous_vdcBumpDeriv2 (a b : ℤ) : Continuous (vdcBumpDeriv2 a b) := by
  unfold vdcBumpDeriv2
  have hc0 := continuous_quinticStep
  have hc1 := continuous_quinticStepDeriv
  have hc2 := continuous_quinticStepDeriv2
  fun_prop

private lemma hasDerivAt_vdcBump (a b : ℤ) (t : ℝ) :
    HasDerivAt (vdcBump a b) (vdcBumpDeriv a b t) t := by
  have hlinL : HasDerivAt (fun x => 2 * (x - ((a : ℝ) + 1 / 4))) 2 t :=
    (((hasDerivAt_id t).sub_const ((a : ℝ) + 1 / 4)).const_mul 2).congr_deriv (by ring)
  have hlinR : HasDerivAt (fun x => 2 * (((b : ℝ) + 3 / 4) - x)) (-2) t :=
    (((hasDerivAt_const t ((b : ℝ) + 3 / 4)).sub (hasDerivAt_id t)).const_mul 2).congr_deriv (by ring)
  have hL : HasDerivAt (fun x => quinticStep (2 * (x - ((a : ℝ) + 1 / 4))))
      (quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4))) * 2) t :=
    (hasDerivAt_quinticStep _).comp t hlinL
  have hR : HasDerivAt (fun x => quinticStep (2 * (((b : ℝ) + 3 / 4) - x)))
      (quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t)) * (-2)) t :=
    (hasDerivAt_quinticStep _).comp t hlinR
  exact (hL.mul hR).congr_deriv (by unfold vdcBumpDeriv; ring)

private lemma hasDerivAt_vdcBumpDeriv (a b : ℤ) (t : ℝ) :
    HasDerivAt (vdcBumpDeriv a b) (vdcBumpDeriv2 a b t) t := by
  have hlinL : HasDerivAt (fun x => 2 * (x - ((a : ℝ) + 1 / 4))) 2 t :=
    (((hasDerivAt_id t).sub_const ((a : ℝ) + 1 / 4)).const_mul 2).congr_deriv (by ring)
  have hlinR : HasDerivAt (fun x => 2 * (((b : ℝ) + 3 / 4) - x)) (-2) t :=
    (((hasDerivAt_const t ((b : ℝ) + 3 / 4)).sub (hasDerivAt_id t)).const_mul 2).congr_deriv (by ring)
  have hL : HasDerivAt (fun x => quinticStep (2 * (x - ((a : ℝ) + 1 / 4))))
      (2 * quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4)))) t :=
    ((hasDerivAt_quinticStep _).comp t hlinL).congr_deriv (by ring)
  have hR : HasDerivAt (fun x => quinticStep (2 * (((b : ℝ) + 3 / 4) - x)))
      (-2 * quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t))) t :=
    ((hasDerivAt_quinticStep _).comp t hlinR).congr_deriv (by ring)
  have hL' : HasDerivAt (fun x => quinticStepDeriv (2 * (x - ((a : ℝ) + 1 / 4))))
      (2 * quinticStepDeriv2 (2 * (t - ((a : ℝ) + 1 / 4)))) t :=
    ((hasDerivAt_quinticStepDeriv _).comp t hlinL).congr_deriv (by ring)
  have hR' : HasDerivAt (fun x => quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - x)))
      (-2 * quinticStepDeriv2 (2 * (((b : ℝ) + 3 / 4) - t))) t :=
    ((hasDerivAt_quinticStepDeriv _).comp t hlinR).congr_deriv (by ring)
  have h1 := (hL'.const_mul 2).mul hR
  have h2 := hL.mul (hR'.const_mul 2)
  exact (h1.sub h2).congr_deriv (by unfold vdcBumpDeriv2; ring)

private lemma vdcBump_props {a b : ℤ} (hab : a < b) :
    (∀ t ∉ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), vdcBump a b t = 0) ∧
    (∀ t ∈ Set.Icc ((a : ℝ) + 3 / 4) ((b : ℝ) + 1 / 4), vdcBump a b t = 1) ∧
    (∀ t, 0 ≤ vdcBump a b t ∧ vdcBump a b t ≤ 1) ∧
    (∀ t, |vdcBumpDeriv a b t| ≤ 4) ∧
    (∀ t ∈ Set.Icc ((a : ℝ) + 3 / 4) ((b : ℝ) + 1 / 4),
      vdcBumpDeriv a b t = 0 ∧ vdcBumpDeriv2 a b t = 0) ∧
    (vdcBump a b ((a : ℝ) + 1 / 4) = 0 ∧ vdcBump a b ((b : ℝ) + 3 / 4) = 0) ∧
    (vdcBumpDeriv a b ((a : ℝ) + 1 / 4) = 0 ∧ vdcBumpDeriv a b ((b : ℝ) + 3 / 4) = 0) ∧
    (∀ t, |vdcBumpDeriv2 a b t| ≤ 160) := by
  have hab_R : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with hlt | hgt
    · rw [vdcBump, quinticStep_of_nonpos (by linarith), zero_mul]
    · rw [vdcBump, quinticStep_of_nonpos (show 2 * (((b : ℝ) + 3 / 4) - t) ≤ 0 by linarith), mul_zero]
  · intro t ht
    rw [vdcBump, quinticStep_of_ge_one (by linarith [ht.1]),
      quinticStep_of_ge_one (by linarith [ht.2]), mul_one]
  · intro t
    obtain ⟨ha0, ha1, _, _, _⟩ := quinticStep_bounds (2 * (t - ((a : ℝ) + 1 / 4)))
    obtain ⟨hb0, hb1, _, _, _⟩ := quinticStep_bounds (2 * (((b : ℝ) + 3 / 4) - t))
    exact ⟨mul_nonneg ha0 hb0, (mul_le_mul ha1 hb1 hb0 zero_le_one).trans_eq (one_mul 1)⟩
  · intro t
    obtain ⟨ha0, ha1, ha'0, ha'1, _⟩ := quinticStep_bounds (2 * (t - ((a : ℝ) + 1 / 4)))
    obtain ⟨hb0, hb1, hb'0, hb'1, _⟩ := quinticStep_bounds (2 * (((b : ℝ) + 3 / 4) - t))
    unfold vdcBumpDeriv
    have hdisj : quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4))) = 0 ∨
        quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t)) = 0 := by
      by_cases ht_mid : t ≤ (a : ℝ) + 3 / 4
      · right; exact quinticStepDeriv_of_ge_one (by linarith)
      · left; exact quinticStepDeriv_of_ge_one (by linarith)
    rcases hdisj with h0 | h0
    · rw [h0]; simp only [mul_zero, zero_mul, zero_sub, abs_neg]
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    · rw [h0]; simp only [mul_zero, sub_zero]
      rw [abs_of_nonneg (by positivity)]
      nlinarith
  · intro t ht
    have ha1 : 1 ≤ 2 * (t - ((a : ℝ) + 1 / 4)) := by linarith [ht.1]
    have hb1 : 1 ≤ 2 * (((b : ℝ) + 3 / 4) - t) := by linarith [ht.2]
    have ha' : quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4))) = 0 := quinticStepDeriv_of_ge_one ha1
    have hb' : quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t)) = 0 := quinticStepDeriv_of_ge_one hb1
    have ha'' : quinticStepDeriv2 (2 * (t - ((a : ℝ) + 1 / 4))) = 0 := by
      unfold quinticStepDeriv2; rw [clamp01_of_ge_one ha1]; ring
    have hb'' : quinticStepDeriv2 (2 * (((b : ℝ) + 3 / 4) - t)) = 0 := by
      unfold quinticStepDeriv2; rw [clamp01_of_ge_one hb1]; ring
    refine ⟨?_, ?_⟩
    · unfold vdcBumpDeriv; rw [ha', hb']; ring
    · unfold vdcBumpDeriv2; rw [ha', hb', ha'', hb'']; ring
  · constructor
    · unfold vdcBump
      rw [quinticStep_of_nonpos (show 2 * (((a : ℝ) + 1 / 4) - ((a : ℝ) + 1 / 4)) ≤ 0 by linarith), zero_mul]
    · unfold vdcBump
      rw [quinticStep_of_nonpos (show 2 * (((b : ℝ) + 3 / 4) - ((b : ℝ) + 3 / 4)) ≤ 0 by linarith), mul_zero]
  · constructor
    · unfold vdcBumpDeriv
      have h0 : 2 * (((a : ℝ) + 1 / 4) - ((a : ℝ) + 1 / 4)) ≤ 0 := by linarith
      rw [quinticStep_of_nonpos h0, quinticStepDeriv_of_nonpos h0]
      ring
    · unfold vdcBumpDeriv
      have h0 : 2 * (((b : ℝ) + 3 / 4) - ((b : ℝ) + 3 / 4)) ≤ 0 := by linarith
      rw [quinticStep_of_nonpos h0, quinticStepDeriv_of_nonpos h0]
      ring
  · intro t
    obtain ⟨ha0, ha1, ha'0, ha'1, ha''⟩ := quinticStep_bounds (2 * (t - ((a : ℝ) + 1 / 4)))
    obtain ⟨hb0, hb1, hb'0, hb'1, hb''⟩ := quinticStep_bounds (2 * (((b : ℝ) + 3 / 4) - t))
    unfold vdcBumpDeriv2
    calc |4 * quinticStepDeriv2 (2 * (t - ((a : ℝ) + 1 / 4))) *
            quinticStep (2 * (((b : ℝ) + 3 / 4) - t)) -
          8 * quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4))) *
            quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t)) +
          quinticStep (2 * (t - ((a : ℝ) + 1 / 4))) *
            (4 * quinticStepDeriv2 (2 * (((b : ℝ) + 3 / 4) - t)))|
        ≤ |4 * quinticStepDeriv2 (2 * (t - ((a : ℝ) + 1 / 4))) *
            quinticStep (2 * (((b : ℝ) + 3 / 4) - t))| +
          |8 * quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4))) *
            quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t))| +
          |quinticStep (2 * (t - ((a : ℝ) + 1 / 4))) *
            (4 * quinticStepDeriv2 (2 * (((b : ℝ) + 3 / 4) - t)))| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 4 * 16 * 1 + 8 * 2 * 2 + 1 * (4 * 16) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
          have hq1 : |quinticStep (2 * (((b : ℝ) + 3 / 4) - t))| ≤ 1 := by
            rwa [abs_of_nonneg hb0]
          have hq2 : |quinticStep (2 * (t - ((a : ℝ) + 1 / 4)))| ≤ 1 := by
            rwa [abs_of_nonneg ha0]
          have hq'1 : |quinticStepDeriv (2 * (t - ((a : ℝ) + 1 / 4)))| ≤ 2 := by
            rwa [abs_of_nonneg ha'0]
          have hq'2 : |quinticStepDeriv (2 * (((b : ℝ) + 3 / 4) - t))| ≤ 2 := by
            rwa [abs_of_nonneg hb'0]
          have h4 : |(4 : ℝ)| = 4 := by norm_num
          have h8 : |(8 : ℝ)| = 8 := by norm_num
          rw [h4, h8]
          gcongr
      _ = 160 := by norm_num

/-- The Poisson cutoff takes values in the closed unit interval. -/
theorem vdcBump_mem_unitInterval {a b : ℤ} (hab : a < b) (t : ℝ) :
    0 ≤ vdcBump a b t ∧ vdcBump a b t ≤ 1 :=
  (vdcBump_props hab).2.2.1 t

/-- The Poisson cutoff equals one between its two transition intervals. -/
theorem vdcBump_eq_one {a b : ℤ} (hab : a < b) {t : ℝ}
    (ht : t ∈ Set.Icc ((a:ℝ)+3/4) ((b:ℝ)+1/4)) : vdcBump a b t = 1 :=
  (vdcBump_props hab).2.1 t ht

private lemma vdcBump_end_bound_left (a b : ℤ) (t : ℝ) :
    |vdcBump a b t| ≤ 128 * (t - ((a : ℝ) + 1 / 4)) ^ 2 := by
  by_cases ht : t ≤ (a : ℝ) + 1 / 4
  · rw [show vdcBump a b t = 0 by rw [vdcBump, quinticStep_of_nonpos (by linarith), zero_mul], abs_zero]
    positivity
  · have ht_gt : (a : ℝ) + 1 / 4 < t := not_le.mp ht
    set u := 2 * (t - ((a : ℝ) + 1 / 4))
    have hu_pos : 0 < u := by positivity
    obtain ⟨hb0, _, _, _, _⟩ := quinticStep_bounds (2 * (((b : ℝ) + 3 / 4) - t))
    have hq_le : |quinticStep u| ≤ 16 * u ^ 2 := by
      by_cases hu1 : 1 ≤ u
      · rw [quinticStep_of_ge_one hu1, abs_one]
        nlinarith [sq_nonneg u]
      · have hu_le : u ≤ 1 := (not_le.mp hu1).le
        have hc : clamp01 u = u := clamp01_mem_Icc ⟨hu_pos.le, hu_le⟩
        have hpos : 0 ≤ quinticStep u := (quinticStep_bounds u).1
        rw [abs_of_nonneg hpos]
        dsimp only [quinticStep]
        rw [hc]
        have hu3 : u ^ 3 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
        have hu4 : 0 ≤ u ^ 4 := by positivity
        have hu5 : u ^ 5 ≤ u ^ 2 := by
          have : u ^ 3 ≤ 1 := by nlinarith [sq_nonneg u]
          nlinarith [sq_nonneg u]
        linarith
    have hb_abs : |quinticStep (2 * (((b : ℝ) + 3 / 4) - t))| ≤ 1 := by
      rw [abs_of_nonneg hb0]; exact (quinticStep_bounds _).2.1
    rw [vdcBump, abs_mul]
    calc |quinticStep u| * |quinticStep (2 * (((b : ℝ) + 3 / 4) - t))|
        ≤ (16 * u ^ 2) * 1 := mul_le_mul hq_le hb_abs (abs_nonneg _) (by positivity)
      _ = 64 * (t - ((a : ℝ) + 1 / 4)) ^ 2 := by dsimp only [u]; ring
      _ ≤ 128 * (t - ((a : ℝ) + 1 / 4)) ^ 2 := by
          have : 0 ≤ (t - ((a : ℝ) + 1 / 4)) ^ 2 := sq_nonneg _
          linarith

private lemma vdcBump_end_bound_right (a b : ℤ) (t : ℝ) :
    |vdcBump a b t| ≤ 128 * (t - ((b : ℝ) + 3 / 4)) ^ 2 := by
  by_cases ht : (b : ℝ) + 3 / 4 ≤ t
  · rw [show vdcBump a b t = 0 by rw [vdcBump, quinticStep_of_nonpos (show 2 * (((b : ℝ) + 3 / 4) - t) ≤ 0 by linarith), mul_zero], abs_zero]
    positivity
  · have ht_lt : t < (b : ℝ) + 3 / 4 := not_le.mp ht
    set v := 2 * (((b : ℝ) + 3 / 4) - t)
    have hv_pos : 0 < v := by positivity
    obtain ⟨ha0, _, _, _, _⟩ := quinticStep_bounds (2 * (t - ((a : ℝ) + 1 / 4)))
    have hq_le : |quinticStep v| ≤ 16 * v ^ 2 := by
      by_cases hv1 : 1 ≤ v
      · rw [quinticStep_of_ge_one hv1, abs_one]
        nlinarith [sq_nonneg v]
      · have hv_le : v ≤ 1 := (not_le.mp hv1).le
        have hc : clamp01 v = v := clamp01_mem_Icc ⟨hv_pos.le, hv_le⟩
        have hpos : 0 ≤ quinticStep v := (quinticStep_bounds v).1
        rw [abs_of_nonneg hpos]
        dsimp only [quinticStep]
        rw [hc]
        have hv3 : v ^ 3 ≤ v ^ 2 := by nlinarith [sq_nonneg v]
        have hv4 : 0 ≤ v ^ 4 := by positivity
        have hv5 : v ^ 5 ≤ v ^ 2 := by
          have : v ^ 3 ≤ 1 := by nlinarith [sq_nonneg v]
          nlinarith [sq_nonneg v]
        linarith
    have ha_abs : |quinticStep (2 * (t - ((a : ℝ) + 1 / 4)))| ≤ 1 := by
      rw [abs_of_nonneg ha0]; exact (quinticStep_bounds _).2.1
    rw [vdcBump, abs_mul]
    calc |quinticStep (2 * (t - ((a : ℝ) + 1 / 4)))| * |quinticStep v|
        ≤ 1 * (16 * v ^ 2) := mul_le_mul ha_abs hq_le (abs_nonneg _) zero_le_one
      _ = 64 * (t - ((b : ℝ) + 3 / 4)) ^ 2 := by dsimp only [v]; ring
      _ ≤ 128 * (t - ((b : ℝ) + 3 / 4)) ^ 2 := by
          have : 0 ≤ (t - ((b : ℝ) + 3 / 4)) ^ 2 := sq_nonneg _
          linarith

private lemma vdcBump_int_mem_Ioc {a b : ℤ} (_hab : a < b) :
    Finset.Icc ⌈(a : ℝ) + 1 / 4⌉ ⌊(b : ℝ) + 3 / 4⌋ = Finset.Ioc a b := by
  have hceil : ⌈(a : ℝ) + 1 / 4⌉ = a + 1 := by rw [Int.ceil_eq_iff]; norm_num
  have hfloor : ⌊(b : ℝ) + 3 / 4⌋ = b := by rw [Int.floor_eq_iff]; norm_num
  rw [hceil, hfloor]
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

private lemma vdc_sum_recips_diff_le (R : ℝ) (M K : ℕ) (hK : 1 ≤ K) (hR : 1 ≤ R)
    (α β : ℝ) (hαβ0 : α ≤ β) (hαβ : β - α ≤ (K : ℝ)) :
    ∑ j ∈ Finset.range M, (1 / (R + (j : ℝ)) - 1 / (R + (j : ℝ) + (β - α))) ≤
      1 + Real.log (K : ℝ) := by
  have h1 :
      ∑ j ∈ Finset.range M, (1 / (R + (j : ℝ)) - 1 / (R + (j : ℝ) + (β - α))) ≤
        ∑ j ∈ Finset.range M, (1 / (R + (j : ℝ)) - 1 / (R + (j : ℝ) + (K : ℝ))) := by
    refine Finset.sum_le_sum fun j _ => ?_
    refine sub_le_sub_left ?_ _
    exact div_le_div_of_nonneg_left zero_le_one (by linarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]) (by linarith)
  have h2 :
      ∑ j ∈ Finset.range M, (1 / (R + (j : ℝ)) - 1 / (R + (j : ℝ) + (K : ℝ))) ≤
        ∑ j ∈ Finset.range K, 1 / (R + (j : ℝ)) := by
    let g : ℕ → ℝ := fun n => 1 / (R + (n : ℝ))
    have hsplit :
        ∑ j ∈ Finset.range M, (g j - g (j + K)) =
          ∑ j ∈ Finset.range M, g j - ∑ j ∈ Finset.range M, g (j + K) := by
        rw [Finset.sum_sub_distrib]
    have heq_shift : ∑ j ∈ Finset.range M, g (j + K) = ∑ j ∈ Finset.Ico K (M + K), g j := by
      refine Finset.sum_bij (fun j _ => j + K) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_range, Finset.mem_Ico] at hj ⊢; omega
      · intro _ _ _ _ h; omega
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        exact ⟨j - K, Finset.mem_range.mpr (by omega), by omega⟩
      · intro _ _; rfl
    have hsub_le : ∑ j ∈ Finset.range M, g j - ∑ j ∈ Finset.Ico K (M + K), g j ≤
        ∑ j ∈ Finset.range K, g j := by
      have hg_nonneg : ∀ n, 0 ≤ g n := fun n => by dsimp only [g]; positivity
      by_cases hMK : M ≤ K
      · have hle : ∑ j ∈ Finset.range M, g j ≤ ∑ j ∈ Finset.range K, g j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMK) (fun _ _ _ => hg_nonneg _)
        have hpos : 0 ≤ ∑ j ∈ Finset.Ico K (M + K), g j :=
          Finset.sum_nonneg fun _ _ => hg_nonneg _
        linarith
      · have hKM : K < M := not_le.mp hMK
        have hA : ∑ j ∈ Finset.range M, g j =
            ∑ j ∈ Finset.range K, g j + ∑ j ∈ Finset.Ico K M, g j := by
          rw [← Finset.sum_range_add_sum_Ico g hKM.le]
        have hB : ∑ j ∈ Finset.Ico K M, g j ≤ ∑ j ∈ Finset.Ico K (M + K), g j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
            (fun _ _ _ => hg_nonneg _)
        linarith
    calc ∑ j ∈ Finset.range M, (1 / (R + (j : ℝ)) - 1 / (R + (j : ℝ) + (K : ℝ)))
        = ∑ j ∈ Finset.range M, (g j - g (j + K)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [g]
          push_cast
          ring_nf
      _ = ∑ j ∈ Finset.range M, g j - ∑ j ∈ Finset.Ico K (M + K), g j := by rw [hsplit, heq_shift]
      _ ≤ ∑ j ∈ Finset.range K, g j := hsub_le
  have h3 : ∑ j ∈ Finset.range K, 1 / (R + (j : ℝ)) ≤ 1 + Real.log (K : ℝ) := by
    calc ∑ j ∈ Finset.range K, 1 / (R + (j : ℝ))
        ≤ ∑ j ∈ Finset.range K, 1 / ((j : ℝ) + 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
      _ ≤ 1 + Real.log (K : ℝ) := by
          clear * - hK
          induction K, hK using Nat.le_induction with
          | base => simp
          | succ m hm ih =>
            rw [Finset.sum_range_succ]
            have hm_pos : (0 : ℝ) < m := by positivity
            have hinv : 1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
              have h := Real.log_le_sub_one_of_pos (div_pos hm_pos (by positivity : 0 < (m : ℝ) + 1))
              rw [Real.log_div hm_pos.ne' (by positivity)] at h
              have heq : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
                field_simp [(by positivity : (m : ℝ) + 1 ≠ 0)]
                ring
              linarith
            push_cast
            linarith
  exact h1.trans (h2.trans h3)

private lemma vdc_sum_inv_sq_le (M : ℕ) :
    ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  cases M with
  | zero => simp
  | succ M' =>
    have hbd : ∀ m : ℕ, 1 ≤ m →
        ∑ j ∈ Finset.range m, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / (m : ℝ) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp; norm_num
      | succ n hn ihn =>
        rw [Finset.sum_range_succ]
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hstep : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
          rw [div_sub_div _ _ hn_pos.ne' hn1_pos.ne', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hn_pos]
        push_cast
        linarith
    exact (hbd (M' + 1) (Nat.succ_pos M')).trans (by
      have : (0 : ℝ) ≤ 1 / ((M' + 1 : ℕ) : ℝ) := by positivity
      linarith)

private lemma vdc_tail_integral_bound {a b : ℤ} (hab : a < b) {f f' f'' : ℝ → ℝ}
    {α β : ℝ} (hαβ : α ≤ β)
    (hf : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), HasDerivAt f' (f'' t) t)
    (hf''_cont : ContinuousOn f'' (Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4)))
    (hmono : (∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), 0 ≤ f'' t) ∨
      (∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), f'' t ≤ 0))
    (hbounds : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), α ≤ f' t ∧ f' t ≤ β)
    (n : ℤ) (hn : n ≤ ⌊α⌋ - 2 ∨ ⌈β⌉ + 2 ≤ n) :
    ‖∫ t in ((a : ℝ) + 1 / 4)..((b : ℝ) + 3 / 4),
      (vdcBump a b t : ℂ) * vdcE (f t - (n : ℝ) * t)‖ ≤
      (if ⌈β⌉ + 2 ≤ n then
        5 / ((n : ℝ) - ⌈β⌉) ^ 2 + (1 / ((n : ℝ) - β) - 1 / ((n : ℝ) - α))
      else
        5 / ((⌊α⌋ : ℝ) - n) ^ 2 + (1 / (α - (n : ℝ)) - 1 / (β - (n : ℝ)))) := by
  let A : ℝ := (a : ℝ) + 1 / 4
  let B : ℝ := (b : ℝ) + 3 / 4
  have hab_R : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
  have hAB : A ≤ B := by dsimp only [A, B]; linarith
  let χ := vdcBump a b
  let χ' := vdcBumpDeriv a b
  let χ'' := vdcBumpDeriv2 a b
  obtain ⟨_, _, hχ_bd, hχ'_bd, hχ_mid, hχ_end, hχ'_end, _⟩ := vdcBump_props hab
  let G : ℝ → ℝ := fun t => f t - (n : ℝ) * t
  let G' : ℝ → ℝ := fun t => f' t - (n : ℝ)
  have hG : ∀ t ∈ Set.Icc A B, HasDerivAt G (G' t) t := fun t ht => by
    have hn_d : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (n : ℝ)
    exact (hf t ht).sub hn_d
  have hG' : ∀ t ∈ Set.Icc A B, HasDerivAt G' (f'' t) t := fun t ht => (hf' t ht).sub_const (n : ℝ)
  have hG'_cont : ContinuousOn G' (Set.Icc A B) := fun t ht =>
    (hG' t ht).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Set.Icc A B) := fun t ht =>
    (hG t ht).continuousAt.continuousWithinAt
  have hG'_ge2 : ∀ t ∈ Set.Icc A B, 2 ≤ |G' t| := fun t ht => by
    obtain ⟨hlo, hhi⟩ := hbounds t ht
    rcases hn with hle | hge
    · have hfl : (⌊α⌋ : ℝ) ≤ α := Int.floor_le α
      have hn2 : (n : ℝ) ≤ (⌊α⌋ : ℝ) - 2 := by exact_mod_cast hle
      have hpos : 2 ≤ G' t := by dsimp only [G']; linarith
      exact hpos.trans (le_abs_self _)
    · have hcl : β ≤ (⌈β⌉ : ℝ) := Int.le_ceil β
      have hn2 : (⌈β⌉ : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hge
      have hneg : G' t ≤ -2 := by dsimp only [G']; linarith
      calc (2 : ℝ) ≤ -G' t := by linarith
        _ ≤ |G' t| := neg_le_abs _
  have hG'_real_ne : ∀ t ∈ Set.Icc A B, G' t ≠ 0 := fun t ht h0 => by
    have := hG'_ge2 t ht
    rw [h0, abs_zero] at this
    linarith
  have hG'_ne : ∀ t ∈ Set.Icc A B, (G' t : ℂ) ≠ 0 := fun t ht =>
    Complex.ofReal_ne_zero.mpr (hG'_real_ne t ht)
  let κ : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hκ_ne : κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  let u₁ : ℝ → ℂ := fun t => (χ t : ℂ) / (κ * (G' t : ℂ))
  let u₁' : ℝ → ℂ := fun t =>
    ((χ' t : ℂ) * (G' t : ℂ) - (χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2)
  let v : ℝ → ℂ := fun t => vdcE (G t)
  let v' : ℝ → ℂ := fun t => κ * (G' t : ℂ) * v t
  have hu₁ : ∀ t ∈ Set.uIcc A B, HasDerivAt u₁ (u₁' t) t := fun t ht => by
    rw [Set.uIcc_of_le hAB] at ht
    have hnum : HasDerivAt (fun x => (χ x : ℂ)) (χ' t : ℂ) t :=
      (hasDerivAt_vdcBump a b t).ofReal_comp
    have hden : HasDerivAt (fun x => κ * (G' x : ℂ)) (κ * (f'' t : ℂ)) t :=
      (hG' t ht).ofReal_comp.const_mul κ
    have hden_ne : κ * (G' t : ℂ) ≠ 0 := mul_ne_zero hκ_ne (hG'_ne t ht)
    convert hnum.div hden hden_ne using 1
    dsimp only [u₁']
    field_simp [hκ_ne, hG'_ne t ht]
  have hv : ∀ t ∈ Set.uIcc A B, HasDerivAt v (v' t) t := fun t ht => by
    rw [Set.uIcc_of_le hAB] at ht
    have h1 : HasDerivAt (fun x => κ * (G x : ℂ)) (κ * (G' t : ℂ)) t :=
      (hG t ht).ofReal_comp.const_mul κ
    have hv_eq : v = fun x => Complex.exp (κ * (G x : ℂ)) :=
      funext fun x => congrArg Complex.exp (by dsimp only [κ]; ring)
    rw [hv_eq]
    convert h1.cexp using 1
    dsimp only [v']
    rw [hv_eq]
    dsimp only
    ring
  have hv_cont : ContinuousOn v (Set.Icc A B) :=
    Complex.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hGc)).mul continuousOn_const)
  have hu₁' : IntervalIntegrable u₁' volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
    refine ContinuousOn.integrableOn_Icc ?_
    have hc1 : ContinuousOn (fun t => (χ t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn (continuous_vdcBump a b).continuousOn
    have hc2 : ContinuousOn (fun t => (χ' t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn (continuous_vdcBumpDeriv a b).continuousOn
    have hG'c : ContinuousOn (fun t => (G' t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn hG'_cont
    have hf''c : ContinuousOn (fun t => (f'' t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn hf''_cont
    have hnum : ContinuousOn (fun t => (χ' t : ℂ) * (G' t : ℂ) - (χ t : ℂ) * (f'' t : ℂ)) (Set.Icc A B) :=
      (hc2.mul hG'c).sub (hc1.mul hf''c)
    have hden : ContinuousOn (fun t => κ * (G' t : ℂ) ^ 2) (Set.Icc A B) :=
      continuousOn_const.mul (hG'c.pow 2)
    exact hnum.div hden fun t ht => mul_ne_zero hκ_ne (pow_ne_zero 2 (hG'_ne t ht))
  have hv' : IntervalIntegrable v' volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
    refine ContinuousOn.integrableOn_Icc ?_
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hG'_cont)).mul hv_cont
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu₁ hv hu₁' hv'
  have hu₁A : u₁ A = 0 := by
    dsimp only [u₁, χ, A]; rw [hχ_end.1, Complex.ofReal_zero, zero_div]
  have hu₁B : u₁ B = 0 := by
    dsimp only [u₁, χ, B]; rw [hχ_end.2, Complex.ofReal_zero, zero_div]
  have hlhs1 : ∫ t in A..B, u₁ t * v' t = ∫ t in A..B, (χ t : ℂ) * v t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hAB] at ht
    dsimp only [u₁, v']
    field_simp [hκ_ne, hG'_ne t ht]
  rw [hlhs1, hu₁A, hu₁B, zero_mul, zero_mul, sub_zero, zero_sub] at hibp1
  let u₂ : ℝ → ℂ := fun t => (χ' t : ℂ) / (κ ^ 2 * (G' t : ℂ) ^ 2)
  let u₂' : ℝ → ℂ := fun t =>
    ((χ'' t : ℂ) * (G' t : ℂ) - 2 * (χ' t : ℂ) * (f'' t : ℂ)) / (κ ^ 2 * (G' t : ℂ) ^ 3)
  have hu₂ : ∀ t ∈ Set.uIcc A B, HasDerivAt u₂ (u₂' t) t := fun t ht => by
    rw [Set.uIcc_of_le hAB] at ht
    have hnum : HasDerivAt (fun x => (χ' x : ℂ)) (χ'' t : ℂ) t :=
      (hasDerivAt_vdcBumpDeriv a b t).ofReal_comp
    have hden : HasDerivAt (fun x => κ ^ 2 * (G' x : ℂ) ^ 2)
        (κ ^ 2 * (2 * (G' t : ℂ) * (f'' t : ℂ))) t := by
      have hp := (hG' t ht).ofReal_comp.pow 2
      convert hp.const_mul (κ ^ 2) using 1
      ring
    have hden_ne : κ ^ 2 * (G' t : ℂ) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hκ_ne) (pow_ne_zero 2 (hG'_ne t ht))
    convert hnum.div hden hden_ne using 1
    dsimp only [u₂']
    field_simp [hκ_ne, hG'_ne t ht]
  have hu₂' : IntervalIntegrable u₂' volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
    refine ContinuousOn.integrableOn_Icc ?_
    have hc2 : ContinuousOn (fun t => (χ' t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn (continuous_vdcBumpDeriv a b).continuousOn
    have hc3 : ContinuousOn (fun t => (χ'' t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn (continuous_vdcBumpDeriv2 a b).continuousOn
    have hG'c : ContinuousOn (fun t => (G' t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn hG'_cont
    have hf''c : ContinuousOn (fun t => (f'' t : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn hf''_cont
    have hnum : ContinuousOn (fun t => (χ'' t : ℂ) * (G' t : ℂ) - 2 * (χ' t : ℂ) * (f'' t : ℂ))
        (Set.Icc A B) :=
      (hc3.mul hG'c).sub ((continuousOn_const.mul hc2).mul hf''c)
    have hden : ContinuousOn (fun t => κ ^ 2 * (G' t : ℂ) ^ 3) (Set.Icc A B) :=
      continuousOn_const.mul (hG'c.pow 3)
    exact hnum.div hden fun t ht => mul_ne_zero (pow_ne_zero 2 hκ_ne) (pow_ne_zero 3 (hG'_ne t ht))
  have hibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu₂ hv hu₂' hv'
  have hu₂A : u₂ A = 0 := by
    dsimp only [u₂, χ', A]; rw [hχ'_end.1, Complex.ofReal_zero, zero_div]
  have hu₂B : u₂ B = 0 := by
    dsimp only [u₂, χ', B]; rw [hχ'_end.2, Complex.ofReal_zero, zero_div]
  have hlhs2 : ∫ t in A..B, u₂ t * v' t =
      ∫ t in A..B, ((χ' t : ℂ) / (κ * (G' t : ℂ))) * v t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hAB] at ht
    dsimp only [u₂, v']
    field_simp [hκ_ne, hG'_ne t ht]
  rw [hlhs2, hu₂A, hu₂B, zero_mul, zero_mul, sub_zero, zero_sub] at hibp2
  let term1 : ℝ → ℂ := fun t => ((χ' t : ℂ) / (κ * (G' t : ℂ))) * v t
  let term2 : ℝ → ℂ := fun t => -(((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t)
  have hsplit_u1 : ∀ t ∈ Set.Icc A B, u₁' t * v t = term1 t + term2 t := fun t ht => by
    dsimp only [u₁', term1, term2]
    field_simp [hκ_ne, hG'_ne t ht]
    ring
  have ht1_int : IntervalIntegrable term1 volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
    refine ContinuousOn.integrableOn_Icc ?_
    have hc2 := (continuous_vdcBumpDeriv a b).continuousOn (s := Set.Icc A B)
    exact ((Complex.continuous_ofReal.comp_continuousOn hc2).div
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hG'_cont))
      fun t ht => mul_ne_zero hκ_ne (hG'_ne t ht)).mul hv_cont
  have ht2_int : IntervalIntegrable term2 volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
    refine ContinuousOn.integrableOn_Icc ?_
    have hc1 := (continuous_vdcBump a b).continuousOn (s := Set.Icc A B)
    exact (((Complex.continuous_ofReal.comp_continuousOn hc1).mul
      (Complex.continuous_ofReal.comp_continuousOn hf''_cont)).div
      (continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hG'_cont).pow 2))
      fun t ht => mul_ne_zero hκ_ne (pow_ne_zero 2 (hG'_ne t ht))).mul hv_cont |>.neg
  have hmain_eq :
      ∫ t in A..B, (χ t : ℂ) * v t =
        (∫ t in A..B, u₂' t * v t) +
          ∫ t in A..B, ((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t := by
    have hcongr : ∫ t in A..B, u₁' t * v t = ∫ t in A..B, (term1 t + term2 t) :=
      intervalIntegral.integral_congr fun t ht => hsplit_u1 t (Set.uIcc_of_le hAB ▸ ht)
    have hsplit_int : ∫ t in A..B, u₁' t * v t =
        (∫ t in A..B, term1 t) + ∫ t in A..B, term2 t := by
      rw [hcongr, intervalIntegral.integral_add ht1_int ht2_int]
    rw [hibp1, hsplit_int, neg_add, hibp2]
    have hneg_t2 : -(∫ t in A..B, term2 t) =
        ∫ t in A..B, ((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => by dsimp only [term2]; ring
    rw [hneg_t2]
    ring
  let g1 : ℝ → ℂ := fun t => ((χ'' t : ℂ) / (κ ^ 2 * (G' t : ℂ) ^ 2)) * v t
  let g2 : ℝ → ℂ := fun t => -((2 * (χ' t : ℂ) * (f'' t : ℂ)) / (κ ^ 2 * (G' t : ℂ) ^ 3) * v t)
  have hu₂'_split : ∀ t ∈ Set.Icc A B, u₂' t * v t = g1 t + g2 t := fun t ht => by
    dsimp only [u₂', g1, g2]
    have hgne : (G' t : ℂ) ≠ 0 := hG'_ne t ht
    field_simp [hκ_ne, hgne]
    ring
  have hg1_cont : ContinuousOn g1 (Set.Icc A B) := by
    have hc3 := (continuous_vdcBumpDeriv2 a b).continuousOn (s := Set.Icc A B)
    exact ((Complex.continuous_ofReal.comp_continuousOn hc3).div
      (continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hG'_cont).pow 2))
      fun t ht => mul_ne_zero (pow_ne_zero 2 hκ_ne) (pow_ne_zero 2 (hG'_ne t ht))).mul hv_cont
  have hg2_cont : ContinuousOn g2 (Set.Icc A B) := by
    have hc2 := (continuous_vdcBumpDeriv a b).continuousOn (s := Set.Icc A B)
    exact (((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc2)).mul
      (Complex.continuous_ofReal.comp_continuousOn hf''_cont)).div
      (continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hG'_cont).pow 3))
      fun t ht => mul_ne_zero (pow_ne_zero 2 hκ_ne) (pow_ne_zero 3 (hG'_ne t ht))).mul hv_cont |>.neg
  have hg1_int : IntervalIntegrable g1 volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hg1_cont.integrableOn_Icc
  have hg2_int : IntervalIntegrable g2 volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hg2_cont.integrableOn_Icc
  have hu₂'_eq : ∫ t in A..B, u₂' t * v t = (∫ t in A..B, g1 t) + ∫ t in A..B, g2 t := by
    rw [← intervalIntegral.integral_add hg1_int hg2_int]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hAB] at ht
    exact hu₂'_split t ht
  have hκ_norm : ‖κ‖ = 2 * Real.pi := by
    dsimp only [κ]
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  have hκ_sq : 36 ≤ ‖κ‖ ^ 2 := by
    have : 6 ≤ ‖κ‖ := by linarith [Real.pi_gt_three, hκ_norm]
    nlinarith
  let mdist : ℝ := if ⌈β⌉ + 2 ≤ n then (n : ℝ) - ⌈β⌉ else (⌊α⌋ : ℝ) - n
  have hmdist_ge2 : 2 ≤ mdist := by
    dsimp only [mdist]
    split_ifs with hge
    · exact_mod_cast (by omega : (2 : ℤ) ≤ n - ⌈β⌉)
    · have hle : n ≤ ⌊α⌋ - 2 := hn.resolve_right hge
      exact_mod_cast (by omega : (2 : ℤ) ≤ ⌊α⌋ - n)
  have hm_le_G' : ∀ t ∈ Set.Icc A B, mdist ≤ |G' t| := fun t ht => by
    obtain ⟨hlo, hhi⟩ := hbounds t ht
    dsimp only [mdist, G']
    split_ifs with hge
    · have hcl : β ≤ (⌈β⌉ : ℝ) := Int.le_ceil β
      have hneg : f' t - n ≤ -((n : ℝ) - ⌈β⌉) := by linarith
      calc (n : ℝ) - ⌈β⌉ ≤ -(f' t - n) := by linarith
        _ ≤ |f' t - n| := neg_le_abs _
    · have hfl : (⌊α⌋ : ℝ) ≤ α := Int.floor_le α
      have hpos : (⌊α⌋ : ℝ) - n ≤ f' t - n := by linarith
      exact hpos.trans (le_abs_self _)
  have hg1_bd : ‖∫ t in A..B, g1 t‖ ≤ 5 / mdist ^ 2 := by
    let bound1 : ℝ → ℝ := fun t => |χ'' t| / (36 * mdist ^ 2)
    have hb1_cont : Continuous bound1 := by
      have hc3 := continuous_vdcBumpDeriv2 a b
      unfold bound1
      fun_prop
    have hnorm_le : ‖∫ t in A..B, g1 t‖ ≤ ∫ t in A..B, bound1 t := by
      calc ‖∫ t in A..B, g1 t‖ ≤ ∫ t in A..B, ‖g1 t‖ :=
            intervalIntegral.norm_integral_le_integral_norm hAB
        _ ≤ ∫ t in A..B, bound1 t := by
            refine intervalIntegral.integral_mono_on hAB hg1_int.norm
              (hb1_cont.intervalIntegrable A B) fun t ht => ?_
            have hvt : ‖v t‖ = 1 := norm_vdcE (G t)
            have hg1_norm : ‖g1 t‖ = |χ'' t| / (‖κ‖ ^ 2 * |G' t| ^ 2) := by
              dsimp only [g1]
              rw [norm_mul, hvt, mul_one, norm_div, norm_mul, norm_pow, norm_pow,
                Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
            rw [hg1_norm]
            dsimp only [bound1]
            have hm_sq : mdist ^ 2 ≤ |G' t| ^ 2 :=
              pow_le_pow_left₀ (by linarith) (hm_le_G' t ht) 2
            have hden : 36 * mdist ^ 2 ≤ ‖κ‖ ^ 2 * |G' t| ^ 2 :=
              mul_le_mul hκ_sq hm_sq (by positivity) (by positivity)
            exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (by norm_num) (pow_pos (by linarith [hmdist_ge2]) 2)) hden
    let A₁ : ℝ := (a : ℝ) + 3 / 4
    let B₁ : ℝ := (b : ℝ) + 1 / 4
    have hAA₁ : A ≤ A₁ := by dsimp only [A, A₁]; linarith
    have hA₁B₁ : A₁ ≤ B₁ := by dsimp only [A₁, B₁]; linarith
    have hB₁B : B₁ ≤ B := by dsimp only [B₁, B]; linarith
    have hsplit_int : ∫ t in A..B, bound1 t =
        (∫ t in A..A₁, bound1 t) + (∫ t in A₁..B₁, bound1 t) + ∫ t in B₁..B, bound1 t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hb1_cont.intervalIntegrable A B₁) (hb1_cont.intervalIntegrable B₁ B),
        ← intervalIntegral.integral_add_adjacent_intervals
        (hb1_cont.intervalIntegrable A A₁) (hb1_cont.intervalIntegrable A₁ B₁)]
    have hint_mid : ∫ t in A₁..B₁, bound1 t = 0 := by
      have hz : ∀ t ∈ Set.uIcc A₁ B₁, bound1 t = 0 := fun t ht => by
        rw [Set.uIcc_of_le hA₁B₁] at ht
        dsimp only [bound1]
        rw [show χ'' t = 0 from (hχ_mid t ht).2, abs_zero, zero_div]
      rw [intervalIntegral.integral_congr hz]
      simp
    have hint_L : ∫ t in A..A₁, bound1 t ≤ (1 / 2) * (160 / (36 * mdist ^ 2)) := by
      calc ∫ t in A..A₁, bound1 t
          ≤ ∫ _t in A..A₁, (160 / (36 * mdist ^ 2) : ℝ) := by
            refine intervalIntegral.integral_mono_on hAA₁ (hb1_cont.intervalIntegrable A A₁)
              intervalIntegrable_const fun t _ => ?_
            exact div_le_div_of_nonneg_right ((vdcBump_props hab).2.2.2.2.2.2.2 t) (by positivity)
        _ = (A₁ - A) * (160 / (36 * mdist ^ 2)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ = (1 / 2) * (160 / (36 * mdist ^ 2)) := by dsimp only [A, A₁]; ring
    have hint_R : ∫ t in B₁..B, bound1 t ≤ (1 / 2) * (160 / (36 * mdist ^ 2)) := by
      calc ∫ t in B₁..B, bound1 t
          ≤ ∫ _t in B₁..B, (160 / (36 * mdist ^ 2) : ℝ) := by
            refine intervalIntegral.integral_mono_on hB₁B (hb1_cont.intervalIntegrable B₁ B)
              intervalIntegrable_const fun t _ => ?_
            exact div_le_div_of_nonneg_right ((vdcBump_props hab).2.2.2.2.2.2.2 t) (by positivity)
        _ = (B - B₁) * (160 / (36 * mdist ^ 2)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ = (1 / 2) * (160 / (36 * mdist ^ 2)) := by dsimp only [B₁, B]; ring
    calc ‖∫ t in A..B, g1 t‖ ≤ ∫ t in A..B, bound1 t := hnorm_le
      _ = (∫ t in A..A₁, bound1 t) + 0 + ∫ t in B₁..B, bound1 t := by rw [hsplit_int, hint_mid]
      _ ≤ (1 / 2) * (160 / (36 * mdist ^ 2)) + 0 + (1 / 2) * (160 / (36 * mdist ^ 2)) := by
          linarith [hint_L, hint_R]
      _ = 160 / (36 * mdist ^ 2) := by ring
      _ ≤ 5 / mdist ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg mdist]
  let recFun : ℝ → ℝ := fun t => |f'' t| / G' t ^ 2
  have hrec_cont : ContinuousOn recFun (Set.Icc A B) := by
    refine ContinuousOn.div hf''_cont.abs (hG'_cont.pow 2) fun t ht => ?_
    exact pow_ne_zero 2 (hG'_real_ne t ht)
  have hrec_int : IntervalIntegrable recFun volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hrec_cont.integrableOn_Icc
  have hrec_bd : ∫ t in A..B, recFun t ≤
      (if ⌈β⌉ + 2 ≤ n then 1 / ((n : ℝ) - β) - 1 / ((n : ℝ) - α)
      else 1 / (α - (n : ℝ)) - 1 / (β - (n : ℝ))) := by
    have hftc : ∫ t in A..B, f'' t / G' t ^ 2 = (G' A)⁻¹ - (G' B)⁻¹ := by
      have hderiv : ∀ t ∈ Set.uIcc A B, HasDerivAt (fun x => -(G' x)⁻¹) (f'' t / G' t ^ 2) t := by
        intro t ht
        rw [Set.uIcc_of_le hAB] at ht
        convert ((hG' t ht).inv (hG'_real_ne t ht)).neg using 1; simp [div_eq_mul_inv]
      have hint : IntervalIntegrable (fun t => f'' t / G' t ^ 2) volume A B := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
        exact (hf''_cont.div (hG'_cont.pow 2) fun t ht => pow_ne_zero 2 (hG'_real_ne t ht)).integrableOn_Icc
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      ring
    have habs_int : ∫ t in A..B, recFun t = |(G' A)⁻¹ - (G' B)⁻¹| := by
      rcases hmono with hpos | hneg
      · have hcongr : ∫ t in A..B, recFun t = ∫ t in A..B, f'' t / G' t ^ 2 := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le hAB] at ht
          simp only [recFun, abs_of_nonneg (hpos t ht)]
        rw [hcongr, hftc]
        have hnonneg : 0 ≤ (G' A)⁻¹ - (G' B)⁻¹ := by
          rw [← hftc]
          refine intervalIntegral.integral_nonneg hAB fun t ht => ?_
          exact div_nonneg (hpos t ht) (sq_nonneg _)
        exact (abs_of_nonneg hnonneg).symm
      · have hcongr : ∫ t in A..B, recFun t = -(∫ t in A..B, f'' t / G' t ^ 2) := by
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le hAB] at ht
          simp only [recFun, abs_of_nonpos (hneg t ht), neg_div]
        rw [hcongr, hftc]
        have hnonpos : (G' A)⁻¹ - (G' B)⁻¹ ≤ 0 := by
          rw [← hftc]
          rw [← neg_nonneg, ← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_nonneg hAB fun t ht => ?_
          exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (hneg t ht) (sq_nonneg _))
        exact (abs_of_nonpos hnonpos).symm
    rw [habs_int]
    have hA_bd := hbounds A (Set.left_mem_Icc.mpr hAB)
    have hB_bd := hbounds B (Set.right_mem_Icc.mpr hAB)
    split_ifs with hge
    · have hcl : β ≤ (⌈β⌉ : ℝ) := Int.le_ceil β
      have hnβ : 1 ≤ (n : ℝ) - β := by
        have : (⌈β⌉ : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hge
        linarith
      have hnα : (n : ℝ) - β ≤ (n : ℝ) - α := by linarith
      have hnegA : -(G' A)⁻¹ = 1 / ((n : ℝ) - f' A) := by
        rw [show G' A = -((n : ℝ) - f' A) by dsimp only [G']; ring, inv_neg, neg_neg, one_div]
      have hnegB : -(G' B)⁻¹ = 1 / ((n : ℝ) - f' B) := by
        rw [show G' B = -((n : ℝ) - f' B) by dsimp only [G']; ring, inv_neg, neg_neg, one_div]
      rw [show |(G' A)⁻¹ - (G' B)⁻¹| = |(-(G' A)⁻¹) - (-(G' B)⁻¹)| by
        rw [← abs_neg]; ring_nf, hnegA, hnegB]
      have hA_int : 1 / ((n : ℝ) - α) ≤ 1 / ((n : ℝ) - f' A) ∧
          1 / ((n : ℝ) - f' A) ≤ 1 / ((n : ℝ) - β) :=
        ⟨div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith),
          div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)⟩
      have hB_int : 1 / ((n : ℝ) - α) ≤ 1 / ((n : ℝ) - f' B) ∧
          1 / ((n : ℝ) - f' B) ≤ 1 / ((n : ℝ) - β) :=
        ⟨div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith),
          div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hle : n ≤ ⌊α⌋ - 2 := hn.resolve_right hge
      have hfl : (⌊α⌋ : ℝ) ≤ α := Int.floor_le α
      have hαn : 1 ≤ α - (n : ℝ) := by
        have : (n : ℝ) ≤ (⌊α⌋ : ℝ) - 2 := by exact_mod_cast hle
        linarith
      have hA_int : 1 / (β - (n : ℝ)) ≤ (G' A)⁻¹ ∧ (G' A)⁻¹ ≤ 1 / (α - (n : ℝ)) := by
        rw [one_div, one_div]
        exact ⟨inv_anti₀ (by linarith) (by dsimp only [G']; linarith),
          inv_anti₀ (by linarith) (by dsimp only [G']; linarith)⟩
      have hB_int : 1 / (β - (n : ℝ)) ≤ (G' B)⁻¹ ∧ (G' B)⁻¹ ≤ 1 / (α - (n : ℝ)) := by
        rw [one_div, one_div]
        exact ⟨inv_anti₀ (by linarith) (by dsimp only [G']; linarith),
          inv_anti₀ (by linarith) (by dsimp only [G']; linarith)⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hg2_bd : ‖∫ t in A..B, g2 t‖ ≤ (1 / 2) * ∫ t in A..B, recFun t := by
    calc ‖∫ t in A..B, g2 t‖ ≤ ∫ t in A..B, ‖g2 t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hAB
      _ ≤ ∫ t in A..B, (1 / 2) * recFun t := by
          refine intervalIntegral.integral_mono_on hAB hg2_int.norm (hrec_int.const_mul (1 / 2))
            fun t ht => ?_
          have hvt : ‖v t‖ = 1 := norm_vdcE (G t)
          have hg2_norm : ‖g2 t‖ = 2 * |χ' t| * |f'' t| / (‖κ‖ ^ 2 * |G' t| ^ 3) := by
            dsimp only [g2]
            rw [norm_neg, norm_mul, hvt, mul_one, norm_div, norm_mul, norm_mul,
              Complex.norm_ofNat, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
          rw [hg2_norm]
          dsimp only [recFun]
          rw [← sq_abs (G' t)]
          have hχ'4 : |χ' t| ≤ 4 := hχ'_bd t
          have hG2 : 2 ≤ |G' t| := hG'_ge2 t ht
          have hden_ge : 16 * |G' t| ^ 2 ≤ ‖κ‖ ^ 2 * |G' t| ^ 3 := by
            have h1 : 16 ≤ ‖κ‖ ^ 2 * |G' t| := by nlinarith [hκ_sq, hG2]
            calc 16 * |G' t| ^ 2 ≤ (‖κ‖ ^ 2 * |G' t|) * |G' t| ^ 2 :=
                  mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
              _ = ‖κ‖ ^ 2 * |G' t| ^ 3 := by ring
          have hnum_le : 2 * |χ' t| * |f'' t| ≤ 8 * |f'' t| := by
            have : 0 ≤ |f'' t| := abs_nonneg _
            nlinarith
          calc 2 * |χ' t| * |f'' t| / (‖κ‖ ^ 2 * |G' t| ^ 3)
              ≤ 8 * |f'' t| / (‖κ‖ ^ 2 * |G' t| ^ 3) :=
                div_le_div_of_nonneg_right hnum_le (by positivity)
            _ ≤ 8 * |f'' t| / (16 * |G' t| ^ 2) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
            _ = (1 / 2) * (|f'' t| / |G' t| ^ 2) := by ring
      _ = (1 / 2) * ∫ t in A..B, recFun t := intervalIntegral.integral_const_mul _ _
  have ht2_bd : ‖∫ t in A..B, ((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t‖ ≤
      (1 / 2) * ∫ t in A..B, recFun t := by
    let h3 : ℝ → ℂ := fun t => ((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t
    have hh3_int : IntervalIntegrable h3 volume A B := by
      have : h3 = fun t => -term2 t := by ext t; dsimp only [h3, term2]; ring
      rw [this]
      exact ht2_int.neg
    calc ‖∫ t in A..B, h3 t‖ ≤ ∫ t in A..B, ‖h3 t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hAB
      _ ≤ ∫ t in A..B, (1 / 2) * recFun t := by
          refine intervalIntegral.integral_mono_on hAB hh3_int.norm (hrec_int.const_mul (1 / 2))
            fun t ht => ?_
          have hvt : ‖v t‖ = 1 := norm_vdcE (G t)
          have hh3_norm : ‖h3 t‖ = |χ t| * |f'' t| / (‖κ‖ * |G' t| ^ 2) := by
            dsimp only [h3]
            rw [norm_mul, hvt, mul_one, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
              Real.norm_eq_abs]
          rw [hh3_norm]
          dsimp only [recFun]
          rw [← sq_abs (G' t)]
          have hχ1 : |χ t| ≤ 1 := by
            rw [abs_of_nonneg (hχ_bd t).1]; exact (hχ_bd t).2
          have hκ2 : 2 ≤ ‖κ‖ := by linarith [Real.pi_gt_three, hκ_norm]
          calc |χ t| * |f'' t| / (‖κ‖ * |G' t| ^ 2)
              ≤ 1 * |f'' t| / (‖κ‖ * |G' t| ^ 2) :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hχ1 (abs_nonneg _)) (by positivity)
            _ ≤ |f'' t| / (2 * |G' t| ^ 2) := by
                rw [one_mul]
                exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (by norm_num) (pow_pos (by linarith [hmdist_ge2, hm_le_G' t ht]) 2))
                  (mul_le_mul_of_nonneg_right hκ2 (sq_nonneg _))
            _ = (1 / 2) * (|f'' t| / |G' t| ^ 2) := by ring
      _ = (1 / 2) * ∫ t in A..B, recFun t := intervalIntegral.integral_const_mul _ _
  calc ‖∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)‖
      = ‖(∫ t in A..B, g1 t) + (∫ t in A..B, g2 t) +
          ∫ t in A..B, ((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t‖ := by
          rw [hmain_eq, hu₂'_eq]
    _ ≤ ‖(∫ t in A..B, g1 t) + (∫ t in A..B, g2 t)‖ +
          ‖∫ t in A..B, ((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t‖ := norm_add_le _ _
    _ ≤ (‖∫ t in A..B, g1 t‖ + ‖∫ t in A..B, g2 t‖) +
          ‖∫ t in A..B, ((χ t : ℂ) * (f'' t : ℂ)) / (κ * (G' t : ℂ) ^ 2) * v t‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 5 / mdist ^ 2 + ((1 / 2) * ∫ t in A..B, recFun t) + (1 / 2) * ∫ t in A..B, recFun t :=
        add_le_add (add_le_add hg1_bd hg2_bd) ht2_bd
    _ = 5 / mdist ^ 2 + ∫ t in A..B, recFun t := by ring
    _ ≤ (if ⌈β⌉ + 2 ≤ n then
          5 / ((n : ℝ) - ⌈β⌉) ^ 2 + (1 / ((n : ℝ) - β) - 1 / ((n : ℝ) - α))
        else
          5 / ((⌊α⌋ : ℝ) - n) ^ 2 + (1 / (α - (n : ℝ)) - 1 / (β - (n : ℝ)))) := by
        dsimp only [mdist]
        split_ifs with hge <;> [simp only [hge, ↓reduceIte] at hrec_bd; simp only [hge, ↓reduceIte] at hrec_bd] <;> linarith

/-- **van der Corput truncated Poisson summation formula** (B-process reduction):
for `f : ℝ → ℝ` of class `C²` on `[a + 1/4, b + 3/4]` (`a < b`) with `f''` keeping constant sign
and `α ≤ f' t ≤ β`, the exponential sum `∑_{n ∈ Ioc a b} e(f(n))` is approximated by the finite sum
of smoothed oscillatory integrals `∫_{a+1/4}^{b+3/4} vdcBump a b t * e(f(t) - n t) dt` over
`n ∈ Icc (⌊α⌋ - 1) (⌈β⌉ + 1)` with error at most `40 * (1 + Real.log (2 + (β - α)))`. -/
theorem vanDerCorput_B_poisson_reduction {a b : ℤ} (hab : a < b) {f f' f'' : ℝ → ℝ}
    {α β : ℝ} (hαβ : α ≤ β)
    (hf : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), HasDerivAt f' (f'' t) t)
    (hf''_cont : ContinuousOn f'' (Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4)))
    (hmono : (∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), 0 ≤ f'' t) ∨
      (∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), f'' t ≤ 0))
    (hbounds : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), α ≤ f' t ∧ f' t ≤ β) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I) -
      ∑ n ∈ Finset.Icc (⌊α⌋ - 1) (⌈β⌉ + 1),
        ∫ t in ((a : ℝ) + 1 / 4)..((b : ℝ) + 3 / 4),
          (vdcBump a b t : ℂ) *
            Complex.exp (2 * Real.pi * ((f t - (n : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ ≤
      40 * (1 + Real.log (2 + (β - α))) := by
  let A : ℝ := (a : ℝ) + 1 / 4
  let B : ℝ := (b : ℝ) + 3 / 4
  have hab_R : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
  have hAB : A ≤ B := by dsimp only [A, B]; linarith
  let χ := vdcBump a b
  let χ' := vdcBumpDeriv a b
  obtain ⟨hsupp, hunit, hχ_bd, hχ'_bd, _, hχ_end, hχ'_end, _⟩ := vdcBump_props hab
  let F : ℝ → ℂ := fun t => if t ∈ Set.Icc A B then (χ t : ℂ) * vdcE (f t) else 0
  let F' : ℝ → ℂ := fun t =>
    if t ∈ Set.Icc A B then
      ((χ' t : ℂ) + (χ t : ℂ) * (2 * Real.pi * Complex.I * (f' t : ℂ))) * vdcE (f t)
    else 0
  have hf'_cont : ContinuousOn f' (Set.Icc A B) := fun t ht =>
    (hf' t ht).continuousAt.continuousWithinAt
  have hf_cont : ContinuousOn f (Set.Icc A B) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hF_deriv : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    by_cases hx_in : x ∈ Set.Ioo A B
    · have hmem : Set.Ioo A B ∈ 𝓝 x := Ioo_mem_nhds hx_in.1 hx_in.2
      have hev : F =ᶠ[𝓝 x] fun t => (χ t : ℂ) * vdcE (f t) :=
        Filter.eventually_of_mem hmem fun t ht => by
          simp only [F, Set.Ioo_subset_Icc_self ht, ↓reduceIte]
      have hx_Icc : x ∈ Set.Icc A B := Set.Ioo_subset_Icc_self hx_in
      have hχd : HasDerivAt (fun t => (χ t : ℂ)) (χ' x : ℂ) x :=
        (hasDerivAt_vdcBump a b x).ofReal_comp
      have hed : HasDerivAt (fun t => vdcE (f t))
          ((2 * Real.pi * Complex.I * (f' x : ℂ)) * vdcE (f x)) x := by
        have hlin : HasDerivAt (fun t => 2 * Real.pi * (f t : ℂ) * Complex.I)
            (2 * Real.pi * Complex.I * (f' x : ℂ)) x := by
          have := ((hf x hx_Icc).ofReal_comp.const_mul (2 * (Real.pi : ℂ))).mul_const Complex.I
          convert this using 1; ring
        simpa [vdcE, mul_comm] using hlin.cexp
      have hprod := hχd.mul hed
      have hF'eq : F' x = (χ' x : ℂ) * vdcE (f x) +
          (χ x : ℂ) * ((2 * Real.pi * Complex.I * (f' x : ℂ)) * vdcE (f x)) := by
        simp only [F', hx_Icc, ↓reduceIte]; ring
      rw [hF'eq]
      exact hprod.congr_of_eventuallyEq hev
    · rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx_in
      rcases hx_in with hle | hge
      · rcases lt_or_eq_of_le hle with hlt | rfl
        · have hF'x : F' x = 0 := by simp only [F', show x ∉ Set.Icc A B from fun hmem => hlt.not_ge hmem.1, ↓reduceIte]
          have hev : F =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
            Filter.eventually_of_mem (Iio_mem_nhds hlt) fun t ht => by
              simp only [F, show t ∉ Set.Icc A B from fun hmem => (hmem.1.trans_lt ht).not_ge le_rfl, ↓reduceIte]
          rw [hF'x]
          exact (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hev
        · have hFA : F A = 0 := by
            dsimp only [F, χ, A]; rw [hχ_end.1, Complex.ofReal_zero, zero_mul, ite_self]
          have hF'A : F' A = 0 := by
            dsimp only [F', χ, χ', A]
            rw [hχ_end.1, hχ'_end.1, Complex.ofReal_zero, zero_mul, add_zero, zero_mul, ite_self]
          rw [hF'A, hasDerivAt_iff_tendsto_slope_zero]
          refine squeeze_zero_norm (a := fun t => 128 * |t|) ?_ ?_
          · intro t
            by_cases hteq : t = 0
            · simp [hteq]
            · rw [hFA, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv]
              by_cases ht_mem : A + t ∈ Set.Icc A B
              · have hFt : ‖F (A + t)‖ = |χ (A + t)| := by
                  simp only [F, ht_mem, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                    norm_vdcE, mul_one]
                rw [hFt]
                have hbd := vdcBump_end_bound_left a b (A + t)
                have hsubA : (A + t) - ((a : ℝ) + 1 / 4) = t := by dsimp only [A]; ring
                rw [hsubA, ← sq_abs t] at hbd
                calc |t|⁻¹ * |χ (A + t)| ≤ |t|⁻¹ * (128 * |t| ^ 2) :=
                      mul_le_mul_of_nonneg_left hbd (by positivity)
                  _ = 128 * |t| := by
                      have hne : |t| ≠ 0 := abs_ne_zero.mpr hteq
                      field_simp [hne]
              · simp only [F, ht_mem, ↓reduceIte, norm_zero, mul_zero]; positivity
          · have htend : Filter.Tendsto (fun t : ℝ => 128 * |t|) (𝓝 (0 : ℝ)) (𝓝 (128 * |(0 : ℝ)|)) :=
              (continuous_const.mul continuous_abs).tendsto 0
            simp only [abs_zero, mul_zero] at htend
            exact htend.mono_left nhdsWithin_le_nhds
      · rcases lt_or_eq_of_le hge with hgt | rfl
        · have hF'x : F' x = 0 := by simp only [F', show x ∉ Set.Icc A B from fun hmem => hgt.not_ge hmem.2, ↓reduceIte]
          have hev : F =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
            Filter.eventually_of_mem (Ioi_mem_nhds hgt) fun t ht => by
              simp only [F, show t ∉ Set.Icc A B from fun hmem => (ht.trans_le hmem.2).not_ge le_rfl, ↓reduceIte]
          rw [hF'x]
          exact (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hev
        · have hFB : F B = 0 := by
            dsimp only [F, χ, B]; rw [hχ_end.2, Complex.ofReal_zero, zero_mul, ite_self]
          have hF'B : F' B = 0 := by
            dsimp only [F', χ, χ', B]
            rw [hχ_end.2, hχ'_end.2, Complex.ofReal_zero, zero_mul, add_zero, zero_mul, ite_self]
          rw [hF'B, hasDerivAt_iff_tendsto_slope_zero]
          refine squeeze_zero_norm (a := fun t => 128 * |t|) ?_ ?_
          · intro t
            by_cases hteq : t = 0
            · simp [hteq]
            · rw [hFB, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv]
              by_cases ht_mem : B + t ∈ Set.Icc A B
              · have hFt : ‖F (B + t)‖ = |χ (B + t)| := by
                  simp only [F, ht_mem, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                    norm_vdcE, mul_one]
                rw [hFt]
                have hbd := vdcBump_end_bound_right a b (B + t)
                have hsubB : (B + t) - ((b : ℝ) + 3 / 4) = t := by dsimp only [B]; ring
                rw [hsubB, ← sq_abs t] at hbd
                calc |t|⁻¹ * |χ (B + t)| ≤ |t|⁻¹ * (128 * |t| ^ 2) :=
                      mul_le_mul_of_nonneg_left hbd (by positivity)
                  _ = 128 * |t| := by
                      have hne : |t| ≠ 0 := abs_ne_zero.mpr hteq
                      field_simp [hne]
              · simp only [F, ht_mem, ↓reduceIte, norm_zero, mul_zero]; positivity
          · have htend : Filter.Tendsto (fun t : ℝ => 128 * |t|) (𝓝 (0 : ℝ)) (𝓝 (128 * |(0 : ℝ)|)) :=
              (continuous_const.mul continuous_abs).tendsto 0
            simp only [abs_zero, mul_zero] at htend
            exact htend.mono_left nhdsWithin_le_nhds
  have hF'_cont : Continuous F' := by
    rw [continuous_iff_continuousAt]
    intro x
    let Mf' := max |α| |β|
    have hMf'_bd : ∀ t ∈ Set.Icc A B, |f' t| ≤ Mf' := fun t ht => by
      obtain ⟨hlo, hhi⟩ := hbounds t ht
      have hlo' : -Mf' ≤ α := by linarith [neg_le_abs α, le_max_left |α| |β|]
      exact abs_le.mpr ⟨hlo'.trans hlo, hhi.trans ((le_abs_self β).trans (le_max_right |α| |β|))⟩
    by_cases hx_in : x ∈ Set.Ioo A B
    · have hmem : Set.Ioo A B ∈ 𝓝 x := Ioo_mem_nhds hx_in.1 hx_in.2
      have hcon : ContinuousOn F' (Set.Ioo A B) := by
        have hsub : Set.Ioo A B ⊆ Set.Icc A B := Set.Ioo_subset_Icc_self
        have hev_on : ContinuousOn
            (fun t => ((χ' t : ℂ) + (χ t : ℂ) * (2 * Real.pi * Complex.I * (f' t : ℂ))) * vdcE (f t))
            (Set.Icc A B) := by
          have hc0 := (continuous_vdcBump a b).continuousOn (s := Set.Icc A B)
          have hc1 := (continuous_vdcBumpDeriv a b).continuousOn (s := Set.Icc A B)
          refine ((Complex.continuous_ofReal.comp_continuousOn hc1).add
            ((Complex.continuous_ofReal.comp_continuousOn hc0).mul
              (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hf'_cont)))).mul
            (Complex.continuous_exp.comp_continuousOn
              ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hf_cont)).mul
                continuousOn_const))
        refine (hev_on.mono hsub).congr fun t ht => ?_
        simp only [F', hsub ht, ↓reduceIte]
      exact hcon.continuousAt hmem
    · rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx_in
      rcases hx_in with hle | hge
      · rcases lt_or_eq_of_le hle with hlt | rfl
        · have hev : F' =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
            Filter.eventually_of_mem (Iio_mem_nhds hlt) fun t ht => by
              simp only [F', show t ∉ Set.Icc A B from fun hmem => (hmem.1.trans_lt ht).not_ge le_rfl, ↓reduceIte]
          exact continuousAt_const.congr hev.symm
        · have hF'A : F' A = 0 := by
            dsimp only [F', χ, χ', A]
            rw [hχ_end.1, hχ'_end.1, Complex.ofReal_zero, zero_mul, add_zero, zero_mul, ite_self]
          rw [ContinuousAt, hF'A]
          refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero
            (g := fun t => |χ' t| + |χ t| * (2 * Real.pi * Mf'))
            (fun _ => norm_nonneg _) (fun t => ?_) ?_)
          · by_cases ht : t ∈ Set.Icc A B
            · have h1 : ‖F' t‖ ≤ |χ' t| + |χ t| * (2 * Real.pi * Mf') := by
                simp only [F', ht, ↓reduceIte, norm_mul, norm_vdcE, mul_one]
                refine (norm_add_le _ _).trans ?_
                rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, norm_mul, norm_mul,
                  Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_real,
                  Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
                  Complex.norm_real, Real.norm_eq_abs]
                gcongr
                exact hMf'_bd t ht
              exact h1
            · simp only [F', ht, ↓reduceIte, norm_zero]; positivity
          · have hcont_bd : Continuous fun t => |χ' t| + |χ t| * (2 * Real.pi * Mf') :=
              (continuous_abs.comp (continuous_vdcBumpDeriv a b)).add
                ((continuous_abs.comp (continuous_vdcBump a b)).mul continuous_const)
            have htend := hcont_bd.tendsto A
            dsimp only [χ, χ', A] at htend
            rw [hχ_end.1, hχ'_end.1, abs_zero, zero_mul, add_zero] at htend
            exact htend
      · rcases lt_or_eq_of_le hge with hgt | rfl
        · have hev : F' =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
            Filter.eventually_of_mem (Ioi_mem_nhds hgt) fun t ht => by
              simp only [F', show t ∉ Set.Icc A B from fun hmem => (ht.trans_le hmem.2).not_ge le_rfl, ↓reduceIte]
          exact continuousAt_const.congr hev.symm
        · have hF'B : F' B = 0 := by
            dsimp only [F', χ, χ', B]
            rw [hχ_end.2, hχ'_end.2, Complex.ofReal_zero, zero_mul, add_zero, zero_mul, ite_self]
          rw [ContinuousAt, hF'B]
          refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero
            (g := fun t => |χ' t| + |χ t| * (2 * Real.pi * Mf'))
            (fun _ => norm_nonneg _) (fun t => ?_) ?_)
          · by_cases ht : t ∈ Set.Icc A B
            · have h1 : ‖F' t‖ ≤ |χ' t| + |χ t| * (2 * Real.pi * Mf') := by
                simp only [F', ht, ↓reduceIte, norm_mul, norm_vdcE, mul_one]
                refine (norm_add_le _ _).trans ?_
                rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, norm_mul, norm_mul,
                  Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_real,
                  Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
                  Complex.norm_real, Real.norm_eq_abs]
                gcongr
                exact hMf'_bd t ht
              exact h1
            · simp only [F', ht, ↓reduceIte, norm_zero]; positivity
          · have hcont_bd : Continuous fun t => |χ' t| + |χ t| * (2 * Real.pi * Mf') :=
              (continuous_abs.comp (continuous_vdcBumpDeriv a b)).add
                ((continuous_abs.comp (continuous_vdcBump a b)).mul continuous_const)
            have htend := hcont_bd.tendsto B
            dsimp only [χ, χ', B] at htend
            rw [hχ_end.2, hχ'_end.2, abs_zero, zero_mul, add_zero] at htend
            exact htend
  have hF_supp : ∀ t ∉ Set.Icc A B, F t = 0 := fun t ht => by simp only [F, ht, ↓reduceIte]
  have hps := poisson_summation_compactSupport_truncated_zero hAB hF_supp hF_deriv hF'_cont
  have hlhs_eq : ∑ n ∈ Finset.Icc ⌈A⌉ ⌊B⌋, F (n : ℝ) = ∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ)) := by
    rw [show Finset.Icc ⌈A⌉ ⌊B⌋ = Finset.Ioc a b from vdcBump_int_mem_Ioc hab]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Ioc] at hn
    have hn_R : (a : ℝ) + 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ (b : ℝ) := ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
    have hn_Icc : (n : ℝ) ∈ Set.Icc A B := ⟨by dsimp only [A]; linarith, by dsimp only [B]; linarith⟩
    have hn_mid : (n : ℝ) ∈ Set.Icc ((a : ℝ) + 3 / 4) ((b : ℝ) + 1 / 4) :=
      ⟨by linarith, by linarith⟩
    dsimp only [F, χ]
    simp only [hn_Icc, ↓reduceIte, hunit (n : ℝ) hn_mid, Complex.ofReal_one, one_mul]
  let I : ℤ → ℂ := fun n =>
    ∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)
  have hrhs_eq : ∀ n : ℤ,
      ∫ t in A..B, Complex.exp ((-2 * Real.pi * t * (n : ℝ) : ℝ) * Complex.I) * F t = I n := fun n => by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hAB] at ht
    simp only [F, ht, ↓reduceIte]
    have hexp : Complex.exp ((-2 * Real.pi * t * (n : ℝ) : ℝ) * Complex.I) * vdcE (f t) =
        vdcE (f t - (n : ℝ) * t) := by
      simp only [vdcE, Complex.ofReal_sub, Complex.ofReal_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [← hexp]; ring
  simp_rw [hlhs_eq, hrhs_eq] at hps
  let L : ℤ := ⌊α⌋ - 1
  let R : ℤ := ⌈β⌉ + 1
  let S : Finset ℤ := Finset.Icc L R
  have hfinite_tail : ∀ u : Finset {n : ℤ // n ∉ S},
      ∑ x ∈ u, ‖I x.1‖ ≤ 40 * (1 + Real.log (2 + (β - α))) := by
    intro u
    let uZ : Finset ℤ := u.image Subtype.val
    have hu_eq : ∑ x ∈ u, ‖I x.1‖ = ∑ n ∈ uZ, ‖I n‖ := by
      rw [Finset.sum_image]
      intro x₁ _ x₂ _ h; exact Subtype.ext h
    have huZ_disj : ∀ n ∈ uZ, n ≤ ⌊α⌋ - 2 ∨ ⌈β⌉ + 2 ≤ n := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨x, _, rfl⟩
      have hx : x.1 ∉ S := x.2
      simp only [S, L, R, Finset.mem_Icc, not_and_or, not_le] at hx
      omega
    let M₁ : ℕ := uZ.sup (fun n => Int.toNat (n - (⌈β⌉ + 1)))
    let M₂ : ℕ := uZ.sup (fun n => Int.toNat ((⌊α⌋ - 1) - n))
    let M := max M₁ M₂
    have hsub_uZ : uZ ⊆ Finset.Icc (R + 1) (R + M) ∪ Finset.Icc (L - M) (L - 1) := by
      intro n hn
      rcases huZ_disj n hn with hle | hge
      · refine Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨?_, ?_⟩)
        · have h1 : Int.toNat ((⌊α⌋ - 1) - n) ≤ M₂ := Finset.le_sup (f := fun m => Int.toNat ((⌊α⌋ - 1) - m)) hn
          have h2 : (M₂ : ℤ) ≤ (M : ℤ) := Int.ofNat_le.mpr (le_max_right _ _)
          dsimp only [L]; omega
        · dsimp only [L]; omega
      · refine Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨?_, ?_⟩)
        · dsimp only [R]; omega
        · have h1 : Int.toNat (n - (⌈β⌉ + 1)) ≤ M₁ := Finset.le_sup (f := fun m => Int.toNat (m - (⌈β⌉ + 1))) hn
          have h2 : (M₁ : ℤ) ≤ (M : ℤ) := Int.ofNat_le.mpr (le_max_left _ _)
          dsimp only [R]; omega
    let K : ℕ := Nat.ceil (β - α) + 1
    have hK : 1 ≤ K := by dsimp only [K]; omega
    have hαβ_K : β - α ≤ (K : ℝ) := by
      have h1 : β - α ≤ (Nat.ceil (β - α) : ℝ) := Nat.le_ceil _
      dsimp only [K]; push_cast; linarith
    have hsum_right : ∑ n ∈ Finset.Icc (R + 1) (R + M), ‖I n‖ ≤
        10 + (1 + Real.log (K : ℝ)) := by
      have hterm : ∑ n ∈ Finset.Icc (R + 1) (R + M), ‖I n‖ ≤
          ∑ j ∈ Finset.range M,
            (5 / (((j : ℝ) + 1) ^ 2) +
              (1 / (((⌈β⌉ : ℝ) + 2 - β) + (j : ℝ)) -
                1 / (((⌈β⌉ : ℝ) + 2 - β) + (j : ℝ) + (β - α)))) := by
        calc ∑ n ∈ Finset.Icc (R + 1) (R + M), ‖I n‖
            ≤ ∑ n ∈ Finset.Icc (R + 1) (R + M),
                (5 / ((n : ℝ) - ⌈β⌉) ^ 2 + (1 / ((n : ℝ) - β) - 1 / ((n : ℝ) - α))) := by
              refine Finset.sum_le_sum fun n hn => ?_
              simp only [Finset.mem_Icc, R] at hn
              have hge : ⌈β⌉ + 2 ≤ n := by omega
              have hbd := vdc_tail_integral_bound hab hαβ hf hf' hf''_cont hmono hbounds n (Or.inr hge)
              simp only [hge, ↓reduceIte] at hbd; exact hbd
          _ = ∑ j ∈ Finset.range M,
                (5 / (((⌈β⌉ : ℝ) + 2 + (j : ℝ) - ⌈β⌉) ^ 2) +
                  (1 / ((⌈β⌉ : ℝ) + 2 + (j : ℝ) - β) - 1 / ((⌈β⌉ : ℝ) + 2 + (j : ℝ) - α))) := by
              refine Finset.sum_bij (fun n _ => Int.toNat (n - (⌈β⌉ + 2))) ?_ ?_ ?_ ?_
              · intro n hn; simp only [Finset.mem_Icc, R] at hn; simp only [Finset.mem_range]; omega
              · intro n₁ hn₁ n₂ hn₂ heq
                simp only [Finset.mem_Icc, R] at hn₁ hn₂; omega
              · intro j hj
                simp only [Finset.mem_range] at hj
                refine ⟨⌈β⌉ + 2 + (j : ℤ), Finset.mem_Icc.mpr ⟨by dsimp only [R]; omega, by dsimp only [R]; omega⟩, by omega⟩
              · intro n hn
                simp only [Finset.mem_Icc, R] at hn
                have hcast : ((Int.toNat (n - (⌈β⌉ + 2)) : ℕ) : ℝ) = (n : ℝ) - (⌈β⌉ + 2) := by
                  have : (Int.toNat (n - (⌈β⌉ + 2)) : ℤ) = n - (⌈β⌉ + 2) := by omega
                  exact_mod_cast this
                have h5 : 5 / ((n : ℝ) - ⌈β⌉) ^ 2 =
                    5 / ((⌈β⌉ : ℝ) + 2 + ((n : ℝ) - (⌈β⌉ + 2)) - ⌈β⌉) ^ 2 := by
                  congr 1; congr 1; ring
                have h1a : 1 / ((n : ℝ) - β) =
                    1 / ((⌈β⌉ : ℝ) + 2 + ((n : ℝ) - (⌈β⌉ + 2)) - β) := by
                  congr 1; ring
                have h1b : 1 / ((n : ℝ) - α) =
                    1 / ((⌈β⌉ : ℝ) + 2 + ((n : ℝ) - (⌈β⌉ + 2)) - α) := by
                  congr 1; ring
                rw [← hcast] at h5 h1a h1b
                rw [h5, h1a, h1b]
          _ ≤ ∑ j ∈ Finset.range M,
                (5 / (((j : ℝ) + 1) ^ 2) +
                  (1 / (((⌈β⌉ : ℝ) + 2 - β) + (j : ℝ)) -
                    1 / (((⌈β⌉ : ℝ) + 2 - β) + (j : ℝ) + (β - α)))) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hsq : ((j : ℝ) + 1) ^ 2 ≤ ((⌈β⌉ : ℝ) + 2 + (j : ℝ) - ⌈β⌉) ^ 2 := by
                have heq : (⌈β⌉ : ℝ) + 2 + (j : ℝ) - ⌈β⌉ = (j : ℝ) + 2 := by ring
                rw [heq]; nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
              have hrec : 1 / ((⌈β⌉ : ℝ) + 2 + (j : ℝ) - β) - 1 / ((⌈β⌉ : ℝ) + 2 + (j : ℝ) - α) =
                  1 / (((⌈β⌉ : ℝ) + 2 - β) + (j : ℝ)) -
                    1 / (((⌈β⌉ : ℝ) + 2 - β) + (j : ℝ) + (β - α)) := by ring_nf
              rw [hrec]
              exact add_le_add (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq) le_rfl
      rw [Finset.sum_add_distrib] at hterm
      have hsq_sum : ∑ j ∈ Finset.range M, 5 / ((j : ℝ) + 1) ^ 2 ≤ 10 := by
        have : ∑ j ∈ Finset.range M, 5 / ((j : ℝ) + 1) ^ 2 =
            5 * ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        rw [this]
        linarith [vdc_sum_inv_sq_le M]
      have hR_ge1 : 1 ≤ (⌈β⌉ : ℝ) + 2 - β := by linarith [Int.le_ceil β]
      have hdiff_sum := vdc_sum_recips_diff_le ((⌈β⌉ : ℝ) + 2 - β) M K hK hR_ge1 α β hαβ hαβ_K
      linarith
    have hsum_left : ∑ n ∈ Finset.Icc (L - M) (L - 1), ‖I n‖ ≤
        10 + (1 + Real.log (K : ℝ)) := by
      have hterm : ∑ n ∈ Finset.Icc (L - M) (L - 1), ‖I n‖ ≤
          ∑ j ∈ Finset.range M,
            (5 / (((j : ℝ) + 1) ^ 2) +
              (1 / ((α - ((⌊α⌋ : ℝ) - 2)) + (j : ℝ)) -
                1 / ((α - ((⌊α⌋ : ℝ) - 2)) + (j : ℝ) + (β - α)))) := by
        calc ∑ n ∈ Finset.Icc (L - M) (L - 1), ‖I n‖
            ≤ ∑ n ∈ Finset.Icc (L - M) (L - 1),
                (5 / ((⌊α⌋ : ℝ) - n) ^ 2 + (1 / (α - (n : ℝ)) - 1 / (β - (n : ℝ)))) := by
              refine Finset.sum_le_sum fun n hn => ?_
              simp only [Finset.mem_Icc, L] at hn
              have hle : n ≤ ⌊α⌋ - 2 := by omega
              have hnot : ¬ ⌈β⌉ + 2 ≤ n := by
                have : ⌊α⌋ ≤ ⌈β⌉ := Int.floor_le_ceil α |>.trans (Int.ceil_mono hαβ)
                omega
              have hbd := vdc_tail_integral_bound hab hαβ hf hf' hf''_cont hmono hbounds n (Or.inl hle)
              simp only [hnot, ↓reduceIte] at hbd; exact hbd
          _ = ∑ j ∈ Finset.range M,
                (5 / (((⌊α⌋ : ℝ) - ((⌊α⌋ : ℝ) - 2 - (j : ℝ))) ^ 2) +
                  (1 / (α - ((⌊α⌋ : ℝ) - 2 - (j : ℝ))) - 1 / (β - ((⌊α⌋ : ℝ) - 2 - (j : ℝ))))) := by
              refine Finset.sum_bij (fun n _ => Int.toNat ((⌊α⌋ - 2) - n)) ?_ ?_ ?_ ?_
              · intro n hn; simp only [Finset.mem_Icc, L] at hn; simp only [Finset.mem_range]; omega
              · intro n₁ hn₁ n₂ hn₂ heq
                simp only [Finset.mem_Icc, L] at hn₁ hn₂; omega
              · intro j hj
                simp only [Finset.mem_range] at hj
                refine ⟨⌊α⌋ - 2 - (j : ℤ), Finset.mem_Icc.mpr ⟨by dsimp only [L]; omega, by dsimp only [L]; omega⟩, by omega⟩
              · intro n hn
                simp only [Finset.mem_Icc, L] at hn
                have hcast : ((Int.toNat ((⌊α⌋ - 2) - n) : ℕ) : ℝ) = ((⌊α⌋ : ℝ) - 2) - (n : ℝ) := by
                  have : (Int.toNat ((⌊α⌋ - 2) - n) : ℤ) = (⌊α⌋ - 2) - n := by omega
                  exact_mod_cast this
                have h5 : 5 / ((⌊α⌋ : ℝ) - n) ^ 2 =
                    5 / ((⌊α⌋ : ℝ) - ((⌊α⌋ : ℝ) - 2 - ((⌊α⌋ : ℝ) - 2 - n))) ^ 2 := by
                  congr 1; congr 1; ring
                have h1a : 1 / (α - (n : ℝ)) =
                    1 / (α - ((⌊α⌋ : ℝ) - 2 - ((⌊α⌋ : ℝ) - 2 - n))) := by
                  congr 1; ring
                have h1b : 1 / (β - (n : ℝ)) =
                    1 / (β - ((⌊α⌋ : ℝ) - 2 - ((⌊α⌋ : ℝ) - 2 - n))) := by
                  congr 1; ring
                rw [← hcast] at h5 h1a h1b
                rw [h5, h1a, h1b]
          _ ≤ ∑ j ∈ Finset.range M,
                (5 / (((j : ℝ) + 1) ^ 2) +
                  (1 / ((α - ((⌊α⌋ : ℝ) - 2)) + (j : ℝ)) -
                    1 / ((α - ((⌊α⌋ : ℝ) - 2)) + (j : ℝ) + (β - α)))) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hsq : ((j : ℝ) + 1) ^ 2 ≤ ((⌊α⌋ : ℝ) - ((⌊α⌋ : ℝ) - 2 - (j : ℝ))) ^ 2 := by
                have heq : (⌊α⌋ : ℝ) - ((⌊α⌋ : ℝ) - 2 - (j : ℝ)) = (j : ℝ) + 2 := by ring
                rw [heq]; nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
              have hrec : 1 / (α - ((⌊α⌋ : ℝ) - 2 - (j : ℝ))) - 1 / (β - ((⌊α⌋ : ℝ) - 2 - (j : ℝ))) =
                  1 / ((α - ((⌊α⌋ : ℝ) - 2)) + (j : ℝ)) -
                    1 / ((α - ((⌊α⌋ : ℝ) - 2)) + (j : ℝ) + (β - α)) := by ring_nf
              rw [hrec]
              exact add_le_add (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq) le_rfl
      rw [Finset.sum_add_distrib] at hterm
      have hsq_sum : ∑ j ∈ Finset.range M, 5 / ((j : ℝ) + 1) ^ 2 ≤ 10 := by
        have : ∑ j ∈ Finset.range M, 5 / ((j : ℝ) + 1) ^ 2 =
            5 * ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        rw [this]
        linarith [vdc_sum_inv_sq_le M]
      have hR_ge1 : 1 ≤ α - ((⌊α⌋ : ℝ) - 2) := by linarith [Int.floor_le α]
      have hdiff_sum := vdc_sum_recips_diff_le (α - ((⌊α⌋ : ℝ) - 2)) M K hK hR_ge1 α β hαβ hαβ_K
      linarith
    have hlogK_le : Real.log (K : ℝ) ≤ Real.log (2 + (β - α)) := by
      refine Real.log_le_log (by positivity) ?_
      have hceil_lt : (Nat.ceil (β - α) : ℝ) < (β - α) + 1 := Nat.ceil_lt_add_one (by linarith)
      dsimp only [K]
      push_cast
      linarith
    have hlog_nonneg : 0 ≤ Real.log (2 + (β - α)) := Real.log_nonneg (by linarith)
    calc ∑ x ∈ u, ‖I x.1‖ = ∑ n ∈ uZ, ‖I n‖ := hu_eq
      _ ≤ ∑ n ∈ Finset.Icc (R + 1) (R + M) ∪ Finset.Icc (L - M) (L - 1), ‖I n‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_uZ (fun _ _ _ => norm_nonneg _)
      _ ≤ (∑ n ∈ Finset.Icc (R + 1) (R + M), ‖I n‖) +
            ∑ n ∈ Finset.Icc (L - M) (L - 1), ‖I n‖ := by
          have hui := Finset.sum_union_inter (s₁ := Finset.Icc (R + 1) (R + M))
            (s₂ := Finset.Icc (L - M) (L - 1)) (f := fun n => ‖I n‖)
          have hnn : 0 ≤ ∑ n ∈ Finset.Icc (R + 1) (R + M) ∩ Finset.Icc (L - M) (L - 1), ‖I n‖ :=
            Finset.sum_nonneg fun _ _ => norm_nonneg _
          linarith
      _ ≤ 22 + 2 * Real.log (K : ℝ) := by linarith [hsum_right, hsum_left]
      _ ≤ 40 * (1 + Real.log (2 + (β - α))) := by linarith
  have hsumm_compl_norm : Summable (fun x : {n : ℤ // n ∉ S} => ‖I x.1‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfinite_tail
  have htsum_compl_norm : ∑' x : {n : ℤ // n ∉ S}, ‖I x.1‖ ≤ 40 * (1 + Real.log (2 + (β - α))) :=
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hfinite_tail
  have hsumm_compl : Summable (fun x : {n : ℤ // n ∉ S} => I x.1) :=
    hsumm_compl_norm.of_norm
  have hsumm_S : Summable (fun x : {n : ℤ // n ∈ S} => I x.1) :=
    (S.finite_toSet).summable (f := I)
  have hsplit_tsum : ∑' n : ℤ, I n =
      (∑ n ∈ S, I n) + ∑' x : {n : ℤ // n ∉ S}, I x.1 := by
    have h1 := (Summable.tsum_add_tsum_compl (s := (S : Set ℤ)) (f := I) hsumm_S hsumm_compl).symm
    have h2 : ∑' x : {n : ℤ // n ∈ S}, I x.1 = ∑ n ∈ S, I n := Finset.tsum_subtype S I
    rw [← h2]
    exact h1
  have hdiff_eq : ∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ)) - ∑ n ∈ S, I n =
      ∑' x : {n : ℤ // n ∉ S}, I x.1 := by
    rw [hps, hsplit_tsum]
    ring
  change ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ)) - ∑ n ∈ S, I n‖ ≤ _
  rw [hdiff_eq]
  exact (norm_tsum_le_tsum_norm hsumm_compl_norm).trans htsum_compl_norm

/-- **van der Corput second derivative test via truncated Poisson summation** (B-process):
for `f : ℝ → ℝ` of class `C²` on `[a + 1/4, b + 3/4]` (`a < b`) with `0 < λ₂ ≤ 1`, `1 ≤ c`, and
`λ₂ ≤ |f'' t| ≤ c * λ₂` keeping constant sign,
`‖∑_{n ∈ Ioc a b} e(f(n))‖ ≤ 400 * c * ((b - a) * λ₂^(1/2) + λ₂^(-1/2))`. -/
theorem vanDerCorput_B_second_deriv_from_poisson {a b : ℤ} (hab : a < b) {f f' f'' : ℝ → ℝ}
    {lam₂ c : ℝ} (hlam_pos : 0 < lam₂) (hlam_le : lam₂ ≤ 1) (hc : 1 ≤ c)
    (hf : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), HasDerivAt f' (f'' t) t)
    (hf''_cont : ContinuousOn f'' (Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4)))
    (hbound : (∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), lam₂ ≤ f'' t ∧ f'' t ≤ c * lam₂) ∨
      (∀ t ∈ Set.Icc ((a : ℝ) + 1 / 4) ((b : ℝ) + 3 / 4), -(c * lam₂) ≤ f'' t ∧ f'' t ≤ -lam₂)) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      400 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-1 / 2 : ℝ)) := by
  let A : ℝ := (a : ℝ) + 1 / 4
  let B : ℝ := (b : ℝ) + 3 / 4
  let A₁ : ℝ := (a : ℝ) + 3 / 4
  let B₁ : ℝ := (b : ℝ) + 1 / 4
  have hab_R : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
  have hAA₁ : A ≤ A₁ := by dsimp only [A, A₁]; linarith
  have hA₁B₁ : A₁ ≤ B₁ := by dsimp only [A₁, B₁]; linarith
  have hB₁B : B₁ ≤ B := by dsimp only [B₁, B]; linarith
  have hAB : A ≤ B := hAA₁.trans (hA₁B₁.trans hB₁B)
  have hf'_cont : ContinuousOn f' (Set.Icc A B) := fun t ht =>
    (hf' t ht).continuousAt.continuousWithinAt
  have hmono : (∀ t ∈ Set.Icc A B, 0 ≤ f'' t) ∨ (∀ t ∈ Set.Icc A B, f'' t ≤ 0) := by
    rcases hbound with hp | hn
    · exact Or.inl fun t ht => hlam_pos.le.trans (hp t ht).1
    · exact Or.inr fun t ht => (hn t ht).2.trans (neg_nonpos.mpr hlam_pos.le)
  have habs_f'' : ∀ t ∈ Set.Icc A B, |f'' t| ≤ c * lam₂ := fun t ht => by
    rcases hbound with hp | hn
    · rw [abs_of_nonneg (hlam_pos.le.trans (hp t ht).1)]; exact (hp t ht).2
    · rw [abs_of_nonpos ((hn t ht).2.trans (neg_nonpos.mpr hlam_pos.le))]; linarith [(hn t ht).1]
  have hmvt : ∀ x y : ℝ, A ≤ x → x ≤ y → y ≤ B → |f' y - f' x| ≤ c * lam₂ * (y - x) := by
    intro x y hx hxy hy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f' f'' hlt
      (hf'_cont.mono (Set.Icc_subset_Icc hx hy))
      (fun t ht => hf' t ⟨hx.trans ht.1.le, ht.2.le.trans hy⟩)
    have hbd : |f'' ξ| ≤ c * lam₂ := habs_f'' ξ ⟨hx.trans hξ.1.le, hξ.2.le.trans hy⟩
    have hmul : |f' y - f' x| = |f'' ξ| * (y - x) := by
      rw [hEq, abs_div, abs_of_pos (sub_pos.mpr hlt), div_mul_cancel₀ _ (sub_pos.mpr hlt).ne']
    rw [hmul]
    exact mul_le_mul_of_nonneg_right hbd (sub_pos.mpr hlt).le
  let α := min (f' A) (f' B)
  let β := max (f' A) (f' B)
  have hαβ : α ≤ β := (min_le_left _ _).trans (le_max_left _ _)
  have hbounds : ∀ t ∈ Set.Icc A B, α ≤ f' t ∧ f' t ≤ β := fun t ht => by
    rcases hmono with hp | hn
    · have h1 : f' A ≤ f' t := by
        rcases eq_or_lt_of_le ht.1 with rfl | hlt
        · exact le_rfl
        obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f' f'' hlt
          (hf'_cont.mono (Set.Icc_subset_Icc_right ht.2))
          (fun s hs => hf' s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
        have hnn := (div_nonneg_iff.mp (hEq ▸ hp ξ ⟨hξ.1.le, hξ.2.le.trans ht.2⟩))
        have hsub := mul_nonneg (hp ξ ⟨hξ.1.le, hξ.2.le.trans ht.2⟩) (sub_pos.mpr hlt).le
        rw [hEq, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne'] at hsub
        linarith
      have h2 : f' t ≤ f' B := by
        rcases eq_or_lt_of_le ht.2 with rfl | hlt
        · exact le_rfl
        obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f' f'' hlt
          (hf'_cont.mono (Set.Icc_subset_Icc_left ht.1))
          (fun s hs => hf' s ⟨ht.1.trans hs.1.le, hs.2.le⟩)
        have hsub := mul_nonneg (hp ξ ⟨ht.1.trans hξ.1.le, hξ.2.le⟩) (sub_pos.mpr hlt).le
        rw [hEq, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne'] at hsub
        linarith
      exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩
    · have h1 : f' t ≤ f' A := by
        rcases eq_or_lt_of_le ht.1 with rfl | hlt
        · exact le_rfl
        obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f' f'' hlt
          (hf'_cont.mono (Set.Icc_subset_Icc_right ht.2))
          (fun s hs => hf' s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
        have hsub := mul_nonpos_of_nonpos_of_nonneg (hn ξ ⟨hξ.1.le, hξ.2.le.trans ht.2⟩)
          (sub_pos.mpr hlt).le
        rw [hEq, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne'] at hsub
        linarith
      have h2 : f' B ≤ f' t := by
        rcases eq_or_lt_of_le ht.2 with rfl | hlt
        · exact le_rfl
        obtain ⟨ξ, hξ, hEq⟩ := exists_hasDerivAt_eq_slope f' f'' hlt
          (hf'_cont.mono (Set.Icc_subset_Icc_left ht.1))
          (fun s hs => hf' s ⟨ht.1.trans hs.1.le, hs.2.le⟩)
        have hsub := mul_nonpos_of_nonpos_of_nonneg (hn ξ ⟨ht.1.trans hξ.1.le, hξ.2.le⟩)
          (sub_pos.mpr hlt).le
        rw [hEq, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne'] at hsub
        linarith
      exact ⟨(min_le_right _ _).trans h2, h1.trans (le_max_left _ _)⟩
  have hβα_le : β - α ≤ c * lam₂ * ((b : ℝ) - a + 1 / 2) := by
    have hdiff : β - α = |f' B - f' A| := by
      dsimp only [α, β]
      rcases le_total (f' A) (f' B) with h | h
      · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
      · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    rw [hdiff]
    have hAB' := hmvt A B le_rfl hAB le_rfl
    rwa [show B - A = (b : ℝ) - a + 1 / 2 by dsimp only [A, B]; ring] at hAB'
  have hpois := vanDerCorput_B_poisson_reduction hab hαβ hf hf' hf''_cont hmono hbounds
  let χ := vdcBump a b
  obtain ⟨_, hunit, hχ_bd, _, _, _, _, _⟩ := vdcBump_props hab
  have hinv_sqrt : lam₂ ^ (-1 / 2 : ℝ) = (Real.sqrt lam₂)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hlam_pos.le,
      ← Real.sqrt_eq_rpow]
  have hsqrt_le1 : Real.sqrt lam₂ ≤ 1 := Real.sqrt_le_one.mpr hlam_le
  have h1_le_inv : 1 ≤ lam₂ ^ (-1 / 2 : ℝ) := by
    rw [hinv_sqrt]
    exact one_le_inv_iff₀.mpr ⟨Real.sqrt_pos.mpr hlam_pos, hsqrt_le1⟩
  have hterm_bd : ∀ n : ℤ,
      ‖∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)‖ ≤ 9 * lam₂ ^ (-1 / 2 : ℝ) := by
    intro n
    let integrand : ℝ → ℂ := fun t => (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)
    have hf_cont : ContinuousOn f (Set.Icc A B) := fun t ht =>
      (hf t ht).continuousAt.continuousWithinAt
    have hint_cont : ContinuousOn integrand (Set.Icc A B) := by
      have hc0 := (continuous_vdcBump a b).continuousOn (s := Set.Icc A B)
      refine (Complex.continuous_ofReal.comp_continuousOn hc0).mul
        (Complex.continuous_exp.comp_continuousOn ?_)
      have hg : ContinuousOn (fun t => f t - (n : ℝ) * t) (Set.Icc A B) :=
        hf_cont.sub (continuousOn_const.mul continuousOn_id)
      exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hg)).mul
        continuousOn_const
    have hint_AA₁ : IntervalIntegrable integrand volume A A₁ :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hAA₁).mpr
        (hint_cont.mono (Set.Icc_subset_Icc_right (hA₁B₁.trans hB₁B))).integrableOn_Icc
    have hint_A₁B₁ : IntervalIntegrable integrand volume A₁ B₁ :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hA₁B₁).mpr
        (hint_cont.mono (Set.Icc_subset_Icc hAA₁ hB₁B)).integrableOn_Icc
    have hint_B₁B : IntervalIntegrable integrand volume B₁ B :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hB₁B).mpr
        (hint_cont.mono (Set.Icc_subset_Icc_left (hAA₁.trans hA₁B₁))).integrableOn_Icc
    have hsplit_n : ∫ t in A..B, integrand t =
        (∫ t in A..A₁, integrand t) + (∫ t in A₁..B₁, integrand t) + ∫ t in B₁..B, integrand t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint_AA₁.trans hint_A₁B₁) hint_B₁B,
        ← intervalIntegral.integral_add_adjacent_intervals hint_AA₁ hint_A₁B₁]
    have hnorm1 : ∀ t ∈ Set.Icc A B, ‖integrand t‖ ≤ 1 := fun t _ => by
      dsimp only [integrand]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_vdcE, mul_one,
        abs_of_nonneg (hχ_bd t).1]
      exact (hχ_bd t).2
    have hL_bd : ‖∫ t in A..A₁, integrand t‖ ≤ 1 / 2 := by
      calc ‖∫ t in A..A₁, integrand t‖ ≤ ∫ t in A..A₁, ‖integrand t‖ :=
            intervalIntegral.norm_integral_le_integral_norm hAA₁
        _ ≤ ∫ _t in A..A₁, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hAA₁ hint_AA₁.norm intervalIntegrable_const
              fun t ht => hnorm1 t ⟨ht.1, ht.2.trans (hA₁B₁.trans hB₁B)⟩
        _ = 1 / 2 := by simp [A, A₁]; ring
    have hR_bd : ‖∫ t in B₁..B, integrand t‖ ≤ 1 / 2 := by
      calc ‖∫ t in B₁..B, integrand t‖ ≤ ∫ t in B₁..B, ‖integrand t‖ :=
            intervalIntegral.norm_integral_le_integral_norm hB₁B
        _ ≤ ∫ _t in B₁..B, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hB₁B hint_B₁B.norm intervalIntegrable_const
              fun t ht => hnorm1 t ⟨(hAA₁.trans hA₁B₁).trans ht.1, ht.2⟩
        _ = 1 / 2 := by simp [B₁, B]; ring
    have hMid_bd : ‖∫ t in A₁..B₁, integrand t‖ ≤ 8 * lam₂ ^ (-1 / 2 : ℝ) := by
      have hcongr : ∫ t in A₁..B₁, integrand t =
          ∫ t in A₁..B₁, Complex.exp (((2 * Real.pi * (f t - (n : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hA₁B₁] at ht
        dsimp only [integrand]
        rw [show χ t = 1 from hunit t ht, Complex.ofReal_one, one_mul]
        dsimp only [vdcE]; congr 1; push_cast; ring
      rw [hcongr]
      let F : ℝ → ℝ := fun t => 2 * Real.pi * (f t - (n : ℝ) * t)
      let F' : ℝ → ℝ := fun t => 2 * Real.pi * (f' t - (n : ℝ))
      let F'' : ℝ → ℝ := fun t => 2 * Real.pi * f'' t
      have hsub_mid : Set.Icc A₁ B₁ ⊆ Set.Icc A B := Set.Icc_subset_Icc hAA₁ hB₁B
      have hF : ∀ t ∈ Set.Icc A₁ B₁, HasDerivAt F (F' t) t := fun t ht => by
        have hn_d : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) t :=
          ((hasDerivAt_id t).const_mul (n : ℝ)).congr_deriv (mul_one _)
        exact (((hf t (hsub_mid ht)).sub hn_d).const_mul (2 * Real.pi))
      have hF' : ∀ t ∈ Set.Icc A₁ B₁, HasDerivAt F' (F'' t) t := fun t ht =>
        ((hf' t (hsub_mid ht)).sub_const (n : ℝ)).const_mul (2 * Real.pi)
      have hF''_cont : ContinuousOn F'' (Set.Icc A₁ B₁) :=
        continuousOn_const.mul (hf''_cont.mono hsub_mid)
      have hsign : (∀ t ∈ Set.Icc A₁ B₁, 2 * Real.pi * lam₂ ≤ F'' t) ∨
          (∀ t ∈ Set.Icc A₁ B₁, F'' t ≤ -(2 * Real.pi * lam₂)) := by
        rcases hbound with hp | hn
        · exact Or.inl fun t ht => mul_le_mul_of_nonneg_left (hp t (hsub_mid ht)).1 (by positivity)
        · exact Or.inr fun t ht => by
            have := mul_le_mul_of_nonneg_left (hn t (hsub_mid ht)).2 (by positivity : 0 ≤ 2 * Real.pi)
            dsimp only [F'']; linarith
      have habs_lb : ∀ t ∈ Set.Icc A₁ B₁, 2 * Real.pi * lam₂ ≤ |F'' t| := fun t ht => by
        rcases hsign with hp | hn
        · exact (hp t ht).trans (le_abs_self _)
        · exact (by linarith [hn t ht] : 2 * Real.pi * lam₂ ≤ -F'' t).trans (neg_le_abs _)
      have hvdc := vanDerCorput_integral_second_deriv hA₁B₁ (by positivity : 0 < 2 * Real.pi * lam₂)
        hF hF' hF''_cont habs_lb
      have hsq_ge : Real.sqrt lam₂ ≤ Real.sqrt (2 * Real.pi * lam₂) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi, hlam_pos])
      calc ‖∫ t in A₁..B₁, Complex.exp ((F t : ℂ) * Complex.I)‖
          ≤ 8 / Real.sqrt (2 * Real.pi * lam₂) := hvdc
        _ ≤ 8 / Real.sqrt lam₂ :=
            div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hlam_pos) hsq_ge
        _ = 8 * lam₂ ^ (-1 / 2 : ℝ) := by rw [div_eq_mul_inv, hinv_sqrt]
    calc ‖∫ t in A..B, integrand t‖
        = ‖(∫ t in A..A₁, integrand t) + (∫ t in A₁..B₁, integrand t) + ∫ t in B₁..B, integrand t‖ := by
          rw [hsplit_n]
      _ ≤ ‖(∫ t in A..A₁, integrand t) + (∫ t in A₁..B₁, integrand t)‖ +
            ‖∫ t in B₁..B, integrand t‖ := norm_add_le _ _
      _ ≤ (‖∫ t in A..A₁, integrand t‖ + ‖∫ t in A₁..B₁, integrand t‖) +
            ‖∫ t in B₁..B, integrand t‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ 1 / 2 + 8 * lam₂ ^ (-1 / 2 : ℝ) + 1 / 2 := by linarith
      _ ≤ 9 * lam₂ ^ (-1 / 2 : ℝ) := by linarith [h1_le_inv]
  let S := Finset.Icc (⌊α⌋ - 1) (⌈β⌉ + 1)
  have hS_card : (S.card : ℝ) ≤ c * lam₂ * ((b : ℝ) - a + 1 / 2) + 5 := by
    have hcardZ : (S.card : ℝ) = ((Int.toNat (⌈β⌉ + 1 + 1 - (⌊α⌋ - 1)) : ℕ) : ℝ) := by
      dsimp only [S]; rw [Int.card_Icc]
    have hle_diff : (S.card : ℝ) ≤ max 0 ((⌈β⌉ : ℝ) - ⌊α⌋ + 3) := by
      rw [hcardZ]
      rcases le_total 0 (⌈β⌉ + 1 + 1 - (⌊α⌋ - 1)) with hpos | hneg
      · have heq : ((Int.toNat (⌈β⌉ + 1 + 1 - (⌊α⌋ - 1)) : ℕ) : ℝ) = (⌈β⌉ : ℝ) - ⌊α⌋ + 3 := by
          have hInt : (Int.toNat (⌈β⌉ + 1 + 1 - (⌊α⌋ - 1)) : ℤ) = ⌈β⌉ + 1 + 1 - (⌊α⌋ - 1) := by omega
          have hR : ((Int.toNat (⌈β⌉ + 1 + 1 - (⌊α⌋ - 1)) : ℕ) : ℝ) =
              ((⌈β⌉ + 1 + 1 - (⌊α⌋ - 1) : ℤ) : ℝ) := by exact_mod_cast hInt
          rw [hR]; push_cast; ring
        rw [heq]; exact le_max_right _ _
      · have h0 : Int.toNat (⌈β⌉ + 1 + 1 - (⌊α⌋ - 1)) = 0 := by omega
        rw [h0]; simp
    have hcl : (⌈β⌉ : ℝ) < β + 1 := Int.ceil_lt_add_one β
    have hfl : α - 1 < (⌊α⌋ : ℝ) := Int.sub_one_lt_floor α
    have hpos_rhs : 0 ≤ β - α + 5 := by linarith
    have hmax_le : max 0 ((⌈β⌉ : ℝ) - ⌊α⌋ + 3) ≤ β - α + 5 :=
      max_le hpos_rhs (by linarith)
    exact hle_diff.trans (hmax_le.trans (by linarith))
  have hmain_sum :
      ‖∑ n ∈ S, ∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)‖ ≤
        (S.card : ℝ) * (9 * lam₂ ^ (-1 / 2 : ℝ)) := by
    calc ‖∑ n ∈ S, ∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)‖
        ≤ ∑ n ∈ S, ‖∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ S, (9 * lam₂ ^ (-1 / 2 : ℝ)) := Finset.sum_le_sum fun n _ => hterm_bd n
      _ = (S.card : ℝ) * (9 * lam₂ ^ (-1 / 2 : ℝ)) := by simp
  have hba1 : (1 : ℝ) ≤ (b : ℝ) - a := by linarith
  have hlam_mul_inv : lam₂ * lam₂ ^ (-1 / 2 : ℝ) = lam₂ ^ (1 / 2 : ℝ) := by
    conv_lhs => (lhs; rw [← Real.rpow_one lam₂])
    rw [← Real.rpow_add hlam_pos]
    norm_num
  have hS_term : (S.card : ℝ) * (9 * lam₂ ^ (-1 / 2 : ℝ)) ≤
      60 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-1 / 2 : ℝ)) := by
    have hlam_half_le1 : lam₂ ^ (1 / 2 : ℝ) ≤ 1 := by
      rw [← Real.sqrt_eq_rpow]; exact hsqrt_le1
    calc (S.card : ℝ) * (9 * lam₂ ^ (-1 / 2 : ℝ))
        ≤ (c * lam₂ * ((b : ℝ) - a + 1 / 2) + 5) * (9 * lam₂ ^ (-1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hS_card (by positivity)
      _ = 9 * c * ((b : ℝ) - a) * (lam₂ * lam₂ ^ (-1 / 2 : ℝ)) +
            (9 / 2) * c * (lam₂ * lam₂ ^ (-1 / 2 : ℝ)) + 45 * lam₂ ^ (-1 / 2 : ℝ) := by ring
      _ = 9 * c * ((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) +
            (9 / 2) * c * lam₂ ^ (1 / 2 : ℝ) + 45 * lam₂ ^ (-1 / 2 : ℝ) := by rw [hlam_mul_inv]
      _ ≤ 9 * c * ((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) +
            (9 / 2) * c * lam₂ ^ (-1 / 2 : ℝ) + 45 * c * lam₂ ^ (-1 / 2 : ℝ) := by
          have h45 : 45 * lam₂ ^ (-1 / 2 : ℝ) ≤ 45 * c * lam₂ ^ (-1 / 2 : ℝ) := by
            nlinarith [show 0 ≤ lam₂ ^ (-1 / 2 : ℝ) by positivity]
          have h92 : (9 / 2) * c * lam₂ ^ (1 / 2 : ℝ) ≤ (9 / 2) * c * lam₂ ^ (-1 / 2 : ℝ) := by
            have : lam₂ ^ (1 / 2 : ℝ) ≤ lam₂ ^ (-1 / 2 : ℝ) := hlam_half_le1.trans h1_le_inv
            have h0 : 0 ≤ (9 / 2 : ℝ) * c := by positivity
            exact mul_le_mul_of_nonneg_left this h0
          linarith
      _ ≤ 60 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-1 / 2 : ℝ)) := by
          have hc0 : 0 ≤ c := by positivity
          have ht1 : 0 ≤ ((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) := by positivity
          have ht2 : 0 ≤ lam₂ ^ (-1 / 2 : ℝ) := by positivity
          nlinarith
  have hlog_bd : 40 * (1 + Real.log (2 + (β - α))) ≤
      340 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-1 / 2 : ℝ)) := by
    let u := 2 + (β - α)
    have hu2 : 2 ≤ u := by dsimp only [u]; linarith
    have hu_pos : 0 < u := by linarith
    have hlog_sqrt : Real.log u ≤ 2 * Real.sqrt u := by
      have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu_pos)
      have h2 : Real.log u = 2 * Real.log (Real.sqrt u) := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow hu_pos]; ring
      linarith only [h1, h2]
    have hu_le : u ≤ 2 + c * lam₂ * ((b : ℝ) - a + 1 / 2) := by
      dsimp only [u]; linarith only [hβα_le]
    have hu_le2 : u ≤ 4 + 2 * c * ((b : ℝ) - a) * lam₂ := by
      have hle2 : (b : ℝ) - a + 1 / 2 ≤ 2 * ((b : ℝ) - a) := by linarith only [hba1]
      have hmul := mul_le_mul_of_nonneg_left hle2 (mul_nonneg (by linarith only [hc] : 0 ≤ c) hlam_pos.le)
      have hclam : c * lam₂ * (2 * ((b : ℝ) - a)) = 2 * c * ((b : ℝ) - a) * lam₂ := by ring
      linarith only [hu_le, hmul, hclam]
    have hsqrt_u : Real.sqrt u ≤ 2 + 2 * c * ((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) := by
      have hsq : Real.sqrt u ≤ Real.sqrt (4 + 2 * c * ((b : ℝ) - a) * lam₂) :=
        Real.sqrt_le_sqrt hu_le2
      have hclam_nn : 0 ≤ 2 * c * ((b : ℝ) - a) * lam₂ :=
        mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (by linarith only [hc] : 0 ≤ c))
          (by linarith only [hba1] : 0 ≤ (b : ℝ) - a)) hlam_pos.le
      have hadd_sqrt : Real.sqrt (4 + 2 * c * ((b : ℝ) - a) * lam₂) ≤
          Real.sqrt 4 + Real.sqrt (2 * c * ((b : ℝ) - a) * lam₂) := by
        rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg 4) (Real.sqrt_nonneg _))]
        refine Real.sqrt_le_sqrt ?_
        have hsq4 : Real.sqrt 4 ^ 2 = 4 := Real.sq_sqrt zero_le_four
        have hsq2 : Real.sqrt (2 * c * ((b : ℝ) - a) * lam₂) ^ 2 = 2 * c * ((b : ℝ) - a) * lam₂ :=
          Real.sq_sqrt hclam_nn
        have hcross : 0 ≤ 2 * Real.sqrt 4 * Real.sqrt (2 * c * ((b : ℝ) - a) * lam₂) :=
          mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg 4)) (Real.sqrt_nonneg _)
        have hexp_sq : (Real.sqrt 4 + Real.sqrt (2 * c * ((b : ℝ) - a) * lam₂)) ^ 2 =
            Real.sqrt 4 ^ 2 + Real.sqrt (2 * c * ((b : ℝ) - a) * lam₂) ^ 2 +
              2 * Real.sqrt 4 * Real.sqrt (2 * c * ((b : ℝ) - a) * lam₂) := by ring
        linarith only [hsq4, hsq2, hcross, hexp_sq]
      have h4eq : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
      have hca_nn : 0 ≤ 2 * c * ((b : ℝ) - a) :=
        mul_nonneg (mul_nonneg zero_le_two (by linarith only [hc] : 0 ≤ c))
          (by linarith only [hba1] : 0 ≤ (b : ℝ) - a)
      have hterm2_sqrt : Real.sqrt (2 * c * ((b : ℝ) - a) * lam₂) ≤
          2 * c * ((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul hca_nn, ← Real.sqrt_eq_rpow]
        have hle_sq : Real.sqrt (2 * c * ((b : ℝ) - a)) ≤ 2 * c * ((b : ℝ) - a) := by
          have h1 : 1 ≤ 2 * c * ((b : ℝ) - a) := by
            have hprod : 1 ≤ c * ((b : ℝ) - a) := one_le_mul_of_one_le_of_one_le hc hba1
            linarith only [hprod]
          have hsq' : Real.sqrt (2 * c * ((b : ℝ) - a)) ^ 2 ≤ (2 * c * ((b : ℝ) - a)) ^ 2 := by
            rw [Real.sq_sqrt hca_nn]
            have hsq_ge : 2 * c * ((b : ℝ) - a) ≤ (2 * c * ((b : ℝ) - a)) ^ 2 := by
              simpa [sq, one_mul] using mul_le_mul_of_nonneg_right h1 hca_nn
            exact hsq_ge
          exact le_of_pow_le_pow_left₀ (by norm_num) hca_nn hsq'
        exact mul_le_mul_of_nonneg_right hle_sq (Real.sqrt_nonneg _)
      linarith only [hsq, hadd_sqrt, h4eq, hterm2_sqrt]
    have hlog_bound : 40 * (1 + Real.log u) ≤
        200 + 160 * c * ((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) := by
      linarith only [hlog_sqrt, hsqrt_u]
    have h200 : 200 ≤ 340 * c * lam₂ ^ (-1 / 2 : ℝ) := by
      have hprod : 1 ≤ c * lam₂ ^ (-1 / 2 : ℝ) := one_le_mul_of_one_le_of_one_le hc h1_le_inv
      linarith only [hprod]
    have hpos1 : 0 ≤ ((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) :=
      mul_nonneg (by linarith only [hba1] : 0 ≤ (b : ℝ) - a) (Real.rpow_nonneg hlam_pos.le _)
    have h160_340 : 160 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ)) ≤
        340 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hc] : 160 * c ≤ 340 * c) hpos1
    linarith only [hlog_bound, h200, h160_340]
  have htri : ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ))‖ ≤
      ‖∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ)) -
        ∑ n ∈ S, ∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)‖ +
      ‖∑ n ∈ S, ∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t)‖ := by
    simpa [sub_add_cancel] using norm_add_le
      (∑ n ∈ Finset.Ioc a b, vdcE (f (n : ℝ)) -
        ∑ n ∈ S, ∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t))
      (∑ n ∈ S, ∫ t in A..B, (χ t : ℂ) * vdcE (f t - (n : ℝ) * t))
  calc ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖
      ≤ 40 * (1 + Real.log (2 + (β - α))) + (S.card : ℝ) * (9 * lam₂ ^ (-1 / 2 : ℝ)) := by
        exact htri.trans (add_le_add hpois hmain_sum)
    _ ≤ 340 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-1 / 2 : ℝ)) +
          60 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-1 / 2 : ℝ)) :=
        add_le_add hlog_bd hS_term
    _ = 400 * c * (((b : ℝ) - a) * lam₂ ^ (1 / 2 : ℝ) + lam₂ ^ (-1 / 2 : ℝ)) := by ring

private lemma sum_Ioc_abel_monotone_weight (M₁ M₂ : ℤ) (w : ℤ → ℝ) (z : ℤ → ℂ)
    {W D : ℝ} (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hw_bd : ∀ n ∈ Finset.Ioc M₁ M₂, 0 ≤ w n ∧ w n ≤ W)
    (hw_mono : (∀ n ∈ Finset.Ioc M₁ M₂, n + 1 ∈ Finset.Ioc M₁ M₂ → w n ≤ w (n + 1)) ∨
      (∀ n ∈ Finset.Ioc M₁ M₂, n + 1 ∈ Finset.Ioc M₁ M₂ → w (n + 1) ≤ w n))
    (hz : ∀ N' ∈ Finset.Icc M₁ M₂, ‖∑ n ∈ Finset.Ioc M₁ N', z n‖ ≤ D) :
    ‖∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * z n‖ ≤ 2 * W * D := by
  by_cases hM : M₂ ≤ M₁
  · have he : Finset.Ioc M₁ M₂ = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [he, Finset.sum_empty, norm_zero]
    positivity
  · have hM_lt : M₁ < M₂ := not_le.mp hM
    let S : ℤ → ℂ := fun N' => ∑ n ∈ Finset.Ioc M₁ N', z n
    have hS0 : S M₁ = 0 := by simp [S]
    have hz_diff : ∀ n : ℤ, M₁ < n → z n = S n - S (n - 1) := fun n hn => by
      have hsplit : Finset.Ioc M₁ n = insert n (Finset.Ioc M₁ (n - 1)) := by
        ext m; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot : n ∉ Finset.Ioc M₁ (n - 1) := by simp [Finset.mem_Ioc]
      dsimp only [S]
      rw [hsplit, Finset.sum_insert hnot]
      ring
    have hab_id : ∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * z n =
        (w M₂ : ℂ) * S M₂ + ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * S n := by
      have h1 : ∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * z n =
          ∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * (S n - S (n - 1)) :=
        Finset.sum_congr rfl fun n hn => by rw [hz_diff n (Finset.mem_Ioc.mp hn).1]
      rw [h1]
      have hsplit1 : ∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * (S n - S (n - 1)) =
          (∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * S n) -
            ∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * S (n - 1) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => by ring
      have hshift : ∑ n ∈ Finset.Ioc M₁ M₂, (w n : ℂ) * S (n - 1) =
          ∑ n ∈ Finset.Ioc (M₁ - 1) (M₂ - 1), (w (n + 1) : ℂ) * S n := by
        refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
        · intro n hn; simp only [Finset.mem_Ioc] at hn ⊢; omega
        · intro _ _ _ _ h; omega
        · intro n hn; simp only [Finset.mem_Ioc] at hn; exact ⟨n + 1, Finset.mem_Ioc.mpr (by omega), by omega⟩
        · intro n _; simp [sub_add_cancel]
      have hM₂_mem : M₂ ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨hM_lt, le_rfl⟩
      have hsplit_top : Finset.Ioc M₁ M₂ = insert M₂ (Finset.Ioc M₁ (M₂ - 1)) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hM₂_not : M₂ ∉ Finset.Ioc M₁ (M₂ - 1) := by simp [Finset.mem_Ioc]
      have hsplit_bot : Finset.Ioc (M₁ - 1) (M₂ - 1) = insert M₁ (Finset.Ioc M₁ (M₂ - 1)) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hM₁_not : M₁ ∉ Finset.Ioc M₁ (M₂ - 1) := by simp [Finset.mem_Ioc]
      rw [hsplit1, hshift, hsplit_top, Finset.sum_insert hM₂_not, hsplit_bot, Finset.sum_insert hM₁_not,
        hS0, mul_zero, zero_add, add_sub_assoc, ← Finset.sum_sub_distrib]
      have hcong : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ((w n : ℂ) * S n - (w (n + 1) : ℂ) * S n) =
          ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * S n :=
        Finset.sum_congr rfl fun n _ => by ring
      rw [hcong]
    rw [hab_id]
    have hM₂_mem : M₂ ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨hM_lt, le_rfl⟩
    have hS_bd : ∀ n ∈ Finset.Ioc M₁ M₂, ‖S n‖ ≤ D := fun n hn =>
      hz n (Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩)
    have hterm_top : ‖(w M₂ : ℂ) * S M₂‖ ≤ W * D := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_bd M₂ hM₂_mem).1]
      exact mul_le_mul (hw_bd M₂ hM₂_mem).2 (hS_bd M₂ hM₂_mem) (norm_nonneg _) hW
    have hdiff_sum : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), |w n - w (n + 1)| ≤ W := by
      rcases hw_mono with hinc | hdec
      · have hcongr : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), |w n - w (n + 1)| =
            ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), (w (n + 1) - w n) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [Finset.mem_Ioc] at hn
          have hn1 : n ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨hn.1, by omega⟩
          have hn2 : n + 1 ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
          rw [abs_of_nonpos (sub_nonpos.mpr (hinc n hn1 hn2))]; ring
        rw [hcongr]
        have htele : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), (w (n + 1) - w n) = w M₂ - w (M₁ + 1) := by
          let len := Int.toNat (M₂ - (M₁ + 1))
          have hlen : M₁ + 1 + (len : ℤ) = M₂ := by dsimp only [len]; omega
          have hbij : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), (w (n + 1) - w n) =
              ∑ j ∈ Finset.range len, (w (M₁ + 1 + ((j : ℤ) + 1)) - w (M₁ + 1 + (j : ℤ))) := by
            refine Finset.sum_bij (fun n _ => Int.toNat (n - (M₁ + 1))) ?_ ?_ ?_ ?_
            · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_range]; omega
            · intro n₁ hn₁ n₂ hn₂ heq; simp only [Finset.mem_Ioc] at hn₁ hn₂; omega
            · intro j hj; simp only [Finset.mem_range] at hj
              refine ⟨M₁ + 1 + (j : ℤ), Finset.mem_Ioc.mpr (by omega), by omega⟩
            · intro n hn
              simp only [Finset.mem_Ioc] at hn
              have heq1 : M₁ + 1 + (Int.toNat (n - (M₁ + 1)) : ℤ) = n := by omega
              have heq2 : M₁ + 1 + ((Int.toNat (n - (M₁ + 1)) : ℤ) + 1) = n + 1 := by omega
              rw [heq1, heq2]
          rw [hbij, show ∑ j ∈ Finset.range len, (w (M₁ + 1 + ((j : ℤ) + 1)) - w (M₁ + 1 + (j : ℤ))) =
              w (M₁ + 1 + (len : ℤ)) - w (M₁ + 1 + 0) from
              Finset.sum_range_sub (fun j => w (M₁ + 1 + (j : ℤ))) len, hlen, add_zero]
        rw [htele]
        have hM₁_mem : M₁ + 1 ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        linarith [(hw_bd M₂ hM₂_mem).2, (hw_bd (M₁ + 1) hM₁_mem).1]
      · have hcongr : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), |w n - w (n + 1)| =
            ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), (w n - w (n + 1)) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [Finset.mem_Ioc] at hn
          have hn1 : n ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨hn.1, by omega⟩
          have hn2 : n + 1 ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
          exact abs_of_nonneg (sub_nonneg.mpr (hdec n hn1 hn2))
        rw [hcongr]
        have htele : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), (w n - w (n + 1)) = w (M₁ + 1) - w M₂ := by
          let len := Int.toNat (M₂ - (M₁ + 1))
          have hlen : M₁ + 1 + (len : ℤ) = M₂ := by dsimp only [len]; omega
          have hbij : ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), (w n - w (n + 1)) =
              ∑ j ∈ Finset.range len, (w (M₁ + 1 + (j : ℤ)) - w (M₁ + 1 + ((j : ℤ) + 1))) := by
            refine Finset.sum_bij (fun n _ => Int.toNat (n - (M₁ + 1))) ?_ ?_ ?_ ?_
            · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_range]; omega
            · intro n₁ hn₁ n₂ hn₂ heq; simp only [Finset.mem_Ioc] at hn₁ hn₂; omega
            · intro j hj; simp only [Finset.mem_range] at hj
              refine ⟨M₁ + 1 + (j : ℤ), Finset.mem_Ioc.mpr (by omega), by omega⟩
            · intro n hn
              simp only [Finset.mem_Ioc] at hn
              have heq1 : M₁ + 1 + (Int.toNat (n - (M₁ + 1)) : ℤ) = n := by omega
              have heq2 : M₁ + 1 + ((Int.toNat (n - (M₁ + 1)) : ℤ) + 1) = n + 1 := by omega
              rw [heq1, heq2]
          have hsub_eq :
              ∑ j ∈ Finset.range len, (w (M₁ + 1 + (j : ℤ)) - w (M₁ + 1 + ((j : ℤ) + 1))) =
                ∑ j ∈ Finset.range len, (w (M₁ + 1 + (j : ℤ)) - w (M₁ + 1 + ((j + 1 : ℕ) : ℤ))) :=
            Finset.sum_congr rfl fun j _ => by push_cast; rfl
          rw [hbij, hsub_eq, Finset.sum_range_sub' (fun j => w (M₁ + 1 + (j : ℤ))) len, hlen, Int.ofNat_zero, add_zero]
        rw [htele]
        have hM₁_mem : M₁ + 1 ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        linarith [(hw_bd (M₁ + 1) hM₁_mem).2, (hw_bd M₂ hM₂_mem).1]
    have hsum_tail : ‖∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * S n‖ ≤ W * D := by
      calc ‖∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * S n‖
          ≤ ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ‖((w n : ℂ) - (w (n + 1) : ℂ)) * S n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), |w n - w (n + 1)| * D := by
            refine Finset.sum_le_sum fun n hn => ?_
            simp only [Finset.mem_Ioc] at hn
            have hn_mem : n ∈ Finset.Ioc M₁ M₂ := Finset.mem_Ioc.mpr ⟨hn.1, by omega⟩
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hS_bd n hn_mem) (abs_nonneg _)
        _ = (∑ n ∈ Finset.Ioc M₁ (M₂ - 1), |w n - w (n + 1)|) * D := (Finset.sum_mul _ _ _).symm
        _ ≤ W * D := mul_le_mul_of_nonneg_right hdiff_sum hD
    calc ‖(w M₂ : ℂ) * S M₂ + ∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * S n‖
        ≤ ‖(w M₂ : ℂ) * S M₂‖ +
            ‖∑ n ∈ Finset.Ioc M₁ (M₂ - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * S n‖ := norm_add_le _ _
      _ ≤ W * D + W * D := add_le_add hterm_top hsum_tail
      _ = 2 * W * D := by ring

/-- **van der Corput B-process transfer via stationary phase**:
given a stationary-phase transformation of `∑_{n ∈ Ioc a (a + d)} e(f(n))` into
`c₀ * ∑_{ν ∈ Ioc M₁ M₂} w ν * e(g ν) + rem` with monotone amplitude `0 ≤ w ν ≤ C_w * (a / λ₁)^(1/2)`,
unit factor `‖c₀‖ = 1`, dual `(k, l)` exponent-pair bound `C₁ * a^k * λ₁^l` on all sub-intervals
`Ioc M₁ N'`, and error `‖rem‖ ≤ C_err * (λ₁^(l - 1/2) * a^(k + 1/2) + (a / λ₁)^(1/2))`,
applying Abel summation yields the transformed exponent pair `(l - 1/2, k + 1/2)`. -/
theorem vanDerCorput_B_process_of_stationaryPhase {f : ℝ → ℝ} {a d : ℕ} {M₁ M₂ : ℤ}
    {w g : ℤ → ℝ} {c₀ : ℂ} {lam₁ k l C_w C₁ C_err : ℝ}
    (ha : 1 ≤ a) (hlam : 0 < lam₁) (hCw : 0 ≤ C_w) (hC₁ : 0 ≤ C₁) (_hCerr : 0 ≤ C_err)
    (hc₀ : ‖c₀‖ = 1)
    (hstat : ‖∑ n ∈ Finset.Ioc a (a + d), Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I) -
        c₀ * ∑ ν ∈ Finset.Ioc M₁ M₂,
          (w ν : ℂ) * Complex.exp (2 * Real.pi * (g ν : ℂ) * Complex.I)‖ ≤
      C_err * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) + ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)))
    (hw_bd : ∀ ν ∈ Finset.Ioc M₁ M₂, 0 ≤ w ν ∧ w ν ≤ C_w * ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ))
    (hw_mono : (∀ ν ∈ Finset.Ioc M₁ M₂, ν + 1 ∈ Finset.Ioc M₁ M₂ → w ν ≤ w (ν + 1)) ∨
      (∀ ν ∈ Finset.Ioc M₁ M₂, ν + 1 ∈ Finset.Ioc M₁ M₂ → w (ν + 1) ≤ w ν))
    (hdual : ∀ N' ∈ Finset.Icc M₁ M₂,
      ‖∑ ν ∈ Finset.Ioc M₁ N', Complex.exp (2 * Real.pi * (g ν : ℂ) * Complex.I)‖ ≤
        C₁ * (a : ℝ) ^ k * lam₁ ^ l) :
    ‖∑ n ∈ Finset.Ioc a (a + d), Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖ ≤
      (2 * C_w * C₁ + C_err) *
        (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) + ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)) := by
  have ha_pos : (0 : ℝ) < a := by positivity
  let W := C_w * ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)
  let D := C₁ * (a : ℝ) ^ k * lam₁ ^ l
  have hW : 0 ≤ W := by positivity
  have hD : 0 ≤ D := by positivity
  have habel := sum_Ioc_abel_monotone_weight M₁ M₂ w (fun ν => vdcE (g ν)) hW hD hw_bd hw_mono hdual
  have hpow_comb : ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ) * ((a : ℝ) ^ k * lam₁ ^ l) =
      lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) := by
    rw [Real.div_rpow ha_pos.le hlam.le]
    have hinv : (lam₁ ^ (1 / 2 : ℝ))⁻¹ = lam₁ ^ (-1 / 2 : ℝ) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hlam.le]
    calc (a : ℝ) ^ (1 / 2 : ℝ) / lam₁ ^ (1 / 2 : ℝ) * ((a : ℝ) ^ k * lam₁ ^ l)
        = (lam₁ ^ l * lam₁ ^ (-1 / 2 : ℝ)) * ((a : ℝ) ^ k * (a : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [div_eq_mul_inv, hinv]; ring
      _ = lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) := by
          rw [← Real.rpow_add hlam, ← Real.rpow_add ha_pos]
          congr 2; ring
  have h2WD : 2 * W * D = 2 * C_w * C₁ * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2)) := by
    dsimp only [W, D]
    calc 2 * (C_w * ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)) * (C₁ * (a : ℝ) ^ k * lam₁ ^ l)
        = 2 * C_w * C₁ * (((a : ℝ) / lam₁) ^ (1 / 2 : ℝ) * ((a : ℝ) ^ k * lam₁ ^ l)) := by ring
      _ = 2 * C_w * C₁ * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2)) := by rw [hpow_comb]
  have hmain_norm :
      ‖c₀ * ∑ ν ∈ Finset.Ioc M₁ M₂, (w ν : ℂ) * vdcE (g ν)‖ ≤
        2 * C_w * C₁ * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2)) := by
    rw [norm_mul, hc₀, one_mul]
    exact habel.trans_eq h2WD
  have htri :
      ‖∑ n ∈ Finset.Ioc a (a + d), vdcE (f (n : ℝ))‖ ≤
        ‖∑ n ∈ Finset.Ioc a (a + d), vdcE (f (n : ℝ)) -
          c₀ * ∑ ν ∈ Finset.Ioc M₁ M₂, (w ν : ℂ) * vdcE (g ν)‖ +
        ‖c₀ * ∑ ν ∈ Finset.Ioc M₁ M₂, (w ν : ℂ) * vdcE (g ν)‖ := by
    simpa [sub_add_cancel] using norm_add_le
      (∑ n ∈ Finset.Ioc a (a + d), vdcE (f (n : ℝ)) -
        c₀ * ∑ ν ∈ Finset.Ioc M₁ M₂, (w ν : ℂ) * vdcE (g ν))
      (c₀ * ∑ ν ∈ Finset.Ioc M₁ M₂, (w ν : ℂ) * vdcE (g ν))
  have hpos_rhs : 0 ≤ ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ) := by positivity
  have hpos_pref : 0 ≤ 2 * C_w * C₁ := by positivity
  calc ‖∑ n ∈ Finset.Ioc a (a + d), Complex.exp (2 * Real.pi * (f (n : ℝ) : ℂ) * Complex.I)‖
      ≤ C_err * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) + ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)) +
          2 * C_w * C₁ * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2)) :=
        htri.trans (add_le_add hstat hmain_norm)
    _ ≤ C_err * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) + ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)) +
          2 * C_w * C₁ * (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) + ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)) := by
        nlinarith
    _ = (2 * C_w * C₁ + C_err) *
          (lam₁ ^ (l - 1 / 2) * (a : ℝ) ^ (k + 1 / 2) + ((a : ℝ) / lam₁) ^ (1 / 2 : ℝ)) := by ring

end ProcessBPoissonAndStationaryPhase

section ExponentPairs

/-- Formal structure representing an exponent pair `(k, l)` with `0 ≤ k ≤ 1/2 ≤ l ≤ 1`. -/
@[ext]
structure ExponentPair where
  /-- First exponent `k`, satisfying `0 ≤ k ≤ 1/2`. -/
  k : ℝ
  /-- Second exponent `l`, satisfying `1/2 ≤ l ≤ 1`. -/
  l : ℝ
  /-- Lower bound `0 ≤ k`. -/
  hk0 : 0 ≤ k
  /-- Upper bound `k ≤ 1/2`. -/
  hk_half : k ≤ 1 / 2
  /-- Lower bound `1/2 ≤ l`. -/
  hl_half : 1 / 2 ≤ l
  /-- Upper bound `l ≤ 1`. -/
  hl1 : l ≤ 1

/-- The trivial exponent pair `(0, 1)`. -/
def exponentPair_zero_one : ExponentPair where
  k := 0
  l := 1
  hk0 := le_rfl
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := le_rfl

/-- The quadratic exponent pair `(1/2, 1/2)` obtained as `B(0, 1)`. -/
def exponentPair_half_half : ExponentPair where
  k := 1 / 2
  l := 1 / 2
  hk0 := by norm_num
  hk_half := le_rfl
  hl_half := le_rfl
  hl1 := by norm_num

/-- **Weyl–van der Corput A-process** on exponent pairs:
`A(k, l) = (k / (2k + 2), (k + l + 1) / (2k + 2))`. -/
def ExponentPair.processA (p : ExponentPair) : ExponentPair where
  k := p.k / (2 * p.k + 2)
  l := (p.k + p.l + 1) / (2 * p.k + 2)
  hk0 := div_nonneg p.hk0 (by linarith [p.hk0])
  hk_half := by
    rw [div_le_div_iff₀ (by linarith [p.hk0]) (by norm_num)]
    linarith
  hl_half := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith [p.hk0])]
    linarith [p.hl_half]
  hl1 := by
    rw [div_le_one (by linarith [p.hk0])]
    linarith [p.hk0, p.hl1]

/-- **van der Corput B-process** on exponent pairs: `B(k, l) = (l - 1/2, k + 1/2)`. -/
def ExponentPair.processB (p : ExponentPair) : ExponentPair where
  k := p.l - 1 / 2
  l := p.k + 1 / 2
  hk0 := by linarith [p.hl_half]
  hk_half := by linarith [p.hl1]
  hl_half := by linarith [p.hk0]
  hl1 := by linarith [p.hk_half]

/-- Convex combination of two exponent pairs. -/
def ExponentPair.convexComb (p q : ExponentPair) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ExponentPair where
  k := θ * p.k + (1 - θ) * q.k
  l := θ * p.l + (1 - θ) * q.l
  hk0 := add_nonneg (mul_nonneg hθ0 p.hk0) (mul_nonneg (by linarith) q.hk0)
  hk_half := by nlinarith [p.hk_half, q.hk_half]
  hl_half := by nlinarith [p.hl_half, q.hl_half]
  hl1 := by nlinarith [p.hl1, q.hl1]

/-- Applying Process B twice is the identity. -/
@[simp]
theorem ExponentPair.processB_processB (p : ExponentPair) :
    p.processB.processB = p := by
  ext <;> dsimp [ExponentPair.processB] <;> ring

/-- Process B maps `(0, 1)` to `(1/2, 1/2)`. -/
@[simp]
theorem exponentPair_zero_one_processB :
    exponentPair_zero_one.processB = exponentPair_half_half := by
  ext <;> simp [exponentPair_zero_one, exponentPair_half_half, ExponentPair.processB]
  norm_num

/-- Process A fixes `(0, 1)`. -/
@[simp]
theorem exponentPair_zero_one_processA :
    exponentPair_zero_one.processA = exponentPair_zero_one := by
  ext <;> simp [exponentPair_zero_one, ExponentPair.processA]

/-- Classical exponent pair `(1/6, 2/3) = A(1/2, 1/2) = AB(0, 1)`. -/
def exponentPair_one_sixth_two_thirds : ExponentPair where
  k := 1 / 6
  l := 2 / 3
  hk0 := by norm_num
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := by norm_num

/-- `A(1/2, 1/2) = (1/6, 2/3)`. -/
theorem exponentPair_half_half_processA :
    exponentPair_half_half.processA = exponentPair_one_sixth_two_thirds := by
  ext <;> simp [exponentPair_half_half, exponentPair_one_sixth_two_thirds, ExponentPair.processA] <;>
    norm_num

/-- Classical exponent pair `(1/14, 11/14) = A(1/6, 2/3) = A^2 B(0, 1)`. -/
def exponentPair_one_fourteenth_eleven_fourteenths : ExponentPair where
  k := 1 / 14
  l := 11 / 14
  hk0 := by norm_num
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := by norm_num

/-- `A(1/6, 2/3) = (1/14, 11/14)`. -/
theorem exponentPair_one_sixth_two_thirds_processA :
    exponentPair_one_sixth_two_thirds.processA = exponentPair_one_fourteenth_eleven_fourteenths := by
  ext <;> simp [exponentPair_one_sixth_two_thirds, exponentPair_one_fourteenth_eleven_fourteenths,
    ExponentPair.processA] <;> norm_num

/-- Classical exponent pair `(2/7, 4/7) = B(1/14, 11/14) = B A^2 B(0, 1)`. -/
def exponentPair_two_sevenths_four_sevenths : ExponentPair where
  k := 2 / 7
  l := 4 / 7
  hk0 := by norm_num
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := by norm_num

/-- `B(1/14, 11/14) = (2/7, 4/7)`. -/
theorem exponentPair_one_fourteenth_processB :
    exponentPair_one_fourteenth_eleven_fourteenths.processB =
      exponentPair_two_sevenths_four_sevenths := by
  ext <;> simp [exponentPair_one_fourteenth_eleven_fourteenths,
    exponentPair_two_sevenths_four_sevenths, ExponentPair.processB] <;> norm_num

/-- Classical exponent pair `(1/9, 13/18) = A(2/7, 4/7)`. -/
def exponentPair_one_ninth_thirteen_eighteenths : ExponentPair where
  k := 1 / 9
  l := 13 / 18
  hk0 := by norm_num
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := by norm_num

/-- `A(2/7, 4/7) = (1/9, 13/18)`. -/
theorem exponentPair_two_sevenths_processA :
    exponentPair_two_sevenths_four_sevenths.processA = exponentPair_one_ninth_thirteen_eighteenths := by
  ext <;> simp [exponentPair_two_sevenths_four_sevenths, exponentPair_one_ninth_thirteen_eighteenths,
    ExponentPair.processA] <;> norm_num

/-- Classical exponent pair `(2/9, 11/18) = B(1/9, 13/18) = B A B A^2 B(0, 1)`. -/
def exponentPair_two_ninths_eleven_eighteenths : ExponentPair where
  k := 2 / 9
  l := 11 / 18
  hk0 := by norm_num
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := by norm_num

/-- `B(1/9, 13/18) = (2/9, 11/18)`. -/
theorem exponentPair_one_ninth_processB :
    exponentPair_one_ninth_thirteen_eighteenths.processB = exponentPair_two_ninths_eleven_eighteenths := by
  ext <;> simp [exponentPair_one_ninth_thirteen_eighteenths,
    exponentPair_two_ninths_eleven_eighteenths, ExponentPair.processB] <;> norm_num

/-- Classical exponent pair `(1/30, 13/15) = A(1/14, 11/14) = A^3 B(0, 1)`. -/
def exponentPair_one_thirtieth_thirteen_fifteenths : ExponentPair where
  k := 1 / 30
  l := 13 / 15
  hk0 := by norm_num
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := by norm_num

/-- `A(1/14, 11/14) = (1/30, 13/15)`. -/
theorem exponentPair_one_fourteenth_processA :
    exponentPair_one_fourteenth_eleven_fourteenths.processA =
      exponentPair_one_thirtieth_thirteen_fifteenths := by
  ext <;> simp [exponentPair_one_fourteenth_eleven_fourteenths,
    exponentPair_one_thirtieth_thirteen_fifteenths, ExponentPair.processA] <;> norm_num

/-- Classical exponent pair `(11/30, 8/15) = B(1/30, 13/15) = B A^3 B(0, 1)`. -/
def exponentPair_eleven_thirtieths_eight_fifteenths : ExponentPair where
  k := 11 / 30
  l := 8 / 15
  hk0 := by norm_num
  hk_half := by norm_num
  hl_half := by norm_num
  hl1 := by norm_num

/-- `B(1/30, 13/15) = (11/30, 8/15)`. -/
theorem exponentPair_one_thirtieth_processB :
    exponentPair_one_thirtieth_thirteen_fifteenths.processB =
      exponentPair_eleven_thirtieths_eight_fifteenths := by
  ext <;> simp [exponentPair_one_thirtieth_thirteen_fifteenths,
    exponentPair_eleven_thirtieths_eight_fifteenths, ExponentPair.processB] <;> norm_num

/-- Inductive predicate characterizing valid van der Corput exponent pairs generated from `(0, 1)`
under Process A, Process B, and convex combinations. -/
inductive IsExponentPair : ℝ → ℝ → Prop where
  | zero_one : IsExponentPair 0 1
  | processA {k l : ℝ} (h : IsExponentPair k l) :
      IsExponentPair (k / (2 * k + 2)) ((k + l + 1) / (2 * k + 2))
  | processB {k l : ℝ} (h : IsExponentPair k l) :
      IsExponentPair (l - 1 / 2) (k + 1 / 2)
  | convexComb {k₁ l₁ k₂ l₂ θ : ℝ} (h₁ : IsExponentPair k₁ l₁) (h₂ : IsExponentPair k₂ l₂)
      (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
      IsExponentPair (θ * k₁ + (1 - θ) * k₂) (θ * l₁ + (1 - θ) * l₂)

/-- Every `IsExponentPair k l` satisfies the exponent-pair box inequalities `0 ≤ k ≤ 1/2 ≤ l ≤ 1`. -/
theorem isExponentPair_bounds {k l : ℝ} (h : IsExponentPair k l) :
    0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 := by
  induction h with
  | zero_one => norm_num
  | processA _ ih =>
    rcases ih with ⟨hk0, hk1, hl0, hl1⟩
    refine ⟨div_nonneg hk0 (by linarith), ?_, ?_, ?_⟩
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    · rw [div_le_one (by linarith)]; linarith
  | processB _ ih =>
    rcases ih with ⟨hk0, hk1, hl0, hl1⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  | convexComb _ _ hθ0 hθ1 ih₁ ih₂ =>
    rcases ih₁ with ⟨hk10, hk11, hl10, hl11⟩
    rcases ih₂ with ⟨hk20, hk21, hl20, hl21⟩
    refine ⟨add_nonneg (mul_nonneg hθ0 hk10) (mul_nonneg (by linarith) hk20), ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith

/-- `(1/2, 1/2)` is an exponent pair. -/
theorem isExponentPair_half_half : IsExponentPair (1 / 2) (1 / 2) := by
  convert IsExponentPair.processB IsExponentPair.zero_one using 1 <;> norm_num

/-- `(1/6, 2/3)` is an exponent pair (`AB(0, 1)`). -/
theorem isExponentPair_one_sixth_two_thirds : IsExponentPair (1 / 6) (2 / 3) := by
  convert IsExponentPair.processA isExponentPair_half_half using 1 <;> norm_num

/-- `(1/14, 11/14)` is an exponent pair (`A^2 B(0, 1)`). -/
theorem isExponentPair_one_fourteenth_eleven_fourteenths : IsExponentPair (1 / 14) (11 / 14) := by
  convert IsExponentPair.processA isExponentPair_one_sixth_two_thirds using 1 <;> norm_num

/-- `(2/7, 4/7)` is an exponent pair (`B A^2 B(0, 1)`). -/
theorem isExponentPair_two_sevenths_four_sevenths : IsExponentPair (2 / 7) (4 / 7) := by
  convert IsExponentPair.processB isExponentPair_one_fourteenth_eleven_fourteenths using 1 <;> norm_num

/-- `(1/9, 13/18)` is an exponent pair (`A B A^2 B(0, 1)`). -/
theorem isExponentPair_one_ninth_thirteen_eighteenths : IsExponentPair (1 / 9) (13 / 18) := by
  convert IsExponentPair.processA isExponentPair_two_sevenths_four_sevenths using 1 <;> norm_num

/-- `(2/9, 11/18)` is an exponent pair (`B A B A^2 B(0, 1)`). -/
theorem isExponentPair_two_ninths_eleven_eighteenths : IsExponentPair (2 / 9) (11 / 18) := by
  convert IsExponentPair.processB isExponentPair_one_ninth_thirteen_eighteenths using 1 <;> norm_num

/-- `(1/30, 13/15)` is an exponent pair (`A^3 B(0, 1)`). -/
theorem isExponentPair_one_thirtieth_thirteen_fifteenths : IsExponentPair (1 / 30) (13 / 15) := by
  convert IsExponentPair.processA isExponentPair_one_fourteenth_eleven_fourteenths using 1 <;> norm_num

/-- `(11/30, 8/15)` is an exponent pair (`B A^3 B(0, 1)`). -/
theorem isExponentPair_eleven_thirtieths_eight_fifteenths : IsExponentPair (11 / 30) (8 / 15) := by
  convert IsExponentPair.processB isExponentPair_one_thirtieth_thirteen_fifteenths using 1 <;> norm_num

end ExponentPairs

end AnalyticNumberTheory.ExponentialSums
