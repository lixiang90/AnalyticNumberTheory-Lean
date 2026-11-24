import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl

/-!
# A finite Fourier enclosure for the sawtooth

The periodic second Bernoulli kernel has an absolutely convergent cosine series.
Its forward and backward differences bound the sawtooth from opposite sides,
including at integer arguments. Truncating the cosine series gives computable
one-sided estimates with an explicit error.
-/

noncomputable section

open Finset
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.DivisorProblems

/-- A Fourier partial sum of the normalized second Bernoulli kernel. -/
def bernoulliKernelFourierSum (H : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 H, Real.cos (2 * Real.pi * n * t) / (n : ℝ) ^ 2) / (2 * Real.pi ^ 2)

/-- Uniform tail estimate for the second Bernoulli kernel, valid at the period endpoints. -/
theorem abs_bernoulliKernelFourierSum_sub_le {H : ℕ} (hH : 1 ≤ H) (t : ℝ) :
    |bernoulliKernelFourierSum H t - bernoulliKernel 2 t| ≤ (H : ℝ)⁻¹ / (2 * Real.pi ^ 2) := by
  have hraw := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero
    (show Int.fract t ∈ Set.Icc (0 : ℝ) 1 from ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
  have hcos (n : ℕ) :
      Real.cos (2 * Real.pi * n * Int.fract t) = Real.cos (2 * Real.pi * n * t) := by
    rw [show 2 * Real.pi * n * Int.fract t =
        2 * Real.pi * n * t - ((n : ℤ) * ⌊t⌋ : ℤ) * (2 * Real.pi) by
          rw [Int.fract]; push_cast; ring]
    exact Real.cos_sub_int_mul_two_pi _ _
  have hseries : HasSum (fun n : ℕ => Real.cos (2 * Real.pi * n * t) / (n : ℝ) ^ 2)
      ((2 * Real.pi ^ 2) * bernoulliKernel 2 t) := by
    convert hraw using 1
    · ext n
      rw [hcos]
      norm_num
      ring
    · change _ = _ * bernoulliFun (2 * 1) (Int.fract t)
      norm_num [bernoulliKernel, periodicBernoulli]
      ring
  have h := abs_sum_Icc_div_sq_sub_tsum_le (fun n => Real.abs_cos_le_one _)
    hseries.summable hH
  rw [hseries.tsum_eq] at h
  have hd : 0 < 2 * Real.pi ^ 2 := by positivity
  rw [bernoulliKernelFourierSum, div_sub' hd.ne', abs_div, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  simpa only [mul_comm (bernoulliKernel 2 t)] using h

/-- A step crossing an integer contributes a jump of one to the sawtooth. The finite
difference of its continuous Bernoulli primitive lies between the two endpoint values
after allowing for the linear change within each period. -/
theorem bernoulliKernel_two_step_bounds (t : ℝ) {h : ℝ} (hh : 0 ≤ h) (h1 : h < 1) :
    h * sawtooth (t + h) - h ^ 2 / 2 ≤ bernoulliKernel 2 (t + h) - bernoulliKernel 2 t ∧
      bernoulliKernel 2 (t + h) - bernoulliKernel 2 t ≤ h * sawtooth t + h ^ 2 / 2 := by
  have hfract : Int.fract h = h := Int.fract_eq_self.mpr ⟨hh, h1⟩
  simp only [bernoulliKernel_two, sawtooth]
  rcases Int.fract_add_eq_or t h with hstep | hstep <;> rw [hfract] at hstep <;> rw [hstep]
  · constructor <;> linarith only
  · have hafter := Int.fract_nonneg (t + h)
    rw [hstep] at hafter
    constructor <;> linarith only [hafter, Int.fract_lt_one t]

/-- Forward and backward finite trigonometric polynomials enclose the sawtooth at every
real argument. The truncation error before dividing by the step is `1/(π² H)` on each side. -/
theorem sawtooth_fourier_enclosure (t : ℝ) {H : ℕ} (hH : 1 ≤ H) {h : ℝ}
    (hh : 0 < h) (h1 : h < 1) :
    bernoulliKernelFourierSum H (t + h) - bernoulliKernelFourierSum H t -
        (H : ℝ)⁻¹ / Real.pi ^ 2 - h ^ 2 / 2 ≤ h * sawtooth t ∧
      h * sawtooth t ≤ bernoulliKernelFourierSum H t - bernoulliKernelFourierSum H (t - h) +
        (H : ℝ)⁻¹ / Real.pi ^ 2 + h ^ 2 / 2 := by
  have hf := (bernoulliKernel_two_step_bounds t hh.le h1).2
  have hb := (bernoulliKernel_two_step_bounds (t - h) hh.le h1).1
  rw [sub_add_cancel] at hb
  have hplus := (abs_le.mp (abs_bernoulliKernelFourierSum_sub_le hH (t + h))).2
  have hminus := (abs_le.mp (abs_bernoulliKernelFourierSum_sub_le hH (t - h))).2
  have hcenter := (abs_le.mp (abs_bernoulliKernelFourierSum_sub_le hH t)).1
  have hd : (H : ℝ)⁻¹ / Real.pi ^ 2 = 2 * ((H : ℝ)⁻¹ / (2 * Real.pi ^ 2)) := by ring
  constructor <;> linarith only [hf, hb, hplus, hminus, hcenter, hd]

/-- Translating a truncated Bernoulli kernel multiplies its frequency `n` by
`e(nh) - 1`. The resulting bound retains cancellation across all points of `s`. -/
theorem abs_sum_bernoulliKernelFourierSum_shift_le {ι : Type*} (s : Finset ι)
    (t : ι → ℝ) (H : ℕ) (h : ℝ) :
    |∑ i ∈ s, (bernoulliKernelFourierSum H (t i + h) - bernoulliKernelFourierSum H (t i))| ≤
      (∑ n ∈ Icc 1 H, ‖e (n * h) - 1‖ * ‖∑ i ∈ s, e (n * t i)‖ / (n : ℝ) ^ 2) /
        (2 * Real.pi ^ 2) := by
  have hre (u : ℝ) : (e u).re = Real.cos (2 * Real.pi * u) := by
    unfold e
    rw [← Complex.exp_ofReal_mul_I_re]
    push_cast
    rfl
  have hcos (n : ℕ) :
      ∑ i ∈ s, (Real.cos (2 * Real.pi * n * (t i + h)) - Real.cos (2 * Real.pi * n * t i)) =
        ((e (n * h) - 1) * ∑ i ∈ s, e (n * t i)).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [sub_mul, one_mul, Complex.sub_re, ← e_add, hre, hre]
    rw [show 2 * Real.pi * n * (t i + h) = 2 * Real.pi * (n * h + n * t i) by ring,
      mul_assoc (2 * Real.pi) (n : ℝ) (t i)]
  simp only [bernoulliKernelFourierSum, ← sub_div, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_div, Finset.sum_comm, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi ^ 2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  rw [← Finset.sum_div]
  rw [hcos, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa only [norm_mul] using Complex.abs_re_le_norm ((e (n * h) - 1) * ∑ i ∈ s, e (n * t i))

/-- A finite exponential-sum bound for the sawtooth sum of an arbitrary collection of
phases. Both one-sided estimates use the same Fourier weights. -/
theorem abs_sum_sawtooth_le_exponential_sums {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {H : ℕ} (hH : 1 ≤ H) {h : ℝ} (hh : 0 < h) (h1 : h < 1) :
    h * |∑ i ∈ s, sawtooth (t i)| ≤
      s.card * ((H : ℝ)⁻¹ / Real.pi ^ 2 + h ^ 2 / 2) +
        (∑ n ∈ Icc 1 H, ‖e (n * h) - 1‖ * ‖∑ i ∈ s, e (n * t i)‖ / (n : ℝ) ^ 2) /
          (2 * Real.pi ^ 2) := by
  let T := bernoulliKernelFourierSum H
  let R := (H : ℝ)⁻¹ / Real.pi ^ 2 + h ^ 2 / 2
  have hup := sum_le_sum (s := s) (fun i _ =>
    show h * sawtooth (t i) ≤ -(T (t i - h) - T (t i)) + R by
      dsimp only [T, R]
      linarith only [(sawtooth_fourier_enclosure (t i) hH hh h1).2])
  have hlo := sum_le_sum (s := s) (fun i _ =>
    show (T (t i + h) - T (t i)) - R ≤ h * sawtooth (t i) by
      dsimp only [T, R]
      linarith only [(sawtooth_fourier_enclosure (t i) hH hh h1).1])
  rw [← mul_sum, sum_add_distrib, sum_neg_distrib, sum_const, nsmul_eq_mul] at hup
  rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at hlo
  have hpos := (abs_le.mp (abs_sum_bernoulliKernelFourierSum_shift_le s t H h)).1
  have hneg := (abs_le.mp (abs_sum_bernoulliKernelFourierSum_shift_le s t H (-h))).1
  have hw (n : ℕ) : ‖e (n * -h) - 1‖ = ‖e (n * h) - 1‖ := by
    rw [mul_neg, norm_sub_rev, norm_one_sub_e, distToInt_neg, ← norm_one_sub_e, norm_sub_rev]
  simp only [hw, ← sub_eq_add_neg] at hneg
  dsimp only [T, R] at hup hlo
  rw [← abs_of_pos hh, ← abs_mul, abs_of_pos hh, abs_le]
  constructor <;> linarith only [hup, hlo, hpos, hneg]

end AnalyticNumberTheory.DivisorProblems
