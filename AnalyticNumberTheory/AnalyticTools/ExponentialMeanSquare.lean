import AnalyticNumberTheory.AnalyticTools.ExponentialMeans
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Mean orthogonality for exponential series with distinct frequencies -/

noncomputable section

open Complex Filter
open scoped Topology ComplexConjugate

namespace AnalyticNumberTheory.AnalyticTools

private lemma character_mul_conj (x y t : ℝ) :
    Complex.exp ((x*t : ℝ)*I) * conj (Complex.exp ((y*t : ℝ)*I)) =
      Complex.exp (((x-y)*t : ℝ)*I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp
  ring

/-- The product of two absolutely summable exponential expansions, with
the second conjugated, has the differences of their frequencies. -/
theorem exponentialSeries_mul_conj {ι κ : Type*}
    (c : ι → ℂ) (d : κ → ℂ) (ω : ι → ℝ) (ν : κ → ℝ)
    (hc : Summable (fun j => ‖c j‖)) (hd : Summable (fun j => ‖d j‖)) (t : ℝ) :
    exponentialSeries c ω t * conj (exponentialSeries d ν t) =
      exponentialSeries (fun p : ι × κ => c p.1 * conj (d p.2)) (fun p => ω p.1 - ν p.2) t := by
  unfold exponentialSeries
  rw [Complex.conj_tsum]
  have h₁ : Summable (fun j => ‖c j * Complex.exp ((ω j*t : ℝ)*I)‖) := by
    simpa only [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one] using hc
  have h₂ : Summable (fun j => ‖conj (d j * Complex.exp ((ν j*t : ℝ)*I))‖) := by
    simpa only [Complex.norm_conj,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one] using hd
  rw [tsum_mul_tsum_of_summable_norm h₁ h₂]
  apply tsum_congr
  intro p
  rw [map_mul, ← character_mul_conj]
  ring

/-- For an injective frequency, the sum over equal-frequency pairs reduces
to the diagonal sum, under absolute summability of the pair weights. -/
theorem tsum_equal_frequency {ι : Type*} (ω : ι → ℝ) (hω : Function.Injective ω)
    (P : ι × ι → ℂ) (hP : Summable (fun p => ‖P p‖)) :
    (∑' p : ι × ι, if ω p.1 - ω p.2 = 0 then P p else 0) = ∑' j, P (j,j) := by
  let f (p : ι × ι) : ℂ := if ω p.1 - ω p.2 = 0 then P p else 0
  have hf : Summable f := by
    apply hP.of_norm_bounded
    intro p
    by_cases h : ω p.1 - ω p.2 = 0 <;> simp [f,h]
  change (∑' p, f p) = _
  rw [hf.tsum_prod]
  apply tsum_congr
  intro j
  calc
    (∑' k, f (j,k)) = f (j,j) := by
      apply tsum_eq_single
      intro k hne
      have hωne : ω j ≠ ω k := fun h => hne (hω h).symm
      simp [f, sub_ne_zero.mpr hωne]
    _ = P (j,j) := by simp [f]

/-- On a common sequence of distinct real frequencies the symmetric mean of
a mixed product equals the diagonal sum of the coefficients. -/
theorem tendsto_symmetricMean_mul_conj {ι : Type*} [Countable ι] (c d : ι → ℂ) (ω : ι → ℝ)
    (hω : Function.Injective ω) (hc : Summable (fun j => ‖c j‖)) (hd : Summable (fun j => ‖d j‖)) :
    Tendsto (symmetricMean (fun t => exponentialSeries c ω t * conj (exponentialSeries d ω t)))
      atTop (𝓝 (∑' j, c j * conj (d j))) := by
  have hd' : Summable (fun j => ‖conj (d j)‖) := by simpa only [Complex.norm_conj] using hd
  have hC : Summable (fun p : ι × ι => ‖c p.1 * conj (d p.2)‖) :=
    Summable.mul_norm (f := c) (g := fun j => conj (d j)) hc hd'
  let pair (p : ι × ι) := c p.1 * conj (d p.2)
  let diff (p : ι × ι) := ω p.1 - ω p.2
  have hf : (fun t => exponentialSeries c ω t * conj (exponentialSeries d ω t)) = exponentialSeries pair diff :=
    funext (exponentialSeries_mul_conj c d ω ω hc hd)
  rw [hf]
  have he := tsum_equal_frequency ω hω pair hC
  exact he ▸ tendsto_symmetricMean_expansion pair diff hC

/-- The mean square of an absolutely summable exponential expansion with distinct
frequencies equals the sum of the squared coefficient norms. -/
theorem tendsto_meanSquare_exponentialSeries {ι : Type*} [Countable ι] (c : ι → ℂ) (ω : ι → ℝ)
    (hω : Function.Injective ω) (hc : Summable (fun j => ‖c j‖)) :
    Tendsto (fun T : ℝ => (∫ t : ℝ in -T..T, ‖exponentialSeries c ω t‖^2) / (2*T))
      atTop (𝓝 (∑' j, ‖c j‖^2)) := by
  have H := tendsto_symmetricMean_mul_conj c c ω hω hc hc
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_tsum] at H
  have H' := Complex.continuous_re.continuousAt.tendsto.comp H
  simpa only [Function.comp_def, symmetricMean, intervalIntegral.integral_ofReal, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re] using H'

end AnalyticNumberTheory.AnalyticTools
