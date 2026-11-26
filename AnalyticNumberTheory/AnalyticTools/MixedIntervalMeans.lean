import AnalyticNumberTheory.AnalyticTools.ExponentialMeanSquare
import AnalyticNumberTheory.AnalyticTools.IntervalMeans

/-! # Mixed means of exponential expansions on growing intervals -/

noncomputable section

open Complex Filter
open scoped Topology ComplexConjugate

namespace AnalyticNumberTheory.AnalyticTools

/-- Reversing time conjugates an exponential series with conjugated
coefficients. No relation between distinct frequencies is needed. -/
theorem exponentialSeries_neg_time {ι : Type*} (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    exponentialSeries c ω (-t) = conj (exponentialSeries (fun j => conj (c j)) ω t) := by
  rw [exponentialSeries, exponentialSeries, Complex.conj_tsum]
  apply tsum_congr
  intro j
  rw [map_mul, conj_conj, ← Complex.exp_conj]
  simp

/-- On two possibly different spectra, the mixed mean of an expansion at
time `t` and a second at time `-t` retains every pair of equal frequencies.
The interval may move as its length tends to infinity. -/
theorem tendsto_intervalMean_mul_reflected {ι κ α : Type*} [Countable ι] [Countable κ]
    {l : Filter α} (c : ι → ℂ) (d : κ → ℂ) (ω : ι → ℝ) (ν : κ → ℝ)
    (hc : Summable (fun i => ‖c i‖)) (hd : Summable (fun j => ‖d j‖))
    (x y : α → ℝ) (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => intervalMean (fun t => exponentialSeries c ω t * exponentialSeries d ν (-t))
      (x k) (y k)) l (𝓝 (∑' p : ι × κ, if ω p.1 = ν p.2 then c p.1 * d p.2 else 0)) := by
  have hd' : Summable (fun j => ‖conj (d j)‖) := by simpa only [Complex.norm_conj] using hd
  have hpair := Summable.mul_norm (f := c) (g := d) hc hd
  have hf (t : ℝ) : exponentialSeries c ω t * exponentialSeries d ν (-t) =
      exponentialSeries (fun p : ι × κ => c p.1 * d p.2) (fun p => ω p.1 - ν p.2) t := by
    rw [exponentialSeries_neg_time, exponentialSeries_mul_conj c _ ω ν hc hd']
    simp only [conj_conj]
  simp only [hf]
  simpa only [sub_eq_zero] using tendsto_intervalMean_expansion
    (fun p : ι × κ => c p.1 * d p.2) (fun p => ω p.1 - ν p.2) hpair x y hlen

/-- On a common injective spectrum the moving-interval bilinear mean is the
diagonal sum of the coefficient products. -/
theorem tendsto_intervalMean_mul_reflected_diagonal {ι α : Type*} [Countable ι] {l : Filter α}
    (c d : ι → ℂ) (ω : ι → ℝ) (hω : Function.Injective ω)
    (hc : Summable (fun j => ‖c j‖)) (hd : Summable (fun j => ‖d j‖))
    (x y : α → ℝ) (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => intervalMean (fun t => exponentialSeries c ω t * exponentialSeries d ω (-t))
      (x k) (y k)) l (𝓝 (∑' j, c j * d j)) := by
  have he := tsum_equal_frequency ω hω (fun p : ι × ι => c p.1 * d p.2)
    (Summable.mul_norm (f := c) (g := d) hc hd)
  simp only [sub_eq_zero] at he
  rw [← he]
  exact tendsto_intervalMean_mul_reflected c d ω ω hc hd x y hlen

end AnalyticNumberTheory.AnalyticTools
