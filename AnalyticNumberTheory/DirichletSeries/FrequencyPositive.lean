import AnalyticNumberTheory.DirichletSeries.FrequencyDerivatives

/-! # Positive coefficients and exponential Taylor moments -/

noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a : ℕ → ℝ}

private lemma real_partialSum (σ : ℝ) (N : ℕ) :
    F.partialSum (fun n => (a n : ℂ)) σ N = ((∑ n ∈ Finset.range N, a n * Real.exp (-σ*F n) : ℝ) : ℂ) := by
  simp [partialSum,Complex.ofReal_exp]

/-- On the real axis, ordered convergence of a series with nonnegative
coefficients already gives absolute convergence. -/
theorem absConvergesAt_of_nonneg {σ : ℝ} (ha : ∀ n, 0 ≤ a n)
    (h : F.ConvergesAt (fun n => (a n : ℂ)) (σ : ℂ)) :
    F.AbsConvergesAt (fun n => (a n : ℂ)) (σ : ℂ) := by
  have H := Complex.continuous_re.continuousAt.tendsto.comp h.tendsto
  simp only [Function.comp_def,real_partialSum,Complex.ofReal_re] at H
  have hp (n) : 0 ≤ a n * Real.exp (-σ*F n) := mul_nonneg (ha n) (Real.exp_pos _).le
  have hs := ((hasSum_iff_tendsto_nat_of_nonneg hp _).mpr H).summable
  simpa only [F.absConvergesAt_iff, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha _),ofReal_re] using hs

/-- For nonnegative real coefficients the absolute and ordered abscissae coincide,
even for a frequency whose upper exponential density is infinite. -/
theorem absoluteAbscissa_eq_of_nonneg (ha : ∀ n, 0 ≤ a n) :
    F.absoluteAbscissa (fun n => (a n : ℂ)) = F.abscissa (fun n => (a n : ℂ)) := by
  refine le_antisymm (le_sInf ?_) (F.abscissa_le_absoluteAbscissa _)
  rintro _ ⟨σ,hσ,rfl⟩
  exact absoluteAbscissa_le_re (s := (σ : ℂ)) (absConvergesAt_of_nonneg ha hσ)

/-- The nonnegative Taylor contribution of a single frequency when continuing
from a real center `c` to a real point `x ≤ c`. -/
def taylorMoment (F : DirichletFrequency) (a : ℕ → ℝ) (c x : ℝ) (k n : ℕ) : ℝ :=
  a n * Real.exp (-c*F n) * (((c-x)*F n)^k / (k.factorial : ℝ))

theorem taylorMoment_nonneg (ha : ∀ n, 0 ≤ a n) {x c : ℝ} (hx : x ≤ c) (k n : ℕ) :
    0 ≤ F.taylorMoment a c x k n := by
  unfold taylorMoment
  exact mul_nonneg (mul_nonneg (ha n) (Real.exp_pos _).le)
    (div_nonneg (pow_nonneg (mul_nonneg (sub_nonneg.mpr hx) (F.nonneg n)) k) (Nat.cast_nonneg _))

/-- Summing over the frequencies gives the real Taylor coefficient, including
its displacement factor. The proof uses only ordered convergence in the open half-plane. -/
theorem hasSum_taylorMoment_frequency (ha : ∀ n, 0 ≤ a n) {x c : ℝ} (hx : x ≤ c)
    (hc : F.abscissa (fun n => (a n : ℂ)) < (c : EReal)) (k : ℕ) :
    HasSum (F.taylorMoment a c x k)
      (((k.factorial : ℂ)⁻¹ * ((x : ℂ)-c)^k) * iteratedDeriv k (F.sum (fun n => (a n : ℂ))) c).re := by
  let Z : ℂ := (k.factorial : ℂ)⁻¹ * ((x : ℂ)-c)^k
  have hterm (n : ℕ) :
      Z * (((-(F n : ℂ))^k * (a n : ℂ)) * Complex.exp (-(c : ℂ)*F n)) = (F.taylorMoment a c x k n : ℂ) := by
    have hp : ((x : ℂ)-c)^k * (-(F n : ℂ))^k = ((((c-x)*F n)^k : ℝ) : ℂ) := by
      rw [← mul_pow]
      push_cast
      congr 1
      ring
    have he : Complex.exp (-(c : ℂ)*F n) = (Real.exp (-c*F n) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; rfl
    unfold Z taylorMoment
    rw [he]
    push_cast at hp ⊢
    linear_combination ((k.factorial : ℂ)⁻¹ * (a n : ℂ) * Complex.exp (-(c : ℂ)*F n)) * hp
  have hP (N : ℕ) :
      Z * F.partialSum (fun n => (-(F n : ℂ))^k * (a n : ℂ)) c N =
      ((∑ n ∈ Finset.range N, F.taylorMoment a c x k n : ℝ) : ℂ) := by
    rw [partialSum,Finset.mul_sum,Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun n _ => hterm n
  have H := ((F.tendstoLocallyUniformlyOn_weighted_partialSum (fun n => (a n : ℂ)) k).tendsto_at
    (show F.abscissa (fun n => (a n : ℂ)) < ((c : ℂ).re : EReal) from hc)).const_mul Z
  apply (hasSum_iff_tendsto_nat_of_nonneg (taylorMoment_nonneg (F := F) ha hx k) _).mpr
  have HR := Complex.continuous_re.continuousAt.tendsto.comp H
  simpa only [Function.comp_def, hP, Complex.ofReal_re] using HR

/-- At a fixed frequency, summing the Taylor terms reproduces the original
positive exponential weight at the new point. -/
theorem hasSum_taylorMoment_degree (F : DirichletFrequency) (a : ℕ → ℝ) (c x : ℝ) (n : ℕ) :
    HasSum (fun k => F.taylorMoment a c x k n) (a n * Real.exp (-x*F n)) := by
  have he : HasSum (fun k : ℕ => ((c-x)*F n)^k / (k.factorial : ℝ)) (Real.exp ((c-x)*F n)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have H := he.mul_left (a n * Real.exp (-c*F n))
  rwa [mul_assoc, ← Real.exp_add, show -c*F n + (c-x)*F n = -x*F n by ring] at H

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
