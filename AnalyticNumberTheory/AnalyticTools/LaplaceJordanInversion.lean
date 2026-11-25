import AnalyticNumberTheory.AnalyticTools.BromwichJordan
import Mathlib.Analysis.BoundedVariation

/-! # Laplace inversion on every line of absolute convergence

A real exponential weight moves the line of integration to a positive
abscissa. On compact intervals multiplication by this weight preserves
bounded variation, and the exponential factors cancel at the inversion point.
-/

noncomputable section
open MeasureTheory Filter Set Function Complex
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

private def tilt (k : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (k*u) * f u

private lemma damped_tilt (f : ℝ → ℝ) (σ c : ℝ) :
    laplaceDamped c (fun u : ℝ => (tilt (c-σ) f u : ℂ)) =
      laplaceDamped σ (fun u : ℝ => (f u : ℂ)) := by
  funext u
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · simp only [laplaceDamped, indicator_of_mem hu, tilt, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_sub]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · simp [laplaceDamped, hu]

private lemma bromwich_tilt (f : ℝ → ℝ) (σ c x T : ℝ) :
    truncatedBromwich (laplaceTransform (fun u : ℝ => (f u : ℂ))) σ x T =
      (Real.exp ((σ-c)*x) : ℂ) *
      truncatedBromwich (laplaceTransform (fun u : ℝ => (tilt (c-σ) f u : ℂ))) c x T := by
  simp_rw [truncatedBromwich_eq_fourier]
  rw [damped_tilt, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  congr 2
  ring

private lemma transfer_tilt {f : ℝ → ℝ} {σ c x : ℝ} {L : ℂ}
    (h : Tendsto (truncatedBromwich (laplaceTransform (fun u : ℝ => (tilt (c-σ) f u : ℂ))) c x)
      atTop (𝓝 ((Real.exp ((c-σ)*x) : ℂ) * L))) :
    Tendsto (truncatedBromwich (laplaceTransform (fun u : ℝ => (f u : ℂ))) σ x) atTop (𝓝 L) := by
  have H := h.const_mul (Real.exp ((σ-c)*x) : ℂ)
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    show (σ-c)*x + (c-σ)*x = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul] at H
  exact H.congr fun T => (bromwich_tilt f σ c x T).symm

private lemma variation_tilt {f : ℝ → ℝ} {a b k : ℝ} (hk : 0 ≤ k)
    (hf : BoundedVariationOn f (Icc a b)) : BoundedVariationOn (tilt k f) (Icc a b) := by
  have hm : Monotone (fun u : ℝ => Real.exp (k*u)) :=
    fun u v huv => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huv hk)
  have hw := (hm.monotoneOn (Icc a b)).boundedVariationOn (C := Real.exp (k*b))
    (fun u hu => by rw [abs_of_pos (Real.exp_pos _)]; exact hm hu.2)
  exact hw.mul hf

private lemma right_tilt {f : ℝ → ℝ} {a b x : ℝ} (k : ℝ)
    (hv : BoundedVariationOn f (Icc a b)) (hmem : Icc a b ∈ 𝓝[>] x) :
    rightLim (tilt k f) x = Real.exp (k*x) * rightLim f x := by
  obtain ⟨r,hr⟩ := hv.exists_tendsto_right x
  rw [nhdsWithin_inter_of_mem hmem] at hr
  rw [rightLim_eq_of_tendsto hr]
  have hc : Continuous (fun u : ℝ => Real.exp (k*u)) := by fun_prop
  exact rightLim_eq_of_tendsto (((hc.tendsto x).mono_left nhdsWithin_le_nhds).mul hr)

private lemma left_tilt {f : ℝ → ℝ} {a b x : ℝ} (k : ℝ)
    (hv : BoundedVariationOn f (Icc a b)) (hmem : Icc a b ∈ 𝓝[<] x) :
    leftLim (tilt k f) x = Real.exp (k*x) * leftLim f x := by
  obtain ⟨l,hl⟩ := hv.exists_tendsto_left x
  rw [nhdsWithin_inter_of_mem hmem] at hl
  rw [leftLim_eq_of_tendsto hl]
  have hc : Continuous (fun u : ℝ => Real.exp (k*u)) := by fun_prop
  exact leftLim_eq_of_tendsto (((hc.tendsto x).mono_left nhdsWithin_le_nhds).mul hl)

/-- The Bromwich–Jordan theorem at an interior point. Bounded variation is
required only on one neighborhood of x, and the abscissa is any real number
on which the exponentially weighted input is absolutely integrable. -/
theorem laplace_jordan_inversion {f : ℝ → ℝ} {a x b σ : ℝ} (ha : 0 ≤ a)
    (hax : a < x) (hxb : x < b) (hv : BoundedVariationOn f (Icc a b))
    (hf : Integrable (laplaceDamped σ (fun t : ℝ => (f t : ℂ)))) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (f t : ℂ))) σ x)
      atTop (𝓝 ((((leftLim f x : ℝ) : ℂ) + ((rightLim f x : ℝ) : ℂ)) / 2)) := by
  let c := max σ 0 + 1
  have hc : 0 < c := by dsimp [c]; linarith [le_max_right σ 0]
  have hk : 0 ≤ c-σ := by dsimp [c]; linarith [le_max_left σ 0]
  have hmem : Icc a b ∈ 𝓝 x := Icc_mem_nhds hax hxb
  have hI : Integrable (laplaceDamped c (fun u : ℝ => (tilt (c-σ) f u : ℂ))) := by
    rw [damped_tilt]; exact hf
  have H := laplace_inversion_boundedVariation_pos ha hax hxb (variation_tilt hk hv) hc hI
  apply transfer_tilt (f := f) (σ := σ) (c := c) (x := x)
  rw [left_tilt _ hv (mem_nhdsWithin_of_mem_nhds hmem),
      right_tilt _ hv (mem_nhdsWithin_of_mem_nhds hmem)] at H
  convert H using 2
  push_cast
  ring

/-- At the boundary of the positive half-line the inverse integral recovers
half the right limit on every line of absolute convergence. -/
theorem laplace_jordan_inversion_zero {f : ℝ → ℝ} {b σ : ℝ} (hb : 0 < b)
    (hv : BoundedVariationOn f (Icc 0 b)) (hf : Integrable (laplaceDamped σ (fun t : ℝ => (f t : ℂ)))) :
    Tendsto (truncatedBromwich (laplaceTransform (fun t : ℝ => (f t : ℂ))) σ 0)
      atTop (𝓝 (((rightLim f 0 : ℝ) : ℂ) / 2)) := by
  let c := max σ 0 + 1
  have hc : 0 < c := by dsimp [c]; linarith [le_max_right σ 0]
  have hk : 0 ≤ c-σ := by dsimp [c]; linarith [le_max_left σ 0]
  have hmem : Icc (0 : ℝ) b ∈ 𝓝[>] 0 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hb)]
      with u hu hu' using ⟨le_of_lt hu, hu'.le⟩
  have hI : Integrable (laplaceDamped c (fun u : ℝ => (tilt (c-σ) f u : ℂ))) := by
    rw [damped_tilt]; exact hf
  have H := laplace_inversion_boundedVariation_zero hb (variation_tilt hk hv) hc hI
  apply transfer_tilt (f := f) (σ := σ) (c := c) (x := 0)
  rw [right_tilt _ hv hmem] at H
  simpa using H

/-- For negative arguments, symmetric truncations of a one-sided Laplace
transform converge to zero on every line of absolute convergence. -/
theorem laplace_jordan_inversion_neg {f : ℝ → ℂ} {x σ : ℝ} (hx : x < 0)
    (hf : Integrable (laplaceDamped σ f)) :
    Tendsto (truncatedBromwich (laplaceTransform f) σ x) atTop (𝓝 0) := by
  have hD : laplaceDamped σ (0 : ℝ → ℂ) = 0 := by ext t; simp [laplaceDamped]
  have hZ : ∀ T, truncatedBromwich (laplaceTransform (0 : ℝ → ℂ)) σ x T = 0 := by
    intro T; simp [truncatedBromwich, laplaceTransform]
  have hnear : ∀ᶠ u in 𝓝 x, 0 < u → f u = (0 : ℝ → ℂ) u :=
    (gt_mem_nhds hx).mono fun u hu hn => (not_lt_of_ge hn.le hu).elim
  have h0 : Integrable (laplaceDamped σ (0 : ℝ → ℂ)) := by rw [hD]; exact integrable_zero ..
  simpa only [hZ, sub_zero] using truncatedBromwich_localization hf h0 hnear

end AnalyticNumberTheory.AnalyticTools
