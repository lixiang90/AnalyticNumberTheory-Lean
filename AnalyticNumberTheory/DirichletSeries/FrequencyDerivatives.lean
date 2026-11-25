import AnalyticNumberTheory.DirichletSeries.FrequencyDensity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Termwise derivatives of general Dirichlet series -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- Differentiating a partial sum multiplies each coefficient by the negative
of its frequency. The formula includes an arbitrary number of existing factors. -/
theorem hasDerivAt_weighted_partialSum (k N : ℕ) (s : ℂ) :
    HasDerivAt (fun z => F.partialSum (fun n => (-(F n : ℂ))^k * a n) z N)
      (F.partialSum (fun n => (-(F n : ℂ))^(k+1) * a n) s N) s := by
  unfold partialSum
  apply HasDerivAt.fun_sum
  intro n _
  have H := (((hasDerivAt_neg s).mul_const (F n : ℂ)).cexp).const_mul ((-(F n : ℂ))^k * a n)
  apply H.congr_deriv
  simp only [pow_succ]
  ring

/-- Every termwise derivative converges locally uniformly on the original open
half-plane of ordered convergence, with limit equal to the analytic derivative. -/
theorem tendstoLocallyUniformlyOn_weighted_partialSum (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N s => F.partialSum (fun n => (-(F n : ℂ))^k * a n) s N)
      (iteratedDeriv k (F.sum a)) atTop {s : ℂ | F.abscissa a < (s.re : EReal)} := by
  have hU : IsOpen {s : ℂ | F.abscissa a < (s.re : EReal)} :=
    isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)
  induction k with
  | zero => simpa using F.tendstoLocallyUniformlyOn_partialSum a
  | succ k ih =>
    have hdiff (N : ℕ) : Differentiable ℂ (fun s => F.partialSum (fun n => (-(F n : ℂ))^k*a n) s N) :=
      fun s => (F.hasDerivAt_weighted_partialSum a k N s).differentiableAt
    have H := ih.deriv (.of_forall fun N => (hdiff N).differentiableOn) hU
    have he : (deriv ∘ fun N s => F.partialSum (fun n => (-(F n : ℂ))^k*a n) s N) =
        (fun N s => F.partialSum (fun n => (-(F n : ℂ))^(k+1)*a n) s N) := by
      funext N s
      exact (F.hasDerivAt_weighted_partialSum a k N s).deriv
    rwa [he, ← iteratedDeriv_succ] at H

/-- On the open half-plane of convergence the `k`-th derivative has the
coefficients `(-λₙ)^k aₙ`. -/
theorem iteratedDeriv_sum {s : ℂ} (hs : F.abscissa a < (s.re : EReal)) (k : ℕ) :
    iteratedDeriv k (F.sum a) s = F.sum (fun n => (-(F n : ℂ))^k * a n) s := by
  have H := (F.tendstoLocallyUniformlyOn_weighted_partialSum a k).tendsto_at hs
  have hc : F.ConvergesAt (fun n => (-(F n : ℂ))^k*a n) s := ⟨_,H⟩
  exact tendsto_nhds_unique H hc.tendsto

/-- Multiplying the coefficients by a power of the negative frequency does not
increase the abscissa of ordered convergence. -/
theorem abscissa_frequencyPower_le (k : ℕ) :
    F.abscissa (fun n => (-(F n : ℂ))^k * a n) ≤ F.abscissa a := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro t ht
  exact abscissa_le_re (s := (t : ℂ)) ⟨_,(F.tendstoLocallyUniformlyOn_weighted_partialSum a k).tendsto_at ht⟩

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
