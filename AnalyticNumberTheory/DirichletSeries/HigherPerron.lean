import AnalyticNumberTheory.DirichletSeries.PowerLogPerronKernel
import AnalyticNumberTheory.DirichletSeries.SmoothedPerron

/-! # Higher logarithmic and Riesz means for arbitrary Dirichlet frequencies -/

noncomputable section

open Complex MeasureTheory Finset

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- Arbitrary positive integral logarithmic smoothing of an absolutely
convergent general Dirichlet series. A frequency at the cutoff contributes zero. -/
theorem powerLogPerron_formula {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : 0 < σ)
    (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    (∫ t : ℝ, F.sum a ((σ : ℂ)+t*I) * powerLogPerronKernel k σ u t)/(2*Real.pi) =
      ∑ n ∈ range (F.count u), a n * (((u-F n : ℝ) : ℂ)^k / k.factorial) := by
  let w := fun v : ℝ => ((max v 0 : ℝ) : ℂ)^k / k.factorial
  have H := F.smoothedPerron_formula a (fun s => s^(k+1)) w h
    (integrable_powerLogPerronKernel hk hσ) (integral_powerLogPerronKernel hk hσ)
    (fun v hv => by simp [w, max_eq_right hv.le, zero_pow hk.ne']) u
  apply H.trans
  refine sum_congr rfl fun n hn => ?_
  simp only [w, max_eq_left (sub_nonneg.mpr (F.lt_count_iff.mp (mem_range.mp hn)))]

private lemma cpow_real_exp (v : ℝ) (s : ℂ) :
    ((Real.exp v : ℝ) : ℂ)^s = Complex.exp (s*v) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, mul_comm]

/-- The Riesz denominator transfers to a general frequency sequence with
weight `(1-exp(λₙ-u))^k/k!`. The cutoff can be any real number. -/
theorem rieszPerron_formula {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : 0 < σ)
    (h : F.AbsConvergesAt a (σ : ℂ)) (u : ℝ) :
    (∫ t : ℝ, F.sum a ((σ : ℂ)+t*I) * (Complex.exp (((σ : ℂ)+t*I)*u)/rieszDenom k ((σ : ℂ)+t*I))) /
      (2*Real.pi) = ∑ n ∈ range (F.count u), a n *
        (((1-Real.exp (F n-u) : ℝ) : ℂ)^k / k.factorial) := by
  let w := fun v : ℝ => if 0 ≤ v then (((1-Real.exp (-v) : ℝ) : ℂ)^k / k.factorial) else 0
  have hK (v : ℝ) : Integrable (fun t : ℝ => Complex.exp (((σ : ℂ)+t*I)*v)/rieszDenom k ((σ : ℂ)+t*I)) := by
    simpa only [cpow_real_exp] using integrable_cpow_div_rieszDenom hk (Real.exp_pos v) hσ
  have hw (v : ℝ) : (∫ t : ℝ, Complex.exp (((σ : ℂ)+t*I)*v)/rieszDenom k ((σ : ℂ)+t*I))/(2*Real.pi) = w v := by
    have H := rieszKernel_eq hk (Real.exp_pos v) hσ
    simp only [rieszKernel, cpow_real_exp, Real.one_le_exp_iff, ← Real.exp_neg,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] at H
    calc
      _ = (1/(2*Real.pi : ℂ)) * ∫ t : ℝ, Complex.exp (((σ : ℂ)+t*I)*v)/rieszDenom k ((σ : ℂ)+t*I) := by ring
      _ = _ := H
  rw [F.smoothedPerron_formula a (rieszDenom k) w h hK hw (fun v hv => by simp [w, not_le.mpr hv]) u]
  refine sum_congr rfl fun n hn => ?_
  simp only [w, ite_eq_left (sub_nonneg.mpr (F.lt_count_iff.mp (mem_range.mp hn))), neg_sub]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
