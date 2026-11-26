import AnalyticNumberTheory.DirichletSeries.FrequencyDensity

/-! # Explicit finite and infinite convergence abscissae -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a : ℕ → ℂ}

/-- Ordered convergence forces each weighted coefficient to tend to zero. -/
theorem ConvergesAt.tendsto_term_zero {s : ℂ} (h : F.ConvergesAt a s) :
    Tendsto (fun n => a n * Complex.exp (-s * F n)) atTop (𝓝 0) := by
  have hs := (h.tendsto.comp (tendsto_add_atTop_nat 1)).sub h.tendsto
  simpa only [Function.comp_def, partialSum_succ, add_sub_cancel_left, sub_self] using hs

/-- A Dirichlet polynomial has both abscissae equal to minus infinity for
every choice of frequency. -/
theorem abscissae_eq_bot_of_eventually_zero (h : ∀ᶠ n in atTop, a n = 0) :
    F.abscissa a = ⊥ ∧ F.absoluteAbscissa a = ⊥ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have ha (s : ℂ) : F.AbsConvergesAt a s := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    rw [hN n (Nat.le_of_not_gt (fun hlt => hn (Finset.mem_range.mpr hlt))), zero_mul]
  have habs : F.absoluteAbscissa a = ⊥ := by
    apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro y
    exact (absoluteAbscissa_le_re (ha ((y-1 : ℝ) : ℂ))).trans_lt
      (EReal.coe_lt_coe_iff.mpr (by simp))
  exact ⟨bot_unique ((F.abscissa_le_absoluteAbscissa a).trans habs.le), habs⟩

/-- On the integer frequencies the coefficients `exp(b(n+1))` give an
absolutely convergent geometric series precisely in `Re s > b`. -/
theorem geometric_absConvergesAt_iff (b : ℝ) (s : ℂ) :
    positiveIntegers.AbsConvergesAt (fun n => (Real.exp (b * positiveIntegers n) : ℂ)) s ↔ b < s.re := by
  rw [absConvergesAt_iff]
  have hm (n : ℕ) :
      ‖(Real.exp (b * positiveIntegers n) : ℂ)‖ * Real.exp (-s.re * positiveIntegers n) =
        Real.exp (((n+1 : ℕ) : ℝ) * (b-s.re)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    change b * ((n+1 : ℕ) : ℝ) + -s.re * ((n+1 : ℕ) : ℝ) = _
    ring
  simp only [hm]
  rw [summable_nat_add_iff (f := fun n : ℕ => Real.exp ((n : ℝ) * (b-s.re))) 1,
    Real.summable_exp_nat_mul_iff, sub_neg]

/-- Every finite real number occurs as the common ordered and absolute
abscissa of an explicit series with positive coefficients. -/
theorem geometric_abscissae (b : ℝ) :
    let a := fun n => (Real.exp (b * positiveIntegers n) : ℂ)
    positiveIntegers.abscissa a = (b : EReal) ∧ positiveIntegers.absoluteAbscissa a = (b : EReal) := by
  let a := fun n => (Real.exp (b * positiveIntegers n) : ℂ)
  have ha : positiveIntegers.absoluteAbscissa a = (b : EReal) := by
    apply le_antisymm
    · apply EReal.le_of_forall_lt_iff_le.mp
      intro t ht
      exact absoluteAbscissa_le_re ((geometric_absConvergesAt_iff b (t : ℂ)).mpr (EReal.coe_lt_coe_iff.mp ht))
    · apply le_sInf
      rintro _ ⟨t, ht, rfl⟩
      exact EReal.coe_le_coe_iff.mpr ((geometric_absConvergesAt_iff b (t : ℂ)).mp ht).le
  exact ⟨(positiveIntegers_absoluteAbscissa_eq a).symm.trans ha, ha⟩

/-- Coefficients `exp(λₙ²)` give a series converging nowhere, for every
frequency. Hence both abscissae are plus infinity. -/
theorem superexponential_abscissae (F : DirichletFrequency) :
    let a := fun n => (Real.exp ((F n)^2) : ℂ)
    F.abscissa a = ⊤ ∧ F.absoluteAbscissa a = ⊤ := by
  let a := fun n => (Real.exp ((F n)^2) : ℂ)
  have hdiv (s : ℂ) : ¬ F.ConvergesAt a s := by
    intro h
    have ht : ∀ᶠ n in atTop, ‖a n * Complex.exp (-s * F n)‖ < 1 :=
      h.tendsto_term_zero.norm.eventually_lt_const (by simp)
    obtain ⟨n, hn, hlarge⟩ := (ht.and (F.tendsto_atTop.eventually_ge_atTop s.re)).exists
    apply hn.not_ge
    simp only [a, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, ← Real.exp_add, Real.one_le_exp_iff]
    nlinarith [mul_nonneg (F.nonneg n) (sub_nonneg.mpr hlarge)]
  have hord : F.abscissa a = ⊤ := by
    simp [abscissa, hdiv]
  exact ⟨hord, top_unique (hord ▸ F.abscissa_le_absoluteAbscissa a)⟩

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
