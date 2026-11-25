import AnalyticNumberTheory.DirichletSeries.Convergence

/-! # Frequencies and partial sums of general Dirichlet series -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries

/-- A nonnegative, strictly increasing sequence of real exponents tending to infinity.
The first coefficient of the associated series has index zero. -/
structure DirichletFrequency where
  /-- The real exponent attached to each coefficient. -/
  exponent : ℕ → ℝ
  /-- The initial exponent is nonnegative, so all exponents are nonnegative. -/
  nonneg_zero : 0 ≤ exponent 0
  /-- Successive exponents are strictly increasing. -/
  strictMono : StrictMono exponent
  /-- Every finite height contains only finitely many exponents. -/
  tendsto_atTop : Tendsto exponent atTop atTop

namespace DirichletFrequency

instance : CoeFun DirichletFrequency (fun _ => ℕ → ℝ) := ⟨exponent⟩

variable (F : DirichletFrequency)

theorem nonneg (n : ℕ) : 0 ≤ F n :=
  F.nonneg_zero.trans (F.strictMono.monotone (Nat.zero_le n))

/-- The number of frequencies at most `u`, including a frequency equal to `u`. -/
def count (u : ℝ) : ℕ :=
  Nat.find ((F.tendsto_atTop.eventually_gt_atTop u).exists)

theorem lt_count_iff {n : ℕ} {u : ℝ} : n < F.count u ↔ F n ≤ u := by
  rw [count, Nat.lt_find_iff]
  exact ⟨fun h => le_of_not_gt (h n le_rfl), fun h m hm => not_lt.mpr ((F.strictMono.monotone hm).trans h)⟩

theorem monotone_count : Monotone F.count := by
  intro u v huv
  by_contra! h
  exact (Nat.lt_irrefl _) ((F.lt_count_iff).2 (((F.lt_count_iff).1 h).trans huv))

theorem count_eq_succ {u : ℝ} {n : ℕ} (hl : F n ≤ u) (hr : u < F (n+1)) :
    F.count u = n+1 := by
  have h₁ := (F.lt_count_iff).2 hl
  have h₂ : ¬ n+1 < F.count u := fun h => hr.not_ge ((F.lt_count_iff).1 h)
  omega

@[simp] theorem count_exponent (n : ℕ) : F.count (F n) = n+1 :=
  F.count_eq_succ le_rfl (F.strictMono (Nat.lt_succ_self n))

/-- The first `N` terms of the general Dirichlet series with coefficients `a`. -/
def partialSum (a : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * Complex.exp (-s * F n)

@[simp] theorem partialSum_succ (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    F.partialSum a s (n+1) = F.partialSum a s n + a n * Complex.exp (-s * F n) :=
  Finset.sum_range_succ _ _

/-- The frequency cutoff includes all terms with `λₙ ≤ u`. -/
def summatory (a : ℕ → ℂ) (s : ℂ) (u : ℝ) : ℂ :=
  F.partialSum a s (F.count u)

theorem measurable_summatory (a : ℕ → ℂ) (s : ℂ) : Measurable (F.summatory a s) :=
  (measurable_of_countable (F.partialSum a s)).comp F.monotone_count.measurable

/-- Ordered convergence of the series, including conditionally convergent values. -/
def ConvergesAt (a : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (F.partialSum a s) atTop (𝓝 L)

/-- The limit of the ordered partial sums, with value zero at a point of divergence. -/
def sum (a : ℕ → ℂ) (s : ℂ) : ℂ := by
  classical exact if h : F.ConvergesAt a s then h.choose else 0

theorem ConvergesAt.tendsto {F : DirichletFrequency} {a : ℕ → ℂ} {s : ℂ}
    (h : F.ConvergesAt a s) : Tendsto (F.partialSum a s) atTop (𝓝 (F.sum a s)) := by
  simpa only [sum, h, ↓reduceDIte] using h.choose_spec

/-- The abscissa of ordered convergence, allowing both infinite values. -/
def abscissa (a : ℕ → ℂ) : EReal :=
  sInf (Real.toEReal '' {x : ℝ | F.ConvergesAt a x})

/-- Logarithmic frequencies yield the ordinary Dirichlet series starting at one. -/
def logarithmic : DirichletFrequency where
  exponent n := Real.log (n+1 : ℕ)
  nonneg_zero := by simp
  strictMono := by
    intro m n h
    apply Real.log_lt_log (by positivity)
    exact_mod_cast Nat.succ_lt_succ h
  tendsto_atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-- With logarithmic frequencies, each finite partial sum agrees exactly with
the ordinary Dirichlet partial sum indexed from one. -/
theorem logarithmic_partialSum (a : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    logarithmic.partialSum (fun n => a (n+1)) s N = dirichletPartialSum a s N := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    rw [partialSum_succ, dirichletPartialSum_succ, ih, LSeries.term_of_ne_zero (Nat.succ_ne_zero _),
      div_eq_mul_inv, ← Complex.cpow_neg, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))]
    change _ + _ * Complex.exp (-s * (Real.log ((N+1 : ℕ) : ℝ) : ℂ)) = _
    rw [Complex.ofReal_log (by positivity : 0 ≤ ((N+1 : ℕ) : ℝ)), Complex.ofReal_natCast, mul_comm (-s)]

@[simp] theorem logarithmic_convergesAt (a : ℕ → ℂ) (s : ℂ) :
    logarithmic.ConvergesAt (fun n => a (n+1)) s ↔ DirichletConvergesAt a s := by
  simp only [ConvergesAt, DirichletConvergesAt, funext (logarithmic_partialSum a s)]

theorem logarithmic_sum (a : ℕ → ℂ) (s : ℂ) :
    logarithmic.sum (fun n => a (n+1)) s = dirichletSum a s := by
  by_cases h : DirichletConvergesAt a s
  · have H := ((logarithmic_convergesAt a s).2 h).tendsto
    rw [funext (logarithmic_partialSum a s)] at H
    exact tendsto_nhds_unique H h.tendsto
  · simp [sum, dirichletSum, logarithmic_convergesAt, h]

theorem logarithmic_abscissa (a : ℕ → ℂ) :
    logarithmic.abscissa (fun n => a (n+1)) = abscissaOfConvergence a := by
  simp only [abscissa, abscissaOfConvergence, logarithmic_convergesAt]

end DirichletFrequency
end AnalyticNumberTheory.DirichletSeries
