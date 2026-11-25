import AnalyticNumberTheory.DirichletSeries.FrequencyDensity

/-! # Removing a finite prefix of a general Dirichlet series -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency) (a : ℕ → ℂ)

/-- After the cutoff, the original partial sum splits into the finite prefix
and the series with its first coefficients set to zero. -/
theorem partialSum_tail_add_prefix (s : ℂ) {N M : ℕ} (hNM : N ≤ M) :
    F.partialSum ((Ici N).indicator a) s M + F.partialSum a s N = F.partialSum a s M := by
  induction M, hNM using Nat.le_induction with
  | base =>
    have hz : F.partialSum ((Ici N).indicator a) s N = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hlt : ¬ N ≤ n := not_le.mpr (Finset.mem_range.mp hn)
      simp [hlt]
    rw [hz,zero_add]
  | succ M hM ih =>
    rw [F.partialSum_succ,F.partialSum_succ,indicator_of_mem hM a]
    linear_combination ih

theorem convergesAt_tail_iff (s : ℂ) (N : ℕ) :
    F.ConvergesAt ((Ici N).indicator a) s ↔ F.ConvergesAt a s := by
  constructor
  · rintro ⟨L,hL⟩
    refine ⟨L+F.partialSum a s N, (hL.add_const _).congr' ?_⟩
    filter_upwards [eventually_ge_atTop N] with M hM using F.partialSum_tail_add_prefix a s hM
  · rintro ⟨L,hL⟩
    refine ⟨L-F.partialSum a s N, (hL.sub_const _).congr' ?_⟩
    filter_upwards [eventually_ge_atTop N] with M hM
    exact (eq_sub_of_add_eq (F.partialSum_tail_add_prefix a s hM)).symm

/-- The tail sum is obtained by subtracting the finite Dirichlet polynomial
at every point of ordered convergence. -/
theorem sum_tail_eq_sub {s : ℂ} (h : F.ConvergesAt a s) (N : ℕ) :
    F.sum ((Ici N).indicator a) s = F.sum a s - F.partialSum a s N := by
  refine tendsto_nhds_unique ((F.convergesAt_tail_iff a s N).2 h).tendsto ((h.tendsto.sub_const _).congr' ?_)
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (eq_sub_of_add_eq (F.partialSum_tail_add_prefix a s hM)).symm

theorem abscissa_tail (N : ℕ) : F.abscissa ((Ici N).indicator a) = F.abscissa a := by
  simp only [abscissa,F.convergesAt_tail_iff]

theorem absConvergesAt_tail_iff (s : ℂ) (N : ℕ) :
    F.AbsConvergesAt ((Ici N).indicator a) s ↔ F.AbsConvergesAt a s := by
  change Summable (fun n => (Ici N).indicator a n * Complex.exp (-s*F n)) ↔
    Summable (fun n => a n * Complex.exp (-s*F n))
  rw [← summable_nat_add_iff N (f := fun n => (Ici N).indicator a n * Complex.exp (-s*F n)),
    ← summable_nat_add_iff N (f := fun n => a n * Complex.exp (-s*F n))]
  simp [Set.indicator_of_mem]

theorem absoluteAbscissa_tail (N : ℕ) :
    F.absoluteAbscissa ((Ici N).indicator a) = F.absoluteAbscissa a := by
  simp only [absoluteAbscissa,F.absConvergesAt_tail_iff]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
