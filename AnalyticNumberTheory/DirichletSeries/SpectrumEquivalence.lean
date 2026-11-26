import AnalyticNumberTheory.DirichletSeries.CahenAbsolute
import AnalyticNumberTheory.DirichletSeries.FrequencySpectrum

/-! # Changing frequency sequences without changing a Dirichlet series -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F G : DirichletFrequency} {a b : ℕ → ℂ}

/-- Equal coefficient functions on the real exponents give identical
frequency-cutoff sums, even if zero terms alter the index of a cutoff. -/
theorem summatory_eq_of_coefficientAt_eq (he : F.coefficientAt a = G.coefficientAt b) (s : ℂ) (u : ℝ) :
    F.summatory a s u = G.summatory b s u := by
  classical
  let S := F.exponentsThrough u ∪ G.exponentsThrough u
  have hu (v : ℝ) (hv : v ∈ S) : v ≤ u :=
    (Finset.mem_union.mp hv).elim (fun h => (F.mem_exponentsThrough.mp h).1)
      (fun h => (G.mem_exponentsThrough.mp h).1)
  rw [F.summatory_eq_sum_coefficientAt a (S := S) Finset.subset_union_left hu,
    G.summatory_eq_sum_coefficientAt b (S := S) Finset.subset_union_right hu, he]

private lemma tendsto_partialSum_iff_of_coefficientAt_eq (he : F.coefficientAt a = G.coefficientAt b)
    (s L : ℂ) : Tendsto (F.partialSum a s) atTop (𝓝 L) ↔ Tendsto (G.partialSum b s) atTop (𝓝 L) := by
  rw [← F.tendsto_summatory_iff a, ← G.tendsto_summatory_iff b,
    funext (summatory_eq_of_coefficientAt_eq he s)]

/-- Ordered convergence at each complex point is invariant under changes
of frequency sequence that preserve the coefficient at each real exponent. -/
theorem convergesAt_iff_of_coefficientAt_eq (he : F.coefficientAt a = G.coefficientAt b) (s : ℂ) :
    F.ConvergesAt a s ↔ G.ConvergesAt b s :=
  exists_congr (tendsto_partialSum_iff_of_coefficientAt_eq he s)

/-- Two representations with the same coefficients at the real exponents
define the same sum function on the whole plane, with the usual default at
points of divergence. -/
theorem sum_eq_of_coefficientAt_eq (he : F.coefficientAt a = G.coefficientAt b) : F.sum a = G.sum b := by
  funext s
  by_cases h : F.ConvergesAt a s
  · exact tendsto_nhds_unique ((tendsto_partialSum_iff_of_coefficientAt_eq he s _).mp h.tendsto)
      (((convergesAt_iff_of_coefficientAt_eq he s).mp h).tendsto)
  · have hG := mt (convergesAt_iff_of_coefficientAt_eq he s).mpr h
    simp [sum, h, hG]

/-- Both convergence abscissae depend only on the coefficients attached to
the real exponents. Inserting or removing zero terms therefore preserves both. -/
theorem abscissae_eq_of_coefficientAt_eq (he : F.coefficientAt a = G.coefficientAt b) :
    F.abscissa a = G.abscissa b ∧ F.absoluteAbscissa a = G.absoluteAbscissa b := by
  have hord {c d : ℕ → ℂ} (h : F.coefficientAt c = G.coefficientAt d) : F.abscissa c = G.abscissa d := by
    simp only [abscissa, convergesAt_iff_of_coefficientAt_eq h]
  have hnorm (K : DirichletFrequency) (c : ℕ → ℂ) (u : ℝ) :
      K.coefficientAt (fun n => (‖c n‖ : ℂ)) u = (‖K.coefficientAt c u‖ : ℂ) := by
    by_cases hu : u ∈ Set.range K.exponent
    · obtain ⟨n, rfl⟩ := hu
      simp
    · simp [K.coefficientAt_of_notMem_range _ hu]
  refine ⟨hord he, ?_⟩
  rw [F.absoluteAbscissa_eq_abscissa_norm a, G.absoluteAbscissa_eq_abscissa_norm b]
  apply hord
  funext u
  rw [hnorm, hnorm, he]

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
