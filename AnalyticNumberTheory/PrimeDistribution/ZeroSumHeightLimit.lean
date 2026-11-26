import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula
import AnalyticNumberTheory.RiemannZeta.HadamardProduct

/-! # Height exhaustion and conjugation of critical-strip zeros -/

noncomputable section

open Filter Finset Complex
open scoped Topology Classical ComplexConjugate
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The distinct nontrivial zeros up to a symmetric height, as a finite set inside the zero type. -/
def criticalStripZerosUpTo (T : ℝ) : Finset CriticalStripZeros :=
  (nontrivialZerosUpTo T).subtype (· ∈ CriticalStripZeros)

/-- Membership in a height cutoff within the critical-strip zero type depends only on the ordinate. -/
theorem mem_criticalStripZerosUpTo {z : CriticalStripZeros} {T : ℝ} :
    z ∈ criticalStripZerosUpTo T ↔ |(z:ℂ).im| ≤ T := by
  obtain ⟨hz,h₀,h₁⟩ := mem_criticalStripZeros.mp z.property
  simp only [criticalStripZerosUpTo,Finset.mem_subtype,mem_nontrivialZerosUpTo,hz,h₀,h₁,true_and]

/-- Every absolutely summable family indexed by distinct nontrivial zeros can be summed
by symmetric height cutoffs. The function may include a multiplicity weight. -/
theorem tendsto_sum_nontrivialZerosUpTo_of_summable {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Summable fun z : CriticalStripZeros => f z) :
    Tendsto (fun T => ∑ z ∈ nontrivialZerosUpTo T, f z) atTop (𝓝 (∑' z : CriticalStripZeros, f z)) := by
  have h : Tendsto criticalStripZerosUpTo atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro T U hTU z hz
      exact mem_criticalStripZerosUpTo.mpr ((mem_criticalStripZerosUpTo.mp hz).trans hTU)
    · exact fun z => ⟨|(z : ℂ).im|,mem_criticalStripZerosUpTo.mpr le_rfl⟩
  apply (hf.hasSum.comp h).congr
  intro T
  apply sum_subtype_of_mem
  intro z hz
  obtain ⟨h,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
  exact mem_criticalStripZeros.mpr ⟨h,h₀,h₁⟩

/-- Conjugation preserves each symmetric height cutoff, even at an included boundary ordinate. -/
theorem conj_mem_nontrivialZerosUpTo_iff {T : ℝ} {z : ℂ} :
    conj z ∈ nontrivialZerosUpTo T ↔ z ∈ nontrivialZerosUpTo T := by
  simp only [mem_nontrivialZerosUpTo,riemannZeta_conj,Complex.conj_re,Complex.conj_im,abs_neg,map_eq_zero]

/-- A function odd under conjugation has weighted sum zero at each symmetric height.
The multiplicity at a zero agrees with that at its conjugate. -/
theorem sum_zeroMultiplicity_eq_zero_of_conj_odd (T : ℝ) (f : ℂ → ℂ)
    (hf : ∀ z ∈ nontrivialZerosUpTo T, f (conj z) = -f z) :
    ∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*f z = 0 := by
  let S := nontrivialZerosUpTo T
  let m (z : ℂ) : ℂ := zeroMultiplicity z
  have h : ∑ z ∈ S, m z*f z = ∑ z ∈ S, -(m z*f z) := by
    refine sum_bij' (fun z _ => conj z) (fun z _ => conj z)
      (fun _ hz => conj_mem_nontrivialZerosUpTo_iff.mpr hz) (fun _ hz => conj_mem_nontrivialZerosUpTo_iff.mpr hz)
      (fun _ _ => Complex.conj_conj _) (fun _ _ => Complex.conj_conj _) ?_
    intro z hz
    obtain ⟨_,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
    have hm : m (conj z) = m z := congrArg (fun n : ℕ => (n:ℂ)) (analyticOrderNatAt_riemannZeta_star h₀ h₁)
    rw [hm,hf z hz,mul_neg,neg_neg]
  rw [sum_neg_distrib] at h
  change ∑ z ∈ S, m z*f z = 0
  linear_combination (1/2 : ℂ) * h

end AnalyticNumberTheory.PrimeDistribution
