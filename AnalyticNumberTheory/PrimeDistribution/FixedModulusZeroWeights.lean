import AnalyticNumberTheory.PrimeDistribution.PrimitiveConductorBlockSums

/-! # Weighted critical-strip zeros at one fixed modulus -/

noncomputable section

open Complex Finset
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- A zero sample records both the character modulo `q` and the zero.
Both signs of height and the principal character are included. -/
def modulusZeros (q : ℕ) (T : ℝ) : Finset (Σ _ : DirichletCharacter ℂ q, ℂ) :=
  univ.sigma (fun χ => characterStripZeros χ T)

/-- Sum of a real weight over all strip zeros of all characters modulo `q`,
with each zero counted according to its analytic multiplicity. -/
def modulusZeroWeight (q : ℕ) (T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ p ∈ modulusZeros q T, (characterZeroMultiplicity p.1 p.2 : ℝ)*f p.2

theorem modulusZeroWeight_eq_sum_characters (q : ℕ) (T : ℝ) (f : ℂ → ℝ) :
    modulusZeroWeight q T f = ∑ χ : DirichletCharacter ℂ q, characterZeroWeight χ T f := by
  rw [modulusZeroWeight, modulusZeros, sum_sigma]
  rfl

theorem modulusZeroWeight_tail {q : ℕ} [NeZero q] (σ T : ℝ) :
    modulusZeroWeight q T (fun z => if σ ≤ z.re then 1 else 0) = (modulusDensityCount q σ T : ℝ) := by
  simp only [modulusZeroWeight_eq_sum_characters, modulusDensityCount, Nat.cast_sum]
  apply sum_congr rfl
  intro χ _
  simp only [characterZeroWeight, characterStripZeros, characterZeroMultiplicity, characterDensityCount,
    dite_eq_left (NeZero.ne q), Nat.cast_sum, sum_filter, mul_ite, mul_one, mul_zero, Nat.cast_ite, Nat.cast_zero]

theorem modulusZeros_filter_height {q : ℕ} [NeZero q] {T U : ℝ} (h : U ≤ T) :
    (modulusZeros q T).filter (fun p => |p.2.im| ≤ U) = modulusZeros q U := by
  ext ⟨χ,z⟩
  simp only [modulusZeros, mem_filter, mem_sigma, mem_univ, true_and, mem_characterStripZeros, abs_le]
  constructor
  · rintro ⟨⟨ha,hb,_,_,he⟩,hc,hd⟩
    exact ⟨ha,hb,hc,hd,he⟩
  · rintro ⟨ha,hb,hc,hd,he⟩
    exact ⟨⟨ha,hb,by linarith,hd.trans h,he⟩,hc,hd⟩

end AnalyticNumberTheory.PrimeDistribution
