import AnalyticNumberTheory.PrimeDistribution.InghamRieszInversion
import AnalyticNumberTheory.PrimeDistribution.DirichletZeroDetector

/-! # Riesz inversion of a Möbius-mollified Dirichlet L-function -/
noncomputable section
open Complex Real Finset MeasureTheory
open scoped LSeries.notation ArithmeticFunction.Moebius ArithmeticFunction.zeta
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

/-- A Dirichlet L-function multiplied by its length-`X` Möbius mollifier. -/
def mollifiedLFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℕ) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ s * dirichletPoly (fun n => (μ n:ℂ)*χ n) X s

/-- Twisting preserves the gap in the detector coefficients and gives the
Dirichlet series for the mollified L-function on its half-plane of convergence. -/
theorem character_mollified_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℕ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (fun n : ℕ => χ n*inghamDetectorCoeff X n) s ∧
      LSeries (fun n : ℕ => χ n*inghamDetectorCoeff X n) s = mollifiedLFunction χ X s := by
  let c : ℕ → ℂ := fun n => χ n
  let m : ℕ → ℂ := mobiusCutoff X
  have ht (n : ℕ) : LSeries.term (c*m) s n =
      if n∈Icc 1 X then ((μ n:ℂ)*χ n)*(n:ℂ)^(-s) else 0 := by
    have h : LSeries.term (c*m) s n = c n*LSeries.term m s n := by
      by_cases hn : n=0
      · subst n; simp
      · simp [LSeries.term_of_ne_zero hn,mul_div_assoc]
    rw [h,show LSeries.term m s n=_ from mobiusCutoff_term X s n]
    split_ifs <;> simp [c] <;> ring
  have hm : LSeriesSummable (c*m) s := summable_of_ne_finset_zero (s:=Icc 1 X)
    (fun n hn => by rw [ht,ite_eq_right hn])
  have hM : LSeries (c*m) s = dirichletPoly (fun n => (μ n:ℂ)*χ n) X s := by
    rw [LSeries,tsum_eq_sum (s:=Icc 1 X) (fun n hn => by rw [ht,ite_eq_right hn])]
    exact sum_congr rfl (fun n hn => by rw [ht,ite_eq_left hn])
  have hcoef : (fun n : ℕ => χ n*inghamDetectorCoeff X n) = (c*m) ⍟ c := by
    change c*(↑(mobiusCutoff X*(ζ : ArithmeticFunction ℂ)) : ℕ → ℂ) = _
    rw [←ArithmeticFunction.coe_mul]
    have he : m ⍟ (1:ℕ → ℂ) = m ⍟ (↑(ζ : ArithmeticFunction ℂ) : ℕ → ℂ) := by
      apply LSeries.convolution_congr (fun _ => rfl)
      intro n hn
      simp [ArithmeticFunction.natCoe_apply,hn]
    change c*(m ⍟ _) = _
    rw [←he,←χ.mul_convolution_distrib m 1,mul_one]
  have hc : LSeriesSummable c s := χ.LSeriesSummable_of_one_lt_re hs
  rw [hcoef]
  exact ⟨hm.convolution hc,(LSeries_convolution' hm hc).trans (by
    rw [hM,show LSeries c s=_ from (χ.LFunction_eq_LSeries hs).symm,mul_comm];rfl)⟩

/-- The shifted Riesz kernel for a character, at any integral order. -/
def characterRieszKernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X k : ℕ)
    (ρ : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  mollifiedLFunction χ X (ρ+w)*(Y:ℂ)^w/rieszDenom k w

/-- The right vertical line of the character detector is absolutely integrable.
Its normalized integral is a finite, smoothly weighted character sum. -/
theorem character_riesz_inversion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X k : ℕ) (hk : 1≤k) {ρ : ℂ} (hρ : 0≤ρ.re) {Y : ℝ} (hY : 0<Y) :
    Integrable (fun t : ℝ => characterRieszKernel χ X k ρ Y (2+t*I)) ∧
    ((k.factorial:ℂ)/(2*π))*(∫ t : ℝ, characterRieszKernel χ X k ρ Y (2+t*I)) =
      ∑ n∈Icc 1 ⌊Y⌋₊, (χ n*inghamDetectorCoeff X n)*(n:ℂ)^(-ρ)*(inghamRieszWeight k Y n:ℂ) :=
  translated_riesz_inversion _ _ (character_mollified_series χ X) k hk hρ hY

end AnalyticNumberTheory.PrimeDistribution
