import AnalyticNumberTheory.AdditiveNumberTheory.PageCharacterExpansion
import AnalyticNumberTheory.PrimeDistribution.ReciprocalTotient

/-! # Doubly logarithmic estimates for rational Fourier coefficients -/

noncomputable section
open Real
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- At a reduced rational frequency the Gauss coefficient is at most
C log log(10q) sqrt(cond χ)/q, and hence at most C log log(10q)/sqrt q.
Both bounds use one constant, including imprimitive characters and q=1. -/
theorem rationalCharacterCoefficient_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a : ℕ}, a.Coprime q →
      ‖rationalCharacterCoefficient χ a‖ ≤ C*Real.log (Real.log (10*q))*Real.sqrt χ.conductor/q ∧
      ‖rationalCharacterCoefficient χ a‖ ≤ C*Real.log (Real.log (10*q))/Real.sqrt q := by
  obtain ⟨C,hC,H⟩ := div_totient_le_loglog
  refine ⟨C,hC,?_⟩
  intro q _ χ a ha
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  let W := C*Real.log (Real.log (10*q))
  have hφ : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hratio : (q : ℝ)/q.totient ≤ W := H (NeZero.pos _)
  have hW := (div_nonneg hq.le hφ.le).trans hratio
  have h₁ : ‖rationalCharacterCoefficient χ a‖ ≤ W*Real.sqrt χ.conductor/q := by
    apply (norm_rationalCharacterCoefficient_le_conductor χ ha).trans
    calc
      _ = ((q : ℝ)/q.totient)*(Real.sqrt χ.conductor/q) := by field_simp
      _ ≤ W*(Real.sqrt χ.conductor/q) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring
  refine ⟨h₁,h₁.trans ?_⟩
  have hdq : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  calc
    _ ≤ W*Real.sqrt q/q := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdq) hW) hq.le
    _ = W/Real.sqrt q := by
      apply (div_eq_div_iff hq.ne' (Real.sqrt_pos.mpr hq).ne').mpr
      rw [mul_assoc, ← sq, Real.sq_sqrt hq.le]

end AnalyticNumberTheory.AdditiveNumberTheory
