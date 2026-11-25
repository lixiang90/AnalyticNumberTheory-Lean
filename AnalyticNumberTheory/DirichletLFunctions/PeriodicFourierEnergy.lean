import AnalyticNumberTheory.DirichletLFunctions.PrimitiveApproximateFunctionalEquation
import AnalyticNumberTheory.DirichletLFunctions.CharacterHarmonics

/-!
# Finite Fourier energy of periodic coefficients

The unitary normalization is convenient in the two critical-line
polynomials. The reciprocal polynomial carries the normalized discrete
Fourier transform, even when the coefficients form an imprimitive character.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- The discrete Fourier transform for counting measure, normalized to preserve
the sum of the squared coefficients. -/
def periodicDualWeight {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (k : ZMod q) : ℂ :=
  (((Real.sqrt q)⁻¹:ℝ):ℂ)*ZMod.dft Φ k

theorem periodicFourierCoeff_eq_dft {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (m : ℕ) :
    periodicFourierCoeff Φ (hurwitzOmega m)=ZMod.dft Φ ((m+1:ℕ):ZMod q) := by
  rw [periodicFourierCoeff,ZMod.dft_apply,sum_residues_succ]
  apply sum_congr rfl;intro r _
  have he : -(((r+1:ℕ):ZMod q)*((m+1:ℕ):ZMod q))=((-(r+1:ℕ)*(m+1:ℕ):ℤ):ZMod q) := by push_cast;ring
  rw [he,ZMod.stdAddChar_coe,smul_eq_mul]
  rw [mul_comm (Φ _)]
  apply congrArg (fun z : ℂ => z*Φ ((r+1:ℕ):ZMod q))
  unfold hurwitzShift
  apply congrArg Complex.exp
  dsimp [hurwitzOmega];push_cast;ring

private theorem conj_std {q : ℕ} [NeZero q] (x : ZMod q) :
    conj (ZMod.stdAddChar x)=ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]

/-- Parseval's identity for the unnormalized discrete Fourier transform. -/
theorem periodic_dft_parseval {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) :
    ∑k : ZMod q,‖ZMod.dft Φ k‖^2 = (q:ℝ)*∑r : ZMod q,‖Φ r‖^2 := by
  let F := ZMod.dft Φ
  have hinv (j : ZMod q) : ∑k : ZMod q,ZMod.stdAddChar (-(j*k))*conj (F k)=(q:ℂ)*conj (Φ j) := by
    have hh := congrFun (ZMod.dft_dft Φ) (-j)
    change ZMod.dft F (-j)=(q:ℂ) • Φ (- -j) at hh
    rw [ZMod.dft_apply,neg_neg,smul_eq_mul] at hh
    have h := congrArg conj hh
    simp only [map_sum,map_mul,Complex.conj_natCast,smul_eq_mul,conj_std,mul_neg,neg_neg] at h
    simpa only [mul_comm j] using h
  have he (k : ZMod q) : F k*conj (F k)=∑j : ZMod q,Φ j*(ZMod.stdAddChar (-(j*k))*conj (F k)) := by
    conv_lhs => lhs;rw [show F k=ZMod.dft Φ k from rfl,ZMod.dft_apply]
    rw [sum_mul];apply sum_congr rfl;intro j _;rw [smul_eq_mul];ring
  have H : (∑k : ZMod q,F k*conj (F k))=(q:ℂ)*∑j : ZMod q,Φ j*conj (Φ j) := by
    simp_rw [he];rw [sum_comm,mul_sum];apply sum_congr rfl;intro j _
    rw [←mul_sum,hinv];ring
  have hreal (z : ℂ) : (z*conj z).re=‖z‖^2 := by rw [Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
  have h := congrArg Complex.re H
  simpa only [Complex.re_sum,hreal,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] using h

/-- The reciprocal coefficient function has the same mean squared amplitude. -/
theorem periodicNormMean_dualWeight {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) :
    periodicNormMean (periodicDualWeight Φ)=periodicNormMean Φ := by
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hh (k : ZMod q) : ‖periodicDualWeight Φ k‖^2=(q:ℝ)⁻¹*‖ZMod.dft Φ k‖^2 := by
    rw [periodicDualWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),
      mul_pow,inv_pow,Real.sq_sqrt hq.le]
  simp only [periodicNormMean,hh,←mul_sum,periodic_dft_parseval,←mul_assoc,inv_mul_cancel₀ hq.ne',one_mul]

/-- For a character this is its Gauss sum at the negative frequency divided
by the square root of the modulus. Primitivity is unnecessary. -/
theorem periodicDualWeight_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ZMod q) :
    periodicDualWeight χ k=(((Real.sqrt q)⁻¹:ℝ):ℂ)*gaussSum χ (-k) := by
  rw [periodicDualWeight,dft_eq_gaussSum]

end AnalyticNumberTheory.DirichletLFunctions
