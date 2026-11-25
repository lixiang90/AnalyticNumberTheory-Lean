import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximateFunctionalEquation
import AnalyticNumberTheory.DirichletLFunctions.GaussSums

/-!
# The reciprocal polynomial of a primitive Dirichlet character

At integral frequencies the Fourier transform is a Gauss sum. For a
primitive character it is the Gauss sum at one times the conjugate
character. Both frequency signs have the same reciprocal polynomial.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

theorem periodicFourierCoeff_int {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℤ) :
    periodicFourierCoeff χ (-2*Real.pi*k) = gaussSum χ (k:ZMod q) := by
  rw [periodicFourierCoeff,gaussSum,_root_.gaussSum,sum_residues_succ]
  apply sum_congr rfl
  intro r hr
  rw [AddChar.mulShift_apply,show (k:ZMod q)*((r+1:ℕ):ZMod q)=((k*((r+1:ℕ):ℤ):ℤ):ZMod q) by push_cast;ring,
    ZMod.stdAddChar_coe]
  dsimp [hurwitzShift];push_cast;congr 2;ring

theorem periodicFourierCoeff_omega {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) :
    periodicFourierCoeff χ (hurwitzOmega m)=gaussSum χ (-((m+1:ℕ):ZMod q)) ∧
      periodicFourierCoeff χ (-hurwitzOmega m)=gaussSum χ ((m+1:ℕ):ZMod q) := by
  constructor
  · convert periodicFourierCoeff_int χ (-((m+1:ℕ):ℤ)) using 1 <;> dsimp [hurwitzOmega] <;> push_cast <;> ring
  · convert periodicFourierCoeff_int χ ((m+1:ℕ):ℤ) using 1 <;> dsimp [hurwitzOmega] <;> push_cast <;> ring

/-- Functional-equation gamma factor of a primitive character, in the
two-frequency convention used for Hurwitz zeta. -/
def primitiveDualGamma {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :=
  (q:ℂ)^(-s)*gaussSum χ 1*
    (conj (χ (-1))*hurwitzDualMode s (2*Real.pi)+hurwitzDualMode s (-2*Real.pi))

/-- The reciprocal polynomial uses the conjugate character, with the
parity and Gauss sum absorbed into its single gamma multiplier. -/
theorem periodicDualSum_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (s : ℂ) (y : ℝ) : periodicDualSum χ y s=primitiveDualGamma χ s*
      (∑ m∈range ⌊y⌋₊,conj (χ ((m+1:ℕ):ZMod q))*((m:ℂ)+1)^(s-1)) := by
  unfold periodicDualSum primitiveDualGamma
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro m hm
  obtain ⟨h₁,h₂⟩ := periodicFourierCoeff_omega χ m
  rw [h₁,h₂,gaussSum_eq_star_mul_of_isPrimitive hχ (-((m+1:ℕ):ZMod q)),gaussSum_eq_star_mul_of_isPrimitive hχ ((m+1:ℕ):ZMod q)]
  rw [show -((m+1:ℕ):ZMod q)=(-1)*((m+1:ℕ):ZMod q) by ring,map_mul,star_mul']
  have hpos : 0<(m:ℝ)+1 := by positivity
  have hω : hurwitzOmega m=((m:ℝ)+1)*(2*Real.pi) := by dsimp [hurwitzOmega];ring
  have hω' : -hurwitzOmega m=((m:ℝ)+1)*(-2*Real.pi) := by dsimp [hurwitzOmega];ring
  rw [hω',hω,hurwitzDualMode_scale _ _ hpos,hurwitzDualMode_scale _ _ hpos]
  change _ = _
  simp only [←Complex.star_def]
  push_cast; ring

/-- Primitive-character sharp approximate functional equation in
conjugate-character form. -/
theorem primitiveLFunction_sharp_afe {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {x y : ℝ} (hx : 2≤x) (hy : 2≤y) {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖χ.LFunction s-dirichletPoly (fun n : ℕ => χ n) ⌊(q:ℝ)*x⌋₊ s-
      primitiveDualGamma χ s*(∑ m∈range ⌊y⌋₊,conj (χ ((m+1:ℕ):ZMod q))*((m:ℂ)+1)^(s-1))‖ ≤
      (q:ℝ)^(1-s.re)*(256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt |s.im|)) := by
  rw [←periodicDualSum_primitive hχ]; exact dirichletLFunction_sharp_afe χ hx hy hσ hσ' hxy

end AnalyticNumberTheory.DirichletLFunctions
