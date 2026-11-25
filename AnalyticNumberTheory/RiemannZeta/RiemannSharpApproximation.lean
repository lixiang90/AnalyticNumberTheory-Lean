import AnalyticNumberTheory.RiemannZeta.HurwitzApproximateFunctionalEquation

/-!
# Sharp two-sided approximation of Riemann zeta

At zero circle shift the representative a=1 turns the direct polynomial
into the ordinary sum over positive integers. The two reciprocal modes
have a common gamma multiplier independent of the frequency.
-/
noncomputable section
open Real Complex Finset Set
namespace AnalyticNumberTheory.RiemannZeta

/-- Symmetric gamma multiplier in the approximate functional equation. -/
def riemannDualGamma (s : ℂ) := hurwitzDualMode s (2*Real.pi)+hurwitzDualMode s (-2*Real.pi)

/-- Scaling a Fourier frequency by a positive real number factors out its Dirichlet monomial. -/
theorem hurwitzDualMode_scale (s : ℂ) (ω : ℝ) {v : ℝ} (hv : 0<v) :
    hurwitzDualMode s (v*ω)=(v:ℂ)^(s-1)*hurwitzDualMode s ω := by
  have hf : hurwitzFrequency (v*ω)=(v:ℂ)*hurwitzFrequency ω := by dsimp [hurwitzFrequency]; push_cast; ring
  have ha : (v:ℂ).arg+(hurwitzFrequency ω).arg∈Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hv.le,zero_add]
    exact ⟨Complex.neg_pi_lt_arg _,Complex.arg_le_pi _⟩
  rw [hurwitzDualMode,hurwitzDualMode,hf,Complex.mul_cpow ha]; ring

private theorem shift_one_omega (m : ℕ) :
    hurwitzShift 1 (hurwitzOmega m)=1 ∧ hurwitzShift 1 (-hurwitzOmega m)=1 := by
  have H := Complex.exp_nat_mul_two_pi_mul_I (m+1)
  have H' := Complex.exp_int_mul_two_pi_mul_I (-((m+1:ℕ):ℤ))
  constructor
  · convert H' using 1
    dsimp [hurwitzShift,hurwitzOmega]; congr 1; push_cast; ring
  · convert H using 1
    dsimp [hurwitzShift,hurwitzOmega]; congr 1; push_cast; ring

theorem hurwitzDualSum_one (s : ℂ) (y : ℝ) :
    hurwitzDualSum 1 y s = riemannDualGamma s*(∑ m∈range ⌊y⌋₊,((m:ℂ)+1)^(s-1)) := by
  rw [hurwitzDualSum,mul_sum]
  apply sum_congr rfl
  intro m hm
  simp only [hurwitzPair,(shift_one_omega m).1,(shift_one_omega m).2,one_mul]
  have h₁ : hurwitzOmega m=((m:ℝ)+1)*(2*Real.pi) := by dsimp [hurwitzOmega];ring
  have h₂ : -hurwitzOmega m=((m:ℝ)+1)*(-2*Real.pi) := by dsimp [hurwitzOmega];ring
  rw [h₂,h₁,hurwitzDualMode_scale s (2*Real.pi) (by positivity),hurwitzDualMode_scale s (-2*Real.pi) (by positivity)]
  dsimp [riemannDualGamma]; push_cast; ring

theorem hurwitzDirectSum_one (s : ℂ) {x : ℝ} (hx : 1≤x) :
    hurwitzDirectSum 1 x s = ∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(-s) := by
  have h : 1≤⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hx)
  rw [hurwitzDirectSum,Nat.floor_sub_one,Nat.range_eq_Icc_zero_sub_one _ (by omega)]
  simp

/-- Approximate functional equation at the actual zero shift. Both
polynomials enumerate the positive integers, with their respective real
cutoffs x and y. -/
theorem riemannZeta_sharp_afe {x y : ℝ} (hx : 2≤x) (hy : 2≤y) {s : ℂ}
    (hσ : 0<s.re) (hσ' : s.re<1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖riemannZeta s-(∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(-s))-
      riemannDualGamma s*(∑ m∈range ⌊y⌋₊,((m:ℂ)+1)^(s-1))‖ ≤
      256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt |s.im|) := by
  have H := hurwitzZeta_sharp_afe (a:=1) (by constructor <;>norm_num) hx hy hσ hσ' hxy
  rw [AddCircle.coe_period,HurwitzZeta.hurwitzZeta_zero,hurwitzDirectSum_one s (by linarith),hurwitzDualSum_one] at H
  exact H

/-- Rational parameters include the residue q itself, representing zero in
the additive circle. All parameters use the same numerical constant. -/
theorem hurwitzZeta_rational_sharp_afe {q j : ℕ} (hj : 1≤j) (hjq : j≤q) {x y : ℝ}
    (hx : 2≤x) (hy : 2≤y) {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) (hxy : |s.im|=2*Real.pi*x*y) :
    let a := (j:ℝ)/q
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a y s‖ ≤
      256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt |s.im|) := by
  have hq : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  have hj' : 0<(j:ℝ) := by exact_mod_cast (by omega : 0<j)
  exact hurwitzZeta_sharp_afe ⟨div_pos hj' hq,(div_le_one hq).mpr (by exact_mod_cast hjq)⟩ hx hy hσ hσ' hxy

end AnalyticNumberTheory.RiemannZeta
