import AnalyticNumberTheory.DirichletLFunctions.PrimitiveApproximateFunctionalEquation
import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCosine
import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleEndpoints

/-!
# The elementary Hardy phase for a primitive character

The conductor contributes half the height times log q to Hardy's phase.
The Gauss sum and the sign of the character determine a constant unit.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Conductor-dependent elementary phase on the critical line. -/
def primitiveHardyPhase (q : ℕ) (t : ℝ) := hardyPhase t+t*Real.log q/2

/-- The constant phase in the elementary positive-height dual polynomial. -/
def primitiveHardyMultiplier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  (((Real.sqrt q)⁻¹:ℝ):ℂ)*gaussSum χ 1*conj (χ (-1))

theorem norm_primitiveHardyMultiplier {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖primitiveHardyMultiplier χ‖=1 := by
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  rw [primitiveHardyMultiplier,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    norm_gaussSum_one_of_isPrimitive hχ,Complex.norm_conj,χ.norm_neg_one,mul_one,inv_mul_cancel₀ (Real.sqrt_pos.mpr hq).ne']

private theorem riemann_phase {t : ℝ} (ht : 2≤t) :
    let E := (Circle.exp (hardyPhase t):ℂ)
    ‖E*riemannDualGamma (1/2+(t:ℂ)*I)-conj E‖≤8/t := by
  intro E
  let U := hardyGammaUnit t
  let G := riemannDualGamma (1/2+(t:ℂ)*I)
  have h : U*G=conj U := hardyUnit_mul_dualGamma (by linarith : t≠0)
  have hg := congrArg norm h
  rw [norm_mul,Complex.norm_conj,show ‖U‖=1 from norm_hardyGammaUnit t,one_mul] at hg
  have he : ‖U-E‖≤4/t := norm_hardyGammaUnit_sub_exp_le ht
  change ‖E*G-conj E‖≤_
  rw [show E*G-conj E=(E-U)*G+conj (U-E) by rw [map_sub,←h];ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,hg,mul_one,Complex.norm_conj,norm_sub_rev E U]
  calc _ ≤ 4/t+4/t := add_le_add he he
       _ = _ := by ring

/-- The reciprocal gamma factor, after rotation by the conductor phase,
differs from the conjugate rotation times a constant unit by O(1/t). -/
theorem primitive_gamma_phase_error {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {t : ℝ} (ht : 2≤t) :
    let E := (Circle.exp (primitiveHardyPhase q t):ℂ)
    ‖E*primitiveDualGamma χ ((1/2:ℂ)+t*I)-primitiveHardyMultiplier χ*conj E‖≤
      (8+2*Real.Gamma (1/2))/t := by
  intro E
  let s := (1/2:ℂ)+t*I
  let A := (Circle.exp (hardyPhase t):ℂ)
  let V := (Circle.exp (t*Real.log q/2):ℂ)
  let p := conj (χ (-1))
  let G := riemannDualGamma s
  let J := hurwitzDualMode s (-2*Real.pi)
  let z := (((Real.sqrt q)⁻¹:ℝ):ℂ)*gaussSum χ 1
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hV : ‖V‖=1 := Circle.norm_coe _
  have hA : ‖A‖=1 := Circle.norm_coe _
  have hp : ‖p‖=1 := (Complex.norm_conj _).trans χ.norm_neg_one
  have hz : ‖z‖=1 := by
    rw [show z=(((Real.sqrt q)⁻¹:ℝ):ℂ)*gaussSum χ 1 from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity),norm_gaussSum_one_of_isPrimitive hχ,inv_mul_cancel₀ (Real.sqrt_pos.mpr hq).ne']
  have hrot : E=A*V := by dsimp only [E,A,V,primitiveHardyPhase];rw [Circle.exp_add,Circle.coe_mul]
  have hc : V*(conj V*conj V)=conj V := by
    rw [←mul_assoc,Complex.mul_conj,←Complex.sq_norm,hV];norm_num
  have hQ : (q:ℂ)^(-s)=(((Real.sqrt q)⁻¹:ℝ):ℂ)*(conj V*conj V) := by
    rw [←Complex.ofReal_natCast,critical_monomial_eq hq]
    dsimp only [V,Circle.coe_exp];rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,←Complex.exp_add]
    congr 2;push_cast;ring
  have hγ : E*primitiveDualGamma χ s-primitiveHardyMultiplier χ*conj E=
      z*conj V*(p*(A*G-conj A)+(1-p)*(A*J)) := by
    rw [hrot,map_mul,primitiveDualGamma,hQ]
    change A*V*(((((Real.sqrt q)⁻¹:ℝ):ℂ)*(conj V*conj V))*gaussSum χ 1*
      (p*hurwitzDualMode s (2*Real.pi)+J))-(z*p)*(conj A*conj V)=_
    rw [show ∀ X Y : ℂ,A*V*(((((Real.sqrt q)⁻¹:ℝ):ℂ)*(conj V*conj V))*gaussSum χ 1*X)-Y=
        (V*(conj V*conj V))*(A*z*X)-Y by intros;dsimp [z];ring,hc]
    dsimp only [G,riemannDualGamma,J];ring
  have hG : ‖A*G-conj A‖≤8/t := riemann_phase ht
  have hJ : ‖J‖≤Real.Gamma (1/2)/t := by
    have ht₀ : 0<t := by linarith
    have hE : Real.exp (-(Real.pi/2*t))≤1/t := by
      rw [Real.exp_neg,one_div];apply inv_anti₀ ht₀
      linarith [Real.add_one_le_exp (Real.pi/2*t),mul_le_mul_of_nonneg_right (show 1≤Real.pi/2 by linarith [Real.pi_gt_three]) ht₀.le]
    have hΓ := Real.Gamma_pos_of_pos (by norm_num : 0<(1/2:ℝ))
    have H : ‖J‖≤Real.Gamma (1/2)*Real.exp (-(Real.pi/2*t)) := by
      simpa [J,hurwitzNegativeDual,hurwitzOmega,hurwitzShift,s,neg_mul] using
        norm_hurwitzNegativeDual_critical (s:=s) (by simp [s]) 0 1
    calc ‖J‖ ≤ Real.Gamma (1/2)*Real.exp (-(Real.pi/2*t)) := H
         _ ≤ Real.Gamma (1/2)*(1/t) := mul_le_mul_of_nonneg_left hE hΓ.le
         _ = Real.Gamma (1/2)/t := by ring
  change ‖E*primitiveDualGamma χ s-primitiveHardyMultiplier χ*conj E‖≤_
  rw [hγ,norm_mul,norm_mul,hz,Complex.norm_conj,hV,one_mul,one_mul]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul,norm_mul,hp,hA,one_mul,one_mul]
  have hp' := norm_sub_le (1:ℂ) p
  rw [norm_one,hp] at hp'
  apply (add_le_add hG (mul_le_mul hp' hJ (norm_nonneg _) (by norm_num))).trans_eq
  ring

end AnalyticNumberTheory.DirichletLFunctions
