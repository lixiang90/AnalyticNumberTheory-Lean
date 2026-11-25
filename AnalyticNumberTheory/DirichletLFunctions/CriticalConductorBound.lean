import AnalyticNumberTheory.DirichletLFunctions.CriticalConductorIntegral
import AnalyticNumberTheory.RiemannZeta.HurwitzWeyl

/-!
# The joint critical-line convexity bound

For every Dirichlet character the critical value is bounded by an
absolute constant times `(q(1+|t|))^(1/4)`, including height zero.
-/

open Real Complex Set
open scoped ComplexConjugate
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem riemannZeta_critical_quarter :
    ∃ C : ℝ,0<C ∧ ∀ t : ℝ,‖riemannZeta ((1/2:ℂ)+t*I)‖≤C*(1+|t|)^(1/4:ℝ) := by
  obtain ⟨A,hA,H⟩ := RiemannZeta.riemannZeta_weyl_bound
  let s (t : ℝ) := (1/2:ℂ)+t*I
  have hcont : Continuous (fun t => riemannZeta (s t)) := continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_riemannZeta (by intro he; have := congrArg Complex.re he; norm_num [s] at this)).continuousAt.comp
      (by dsimp [s]; fun_prop)
  obtain ⟨u,_,hu⟩ := isCompact_Icc.exists_isMaxOn (f:=fun t => ‖riemannZeta (s t)‖)
    (nonempty_Icc.mpr (by linarith [Real.pi_pos] : -(2*π)≤2*π)) hcont.norm.continuousOn
  let B := ‖riemannZeta (s u)‖
  have hB : 0≤B := norm_nonneg _
  refine ⟨13*A+B,by positivity,?_⟩
  intro t
  have hd := Real.one_le_rpow (by linarith [abs_nonneg t] : 1≤1+|t|) (by norm_num : 0≤(1/4:ℝ))
  by_cases ht : 2*π≤|t|
  · have hT : 1≤|t| := by linarith [Real.pi_gt_three]
    have h₀ := zero_lt_one.trans_le hT
    have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h₀ (1/12:ℝ))
    rw [Real.log_rpow h₀] at hlog
    have hpow := Real.one_le_rpow hT (by norm_num : 0≤(1/12:ℝ))
    have hsum : 1+Real.log |t|≤13*|t|^(1/12:ℝ) := by linarith only [hlog,hpow]
    apply (H ht).trans
    apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    calc _ = 13*A*|t|^(1/4:ℝ) := by
              rw [show (1/4:ℝ)=1/6+1/12 by norm_num,Real.rpow_add h₀]; ring
         _ ≤ (13*A+B)*(1+|t|)^(1/4:ℝ) := by gcongr <;> linarith
  · have hh : ‖riemannZeta (s t)‖≤B := hu (abs_le.mp (le_of_not_ge ht))
    exact hh.trans ((le_mul_of_one_le_right hB hd).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))

/-- A log-free fourth-root bound uniform in the conductor and height for
all primitive Dirichlet characters. -/
theorem norm_LFunction_primitive_critical_quarter :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsPrimitive → ∀ t : ℝ,‖χ.LFunction ((1/2:ℂ)+t*I)‖≤C*((q:ℝ)*(1+|t|))^(1/4:ℝ) := by
  obtain ⟨A,hA,H⟩ := norm_completedLGaussianIntegral_critical
  obtain ⟨B,hB,HB⟩ := riemannZeta_critical_quarter
  refine ⟨A+B,by positivity,?_⟩
  intro q _ χ hχ t
  by_cases hq : 2≤q
  · let s := (1/2:ℂ)+t*I
    let s' := (1/2:ℂ)+(-t:ℝ)*I
    let G := ‖χ.gammaFactor s‖
    have hG : 0<G := norm_pos_iff.mpr (by
      rw [gammaFactor_eq_Gammaℝ]; apply Complex.Gammaℝ_ne_zero_of_re_pos; simp [s]; positivity)
    have hconj : ‖(star χ).gammaFactor s'‖=G := by
      dsimp only [G]
      rw [gammaFactor_eq_Gammaℝ,gammaFactor_eq_Gammaℝ,parityExp_star,
        show s'+(parityExp χ:ℂ)=conj (s+(parityExp χ:ℂ)) by simp only [s,s',map_add,map_mul,map_div₀,map_one,map_ofNat,map_natCast,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]; ring,
        Complex.Gammaℝ_conj,Complex.norm_conj]
    let X := ((q:ℝ)*(1+|t|))^(1/4:ℝ)
    have hX : (conductorLength q t)^(1/2:ℝ)=X := by
      dsimp [conductorLength,X]; rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by positivity)]; norm_num
    have hX' : (conductorLength q (-t))^(1/2:ℝ)=X := by simpa [conductorLength,abs_neg] using hX
    have hI := H χ t
    have hI' := H (star χ) (-t)
    change ‖completedLGaussianIntegral χ s (3/4)/χ.gammaFactor s‖≤_ at hI
    change ‖completedLGaussianIntegral (star χ) s' (3/4)/(star χ).gammaFactor s'‖≤_ at hI'
    rw [norm_div,hX] at hI
    rw [norm_div,hconj,hX'] at hI'
    have h1 := (div_le_iff₀ hG).mp hI
    have h2 := (div_le_iff₀ hG).mp hI'
    have hFE := completedL_gaussian_functional_equation hχ hq s (by norm_num : (0:ℝ)<3/4)
    rw [show 1-s=s' by dsimp [s,s']; push_cast; ring] at hFE
    have htri := norm_add_le (completedLGaussianIntegral χ s (3/4))
      ((q:ℂ)^(1/2-s)*χ.rootNumber*completedLGaussianIntegral (star χ) s' (3/4))
    rw [hFE,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
      norm_mul,norm_mul,Complex.norm_natCast_cpow_of_pos (by omega),norm_rootNumber_primitive hχ] at htri
    have hL := completedLFunction_eq_mul_gammaFactor χ (s:=s)
      (Or.inr (by omega)) (norm_pos_iff.mp hG)
    rw [hL,norm_mul,show ((1/2:ℂ)-s).re=0 by simp [s],Real.rpow_zero,one_mul,one_mul] at htri
    have hlow : 2*G*‖χ.LFunction s‖≤(2*π)*(‖χ.LFunction s‖*G) := by
      have hp : 1≤π := by linarith [Real.pi_gt_three]
      nlinarith only [mul_le_mul_of_nonneg_right hp (mul_nonneg (norm_nonneg (χ.LFunction s)) hG.le)]
    have hfinal : ‖χ.LFunction s‖≤A*X := by
      apply (le_of_mul_le_mul_right (a:=G) _ hG)
      nlinarith only [hlow,htri,h1,h2]
    exact hfinal.trans (mul_le_mul_of_nonneg_right (by linarith) (by dsimp [X]; positivity))
  · have hq' : q=1 := by have := NeZero.ne q; omega
    subst q
    rw [DirichletCharacter.LFunction_modOne_eq]
    simp only [Nat.cast_one,one_mul]
    exact (HB t).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- Joint critical-line convexity, with an absolute constant, valid for
all Dirichlet characters, every positive modulus, and every real height. -/
theorem norm_LFunction_critical_conductor_quarter :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖χ.LFunction ((1/2:ℂ)+t*I)‖≤C*((q:ℝ)*(1+|t|))^(1/4:ℝ) := by
  obtain ⟨A,hA,H⟩ := norm_LFunction_primitive_critical_quarter
  refine ⟨65536*A,by positivity,?_⟩
  intro q _ χ t
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd : 0<(χ.conductor:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  apply (norm_LFunction_le_conductor_quarter χ t).trans
  apply (mul_le_mul_of_nonneg_right (H χ.primitiveCharacter_isPrimitive t) (by positivity)).trans_eq
  rw [show A*((χ.conductor:ℝ)*(1+|t|))^(1/4:ℝ)*(65536*((q:ℝ)/χ.conductor)^(1/4:ℝ))=
      (65536*A)*(((χ.conductor:ℝ)*(1+|t|))^(1/4:ℝ)*((q:ℝ)/χ.conductor)^(1/4:ℝ)) by ring,
    ←Real.mul_rpow (by positivity) (by positivity),show (χ.conductor:ℝ)*(1+|t|)*((q:ℝ)/χ.conductor)=q*(1+|t|) by field_simp]

end AnalyticNumberTheory.DirichletLFunctions
