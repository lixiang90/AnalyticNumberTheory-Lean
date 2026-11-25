import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation

/-!
# Removing the possible pole of a Dirichlet L-function

The extension of (s−1)L(s,χ) to the full plane has polynomial growth
throughout the strip used by the smoothed character large sieve. Its
value at one vanishes except for the principal character.
-/
noncomputable section
open Real Complex Finset
open scoped Classical
namespace AnalyticNumberTheory.DirichletLFunctions

private def principalFactors (q : ℕ) (s : ℂ) := ∏p∈q.primeFactors,(1-(p:ℂ)^(-s))

/-- The entire extension of (s−1)L(s,χ). -/
def poleClearedLFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  if χ=1 then principalFactors q s*riemannZeta₁ s else (s-1)*χ.LFunction s

theorem poleClearedLFunction_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s≠1) : poleClearedLFunction χ s=(s-1)*χ.LFunction s := by
  unfold poleClearedLFunction;split_ifs with h
  · subst χ
    rw [LFunction_one_eq_mul_riemannZeta hs,riemannZeta_eq_inv_sub_mul hs]
    unfold principalFactors;field_simp [sub_ne_zero.mpr hs]
  · rfl

private theorem analyticAt_principalFactors (q : ℕ) (s : ℂ) : AnalyticAt ℂ (principalFactors q) s := by
  unfold principalFactors
  rw [←Finset.prod_fn q.primeFactors (fun p (z:ℂ) => 1-(p:ℂ)^(-z))]
  apply Finset.analyticAt_prod
  intro p hp
  apply analyticAt_const.sub
  have h : (p:ℂ)≠0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (show Differentiable ℂ (fun z : ℂ => (p:ℂ)^(-z)) from differentiable_id.neg.const_cpow (.inl h)).analyticAt s

theorem analyticAt_poleClearedLFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    AnalyticAt ℂ (poleClearedLFunction χ) s := by
  change AnalyticAt ℂ (fun z => poleClearedLFunction χ z) s
  by_cases h : χ=1
  · simp only [poleClearedLFunction,if_pos h]
    exact (analyticAt_principalFactors q s).mul (differentiable_riemannZeta₁.analyticAt s)
  · simp only [poleClearedLFunction,if_neg h]
    exact (analyticAt_id.sub analyticAt_const).mul ((differentiable_LFunction_of_ne_one h).analyticAt s)

/-- The absolute residue of L(s,χ) is at most 1 for the principal character
and is zero for nonprincipal characters. -/
theorem norm_poleClearedLFunction_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖poleClearedLFunction χ 1‖ ≤ if χ=1 then 1 else 0 := by
  by_cases h : χ=1
  · simp only [poleClearedLFunction,if_pos h,riemannZeta₁,sub_self,zero_mul,add_zero,mul_one,principalFactors,norm_prod]
    apply prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro p hp
    have hpr : (1:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Complex.cpow_neg_one,←Complex.ofReal_natCast,←Complex.ofReal_inv,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [inv_le_one_of_one_le₀ hpr],by linarith [inv_nonneg.mpr (by positivity : 0≤(p:ℝ))]⟩
  · simp [poleClearedLFunction,h]

/-- A cubic polynomial bound on a fixed vertical strip, including the pole of L. -/
theorem poleClearedLFunction_strip_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃B : ℝ,0≤B ∧ ∀s : ℂ, s.re∈Set.Icc (-1/2:ℝ) 2 →
      ‖poleClearedLFunction χ s‖≤ B*(1+|s.im|)^3 := by
  by_cases h : χ=1
  · let E := ∏p∈q.primeFactors,(1+(p:ℝ)^(1/2:ℝ))
    have hE : 0≤E := prod_nonneg fun p _ => by positivity
    refine ⟨80*E,by positivity,?_⟩
    intro s hs
    simp only [poleClearedLFunction,if_pos h,norm_mul]
    have he : ‖principalFactors q s‖ ≤ E := by
      rw [principalFactors,norm_prod]
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      have hb := Nat.prime_of_mem_primeFactors hp
      apply (norm_sub_le ..).trans
      rw [norm_one,Complex.norm_natCast_cpow_of_pos hb.pos,neg_re]
      exact add_le_add_right (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb.one_le) (by linarith [hs.1])) _
    have hz := norm_riemannZeta₁_strip_poly_le (s:=s) (by linarith [hs.1]) hs.2
    have hp := pow_le_pow_left₀ (by positivity : 0≤|s.im|+2)
      (by linarith [abs_nonneg s.im] : |s.im|+2≤2*(1+|s.im|)) 3
    calc _ ≤ E*(10*(2*(1+|s.im|))^3) := mul_le_mul he (hz.trans (by gcongr)) (norm_nonneg _) hE
         _ = _ := by ring
  · let A := (q:ℝ)+48*q^2
    have hA : 0≤A := by dsimp [A];positivity
    refine ⟨16*A,by positivity,?_⟩
    intro s hs
    simp only [poleClearedLFunction,if_neg h,norm_mul]
    have hn := Complex.norm_le_abs_re_add_abs_im (s-1)
    have hr : |s.re-1|≤2 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hz : ‖s-1‖≤4*(1+|s.im|) := by
      simp only [sub_re,one_re,sub_im,one_im,sub_zero] at hn
      linarith [abs_nonneg s.im]
    have hL := norm_LFunction_strip_poly_le h (s:=s) (by linarith [hs.1]) hs.2
    have hpow := pow_le_pow_left₀ (by positivity : 0≤|s.im|+2)
      (by linarith [abs_nonneg s.im] : |s.im|+2≤2*(1+|s.im|)) 2
    calc _ ≤ (4*(1+|s.im|))*(A*(2*(1+|s.im|))^2) :=
           mul_le_mul hz (hL.trans (mul_le_mul_of_nonneg_left hpow hA)) (norm_nonneg _) (by positivity)
         _ = _ := by ring

end AnalyticNumberTheory.DirichletLFunctions
