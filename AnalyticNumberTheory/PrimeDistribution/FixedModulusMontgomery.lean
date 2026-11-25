import AnalyticNumberTheory.PrimeDistribution.FixedModulusMontgomeryNonprincipal
import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaDensity

/-! # Montgomery's density theorem for the full group of characters -/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Montgomery's exponent above four fifths for all Dirichlet characters modulo q, counting both signs
of height and every analytic multiplicity, including the principal character. -/
theorem modulusDensityCount_montgomery_right :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ}, σ∈Set.Icc (4/5:ℝ) 1 → 2≤T →
      (modulusDensityCount q σ T:ℝ) ≤ C*((q:ℝ)*T)^(montgomeryExponent σ)*(Real.log ((q:ℝ)*T))^12 := by
  obtain ⟨C,hC,HC⟩ := fixed_nonprincipal_montgomery
  obtain ⟨D,hD,HD⟩ := principal_character_montgomery_log_twelve
  refine ⟨C+D,by positivity,?_⟩
  intro q _ σ T hσ hT
  let N := characterDensityCount (1:DirichletCharacter ℂ q) σ T
  let M := ∑ χ : DirichletCharacter ℂ q,∑ z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z
  have he : modulusDensityCount q σ T=N+M := by
    unfold modulusDensityCount
    calc _ = ∑ χ : DirichletCharacter ℂ q, ((if χ=1 then N else 0)+
             ∑ z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z) :=
               sum_congr rfl (fun χ _ => characterDensityCount_split_principal χ σ T)
         _ = _ := by rw [sum_add_distrib];simp [M]
  have he' : (modulusDensityCount q σ T:ℝ)=(N:ℝ)+(M:ℝ) := by exact_mod_cast he
  have hP := HD (q:=q) hT hσ
  have hN := HC (q:=q) hσ hT
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have ht : T≤(q:ℝ)*T := le_mul_of_one_le_left (by linarith) hq₁
  have hl := Real.log_le_log (by linarith : 0<T) ht
  have he₀ : 0 ≤ montgomeryExponent σ := by unfold montgomeryExponent;apply div_nonneg <;> linarith [hσ.1,hσ.2]
  have hh := hP.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ht he₀) hD.le)
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hl 12) (by positivity [Real.log_nonneg (by linarith : 1≤T)])
    (by positivity : 0≤D*((q:ℝ)*T)^(montgomeryExponent σ)))
  change (N:ℝ)≤_ at hh
  simp only [M,Nat.cast_sum] at he'
  linarith only [he',hh,hN]

/-- For all characters of a fixed modulus the symmetric zero count, including
multiplicity, satisfies Montgomery's exponent throughout the half-strip. -/
theorem modulusDensityCount_montgomery_log_twelve :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ}, σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (modulusDensityCount q σ T:ℝ)≤C*((q:ℝ)*T)^(montgomeryExponent σ)*(Real.log ((q:ℝ)*T))^12 := by
  obtain ⟨A,hA,HA⟩ := modulusDensityCount_montgomery_left
  obtain ⟨B,hB,HB⟩ := modulusDensityCount_montgomery_right
  refine ⟨16*A+B,by positivity,?_⟩
  intro q _ σ T hσ hT
  let H := (q:ℝ)*T
  have hH : 2≤H := hT.trans (le_mul_of_one_le_left (by linarith) (by exact_mod_cast NeZero.pos q))
  have hl : 1/2≤Real.log H := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log zero_lt_two hH)
  have hp := Real.rpow_nonneg (by linarith : 0≤H) (montgomeryExponent σ)
  by_cases hh : σ≤4/5
  · have h := HA (q:=q) ⟨hσ.1,hh⟩ hT
    have h5 := pow_le_pow_left₀ (by norm_num : 0≤(1/2:ℝ)) hl 4
    norm_num at h5
    have hscale := mul_le_mul_of_nonneg_left h5 (by positivity : 0≤16*A*H^(montgomeryExponent σ)*(Real.log H)^8)
    change _≤(16*A+B)*H^(montgomeryExponent σ)*(Real.log H)^12
    apply h.trans
    change A*H^(montgomeryExponent σ)*(Real.log H)^8≤_
    linarith only [hscale,mul_nonneg (mul_nonneg hB.le hp) (pow_nonneg (by linarith : 0≤Real.log H) 12)]
  · apply (HB (q:=q) ⟨(not_le.mp hh).le,hσ.2⟩ hT).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : B≤16*A+B) hp)
      (pow_nonneg (by linarith : 0≤Real.log H) 12)

/-- The conventional thirteen-logarithm estimate for every character modulo q. -/
theorem modulusDensityCount_montgomery :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ}, σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (modulusDensityCount q σ T:ℝ)≤C*((q:ℝ)*T)^(montgomeryExponent σ)*(Real.log ((q:ℝ)*T))^13 := by
  obtain ⟨C,hC,H⟩ := modulusDensityCount_montgomery_log_twelve
  refine ⟨2*C,by positivity,?_⟩
  intro q _ σ T hσ hT
  have hQT : 2≤(q:ℝ)*T := hT.trans (le_mul_of_one_le_left (by linarith) (by exact_mod_cast NeZero.pos q))
  exact (H (q:=q) hσ hT).trans ((mul_le_mul_of_nonneg_left (log_pow_le_twice_log_succ 12 hQT)
    (by positivity : 0≤C*((q:ℝ)*T)^(montgomeryExponent σ))).trans_eq (by ring))

/-- A conductor-height estimate that includes height zero and real zeros. -/
theorem modulusDensityCount_montgomery_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (1/2:ℝ) 1 → 0≤T →
      (modulusDensityCount q σ T:ℝ)≤C*((q:ℝ)*(T+2))^(montgomeryExponent σ)*(Real.log ((q:ℝ)*(T+2)))^12 := by
  obtain ⟨C,hC,H⟩ := modulusDensityCount_montgomery_log_twelve
  refine ⟨C,hC,?_⟩
  intro q _ σ T hσ hT
  apply le_trans _ (H (q:=q) hσ (show 2≤T+2 by linarith))
  exact_mod_cast sum_le_sum (s:=univ) (fun (χ : DirichletCharacter ℂ q) _ =>
    characterDensityCount_mono_height χ σ (show T≤T+2 by linarith))

end AnalyticNumberTheory.PrimeDistribution
