import AnalyticNumberTheory.PrimeDistribution.InghamFamilyBounds

/-! # Weighted sums over the critical-strip zeros of primitive characters -/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Strip zeros at both signs of height. The empty modulus contributes no zeros. -/
def characterStripZeros {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ :=
  if h : q≠0 then
    letI : NeZero q := ⟨h⟩
    criticalStripZeroFinset χ (-T) T
  else ∅

/-- Each sample records its character as well as its zero. -/
def primitiveFamilyZeros (Q : ℕ) (T : ℝ) : Finset ((p : PrimitiveCharacterIndex) × ℂ) :=
  (primitiveCharacterFamily Q).sigma (fun p => characterStripZeros p.2 T)

/-- Sum a real weight at all critical-strip zeros of primitive characters of
conductor at most Q and absolute ordinate at most T, including multiplicity. -/
def primitiveFamilyZeroWeight (Q : ℕ) (T : ℝ) (f : ℂ→ℝ) : ℝ :=
  ∑ p∈primitiveFamilyZeros Q T,(characterZeroMultiplicity p.1.2 p.2:ℝ)*f p.2

theorem mem_characterStripZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} {z : ℂ} :
    z∈characterStripZeros χ T ↔ 0<z.re ∧ z.re<1 ∧ -T≤z.im ∧ z.im≤T ∧ χ.LFunction z=0 := by
  rw [characterStripZeros,dif_pos (NeZero.ne q),mem_criticalStripZeroFinset]

theorem primitiveFamilyZeros_re {Q : ℕ} {T : ℝ} {p : (i : PrimitiveCharacterIndex) × ℂ}
    (hp : p∈primitiveFamilyZeros Q T) : 0<p.2.re ∧ p.2.re<1 := by
  obtain ⟨hi,hz⟩ := mem_sigma.mp hp
  letI : NeZero p.1.1 := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus hi).1⟩
  exact ⟨((mem_characterStripZeros _).mp hz).1,((mem_characterStripZeros _).mp hz).2.1⟩

/-- Filtering a symmetric height window recovers the smaller family exactly. -/
theorem primitiveFamilyZeros_filter_height {T U : ℝ} (h : U≤T) (Q : ℕ) :
    (primitiveFamilyZeros Q T).filter (fun p => |p.2.im|≤U)=primitiveFamilyZeros Q U := by
  ext ⟨p,z⟩
  simp only [primitiveFamilyZeros,mem_filter,mem_sigma]
  by_cases hp : p∈primitiveCharacterFamily Q
  · letI : NeZero p.1 := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus hp).1⟩
    simp only [hp,true_and,mem_characterStripZeros,abs_le]
    constructor
    · rintro ⟨⟨ha,hb,_,_,he⟩,hc,hd⟩
      exact ⟨ha,hb,hc,hd,he⟩
    · rintro ⟨ha,hb,hc,hd,he⟩
      exact ⟨⟨ha,hb,by linarith,hd.trans h,he⟩,hc,hd⟩
  · simp [hp]

theorem primitiveFamilyZeroWeight_tail (Q : ℕ) (σ T : ℝ) :
    primitiveFamilyZeroWeight Q T (fun z => if σ≤z.re then 1 else 0)=
      ∑ q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ) := by
  unfold primitiveFamilyZeroWeight primitiveFamilyZeros
  rw [sum_sigma]
  have he (p : PrimitiveCharacterIndex) (hp : p∈primitiveCharacterFamily Q) :
      (∑ z∈characterStripZeros p.2 T,(characterZeroMultiplicity p.2 z:ℝ)*(if σ≤z.re then 1 else 0)) =
        (characterDensityCount p.2 σ T:ℝ) := by
    letI : NeZero p.1 := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus hp).1⟩
    simp only [characterStripZeros,characterZeroMultiplicity,characterDensityCount,dif_pos (NeZero.ne p.1),
      Nat.cast_sum,sum_filter,mul_ite,mul_one,mul_zero,Nat.cast_ite,Nat.cast_zero]
  rw [sum_congr rfl he]
  simp only [primitiveCharacterFamily,sum_sigma,primitiveModulusDensityCount,Nat.cast_sum]

/-- Summing the elementary Riemann–von Mangoldt bound over primitive conductors
gives a uniform total for every real-part threshold. -/
theorem primitive_family_density_trivial :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {T : ℝ},1≤Q → 2≤T → ∀ σ : ℝ,
    (∑ q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤C*((Q:ℝ)^2*T)*Real.log ((Q:ℝ)*T) := by
  obtain ⟨C,hC,H⟩ := modulusDensityCount_trivial
  refine ⟨C,hC,?_⟩;intro Q T hQ hT σ
  have hT₀ : 0<T := by linarith
  have ht (q : ℕ) (hq : q∈Icc 1 Q) :
      (primitiveModulusDensityCount q σ T:ℝ)≤C*Q*T*Real.log ((Q:ℝ)*T) := by
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hq
    letI : NeZero q := ⟨by omega⟩
    have hq₁ : (1:ℝ)≤q := by exact_mod_cast h₁
    have hqT : 1≤(q:ℝ)*T := one_le_mul_of_one_le_of_one_le hq₁ (by linarith)
    have hc : primitiveModulusDensityCount q σ T≤modulusDensityCount q σ T :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros;omega)
    apply (show (primitiveModulusDensityCount q σ T:ℝ)≤modulusDensityCount q σ T by exact_mod_cast hc).trans
    apply (H (q:=q) hT σ).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (Nat.totient_le q).trans h₂) hC.le) hT₀.le)
      (Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right (by exact_mod_cast h₂) hT₀.le))
      (Real.log_nonneg hqT) (by positivity)
  exact (sum_le_sum ht).trans_eq (by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel];ring)

end AnalyticNumberTheory.PrimeDistribution
