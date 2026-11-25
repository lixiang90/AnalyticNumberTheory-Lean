import AnalyticNumberTheory.PrimeDistribution.CharacterInghamSymmetric
import AnalyticNumberTheory.PrimeDistribution.CharacterTypeIMeans
import AnalyticNumberTheory.PrimeDistribution.PrincipalCharacterDensity
import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthMoment

/-!
# Ingham's density estimate for primitive Dirichlet characters

The conductor-height scale is Q²T. Zeros are counted with analytic multiplicity
at both signs of the ordinate. The unique primitive principal character,
of modulus one, contributes the corresponding Riemann zeta count.
-/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Splitting off the unique primitive principal character identifies the sum of
all primitive counts with the nonprincipal count plus the Riemann zeta count. -/
theorem primitive_density_sum_eq_principal_add {Q : ℕ} (hQ : 1≤Q) (σ T : ℝ) :
    (∑d∈Icc 1 Q,primitiveModulusDensityCount d σ T) =
      characterDensityCount (1:DirichletCharacter ℂ 1) σ T + primitiveFamilyZeroCount Q σ T := by
  let F := primitiveCharacterFamily Q
  let p₀ : PrimitiveCharacterIndex := ⟨1,1⟩
  have hp₀ : p₀∈F := mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hQ⟩,
    mem_filter.mpr ⟨mem_univ _,DirichletCharacter.isPrimitive_one_level_one⟩⟩
  have hsplit (p : PrimitiveCharacterIndex) (hp : p∈F) :
      characterDensityCount p.2 σ T =
        (if p=p₀ then characterDensityCount (1:DirichletCharacter ℂ 1) σ T else 0) +
          ∑ z∈nonprincipalDensityFinset p.2 σ T,characterZeroMultiplicity p.2 z := by
    rcases p with ⟨q,χ⟩
    letI : NeZero q := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus hp).1⟩
    rw [characterDensityCount_split_principal]
    congr 1
    by_cases he : χ=1
    · subst χ
      have hprim := (mem_filter.mp (mem_sigma.mp hp).2).2
      have hq : q=1 := hprim.symm.trans DirichletCharacter.conductor_one
      subst q;simp [p₀]
    · have hne : (⟨q,χ⟩:PrimitiveCharacterIndex)≠p₀ := by
        intro h
        have hq : q=1 := congrArg Sigma.fst h
        subst q
        exact he (Subsingleton.elim _ _)
      simp [hne,he]
  change _ = _ + (∑p∈F,∑ z∈nonprincipalDensityFinset p.2 σ T,characterZeroMultiplicity p.2 z)
  calc _ = ∑p∈F,characterDensityCount p.2 σ T := by
           simp only [F,primitiveCharacterFamily,sum_sigma,primitiveModulusDensityCount]
       _ = _ := by
           rw [sum_congr rfl hsplit,sum_add_distrib]
           simp [hp₀]

/-- The hybrid estimate at the rounded conductor-height cutoff, with seven
logarithms for nonprincipal primitive characters. -/
theorem primitiveFamilyZeroCount_ingham_at_cutoff :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ} {σ T : ℝ},1≤Q → 2≤T → σ∈Set.Icc (1/2:ℝ) 1 →
      let X : ℕ := Q^2*(⌊T⌋₊+16)
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤ C*(1+Real.log X)^7*(X:ℝ)^(inghamExponent σ) := by
  obtain ⟨B,hB,H₄⟩ := primitive_conductors_critical_fourth_moment
  obtain ⟨D,hD,HD⟩ := character_ingham_symmetric_weighted hB
  refine ⟨D,hD,?_⟩
  intro Q σ T hQ hT hσ
  let L := ⌊T⌋₊+16
  let X := Q^2*L
  let F := primitiveCharacterFamily Q
  let q (p : F) := p.val.1
  let χ (p : F) := p.val.2
  letI (i : F) : NeZero (q i) := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus i.property).1⟩
  let c (i : F) : F := ⟨primitiveStarIndex i.val,primitiveStarIndex_mem i.property⟩
  have hL : 16≤L := by dsimp [L];omega
  have hQ₂ : 1≤Q^2 := Nat.one_le_pow _ _ hQ
  have hX : 16≤X := hL.trans (Nat.le_mul_of_pos_left L hQ₂)
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hLr : (16:ℝ)≤L := by exact_mod_cast hL
  have hTL : T<(L:ℝ) := by dsimp only [L];push_cast;linarith [Nat.lt_floor_add_one T]
  have hrX : (X:ℝ)=(Q:ℝ)^2*L := by simp [X]
  have hhyb (m : ℕ) (hm : 1≤m) : CharacterHybridMean F.attach (fun p n => χ p n) (m*L) ((m:ℝ)*X) := by
    intro N hN a
    have hh := primitive_family_hybrid_mean Q (L:=m*L) (Nat.mul_pos hm (by omega)) N hN a
    rw [hrX]
    convert hh using 1
    · exact sum_attach F (fun p => ∫t in (0:ℝ)..(m*L:ℕ),‖∑n∈Icc 1 N,a n*p.2 n*(n:ℂ)^(-(I*(t:ℂ)))‖^2)
    · push_cast;ring
  have hmom (j : ℕ) : (∑ p∈F.attach,∫ t in -(2^j*(L:ℝ))..2^j*L,
      ‖(χ p).LFunction ((1/2:ℂ)+t*I)‖^4)≤ B*(2^j*(X:ℝ))*(1+Real.log (2^j*(X:ℝ)))^4 := by
    let U := (2:ℝ)^j*L
    have hpow : 1≤(2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hU : 1≤U := one_le_mul_of_one_le_of_one_le hpow (by linarith)
    have heq : (∑ p∈F.attach,∫ t in (-U)..U,‖(χ p).LFunction ((1/2:ℂ)+t*I)‖^4) =
        ∑ p∈F,∫ t in (-U)..U,‖familyLFunction p ((1/2:ℂ)+t*I)‖^4 := by
      rw [←sum_attach F (fun p => ∫ t in (-U)..U,‖familyLFunction p ((1/2:ℂ)+t*I)‖^4)]
      apply sum_congr rfl
      intro i _
      simp only [familyLFunction,dite_eq_right (Nat.ne_of_gt (primitiveCharacterFamily_modulus i.property).1),χ]
    change (∑p∈F.attach,∫ t in (-U)..U,_)≤_
    rw [heq]
    apply (H₄ hQ hU).trans
    have hquad : (Q:ℝ)≤(Q:ℝ)^2 := by nlinarith [sq_nonneg ((Q:ℝ)-1)]
    have hscale : (2:ℝ)^j*X=(Q:ℝ)^2*U := by rw [hrX];dsimp only [U];ring
    rw [hscale,mul_assoc B]
    have hp := one_le_mul_of_one_le_of_one_le hqr hU
    have hl := Real.log_le_log (by linarith : 0<(Q:ℝ)*U) (mul_le_mul_of_nonneg_right hquad (by linarith : 0≤U))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [Real.log_nonneg hp]) (add_le_add_right hl 1) 4) (by positivity)
  have hz := HD F.attach q χ c (X:=X) (L:=L) (σ:=σ) (T:=T)
    (fun i => Subtype.ext (primitiveStarIndex_involutive _)) (fun i _ => mem_attach _ _)
    (fun i _ => nonprincipal_star_conjugate (χ i)) hX (by omega) hTL hσ
    (by simpa only [card_attach,F] using Nat.mul_le_mul_right L (card_primitiveFamily_le Q))
    (fun i _ => Nat.mul_le_mul_right L ((primitiveCharacterFamily_modulus i.property).2.trans
      (by simpa only [pow_two] using Nat.le_mul_of_pos_right Q hQ))) hhyb hmom
  change (primitiveFamilyZeroCount Q σ T:ℝ) ≤ D*(1+Real.log X)^7*(X:ℝ)^(inghamExponent σ)
  simp only [primitiveFamilyZeroCount,Nat.cast_sum]
  exact (Finset.sum_attach F _).symm.le.trans hz

/-- Ingham's mean density bound over nonprincipal primitive characters, with
multiplicities and both signs of the ordinate. -/
theorem primitiveFamilyZeroCount_ingham :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ} {σ T : ℝ},1≤Q → 2≤T → σ∈Set.Icc (1/2:ℝ) 1 →
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤
        C*((Q:ℝ)^2*T)^(inghamExponent σ)*(Real.log ((Q:ℝ)*T))^9 := by
  obtain ⟨D,hD,H⟩ := primitiveFamilyZeroCount_ingham_at_cutoff
  refine ⟨D*(9*20^9),by positivity,?_⟩
  intro Q σ T hQ hT hσ
  let L := ⌊T⌋₊+16
  let X := Q^2*L
  have hcount := H hQ hT hσ
  change (primitiveFamilyZeroCount Q σ T:ℝ) ≤ D*(1+Real.log X)^7*(X:ℝ)^(inghamExponent σ) at hcount
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hrX : (X:ℝ)=(Q:ℝ)^2*L := by simp [X]
  have hLr : (1:ℝ)≤L := by dsimp [L];push_cast;linarith [Nat.cast_nonneg (α:=ℝ) ⌊T⌋₊]
  have hX' : (1:ℝ)≤X := by rw [hrX];exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hqr) hLr
  have hqT : 2≤(Q:ℝ)*T := hT.trans (le_mul_of_one_le_left (by linarith) hqr)
  have hLT : (L:ℝ)≤9*T := by dsimp only [L];push_cast;linarith [Nat.floor_le (by linarith : 0≤T)]
  have hs := ingham_scale_bound hX' (by positivity : 0≤(Q:ℝ)^2*T) hqT
    (by rw [hrX];nlinarith only [mul_le_mul_of_nonneg_left hLT (sq_nonneg (Q:ℝ))])
    (by nlinarith only [mul_nonneg (sq_nonneg (Q:ℝ)) (show 0≤T^2-T by nlinarith only [hT,sq_nonneg (T-1)])]) hσ
  exact hcount.trans ((le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left hs hD.le).trans_eq (by ring)))

/-- The primitive-family Ingham density theorem including modulus one. For
(1/2≤σ≤1), the exponent is (3(1-σ)/(2-σ)); the logarithmic exponent is nine. -/
theorem primitive_conductors_ingham_density :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ} {σ T : ℝ},1≤Q → 2≤T → σ∈Set.Icc (1/2:ℝ) 1 →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*T)^(inghamExponent σ)*(Real.log ((Q:ℝ)*T))^9 := by
  obtain ⟨C,hC,H⟩ := primitiveFamilyZeroCount_ingham
  obtain ⟨D,hD,P⟩ := principal_character_ingham_density_log_nine
  refine ⟨D+C,by positivity,?_⟩
  intro Q σ T hQ hT hσ
  have hr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have ht := hT.trans (le_mul_of_one_le_left (show 0≤T by linarith) hr)
  have hq₂ : (1:ℝ)≤(Q:ℝ)^2 := one_le_pow₀ hr
  have he : 0 ≤ inghamExponent σ := by unfold inghamExponent;apply div_nonneg <;> nlinarith [hσ.2]
  have hpow := Real.rpow_le_rpow (by linarith : 0≤T)
    (le_mul_of_one_le_left (by linarith : 0≤T) hq₂) he
  have hlog := Real.log_le_log (by linarith : 0<T) (le_mul_of_one_le_left (by linarith : 0≤T) hr)
  have hh := P (q:=1) hσ hT
  have hpr := hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hD.le)
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 9) (by positivity [Real.log_nonneg (by linarith : 1≤T)]) (by positivity))
  have hsum := congrArg (fun n : ℕ => (n:ℝ)) (primitive_density_sum_eq_principal_add hQ σ T)
  push_cast at hsum
  rw [hsum]
  exact (add_le_add hpr (H hQ hT hσ)).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
