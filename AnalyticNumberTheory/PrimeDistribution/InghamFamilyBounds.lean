import AnalyticNumberTheory.PrimeDistribution.FixedModulusIngham
import AnalyticNumberTheory.PrimeDistribution.PrimitiveFamilyIngham

/-!
# Uniform heights and eight logarithms in family density bounds

The nonprincipal primitive and fixed-modulus estimates use seven logarithms.
The primitive principal character adds the zeta estimate with eight.
Monotonicity in the height also gives a bound down to height zero.
-/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

private lemma scaled_ingham_family {A q : ℕ} {σ T D E P N : ℝ}
    (hA : 1≤A) (hq : 1≤q) (hAq : A≤q^2) (hT : 2≤T) (hσ : σ∈Set.Icc (1/2:ℝ) 1)
    (hD : 0<D) (hE : 0<E)
    (hp : P ≤ E*T^(inghamExponent σ)*(Real.log T)^8)
    (hn : let X : ℕ := A*(⌊T⌋₊+16); N ≤ D*(1+Real.log X)^7*(X:ℝ)^(inghamExponent σ)) :
    P+N ≤ (E+2*D*9*20^7)*((A:ℝ)*T)^(inghamExponent σ)*(Real.log ((q:ℝ)*T))^8 := by
  let X : ℕ := A*(⌊T⌋₊+16)
  let H := (A:ℝ)*T
  let Y := (q:ℝ)*T
  have ha : (1:ℝ)≤A := by exact_mod_cast hA
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
  have hTH : T≤H := le_mul_of_one_le_left (by linarith) ha
  have hTY : T≤Y := le_mul_of_one_le_left (by linarith) hq₁
  have hY : 2≤Y := hT.trans hTY
  have hY₀ : 0<Y := by linarith
  have hH : 0<H := by linarith
  have hX : (1:ℝ)≤X := by
    dsimp only [X];push_cast
    exact one_le_mul_of_one_le_of_one_le ha (by linarith [Nat.cast_nonneg (α:=ℝ) ⌊T⌋₊])
  have hXH : (X:ℝ)≤9*H := by
    dsimp only [X,H];push_cast
    have hl : (⌊T⌋₊:ℝ)+16≤9*T := by linarith [Nat.floor_le (by linarith : 0≤T)]
    linarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α:=ℝ) A)]
  have hHY : H≤Y^2 := by
    have h : (A:ℝ)≤(q:ℝ)^2 := by exact_mod_cast hAq
    dsimp only [H,Y]
    nlinarith only [mul_le_mul_of_nonneg_right h (by linarith : 0≤T),
      mul_nonneg (sq_nonneg (q:ℝ)) (show 0≤T^2-T by nlinarith only [hT,sq_nonneg (T-1)])]
  have he : 0 ≤ inghamExponent σ := by unfold inghamExponent;apply div_nonneg <;> linarith [hσ.2]
  have he' : inghamExponent σ≤1 := by
    unfold inghamExponent;apply (div_le_iff₀ (by linarith [hσ.2])).mpr;linarith [hσ.1]
  have hbase := Real.rpow_le_rpow (zero_le_one.trans hX) hXH he
  rw [Real.mul_rpow (by norm_num) hH.le] at hbase
  have hg : (9:ℝ)^(inghamExponent σ)≤9 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(9:ℝ)) he'
  have hpow := hbase.trans (mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hH.le _))
  have hlog := Real.log_le_log (zero_lt_one.trans_le hX) (hXH.trans (mul_le_mul_of_nonneg_left hHY (by norm_num)))
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hY₀.ne'),Real.log_pow] at hlog
  change Real.log (X:ℝ)≤Real.log (9:ℝ)+2*Real.log Y at hlog
  have hs : 1/2≤Real.log Y := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log zero_lt_two hY)
  have h₇ := pow_le_pow_left₀ (by linarith [Real.log_nonneg hX] : 0≤1+Real.log (X:ℝ))
    (show 1+Real.log (X:ℝ)≤20*Real.log Y by linarith only [hlog,hs,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)]) 7
  have h₈ : (Real.log Y)^7≤2*(Real.log Y)^8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs (show 0≤(Real.log Y)^7 by positivity [show 0≤Real.log Y by linarith])]
  have hpoly : (1+Real.log (X:ℝ))^7 ≤ 2*20^7*(Real.log Y)^8 := by
    rw [mul_pow] at h₇
    linarith only [h₇,mul_le_mul_of_nonneg_left h₈ (by norm_num : 0≤(20:ℝ)^7)]
  change N ≤ D*(1+Real.log (X:ℝ))^7*(X:ℝ)^(inghamExponent σ) at hn
  have hN := hn.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpoly hD.le) hpow (Real.rpow_nonneg (zero_le_one.trans hX) _) (by positivity))
  have hP := hp.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hTH he) hE.le)
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hTY) 8) (by positivity) (by positivity))
  change _≤(E+2*D*9*20^7)*H^(inghamExponent σ)*(Real.log Y)^8
  linarith only [hN,hP]

private lemma principal_ingham_eight :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (characterDensityCount (1:DirichletCharacter ℂ q) σ T:ℝ)≤C*T^(inghamExponent σ)*(Real.log T)^8 := by
  obtain ⟨C,hC,H⟩ := ingham_zeroDensity_with_multiplicity_log_eight
  refine ⟨2*C,by positivity,?_⟩;intro q _ σ T hσ hT
  rw [characterDensityCount_principal_eq_twice (by linarith [hσ.1])];push_cast
  linarith only [H σ hσ T hT]

/-- Ingham's mean density bound for the full group at one modulus with
eight logarithms, including the principal character and analytic multiplicities. -/
theorem modulusDensityCount_ingham_log_eight :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (modulusDensityCount q σ T:ℝ) ≤ C*((q:ℝ)*T)^(inghamExponent σ)*(Real.log ((q:ℝ)*T))^8 := by
  obtain ⟨D,hD,H⟩ := fixed_nonprincipal_ingham_at_cutoff
  obtain ⟨E,hE,P⟩ := principal_ingham_eight
  refine ⟨E+2*D*9*20^7,by positivity,?_⟩;intro q _ σ T hσ hT
  let M := ∑χ : DirichletCharacter ℂ q,∑ z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z
  let N := characterDensityCount (1:DirichletCharacter ℂ q) σ T
  have hs : modulusDensityCount q σ T=N+M := by
    unfold modulusDensityCount
    calc _ = ∑ χ : DirichletCharacter ℂ q, ((if χ=1 then N else 0)+
          ∑ z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z) :=
            sum_congr rfl (fun χ _ => characterDensityCount_split_principal χ σ T)
         _ = _ := by rw [sum_add_distrib];simp [M]
  rw [hs,Nat.cast_add]
  apply scaled_ingham_family (A:=q) (NeZero.pos q) (NeZero.pos q)
    (by simpa only [pow_two] using Nat.le_mul_of_pos_right q (NeZero.pos q)) hT hσ hD hE (P hσ hT)
  simpa only [M,Nat.cast_sum] using H (q:=q) hσ hT

/-- Ingham's exponent and eight logarithms for all primitive conductors up to Q,
including the Riemann zeta contribution of modulus one. -/
theorem primitive_conductors_ingham_log_eight :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*T)^(inghamExponent σ)*(Real.log ((Q:ℝ)*T))^8 := by
  obtain ⟨D,hD,H⟩ := primitiveFamilyZeroCount_ingham_at_cutoff
  obtain ⟨E,hE,P⟩ := principal_ingham_eight
  refine ⟨E+2*D*9*20^7,by positivity,?_⟩;intro Q σ T hQ hσ hT
  have hs := congrArg (fun n : ℕ => (n:ℝ)) (primitive_density_sum_eq_principal_add hQ σ T)
  push_cast at hs
  rw [hs]
  simpa only [Nat.cast_pow] using scaled_ingham_family (A:=Q^2) (q:=Q) (Nat.one_le_pow _ _ hQ) hQ
    le_rfl hT hσ hD hE (P (q:=1) hσ hT) (H hQ hT hσ)

/-- Enlarging the symmetric range of ordinates preserves all counted zeros
and their analytic multiplicities. -/
theorem characterDensityCount_mono_height {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ)
    {T U : ℝ} (h : T≤U) : characterDensityCount χ σ T ≤ characterDensityCount χ σ U := by
  by_cases hq : q=0
  · simp [characterDensityCount,hq]
  letI : NeZero q := ⟨hq⟩
  simp only [characterDensityCount,dite_eq_left hq]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro z hz
  obtain ⟨hz,hσ⟩ := mem_filter.mp hz
  obtain ⟨hr,hr',h₁,h₂,hzeta⟩ := (mem_criticalStripZeroFinset χ).mp hz
  exact mem_filter.mpr ⟨(mem_criticalStripZeroFinset χ).mpr ⟨hr,hr',by linarith,by linarith,hzeta⟩,hσ⟩

/-- The fixed-modulus Ingham estimate at every nonnegative height. -/
theorem modulusDensityCount_ingham_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (1/2:ℝ) 1 → 0≤T →
      (modulusDensityCount q σ T:ℝ) ≤ C*((q:ℝ)*(T+2))^(inghamExponent σ)*(Real.log ((q:ℝ)*(T+2)))^8 := by
  obtain ⟨C,hC,H⟩ := modulusDensityCount_ingham_log_eight
  refine ⟨C,hC,?_⟩;intro q _ σ T hσ hT
  apply le_trans _ (H (q:=q) hσ (show 2≤T+2 by linarith))
  exact_mod_cast sum_le_sum (s:=univ) (fun (χ : DirichletCharacter ℂ q) _ => characterDensityCount_mono_height χ σ (show T≤T+2 by linarith))

/-- The primitive-conductor Ingham estimate at every nonnegative height. -/
theorem primitive_conductors_ingham_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 0≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*(T+2))^(inghamExponent σ)*(Real.log ((Q:ℝ)*(T+2)))^8 := by
  obtain ⟨C,hC,H⟩ := primitive_conductors_ingham_log_eight
  refine ⟨C,hC,?_⟩;intro Q σ T hQ hσ hT
  apply le_trans _ (H hQ hσ (show 2≤T+2 by linarith))
  apply sum_le_sum
  intro q hq
  exact_mod_cast sum_le_sum (s:=univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
    (fun (χ : DirichletCharacter ℂ q) _ => characterDensityCount_mono_height χ σ (show T≤T+2 by linarith))

end AnalyticNumberTheory.PrimeDistribution
