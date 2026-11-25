import AnalyticNumberTheory.PrimeDistribution.InghamDensity
import AnalyticNumberTheory.DirichletLFunctions.FamilyDensityCounts

/-!
# Density of the principal character

Missing Euler factors leave critical-strip zeros and their orders unchanged.
Conjugation identifies the negative ordinates with the positive ones, and
the real interval (0,1) contains no zero of zeta.
-/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- Exact conversion of the symmetric principal count into the usual positive-height
zeta sum, for any positive threshold and every real endpoint. -/
theorem characterDensityCount_principal_eq_twice {q : ℕ} [NeZero q] {σ : ℝ} (hσ : 0<σ) (T : ℝ) :
    characterDensityCount (1 : DirichletCharacter ℂ q) σ T =
      2*∑z∈zeroDensityFinset σ T,zeroMultiplicity z := by
  have hlevel := characterDensityCount_changeLevel (one_dvd q) (1:DirichletCharacter ℂ 1) σ T
  rw [DirichletCharacter.changeLevel_one] at hlevel
  rw [hlevel,characterDensityCount,dite_eq_left (by decide : (1:ℕ)≠0)]
  let S := zeroDensityFinset σ T
  have he : ((criticalStripZeroFinset (1:DirichletCharacter ℂ 1) (-T) T).filter fun z => σ≤z.re)=
      S ∪ S.image star := by
    ext z
    rw [mem_filter,mem_criticalStripZeroFinset,DirichletCharacter.LFunction_modOne_eq]
    have hsym : (0<z.re ∧ z.re<1 ∧ -T≤z.im ∧ z.im≤T ∧ riemannZeta z=0) ↔ z∈zeroDensityFinsetSymmetric T := by
      rw [mem_zeroDensityFinsetSymmetric,abs_le];tauto
    rw [hsym,zeroDensityFinsetSymmetric,mem_union,mem_union]
    constructor
    · rintro ⟨h|h,hr⟩
      · exact Or.inl (mem_zeroDensityFinset.mpr ⟨(mem_zeroDensityFinset.mp h).1,hr,(mem_zeroDensityFinset.mp h).2.2⟩)
      · obtain ⟨w,hw,rfl⟩ := mem_image.mp h
        exact Or.inr (mem_image.mpr ⟨w,mem_zeroDensityFinset.mpr ⟨(mem_zeroDensityFinset.mp hw).1,hr,
          (mem_zeroDensityFinset.mp hw).2.2⟩,rfl⟩)
    · rintro (h|h)
      · obtain ⟨hz,hr,h₁,ht,hT⟩ := mem_zeroDensityFinset.mp h
        exact ⟨Or.inl (mem_zeroDensityFinset.mpr ⟨hz,hσ.le.trans hr,h₁,ht,hT⟩),hr⟩
      · obtain ⟨w,hw,rfl⟩ := mem_image.mp h
        obtain ⟨hz,hr,h₁,ht,hT⟩ := mem_zeroDensityFinset.mp hw
        exact ⟨Or.inr (mem_image.mpr ⟨w,mem_zeroDensityFinset.mpr ⟨hz,hσ.le.trans hr,h₁,ht,hT⟩,rfl⟩),hr⟩
  have hd : Disjoint S (S.image star) := by
    apply disjoint_left.mpr;intro z hz h
    obtain ⟨w,hw,rfl⟩ := mem_image.mp h
    have hp := (mem_zeroDensityFinset.mp hz).2.2.2.1
    have hn := (mem_zeroDensityFinset.mp hw).2.2.2.1
    change 0 < -w.im at hp
    linarith
  rw [he,sum_union hd,DirichletCharacter.LFunction_modOne_eq,sum_image (fun i _ j _ h => star_injective h)]
  change (∑z∈S,zeroMultiplicity z)+(∑z∈S,zeroMultiplicity (star z))=2*∑z∈S,zeroMultiplicity z
  have hs : (∑z∈S,zeroMultiplicity (star z))=∑z∈S,zeroMultiplicity z :=
    sum_congr rfl (fun z hz => analyticOrderNatAt_riemannZeta_star (hσ.trans_le (mem_zeroDensityFinset.mp hz).2.1)
      (mem_zeroDensityFinset.mp hz).2.2.1)
  rw [hs,two_mul]

/-- At all nonnegative heights the principal Ingham estimate is independent of the modulus. -/
theorem principal_character_ingham_density :
    ∃C > (0:ℝ),∀{q : ℕ} [NeZero q],∀ {σ T : ℝ},σ∈Set.Icc (1/2:ℝ) 1 → 0≤T →
      (characterDensityCount (1:DirichletCharacter ℂ q) σ T:ℝ)≤
        C*(T+2)^(inghamExponent σ)*(1+Real.log (T+2))^8 := by
  obtain ⟨C,hC,H⟩ := ingham_zeroDensity_with_multiplicity_log_eight
  refine ⟨2*C,by positivity,?_⟩
  intro q _ σ T hσ hT
  rw [characterDensityCount_principal_eq_twice (by linarith [hσ.1])]
  push_cast
  have hb : (∑z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤
      ∑z∈zeroDensityFinset σ (T+2),(zeroMultiplicity z:ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
    intro z hz;obtain ⟨hz,hr,h₁,ht,ht'⟩ := mem_zeroDensityFinset.mp hz
    exact mem_zeroDensityFinset.mpr ⟨hz,hr,h₁,ht,by linarith⟩
  have hh := hb.trans (H σ hσ (T+2) (by linarith))
  have hl := Real.log_nonneg (by linarith : 1≤T+2)
  calc _ ≤ 2*(C*(T+2)^(inghamExponent σ)*(1+Real.log (T+2))^8) := by
             apply mul_le_mul_of_nonneg_left _ (by norm_num)
             apply hh.trans
             gcongr <;> linarith
       _ = _ := by ring

/-- For T ≥ 2 this gives the classical ninth logarithmic power with base T. -/
theorem principal_character_ingham_density_log_nine :
    ∃C > (0:ℝ),∀{q : ℕ} [NeZero q],∀{σ T : ℝ},σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (characterDensityCount (1:DirichletCharacter ℂ q) σ T:ℝ)≤C*T^(inghamExponent σ)*(Real.log T)^9 := by
  obtain ⟨C,hC,H⟩ := ingham_zeroDensity_with_multiplicity_log_eight
  refine ⟨4*C,by positivity,?_⟩
  intro q _ σ T hσ hT
  rw [characterDensityCount_principal_eq_twice (by linarith [hσ.1])]
  push_cast
  have e := mul_le_mul_of_nonneg_left (H σ hσ T hT) (by norm_num : (0:ℝ)≤2)
  have hlog : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : 1/2≤Real.log 2).trans (Real.log_le_log zero_lt_two hT)
  have h0 : 0≤C*T^(inghamExponent σ)*(Real.log T)^8 := by positivity
  have hh := mul_le_mul_of_nonneg_right hlog h0
  linarith only [e,hh]

end AnalyticNumberTheory.PrimeDistribution
