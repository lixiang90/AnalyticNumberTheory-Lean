import AnalyticNumberTheory.PrimeDistribution.CharacterInghamCounts
import AnalyticNumberTheory.PrimeDistribution.SymmetricFamilyDensity

/-! # Symmetric Ingham estimates with zero multiplicity -/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical ComplexConjugate
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

theorem nonprincipal_star_conjugate {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : star χ≠1) : χ≠1 ∧ ∀ z : ℂ,(star χ).LFunction z=0 → χ.LFunction (conj z)=0 := by
  refine ⟨fun he => hχ (by simp [he]),?_⟩
  intro z hz
  simpa only [star_star,hz,map_zero] using LFunction_star_conj hχ z

/-- Count all nonprincipal zeros of a conjugation-stable family with analytic
multiplicity. The hybrid cost is X and the height of the samples is less than L. -/
theorem character_ingham_symmetric_weighted {B : ℝ} (hB : 0<B) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} (F : Finset ι) (q : ι→ℕ) [∀ i,NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (c : ι→ι) {X L : ℕ} {σ T : ℝ},
    Function.Involutive c → (∀ i∈F,c i∈F) →
    (∀ i∈F,χ (c i)≠1 → χ i≠1 ∧ ∀ z,(χ (c i)).LFunction z=0 → (χ i).LFunction (conj z)=0) →
    16≤X → 3≤L → T<L → σ∈Set.Icc (1/2:ℝ) 1 → F.card*L≤X → (∀ i∈F,q i*L≤X) →
    (∀ m : ℕ,1≤m → CharacterHybridMean F (fun i n => χ i n) (m*L) ((m:ℝ)*X)) →
    (∀ j : ℕ, (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,‖(χ i).LFunction ((1/2:ℂ)+t*I)‖^4)
      ≤ B*(2^j*(X:ℝ))*(1+Real.log (2^j*(X:ℝ)))^4) →
    (∑ i∈F,∑ z∈nonprincipalDensityFinset (χ i) σ T,(characterZeroMultiplicity (χ i) z:ℝ))
      ≤ C*(1+Real.log X)^7*(X:ℝ)^(inghamExponent σ) := by
  obtain ⟨D,hD,H⟩ := character_ingham_upper_count hB
  let K := jensenUnitZeroDensityConst
  have hK : 0<K := jensenUnitZeroDensityConst_pos
  refine ⟨2*D*K,by positivity,?_⟩
  intro ι F q _ χ c X L σ T hinv hc hstar hX hL hT hσ hcard hq hm h₄
  let S (i : ι) := nonprincipalDensityFinset (χ i) σ T
  let P (i : ι) (z : ℂ) := χ i≠1 ∧ (χ i).LFunction z=0 ∧ σ≤z.re ∧ z.re<1
  have hupper (A : ι→Finset ℂ) (hA : ∀ i∈F,∀ z∈A i,P i z ∧ 0≤z.im ∧ z.im<L) :=
    H F q χ A hX (by omega : 1≤L) hσ hcard hq hm h₄ (by
      intro i hi z hz
      obtain ⟨⟨hn,he,hr,hr'⟩,hi',hi''⟩ := hA i hi z hz
      exact ⟨hn,he,hr,hr',hi',hi''⟩)
  have hh := symmetric_family_count_of_upper F c hinv hc (P:=P) (by
    intro i hi z hz
    obtain ⟨hn,he,hr,hr'⟩ := hz
    obtain ⟨hn',hc'⟩ := hstar i hi hn
    exact ⟨hn',hc' z he,by simpa using hr,by simpa using hr'⟩) hupper S (by
    intro i hi z hz
    obtain ⟨hn,he,_,hr,hr',ht⟩ := (mem_nonprincipalDensityFinset _).mp hz
    exact ⟨⟨hn,he,hr,hr'⟩,ht.trans_lt hT⟩)
  have hx : (1:ℝ)≤X := by exact_mod_cast (by omega : 1≤X)
  have hl : (3:ℝ)≤L := by exact_mod_cast hL
  have hc' := nonprincipal_family_multiplicity_le F q χ (σ:=σ) (T:=T) (zero_lt_one.trans_le hx) (by
    intro i hi
    have hq' : (q i:ℝ)*L≤X := by exact_mod_cast hq i hi
    calc (q i:ℝ)*(T+3) ≤ (q i:ℝ)*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
         _ = 2*((q i:ℝ)*L) := by ring
         _ ≤ _ := by linarith)
  have hlog : 0≤1+Real.log (X:ℝ) := by linarith [Real.log_nonneg hx]
  exact hc'.trans ((mul_le_mul_of_nonneg_right hh (mul_nonneg hK.le hlog)).trans_eq (by ring))

/-- Passing from a rounded cutoff up to 9H to the usual conductor-height
parameter H, with the logarithm measured at Y and H at most Y squared. -/
theorem ingham_scale_bound {X H Y σ : ℝ} (hX : 1≤X) (hH : 0≤H) (hY : 2≤Y)
    (hXH : X≤9*H) (hHY : H≤Y^2) (hσ : σ∈Set.Icc (1/2:ℝ) 1) :
    (1+Real.log X)^7*X^(inghamExponent σ) ≤
      (9*20^9)*(Real.log Y)^9*H^(inghamExponent σ) := by
  have he : 0 ≤ inghamExponent σ := by unfold inghamExponent;apply div_nonneg <;> nlinarith [hσ.2]
  have he' : inghamExponent σ≤1 := by
    unfold inghamExponent;apply (div_le_iff₀ (by linarith [hσ.2])).mpr;linarith [hσ.1]
  have hp := Real.rpow_le_rpow (zero_le_one.trans hX) hXH he
  rw [Real.mul_rpow (by norm_num) hH] at hp
  have hg : (9:ℝ)^(inghamExponent σ)≤9  := by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(9:ℝ)) he')
  have hZ := hp.trans (mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hH _))
  have hlog := Real.log_le_log (zero_lt_one.trans_le hX) (hXH.trans (mul_le_mul_of_nonneg_left hHY (by norm_num)))
  have hy₀ : 0<Y := by linarith
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hy₀.ne'),Real.log_pow] at hlog
  have hylog : 1/2≤Real.log Y := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans
    (Real.log_le_log zero_lt_two hY)
  have h9 : Real.log (9:ℝ)≤8 := by simpa only [show (9:ℝ)-1=8 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)
  norm_num only [Nat.cast_ofNat] at hlog
  have hL : 1+Real.log X≤20*Real.log Y := by linarith only [hlog,h9,hylog]
  have h₇ : (1+Real.log X)^7≤(20*Real.log Y)^9 :=
    (pow_le_pow_left₀ (by linarith [Real.log_nonneg hX]) hL 7).trans (pow_le_pow_right₀ (by linarith) (by decide))
  exact (mul_le_mul h₇ hZ (Real.rpow_nonneg (zero_le_one.trans hX) _) (by positivity [show 0≤Real.log Y by linarith])).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
