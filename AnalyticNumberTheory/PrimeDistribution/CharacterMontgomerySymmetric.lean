import AnalyticNumberTheory.PrimeDistribution.MontgomeryDetectorCounts
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamSymmetric

/-! # Montgomery's zero-density estimate for nonprincipal characters -/
noncomputable section
open Finset Complex Real Filter MeasureTheory
open scoped Classical ComplexConjugate ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

private def detectorConstant : ℝ := 1+32*729*‖(720/(2*π):ℂ)‖
private theorem detectorConstant_pos : 0<detectorConstant := by dsimp [detectorConstant];positivity

private theorem character_montgomery_alternatives {q X : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {σ Y : ℝ} {z : ℂ} (hn : χ≠1) (hx : 1≤X) (hy : 16≤Y) (hσ : 3/4≤σ)
    (hr : σ≤z.re) (hr' : z.re<1) (hz : χ.LFunction z=0) :
    1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*χ n*(n:ℂ)^(-z)‖ ∨
    ∀ᶠ U : ℝ in atTop,1/(detectorConstant*Y^(1/2-σ)) ≤ ∫ t in -U..U,
      1/(1+|t-z.im|)^6*‖χ.LFunction ((1/2:ℂ)+t*I)‖*criticalMollifierNorm (fun n => χ n) X t := by
  rcases character_detector_window hn hx hy (by norm_num : 0<(1/4:ℝ)) (by linarith) hr' hz with h|h
  · exact Or.inl (by linarith)
  right
  filter_upwards [h,eventually_ge_atTop (0:ℝ)] with U hU hu
  let W := ∫ t in -U..U,1/(1+|t-z.im|)^6*‖χ.LFunction ((1/2:ℂ)+t*I)‖*criticalMollifierNorm (fun n => χ n) X t
  have hW : 0≤W := intervalIntegral.integral_nonneg (neg_le_self hu) (fun t _ => by dsimp [criticalMollifierNorm];positivity)
  have hy₀ : 0<Y := by linarith
  have hle := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Y) (by linarith : 1/2-z.re≤1/2-σ)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle
    (by positivity : 0≤729*‖(720/(2*π):ℂ)‖/(1/4:ℝ))) hW
  change 1/8≤(729*‖(720/(2*π):ℂ)‖/(1/4:ℝ)*Y^(1/2-z.re))*W at hU
  apply (div_le_iff₀ (by positivity [detectorConstant_pos] : 0<detectorConstant*Y^(1/2-σ))).mpr
  change 1≤W*(detectorConstant*Y^(1/2-σ))
  dsimp only [detectorConstant]
  linarith only [hU.trans hmul,mul_nonneg (Real.rpow_nonneg hy₀.le (1/2-σ)) hW]

/-- Upper-half nonprincipal zero count under a sparse family mean square and
a fourth moment on the critical line. -/
theorem character_montgomery_upper_count {B C : ℝ} (hB : 0<B) (hC : 0<C) :
    ∃ D : ℝ,0<D ∧ ∀ {ι : Type*} (F : Finset ι) (q : ι→ℕ) [∀ i,NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (S : ι→Finset ℂ) {X L : ℕ} {σ : ℝ},
    16≤X → 1≤L → σ∈Set.Icc (4/5:ℝ) 1 → F.card*L≤X → (∀ i∈F,q i*L≤X) →
    SparseCharacterBound F (fun i n => χ i n) L (X:ℝ) C →
    (∀ j : ℕ,(∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,‖(χ i).LFunction ((1/2:ℂ)+t*I)‖^4)
      ≤ B*(2^j*(X:ℝ))*(1+Real.log (2^j*(X:ℝ)))^4) →
    (∀ i∈F,∀ z∈S i,χ i≠1 ∧ (χ i).LFunction z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0≤z.im ∧ z.im<L) →
    (∑ i∈F,((S i).card:ℝ))≤D*(1+Real.log X)^11*(X:ℝ)^(montgomeryExponent σ) := by
  let K := max 1 jensenUnitZeroDensityConst
  have hK : 1≤K := le_max_left _ _
  obtain ⟨D,hD,HD⟩ := montgomery_count_of_alternatives hC hB detectorConstant_pos hK
  refine ⟨D,hD,?_⟩
  intro ι F q _ χ S X L σ hX hL hσ hcard hq hm h₄ hS
  let R := ∑ i∈F,((S i).card:ℝ)
  let Y := montgomeryCutoff X σ
  let N := montgomeryMollifierLength R X
  have hx : (16:ℝ)≤X := by exact_mod_cast hX
  have hx₁ : (1:ℝ)≤X := by linarith
  have hσ' : σ∈Set.Icc (1/2:ℝ) 1 := ⟨by linarith [hσ.1],hσ.2⟩
  have hy : 16≤Y := hx.trans (montgomeryCutoff_bounds hx₁ hσ').1
  have hlog : 0≤1+Real.log (X:ℝ) := by linarith [Real.log_nonneg hx₁]
  have him (i) (hi : i∈F) (z) (hz : z∈S i) := (hS i hi z hz).2.2.2.2
  have hc (i) (hi : i∈F) (j : ℕ) (hj : j<L) := (nonprincipal_density_unit_count
    (hq i hi) hL hσ'.1 (S i) (hS i hi) j hj).trans (mul_le_mul_of_nonneg_right (le_max_right 1 _) hlog)
  have hcoarse := sum_le_sum (s:=F) (fun i hi => count_from_cells (S i) (him i hi) (hc i hi))
  simp only [sum_const,nsmul_eq_mul] at hcoarse
  have hbound : R≤K*X*(1+Real.log X) := hcoarse.trans (by
    have ht := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard : (F.card:ℝ)*L≤X)
      (mul_nonneg (zero_le_one.trans hK) hlog)
    change _≤(max 1 jensenUnitZeroDensityConst)*(X:ℝ)*(1+Real.log X)
    dsimp only [K] at ht;linarith only [ht])
  have h4' (j : ℕ) := (h₄ j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (show 0≤1+Real.log (2^j*(X:ℝ)) by
      have h' := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : 1≤(2:ℝ)) (n:=j)) hx₁
      linarith [Real.log_nonneg h']) (dyadic_logarithm_bound hx₁ j) 4) (by positivity : 0≤B*(2^j*(X:ℝ))))
  apply HD F (fun i n => χ i n) S (fun i t => ‖(χ i).LFunction ((1/2:ℂ)+t*I)‖)
    hx₁ hL hσ' hm (fun i _ => (continuous_character_critical_line (χ i)).norm)
    (fun i hi z hz => ⟨(hS i hi z hz).2.2.1,(hS i hi z hz).2.2.2.1.le⟩)
    him hc hbound (fun j => (h4' j).trans_eq (by ring)) (inghamRieszCoeff N Y)
    (norm_inghamRieszCoeff (by linarith : 0<Y) N)
  intro i hi z hz
  obtain ⟨hn,he,hr,hr',_⟩ := hS i hi z hz
  have hr₁ : 1≤R := (by exact_mod_cast card_pos.mpr ⟨z,hz⟩ : (1:ℝ)≤(S i).card).trans
    (single_le_sum (f:=fun i => ((S i).card:ℝ)) (fun j _ => Nat.cast_nonneg _) hi)
  have hN : 1≤N := by exact_mod_cast (one_le_mul_of_one_le_of_one_le hr₁
    (by simpa using Real.sqrt_le_sqrt hx₁ : 1≤Real.sqrt (X:ℝ))).trans (montgomeryMollifierLength_bounds hr₁ hx₁).1
  exact character_montgomery_alternatives hn hN hy (by linarith [hσ.1]) hr hr' he


/-- Count all nonprincipal zeros of a conjugation-stable family with analytic
multiplicity. The conductor-height parameter is X and the height of the samples is less than L. -/
theorem character_montgomery_symmetric_weighted {B C₀ : ℝ} (hB : 0<B) (hC₀ : 0<C₀) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} (F : Finset ι) (q : ι→ℕ) [∀ i,NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (c : ι→ι) {X L : ℕ} {σ T : ℝ},
    Function.Involutive c → (∀ i∈F,c i∈F) →
    (∀ i∈F,χ (c i)≠1 → χ i≠1 ∧ ∀ z,(χ (c i)).LFunction z=0 → (χ i).LFunction (conj z)=0) →
    16≤X → 3≤L → T<L → σ∈Set.Icc (4/5:ℝ) 1 → F.card*L≤X → (∀ i∈F,q i*L≤X) →
    SparseCharacterBound F (fun i n => χ i n) L (X:ℝ) C₀ →
    (∀ j : ℕ, (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,‖(χ i).LFunction ((1/2:ℂ)+t*I)‖^4)
      ≤ B*(2^j*(X:ℝ))*(1+Real.log (2^j*(X:ℝ)))^4) →
    (∑ i∈F,∑ z∈nonprincipalDensityFinset (χ i) σ T,(characterZeroMultiplicity (χ i) z:ℝ))
      ≤ C*(1+Real.log X)^12*(X:ℝ)^(montgomeryExponent σ) := by
  obtain ⟨D,hD,H⟩ := character_montgomery_upper_count hB hC₀
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

end AnalyticNumberTheory.PrimeDistribution
