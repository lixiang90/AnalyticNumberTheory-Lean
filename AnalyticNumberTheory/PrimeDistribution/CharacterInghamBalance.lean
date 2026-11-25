import AnalyticNumberTheory.PrimeDistribution.CharacterInghamTypeI
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamTypeII
import AnalyticNumberTheory.PrimeDistribution.CharacterMollifierMean
import AnalyticNumberTheory.PrimeDistribution.CharacterDetectorWindow
import AnalyticNumberTheory.PrimeDistribution.InghamBalance
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveMomentComparison

/-! # The balanced Ingham estimate for character zeros above the critical line -/
noncomputable section
open Finset Real Complex Filter MeasureTheory
open scoped ArithmeticFunction.Moebius Topology Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

private def polyAlternative {ι : Type*} (χ : ι→ℕ→ℂ) (X : ℕ) (Y : ℝ) (i : ι) (z : ℂ) : Prop :=
  1/4≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*χ i n*(n:ℂ)^(-z)‖

private theorem polynomial_count {ι : Type*} (F : Finset ι) (χ : ι→ℕ→ℂ) (S : ι→Finset ℂ)
    {X L : ℕ} {σ K : ℝ} (hX : 1≤X) (hK : 0≤K) (hσ : σ∈Set.Icc (1/2:ℝ) 1)
    (hm : CharacterHybridMean F χ L X)
    (hre : ∀ i∈F,∀ z∈S i,σ≤z.re ∧ z.re<1) (him : ∀ i∈F,∀ z∈S i,0≤z.im ∧ z.im<L)
    (hc : ∀ i∈F,∀ j<L,(((S i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K*(1+Real.log X))
    (hd : ∀ i∈F,∀ z∈S i,polyAlternative χ X (inghamCutoff X σ) i z) :
    (∑ i∈F,((S i).card:ℝ))≤(16*2304*π^3*K*2^5)*(1+Real.log X)^6*(X:ℝ)^(inghamExponent σ) := by
  let Y := inghamCutoff X σ
  let ℓ := 1+Real.log X
  have hx : (1:ℝ)≤X := by exact_mod_cast hX
  have hℓ : 1≤ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hx]
  obtain ⟨hXY,hY⟩ := inghamCutoff_range hx hσ
  have hY1 : 1≤Y := hx.trans hXY
  have hY0 : 0<Y := zero_lt_one.trans_le hY1
  have hN : 1≤⌊Y⌋₊ := (Nat.one_le_floor_iff _).mpr hY1
  have h := character_ingham_typeI_count hm (Nat.cast_nonneg X) le_rfl hN (mul_nonneg hK (by linarith : 0≤ℓ))
    (by norm_num : (0:ℝ)≤1/4) ⟨by linarith [hσ.1],hσ.2⟩ S
    (fun i hi z hz => ⟨(hre i hi z hz).1,by linarith [(hre i hi z hz).2,hσ.1]⟩) him hc
    (norm_inghamRieszCoeff hY0 X) hd
  have hlog := (Real.log_le_log (show (0:ℝ)<⌊Y⌋₊ by exact_mod_cast (Nat.zero_lt_of_lt hN)) (Nat.floor_le hY0.le)).trans
    (Real.log_le_log hY0 hY)
  rw [Real.log_rpow (zero_lt_one.trans_le hx)] at hlog
  have hlog' : 1+Real.log (⌊Y⌋₊:ℝ)≤2*ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hx]
  have hlog₀ : 0≤1+Real.log (⌊Y⌋₊:ℝ) := by linarith [Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤⌊Y⌋₊)]
  have hpow := (Real.rpow_le_rpow (Nat.cast_nonneg ⌊Y⌋₊) (Nat.floor_le hY0.le) (by linarith [hσ.2] : 0≤2*(1-σ))).trans_eq
    (inghamCutoff_balance (zero_lt_one.trans_le hx) hσ.2).1
  have he : (∑ i∈F,((S i).card:ℝ))*(1/4:ℝ)^2 ≤ 2304*π^3*(K*ℓ)*(2*ℓ)^5*(X:ℝ)^(inghamExponent σ) := by
    apply h.trans
    apply mul_le_mul _ hpow (by positivity) (by positivity [show 0≤ℓ by linarith])
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog₀ hlog' _) (by positivity [show 0≤ℓ by linarith])
  change _≤(16*2304*π^3*K*2^5)*ℓ^6*_
  linarith only [he]

private def windowConstant : ℝ := 1+729*‖(720/(2*π):ℂ)‖
private theorem windowConstant_pos : 0<windowConstant := by dsimp [windowConstant];positivity

private theorem integral_alternative {q X : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hX : 16≤X) {σ : ℝ} (hσ : σ∈Set.Icc (1/2:ℝ) 1) (hgap : 1/(1+Real.log X)≤σ-1/2)
    {z : ℂ} (hχ : χ≠1) (hz : χ.LFunction z=0) (hr : σ≤z.re) (hr' : z.re<1)
    (hn : ¬polyAlternative (fun (_ : Unit) n => χ n) X (inghamCutoff X σ) () z) :
    ∀ᶠ R : ℝ in atTop, 1/(8*(windowConstant*(1+Real.log X)*(inghamCutoff X σ)^(1/2-σ))) ≤
      ∫ t in -R..R,1/(1+|t-z.im|)^6*‖χ.LFunction ((1/2:ℂ)+t*I)‖*
        ‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X ((1/2:ℂ)+t*I)‖ := by
  let Y := inghamCutoff X σ
  let ℓ := 1+Real.log X
  have hx : (16:ℝ)≤X := by exact_mod_cast hX
  have hx₁ : (1:ℝ)≤X := by linarith
  have hℓ : 0<ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hx₁]
  have hXY := (inghamCutoff_range hx₁ hσ).1
  have hY₁ : 1≤Y := hx₁.trans hXY
  have hY₀ : 0<Y := zero_lt_one.trans_le hY₁
  have he := (character_detector_window hχ (by omega : 1≤X) (hx.trans hXY)
    (one_div_pos.mpr hℓ) (by linarith [hgap] : 1/ℓ≤z.re-1/2) hr' hz).resolve_left hn
  filter_upwards [he,eventually_ge_atTop (0:ℝ)] with R hR hR₀
  let J := ∫ t in -R..R,1/(1+|t-z.im|)^6*‖χ.LFunction ((1/2:ℂ)+t*I)‖*
        ‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X ((1/2:ℂ)+t*I)‖
  have hJ : 0≤J := intervalIntegral.integral_nonneg (neg_le_self hR₀) (fun t _ => by positivity)
  have hA : 729*‖(720/(2*π):ℂ)‖≤windowConstant := by dsimp [windowConstant];linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hY₁ (by linarith : 1/2-z.re≤1/2-σ)
  change 1/8≤(729*‖(720/(2*π):ℂ)‖/(1/ℓ)*Y^(1/2-z.re))*J at hR
  rw [div_div_eq_mul_div,div_one] at hR
  have hle := mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right hA hℓ.le)
    hp (Real.rpow_nonneg hY₀.le _) (mul_nonneg windowConstant_pos.le hℓ.le)) hJ
  apply (div_le_iff₀ (by positivity [windowConstant_pos] : 0<8*(windowConstant*ℓ*Y^(1/2-σ)))).mpr
  change 1≤J*(8*(windowConstant*ℓ*Y^(1/2-σ)))
  linarith only [hR.trans hle]

/-- Ingham's balanced exponent for distinct zeros of a character family, assuming
its two hybrid mean-value inputs. This upper-half estimate includes real zeros. -/
theorem character_ingham_balanced {B K : ℝ} (hB : 0<B) (hK : 0<K) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} (F : Finset ι) (q : ι→ℕ) [∀ i,NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (S : ι → Finset ℂ) {X L : ℕ} {σ : ℝ},
    16≤X → 1≤L → σ∈Set.Icc (1/2:ℝ) 1 → 1/(1+Real.log X)≤σ-1/2 →
    (∀ m : ℕ,1≤m → CharacterHybridMean F (fun i n => χ i n) (m*L) ((m:ℝ)*X)) →
    (∀ j : ℕ, (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,‖(χ i).LFunction ((1/2:ℂ)+t*I)‖^4)
      ≤ (B*X*(1+Real.log X)^4)*2^j*((j:ℝ)+1)^4) →
    (∀ i∈F,∀ z∈S i,χ i≠1 ∧ (χ i).LFunction z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0≤z.im ∧ z.im<L) →
    (∀ i∈F,∀ j<L,(((S i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K*(1+Real.log X)) →
    (∑ i∈F,((S i).card:ℝ))≤C*(1+Real.log X)^6*(X:ℝ)^(inghamExponent σ) := by
  obtain ⟨D,hD,H⟩ := character_ingham_typeII_count
  let E := D*B*(3*π^3)^2
  let C₁ := 16*2304*π^3*K*2^5
  let C₂ := 1+E*K^3*(8*windowConstant)^4
  have hE : 0<E := by dsimp [E];positivity
  have h₁ : 0<C₁ := by dsimp [C₁];positivity
  have h₂ : 0<C₂ := by dsimp [C₂];positivity
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro ι F q _ χ S X L σ hX hL hσ hgap hm h₄ hS hc
  let Y := inghamCutoff X σ
  let ℓ := 1+Real.log X
  let Z := (X:ℝ)^(inghamExponent σ)
  let P (i : ι) := polyAlternative (fun i n => χ i n) X Y i
  let S₁ (i : ι) := (S i).filter (P i)
  let S₂ (i : ι) := (S i).filter (fun z => ¬P i z)
  let n₁ := ∑ i∈F,((S₁ i).card:ℝ)
  let n₂ := ∑ i∈F,((S₂ i).card:ℝ)
  have hx : (1:ℝ)≤X := by exact_mod_cast (by omega : 1≤X)
  have hℓ : 1≤ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hx]
  have hl₀ : 0<ℓ := zero_lt_one.trans_le hℓ
  have hZ : 0≤Z := Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hY : 0<Y := zero_lt_one.trans_le (hx.trans (inghamCutoff_range hx hσ).1)
  have hloc (W : ι → Finset ℂ) (hs : ∀ i,W i⊆S i) (i) (hi : i∈F) (j : ℕ) (hj : j<L) :
      (((W i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K*ℓ := by
    apply le_trans _ (hc i hi j hj)
    exact_mod_cast card_le_card (filter_subset_filter _ (hs i))
  have hI := polynomial_count F (fun i n => χ i n) S₁ (by omega : 1≤X) hK.le hσ
    (by simpa only [one_mul,Nat.cast_one] using hm 1 le_rfl)
    (fun i hi z hz => ⟨(hS i hi z (mem_filter.mp hz).1).2.2.1,(hS i hi z (mem_filter.mp hz).1).2.2.2.1⟩)
    (fun i hi z hz => (hS i hi z (mem_filter.mp hz).1).2.2.2.2)
    (hloc _ (fun i => filter_subset ..)) (fun i _ z hz => (mem_filter.mp hz).2)
  change n₁≤C₁*ℓ^6*Z at hI
  let V := 1/(8*(windowConstant*ℓ*Y^(1/2-σ)))
  have hV : 0≤V := by dsimp [V];positivity [windowConstant_pos]
  let f (i : ι) (t : ℝ) := ‖(χ i).LFunction ((1/2:ℂ)+t*I)‖
  let g (i : ι) (t : ℝ) := ‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+t*I)‖
  have hg (i : ι) : Continuous (g i) := ((differentiable_dirichletPoly _ X).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (1/2:ℂ)+t*I))).norm
  have hII := H F S₂ hL (mul_nonneg hK.le hl₀.le)
    (by positivity : 0≤B*X*ℓ^4) (by positivity : 0≤3*π^3*X*ℓ) hV
    (fun i hi z hz => (hS i hi z (mem_filter.mp hz).1).2.2.2.2)
    (hloc S₂ (fun i => filter_subset ..)) f g
    (fun i _ => (continuous_character_critical_line (χ i)).norm) (fun i _ => hg i) h₄
    (character_mollifier_dyadic_mean hm (by omega : 1≤X)) (by
      intro i hi z hz
      obtain ⟨hχ,hz₀,hr,hr',_⟩ := hS i hi z (mem_filter.mp hz).1
      exact integral_alternative hX hσ hgap hχ hz₀ hr hr' (mem_filter.mp hz).2)
  have hb : n₂^3*V^4≤E*(K*ℓ)^3*X^3*ℓ^6 := hII.trans_eq (by dsimp only [E];ring)
  have hII' : n₂≤C₂*ℓ^5*Z := ingham_balanced_cubic hx hσ.2
    (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) windowConstant_pos hE hK.le hb
  have hII'' := hII'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ (by decide : 5≤6)) h₂.le) hZ)
  have hcard : (∑ i∈F,((S i).card:ℝ))=n₁+n₂ := by
    dsimp only [n₁,n₂];rw [←sum_add_distrib]
    apply sum_congr rfl;intro i _
    exact_mod_cast (card_filter_add_card_filter_not (s:=S i) (P i)).symm
  change _≤(C₁+C₂)*ℓ^6*Z
  linarith only [hcard,hI,hII'']

end AnalyticNumberTheory.PrimeDistribution
