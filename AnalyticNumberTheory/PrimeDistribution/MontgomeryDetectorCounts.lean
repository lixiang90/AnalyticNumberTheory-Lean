import AnalyticNumberTheory.DirichletLFunctions.AbsolutePolynomialBounds
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityBalance
import AnalyticNumberTheory.PrimeDistribution.SparseMontgomeryTypeI
import AnalyticNumberTheory.PrimeDistribution.SparseMollifierMean
import AnalyticNumberTheory.PrimeDistribution.SparseDetectorIntegral

/-! # Montgomery's density bound from the two zero detectors -/
noncomputable section
open Finset Real Complex MeasureTheory Filter
open scoped ArithmeticFunction.Moebius Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- The absolute value of the Möbius mollifier on the critical line. -/
def criticalMollifierNorm (χ : ℕ→ℂ) (X : ℕ) (t : ℝ) : ℝ :=
  ‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X ((1/2:ℂ)+t*I)‖

/-- Shared sparse large sieve and fourth moment inputs imply a uniform bound
for samples that pass either the polynomial or the integral detector. The
mollifier length depends on the total number of samples in the family. -/
theorem montgomery_count_of_alternatives {C B A K : ℝ}
    (hC : 0<C) (hB : 0<B) (hA : 0<A) (hK : 1≤K) :
    ∃ D : ℝ,0<D ∧ ∀ {ι : Type*} (F : Finset ι) (χ : ι→ℕ→ℂ) (S : ι→Finset ℂ)
      (f : ι→ℝ→ℝ) {H σ : ℝ} {L : ℕ}, 1≤H → 1≤L → σ∈Set.Icc (1/2:ℝ) 1 →
    SparseCharacterBound F χ L H C → (∀ i∈F,Continuous (f i)) →
    (∀ i∈F,∀ z∈S i,z.re∈Set.Icc σ 1) → (∀ i∈F,∀ z∈S i,0≤z.im ∧ z.im<L) →
    (∀ i∈F,∀ j<L,(((S i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K*(1+Real.log H)) →
    (∑ i∈F,((S i).card:ℝ))≤K*H*(1+Real.log H) →
    (∀ j : ℕ,(∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,(f i t)^4)
        ≤ (B*H*(1+Real.log H)^4)*2^j*((j:ℝ)+1)^4) →
    let Y := montgomeryCutoff H σ
    let X := montgomeryMollifierLength (∑ i∈F,((S i).card:ℝ)) H
    ∀ a : ℕ→ℂ,(∀ n,‖a n‖≤(n.divisors.card:ℝ)) →
    (∀ i∈F,∀ z∈S i,
      1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,a n*χ i n*(n:ℂ)^(-z)‖ ∨
      ∀ᶠ U : ℝ in atTop,1/(A*Y^(1/2-σ)) ≤
        ∫ t in -U..U,1/(1+|t-z.im|)^6*f i t*criticalMollifierNorm (χ i) X t) →
    (∑ i∈F,((S i).card:ℝ))≤D*(1+Real.log H)^11*H^(montgomeryExponent σ) := by
  obtain ⟨E,hE,HE⟩ := sparse_integral_detector_count
  let J := 4+Real.log (2*K)
  have hJ : 0<J := by dsimp [J];linarith [Real.log_nonneg (by linarith : 1≤2*K)]
  let M := 8*C*(2*K+1)*J^2
  let D₁ := 64*128*C*(K+1)*2^5
  let D₂ := E*K*B*M^2*A^4
  have hK₀ : 0<K := zero_lt_one.trans_le hK
  have hM : 0<M := by dsimp [M];positivity
  have h₁ : 0<D₁ := by dsimp [D₁];positivity
  have h₂ : 0<D₂ := by dsimp [D₂];positivity
  refine ⟨2*D₁+8*D₂,by positivity,?_⟩
  intro ι F χ S f H σ L hH hL hσ hs hf hre him hc hcoarse h₄
  let R := ∑ i∈F,((S i).card:ℝ)
  let X := montgomeryMollifierLength R H
  let Y := montgomeryCutoff H σ
  let ℓ := 1+Real.log H
  let Z := H^(montgomeryExponent σ)
  dsimp only
  intro a ha hd
  have hpos := zero_lt_one.trans_le hH
  have hℓ : 1≤ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hH]
  have hl₀ := zero_lt_one.trans_le hℓ
  have hZ : 0<Z := Real.rpow_pos_of_pos hpos _
  change R≤(2*D₁+8*D₂)*ℓ^11*Z
  by_cases hR : R=0
  · rw [hR];positivity
  have hnat : R=((∑ i∈F,(S i).card:ℕ):ℝ) := by simp [R]
  have hr : 1≤R := by
    rw [hnat] at hR ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hR (by simp [h]))
  have hr₀ := zero_lt_one.trans_le hr
  have hb := montgomeryMollifierLength_bounds hr hH
  have hsqrt : 1≤Real.sqrt H := by simpa using Real.sqrt_le_sqrt hH
  have hx : 1≤X := by exact_mod_cast (one_le_mul_of_one_le_of_one_le hr hsqrt).trans hb.1
  have hxlog := montgomeryMollifierLength_log hK hr hH hcoarse
  have hy := montgomeryCutoff_bounds hH hσ
  have hy₁ := hH.trans hy.1
  have hy₀ := zero_lt_one.trans_le hy₁
  have hU : 1≤⌊Y⌋₊ := (Nat.one_le_floor_iff _).mpr hy₁
  have hu₀ : (0:ℝ)<⌊Y⌋₊ := by exact_mod_cast Nat.zero_lt_of_lt hU
  have hlog := (Real.log_le_log hu₀ (Nat.floor_le hy₀.le)).trans (Real.log_le_log hy₀ hy.2)
  rw [Real.log_pow] at hlog
  have hlog' : 1+Real.log (⌊Y⌋₊:ℝ)≤2*ℓ := by dsimp [ℓ];push_cast at hlog;linarith
  have hlog₀ : 0≤1+Real.log (⌊Y⌋₊:ℝ) := by linarith [Real.log_nonneg (by exact_mod_cast hU : (1:ℝ)≤⌊Y⌋₊)]
  let P (i : ι) (z : ℂ) := 1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,a n*χ i n*(n:ℂ)^(-z)‖
  let S₁ (i : ι) := (S i).filter (P i)
  let S₂ (i : ι) := (S i).filter (fun z => ¬P i z)
  let r₁ := ∑ i∈F,((S₁ i).card:ℝ)
  let r₂ := ∑ i∈F,((S₂ i).card:ℝ)
  have hcard : R=r₁+r₂ := by
    dsimp only [R,r₁,r₂];rw [←sum_add_distrib]
    apply sum_congr rfl;intro i _
    exact_mod_cast (card_filter_add_card_filter_not (s:=S i) (P i)).symm
  have hr₁ : 0≤r₁ := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hr₂ : 0≤r₂ := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hloc (W : ι→Finset ℂ) (hw : ∀ i,W i⊆S i) (i) (hi : i∈F) (j : ℕ) (hj : j<L) :
      (((W i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K*ℓ := by
    apply le_trans _ (hc i hi j hj)
    exact_mod_cast card_le_card (filter_subset_filter _ (hw i))
  have hI := sparse_montgomery_typeI_count hC hs hH hU (mul_nonneg hK₀.le hl₀.le)
    (by norm_num : (0:ℝ)≤1/8) ⟨by linarith [hσ.1],hσ.2⟩ S₁
    (fun i hi z hz => hre i hi z (mem_filter.mp hz).1) (fun i hi z hz => him i hi z (mem_filter.mp hz).1)
    (hloc _ (fun i => filter_subset ..))
    ((mul_le_mul_of_nonneg_right (by linarith only [hcard,hr₂] : r₁≤R) (Real.sqrt_nonneg H)).trans hb.1)
    ha (fun _ _ _ hz => (mem_filter.mp hz).2)
  have hp := (Real.rpow_le_rpow (Nat.cast_nonneg ⌊Y⌋₊) (Nat.floor_le hy₀.le)
    (by linarith [hσ.2] : 0≤2*(1-σ))).trans_eq (montgomeryCutoff_balance hpos (by linarith [hσ.1] : 0<σ)).1
  have hsum : K*ℓ+1+Real.log H=(K+1)*ℓ := by dsimp [ℓ];ring
  rw [hsum] at hI
  have hI' := hI.trans (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog₀ hlog' 5)
    (by positivity : 0≤128*C*((K+1)*ℓ))) hp (by positivity) (by positivity))
  have hsmall : r₁≤D₁*ℓ^6*Z := by
    change r₁*(1/8:ℝ)^2≤128*C*((K+1)*ℓ)*(2*ℓ)^5*Z at hI'
    dsimp only [D₁];linarith only [hI']
  have hsmall' := hsmall.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ (by decide : 6≤11)) h₁.le) hZ.le)
  let g (i : ι) := criticalMollifierNorm (χ i) X
  have hg (i : ι) : Continuous (g i) := ((differentiable_dirichletPoly _ X).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (1/2:ℂ)+t*I))).norm
  have hd₂ (v : ℝ) : (∑ i∈F,∑ z∈S₂ i,(g i (v+z.im))^2)≤M*R*Real.sqrt H*ℓ^3 := by
    have h := sparse_mollifier_second_mean hs hH hC.le hx (mul_nonneg hK₀.le hl₀.le) S₂
      (fun i hi z hz => him i hi z (mem_filter.mp hz).1) (hloc _ (fun i => filter_subset ..)) v
    have hcost : K*ℓ*X+r₂*Real.sqrt H*ℓ ≤ (2*K+1)*R*Real.sqrt H*ℓ := by
      have hle := mul_le_mul_of_nonneg_left hb.2 (mul_nonneg hK₀.le hl₀.le)
      have hle' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by linarith only [hcard,hr₁] : r₂≤R) (Real.sqrt_nonneg H)) hl₀.le
      change K*ℓ*(X:ℝ)≤_ at hle
      linarith only [hle,hle']
    have hxℓ : 0≤1+Real.log (X:ℝ) := by linarith [Real.log_nonneg (by exact_mod_cast hx : (1:ℝ)≤X)]
    exact h.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hcost (by positivity : 0≤8*C))
      (pow_le_pow_left₀ hxℓ hxlog 2) (sq_nonneg _) (mul_nonneg (by positivity : 0≤8*C) (mul_nonneg (mul_nonneg (mul_nonneg (by positivity : 0≤2*K+1) hr₀.le) (Real.sqrt_nonneg H)) hl₀.le))).trans_eq (by change 8*C*((2*K+1)*R*Real.sqrt H*ℓ)*(J*ℓ)^2=M*R*Real.sqrt H*ℓ^3;dsimp only [M];ring))
  let V := 1/(A*Y^(1/2-σ))
  have hII := HE F S₂ hL (mul_nonneg hK₀.le hl₀.le) (by positivity : 0≤B*H*ℓ^4)
    (mul_nonneg (mul_nonneg (mul_nonneg hM.le hr₀.le) (Real.sqrt_nonneg H)) (pow_nonneg hl₀.le 3)) (one_div_nonneg.mpr (mul_nonneg hA.le (Real.rpow_nonneg hy₀.le _)) : 0≤V)
    (fun i hi z hz => him i hi z (mem_filter.mp hz).1) (hloc _ (fun i => filter_subset ..))
    f g hf (fun i _ => hg i) h₄ hd₂
    (fun i hi z hz => (hd i hi z (mem_filter.mp hz).1).resolve_left (mem_filter.mp hz).2)
  have hcube : r₂^3*V^4 ≤ (E*K*B*M^2)*R^2*H^2*ℓ^11 := hII.trans_eq (by
    calc _ = (E*K*B*M^2)*R^2*H*(Real.sqrt H)^2*ℓ^11 := by ring
         _ = _ := by rw [Real.sq_sqrt hpos.le];ring)
  have hlarge := montgomery_cubic_balance hpos (by linarith [hσ.1] : 0<σ) hA hcube
  exact (montgomery_count_absorption hr₀ hcard hr₂ h₁.le h₂.le (by positivity : 0≤ℓ^11*Z)
    (hsmall'.trans_eq (by ring)) (hlarge.trans_eq (by dsimp only [D₂,Z];ring))).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
