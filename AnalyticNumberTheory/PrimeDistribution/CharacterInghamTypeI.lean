import AnalyticNumberTheory.PrimeDistribution.CharacterTypeIMeans

/-!
# Ingham's type-I count for Dirichlet character families

A divisor-bounded coefficient sequence is shared by all characters.
Each dyadic block is sampled after centering its frequencies. The two
sums over dyadic blocks cost two logarithms; the divisor square costs three.
-/
noncomputable section
open Real Complex Finset
open scoped Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.PrimeDistribution
open Ingham

private lemma twist_block (a g : ℕ→ℂ) (X U i n : ℕ) :
    blockCoeff (fun j => a j*g j) X U i n=blockCoeff a X U i n*g n := by
  unfold blockCoeff;split_ifs <;>simp

private lemma block_shape {a : ℕ→ℂ} {X U i n : ℕ} (h : blockCoeff a X U i n≠0) :
    2^i≤n ∧ n≤2*2^i := by
  unfold blockCoeff at h
  split_ifs at h with hn
  · rw [←hn.2.2]
    exact ⟨Nat.pow_log_le_self 2 (by omega),(by simpa [pow_succ,Nat.mul_comm] using
      (Nat.lt_pow_succ_log_self one_lt_two n).le)⟩
  · contradiction

private theorem detected_block {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ} {L X U i : ℕ} {H K σ : ℝ}
    (hmean : CharacterHybridMean F χ L H) (hH : 0≤H) (hX : H≤X)
    (hi : i∈blocks X U) (hK : 0≤K) (hσ : σ∈Set.Icc (0:ℝ) 1)
    (S : ι→Finset ℂ) (hre : ∀p∈F,∀z∈S p,z.re∈Set.Icc σ (σ+1))
    (him : ∀p∈F,∀z∈S p,0≤z.im ∧ z.im<L)
    (hcount : ∀p∈F,∀j<L,(((S p).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K)
    {a : ℕ→ℂ} (ha : ∀n,‖a n‖≤(n.divisors.card:ℝ)) :
    (∑p∈F,∑z∈S p,‖dirichletPoly (fun n => blockCoeff a X U i n*χ p n) (2*2^i) z‖^2)≤
      (576*π^3*K)*(1+Real.log U)^3*(U:ℝ)^(2*(1-σ)) := by
  let M := 2^i
  have hM : 1≤M := Nat.one_le_pow _ _ (by decide)
  have hM0 : 0<(M:ℝ) := by exact_mod_cast hM
  obtain ⟨hXM,hMU⟩ := (mem_filter.mp hi).2
  change X<2*M at hXM
  change M≤U at hMU
  have hx : H≤2*(M:ℝ) := hX.trans (by exact_mod_cast hXM.le)
  let D := 1+Real.log U
  have hu := Real.log_nonneg (by exact_mod_cast hM.trans hMU : (1:ℝ)≤U)
  have hD : 0≤D := by dsimp [D];linarith
  have hb (n : ℕ) : ‖blockCoeff a X U i n‖^2≤(n.divisors.card:ℝ)^2 := by
    dsimp [blockCoeff];split_ifs
    · exact pow_le_pow_left₀ (norm_nonneg _) (ha n) 2
    · simp
  have hc : (∑n∈Icc 1 (2*M),‖blockCoeff a X U i n‖^2)≤(2*(M:ℝ))*(2*D)^3 := by
    apply (sum_le_sum fun n _ => hb n).trans
    have hs := sum_Icc_card_divisors_sq_le (2*M)
    rw [max_eq_left (by omega)] at hs
    push_cast at hs
    apply hs.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hMr : (1:ℝ)≤M := by exact_mod_cast hM
    have hlog0 := Real.log_nonneg (by linarith : 1≤2*(M:ℝ))
    apply pow_le_pow_left₀ (by linarith)
    rw [Real.log_mul (by norm_num) hM0.ne']
    dsimp only [D];linarith [Real.log_le_log hM0 (by exact_mod_cast hMU : (M:ℝ)≤U),
      Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpow : (M:ℝ)^2*(M:ℝ)^(-2*σ) ≤ (U:ℝ)^(2*(1-σ)) := by
    rw [←Real.rpow_two,←Real.rpow_add hM0,show 2+ -2*σ=2*(1-σ) by ring]
    exact Real.rpow_le_rpow hM0.le (by exact_mod_cast hMU) (by linarith [hσ.2])
  apply (dyadic_character_sampling hmean hH hM hK hσ.1 S hre him hcount _ (fun _ hn => block_shape hn)).trans
  calc _ ≤ 9*K*(π^3*(2*(M:ℝ)+2*M)*((2*(M:ℝ))*(2*D)^3*(M:ℝ)^(-2*σ))) := by gcongr
       _ = (576*π^3*K)*D^3*((M:ℝ)^2*(M:ℝ)^(-2*σ)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A finite family type-I estimate. The starting length dominates the
conductor-height cost of the hybrid mean square. -/
theorem character_ingham_typeI_count {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ} {L X U : ℕ}
    {H K σ V : ℝ} (hmean : CharacterHybridMean F χ L H) (hH : 0≤H) (hX : H≤X)
    (hU : 1≤U) (hK : 0≤K) (hV : 0≤V) (hσ : σ∈Set.Icc (0:ℝ) 1)
    (S : ι→Finset ℂ) (hre : ∀p∈F,∀z∈S p,z.re∈Set.Icc σ (σ+1))
    (him : ∀p∈F,∀z∈S p,0≤z.im ∧ z.im<L)
    (hcount : ∀p∈F,∀j<L,(((S p).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K)
    {a : ℕ→ℂ} (ha : ∀n,‖a n‖≤(n.divisors.card:ℝ))
    (hdet : ∀p∈F,∀z∈S p,V≤‖∑n∈Ioc X U,a n*χ p n*(n:ℂ)^(-z)‖) :
    (∑p∈F,((S p).card:ℝ))*V^2≤2304*π^3*K*(1+Real.log U)^5*(U:ℝ)^(2*(1-σ)) := by
  let J := blocks X U
  let E i p z := ‖dirichletPoly (fun n => blockCoeff a X U i n*χ p n) (2*2^i) z‖
  let D := 1+Real.log U
  let W := (U:ℝ)^(2*(1-σ))
  let C := 576*π^3*K*D^3*W
  have hD : 0≤D := by dsimp [D];linarith [Real.log_nonneg (by exact_mod_cast hU : (1:ℝ)≤U)]
  have hW : 0≤W := by dsimp [W];positivity
  have hC : 0≤C := by dsimp [C];positivity
  have each p (hp : p∈F) z (hz : z∈S p) : V^2≤(J.card:ℝ)*∑i∈J,(E i p z)^2 := by
    have hd := hdet p hp z hz
    rw [tail_by_blocks] at hd
    simp_rw [funext (twist_block a (χ p) X U _)] at hd
    have hh := hd.trans (norm_sum_le ..)
    have hc := sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun i => E i p z)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
    exact (pow_le_pow_left₀ hV hh 2).trans hc
  have hb := sum_le_sum fun p hp => sum_le_sum (each p hp)
  simp only [sum_const,nsmul_eq_mul,←mul_sum,←sum_mul] at hb
  have hswap : (∑p∈F,∑z∈S p,∑i∈J,(E i p z)^2)=∑i∈J,∑p∈F,∑z∈S p,(E i p z)^2 := by
    rw [sum_comm (s:=J) (t:=F)]
    exact sum_congr rfl fun _ _ => sum_comm
  rw [hswap] at hb
  have hb' (i : ℕ) (hi : i∈J) : (∑p∈F,∑z∈S p,(E i p z)^2)≤C :=
    detected_block hmean hH hX hi hK hσ S hre him hcount ha
  apply hb.trans
  have hs := mul_le_mul_of_nonneg_left (sum_le_sum hb') (Nat.cast_nonneg (α:=ℝ) J.card)
  simp only [sum_const,nsmul_eq_mul] at hs
  apply hs.trans
  have hJ : (J.card:ℝ)≤2*D := block_count hU
  calc _ ≤ (2*D)*((2*D)*C) := by gcongr
       _ = _ := by dsimp [C,W,D];ring

/-- Centered-block type-I estimate for a single untwisted polynomial.
The height window may reach 2X+1 while the conductor-height term is X. -/
theorem ingham_typeI_count_log_five {X U : ℕ} (hX : 1≤X) (hU : 1≤U) {a : ℕ→ℂ}
    (ha : ∀n,‖a n‖≤(n.divisors.card:ℝ)) {S : Finset ℂ} {σ K V : ℝ}
    (hσ : σ∈Set.Icc (0:ℝ) 1) (hK : 0≤K) (hV : 0≤V)
    (hre : ∀z∈S,z.re∈Set.Icc σ (σ+1)) (him : ∀z∈S,0≤z.im ∧ z.im<(2*X+1:ℕ))
    (hcount : ∀j<2*X+1,((S.filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K)
    (hdet : ∀z∈S,V≤‖∑n∈Ioc X U,a n*(n:ℂ)^(-z)‖) :
    (S.card:ℝ)*V^2≤2304*π^3*K*(1+Real.log U)^5*(U:ℝ)^(2*(1-σ)) := by
  let F := ({()} : Finset Unit)
  have hm : CharacterHybridMean F (fun _ _ => 1) (2*X+1) (X:ℝ) := by
    intro N _ b
    simp only [F,sum_singleton,mul_one]
    have HH := AnalyticNumberTheory.SieveMethods.dirichletPoly_mean_sq_Icc_le b N
      (T:=((2*X+1:ℕ):ℝ)) (Nat.cast_nonneg _)
    simp only [dirichletPoly,mul_comm _ I] at HH
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
    have hXr : (1:ℝ)≤X := by exact_mod_cast hX
    have hsq : 2≤π^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (π-3)]
    have hπ : 2*π≤π^3 := by nlinarith only [mul_le_mul_of_nonneg_right hsq Real.pi_pos.le]
    have hnx := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : 3≤π^3) (Nat.cast_nonneg (α:=ℝ) X)
    have hnn := mul_le_mul_of_nonneg_right hπ (Nat.cast_nonneg (α:=ℝ) N)
    push_cast
    nlinarith only [hnx,hnn,hXr]
  simpa only [F,sum_singleton] using character_ingham_typeI_count hm (Nat.cast_nonneg _) le_rfl
    hU hK hV hσ (fun _ => S) (fun _ _ => hre) (fun _ _ => him) (fun _ _ => hcount) ha
    (fun _ _ z hz => by simpa only [mul_one] using hdet z hz)

end AnalyticNumberTheory.PrimeDistribution
