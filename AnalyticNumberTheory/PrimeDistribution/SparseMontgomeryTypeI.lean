import AnalyticNumberTheory.PrimeDistribution.SparseDyadicPolynomials

/-!
# Montgomery's sparse type-I estimate

A common real power is absorbed into the coefficients before applying the
sparse family inequality. The lower cutoff controls the off-diagonal
correlation term separately on every occupied dyadic block.
-/
noncomputable section
open Finset Complex Real
open scoped Classical
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution
open Ingham

private theorem shifted_block_square {a : ℕ→ℂ} {X U j : ℕ} {σ : ℝ} (hσ : 0≤σ)
    (ha : ∀n,‖a n‖≤(n.divisors.card:ℝ)) :
    (∑n∈Icc (2^j) (2*2^j),‖blockCoeff a X U j n*(n:ℂ)^(-(σ:ℂ))‖^2) ≤
      (2*((2^j:ℕ):ℝ))*(1+Real.log (2*((2^j:ℕ):ℝ)))^3*((2^j:ℕ):ℝ)^(-2*σ) := by
  let M := 2^j
  have hM : 1≤M := Nat.one_le_pow _ _ (by decide)
  apply le_trans _ (block_energy (X:=X) (U:=U) (i:=j) ha hσ)
  unfold dirichletPolyEnergy
  apply le_trans (b:=∑n∈Icc 1 (2*M),‖blockCoeff a X U j n*(n:ℂ)^(-(σ:ℂ))‖^2)
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left hM) (fun _ _ _ => sq_nonneg _))
  apply le_of_eq
  apply sum_congr rfl
  intro n hn
  rw [norm_mul,mul_pow,Complex.norm_natCast_cpow_of_pos (mem_Icc.mp hn).1,
    ←Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 2
  simp <;> ring

/-- Sparse square mean in a single dyadic block. The constant 32 is absolute. -/
theorem sparse_montgomery_typeI_block {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ}
    {L X U j : ℕ} {H C K σ : ℝ} (hC : 0<C) (hm : SparseCharacterBound F χ L H C)
    (hH : 1≤H) (hK : 0≤K) (hσ : σ∈Set.Icc (0:ℝ) 1)
    (S : ι→Finset ℂ) (hre : ∀p∈F,∀z∈S p,z.re∈Set.Icc σ 1)
    (him : ∀p∈F,∀z∈S p,0≤z.im ∧ z.im<L)
    (hcount : ∀p∈F,∀j<L,(((S p).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K)
    (hX : (∑p∈F,((S p).card:ℝ))*Real.sqrt H≤X)
    {a : ℕ→ℂ} (ha : ∀n,‖a n‖≤(n.divisors.card:ℝ)) (hj : j∈blocks X U) :
    (∑p∈F,∑z∈S p,‖∑n∈Icc (2^j) (2*2^j),blockCoeff a X U j n*χ p n*(n:ℂ)^(-z)‖^2) ≤
      32*C*(K+1+Real.log H)*(1+Real.log U)^3*(U:ℝ)^(2*(1-σ)) := by
  let M := 2^j
  let R := ∑p∈F,((S p).card:ℝ)
  let A := K+1+Real.log H
  let D := 1+Real.log U
  let b (n : ℕ) := blockCoeff a X U j n*(n:ℂ)^(-(σ:ℂ))
  let u (z : ℂ) := z-(σ:ℂ)
  have hM : 1≤M := Nat.one_le_pow _ _ (by decide)
  have hM₀ : 0<(M:ℝ) := by exact_mod_cast hM
  obtain ⟨hx,hmu⟩ := (mem_filter.mp hj).2
  change X<2*M at hx
  change M≤U at hmu
  have hU : (1:ℝ)≤U := by exact_mod_cast hM.trans hmu
  have hA : 0≤A := by dsimp only [A];linarith [Real.log_nonneg hH]
  have hD : 0≤D := by dsimp only [D];linarith [Real.log_nonneg hU]
  have hmz (p : ι) (hp : p∈F) (z : ℂ) (hz : z∈S p) : (u z).re∈Set.Icc (0:ℝ) 1 ∧ (u z).im=z.im := by
    obtain ⟨hl,hh⟩ := hre p hp z hz
    simp only [u,Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero,Set.mem_Icc,true_and,and_true]
    exact ⟨by linarith,by linarith [hσ.1]⟩
  have heq (p : ι) (z : ℂ) : (∑n∈Icc M (2*M),blockCoeff a X U j n*χ p n*(n:ℂ)^(-z)) =
      ∑n∈Icc M (2*M),b n*χ p n*(n:ℂ)^(-u z) := by
    apply sum_congr rfl;intro n hn
    have hn₀ : (n:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt (hM.trans (mem_Icc.mp hn).1)
    rw [show -z=(-(σ:ℂ))+(-u z) by dsimp [u];ring,Complex.cpow_add _ _ hn₀]
    dsimp only [b];ring
  change (∑p∈F,∑z∈S p,‖∑n∈Icc M (2*M),_‖^2) ≤ _
  simp_rw [heq]
  apply (hm S hK him hcount u hmz hM b).trans
  have hh : R*Real.sqrt H≤2*(M:ℝ) := hX.trans (by exact_mod_cast hx.le)
  have hc : K*(M:ℝ)+R*Real.sqrt H*(1+Real.log H)≤2*(M:ℝ)*A := by
    dsimp only [A]
    nlinarith only [mul_le_mul_of_nonneg_right hh (show 0≤1+Real.log H by linarith [Real.log_nonneg hH]),mul_nonneg hK hM₀.le]
  have henergy := shifted_block_square (X:=X) (U:=U) (j:=j) hσ.1 ha
  have hlog : 1+Real.log (2*(M:ℝ)) ≤ 2*D := by
    rw [Real.log_mul (by norm_num) hM₀.ne']
    dsimp only [D];linarith [Real.log_le_log hM₀ (by exact_mod_cast hmu : (M:ℝ)≤U),
      Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),Real.log_nonneg hU]
  have hlog₀ : 0≤1+Real.log (2*(M:ℝ)) := by
    have h₁ : (1:ℝ)≤M := by exact_mod_cast hM
    linarith [Real.log_nonneg (by linarith : 1≤2*(M:ℝ))]
  have hb : (∑n∈Icc M (2*M),‖b n‖^2) ≤ (2*(M:ℝ))*(2*D)^3*(M:ℝ)^(-2*σ) := henergy.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog₀ hlog 3) (by positivity)) (Real.rpow_nonneg hM₀.le _))
  have hpow : (M:ℝ)^2*(M:ℝ)^(-2*σ)≤(U:ℝ)^(2*(1-σ)) := by
    rw [←Real.rpow_two,←Real.rpow_add hM₀,show 2+ -2*σ=2*(1-σ) by ring]
    exact Real.rpow_le_rpow hM₀.le (by exact_mod_cast hmu) (by linarith [hσ.2])
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hc hC.le) hb (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)).trans
  change _ ≤ 32*C*A*D^3*(U:ℝ)^(2*(1-σ))
  linarith only [mul_le_mul_of_nonneg_left hpow (show 0≤32*C*A*D^3 by positivity)]

/-- Montgomery's sparse type-I bound. All detected values have modulus at
least V, while the product of the sample count and the square root of the
correlation parameter is at most the lower cutoff X. -/
theorem sparse_montgomery_typeI_count {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ}
    {L X U : ℕ} {H C K σ V : ℝ} (hC : 0<C) (hm : SparseCharacterBound F χ L H C)
    (hH : 1≤H) (hU : 1≤U) (hK : 0≤K) (hV : 0≤V) (hσ : σ∈Set.Icc (0:ℝ) 1)
    (S : ι→Finset ℂ) (hre : ∀p∈F,∀z∈S p,z.re∈Set.Icc σ 1)
    (him : ∀p∈F,∀z∈S p,0≤z.im ∧ z.im<L)
    (hcount : ∀p∈F,∀j<L,(((S p).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K)
    (hX : (∑p∈F,((S p).card:ℝ))*Real.sqrt H≤X)
    {a : ℕ→ℂ} (ha : ∀n,‖a n‖≤(n.divisors.card:ℝ))
    (hdet : ∀p∈F,∀z∈S p,V≤‖∑n∈Ioc X U,a n*χ p n*(n:ℂ)^(-z)‖) :
    (∑p∈F,((S p).card:ℝ))*V^2≤128*C*(K+1+Real.log H)*(1+Real.log U)^5*(U:ℝ)^(2*(1-σ)) := by
  let D := 1+Real.log U
  let A := K+1+Real.log H
  let W := (U:ℝ)^(2*(1-σ))
  have hD : 0≤D := by dsimp [D];linarith [Real.log_nonneg (by exact_mod_cast hU : (1:ℝ)≤U)]
  have hA : 0≤A := by dsimp [A];linarith [Real.log_nonneg hH]
  have hW : 0≤W := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := sum_le_sum fun p hp => sum_le_sum (fun z hz => pow_le_pow_left₀ hV (hdet p hp z hz) 2)
  simp only [sum_const,nsmul_eq_mul,←sum_mul] at hs
  have hblock := sparse_block_reassembly F χ S a X U id (fun j hj =>
    sparse_montgomery_typeI_block hC hm hH hK hσ S hre him hcount hX ha hj)
  apply hs.trans hblock |>.trans
  have hc := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (blocks X U).card) (block_count (X:=X) hU) 2
  change _≤128*C*A*D^5*W
  have hb := mul_le_mul_of_nonneg_right hc (show 0≤32*C*A*D^3*W by positivity)
  exact hb.trans_eq (by dsimp only [D,A,W];ring)

end AnalyticNumberTheory.PrimeDistribution
