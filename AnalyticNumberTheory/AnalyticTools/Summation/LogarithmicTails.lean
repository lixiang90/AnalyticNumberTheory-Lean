import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Power-weighted tails of logarithmic summatory functions

A summatory bound X(1+log X)^d gives a uniform tail of order
N^(1-k)(1+log N)^d for every integral weight exponent k≥2.
-/
noncomputable section
open Real Finset
namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- Uniform finite tail, suitable both for partial Dirichlet polynomials and
for passage to the limit. -/
theorem logarithmic_power_tail (d k : ℕ) (hk : 2≤k) {f : ℕ→ℝ} (hf : ∀n,0≤f n)
    {B : ℝ} (hB : 0<B) (hF : ∀ {X : ℕ},1≤X →
      ∑n∈Finset.Icc 1 X,f n≤B*(X:ℝ)*(1+Real.log X)^d) :
    ∃ C : ℝ,0<C ∧ ∀ {N : ℕ},1≤N → ∀ M : ℕ,
      ∑n∈Finset.Ioc N M,f n/(n:ℝ)^k ≤ C*((N:ℝ)/(N:ℝ)^k)*(1+Real.log N)^d := by
  let w := fun j : ℕ => ((j:ℝ)+2)^d*(1/2:ℝ)^j
  have hw (j : ℕ) : 0≤w j := by dsimp [w];positivity
  have hs : Summable w := by
    have h := (summable_nat_add_iff 2).mpr (summable_pow_mul_geometric_of_norm_lt_one d (r:=(1/2:ℝ)) (by norm_num))
    convert h.mul_left 4 using 1
    ext j;dsimp [w];push_cast;rw [pow_add];ring
  have hts : 0≤∑'j,w j := tsum_nonneg hw
  refine ⟨2*B*(1+∑'j,w j),by positivity,?_⟩
  intro N hN M
  let X := fun j : ℕ => 2^j*N
  let S := (N:ℝ)/(N:ℝ)^k*(1+Real.log N)^d
  have hNp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hL := Real.log_nonneg (show 1≤(N:ℝ) by exact_mod_cast hN)
  have hS : 0≤S := by dsimp [S];positivity
  have hx (j : ℕ) : 1≤X j := Nat.mul_pos (Nat.pow_pos (by decide : 0<2)) hN
  have hstep (j : ℕ) : X (j+1)=2*X j := by dsimp [X];rw [pow_succ];ring
  have hmono (j : ℕ) : X j≤X (j+1) := by rw [hstep];omega
  have hlow (j : ℕ) : N≤X j := by dsimp [X];exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0<2))
  have hblock (j : ℕ) : (∑n∈Finset.Ioc (X j) (X (j+1)),f n/(n:ℝ)^k)≤(2*B*S)*w j := by
    have hp : 0<(X j:ℝ) := Nat.cast_pos.mpr (hx _)
    have h₁ : ∑n∈Finset.Ioc (X j) (X (j+1)),f n/(n:ℝ)^k≤
        (∑n∈Finset.Icc 1 (X (j+1)),f n)/(X j:ℝ)^k := by
      rw [sum_div]
      apply le_trans (sum_le_sum (g:=fun n=>f n/(X j:ℝ)^k) _)
      · exact sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hn).1;omega,(Finset.mem_Ioc.mp hn).2⟩)
          (fun n _ _=>div_nonneg (hf n) (by positivity))
      · intro n hn;apply div_le_div_of_nonneg_left (hf n) (by positivity)
        exact pow_le_pow_left₀ hp.le (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le) k
    have hl : 1+Real.log (X (j+1))≤((j:ℝ)+2)*(1+Real.log N) := by
      dsimp [X];push_cast;rw [Real.log_mul (by positivity) hNp.ne',Real.log_pow]
      push_cast
      have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      nlinarith only [htwo,mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α:=ℝ) j),hL,mul_nonneg (Nat.cast_nonneg (α:=ℝ) j) hL]
    have hpow := pow_le_pow_left₀ (by have hh := Real.log_nonneg (show (1:ℝ)≤X (j+1) by exact_mod_cast hx (j+1));linarith : 0≤1+Real.log (X (j+1))) hl d
    have hratio : (X (j+1):ℝ)/(X j:ℝ)^k ≤2*((N:ℝ)/(N:ℝ)^k)*(1/2:ℝ)^j := by
      have hking : ((2:ℝ)^j)^2≤((2:ℝ)^j)^k := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hk
      rw [hstep];dsimp [X];push_cast
      rw [mul_pow,one_div,inv_pow]
      field_simp
      exact hking
    apply (h₁.trans (div_le_div_of_nonneg_right (hF (hx _)) (by positivity))).trans
    calc B*(X (j+1):ℝ)*(1+Real.log (X (j+1)))^d/(X j:ℝ)^k=
          B*((X (j+1):ℝ)/(X j:ℝ)^k)*(1+Real.log (X (j+1)))^d := by ring
         _ ≤ (B*(2*((N:ℝ)/(N:ℝ)^k)*(1/2:ℝ)^j))*(((j:ℝ)+2)*(1+Real.log N))^d :=
          mul_le_mul (mul_le_mul_of_nonneg_left hratio hB.le) hpow
            (pow_nonneg (by have hh := Real.log_nonneg (show (1:ℝ)≤X (j+1) by exact_mod_cast hx (j+1));linarith) _)
            (by positivity)
         _ = _ := by dsimp [S,w];rw [mul_pow];ring
  have hdy (J : ℕ) : (∑n∈Finset.Ioc N (X J),f n/(n:ℝ)^k)≤(2*B*S)*∑j∈range J,w j := by
    induction J with
    | zero => simp [X]
    | succ J ih =>
      rw [←sum_Ioc_consecutive (fun n : ℕ=>f n/(n:ℝ)^k) (hlow J) (hmono J),sum_range_succ,mul_add]
      exact add_le_add ih (hblock J)
  have hM : M≤X M := (Nat.lt_two_pow_self.le).trans (Nat.le_mul_of_pos_right _ hN)
  apply (sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hM) (fun n _ _=>div_nonneg (hf n) (by positivity))).trans
  apply (hdy M).trans
  have hh := hs.sum_le_tsum (range M) (fun j _=>hw j)
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*B*S)).trans
  dsimp [S] at *
  nlinarith only [mul_nonneg (show 0≤2*B by positivity) hS]

end AnalyticNumberTheory.AnalyticTools.Summation
