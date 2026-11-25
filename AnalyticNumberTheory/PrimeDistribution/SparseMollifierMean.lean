import AnalyticNumberTheory.PrimeDistribution.SparseDyadicPolynomials
import AnalyticNumberTheory.PrimeDistribution.CharacterMollifierMean

/-! # Sparse second moments for translated Möbius polynomials -/
noncomputable section
open Real Complex Finset
open scoped ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution
open Ingham

private theorem mollifier_block_energy (X j : ℕ) (v : ℝ) :
    (∑ n∈Icc (2^j) (2*2^j),‖blockCoeff (shiftedMobiusCoeff v) 0 X j n‖^2)≤2 := by
  let M := 2^j
  have hM : 1≤M := Nat.one_le_pow _ _ (by decide)
  have hr : (1:ℝ)≤M := by exact_mod_cast hM
  have ht (n : ℕ) (hn : n∈Icc M (2*M)) :
      ‖blockCoeff (shiftedMobiusCoeff v) 0 X j n‖^2 ≤ (M:ℝ)⁻¹ := by
    have hmn := (mem_Icc.mp hn).1
    have h := (shiftedMobiusCoeff_norm_sq (hM.trans hmn) v).trans
      (inv_anti₀ (zero_lt_one.trans_le hr) (by exact_mod_cast hmn))
    unfold blockCoeff;split_ifs
    · exact h
    · simp
  have hc : (Icc M (2*M)).card≤2*M := by rw [Nat.card_Icc];omega
  apply (sum_le_sum ht).trans
  rw [sum_const,nsmul_eq_mul]
  calc _ ≤ ((2*M:ℕ):ℝ)*(M:ℝ)⁻¹ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
       _ = 2 := by push_cast;field_simp [show (M:ℝ)≠0 by linarith]

set_option maxHeartbeats 800000 in
/-- For every vertical translation, the sparse second moment is controlled
by the length and the number of samples. The logarithms in X come only from
reassembling the dyadic pieces. -/
theorem sparse_mollifier_second_mean {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ}
    {L X : ℕ} {H C K : ℝ} (hs : SparseCharacterBound F χ L H C) (hH : 1≤H)
    (hC : 0≤C) (hX : 1≤X) (hK : 0≤K) (S : ι→Finset ℂ)
    (him : ∀ i∈F,∀ z∈S i,0≤z.im ∧ z.im<L)
    (hc : ∀ i∈F,∀ j<L,(((S i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K) (v : ℝ) :
    (∑ i∈F,∑ z∈S i,‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+((v+z.im:ℝ):ℂ)*I)‖^2) ≤
      8*C*(K*X+(∑ i∈F,((S i).card:ℝ))*Real.sqrt H*(1+Real.log H))*(1+Real.log X)^2 := by
  let R := ∑ i∈F,((S i).card:ℝ)
  let E := K*X+R*Real.sqrt H*(1+Real.log H)
  let u (z : ℂ) := I*(z.im:ℂ)
  have hR : 0≤R := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hlog : 0≤1+Real.log H := by linarith [Real.log_nonneg hH]
  have hE : 0≤E := by dsimp [E];positivity
  have hb (j : ℕ) (hj : j∈blocks 0 X) :
      (∑ i∈F,∑ z∈S i,‖∑ n∈Icc (2^j) (2*2^j),
        blockCoeff (shiftedMobiusCoeff v) 0 X j n*χ i n*(n:ℂ)^(-u z)‖^2) ≤ C*E*2 := by
    have hm : (2^j:ℕ)≤X := (mem_filter.mp hj).2.2
    have h := hs S hK him hc u (fun i _ z _ => by simp [u])
      (M:=2^j) (Nat.one_le_pow _ _ (by decide)) (blockCoeff (shiftedMobiusCoeff v) 0 X j)
    apply h.trans
    apply mul_le_mul _ (mollifier_block_energy X j v)
      (sum_nonneg fun _ _ => sq_nonneg _) (mul_nonneg hC hE)
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add _ le_rfl
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm) hK
  have h := sparse_block_reassembly F χ S (shiftedMobiusCoeff v) 0 X u hb
  have hI : Ioc 0 X=Icc 1 X := by ext n;simp;omega
  simp only [hI,u,shiftedMobiusCoeff_sum] at h
  apply h.trans
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (blocks 0 X).card) (block_count hX) 2
  exact (mul_le_mul_of_nonneg_right hh (mul_nonneg (mul_nonneg hC hE) (by norm_num) : 0≤C*E*2)).trans_eq (by dsimp only [E,R];ring)

end AnalyticNumberTheory.PrimeDistribution
