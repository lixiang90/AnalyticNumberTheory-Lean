import AnalyticNumberTheory.PrimeDistribution.InghamTypeI
import AnalyticNumberTheory.SieveMethods.SparseCharacterBound

/-! # Reassembling sparse mean values of dyadic character polynomials -/
noncomputable section
open Finset Complex Real
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution
open Ingham

private theorem block_sum {ι : Type*} (χ : ι→ℕ→ℂ) (a : ℕ→ℂ) (p : ι) (X U i : ℕ) (s : ℂ) :
    dirichletPoly (blockCoeff (fun n => a n*χ p n) X U i) (2*2^i) s =
      ∑ n∈Icc (2^i) (2*2^i),blockCoeff a X U i n*χ p n*(n:ℂ)^(-s) := by
  let M := 2^i
  have hM : 1≤M := Nat.one_le_pow _ _ (by decide)
  unfold dirichletPoly
  have ht (n : ℕ) : blockCoeff (fun n => a n*χ p n) X U i n=blockCoeff a X U i n*χ p n := by
    unfold blockCoeff;split_ifs <;> simp
  simp_rw [ht]
  symm
  apply sum_subset (Icc_subset_Icc_left hM)
  intro n hn hn'
  have hb : ¬(X<n ∧ n≤U ∧ Nat.log 2 n=i) := by
    rintro ⟨hx,_,hi⟩
    apply hn'
    exact mem_Icc.mpr ⟨by dsimp only [M];rw [←hi];exact Nat.pow_log_le_self 2 (by omega : n≠0),(mem_Icc.mp hn).2⟩
  simp [blockCoeff,hb]

/-- Reassembling a polynomial supported on (X,U] costs at most the square of
the number of dyadic blocks. Both the coefficient mask and the exponent are
shared across a finite family of characters. -/
theorem sparse_block_reassembly {ι : Type*} (F : Finset ι) (χ : ι→ℕ→ℂ) (S : ι→Finset ℂ)
    (a : ℕ→ℂ) (X U : ℕ) (u : ℂ→ℂ) {B : ℝ} (hB : ∀ j∈blocks X U,
      (∑ p∈F,∑ z∈S p,‖∑ n∈Icc (2^j) (2*2^j),blockCoeff a X U j n*χ p n*(n:ℂ)^(-u z)‖^2) ≤ B) :
    (∑ p∈F,∑ z∈S p,‖∑ n∈Ioc X U,a n*χ p n*(n:ℂ)^(-u z)‖^2) ≤
      ((blocks X U).card:ℝ)^2*B := by
  let J := blocks X U
  let E (j : ℕ) (p : ι) (z : ℂ) := ‖∑ n∈Icc (2^j) (2*2^j),blockCoeff a X U j n*χ p n*(n:ℂ)^(-u z)‖
  have each (p : ι) (z : ℂ) : ‖∑ n∈Ioc X U,a n*χ p n*(n:ℂ)^(-u z)‖^2 ≤
      (J.card:ℝ)*∑ j∈J,(E j p z)^2 := by
    rw [tail_by_blocks]
    simp_rw [block_sum χ a p]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2).trans
    have h := sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun j => E j p z)
    simpa only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] using h
  apply (sum_le_sum fun p _ => sum_le_sum (fun z _ => each p z)).trans
  simp only [←mul_sum]
  have hswap : (∑ p∈F,∑ z∈S p,∑ j∈J,(E j p z)^2)=∑ j∈J,∑ p∈F,∑ z∈S p,(E j p z)^2 := by
    rw [sum_comm (s:=J) (t:=F)];exact sum_congr rfl (fun _ _ => sum_comm)
  rw [hswap]
  have h := mul_le_mul_of_nonneg_left (sum_le_sum hB) (Nat.cast_nonneg (α:=ℝ) J.card)
  simp only [sum_const,nsmul_eq_mul] at h
  exact h.trans_eq (by dsimp only [J];ring)

end AnalyticNumberTheory.PrimeDistribution
