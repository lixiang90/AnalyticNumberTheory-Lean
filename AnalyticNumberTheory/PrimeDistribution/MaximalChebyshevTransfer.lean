import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovPrimeCounting

/-! # Preservation of explicit logarithmic levels in maximal mean estimates -/
noncomputable section
open Finset
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- A pointwise comparison with the maximal Chebyshev discrepancy and a
square-root error preserves both the saving k and the explicit cutoff
exponent b whenever k ≤ b. -/
theorem maximal_mean_transfer_at_level {k b : ℕ} (hkb : k≤b) {F : ℝ→ℕ→ℝ}
    {D : ℝ} (hD : 0<D) (hcomp : ∀{x : ℝ},2≤x → ∀ {q : ℕ},1≤q →
      F x q≤D*(maximalPsiAPError x q+Real.sqrt x))
    (H : ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},4≤x → 1≤Q → Q≤Real.sqrt x/(Real.log x)^b →
       (∑q∈Icc 1 ⌊Q⌋₊,maximalPsiAPError x q)≤C*x/(Real.log x)^k) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},4≤x → 1≤Q → Q≤Real.sqrt x/(Real.log x)^b →
      (∑q∈Icc 1 ⌊Q⌋₊,F x q)≤C*x/(Real.log x)^k := by
  obtain ⟨C,hC,HM⟩ := H
  refine ⟨D*(C+1),by positivity,?_⟩
  intro x Q hx hQ hcut
  let L := Real.log x
  have hL : 1≤L := (Real.le_log_iff_exp_le (by linarith : 0<x)).mpr (by linarith [Real.exp_one_lt_three])
  have hL₀ : 0<L := by linarith
  have hx₀ : 0≤x := by linarith
  have hN : (⌊Q⌋₊:ℝ)≤Q := Nat.floor_le (by linarith)
  have hcard : ((Icc 1 ⌊Q⌋₊).card:ℝ)=(⌊Q⌋₊:ℝ) := by simp [Nat.card_Icc]
  have hlevel := pow_le_pow_right₀ hL hkb
  have htr : (⌊Q⌋₊:ℝ)*Real.sqrt x≤x/L^k := by
    apply (mul_le_mul_of_nonneg_right (hN.trans (hcut.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (pow_pos hL₀ _) hlevel))) (Real.sqrt_nonneg _)).trans_eq
    rw [div_mul_eq_mul_div,Real.mul_self_sqrt hx₀]
  have hh := sum_le_sum (s:=Icc 1 ⌊Q⌋₊) (fun q hq=>hcomp (by linarith : 2≤x) (mem_Icc.mp hq).1)
  rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,hcard] at hh
  apply hh.trans ((mul_le_mul_of_nonneg_left (add_le_add (HM hx hQ hcut) htr) hD.le).trans_eq ?_)
  change D*(C*x/L^k+x/L^k)=D*(C+1)*x/L^k
  ring

end AnalyticNumberTheory.PrimeDistribution
