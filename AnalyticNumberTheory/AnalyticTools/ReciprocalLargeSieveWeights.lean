import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Reciprocal weights in a quadratic large-sieve bound -/
noncomputable section
open Finset
namespace AnalyticNumberTheory.AnalyticTools

/-- Partial summation of a quadratic cumulative bound. The loss in the
length N depends on the lower cutoff, whereas the loss in U is linear. -/
theorem reciprocal_sum_of_quadratic_cumulative (a : ℕ→ℝ) {N E : ℝ} {R U : ℕ}
    (ha : ∀ n,0≤a n) (hE : 0≤E) (hN : 0≤N) (hR : 1≤R)
    (hc : ∀ u : ℕ,(∑ n∈Icc 1 u,a n)≤(N+(u:ℝ)^2)*E) :
    (∑ n∈Ioc R U,a n/(n:ℝ))≤(2*(U:ℝ)+N/R)*E := by
  let A (u : ℕ) := ∑ n∈Icc 1 u,a n
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  by_cases hu : R≤U
  · have hstep (u : ℕ) (h : R≤u) :
        (∑ n∈Ioc R u,a n/(n:ℝ)) ≤ A u/(u:ℝ)+E*((u:ℝ)-R+N*((R:ℝ)⁻¹-(u:ℝ)⁻¹)) := by
      induction u,h using Nat.le_induction with
      | base =>
        simp only [Ioc_self,sum_empty,sub_self,mul_zero,add_zero]
        exact div_nonneg (sum_nonneg (fun n _ => ha n)) hr.le
      | succ u hu ih =>
        have hu₀ : (0:ℝ)<u := hr.trans_le (by exact_mod_cast hu)
        have hu₁ : 0<(u:ℝ)+1 := by linarith
        let d := (u:ℝ)⁻¹-((u:ℝ)+1)⁻¹
        have hd : 0≤d := sub_nonneg.mpr (inv_anti₀ hu₀ (by linarith))
        have hdu : (u:ℝ)^2*d≤1 := by
          dsimp only [d];field_simp <;> nlinarith
        have hA : A (u+1)=A u+a (u+1) := sum_Icc_succ_top (by omega : 1≤u+1) a
        rw [sum_Ioc_succ_top hu,hA,Nat.cast_succ]
        have hpow := (mul_le_mul_of_nonneg_right (hc u) hd).trans_eq
          (show (N+(u:ℝ)^2)*E*d=E*N*d+E*((u:ℝ)^2*d) by ring)
        change A u*d≤_ at hpow
        have hdelta : A u*d≤E*N*d+E := by linarith only [hpow,mul_le_mul_of_nonneg_left hdu hE]
        dsimp only [d] at hdelta
        simp only [div_eq_mul_inv] at ih ⊢
        linarith only [ih,hdelta]
    have hu₀ : (0:ℝ)<U := hr.trans_le (by exact_mod_cast hu)
    have hh := div_le_div_of_nonneg_right (hc U) hu₀.le
    have he : (N+(U:ℝ)^2)*E/(U:ℝ)+E*((U:ℝ)-R+N*((R:ℝ)⁻¹-(U:ℝ)⁻¹)) =
        (2*(U:ℝ)+N/R)*E-R*E := by field_simp;ring
    exact (hstep U hu).trans (((add_le_add_left hh _).trans_eq he).trans (sub_le_self _ (mul_nonneg hr.le hE)))
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hu),sum_empty];positivity

end AnalyticNumberTheory.AnalyticTools
