import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Coefficient energy to the right of a vertical line

Cauchy–Schwarz and the convergent series at exponent two bound a Dirichlet
polynomial throughout the half-plane one unit to the right of its energy line.
-/
open Real Complex Finset
namespace AnalyticNumberTheory.SieveMethods

/-- Pointwise square bound for arbitrary coefficients and a multiplier
bounded by one, at real part at least one. -/
theorem dirichlet_polynomial_right_energy (N : ℕ) (b g : ℕ→ℂ) (hg : ∀n,‖g n‖≤1)
    {w : ℂ} (hw : 1≤w.re) :
    ‖∑n∈Icc 1 N,b n*g n*(n:ℂ)^(-w)‖^2 ≤ 3*(∑n∈Icc 1 N,‖b n‖^2) := by
  let J := Icc 1 N
  have hb : ‖∑n∈J,b n*g n*(n:ℂ)^(-w)‖ ≤ ∑n∈J,‖b n‖*(n:ℝ)⁻¹ := by
    apply (norm_sum_le ..).trans
    apply sum_le_sum;intro n hn
    have hn' : 1≤n := (mem_Icc.mp hn).1
    have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn' : 1≤(n:ℝ)) (neg_le_neg hw)
    rw [Real.rpow_neg_one] at hpow
    rw [norm_mul,norm_mul,Complex.norm_natCast_cpow_of_pos (by omega : 0<n),Complex.neg_re]
    exact mul_le_mul (mul_le_of_le_one_right (norm_nonneg _) (hg n)) hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_nonneg _)
  have hs : (∑n∈J,((n:ℝ)⁻¹)^2)≤3 := by
    have hh := hasSum_zeta_two.summable.sum_le_tsum J (fun n _ => by positivity)
    rw [hasSum_zeta_two.tsum_eq] at hh
    simp only [one_div,inv_pow] at *
    apply hh.trans
    nlinarith only [Real.pi_lt_four,Real.pi_pos,sq_nonneg (4-Real.pi),mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_four]
  have hc := sum_mul_sq_le_sq_mul_sq J (fun n:ℕ => ‖b n‖) (fun n:ℕ => (n:ℝ)⁻¹)
  exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans (hc.trans
    ((mul_le_mul_of_nonneg_left hs (sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (mul_comm ..)))

end AnalyticNumberTheory.SieveMethods
