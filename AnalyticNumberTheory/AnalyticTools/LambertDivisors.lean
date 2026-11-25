import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Tactic

/-!
# Lambert series of bounded coefficients

Summing the same absolutely convergent series along rows and along
hyperbolas identifies its geometric kernel with a divisor convolution.
-/

open Finset Nat
namespace AnalyticNumberTheory.AnalyticTools

private theorem lambert_row {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (d : ℕ+) :
    ∑' m : ℕ+, r ^ (d*m:ℕ) = r^(d:ℕ) / (1-r^(d:ℕ)) := by
  have h : ‖r^(d:ℕ)‖ < 1 := by
    rw [Real.norm_of_nonneg (pow_nonneg hr _)]; exact pow_lt_one₀ hr hr' d.2.ne'
  calc
    _ = ∑' m : ℕ+, (r^(d:ℕ))^(m:ℕ) := tsum_congr fun m => pow_mul r _ _
    _ = ∑' m : ℕ, (r^(d:ℕ))^(m+1) := tsum_pnat_eq_tsum_succ
    _ = (∑' m : ℕ, (r^(d:ℕ))^m) * r^(d:ℕ) := by simp only [pow_succ, tsum_mul_right]
    _ = _ := by rw [tsum_geometric_of_norm_lt_one h, div_eq_mul_inv, mul_comm]

/-- The Lambert series of a bounded sequence has its divisor sums as coefficients. -/
theorem lambert_divisor_sum {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) :
    ∑' d : ℕ+, f d * (r^(d:ℕ) / (1-r^(d:ℕ))) =
      ∑' n : ℕ+, (∑ d ∈ (n:ℕ).divisors, f d) * r^(n:ℕ) := by
  let F (p : ℕ+ × ℕ+) := f p.1 * r^(p.1*p.2:ℕ)
  have hs : Summable F := by
    have H := summable_prod_mul_pow 0 (by rwa [Real.norm_of_nonneg hr] : ‖r‖<1)
    apply Summable.of_norm_bounded (g := fun p : ℕ+ × ℕ+ => r^(p.1*p.2:ℕ)) (by simpa using H)
    intro p
    simp only [F, norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr _)]
    exact mul_le_of_le_one_left (pow_nonneg hr _) (hf _)
  have hσ := sigmaAntidiagonalEquivProd.summable_iff.mpr hs
  calc
    _ = ∑' d : ℕ+, ∑' m : ℕ+, F (d,m) := by
      apply tsum_congr; intro d
      rw [← lambert_row hr hr', ← tsum_mul_left]
    _ = ∑' p, F p := hs.tsum_prod.symm
    _ = ∑' u, F (sigmaAntidiagonalEquivProd u) := (sigmaAntidiagonalEquivProd.tsum_eq F).symm
    _ = _ := by
      change ∑' u, (F ∘ sigmaAntidiagonalEquivProd) u = _
      rw [Summable.tsum_sigma hσ]
      apply tsum_congr; intro n
      rw [tsum_fintype, univ_eq_attach, sum_mul]
      change ∑ p ∈ (n:ℕ).divisorsAntidiagonal.attach, f p.1.1 * r^(p.1.1*p.1.2) = _
      rw [Finset.sum_attach _ (fun p : ℕ × ℕ => f p.1 * r^(p.1*p.2)), Nat.sum_divisorsAntidiagonal (fun x y => f x * r^(x*y))]
      exact sum_congr rfl fun d hd => by rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

end AnalyticNumberTheory.AnalyticTools
