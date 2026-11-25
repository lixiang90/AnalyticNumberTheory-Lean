import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Ordered factorizations and powers of the divisor count

The coefficient of the r-fold Dirichlet convolution of the constant-one
function counts ordered factorizations into r positive integers.
Its order doubles when two such coefficient sequences are convolved.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace AnalyticNumberTheory.DivisorProblems

/-- The number of ordered factorizations into `r` positive factors.
Order zero is the Dirichlet convolution unit, supported at one. -/
def orderedDivisorCount (r : ℕ) : ArithmeticFunction ℕ := ζ ^ r

theorem orderedDivisorCount_succ (r n : ℕ) :
    orderedDivisorCount (r+1) n = ∑ d ∈ n.divisors, orderedDivisorCount r d := by
  rw [orderedDivisorCount, pow_succ, mul_zeta_apply]
  rfl

/-- Each divisor of a product can be written as a product of divisors. -/
theorem card_divisors_mul_le (a b : ℕ) :
    (a*b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [← card_product]
  apply card_le_card_of_surjOn (fun p : ℕ × ℕ => p.1*p.2)
  intro d hd
  have hd' := Nat.mem_divisors.mp hd
  obtain ⟨u, v, hu, hv, huv⟩ := exists_dvd_and_dvd_of_dvd_mul hd'.1
  exact ⟨(u,v), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hu, left_ne_zero_of_mul hd'.2⟩,
    Nat.mem_divisors.mpr ⟨hv, right_ne_zero_of_mul hd'.2⟩⟩, huv.symm⟩

/-- The k-th power of the ordinary divisor count is bounded pointwise by
the number of ordered factorizations into `2^k` factors, at every positive n. -/
theorem card_divisors_pow_le_ordered (k : ℕ) {n : ℕ} (hn : 0 < n) :
    n.divisors.card ^ k ≤ orderedDivisorCount (2^k) n := by
  induction k generalizing n with
  | zero => simp [orderedDivisorCount, zeta_apply_ne hn.ne']
  | succ k ih =>
    let F := orderedDivisorCount (2^k)
    have conv : orderedDivisorCount (2^(k+1)) n = ∑ p ∈ n.divisorsAntidiagonal, F p.1 * F p.2 := by
      simp only [orderedDivisorCount, pow_succ 2 k, Nat.mul_two, pow_add, ArithmeticFunction.mul_apply, F]
    rw [conv]
    calc
      _ = ∑ _p ∈ n.divisorsAntidiagonal, n.divisors.card ^ k := by
        rw [sum_const, nsmul_eq_mul, ← Nat.map_div_right_divisors, card_map, pow_succ, mul_comm]
        simp
      _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hpos : 0 < p.1*p.2 := he.symm ▸ hn
        have hτ : n.divisors.card ≤ p.1.divisors.card * p.2.divisors.card := he ▸ card_divisors_mul_le _ _
        calc
          _ ≤ (p.1.divisors.card * p.2.divisors.card)^k := Nat.pow_le_pow_left hτ k
          _ = p.1.divisors.card^k * p.2.divisors.card^k := mul_pow ..
          _ ≤ _ := Nat.mul_le_mul (ih (Nat.pos_of_ne_zero (left_ne_zero_of_mul hpos.ne')))
            (ih (Nat.pos_of_ne_zero (right_ne_zero_of_mul hpos.ne')))

end AnalyticNumberTheory.DivisorProblems
