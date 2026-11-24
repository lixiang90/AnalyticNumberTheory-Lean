import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl

/-!
# Mean bounds for the binary Goldbach singular series

Averaging the Ramanujan sums over the target integer permits a positive
power weight on the denominator. This controls both truncating the singular
series and varying the radii of the major arcs.
-/

noncomputable section
open Finset
open scoped Classical ArithmeticFunction.Moebius
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Summing the gcd over the positive initial interval costs at most a
divisor-count factor. For each divisor, its size cancels its frequency. -/
theorem sum_gcd_Ioc_le_divisors (N : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    ∑ n ∈ Ioc 0 N, n.gcd q ≤ N * q.divisors.card := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ∑ d ∈ q.divisors, if d ∣ n then d else 0 := by
      apply sum_le_sum
      intro n _
      have hmem : n.gcd q ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,by omega⟩
      simpa [Nat.gcd_dvd_left] using
        (single_le_sum (f := fun d => if d ∣ n then d else 0) (fun d _ => Nat.zero_le _) hmem)
    _ = ∑ d ∈ q.divisors, (N / d) * d := by
      rw [sum_comm]
      refine sum_congr rfl fun d _ => ?_
      rw [← sum_filter]
      simp [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ _ := by simpa [Nat.mul_comm] using
      (sum_le_sum (s := q.divisors) (fun d _ => Nat.div_mul_le_self N d))

/-- Mean of an individual binary singular-series term across target integers. -/
theorem sum_abs_singularTermBinary_le (N : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    ∑ n ∈ Ioc 0 N, |singularTermBinary q n| ≤ N * (q.divisors.card:ℝ) / q.totient ^ 2 := by
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hg := sum_gcd_Ioc_le_divisors N hq
  have hg' : ∑ n ∈ Ioc 0 N, (n.gcd q : ℝ) ≤ N * (q.divisors.card:ℝ) := by exact_mod_cast hg
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (n.gcd q:ℝ) / q.totient ^ 2 := by
      refine sum_le_sum fun n _ => ?_
      have hram := (Complex.abs_re_le_norm _).trans (norm_ramanujanSum_le_gcd hq (-(n:ℤ)))
      simp only [Int.natAbs_neg, Int.natAbs_natCast] at hram
      rw [singularTermBinary, if_neg (show q ≠ 0 by omega), abs_mul, abs_div, abs_of_pos (sq_pos_of_pos hφ)]
      have hmu : |(μ q : ℝ) ^ 2| ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or q with h|h|h <;> rw [h] <;> norm_num
      calc
        _ ≤ (1 / (q.totient:ℝ)^2) * (n.gcd q : ℝ) :=
          mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hram (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (∑ n ∈ Ioc 0 N, (n.gcd q:ℝ)) / q.totient ^ 2 := by rw [sum_div]
    _ ≤ _ := by gcongr

/-- Absolute first moment with the extra denominator weight, for a fixed
target. Its average over targets is bounded by an absolute constant. -/
def binarySeriesMoment (n : ℕ) : ℝ := ∑' q : ℕ, (q:ℝ)^(1/8:ℝ) * |singularTermBinary q n|

theorem summable_binarySeriesMoment {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun q : ℕ => (q:ℝ)^(1/8:ℝ) * |singularTermBinary q n|) := by
  have hp : Summable (fun q : ℕ => (q:ℝ)^(-(11/8):ℝ)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<11/8))
  apply (hp.mul_left (16*n:ℝ)).of_nonneg_of_le (fun _ => by positivity)
  intro q
  by_cases hq : q = 0
  · simp [hq]
  calc
    _ ≤ (q:ℝ)^(1/8:ℝ) * (16 * n * (q:ℝ)^(-3/2:ℝ)) :=
      mul_le_mul_of_nonneg_left (abs_singularTermBinary_le (by omega) hn) (by positivity)
    _ = 16*n*(q:ℝ)^(-(11/8):ℝ) := by
      rw [mul_left_comm, ← Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero hq)]
      norm_num

/-- For every initial interval, the sum of the weighted absolute moments is
bounded by a universal constant times the length of the interval. -/
theorem sum_binarySeriesMoment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∑ n ∈ Ioc 0 N, binarySeriesMoment n ≤ C * N := by
  obtain ⟨D,hD,hdiv⟩ := AnalyticNumberTheory.ExponentialSums.card_divisors_le_rpow (by norm_num : (0:ℝ)<1/4)
  let f := fun q : ℕ => (q:ℝ)^(-(9/8):ℝ)
  have hf : Summable f := by
    simpa [f,Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<9/8))
  refine ⟨16*D*(∑' q, f q),by dsimp [f]; positivity,fun N => ?_⟩
  have hn (n : ℕ) (hn : n ∈ Ioc 0 N) := summable_binarySeriesMoment (mem_Ioc.mp hn).1
  simp only [binarySeriesMoment]
  rw [← Summable.tsum_finsetSum hn]
  have hmajor (q : ℕ) : (∑ n ∈ Ioc 0 N, (q:ℝ)^(1/8:ℝ) * |singularTermBinary q n|) ≤
      (16*D*N) * f q := by
    by_cases hq : q = 0
    · simp [hq,f]
    have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
    have hφ' := pow_le_pow_left₀ (by positivity) (rpow_three_quarters_le_four_mul_totient (by omega : 1 ≤ q)) 2
    rw [← Real.rpow_natCast ((q:ℝ)^(3/4:ℝ)) 2, ← Real.rpow_mul hq0.le] at hφ'
    norm_num at hφ'
    have htin : (1:ℝ) / q.totient^2 ≤ 16 / (q:ℝ)^(3/2:ℝ) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    rw [← mul_sum]
    calc
      _ ≤ (q:ℝ)^(1/8:ℝ) * (N * (q.divisors.card:ℝ) / q.totient ^ 2) := by
        gcongr; exact sum_abs_singularTermBinary_le N (by omega)
      _ = (q:ℝ)^(1/8:ℝ) * N * q.divisors.card * (1 / (q.totient:ℝ)^2) := by ring
      _ ≤ (q:ℝ)^(1/8:ℝ) * N * (D*(q:ℝ)^(1/4:ℝ)) * (16 / (q:ℝ)^(3/2:ℝ)) := by gcongr; exact hdiv q (by omega)
      _ = _ := by
        dsimp [f]
        rw [div_eq_mul_inv (16:ℝ) _, ← Real.rpow_neg hq0.le]
        calc
          _ = (16*D*N) * ((q:ℝ)^(1/8:ℝ)*(q:ℝ)^(1/4:ℝ)*(q:ℝ)^(-(3/2):ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; norm_num
  calc
    _ ≤ ∑' q, (16*D*N) * f q := (summable_sum hn).tsum_le_tsum hmajor (hf.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

end AnalyticNumberTheory.AdditiveNumberTheory
