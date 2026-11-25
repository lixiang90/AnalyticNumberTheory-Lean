import AnalyticNumberTheory.SieveMethods.WeightedFareySieve
import AnalyticNumberTheory.SieveMethods.SelbergWeightedDenominator
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The weighted large sieve for rough integers

Choosing the local Farey weights gives a bound with numerator equal to
the length of the interval. The cutoff is real, so no rounding loss enters
the logarithmic main term.
-/

open Finset Real
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.SieveMethods

private theorem singleton_sieveWeight {q : ℕ} (hq : 0<q) (hs : Squarefree q) :
    sieveWeight (fun _ => {0}) q = (q.totient:ℝ)⁻¹ := by
  rw [sieveWeight,totient_squarefree_eq_prod hq hs,Nat.cast_prod,←prod_inv_distrib]
  refine prod_congr rfl fun p hp => ?_
  simp [Nat.cast_sub (Nat.mem_primeFactors.mp hp).1.one_lt.le,one_div]

/-- Counting form of the individually weighted arithmetic large sieve. -/
theorem weighted_arithmetic_large_sieve_card
    (Ω : ℕ→Finset ℕ) {M N Q : ℕ} (hQ : 1≤Q) (T : Finset ℕ) (hT : T⊆Ioc M (M+N))
    (hΩ : ∀p,p.Prime → p≤Q → Ω p⊆range p ∧ (Ω p).card<p)
    (havoid : ∀p,p.Prime → p≤Q → ∀n∈T,n%p∉Ω p) :
    (∑q∈(Icc 1 Q).filter Squarefree,sieveWeight Ω q/fareySieveCost N Q q)*(T.card:ℝ)≤1 := by
  by_cases hzero : T.card=0
  · simp [hzero]
  let a (n:ℕ) : ℂ := if n∈T then 1 else 0
  have horig := weighted_arithmetic_large_sieve Ω a M N Q hQ hΩ (by
    intro p hp hpQ n _ hn
    have h : n∉T := fun hT => havoid p hp hpQ n hT hn
    simp [a, h])
  have hset : (Ioc M (M+N)).filter (fun n => n∈T)=T := by
    ext n;simp only [mem_filter];exact ⟨And.right,fun h => ⟨hT h,h⟩⟩
  have hsum : ∑n∈Ioc M (M+N),a n=(T.card:ℂ) := by
    simp only [a,←sum_filter,hset,sum_const,nsmul_eq_mul,mul_one]
  have hnorm (n : ℕ) : ‖a n‖^2=if n∈T then (1:ℝ) else 0 := by
    by_cases h : n∈T <;> simp [a,h]
  simp only [hsum,Complex.norm_natCast,hnorm,←sum_filter,hset,sum_const,nsmul_eq_mul,mul_one] at horig
  have hpos : 0<(T.card:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
  exact le_of_mul_le_mul_right (by simpa only [mul_assoc,←sq,one_mul] using horig) hpos

/-- A bound on any set in a block of N integers avoiding multiples of primes up to z. -/
theorem card_rough_mul_weighted_denominator {M N : ℕ} {z : ℝ} (hz : 1≤z)
    (hscale : weightedHilbertConstant/π*z^2 ≤ N)
    (T : Finset ℕ) (hT : T⊆Ioc M (M+N))
    (hrough : ∀n∈T,∀p : ℕ, p.Prime → (p:ℝ)≤z → ¬p∣n) :
    (T.card:ℝ)*selbergWeightedDenominator z≤N := by
  let Q := ⌊z⌋₊
  have hQ : 1≤Q := (Nat.one_le_floor_iff _).mpr hz
  have hz' : 0<z := by linarith
  have hC : 0<weightedHilbertConstant/π := div_pos weightedHilbertConstant_pos pi_pos
  have hN : 0<(N:ℝ) := (mul_pos hC (sq_pos_of_pos hz')).trans_le hscale
  have hQz : (Q:ℝ)≤z := Nat.floor_le hz'.le
  have H := weighted_arithmetic_large_sieve_card (fun _ => {0}) hQ T hT (by
    intro p hp _;simp [hp.pos,hp.one_lt])
    (by intro p hp hpQ n hn
        simp only [mem_singleton];exact fun h => hrough n hn p hp ((Nat.cast_le.mpr hpQ).trans hQz) (Nat.dvd_of_mod_eq_zero h))
  have hW : selbergWeightedDenominator z ≤
      N * ∑q∈(Icc 1 Q).filter Squarefree,sieveWeight (fun _ => {0}) q/fareySieveCost N Q q := by
    rw [selbergWeightedDenominator,mul_sum]
    apply sum_le_sum
    intro q hq
    obtain ⟨hI,hs⟩ := mem_filter.mp hq
    have hq' := (mem_Icc.mp hI).1
    rw [singleton_sieveWeight hq' hs]
    have hF : 0<fareySieveCost N Q q := add_pos_of_pos_of_nonneg hN (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg q)) (Nat.cast_nonneg Q))
    have hcost : fareySieveCost N Q q*z ≤ N*(z+q) := by
      have hqnn : (0:ℝ)≤q := by positivity
      have hA := mul_le_mul_of_nonneg_left hQz (mul_nonneg (mul_nonneg hC.le hqnn) hz'.le)
      have hB := mul_le_mul_of_nonneg_right hscale hqnn
      dsimp [fareySieveCost];nlinarith [hA,hB]
    have hweight : z/(z+q)≤N/fareySieveCost N Q q := by
      rw [div_le_div_iff₀ (by positivity) hF];linarith only [hcost]
    calc
      _ ≤ (q.totient:ℝ)⁻¹ * (N/fareySieveCost N Q q) := mul_le_mul_of_nonneg_left hweight (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (T.card:ℝ)*(N*_) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = N*((∑q∈(Icc 1 Q).filter Squarefree,sieveWeight (fun _ => {0}) q/fareySieveCost N Q q)*(T.card:ℝ)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left H hN.le).trans_eq (mul_one _)

end AnalyticNumberTheory.SieveMethods
