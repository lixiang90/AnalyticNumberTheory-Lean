import AnalyticNumberTheory.SieveMethods.CombinatorialSieve

/-!
# Legendre's exact formula for prime counting

Sieving `(0, N]` by all primes up to `√N` leaves `1` and the primes strictly
above `√N`. Combining this observation with finite inclusion-exclusion gives
an exact expression for `π(N)` in terms of integer quotients.
-/

namespace AnalyticNumberTheory.SieveMethods

open Finset
open scoped ArithmeticFunction.Moebius

/-- Each divisor `d` contributes its Möbius weight times the number `⌊N / d⌋`
of positive multiples up to `N`. -/
theorem legendre_interval (N : ℕ) {P : ℕ} (hP : P ≠ 0) :
    (siftedCountOf (Ioc 0 N) P : ℤ) = ∑ d ∈ P.divisors, μ d * (↑(N / d) : ℤ) := by
  simpa only [sieveMultiple, Nat.Ioc_filter_dvd_card_eq_div] using
    legendre_inclusion_exclusion_int (Ioc 0 N) hP

/-- A positive integer up to `N` survives the sieve up to `√N` precisely when
it is `1` or a prime exceeding `√N`. -/
theorem coprime_primorial_sqrt_iff {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.Coprime (primorial N.sqrt) ↔ n = 1 ∨ n.Prime ∧ N.sqrt < n := by
  constructor
  · intro h
    by_cases h₁ : n = 1
    · exact Or.inl h₁
    have hp : n.Prime := by
      by_contra hcomp
      have hmin := Nat.minFac_prime h₁
      have hle := Nat.le_sqrt'.2 ((Nat.minFac_sq_le_self hn hcomp).trans hnN)
      exact (hmin.coprime_iff_not_dvd.mp (h.coprime_dvd_left (Nat.minFac_dvd n)))
        (hmin.dvd_primorial_iff.mpr hle)
    exact Or.inr ⟨hp, lt_of_not_ge fun hle =>
      hp.coprime_iff_not_dvd.mp h (hp.dvd_primorial_iff.mpr hle)⟩
  · rintro (rfl | ⟨hp, hlt⟩)
    · exact Nat.coprime_one_left _
    · exact hp.coprime_iff_not_dvd.mpr fun hd => hlt.not_ge (hp.dvd_primorial_iff.mp hd)

/-- **Legendre's prime-counting formula**. The `- 1` removes the unit among
the survivors. The lower bound on `N` ensures that the unit is in `(0, N]`. -/
theorem legendre_primeCounting {N : ℕ} (hN : 0 < N) :
    (N.primeCounting : ℤ) = (N.sqrt.primeCounting : ℤ) - 1 +
      ∑ d ∈ (primorial N.sqrt).divisors, μ d * (↑(N / d) : ℤ) := by
  classical
  let large := N.primesLE \ N.sqrt.primesLE
  have hsurvivors : (Ioc 0 N).filter (fun n => n.Coprime (primorial N.sqrt)) =
      insert 1 large := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_insert, large, mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hn, hnN⟩, h⟩
      rcases (coprime_primorial_sqrt_iff hn hnN).mp h with h₁ | ⟨hp, hlt⟩
      · exact Or.inl h₁
      · exact Or.inr ⟨⟨hnN, hp⟩, fun hs => hlt.not_ge hs.1⟩
    · rintro (rfl | ⟨⟨hnN, hp⟩, hs⟩)
      · exact ⟨⟨Nat.zero_lt_one, hN⟩, Nat.coprime_one_left _⟩
      · exact ⟨⟨hp.pos, hnN⟩, (coprime_primorial_sqrt_iff hp.pos hnN).mpr
          (Or.inr ⟨hp, lt_of_not_ge fun hle => hs ⟨hle, hp⟩⟩)⟩
  have h₁ : 1 ∉ large := fun h => Nat.not_prime_one (Nat.mem_primesLE.mp (mem_sdiff.mp h).1).2
  have hcount := card_sdiff_add_card_eq_card (Nat.primesLE_mono (Nat.sqrt_le_self N))
  change large.card + N.sqrt.primesLE.card = N.primesLE.card at hcount
  simp only [Nat.primesLE_card_eq_primeCounting] at hcount
  rw [← legendre_interval N (primorial_pos _).ne', siftedCountOf, hsurvivors,
    card_insert_of_notMem h₁]
  omega

end AnalyticNumberTheory.SieveMethods
