import AnalyticNumberTheory.SieveMethods.PrimeCharacterSieve

/-! # Character large sieves on integers without small prime divisors -/
noncomputable section
open Real Complex Finset
open scoped Classical
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- Absence of a prime factor at most Q is equivalent to coprimality with
every positive modulus at most Q. -/
theorem rough_iff_coprime_moduli (n Q : ℕ) :
    (∀ p : ℕ,p.Prime → p≤Q → ¬p∣n) ↔ (∀r∈Icc 1 Q,n.Coprime r) := by
  constructor
  · intro h r hr
    by_contra hn
    obtain ⟨p,hp,hpn,hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact h p hp ((Nat.le_of_dvd (mem_Icc.mp hr).1 hpr).trans (mem_Icc.mp hr).2) hpn
  · intro h p hp hQ
    exact hp.coprime_iff_not_dvd.mp ((h p (mem_Icc.mpr ⟨hp.pos,hQ⟩)).symm)

/-- The arithmetic weight used for all induced characters is exactly the
squared absolute Gauss sum divided by the size of the unit group. -/
theorem inducedCharacterWeight_eq_gauss_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    inducedCharacterWeight q χ=‖DirichletLFunctions.gaussSum (star χ) 1‖^2/q.totient := by
  rw [inducedCharacterWeight,norm_gaussSum_one_eq,star_char_eq_inv,DirichletCharacter.conductor_inv]
  split <;> simp [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Conductor-weighted large sieve on coefficients with no prime factor at
most the real cutoff Q. -/
theorem rough_character_large_sieve_log_weight (a : ℕ→ℂ) (M : ℕ) {N : ℕ} {Q : ℝ}
    (hN : 1≤N) (hQ : 1≤Q)
    (ha : ∀n∈Ioc M (M+N),a n≠0 → ∀p : ℕ,p.Prime → (p:ℝ)≤Q → ¬p∣n) :
    (∑p∈primitiveCharacterFamily ⌊Q⌋₊,Real.log (Q/p.1)*‖∑n∈Ioc M (M+N),a n*p.2 n‖^2)≤
      ((N:ℝ)-1+(⌊Q⌋₊:ℝ)^2)*∑n∈Ioc M (M+N),‖a n‖^2 := by
  apply sifted_conductor_weighted_large_sieve a M hN hQ
  intro n hn h
  exact (rough_iff_coprime_moduli n ⌊Q⌋₊).mp (fun p hp hpQ =>
    ha n hn h p hp ((Nat.cast_le.mpr hpQ).trans (Nat.floor_le (zero_le_one.trans hQ))))

end AnalyticNumberTheory.SieveMethods
