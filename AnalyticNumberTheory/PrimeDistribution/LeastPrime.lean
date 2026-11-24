import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions

/-!
# The least prime in a reduced residue class

Dirichlet's theorem supplies a prime in every reduced class of a positive
modulus. To bound the first prime by a given `x`, it suffices to show that
`θ(x; q, a)` is positive. A lower bound for `ψ(x; q, a)` also suffices if it
exceeds the contribution of higher prime powers.
-/

namespace AnalyticNumberTheory.PrimeDistribution

variable {q a b : ℕ}

private theorem exists_prime_modEq (hq : q ≠ 0) (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] :=
  (dirichlet_primesInAP_infinite hq ha).nonempty

/-- The smallest prime congruent to `a` modulo `q`, for a reduced class. -/
noncomputable def leastPrimeAP (hq : q ≠ 0) (ha : a.Coprime q) : ℕ :=
  Nat.find (exists_prime_modEq hq ha)

theorem leastPrimeAP_spec (hq : q ≠ 0) (ha : a.Coprime q) :
    (leastPrimeAP hq ha).Prime ∧ leastPrimeAP hq ha ≡ a [MOD q] :=
  Nat.find_spec (exists_prime_modEq hq ha)

theorem leastPrimeAP_le (hq : q ≠ 0) (ha : a.Coprime q) {p : ℕ}
    (hp : p.Prime) (hpa : p ≡ a [MOD q]) : leastPrimeAP hq ha ≤ p :=
  Nat.find_min' (exists_prime_modEq hq ha) ⟨hp, hpa⟩

/-- Changing the representative of a reduced class preserves its least prime. -/
theorem leastPrimeAP_congr (hq : q ≠ 0) (ha : a.Coprime q) (hb : b.Coprime q)
    (hab : a ≡ b [MOD q]) : leastPrimeAP hq ha = leastPrimeAP hq hb := by
  obtain ⟨hpa, ha'⟩ := leastPrimeAP_spec hq ha
  obtain ⟨hpb, hb'⟩ := leastPrimeAP_spec hq hb
  exact le_antisymm (leastPrimeAP_le hq ha hpb (hb'.trans hab.symm))
    (leastPrimeAP_le hq hb hpa (ha'.trans hab))

theorem leastPrimeAP_le_iff (hq : q ≠ 0) (ha : a.Coprime q) (n : ℕ) :
    leastPrimeAP hq ha ≤ n ↔ ∃ p ≤ n, p.Prime ∧ p ≡ a [MOD q] :=
  Nat.find_le_iff (exists_prime_modEq hq ha) n

/-- Every prime contributes a strictly positive logarithm to `θ`. This detects
the presence of a prime even when `x` is a real, nonintegral cutoff. -/
theorem thetaAP_pos_iff_exists_prime (x : ℝ) (q a : ℕ) :
    0 < thetaAP x q a ↔ ∃ p : ℕ, (p : ℝ) ≤ x ∧ p.Prime ∧ p ≡ a [MOD q] := by
  let s := (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  have hlog (p : ℕ) (hp : p ∈ s) : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt)
  change 0 < ∑ p ∈ s, Real.log p ↔ _
  rw [Finset.sum_pos_iff_of_nonneg (fun p hp => (hlog p hp).le)]
  constructor
  · rintro ⟨p, hp, _⟩
    obtain ⟨hi, hprime, hmod⟩ := Finset.mem_filter.mp hp
    exact ⟨p, (Nat.le_floor_iff' hprime.ne_zero).mp (Finset.mem_Icc.mp hi).2, hprime, hmod⟩
  · rintro ⟨p, hpx, hprime, hmod⟩
    have hp : p ∈ s := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hprime.pos, Nat.le_floor hpx⟩, hprime, hmod⟩
    exact ⟨p, hp, hlog p hp⟩

/-- The prime with least value in a reduced residue class lies at or below `x`
exactly when the Chebyshev theta sum for that class is positive. -/
theorem leastPrimeAP_le_iff_thetaAP_pos (hq : q ≠ 0) (ha : a.Coprime q) (x : ℝ) :
    (leastPrimeAP hq ha : ℝ) ≤ x ↔ 0 < thetaAP x q a := by
  rw [thetaAP_pos_iff_exists_prime]
  constructor
  · intro h
    exact ⟨_, h, leastPrimeAP_spec hq ha⟩
  · rintro ⟨p, hpx, hp, hpa⟩
    exact (Nat.cast_le.mpr (leastPrimeAP_le hq ha hp hpa)).trans hpx

/-- A `ψ` lower bound that dominates all higher prime powers forces a prime
in the progression by `x`. The constant is uniform in `q` and `a`. -/
theorem leastPrimeAP_le_of_psiAP (hq : q ≠ 0) (ha : a.Coprime q) {x : ℝ}
    (hψ : (Real.log 4 + 4) * 3 * Real.sqrt x < psiAP x q a) :
    (leastPrimeAP hq ha : ℝ) ≤ x := by
  apply (leastPrimeAP_le_iff_thetaAP_pos hq ha x).mpr
  linarith [(le_abs_self _).trans (abs_psiAP_sub_thetaAP_le x q a)]

/-- A bound `E` for the error in the main term of `ψ(x; q, a)` gives a
least-prime estimate once the main term exceeds both sources of error. -/
theorem leastPrimeAP_le_of_psiAP_error (hq : q ≠ 0) (ha : a.Coprime q) {x E : ℝ}
    (herror : |psiAP x q a - x / q.totient| ≤ E)
    (hmain : E + (Real.log 4 + 4) * 3 * Real.sqrt x < x / q.totient) :
    (leastPrimeAP hq ha : ℝ) ≤ x := by
  apply leastPrimeAP_le_of_psiAP hq ha
  linarith [(abs_le.mp herror).1]

open scoped Classical in
/-- A single estimate on the nonprincipal characters yields a bound for the
least prime in *every* reduced class modulo `q`. The first two error terms
account for the principal character, and the last one for higher prime powers. -/
theorem leastPrimeAP_le_of_character_sums (hq : q ≠ 0) {x : ℝ} (hx : 1 ≤ x)
    (h : |Chebyshev.psi x - x| + (Real.log q / Real.log 2) * Real.log x +
      (∑ χ ∈ ({(1 : DirichletCharacter ℂ q)}ᶜ : Finset (DirichletCharacter ℂ q)),
        ‖psiChar x χ‖) + ((Real.log 4 + 4) * 3 * Real.sqrt x) * q.totient < x) :
    ∀ {a : ℕ} (ha : a.Coprime q), (leastPrimeAP hq ha : ℝ) ≤ x := by
  intro a ha
  refine leastPrimeAP_le_of_psiAP_error hq ha
    (abs_psiAP_sub_div_totient_le_sum_chars hx (Nat.pos_of_ne_zero hq) ha) ?_
  have hφ : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  apply (lt_div_iff₀ hφ).mpr
  rwa [add_mul, mul_comm (q.totient : ℝ)⁻¹ _, mul_assoc, inv_mul_cancel₀ hφ.ne', mul_one]

end AnalyticNumberTheory.PrimeDistribution
