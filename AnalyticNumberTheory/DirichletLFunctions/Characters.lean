import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Dirichlet Characters

This file provides an ergonomic API over Mathlib's `DirichletCharacter ℂ q` for analytic
number theory:

- Principal, real/quadratic, and complex characters, norms, conjugation, and unit-coprime
  evaluation.
- Both character orthogonality relations (`∑_{a mod q} χ(a)` and
  `∑_{χ mod q} χ(a) * star (χ(b))`), including `Finset.range` and `Finset.Ioc` variants.
- Even and odd parity (`χ(-1) = 1` vs `χ(-1) = -1`), parity index `paritySign χ ∈ {0, 1}`,
  and parity counts for `q ≥ 3`.
- Conductor `conductor`, primitivity `IsPrimitive`, unique induction factorization
  `χ = principal * χ*`, and exact counting of primitive characters `primitiveCharCount q`
  (`φ*(q)`) together with `∑_{d ∣ q} φ*(d) = φ(q)`, Möbius inversion, multiplicativity,
  and prime-power formulas.
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius Classical

namespace AnalyticNumberTheory.DirichletLFunctions

section BasicAPI

variable {q : ℕ}

/-- The principal (trivial) Dirichlet character modulo `q`. -/
noncomputable def principalChar (q : ℕ) : DirichletCharacter ℂ q :=
  (1 : DirichletCharacter ℂ q)

/-- Predicate stating that a Dirichlet character `χ` modulo `q` is the principal character. -/
def IsPrincipal (χ : DirichletCharacter ℂ q) : Prop :=
  χ = 1

/-- Equivalence between `IsPrincipal χ` and `χ = 1`. -/
@[simp]
theorem isPrincipal_iff {χ : DirichletCharacter ℂ q} : IsPrincipal χ ↔ χ = 1 :=
  Iff.rfl

/-- Evaluation of `principalChar q` at a natural number `n`. -/
theorem principalChar_apply_nat (n : ℕ) :
    principalChar q n = if Nat.Coprime n q then 1 else 0 := by
  by_cases h : Nat.Coprime n q
  · simp [h, principalChar, MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h)]
  · simp [h, principalChar, MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]

/-- Evaluation of `principalChar q` at an integer `a`. -/
theorem principalChar_apply_int (a : ℤ) :
    principalChar q a = if IsCoprime a q then 1 else 0 := by
  by_cases h : IsCoprime a q
  · simp [h, principalChar, MulChar.one_apply ((ZMod.isUnit_intCast_iff_isCoprime a q).mpr h.symm)]
  · have hnu : ¬ IsUnit (a : ZMod q) := by
      rw [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm]
      exact h
    simp [h, principalChar, MulChar.map_nonunit _ hnu]

/-- `χ a ≠ 0` if and only if `IsCoprime a q`. -/
theorem char_ne_zero_iff_isCoprime (χ : DirichletCharacter ℂ q) (a : ℤ) :
    χ a ≠ 0 ↔ IsCoprime a q :=
  χ.apply_ne_zero_iff a

/-- `χ a = 0` if and only if `¬ IsCoprime a q`. -/
theorem char_eq_zero_iff_not_isCoprime (χ : DirichletCharacter ℂ q) (a : ℤ) :
    χ a = 0 ↔ ¬ IsCoprime a q :=
  χ.apply_eq_zero_iff a

/-- `χ (n : ℕ) ≠ 0` if and only if `Nat.Coprime n q`. -/
theorem char_nat_ne_zero_iff_coprime (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ n ≠ 0 ↔ Nat.Coprime n q := by
  rw [MulChar.apply_ne_zero_iff, ZMod.isUnit_iff_coprime]

/-- `χ (n : ℕ) = 0` if and only if `¬ Nat.Coprime n q`. -/
theorem char_nat_eq_zero_iff_not_coprime (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ n = 0 ↔ ¬ Nat.Coprime n q := by
  rw [← (char_nat_ne_zero_iff_coprime χ n).not, ne_eq, not_not]

/-- Norm of `χ a` equals `1` whenever `a : ZMod q` is a unit. -/
theorem norm_char_eq_one_of_isUnit (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    ‖χ a‖ = 1 := by
  simpa using χ.unit_norm_eq_one ha.unit

/-- Norm of `χ n` equals `1` whenever `Nat.Coprime n q`. -/
theorem norm_char_eq_one_of_coprime (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : Nat.Coprime n q) :
    ‖χ n‖ = 1 :=
  norm_char_eq_one_of_isUnit χ ((ZMod.isUnit_iff_coprime n q).mpr hn)

/-- Every character value satisfies `‖χ a‖ ≤ 1`. -/
theorem norm_char_le_one (χ : DirichletCharacter ℂ q) (a : ZMod q) : ‖χ a‖ ≤ 1 :=
  χ.norm_le_one a

/-- Complex conjugation of a complex Dirichlet character equals its multiplicative inverse. -/
theorem star_char_eq_inv (χ : DirichletCharacter ℂ q) : star χ = χ⁻¹ :=
  MulChar.star_eq_inv χ

/-- Pointwise identity `star (χ a) = χ⁻¹ a` for complex Dirichlet characters. -/
theorem star_char_apply (χ : DirichletCharacter ℂ q) (a : ZMod q) : star (χ a) = χ⁻¹ a :=
  MulChar.star_apply' χ a

/-- Conjugation `starRingEnd ℂ (χ a)` equals `χ⁻¹ a`. -/
theorem conj_char_apply (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    starRingEnd ℂ (χ a) = χ⁻¹ a := by
  simpa [RCLike.star_def] using star_char_apply χ a

/-- Raising `χ` to `q.totient` gives the principal character (for `q ≠ 0`). -/
theorem char_pow_totient_eq_one [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ ^ q.totient = 1 := by
  rw [← ZMod.card_units_eq_totient q, MulChar.pow_card_eq_one]

/-- The number of Dirichlet characters modulo `q` (`q ≠ 0`) equals `q.totient`. -/
theorem card_dirichletCharacter_eq_totient [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

end BasicAPI

section Orthogonality

variable {q : ℕ} [NeZero q]

private theorem sum_zmod_eq_sum_range (f : ZMod q → ℂ) :
    ∑ a : ZMod q, f a = ∑ a ∈ Finset.range q, f (a : ZMod q) := by
  refine Finset.sum_bij (fun a _ ↦ a.val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a₁ _ a₂ _ h
    exact ZMod.val_injective q h
  · intro b hb
    refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)
  · intro a _
    simp

/-- Sum of `χ a` over all `a : ZMod q` is `0` when `χ ≠ 1`. -/
theorem sum_zmod_eq_zero_of_ne_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∑ a : ZMod q, χ a = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

/-- Sum of `χ a` over all `a : ZMod q` equals `q.totient` if `χ = 1` and `0` otherwise. -/
theorem sum_zmod_eq (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, χ a = if χ = 1 then (q.totient : ℂ) else 0 := by
  split_ifs with h
  · subst h
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact sum_zmod_eq_zero_of_ne_one h

/-- First orthogonality relation over `ZMod q`:
`∑ a : ZMod q, χ a * star (ψ a) = if χ = ψ then q.totient else 0`. -/
theorem sum_zmod_mul_conj_eq (χ ψ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, χ a * star (ψ a) = if χ = ψ then (q.totient : ℂ) else 0 := by
  have hterm (a : ZMod q) : χ a * star (ψ a) = (χ * ψ⁻¹) a := by
    rw [MulChar.mul_apply, star_char_apply]
  simp_rw [hterm, sum_zmod_eq]
  simp [mul_inv_eq_one]

/-- Sum of `χ a` over `a ∈ Finset.range q` equals `q.totient` if `χ = 1` and `0` otherwise. -/
theorem sum_range_eq (χ : DirichletCharacter ℂ q) :
    ∑ a ∈ Finset.range q, χ a = if χ = 1 then (q.totient : ℂ) else 0 := by
  rw [← sum_zmod_eq_sum_range, sum_zmod_eq]

/-- Sum of `χ a * star (ψ a)` over `a ∈ Finset.range q`. -/
theorem sum_range_mul_conj_eq (χ ψ : DirichletCharacter ℂ q) :
    ∑ a ∈ Finset.range q, χ a * star (ψ a) = if χ = ψ then (q.totient : ℂ) else 0 := by
  have hterm (a : ℕ) : χ a * star (ψ a) = (χ * ψ⁻¹) a := by
    rw [MulChar.mul_apply, star_char_apply]
  simp_rw [hterm, sum_range_eq]
  simp [mul_inv_eq_one]

/-- Sum of `χ (M + a)` over a full period `a ∈ Finset.range q` equals `q.totient` if `χ = 1`
and `0` otherwise. -/
theorem sum_shift_range_eq (χ : DirichletCharacter ℂ q) (M : ℕ) :
    ∑ a ∈ Finset.range q, χ (M + a : ℕ) = if χ = 1 then (q.totient : ℂ) else 0 := by
  have h : ∑ a ∈ Finset.range q, χ (M + a : ℕ) = ∑ a : ZMod q, χ ((M : ZMod q) + a) := by
    symm
    calc
      ∑ a : ZMod q, χ ((M : ZMod q) + a)
          = ∑ a ∈ Finset.range q, χ ((M : ZMod q) + (a : ZMod q)) :=
            sum_zmod_eq_sum_range (fun a ↦ χ ((M : ZMod q) + a))
      _ = ∑ a ∈ Finset.range q, χ (M + a : ℕ) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          push_cast
          rfl
  rw [h]
  exact (Equiv.sum_comp (Equiv.addLeft (M : ZMod q)) χ).trans (sum_zmod_eq χ)

/-- Sum of `χ n` over any interval `Finset.Ioc M (M + q)` of length `q`. -/
theorem sum_Ioc_period_eq (χ : DirichletCharacter ℂ q) (M : ℕ) :
    ∑ n ∈ Finset.Ioc M (M + q), χ n = if χ = 1 then (q.totient : ℂ) else 0 := by
  rw [← sum_shift_range_eq χ (M + 1)]
  refine Finset.sum_bij (fun n _ ↦ n - (M + 1)) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    refine ⟨M + 1 + a, ?_, by omega⟩
    simp only [Finset.mem_Ioc]
    omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    congr 2
    omega

/-- Sum of `χ a` over all Dirichlet characters `χ` modulo `q`. -/
theorem sum_chars_eq (a : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a = if a = 1 then (q.totient : ℂ) else 0 :=
  DirichletCharacter.sum_characters_eq ℂ a

/-- Second orthogonality relation over `ZMod q` when `b` is a unit:
`∑ χ : DirichletCharacter ℂ q, χ a * star (χ b) = if a = b then q.totient else 0`. -/
theorem sum_chars_mul_conj_eq (a : ZMod q) {b : ZMod q} (hb : IsUnit b) :
    ∑ χ : DirichletCharacter ℂ q, χ a * star (χ b) = if a = b then (q.totient : ℂ) else 0 := by
  have hterm (χ : DirichletCharacter ℂ q) : χ a * star (χ b) = χ b⁻¹ * χ a := by
    rw [star_char_apply, MulChar.inv_apply_eq_inv', mul_comm]
    congr 1
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, mul_comm b b⁻¹, (ZMod.inv_mul_eq_one_of_isUnit hb b).mpr rfl, map_one]
  simp_rw [hterm, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb a]
  simp [eq_comm]

/-- Second orthogonality relation over `ZMod q` without unit hypotheses:
`∑ χ, χ a * star (χ b) = if IsUnit b ∧ a = b then q.totient else 0`. -/
theorem sum_chars_mul_conj_eq_general (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a * star (χ b) =
      if IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · simp only [hb, true_and]
    exact sum_chars_mul_conj_eq a hb
  · simp [hb, MulChar.map_nonunit _ hb]

/-- Second orthogonality relation for natural numbers `a, b` with `Nat.Coprime b q`:
`∑ χ : DirichletCharacter ℂ q, χ a * star (χ b) = if a ≡ b [MOD q] then q.totient else 0`. -/
theorem sum_chars_nat_mul_conj_eq (a : ℕ) {b : ℕ} (hb : Nat.Coprime b q) :
    ∑ χ : DirichletCharacter ℂ q, χ a * star (χ b) =
      if a ≡ b [MOD q] then (q.totient : ℂ) else 0 := by
  have hbu : IsUnit (b : ZMod q) := (ZMod.isUnit_iff_coprime b q).mpr hb
  rw [sum_chars_mul_conj_eq (a : ZMod q) hbu]
  simp [ZMod.natCast_eq_natCast_iff]

end Orthogonality

section Parity

variable {q : ℕ}

/-- A Dirichlet character `χ` is even if `χ (-1) = 1`. -/
def IsEven (χ : DirichletCharacter ℂ q) : Prop :=
  χ.Even

/-- A Dirichlet character `χ` is odd if `χ (-1) = -1`. -/
def IsOdd (χ : DirichletCharacter ℂ q) : Prop :=
  χ.Odd

/-- Equivalence between `IsEven χ` and `χ (-1) = 1`. -/
theorem isEven_iff (χ : DirichletCharacter ℂ q) : IsEven χ ↔ χ (-1) = 1 :=
  Iff.rfl

/-- Equivalence between `IsOdd χ` and `χ (-1) = -1`. -/
theorem isOdd_iff (χ : DirichletCharacter ℂ q) : IsOdd χ ↔ χ (-1) = -1 :=
  Iff.rfl

/-- Every complex Dirichlet character is either even or odd. -/
theorem even_or_odd (χ : DirichletCharacter ℂ q) : IsEven χ ∨ IsOdd χ :=
  χ.even_or_odd

/-- No complex Dirichlet character is both even and odd. -/
theorem not_even_and_odd (χ : DirichletCharacter ℂ q) : ¬ (IsEven χ ∧ IsOdd χ) :=
  χ.not_even_and_odd

/-- The parity parameter `κ ∈ {0, 1}` of `χ`: `0` when `χ` is even, and `1` when `χ` is odd. -/
noncomputable def paritySign (χ : DirichletCharacter ℂ q) : ℕ :=
  if χ.Even then 0 else 1

/-- `paritySign χ = 0` if and only if `χ` is even. -/
@[simp]
theorem paritySign_eq_zero_iff (χ : DirichletCharacter ℂ q) :
    paritySign χ = 0 ↔ IsEven χ := by
  simp [paritySign, IsEven]

/-- `paritySign χ = 1` if and only if `χ` is odd. -/
@[simp]
theorem paritySign_eq_one_iff (χ : DirichletCharacter ℂ q) :
    paritySign χ = 1 ↔ IsOdd χ := by
  unfold paritySign IsOdd
  split_ifs with h
  · constructor
    · intro h0; cases h0
    · intro ho; exact absurd ho h.not_odd
  · constructor
    · intro _; exact χ.even_or_odd.resolve_left h
    · intro _; rfl

/-- `paritySign χ` is either `0` or `1`. -/
theorem paritySign_eq_zero_or_one (χ : DirichletCharacter ℂ q) :
    paritySign χ = 0 ∨ paritySign χ = 1 := by
  unfold paritySign
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `χ (-1) = (-1 : ℂ) ^ paritySign χ`. -/
theorem char_neg_one_eq_neg_one_pow_paritySign (χ : DirichletCharacter ℂ q) :
    χ (-1) = (-1 : ℂ) ^ paritySign χ := by
  rcases even_or_odd χ with h | h
  · rw [(paritySign_eq_zero_iff χ).mpr h, pow_zero, h]
  · rw [(paritySign_eq_one_iff χ).mpr h, pow_one, h]

/-- Parity sign of `1` is `0`. -/
@[simp]
theorem paritySign_one : paritySign (1 : DirichletCharacter ℂ q) = 0 :=
  (paritySign_eq_zero_iff _).mpr DirichletCharacter.even_one

/-- Parity sign of `χ⁻¹` equals `paritySign χ`. -/
@[simp]
theorem paritySign_inv (χ : DirichletCharacter ℂ q) : paritySign χ⁻¹ = paritySign χ := by
  have hev : χ⁻¹.Even ↔ χ.Even := by
    simp only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_eq_one]
  simp [paritySign, hev]

/-- Parity sign of `star χ` equals `paritySign χ`. -/
@[simp]
theorem paritySign_star (χ : DirichletCharacter ℂ q) : paritySign (star χ) = paritySign χ := by
  rw [star_char_eq_inv, paritySign_inv]

/-- Parity sign of `χ.primitiveCharacter` equals `paritySign χ` when `q ≠ 0`. -/
@[simp]
theorem paritySign_primitiveCharacter [NeZero q] (χ : DirichletCharacter ℂ q) :
    paritySign χ.primitiveCharacter = paritySign χ := by
  have hev : χ.primitiveCharacter.Even ↔ χ.Even := by
    have hcop : IsCoprime (-1 : ℤ) q := isCoprime_one_left.neg_left
    have hval := χ.primitiveCharacter_apply_of_isCoprime hcop
    simp only [Int.cast_neg, Int.cast_one] at hval
    simp [DirichletCharacter.Even, hval]
  simp [paritySign, hev]

/-- Every character modulo `1` or `2` is even. -/
theorem isEven_of_le_two (hq : q ≤ 2) (hq0 : q ≠ 0) (χ : DirichletCharacter ℂ q) : IsEven χ := by
  have h : (-1 : ZMod q) = 1 := by
    interval_cases q
    · exact absurd rfl hq0
    · decide
    · decide
  rw [isEven_iff, h, map_one]

/-- When `q ≥ 3`, there exists an odd Dirichlet character modulo `q`. -/
theorem exists_isOdd_of_three_le (hq : 3 ≤ q) : ∃ χ : DirichletCharacter ℂ q, IsOdd χ := by
  have : NeZero q := ⟨by omega⟩
  have hne : (-1 : ZMod q) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod q) = 0 := by
      have : (1 : ZMod q) + 1 = (-1 : ZMod q) + 1 := congrArg (· + 1) h.symm
      simpa [one_add_one_eq_two] using this
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h2
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne
  refine ⟨χ, ?_⟩
  rcases even_or_odd χ with hev | hodd
  · exact absurd hev hχ
  · exact hodd

/-- When `q ≥ 3`, the number of even characters equals the number of odd characters. -/
theorem card_isEven_eq_card_isOdd_of_three_le (hq : 3 ≤ q) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ IsEven χ)).card =
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ IsOdd χ)).card := by
  obtain ⟨ψ, hψ⟩ := exists_isOdd_of_three_le hq
  refine Finset.card_bij (fun χ _ ↦ ψ * χ) ?_ ?_ ?_
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    rw [isOdd_iff, MulChar.mul_apply, hψ, hχ, mul_one]
  · intro χ₁ _ χ₂ _ h
    exact mul_left_cancel h
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    refine ⟨ψ⁻¹ * χ, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, isEven_iff, MulChar.mul_apply,
        MulChar.inv_apply_eq_inv']
      rw [hψ, hχ]
      norm_num
    · rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- When `q ≥ 3`, `∑ χ, χ (-1) = 0`. -/
theorem sum_chars_neg_one_of_three_le (hq : 3 ≤ q) :
    ∑ χ : DirichletCharacter ℂ q, χ (-1) = 0 := by
  have : NeZero q := ⟨by omega⟩
  have hne : (-1 : ZMod q) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod q) = 0 := by
      have : (1 : ZMod q) + 1 = (-1 : ZMod q) + 1 := congrArg (· + 1) h.symm
      simpa [one_add_one_eq_two] using this
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h2
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rw [sum_chars_eq (-1)]
  simp [hne]

end Parity

section InductionAndConductor

variable {q : ℕ}

/-- Re-export of conductor divisibility `χ.conductor ∣ q`. -/
theorem conductor_dvd (χ : DirichletCharacter ℂ q) : χ.conductor ∣ q :=
  χ.conductor_dvd_level

/-- `χ.conductor ≠ 0` when `q ≠ 0`. -/
theorem conductor_ne_zero' [NeZero q] (χ : DirichletCharacter ℂ q) : χ.conductor ≠ 0 :=
  χ.conductor_ne_zero

/-- `0 < χ.conductor` when `q ≠ 0`. -/
theorem conductor_pos [NeZero q] (χ : DirichletCharacter ℂ q) : 0 < χ.conductor :=
  Nat.pos_of_ne_zero χ.conductor_ne_zero

/-- Characterization of `χ.conductor = 1`: `χ` is principal if and only if its conductor is `1`. -/
theorem conductor_eq_one_iff [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.conductor = 1 ↔ χ = 1 :=
  χ.eq_one_iff_conductor_eq_one.symm

/-- Non-principal characters have conductor at least `3` (since modulus `2` has only the
principal character). -/
theorem three_le_conductor_of_ne_one [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    3 ≤ χ.conductor := by
  have hpos : 0 < χ.conductor := conductor_pos χ
  have hne1 : χ.conductor ≠ 1 := by rwa [ne_eq, conductor_eq_one_iff]
  have hne2 : χ.conductor ≠ 2 := by
    intro h2
    have h1 : χ.primitiveCharacter = 1 := by
      have hcard : Nat.totient 2 = 1 := by decide
      have hfc : Fintype.card (DirichletCharacter ℂ χ.conductor) = 1 := by
        have : NeZero χ.conductor := ⟨hpos.ne'⟩
        rw [card_dirichletCharacter_eq_totient, h2, hcard]
      have : Subsingleton (DirichletCharacter ℂ χ.conductor) :=
        Fintype.card_le_one_iff_subsingleton.mp hfc.le
      exact Subsingleton.elim χ.primitiveCharacter 1
    have hc := χ.primitiveCharacter_isPrimitive
    rw [DirichletCharacter.isPrimitive_def, h1,
      @DirichletCharacter.conductor_one ℂ _ χ.conductor ⟨hpos.ne'⟩] at hc
    omega
  omega

/-- Every non-principal character modulo `q` forces `q ≥ 3`. -/
theorem three_le_level_of_ne_one [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    3 ≤ q :=
  (three_le_conductor_of_ne_one hχ).trans (Nat.le_of_dvd (NeZero.pos q) (conductor_dvd χ))

/-- Unique induction factorization at the level of `DirichletCharacter ℂ q`:
`χ = principalChar q * DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter`. -/
theorem induced_factorization_eq (χ : DirichletCharacter ℂ q) :
    χ = principalChar q *
      DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter := by
  rw [principalChar, one_mul, χ.changeLevel_primitiveCharacter]

/-- Pointwise induction factorization on `ℤ`:
`χ a = principalChar q a * χ.primitiveCharacter a`. -/
theorem induced_factorization_int (χ : DirichletCharacter ℂ q) (a : ℤ) :
    χ a = principalChar q a * χ.primitiveCharacter a := by
  rw [principalChar_apply_int]
  split_ifs with ha
  · rw [one_mul, χ.primitiveCharacter_apply_of_isCoprime ha]
  · rw [zero_mul, (char_eq_zero_iff_not_isCoprime χ a).mpr ha]

/-- Pointwise induction factorization on `ℕ`:
`χ n = principalChar q n * χ.primitiveCharacter n`. -/
theorem induced_factorization_nat (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ n = principalChar q n * χ.primitiveCharacter n := by
  simpa using induced_factorization_int χ n

/-- Uniqueness of the primitive character inducing `χ`: if `χ = changeLevel hd ψ` for a primitive
character `ψ` of level `d`, then `d = χ.conductor` and
`changeLevel (dvd_of_eq h) ψ = χ.primitiveCharacter`. -/
theorem unique_primitive_factorization [NeZero q] {χ : DirichletCharacter ℂ q} {d : ℕ}
    (hd : d ∣ q) {ψ : DirichletCharacter ℂ d} (hψ : ψ.IsPrimitive)
    (hχ : χ = DirichletCharacter.changeLevel hd ψ) :
    ∃ h : d = χ.conductor,
      DirichletCharacter.changeLevel (dvd_of_eq h) ψ = χ.primitiveCharacter := by
  have hcond : χ.conductor = d := by
    rw [hχ, DirichletCharacter.conductor_changeLevel ψ hd, hψ]
  refine ⟨hcond.symm, ?_⟩
  apply DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
  rw [← DirichletCharacter.changeLevel_trans, χ.changeLevel_primitiveCharacter]
  exact hχ.symm

/-- Lifting a primitive character `ψ` of level `d ∣ q` to level `q` preserves its conductor `d`. -/
theorem conductor_changeLevel_of_isPrimitive [NeZero q] {d : ℕ} (hd : d ∣ q)
    {ψ : DirichletCharacter ℂ d} (hψ : ψ.IsPrimitive) :
    (DirichletCharacter.changeLevel hd ψ).conductor = d := by
  rw [DirichletCharacter.conductor_changeLevel ψ hd, hψ]

end InductionAndConductor

section Classification

variable {q : ℕ}

/-- A Dirichlet character `χ` is real-valued if all its values have imaginary part `0`. -/
def IsReal (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ a : ZMod q, (χ a).im = 0

/-- A Dirichlet character `χ` is a nontrivial quadratic character if `χ ≠ 1` and `χ ^ 2 = 1`. -/
def IsQuadratic (χ : DirichletCharacter ℂ q) : Prop :=
  χ ≠ 1 ∧ χ ^ 2 = 1

/-- A Dirichlet character `χ` is complex (non-real) if `χ ^ 2 ≠ 1`. -/
def IsComplexChar (χ : DirichletCharacter ℂ q) : Prop :=
  χ ^ 2 ≠ 1

/-- `IsReal χ` if and only if `star χ = χ`. -/
theorem isReal_iff_star_eq (χ : DirichletCharacter ℂ q) : IsReal χ ↔ star χ = χ := by
  constructor
  · intro h
    ext1 a
    rw [MulChar.star_apply]
    exact Complex.ext rfl (by simp [h a])
  · intro h a
    have ha : star (χ a) = χ a := by
      have := congr_fun (congr_arg DFunLike.coe h) a
      simpa using this
    have him : -(χ a).im = (χ a).im := by
      have := congr_arg Complex.im ha
      simpa using this
    linarith

/-- `star χ = χ` if and only if `χ ^ 2 = 1`. -/
theorem star_eq_self_iff_sq_eq_one (χ : DirichletCharacter ℂ q) : star χ = χ ↔ χ ^ 2 = 1 := by
  rw [star_char_eq_inv, inv_eq_iff_mul_eq_one, pow_two]

/-- `IsReal χ` if and only if `χ ^ 2 = 1`. -/
theorem isReal_iff_sq_eq_one (χ : DirichletCharacter ℂ q) : IsReal χ ↔ χ ^ 2 = 1 :=
  (isReal_iff_star_eq χ).trans (star_eq_self_iff_sq_eq_one χ)

/-- `IsReal χ` if and only if `MulChar.IsQuadratic χ`. -/
theorem isReal_iff_mulChar_isQuadratic (χ : DirichletCharacter ℂ q) :
    IsReal χ ↔ MulChar.IsQuadratic χ := by
  rw [isReal_iff_sq_eq_one, MulChar.isQuadratic_iff_sq_eq_one]

/-- `IsReal χ` if and only if every value of `χ` lies in `{0, 1, -1}`. -/
theorem isReal_iff_apply_mem (χ : DirichletCharacter ℂ q) :
    IsReal χ ↔ ∀ a : ZMod q, χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  rw [isReal_iff_mulChar_isQuadratic]
  constructor
  · intro h a
    exact h a
  · intro h a
    exact h a

/-- `IsComplexChar χ` if and only if `¬ IsReal χ`. -/
theorem isComplexChar_iff_not_isReal (χ : DirichletCharacter ℂ q) :
    IsComplexChar χ ↔ ¬ IsReal χ := by
  rw [IsComplexChar, isReal_iff_sq_eq_one]

/-- `IsComplexChar χ` if and only if there exists `a : ZMod q` with `(χ a).im ≠ 0`. -/
theorem isComplexChar_iff_exists_im_ne_zero (χ : DirichletCharacter ℂ q) :
    IsComplexChar χ ↔ ∃ a : ZMod q, (χ a).im ≠ 0 := by
  rw [isComplexChar_iff_not_isReal, IsReal, not_forall]

/-- Every Dirichlet character modulo `q` is either principal, nontrivial quadratic, or complex. -/
theorem trichotomy (χ : DirichletCharacter ℂ q) :
    IsPrincipal χ ∨ IsQuadratic χ ∨ IsComplexChar χ := by
  by_cases h1 : χ = 1
  · exact Or.inl h1
  · by_cases h2 : χ ^ 2 = 1
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr h2)

/-- Every real Dirichlet character is either principal or nontrivial quadratic. -/
theorem isPrincipal_or_isQuadratic_of_isReal {χ : DirichletCharacter ℂ q} (h : IsReal χ) :
    IsPrincipal χ ∨ IsQuadratic χ := by
  rw [isReal_iff_sq_eq_one] at h
  by_cases h1 : χ = 1
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h⟩

end Classification

section PrimitiveCounting

/-- The number `φ*(q)` of primitive complex Dirichlet characters modulo `q`. -/
noncomputable def primitiveCharCount (q : ℕ) : ℕ :=
  Fintype.card {χ : DirichletCharacter ℂ q // χ.IsPrimitive}

/-- `primitiveCharCount 1 = 1`. -/
@[simp]
theorem primitiveCharCount_one : primitiveCharCount 1 = 1 := by
  have : Unique {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive} :=
    { default := ⟨1, DirichletCharacter.isPrimitive_one_level_one⟩
      uniq := fun ⟨χ, _⟩ ↦ Subtype.ext (DirichletCharacter.level_one χ) }
  simp [primitiveCharCount]

/-- Sum of `primitiveCharCount d` over divisors `d ∣ q` equals `q.totient` for `q > 0`. -/
theorem sum_divisors_primitiveCharCount {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors, primitiveCharCount d = q.totient := by
  have : NeZero q := ⟨hq.ne'⟩
  let S : ℕ → Finset (DirichletCharacter ℂ q) :=
    fun d ↦ Finset.univ.filter (fun χ ↦ χ.conductor = d)
  have hpart : (Finset.univ : Finset (DirichletCharacter ℂ q)) = q.divisors.biUnion S := by
    ext χ
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff, S]
    exact ⟨χ.conductor, Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq.ne'⟩, rfl⟩
  have hdisj : Set.PairwiseDisjoint (q.divisors : Set ℕ) S := by
    intro d₁ _ d₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro χ h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at h1 h2
    exact hne (h1.symm.trans h2)
  have hcard_S : ∀ d ∈ q.divisors, (S d).card = primitiveCharCount d := by
    intro d hd
    have hd_dvd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have : NeZero d := ⟨hd_pos.ne'⟩
    rw [primitiveCharCount, ← Finset.card_univ]
    symm
    refine Finset.card_bij
      (fun ψ _ ↦ DirichletCharacter.changeLevel hd_dvd ψ.1) ?_ ?_ ?_
    · intro ψ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
      rw [DirichletCharacter.conductor_changeLevel ψ.1 hd_dvd]
      exact ψ.2
    · intro ψ₁ _ ψ₂ _ h
      exact Subtype.ext (DirichletCharacter.changeLevel_injective hd_dvd h)
    · intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hχ
      let ψ₀ : DirichletCharacter ℂ d :=
        DirichletCharacter.changeLevel (dvd_of_eq hχ) χ.primitiveCharacter
      have hψ₀ : ψ₀.IsPrimitive := by
        rw [DirichletCharacter.isPrimitive_def,
          DirichletCharacter.conductor_changeLevel χ.primitiveCharacter (dvd_of_eq hχ)]
        exact hχ.symm ▸ (DirichletCharacter.isPrimitive_def _).mp χ.primitiveCharacter_isPrimitive
      refine ⟨⟨ψ₀, hψ₀⟩, Finset.mem_univ _, ?_⟩
      dsimp only [ψ₀]
      rw [← DirichletCharacter.changeLevel_trans, χ.changeLevel_primitiveCharacter]
  calc
    ∑ d ∈ q.divisors, primitiveCharCount d
        = ∑ d ∈ q.divisors, (S d).card := Finset.sum_congr rfl (fun d hd ↦ (hcard_S d hd).symm)
    _ = (q.divisors.biUnion S).card := (Finset.card_biUnion hdisj).symm
    _ = (Finset.univ : Finset (DirichletCharacter ℂ q)).card := by rw [← hpart]
    _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
    _ = q.totient := card_dirichletCharacter_eq_totient

/-- Möbius inversion formula for `primitiveCharCount q` (antidiagonal form):
`(primitiveCharCount q : ℤ) = ∑ x ∈ q.divisorsAntidiagonal, μ x.1 * (x.2.totient : ℤ)` for `q > 0`. -/
theorem primitiveCharCount_eq_sum_moebius_antidiagonal {q : ℕ} (hq : 0 < q) :
    (primitiveCharCount q : ℤ) =
      ∑ x ∈ q.divisorsAntidiagonal, μ x.1 * (x.2.totient : ℤ) := by
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n ↦ (primitiveCharCount n : ℤ))
    (g := fun n ↦ (n.totient : ℤ)) |>.mp (fun n hn ↦ by
      exact_mod_cast sum_divisors_primitiveCharCount hn)
  exact (h q hq).symm

/-- Möbius inversion formula for `primitiveCharCount q`:
`(primitiveCharCount q : ℤ) = ∑ d ∈ q.divisors, μ (q / d) * (d.totient : ℤ)` for `q > 0`. -/
theorem primitiveCharCount_eq_sum_moebius {q : ℕ} (hq : 0 < q) :
    (primitiveCharCount q : ℤ) =
      ∑ d ∈ q.divisors, μ (q / d) * (d.totient : ℤ) := by
  rw [primitiveCharCount_eq_sum_moebius_antidiagonal hq,
    Nat.sum_divisorsAntidiagonal' (f := fun x y ↦ μ x * (y.totient : ℤ))]

/-- Alternative Möbius inversion formula for `primitiveCharCount q`:
`(primitiveCharCount q : ℤ) = ∑ d ∈ q.divisors, μ d * ((q / d).totient : ℤ)` for `q > 0`. -/
theorem primitiveCharCount_eq_sum_moebius' {q : ℕ} (hq : 0 < q) :
    (primitiveCharCount q : ℤ) =
      ∑ d ∈ q.divisors, μ d * ((q / d).totient : ℤ) := by
  rw [primitiveCharCount_eq_sum_moebius_antidiagonal hq,
    Nat.sum_divisorsAntidiagonal (f := fun x y ↦ μ x * (y.totient : ℤ))]

/-- Arithmetic function `ℤ` realization of `totient`. -/
private def totientZ : ArithmeticFunction ℤ where
  toFun n := (n.totient : ℤ)
  map_zero' := by simp

private theorem isMultiplicative_totientZ : totientZ.IsMultiplicative :=
  ⟨by simp [totientZ], fun {m n} hmn ↦ by
    simp [totientZ, Nat.totient_mul hmn]⟩

private theorem primitiveCharCount_eq_moebius_mul_totientZ {q : ℕ} (hq : 0 < q) :
    (primitiveCharCount q : ℤ) = (μ * totientZ) q := by
  rw [primitiveCharCount_eq_sum_moebius_antidiagonal hq, ArithmeticFunction.mul_apply]
  rfl

/-- Multiplicativity of `primitiveCharCount`: if `m.Coprime n` and `m > 0`, `n > 0`, then
`primitiveCharCount (m * n) = primitiveCharCount m * primitiveCharCount n`. -/
theorem primitiveCharCount_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    primitiveCharCount (m * n) = primitiveCharCount m * primitiveCharCount n := by
  have hmult : (μ * totientZ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.mul isMultiplicative_totientZ
  have hZ : (primitiveCharCount (m * n) : ℤ) =
      (primitiveCharCount m : ℤ) * (primitiveCharCount n : ℤ) := by
    rw [primitiveCharCount_eq_moebius_mul_totientZ (Nat.mul_pos hm hn),
      primitiveCharCount_eq_moebius_mul_totientZ hm,
      primitiveCharCount_eq_moebius_mul_totientZ hn,
      hmult.map_mul_of_coprime hmn]
  exact_mod_cast hZ

/-- For a prime `p`, `primitiveCharCount p = p - 2`. -/
theorem primitiveCharCount_prime {p : ℕ} (hp : p.Prime) :
    primitiveCharCount p = p - 2 := by
  have hsum := sum_divisors_primitiveCharCount hp.pos
  rw [hp.divisors, Finset.sum_pair hp.ne_one.symm, primitiveCharCount_one, Nat.totient_prime hp] at hsum
  omega

/-- For a prime `p` and `k ≥ 0`, `primitiveCharCount (p ^ (k + 2)) = p ^ k * (p - 1) ^ 2`. -/
theorem primitiveCharCount_prime_pow_add_two {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primitiveCharCount (p ^ (k + 2)) = p ^ k * (p - 1) ^ 2 := by
  have h1 := sum_divisors_primitiveCharCount (pow_pos hp.pos (k + 1))
  have h2 := sum_divisors_primitiveCharCount (pow_pos hp.pos (k + 2))
  rw [Nat.divisors_prime_pow hp, Finset.sum_map] at h1 h2
  simp only [Function.Embedding.coeFn_mk] at h1 h2
  rw [Finset.sum_range_succ, h1] at h2
  rw [Nat.totient_prime_pow hp (Nat.succ_pos k),
    Nat.totient_prime_pow hp (Nat.succ_pos (k + 1))] at h2
  simp only [Nat.succ_sub_one] at h2
  have hp1 : 1 ≤ p := hp.one_lt.le
  have heq : primitiveCharCount (p ^ (k + 2)) = p ^ (k + 1) * (p - 1) - p ^ k * (p - 1) := by
    omega
  rw [heq, pow_succ]
  calc
    p ^ k * p * (p - 1) - p ^ k * (p - 1)
        = p ^ k * (p - 1) * p - p ^ k * (p - 1) * 1 := by ring
    _ = p ^ k * (p - 1) * (p - 1) := by rw [← Nat.mul_sub_left_distrib]
    _ = p ^ k * (p - 1) ^ 2 := by ring

/-- Exact prime-power formula for `primitiveCharCount (p ^ k)`. -/
theorem primitiveCharCount_prime_pow {p : ℕ} (hp : p.Prime) : ∀ k : ℕ,
    primitiveCharCount (p ^ k) =
      if k = 0 then 1 else if k = 1 then p - 2 else p ^ (k - 2) * (p - 1) ^ 2
  | 0 => by simp
  | 1 => by simp [primitiveCharCount_prime hp]
  | k + 2 => by simp [primitiveCharCount_prime_pow_add_two hp k]

/-- `primitiveCharCount 2 = 0` (there are no primitive characters modulo `2`). -/
@[simp]
theorem primitiveCharCount_two : primitiveCharCount 2 = 0 := by
  simpa using primitiveCharCount_prime Nat.prime_two

/-- For `q > 0`, `primitiveCharCount q = 0` if and only if `q % 4 = 2` (equivalently `2 ∣ q ∧ ¬ 4 ∣ q`). -/
theorem primitiveCharCount_eq_zero_iff {q : ℕ} (hq : 0 < q) :
    primitiveCharCount q = 0 ↔ q % 4 = 2 := by
  have hmain : ∀ n : ℕ, 0 < n → (primitiveCharCount n = 0 ↔ n % 4 = 2) := by
    intro n hn
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rcases eq_or_ne n 1 with rfl | hn1
      · simp
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      let k := n.factorization p
      have hk_pos : 0 < k := Nat.Prime.factorization_pos_of_dvd hp hn.ne' hpdvd
      let m := n / p ^ k
      have hm_pos : 0 < m := Nat.ordCompl_pos p hn.ne'
      have hcop : (p ^ k).Coprime m := (Nat.coprime_ordCompl hp hn.ne').pow_left k
      have hn_eq : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hmul : primitiveCharCount n = primitiveCharCount (p ^ k) * primitiveCharCount m := by
        rw [hn_eq]
        exact primitiveCharCount_mul (pow_pos hp.pos k) hm_pos hcop
      have hmlt : m < n := by
        have hpk_gt1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt hk_pos.ne'
        rw [hn_eq]
        exact lt_mul_of_one_lt_left hm_pos hpk_gt1
      have ihm := (ih m hmlt hm_pos)
      rw [hmul, mul_eq_zero, ihm]
      by_cases hp2 : p = 2
      · subst hp2
        have hm_odd : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
        have hm_mod : m % 2 = 1 := Nat.two_dvd_ne_zero.mp hm_odd
        have hm_mod4 : m % 4 ≠ 2 := by omega
        rcases Nat.lt_trichotomy k 2 with hk1 | hk2 | hkgt
        · have hk_eq : k = 1 := by omega
          rw [hk_eq, pow_one, primitiveCharCount_two]
          simp only [true_or, true_iff]
          rw [hn_eq, hk_eq, pow_one]
          omega
        · rw [hk2, primitiveCharCount_prime_pow_add_two Nat.prime_two 0]
          simp [hm_mod4]
          rw [hn_eq, hk2]
          norm_num [Nat.mul_mod]
        · obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_lt hkgt)
          have hk_eq : k = k' + 2 := by omega
          have hnz : primitiveCharCount (2 ^ (k' + 2)) ≠ 0 := by
            rw [primitiveCharCount_prime_pow_add_two Nat.prime_two k']
            positivity
          rw [hk_eq]
          simp only [hnz, false_or, hm_mod4, false_iff]
          rw [hn_eq, hk_eq, pow_add]
          norm_num [Nat.mul_mod]
      · have hp3 : 3 ≤ p := by
          have := hp.two_le
          omega
        have hpk_nz : primitiveCharCount (p ^ k) ≠ 0 := by
          rw [primitiveCharCount_prime_pow hp k]
          split_ifs with h0 h1
          · exact one_ne_zero
          · omega
          · have : 0 < p ^ (k - 2) * (p - 1) ^ 2 := by
              refine mul_pos (pow_pos hp.pos _) (pow_pos (by omega) 2)
            exact this.ne'
        have hp_odd : p % 2 = 1 := by
          rcases Nat.even_or_odd p with hev | hodd
          · have h2p : 2 ∣ p := even_iff_two_dvd.mp hev
            exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm hp2
          · exact Nat.odd_iff.mp hodd
        have hpk_odd : (p ^ k) % 2 = 1 := by
          have : Odd (p ^ k) := (Nat.odd_iff.mpr hp_odd).pow
          exact Nat.odd_iff.mp this
        simp only [hpk_nz, false_or]
        have hpk4 : p ^ k % 4 = 1 ∨ p ^ k % 4 = 3 := by omega
        have hn_mod4 : n % 4 = ((p ^ k % 4) * (m % 4)) % 4 := by
          rw [hn_eq, Nat.mul_mod]
        have hm4_cases : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
        rcases hpk4 with hpk | hpk <;> rcases hm4_cases with hm | hm | hm | hm <;>
          simp [hn_mod4, hpk, hm]
  exact hmain q hq

end PrimitiveCounting

end AnalyticNumberTheory.DirichletLFunctions
