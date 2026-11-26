import AnalyticNumberTheory.AdditiveNumberTheory.PageCharacterExpansion

/-! # Character expansion of a rational additive phase with a real shift -/

noncomputable section

open Finset AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.PrimeDistribution
open scoped Classical ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Inverse finite Fourier transform of a rational additive phase on the
reduced residues. Extension by zero covers every integer index. -/
theorem sum_rationalCharacterCoefficient_mul_char {q : ℕ} [NeZero q] (a n : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, rationalCharacterCoefficient χ a*χ n) =
      if n.Coprime q then e (((a : ℝ)/q)*n) else 0 := by
  let R := coprimeResidues q
  let E (r : ℕ) := e ((r : ℝ)*a/q)
  have hφ : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  calc _ = ∑ r ∈ R, (q.totient : ℂ)⁻¹ * (∑ χ : DirichletCharacter ℂ q, χ n*star (χ r)) * E r := by
           unfold rationalCharacterCoefficient
           simp_rw [mul_sum, sum_mul]
           rw [sum_comm]
           apply sum_congr rfl
           intro r _
           apply sum_congr rfl
           intro χ _
           ring
       _ = ∑ r ∈ R, if n%q = r then E r else 0 := by
           apply sum_congr rfl
           intro r hr
           obtain ⟨hrq, hr'⟩ := mem_filter.mp hr
           rw [sum_chars_nat_mul_conj_eq n hr']
           have he : n ≡ r [MOD q] ↔ n%q = r := by
             rw [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hrq)]
           by_cases hn : n ≡ r [MOD q]
           · rw [if_pos hn, if_pos (he.mp hn), inv_mul_cancel₀ hφ, one_mul]
           · rw [if_neg hn, if_neg (fun h => hn (he.mpr h)), mul_zero, zero_mul]
       _ = _ := by
           have hm : n%q ∈ R ↔ n.Coprime q := by
             simp only [R, coprimeResidues, mem_filter, mem_range, Nat.mod_lt n (NeZero.pos q),
               true_and, ZMod.coprime_mod_iff_coprime]
           have he := e_rat_mul_eq_mod (a : ℤ) (NeZero.pos q) n
           push_cast at he
           simp [hm, E, ← he]

/-- A real frequency shift does not increase the error from the prime
powers dividing q. This includes q = 1 and both signs of the shift. -/
theorem norm_primeExpSum_shift_sub_character_expansion {x : ℝ} (hx : 1 ≤ x)
    {q : ℕ} [NeZero q] (a : ℕ) (z : ℝ) :
    ‖primeExpSum x ((a : ℝ)/q+z) - ∑ χ : DirichletCharacter ℂ q,
      rationalCharacterCoefficient χ a*characterPrimeSum χ ⌊x⌋₊ z‖ ≤
      (Real.log q/Real.log 2)*Real.log x := by
  let A := Icc 1 ⌊x⌋₊
  let G (χ : DirichletCharacter ℂ q) := rationalCharacterCoefficient χ a
  have hex : (∑ χ : DirichletCharacter ℂ q, G χ*characterPrimeSum χ ⌊x⌋₊ z) =
      ∑ n ∈ A, (∑ χ : DirichletCharacter ℂ q, G χ*χ n)*(Λ n : ℂ)*e (z*n) := by
    unfold characterPrimeSum expSum
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro χ _
    ring
  have hram := norm_psi_sub_psiChar_one_le hx (NeZero.pos q)
  rw [psiChar_one_eq_psi_sub, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))] at hram
  change ‖primeExpSum x ((a : ℝ)/q+z) - ∑ χ : DirichletCharacter ℂ q,
    G χ*characterPrimeSum χ ⌊x⌋₊ z‖ ≤ _
  rw [hex]
  change ‖(∑ n ∈ A, (Λ n : ℂ)*e (((a : ℝ)/q+z)*n)) - _‖ ≤ _
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply le_trans _ hram
  rw [sum_filter]
  apply sum_le_sum
  intro n _
  dsimp only [G]
  rw [sum_rationalCharacterCoefficient_mul_char, add_mul, e_add]
  by_cases hn : n.Coprime q
  · simp [hn, mul_comm, mul_assoc]
    rw [ite_eq_left hn, sub_self]
  · simp [hn, norm_mul, norm_e, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

end AnalyticNumberTheory.AdditiveNumberTheory
