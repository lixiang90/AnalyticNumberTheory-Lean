import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovBilinear
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions
import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation
import AnalyticNumberTheory.ExponentialSums.VaughanIdentity

/-!
# Type I sums in Vaughan's identity for Dirichlet characters

After separating the factor with small index, one only needs the cancellation
of a nonprincipal character on complete periods. Abel summation gives the
corresponding estimate with one logarithmic weight.
-/

noncomputable section

open Finset
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.PrimeDistribution

/-- Abel summation bounds a logarithmically weighted character sum by twice the
modulus times the logarithm of the cutoff. -/
theorem norm_sum_log_char_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ m ∈ Icc 1 M, χ m * (Real.log m : ℂ)‖ ≤ 2 * q * Real.log M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have h := abel_discrete_Icc_one (fun m => χ m) (fun m => (Real.log m : ℂ)) M
  rw [h]
  have htop : ‖(∑ m ∈ Icc 1 M, χ m) * (Real.log M : ℂ)‖ ≤ q * Real.log M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_sum_Icc_char_le_modulus hχ M) (Real.log_natCast_nonneg _)
  have hrest : ‖∑ m ∈ Ico 1 M, (∑ j ∈ Icc 1 m, χ j) *
      ((Real.log (m+1 : ℕ) : ℂ) - (Real.log m : ℂ))‖ ≤ q * Real.log M := by
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑ m ∈ Ico 1 M, (q : ℝ) * (Real.log (m+1 : ℕ) - Real.log m) := by
             apply sum_le_sum
             intro m hm
             have hpos : (0 : ℝ) < m := by exact_mod_cast (mem_Ico.mp hm).1
             have hd : 0 ≤ Real.log (m+1 : ℕ) - Real.log m :=
               sub_nonneg.mpr (Real.log_le_log hpos (by exact_mod_cast Nat.le_succ m))
             rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
             exact mul_le_mul_of_nonneg_right (norm_sum_Icc_char_le_modulus hχ m) hd
         _ = _ := by
           rw [← mul_sum]
           congr 1
           clear h htop
           induction M, hM using Nat.le_induction with
           | base => simp
           | succ m hm ih => rw [sum_Ico_succ_top hm, ih]; ring
  exact (norm_sub_le ..).trans (by linarith)

private theorem norm_log_char_block {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (d M : ℕ) :
    ‖∑ m ∈ Icc 1 M, (Real.log m : ℂ) * χ (d * m : ℕ)‖ ≤ 2 * q * Real.log M := by
  have heq : (∑ m ∈ Icc 1 M, (Real.log m : ℂ) * χ (d*m : ℕ)) =
      χ d * ∑ m ∈ Icc 1 M, χ m * (Real.log m : ℂ) := by
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by rw [Nat.cast_mul, map_mul]; ring
  rw [heq, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (norm_sum_log_char_le hχ M)

private theorem norm_char_block {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (d M : ℕ) : ‖∑ m ∈ Icc 1 M, χ (d*m : ℕ)‖ ≤ q := by
  simp_rw [Nat.cast_mul, map_mul, ← mul_sum]
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (norm_sum_Icc_char_le_modulus hχ M)

/-- The last term in Vaughan's identity is precisely the bilinear polynomial
with row-dependent cutoff `⌊x⌋/m`. -/
theorem vaughan_char_typeII_eq (X U q : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ m ∈ Ioc U (X / U), (vaughanTypeIICoeff U m : ℂ) *
      ∑ n ∈ Ioc U (X / m), (Λ n : ℂ) * χ (m*n : ℕ)) =
    cutoffCharacterBilinear (Ioc U (X / U)) (Ioc U X) (fun m => (vaughanTypeIICoeff U m : ℂ))
      (fun n => (Λ n : ℂ)) (fun m => X / m) q χ := by
  unfold cutoffCharacterBilinear characterPolynomial
  refine sum_congr rfl fun m _ => ?_
  have hs : (Ioc U X).filter (· ≤ X / m) = Ioc U (X / m) := by
    ext n; simp only [mem_filter, mem_Ioc]; have := Nat.div_le_self X m; omega
  rw [hs, mul_sum, mul_sum]
  exact sum_congr rfl fun n _ => by rw [Nat.cast_mul, map_mul]; ring


private theorem norm_sum_initial_le (M : ℕ) (f : ℕ → ℂ) {B : ℝ}
    (h : ∀ m ∈ Icc 1 M, ‖f m‖ ≤ B) : ‖∑ m ∈ Icc 1 M, f m‖ ≤ M * B := by
  calc _ ≤ ∑ m ∈ Icc 1 M, ‖f m‖ := norm_sum_le ..
       _ ≤ ∑ _m ∈ Icc 1 M, B := sum_le_sum h
       _ = _ := by simp [Nat.card_Icc]

set_option maxHeartbeats 1200000 in
/-- Removing the Type II polynomial from the character-twisted Chebyshev sum
leaves three short Type I sums, uniformly bounded for every nonprincipal character. -/
theorem norm_psiChar_sub_vaughanTypeII_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {U : ℕ} (hU : 1 ≤ U) {x : ℝ} (hx : 2 ≤ x) :
    ‖psiChar x χ - cutoffCharacterBilinear (Ioc U (⌊x⌋₊ / U)) (Ioc U ⌊x⌋₊)
      (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun n => (Λ n : ℂ)) (fun m => ⌊x⌋₊ / m) q χ‖ ≤
      4 * q * (U : ℝ)^2 * Real.log x := by
  let X := ⌊x⌋₊
  let L := Real.log x
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hx' : (X : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hUsq : (U : ℝ) ≤ (U : ℝ)^2 := by nlinarith [mul_nonneg (show (0 : ℝ) ≤ U by positivity) (sub_nonneg.mpr hU1)]
  have log_le (m : ℕ) (hm : m ≤ X) : Real.log m ≤ L := by
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · simpa using hL
    exact Real.log_le_log (Nat.cast_pos.mpr hp) ((Nat.cast_le.mpr hm).trans hx')
  let a := ∑ n ∈ Icc 1 (min X U), (Λ n : ℂ) * χ n
  let b := ∑ d ∈ Icc 1 U, (μ d : ℂ) * ∑ m ∈ Icc 1 (X/d), (Real.log m : ℂ) * χ (d*m : ℕ)
  let g := ∑ d ∈ Icc 1 (U*U), (vaughanTypeICoeff U U d : ℂ) * ∑ m ∈ Icc 1 (X/d), χ (d*m : ℕ)
  have ha : ‖a‖ ≤ (U : ℝ) * L := by
    apply (norm_sum_initial_le (min X U) _ (B := L) ?_).trans
    · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_right ..)) hL
    intro n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
      (ArithmeticFunction.vonMangoldt_le_log.trans (log_le n ((mem_Icc.mp hn).2.trans (min_le_left ..))))
  have hb : ‖b‖ ≤ (U : ℝ) * (2 * q * L) := by
    apply norm_sum_initial_le
    intro d _
    have hmu : ‖(μ d : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hmu).trans
    exact (norm_log_char_block hχ d (X/d)).trans
      (mul_le_mul_of_nonneg_left (log_le _ (Nat.div_le_self ..)) (by positivity))
  have hg : ‖g‖ ≤ (U : ℝ)^2 * (q * L) := by
    rw [pow_two, ← Nat.cast_mul]
    apply norm_sum_initial_le
    intro d _
    by_cases hd : d ≤ X
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm (q : ℝ) L]
      exact mul_le_mul ((abs_vaughanTypeICoeff_le_log U U d).trans (log_le d hd))
        (norm_char_block hχ d (X/d)) (norm_nonneg _) hL
    · simp [Nat.div_eq_of_lt (lt_of_not_ge hd), mul_nonneg (Nat.cast_nonneg q) hL]
  have hid := vaughan_identity_sum x (U := U) hU (fun n => χ n)
  rw [vaughan_char_typeII_eq] at hid
  have hpsi : psiChar x χ = ∑ n ∈ Icc 1 X, (Λ n : ℂ) * χ n := by
    unfold psiChar
    exact sum_congr rfl fun _ _ => mul_comm ..
  rw [hpsi, hid, add_sub_cancel_right]
  change ‖a+b-g‖ ≤ _
  have hbig : (U : ℝ) * L ≤ (U : ℝ)^2 * (q * L) := by
    exact mul_le_mul hUsq (le_mul_of_one_le_left hL hq1) hL (by positivity)
  calc ‖a+b-g‖ ≤ (‖a‖ + ‖b‖) + ‖g‖ :=
           (norm_sub_le ..).trans (add_le_add (norm_add_le a b) le_rfl)
       _ ≤ ((U : ℝ)^2 * (q * L) + (U : ℝ)^2 * (2 * q * L)) + (U : ℝ)^2 * (q * L) :=
           add_le_add (add_le_add (ha.trans hbig)
             (hb.trans (mul_le_mul_of_nonneg_right hUsq (by positivity)))) hg
       _ = _ := by dsimp [L]; ring


/-- The Type I contribution to the primitive-character mean over `D < q ≤ Q`.
The reciprocal totient cancels the size of each character group. -/
theorem sum_primitive_psiChar_sub_vaughanTypeII_le {D Q U : ℕ} (hD : 1 ≤ D) (hU : 1 ≤ U)
    {x : ℝ} (hx : 2 ≤ x) :
    ∑ q ∈ Ioc D Q, (q.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖psiChar x χ - cutoffCharacterBilinear (Ioc U (⌊x⌋₊ / U)) (Ioc U ⌊x⌋₊)
          (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun n => (Λ n : ℂ)) (fun m => ⌊x⌋₊ / m) q χ‖ ≤
      4 * (Q : ℝ)^2 * (U : ℝ)^2 * Real.log x := by
  let E := 4 * (Q : ℝ) * (U : ℝ)^2 * Real.log x
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he (q : ℕ) (hq : q ∈ Ioc D Q) :
      (q.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖psiChar x χ - cutoffCharacterBilinear (Ioc U (⌊x⌋₊ / U)) (Ioc U ⌊x⌋₊)
          (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun n => (Λ n : ℂ)) (fun m => ⌊x⌋₊ / m) q χ‖ ≤ E := by
    have hq' := mem_Ioc.mp hq
    have : NeZero q := ⟨by omega⟩
    let F := (univ : Finset (DirichletCharacter ℂ q)).filter fun χ => χ.IsPrimitive
    have hc : F.card ≤ q.totient := by
      have hh := card_le_univ F
      rwa [Fintype.card_eq_nat_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity] at hh
    rw [inv_mul_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega)))]
    apply (le_trans (b := ∑ _χ ∈ F, E) (sum_le_sum ?_) ?_)
    · intro χ hχ
      have hprim := (mem_filter.mp hχ).2
      have hne : χ ≠ 1 := by
        intro h1
        have hc : χ.conductor = q := hprim
        rw [h1, DirichletCharacter.conductor_one] at hc
        omega
      apply (norm_psiChar_sub_vaughanTypeII_le hne hU hx).trans
      dsimp [E]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hq'.2) (by norm_num)) (sq_nonneg _)) hlogx
    · simpa only [sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) hE
  calc _ ≤ ∑ _q ∈ Ioc D Q, E := sum_le_sum he
       _ ≤ (Q : ℝ) * E := by
         simp only [sum_const, nsmul_eq_mul]
         exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simp [Nat.card_Ioc])) hE
       _ = _ := by dsimp [E]; ring

end AnalyticNumberTheory.PrimeDistribution
