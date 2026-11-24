import AnalyticNumberTheory.DirichletLFunctions.Characters
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic density of the invertible residue classes

The diagonal of the second moment of a Dirichlet L-function at the critical
line sums `‖χ(n)‖²/n`. In each block of `q` terms exactly `φ(q)` of the
weights are one. Summation by parts yields a bounded harmonic discrepancy.
-/

open Finset

namespace AnalyticNumberTheory.DirichletLFunctions

private theorem sum_reciprocal_weight_le {b : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, |∑ i ∈ range N, b (i+1)| ≤ B) (N : ℕ) :
    |∑ i ∈ range N, b (i+1)/(i+1:ℕ)| ≤ B := by
  let S (k : ℕ) := ∑ i ∈ range k, b (i+1)
  let F (k : ℕ) := ∑ i ∈ range k, b (i+1)/(i+1:ℕ)
  have hS (k : ℕ) : S (k+1) = S k+b (k+1) := sum_range_succ ..
  have hF (k : ℕ) : F (k+1) = F k+b (k+1)/(k+1:ℕ) := sum_range_succ ..
  have H (k : ℕ) : |F k - S k/(k+1:ℕ)| ≤ B*(1-((k+1:ℕ):ℝ)⁻¹) := by
    induction k with
    | zero => simp [F,S]
    | succ k ih =>
      let a : ℝ := ((k+1:ℕ):ℝ)⁻¹
      let d : ℝ := ((k+1+1:ℕ):ℝ)⁻¹
      have had : d ≤ a := inv_anti₀ (by positivity : 0 < ((k+1:ℕ):ℝ)) (by norm_num)
      have he : F (k+1)-S (k+1)/(k+1+1:ℕ) = (F k-S k/(k+1:ℕ))+S (k+1)*(a-d) := by
        rw [hF,hS]; dsimp [a,d]; ring
      rw [he]
      apply (abs_add_le ..).trans
      rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr had)]
      apply (add_le_add ih (mul_le_mul_of_nonneg_right (hb (k+1)) (sub_nonneg.mpr had))).trans_eq
      dsimp [a,d]; ring
  have he : F N = (F N-S N/(N+1:ℕ))+S N/(N+1:ℕ) := by ring
  change |F N| ≤ B
  rw [he]
  apply (abs_add_le ..).trans
  rw [abs_div,abs_of_pos (by positivity : 0 < ((N+1:ℕ):ℝ))]
  apply (add_le_add (H N) (div_le_div_of_nonneg_right (hb N) (by positivity))).trans_eq
  ring

/-- The squared absolute values over any complete period sum to the totient. -/
theorem sum_shift_norm_char_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (M : ℕ) :
    ∑ n ∈ range q, ‖χ ((M+n:ℕ):ZMod q)‖^2 = (q.totient:ℝ) := by
  have h := sum_shift_range_eq (1 : DirichletCharacter ℂ q) M
  have hterm (n : ℕ) : ‖χ (n:ZMod q)‖^2 = ((1 : DirichletCharacter ℂ q) (n:ZMod q)).re := by
    by_cases h : n.Coprime q
    · simp [norm_char_eq_one_of_coprime χ h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h)]
    · simp [(char_nat_eq_zero_iff_not_coprime χ n).mpr h,
        (char_nat_eq_zero_iff_not_coprime (1 : DirichletCharacter ℂ q) n).mpr h]
  simpa only [hterm, ← Complex.re_sum,ite_true,Complex.natCast_re] using congrArg Complex.re h

/-- Average squared amplitude over one residue period. -/
noncomputable def periodicNormMean {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) : ℝ :=
  (∑ r : ZMod q, ‖Φ r‖^2)/q

private theorem sum_shift_periodic_sq {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (M : ℕ) :
    ∑ n ∈ range q, ‖Φ ((M+n:ℕ):ZMod q)‖^2 = ∑ r : ZMod q, ‖Φ r‖^2 := by
  have h : ∑ r : ZMod q, ‖Φ ((M:ZMod q)+r)‖^2 = ∑ n ∈ range q, ‖Φ ((M+n:ℕ):ZMod q)‖^2 := by
    refine sum_bij (fun r _ => r.val) (fun r _ => mem_range.mpr (ZMod.val_lt r))
      (fun _ _ _ _ h => ZMod.val_injective q h) ?_ ?_
    · intro n hn
      exact ⟨n,mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hn)⟩
    · intro r _
      simp
  exact h.symm.trans (Equiv.sum_comp (Equiv.addLeft (M:ZMod q)) (fun r => ‖Φ r‖^2))

theorem periodicNormMean_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    periodicNormMean χ = (q.totient:ℝ)/q := by
  rw [periodicNormMean,← sum_shift_periodic_sq _ 0,sum_shift_norm_char_sq]

/-- A bounded periodic sequence has harmonic diagonal equal to its
period mean times the harmonic sum, up to an error at most the period. -/
theorem abs_periodic_harmonic_sub_mean_le {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ)
    (hΦ : ∀ r, ‖Φ r‖ ≤ 1) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, ‖Φ (n:ZMod q)‖^2/(n:ℝ)) -
      periodicNormMean Φ*(harmonic N:ℝ)| ≤ q := by
  let c := periodicNormMean Φ
  let b (n : ℕ) := ‖Φ (n:ZMod q)‖^2-c
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hc : 0 ≤ c := by dsimp [c,periodicNormMean]; positivity
  have hc1 : c ≤ 1 := by
    apply (div_le_one hq).mpr
    calc _ ≤ ∑ _r : ZMod q, (1:ℝ) := sum_le_sum (fun r _ => by simpa using pow_le_pow_left₀ (norm_nonneg _) (hΦ r) 2)
         _ = _ := by simp
  have hb (n : ℕ) : |b n| ≤ 1 := by
    have h := hΦ (n:ZMod q)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [abs_le]; dsimp [b]; constructor <;> nlinarith [sq_nonneg ‖Φ (n:ZMod q)‖]
  let S (M : ℕ) := ∑ i ∈ range M, b (i+1)
  have hper (M : ℕ) : S (M+q) = S M := by
    dsimp only [S]
    rw [sum_range_add]
    change _ + _ = _
    rw [add_eq_left]
    simp only [b, sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    simp_rw [show ∀ j : ℕ, M+j+1=M+1+j by intro; omega]
    rw [sum_shift_periodic_sq]
    dsimp only [c,periodicNormMean]
    field_simp <;> ring
  have hs (M : ℕ) : |S M| ≤ q := by
    induction M using Nat.strong_induction_on with
    | ind M ih =>
      by_cases h : M < q
      · apply (Finset.abs_sum_le_sum_abs ..).trans
        apply (sum_le_sum fun i _ => hb (i+1)).trans
        simpa using (show (M:ℝ) ≤ q by exact_mod_cast h.le)
      · rw [show M = M-q+q by omega,hper]
        exact ih (M-q) (by have := NeZero.pos q; omega)
  have hh := sum_reciprocal_weight_le hq.le hs N
  let G (k : ℕ) := (∑ n ∈ Icc 1 k, ‖Φ (n:ZMod q)‖^2/(n:ℝ))-c*(harmonic k:ℝ)
  have he (k : ℕ) : G k = ∑ i ∈ range k, b (i+1)/(i+1:ℕ) := by
    induction k with
    | zero => simp [G]
    | succ k ih =>
      rw [sum_range_succ,← ih]
      simp only [G,sum_Icc_succ_top (by omega : 1 ≤ k+1),harmonic_succ,Rat.cast_add,
        Rat.cast_inv,Rat.cast_natCast,b]
      push_cast
      ring
  change |G N| ≤ q
  rwa [he]

/-- For a character the coefficient of the harmonic diagonal is `φ(q)/q`. -/
theorem abs_char_harmonic_sub_mean_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, ‖χ (n:ZMod q)‖^2/(n:ℝ)) -
      (q.totient:ℝ)/q*(harmonic N:ℝ)| ≤ q := by
  simpa only [periodicNormMean_char] using abs_periodic_harmonic_sub_mean_le χ (norm_char_le_one χ) N

end AnalyticNumberTheory.DirichletLFunctions
