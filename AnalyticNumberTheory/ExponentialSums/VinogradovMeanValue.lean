import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-!
# Vinogradov Mean Value, Hua's Lemma, and Complete Exponential Sums

This file develops multi-dimensional Vinogradov mean values, Hua's lemma, and bounds for complete
polynomial exponential sums modulo `q`:

- `torusIntegral`, `torusIntegralC`, `vinogradovF`, `vinogradovJ`, `vinogradovSolutionCount`, and
  the exact Diophantine solution-count identity `vinogradovJ_eq_card_solutions`.
- `hua_lemma_step` and `hua_lemma`: the `2^k`-th moment estimate on `[0, 1]` for degree-`k`
  Weyl sums `∑_{1 ≤ n ≤ N} exp (2πi α n^k)`, proved by induction via `j`-fold Weyl differencing
  and the elementary divisor bound.
- `completeExpSum`, `completeExpSum_mul_coprime` (Chinese Remainder Theorem multiplicativity),
  `completeExpSum_quadratic_bound`, `completeExpSum_prime_bound`,
  `completeExpSum_prime_pow_intermediate`, `completeExpSum_prime_pow_reduction`, and the sharp
  general bounds `completeExpSum_bound` and `completeExpSum_bound_rpow`.
-/

noncomputable section

open Complex Finset
open scoped BigOperators

namespace AnalyticNumberTheory.ExponentialSums

/-! ## Private additive character and elementary divisor helper -/

private def vmvE (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * α * Complex.I)

private lemma vmvE_zero : vmvE 0 = 1 := by
  simp [vmvE]

private lemma vmvE_add (α β : ℝ) : vmvE (α + β) = vmvE α * vmvE β := by
  simp only [vmvE, Complex.ofReal_add]
  rw [← Complex.exp_add]
  congr 1
  ring

private lemma vmvE_sub (α β : ℝ) : vmvE (α - β) = vmvE α * vmvE (-β) := by
  simpa [sub_eq_add_neg] using vmvE_add α (-β)

private lemma vmvE_neg (α : ℝ) : vmvE (-α) = (vmvE α)⁻¹ := by
  simp only [vmvE, Complex.ofReal_neg, ← Complex.exp_neg]
  congr 1
  ring

private lemma star_vmvE (α : ℝ) : star (vmvE α) = vmvE (-α) := by
  simp only [vmvE, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
  ring

private lemma vmv_norm_sq_eq_mul_star (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, RCLike.mul_conj]
  push_cast
  rfl

private lemma vmv_succ_le_two_pow (j : ℕ) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ m ih => rw [pow_succ']; omega

private lemma prod_const_le_of_subset_of_one_le {α : Type*} {s t : Finset α} {B : ℝ}
    (hst : s ⊆ t) (hB : 1 ≤ B) :
    (∏ _a ∈ s, B) ≤ ∏ _a ∈ t, B := by
  simp only [Finset.prod_const]
  exact pow_le_pow_right₀ hB (Finset.card_le_card hst)

private lemma vmv_intervalIntegral_re {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    ∫ x in (0 : ℝ)..1, (f x).re = (∫ x in (0 : ℝ)..1, f x).re :=
  intervalIntegral.intervalIntegral_re hf

private lemma norm_vmvE (α : ℝ) : ‖vmvE α‖ = 1 := by
  rw [vmvE]
  have hre : (2 * Real.pi * (α : ℂ) * Complex.I).re = 0 := by
    simp [mul_assoc]
  rw [Complex.norm_exp, hre, Real.exp_zero]

private lemma continuous_vmvE : Continuous vmvE := by
  unfold vmvE
  fun_prop

private lemma vmvE_int_eq_one (m : ℤ) : vmvE (m : ℝ) = 1 := by
  rw [vmvE]
  have h : (2 : ℂ) * Real.pi * ((m : ℝ) : ℂ) * Complex.I =
      (m : ℤ) * (2 * Real.pi * Complex.I) := by
    simp only [Complex.ofReal_intCast]
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I m

private lemma vmvE_eq_of_int_sub {α β : ℝ} {m : ℤ} (h : α - β = m) : vmvE α = vmvE β := by
  have hα : α = β + m := by linarith
  rw [hα, vmvE_add, vmvE_int_eq_one, mul_one]

private lemma vmvE_pow_nat (α : ℝ) (n : ℕ) : (vmvE α) ^ n = vmvE (α * n) := by
  simp only [vmvE, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma intervalIntegral_vmvE_int (m : ℤ) :
    ∫ t in (0 : ℝ)..1, vmvE ((m : ℝ) * t) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm
    simp [vmvE_zero]
  · let c : ℂ := 2 * Real.pi * (m : ℝ) * Complex.I
    have hc : c ≠ 0 := by
      simp only [c, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
        Real.pi_ne_zero, Int.cast_eq_zero, hm, Complex.I_ne_zero, or_self, not_false_eq_true]
    have hrew : (fun t : ℝ => vmvE ((m : ℝ) * t)) = fun t : ℝ => Complex.exp (c * t) := by
      ext t
      simp only [vmvE, c, Complex.ofReal_mul]
      congr 1
      ring
    rw [hrew, integral_exp_mul_complex hc]
    have h1 : Complex.exp (c * (1 : ℝ)) = 1 := by
      simp only [c, Complex.ofReal_one, mul_one]
      exact vmvE_int_eq_one m
    have h0 : Complex.exp (c * (0 : ℝ)) = 1 := by
      simp [c]
    rw [h1, h0, sub_self, zero_div]

private lemma vmvE_eq_one_iff_int (α : ℝ) : vmvE α = 1 ↔ ∃ m : ℤ, α = m := by
  constructor
  · intro h
    rw [vmvE, Complex.exp_eq_one_iff] at h
    rcases h with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have him := congrArg Complex.im hm
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hre : 2 * Real.pi * α = m * (2 * Real.pi) := by
      simpa [mul_assoc, Complex.ofReal_mul, Complex.mul_im] using him
    exact mul_left_cancel₀ h2pi (by linarith)
  · rintro ⟨m, rfl⟩
    exact vmvE_int_eq_one m

private lemma completeExpSum_linear_int_eq (q : ℕ) (hq : 1 ≤ q) (c : ℤ) :
    ∑ x ∈ Finset.range q, vmvE ((c : ℝ) * (x : ℝ) / q) =
      if (q : ℤ) ∣ c then (q : ℂ) else 0 := by
  have hrew : ∀ x : ℕ, vmvE ((c : ℝ) * (x : ℝ) / q) = (vmvE ((c : ℝ) / q)) ^ x := by
    intro x
    rw [vmvE_pow_nat]
    congr 1
    ring
  simp_rw [hrew]
  split_ifs with hdvd
  · rcases hdvd with ⟨m, hm⟩
    have hz : vmvE ((c : ℝ) / q) = 1 := by
      refine (vmvE_eq_one_iff_int _).mpr ⟨m, ?_⟩
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have hc : (c : ℝ) = (q : ℝ) * (m : ℝ) := by exact_mod_cast hm
      rw [hc]
      field_simp [hq0]
    simp [hz]
  · have hz1 : vmvE ((c : ℝ) / q) ≠ 1 := by
      intro hz
      rcases (vmvE_eq_one_iff_int _).mp hz with ⟨m, hm⟩
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have hc : (c : ℝ) = (q : ℝ) * (m : ℝ) := (div_eq_iff hq0).mp hm |>.trans (mul_comm _ _)
      have hci : c = (q : ℤ) * m := by exact_mod_cast hc
      exact hdvd ⟨m, hci⟩
    rw [geom_sum_eq hz1 q, vmvE_pow_nat]
    have hzq : vmvE ((c : ℝ) / q * (q : ℝ)) = 1 := by
      refine (vmvE_eq_one_iff_int _).mpr ⟨c, ?_⟩
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      field_simp [hq0]
    rw [hzq, sub_self, zero_div]

private lemma vmv_nat_add_one_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      rw [pow_succ']
      omega

private lemma vmv_prime_pow_divisors_le_of_large {δ : ℝ} (_hδ : 0 < δ) {p : ℕ}
    (hp2 : (2 : ℝ) ≤ (p : ℝ) ^ δ) (a : ℕ) :
    ((a + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (a * δ) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpow : ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := by exact_mod_cast vmv_nat_add_one_le_two_pow a
  calc ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := hpow
    _ ≤ ((p : ℝ) ^ δ) ^ a := pow_le_pow_left₀ zero_le_two hp2 a
    _ = (p : ℝ) ^ ((a : ℝ) * δ) := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ δ) a, ← Real.rpow_mul hp0, mul_comm]

private lemma vmv_prime_pow_divisors_le_all {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : 2 ≤ p)
    (a : ℕ) :
    ((a + 1 : ℕ) : ℝ) ≤ (1 / min 1 (δ * Real.log 2)) * (p : ℝ) ^ (a * δ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let η : ℝ := min 1 (δ * Real.log 2)
  have hη_pos : 0 < η := lt_min zero_lt_one (mul_pos hδ hlog2)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ δ * Real.log 2 := min_le_right _ _
  have hexp : η * (a + 1 : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) * δ) := by
    have hlin : η * ((a : ℝ) + 1) ≤ (a : ℝ) * (δ * Real.log 2) + 1 := by
      have h1 : η * (a : ℝ) ≤ (a : ℝ) * (δ * Real.log 2) := by
        calc η * (a : ℝ) ≤ (δ * Real.log 2) * (a : ℝ) :=
              mul_le_mul_of_nonneg_right hη2 (Nat.cast_nonneg a)
          _ = (a : ℝ) * (δ * Real.log 2) := mul_comm _ _
      linarith only [h1, hη1]
    have hexp_le : (a : ℝ) * (δ * Real.log 2) + 1 ≤ Real.exp ((a : ℝ) * (δ * Real.log 2)) :=
      Real.add_one_le_exp _
    have hrpow : Real.exp ((a : ℝ) * (δ * Real.log 2)) = (2 : ℝ) ^ ((a : ℝ) * δ) := by
      rw [Real.rpow_def_of_pos zero_lt_two]
      congr 1
      ring
    linarith only [hlin, hexp_le, hrpow]
  have hp_rpow : (2 : ℝ) ^ ((a : ℝ) * δ) ≤ (p : ℝ) ^ ((a : ℝ) * δ) :=
    Real.rpow_le_rpow zero_le_two (by exact_mod_cast hp) (by positivity)
  have hmul : η * ((a + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ ((a : ℝ) * δ) := by
    push_cast
    exact hexp.trans hp_rpow
  have hdiv : ((a + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ ((a : ℝ) * δ) / η :=
    (le_div_iff₀' hη_pos).mpr hmul
  simpa [div_eq_mul_inv, mul_comm] using hdiv

private lemma vmv_card_divisors_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let B : ℝ := 1 / min 1 (δ * Real.log 2)
  have hB1 : 1 ≤ B := by
    have hη_pos : 0 < min 1 (δ * Real.log 2) := lt_min zero_lt_one (mul_pos hδ hlog2)
    have hη1 : min 1 (δ * Real.log 2) ≤ 1 := min_le_left _ _
    exact (one_le_div hη_pos).mpr hη1
  have hmain : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤
        (∏ _p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ δ < 2), B) * (n : ℝ) ^ δ := by
    intro n hn
    induction n using Nat.strongRecOn with
    | ind n ih =>
        by_cases hn1 : n = 1
        · subst hn1
          simp
        · have hn2 : 2 ≤ n := by omega
          let p := n.minFac
          have hp : p.Prime := Nat.minFac_prime hn1
          let q₁ := p ^ n.factorization p
          let q₂ := n / q₁
          have hq_mul : q₁ * q₂ = n := Nat.ordProj_mul_ordCompl_eq_self n p
          have hn0 : n ≠ 0 := by omega
          have hcop_p : Nat.Coprime p q₂ := Nat.coprime_ordCompl hp hn0
          have hcop : Nat.Coprime q₁ q₂ := hcop_p.pow_left (n.factorization p)
          have hq₂_pos : 1 ≤ q₂ := Nat.ordCompl_pos p hn0
          have hp_dvd : p ∣ n := Nat.minFac_dvd n
          have hp_fac : 1 ≤ n.factorization p :=
            (hp.dvd_iff_one_le_factorization hn0).mp hp_dvd
          have hp_le_q₁ : p ≤ q₁ := by
            have h1 : p ^ 1 ≤ p ^ (n.factorization p) := Nat.pow_le_pow_right hp.pos hp_fac
            simpa [q₁] using h1
          have hq₂_lt : q₂ < n := by
            calc q₂ = 1 * q₂ := (one_mul q₂).symm
              _ < p * q₂ := Nat.mul_lt_mul_of_pos_right hp.one_lt hq₂_pos
              _ ≤ q₁ * q₂ := Nat.mul_le_mul_right q₂ hp_le_q₁
              _ = n := hq_mul
          have ih2 := ih q₂ hq₂_lt hq₂_pos
          have hcard_mul : n.divisors.card = q₁.divisors.card * q₂.divisors.card := by
            rw [← hq_mul]
            exact Nat.Coprime.card_divisors_mul hcop
          have hq₁_card : q₁.divisors.card = n.factorization p + 1 := by
            dsimp only [q₁]
            rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
          have hq₁_bound :
              (q₁.divisors.card : ℝ) ≤
                (if (p : ℝ) ^ δ < 2 then B else 1) * (q₁ : ℝ) ^ δ := by
            rw [hq₁_card]
            have hq₁_cast : (q₁ : ℝ) ^ δ = (p : ℝ) ^ ((n.factorization p : ℝ) * δ) := by
              dsimp only [q₁]
              push_cast
              rw [← Real.rpow_natCast (p : ℝ) (n.factorization p),
                ← Real.rpow_mul (Nat.cast_nonneg p)]
            rw [hq₁_cast]
            split_ifs with hlt
            · exact vmv_prime_pow_divisors_le_all hδ hp.two_le (n.factorization p)
            · rw [one_mul]
              exact vmv_prime_pow_divisors_le_of_large hδ (not_lt.mp hlt) (n.factorization p)
          have hq₁0 : q₁ ≠ 0 := (Nat.ordProj_pos n p).ne'
          have hq₂0 : q₂ ≠ 0 := by omega
          have hpf : n.primeFactors = insert p q₂.primeFactors := by
            rw [← hq_mul, Nat.primeFactors_mul hq₁0 hq₂0]
            have hq₁_pf : q₁.primeFactors = {p} := by
              dsimp only [q₁]
              exact Nat.primeFactors_prime_pow (by omega : n.factorization p ≠ 0) hp
            rw [hq₁_pf, Finset.singleton_union]
          have hp_not_mem : p ∉ q₂.primeFactors := by
            intro hm
            exact Nat.not_dvd_ordCompl hp hn0 (Nat.dvd_of_mem_primeFactors hm)
          have hfilt :
              n.primeFactors.filter (fun r : ℕ => (r : ℝ) ^ δ < 2) =
                if (p : ℝ) ^ δ < 2 then
                  insert p (q₂.primeFactors.filter (fun r : ℕ => (r : ℝ) ^ δ < 2))
                else q₂.primeFactors.filter (fun r : ℕ => (r : ℝ) ^ δ < 2) := by
            rw [hpf]
            ext r
            simp only [Finset.mem_filter, Finset.mem_insert]
            split_ifs with hlt <;> simp only [Finset.mem_insert, Finset.mem_filter]
            · constructor
              · rintro ⟨rfl | hr, hrlt⟩
                · exact Or.inl rfl
                · exact Or.inr ⟨hr, hrlt⟩
              · rintro (rfl | ⟨hr, hrlt⟩)
                · exact ⟨Or.inl rfl, hlt⟩
                · exact ⟨Or.inr hr, hrlt⟩
            · constructor
              · rintro ⟨rfl | hr, hrlt⟩
                · exact False.elim (hlt hrlt)
                · exact ⟨hr, hrlt⟩
              · rintro ⟨hr, hrlt⟩
                exact ⟨Or.inr hr, hrlt⟩
          have hp_not_filt : p ∉ q₂.primeFactors.filter (fun r : ℕ => (r : ℝ) ^ δ < 2) :=
            fun h => hp_not_mem (Finset.mem_filter.mp h).1
          have hprod_eq :
              ∏ _r ∈ n.primeFactors.filter (fun r : ℕ => (r : ℝ) ^ δ < 2), B =
                (if (p : ℝ) ^ δ < 2 then B else 1) *
                  ∏ _r ∈ q₂.primeFactors.filter (fun r : ℕ => (r : ℝ) ^ δ < 2), B := by
            rw [hfilt]
            split_ifs with hlt
            · rw [Finset.prod_insert hp_not_filt]
            · rw [one_mul]
          have hnrpow : (n : ℝ) ^ δ = (q₁ : ℝ) ^ δ * (q₂ : ℝ) ^ δ := by
            rw [← hq_mul]
            push_cast
            exact Real.mul_rpow (Nat.cast_nonneg q₁) (Nat.cast_nonneg q₂)
          rw [hprod_eq, hnrpow, hcard_mul]
          push_cast
          have h1 : 0 ≤ (q₁.divisors.card : ℝ) := Nat.cast_nonneg _
          have h2 : 0 ≤ (q₂.divisors.card : ℝ) := Nat.cast_nonneg _
          have h3 : 0 ≤ (if (p : ℝ) ^ δ < 2 then B else 1) * (q₁ : ℝ) ^ δ := by positivity
          calc (q₁.divisors.card : ℝ) * (q₂.divisors.card : ℝ)
              ≤ ((if (p : ℝ) ^ δ < 2 then B else 1) * (q₁ : ℝ) ^ δ) *
                  ((∏ _r ∈ q₂.primeFactors.filter (fun r : ℕ => (r : ℝ) ^ δ < 2), B) *
                    (q₂ : ℝ) ^ δ) := mul_le_mul hq₁_bound ih2 h2 h3
            _ = _ := by ring
  let M : ℕ := Nat.ceil ((2 : ℝ) ^ (1 / δ)) + 1
  let U : Finset ℕ := (Finset.range M).filter Nat.Prime
  let C : ℝ := ∏ _p ∈ U, B
  have hC_pos : 0 < C := Finset.prod_pos fun _ _ => lt_of_lt_of_le zero_lt_one hB1
  refine ⟨C, hC_pos, fun n hn => ?_⟩
  have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ δ < 2) ⊆ U := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [U, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Nat.prime_of_mem_primeFactors hp.1⟩
    have hp_lt_pow : (p : ℝ) < (2 : ℝ) ^ (1 / δ) := by
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp.1).pos
      calc (p : ℝ) = ((p : ℝ) ^ δ) ^ (1 / δ) := by
            rw [← Real.rpow_mul hp0.le, mul_one_div_cancel hδ.ne', Real.rpow_one]
        _ < (2 : ℝ) ^ (1 / δ) := Real.rpow_lt_rpow (by positivity) hp.2 (div_pos zero_lt_one hδ)
    have hp_le_ceil : p ≤ Nat.ceil ((2 : ℝ) ^ (1 / δ)) :=
      Nat.lt_of_lt_of_le (Nat.lt_ceil.mpr hp_lt_pow) le_rfl |>.le
    omega
  have hprod_le :
      ∏ _p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ δ < 2), B ≤ C :=
    prod_const_le_of_subset_of_one_le hsub hB1
  exact (hmain n hn).trans (mul_le_mul_of_nonneg_right hprod_le (by positivity))

/-! ## Torus integrals and Vinogradov mean value J_{s,k}(N) -/

/-- Iterated integral over `[0, 1]^k` for a real-valued function on `Fin k → ℝ`. -/
noncomputable def torusIntegral : ∀ k : ℕ, ((Fin k → ℝ) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | k + 1, f => ∫ t in (0 : ℝ)..1, torusIntegral k (fun α => f (Fin.cons t α))

/-- Iterated integral over `[0, 1]^k` for a complex-valued function on `Fin k → ℝ`. -/
noncomputable def torusIntegralC : ∀ k : ℕ, ((Fin k → ℝ) → ℂ) → ℂ
  | 0, f => f Fin.elim0
  | k + 1, f => ∫ t in (0 : ℝ)..1, torusIntegralC k (fun α => f (Fin.cons t α))

/-- Vinogradov exponential sum `∑_{1 ≤ n ≤ N} exp (2πi ∑_{j=1}^k α_j n^j)`. -/
def vinogradovF (k N : ℕ) (α : Fin k → ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    Complex.exp (2 * Real.pi * (∑ j : Fin k, α j * (n : ℝ) ^ ((j : ℕ) + 1)) * Complex.I)

/-- Vinogradov mean value `J_{s,k}(N) = ∫_{[0,1]^k} ‖vinogradovF k N α‖^(2s) dα`. -/
noncomputable def vinogradovJ (s k N : ℕ) : ℝ :=
  torusIntegral k (fun α => ‖vinogradovF k N α‖ ^ (2 * s))

/-- Number of tuples `(x, y) ∈ [1, N]^s × [1, N]^s` satisfying `∑ x_i^j = ∑ y_i^j` for all
`1 ≤ j ≤ k`. -/
def vinogradovSolutionCount (s k N : ℕ) : ℕ :=
  let P := Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 N)
  ((P ×ˢ P).filter fun xy =>
    ∀ j : Fin k, ∑ i : Fin s, (xy.1 i : ℕ) ^ ((j : ℕ) + 1) =
      ∑ i : Fin s, (xy.2 i : ℕ) ^ ((j : ℕ) + 1)).card

private def torusChar (k : ℕ) (m : Fin k → ℤ) (α : Fin k → ℝ) : ℂ :=
  ∏ j : Fin k, vmvE (α j * (m j : ℝ))

private lemma torusIntegralC_char_sum_eq :
    ∀ (k : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (m : ι → Fin k → ℤ),
      torusIntegralC k (fun α => ∑ i ∈ s, c i * torusChar k (m i) α) =
        ∑ i ∈ s, c i * (if ∀ j : Fin k, m i j = 0 then (1 : ℂ) else 0)
  | 0, _, s, c, m => by
      simp [torusIntegralC, torusChar]
  | k + 1, _, s, c, m => by
      have hinner : ∀ t : ℝ,
          torusIntegralC k
            (fun α => ∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)) =
          ∑ i ∈ s,
            (c i * (if ∀ j : Fin k, m i j.succ = 0 then (1 : ℂ) else 0)) *
              vmvE ((m i 0 : ℝ) * t) := by
        intro t
        have hrew : (fun α : Fin k → ℝ =>
              ∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)) =
            fun α : Fin k → ℝ =>
              ∑ i ∈ s, (c i * vmvE ((m i 0 : ℝ) * t)) *
                torusChar k (fun j : Fin k => m i j.succ) α := by
          ext α
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp only [torusChar]
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm t (m i 0 : ℝ)]
          ring
        rw [hrew, torusIntegralC_char_sum_eq k s _ _]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      simp only [torusIntegralC]
      simp_rw [hinner]
      have hint : ∀ i ∈ s, IntervalIntegrable
          (fun t : ℝ => (c i * (if ∀ j : Fin k, m i j.succ = 0 then (1 : ℂ) else 0)) *
            vmvE ((m i 0 : ℝ) * t)) MeasureTheory.volume 0 1 := by
        intro i _
        refine Continuous.intervalIntegrable ?_ 0 1
        exact continuous_const.mul (continuous_vmvE.comp (continuous_const.mul continuous_id))
      rw [intervalIntegral.integral_finsetSum hint]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral_vmvE_int (m i 0)]
      by_cases h0 : m i 0 = 0 <;> by_cases hsucc : ∀ j : Fin k, m i j.succ = 0
      · have hall : ∀ j : Fin (k + 1), m i j = 0 := Fin.forall_fin_succ.mpr ⟨h0, hsucc⟩
        simp [h0, hsucc, hall]
      · have hnot : ¬ ∀ j : Fin (k + 1), m i j = 0 := fun hf => hsucc (Fin.forall_fin_succ.mp hf).2
        simp [h0, hsucc, hnot]
      · have hnot : ¬ ∀ j : Fin (k + 1), m i j = 0 := fun hf => h0 (Fin.forall_fin_succ.mp hf).1
        simp [h0, hsucc, hnot]
      · have hnot : ¬ ∀ j : Fin (k + 1), m i j = 0 := fun hf => h0 (Fin.forall_fin_succ.mp hf).1
        simp [h0, hsucc, hnot]

private lemma torusIntegral_re_char_sum :
    ∀ (k : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (m : ι → Fin k → ℤ),
      torusIntegral k (fun α => (∑ i ∈ s, c i * torusChar k (m i) α).re) =
        (torusIntegralC k (fun α => ∑ i ∈ s, c i * torusChar k (m i) α)).re
  | 0, _, s, c, m => by
      simp [torusIntegral, torusIntegralC]
  | k + 1, _, s, c, m => by
      have hstep : ∀ t : ℝ,
          torusIntegral k
            (fun α => (∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)).re) =
          (torusIntegralC k
            (fun α => ∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α))).re := by
        intro t
        have hrew : (fun α : Fin k → ℝ =>
              ∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)) =
            fun α : Fin k → ℝ =>
              ∑ i ∈ s, (c i * vmvE ((m i 0 : ℝ) * t)) *
                torusChar k (fun j : Fin k => m i j.succ) α := by
          ext α
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp only [torusChar]
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm t (m i 0 : ℝ)]
          ring
        have hrew_re :
            (fun α : Fin k → ℝ => (∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)).re) =
            fun α : Fin k → ℝ =>
              (∑ i ∈ s, (c i * vmvE ((m i 0 : ℝ) * t)) *
                torusChar k (fun j : Fin k => m i j.succ) α).re := by
          ext α
          exact congrArg Complex.re (congrFun hrew α)
        rw [hrew, hrew_re, torusIntegral_re_char_sum k s _ _]
      have hinner : ∀ t : ℝ,
          torusIntegralC k
            (fun α => ∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)) =
          ∑ i ∈ s,
            (c i * (if ∀ j : Fin k, m i j.succ = 0 then (1 : ℂ) else 0)) *
              vmvE ((m i 0 : ℝ) * t) := by
        intro t
        have hrew : (fun α : Fin k → ℝ =>
              ∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)) =
            fun α : Fin k → ℝ =>
              ∑ i ∈ s, (c i * vmvE ((m i 0 : ℝ) * t)) *
                torusChar k (fun j : Fin k => m i j.succ) α := by
          ext α
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp only [torusChar]
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm t (m i 0 : ℝ)]
          ring
        rw [hrew, torusIntegralC_char_sum_eq k s _ _]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have hint : IntervalIntegrable
          (fun t : ℝ => torusIntegralC k
            (fun α => ∑ i ∈ s, c i * torusChar (k + 1) (m i) (Fin.cons t α)))
          MeasureTheory.volume 0 1 := by
        simp_rw [hinner]
        refine Continuous.intervalIntegrable ?_ 0 1
        refine continuous_finsetSum s fun i _ => ?_
        exact continuous_const.mul (continuous_vmvE.comp (continuous_const.mul continuous_id))
      simp only [torusIntegral, torusIntegralC]
      simp_rw [hstep]
      exact vmv_intervalIntegral_re hint

/-- Exact Diophantine identity expressing the Vinogradov mean value `vinogradovJ s k N` as the
number of integer solutions `(x, y) ∈ [1, N]^{2s}` to `∑ x_i^j = ∑ y_i^j` (`1 ≤ j ≤ k`). -/
theorem vinogradovJ_eq_card_solutions (s k N : ℕ) :
    vinogradovJ s k N = (vinogradovSolutionCount s k N : ℝ) := by
  let S_N : Finset ℕ := Finset.Icc 1 N
  let P := Fintype.piFinset (fun _ : Fin s => S_N)
  let m_xy : (Fin s → ℕ) × (Fin s → ℕ) → Fin k → ℤ := fun p j =>
    ∑ i : Fin s, (p.1 i : ℤ) ^ ((j : ℕ) + 1) -
      ∑ i : Fin s, (p.2 i : ℤ) ^ ((j : ℕ) + 1)
  have hnorm_eq : ∀ α : Fin k → ℝ,
      ‖vinogradovF k N α‖ ^ (2 * s) =
        (∑ p ∈ P ×ˢ P, (1 : ℂ) * torusChar k (m_xy p) α).re := by
    intro α
    have hpowC : ((‖vinogradovF k N α‖ ^ (2 * s) : ℝ) : ℂ) =
        (vinogradovF k N α * star (vinogradovF k N α)) ^ s := by
      rw [← vmv_norm_sq_eq_mul_star, ← Complex.ofReal_pow, ← pow_mul]
    have hbase : vinogradovF k N α * star (vinogradovF k N α) =
        ∑ q ∈ S_N ×ˢ S_N,
          torusChar k (fun j : Fin k => (q.1 : ℤ) ^ ((j : ℕ) + 1) - (q.2 : ℤ) ^ ((j : ℕ) + 1)) α := by
      rw [vinogradovF, star_sum, Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      have hchar : ∀ n : ℕ,
          Complex.exp (2 * Real.pi * (∑ j : Fin k, α j * (n : ℝ) ^ ((j : ℕ) + 1)) * Complex.I) =
            ∏ j : Fin k, vmvE (α j * ((n : ℤ) ^ ((j : ℕ) + 1) : ℝ)) := by
        intro n
        have hsum : (2 : ℂ) * Real.pi * ↑(∑ j : Fin k, α j * (n : ℝ) ^ ((j : ℕ) + 1)) * Complex.I =
            ∑ j : Fin k, (2 : ℂ) * Real.pi * ↑(α j * ((n : ℤ) ^ ((j : ℕ) + 1) : ℝ)) * Complex.I := by
          push_cast
          rw [Finset.mul_sum, Finset.sum_mul]
        rw [hsum, Complex.exp_sum]
        rfl
      rw [hchar x, hchar y, star_prod]
      simp_rw [star_vmvE, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← vmvE_add]
      congr 1
      push_cast
      ring
    have hpow_sum :
        (vinogradovF k N α * star (vinogradovF k N α)) ^ s =
          ∑ p ∈ P ×ˢ P, (1 : ℂ) * torusChar k (m_xy p) α := by
      rw [hbase, Finset.sum_pow']
      let Q := Fintype.piFinset (fun _ : Fin s => S_N ×ˢ S_N)
      let φ : (Fin s → ℕ) × (Fin s → ℕ) → Fin s → ℕ × ℕ :=
        fun p i => (p.1 i, p.2 i)
      have hQ : (P ×ˢ P).image φ = Q := by
        ext f
        simp only [Finset.mem_image, Finset.mem_product, P, Q, Fintype.mem_piFinset, Prod.exists]
        constructor
        · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩ i
          exact ⟨hx i, hy i⟩
        · intro hf
          refine ⟨fun i => (f i).1, fun i => (f i).2,
            ⟨fun i => (hf i).1, fun i => (hf i).2⟩, rfl⟩
      have hφ_inj : Set.InjOn φ ↑(P ×ˢ P) := by
        intro p₁ _ p₂ _ h
        ext i
        · exact congrArg (fun g => (g i).1) h
        · exact congrArg (fun g => (g i).2) h
      change (∑ p ∈ Q, _) = _
      rw [← hQ, Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hφ_inj hp₁ hp₂ h)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [one_mul]
      dsimp only [torusChar, φ, m_xy]
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hsumE : ∀ g : Fin s → ℝ, (∏ i : Fin s, vmvE (g i)) = vmvE (∑ i : Fin s, g i) := by
        intro g
        induction Finset.univ (α := Fin s) using Finset.induction_on with
        | empty => simp [vmvE_zero]
        | insert a t ha ih =>
            rw [Finset.prod_insert ha, Finset.sum_insert ha, vmvE_add, ih]
      rw [hsumE]
      congr 1
      push_cast
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have hre := congrArg Complex.re (hpowC.trans hpow_sum)
    simpa only [Complex.ofReal_re] using hre
  dsimp only [vinogradovJ]
  simp_rw [hnorm_eq]
  rw [torusIntegral_re_char_sum k (P ×ˢ P) (fun _ => 1) m_xy,
    torusIntegralC_char_sum_eq k (P ×ˢ P) (fun _ => 1) m_xy]
  simp only [one_mul, Complex.re_sum]
  dsimp only [vinogradovSolutionCount]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff : (∀ j : Fin k, m_xy p j = 0) ↔
      ∀ j : Fin k, ∑ i : Fin s, (p.1 i : ℕ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin s, (p.2 i : ℕ) ^ ((j : ℕ) + 1) := by
    refine forall_congr' fun j => ?_
    dsimp only [m_xy]
    rw [sub_eq_zero]
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  by_cases h1 : ∀ j : Fin k, m_xy p j = 0
  · simp [h1, hiff.mp h1]
  · simp [h1, show ¬ ∀ j : Fin k, ∑ i : Fin s, (p.1 i : ℕ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin s, (p.2 i : ℕ) ^ ((j : ℕ) + 1) from fun h2 => h1 (hiff.mpr h2)]

/-- Nonnegativity of `vinogradovJ s k N`. -/
theorem vinogradovJ_nonneg (s k N : ℕ) : 0 ≤ vinogradovJ s k N := by
  rw [vinogradovJ_eq_card_solutions]
  exact Nat.cast_nonneg _

/-! ## Weyl differencing and Hua's lemma -/

private def vmvPolyStep (P : Polynomial ℤ) (h : ℤ) : Polynomial ℤ :=
  P.comp (Polynomial.X + Polynomial.C h) - P

private def vmvPolyIter : ∀ j : ℕ, (Fin j → ℤ) → Polynomial ℤ → Polynomial ℤ
  | 0, _, P => P
  | j + 1, h, P => vmvPolyStep (vmvPolyIter j (Fin.init h) P) (h (Fin.last j))

private def vmvWeylDom : ∀ j : ℕ, (Fin j → ℤ) → ℕ → Finset ℤ
  | 0, _, N => Finset.Icc (1 : ℤ) N
  | j + 1, h, N =>
      let D := vmvWeylDom j (Fin.init h) N
      D.filter (fun n => n + h (Fin.last j) ∈ D)

private lemma vmvWeylDom_subset_Icc :
    ∀ (j : ℕ) (h : Fin j → ℤ) (N : ℕ), vmvWeylDom j h N ⊆ Finset.Icc (1 : ℤ) N
  | 0, _, _ => le_rfl
  | j + 1, h, N => (Finset.filter_subset _ _).trans (vmvWeylDom_subset_Icc j (Fin.init h) N)

private lemma C_dvd_vmvPolyStep (P : Polynomial ℤ) (h : ℤ) :
    Polynomial.C h ∣ vmvPolyStep P h := by
  dsimp only [vmvPolyStep]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, add_sub_add_comm]
      exact dvd_add hp hq
  | monomial n a =>
      have hcomp : (Polynomial.monomial n a).comp (Polynomial.X + Polynomial.C h) -
          Polynomial.monomial n a =
            Polynomial.C a * ((Polynomial.X + Polynomial.C h) ^ n - Polynomial.X ^ n) := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.X_pow_comp]
        ring
      rw [hcomp]
      refine dvd_mul_of_dvd_right ?_ _
      have hdvd := sub_dvd_pow_sub_pow (Polynomial.X + Polynomial.C h) Polynomial.X n
      simpa only [add_sub_cancel_left] using hdvd

private lemma C_dvd_vmvPolyStep_mul (P : Polynomial ℤ) {d h : ℤ} (hd : Polynomial.C d ∣ P) :
    Polynomial.C (d * h) ∣ vmvPolyStep P h := by
  rcases hd with ⟨Q, rfl⟩
  have hrew : vmvPolyStep (Polynomial.C d * Q) h = Polynomial.C d * vmvPolyStep Q h := by
    simp only [vmvPolyStep, Polynomial.mul_comp, Polynomial.C_comp]
    ring
  rw [hrew, map_mul]
  exact mul_dvd_mul_left _ (C_dvd_vmvPolyStep Q h)

private lemma prod_dvd_vmvPolyIter :
    ∀ (j : ℕ) (h : Fin j → ℤ) (P : Polynomial ℤ),
      Polynomial.C (∏ i : Fin j, h i) ∣ vmvPolyIter j h P
  | 0, _, P => by simp [vmvPolyIter]
  | j + 1, h, P => by
      rw [vmvPolyIter, Fin.prod_univ_castSucc]
      exact C_dvd_vmvPolyStep_mul _ (prod_dvd_vmvPolyIter j (Fin.init h) P)

private lemma eval_prod_dvd_vmvPolyIter (j : ℕ) (h : Fin j → ℤ) (P : Polynomial ℤ) (n : ℤ) :
    (∏ i : Fin j, h i) ∣ (vmvPolyIter j h P).eval n := by
  rcases prod_dvd_vmvPolyIter j h P with ⟨Q, hQ⟩
  refine ⟨Q.eval n, ?_⟩
  have hev := congrArg (Polynomial.eval n) hQ
  rw [Polynomial.eval_mul, Polynomial.eval_C] at hev
  exact hev

private lemma vmvPolyStep_C_mul_X_pow_coeff (a : ℤ) (r : ℕ) (h : ℤ) (i : ℕ) :
    (vmvPolyStep (Polynomial.C a * Polynomial.X ^ r) h).coeff i =
      a * ((if i ≤ r then (r.choose i : ℤ) * h ^ (r - i) else 0) - if i = r then 1 else 0) := by
  have hcomp : vmvPolyStep (Polynomial.C a * Polynomial.X ^ r) h =
      Polynomial.C a * ((Polynomial.X + Polynomial.C h) ^ r - Polynomial.X ^ r) := by
    simp only [vmvPolyStep, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
    ring
  rw [hcomp, Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  congr 1
  congr 1
  by_cases hi : i ≤ r
  · simp only [hi, ↓reduceIte, Polynomial.coeff_X_add_C_pow, mul_comm]
  · simp only [hi, ↓reduceIte]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    have hdeg : ((Polynomial.X + Polynomial.C h : Polynomial ℤ) ^ r).natDegree ≤ r :=
      (Polynomial.natDegree_pow_le).trans (by
        rw [Polynomial.natDegree_X_add_C, mul_one])
    exact lt_of_le_of_lt hdeg (not_le.mp hi)

private lemma vmvPolyStep_coeff_eq_zero_of_le {P : Polynomial ℤ} (h : ℤ) {i : ℕ}
    (hi : P.natDegree ≤ i) :
    (vmvPolyStep P h).coeff i = 0 := by
  have hsum : P = ∑ r ∈ Finset.range (P.natDegree + 1),
      Polynomial.C (P.coeff r) * Polynomial.X ^ r :=
    Polynomial.as_sum_range_C_mul_X_pow P
  have hstep : vmvPolyStep P h = ∑ r ∈ Finset.range (P.natDegree + 1),
      vmvPolyStep (Polynomial.C (P.coeff r) * Polynomial.X ^ r) h := by
    conv_lhs => rw [hsum]
    simp only [vmvPolyStep, Polynomial.sum_comp]
    rw [Finset.sum_sub_distrib]
  rw [hstep, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hr_le : r ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [vmvPolyStep_C_mul_X_pow_coeff]
  by_cases hir : i = r
  · subst hir
    simp
  · by_cases hle : i ≤ r
    · exact False.elim (hir (le_antisymm hle (hr_le.trans hi)))
    · simp [hle, hir]

private lemma vmvPolyStep_coeff_pred {P : Polynomial ℤ} (hdeg : 1 ≤ P.natDegree) (h : ℤ) :
    (vmvPolyStep P h).coeff (P.natDegree - 1) =
      (P.natDegree : ℤ) * h * P.leadingCoeff := by
  let d := P.natDegree
  have hsum : P = ∑ r ∈ Finset.range (d + 1), Polynomial.C (P.coeff r) * Polynomial.X ^ r :=
    Polynomial.as_sum_range_C_mul_X_pow P
  have hstep : vmvPolyStep P h = ∑ r ∈ Finset.range (d + 1),
      vmvPolyStep (Polynomial.C (P.coeff r) * Polynomial.X ^ r) h := by
    conv_lhs => rw [hsum]
    simp only [vmvPolyStep, Polynomial.sum_comp]
    rw [Finset.sum_sub_distrib]
  rw [hstep, Polynomial.finsetSum_coeff, Finset.sum_range_succ]
  have hlow : ∑ r ∈ Finset.range d,
      (vmvPolyStep (Polynomial.C (P.coeff r) * Polynomial.X ^ r) h).coeff (d - 1) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr_lt : r < d := Finset.mem_range.mp hr
    rw [vmvPolyStep_C_mul_X_pow_coeff]
    by_cases hdr : d - 1 = r
    · subst hdr
      simp
    · have hle : ¬ d - 1 ≤ r := by omega
      simp [hle, hdr]
  rw [hlow, zero_add, vmvPolyStep_C_mul_X_pow_coeff]
  have hd1 : d - 1 ≤ d := Nat.sub_le d 1
  have hd_ne : d - 1 ≠ d := by omega
  have hchoose : d.choose (d - 1) = d :=
    (Nat.choose_symm (by omega : 1 ≤ d)).trans (Nat.choose_one_right d)
  have hexp : d - (d - 1) = 1 := by omega
  dsimp only [d] at hd1 hd_ne hchoose hexp ⊢
  simp only [hd1, ↓reduceIte, hd_ne, hchoose, hexp, pow_one, sub_zero]
  rw [Polynomial.leadingCoeff, mul_comm]

private lemma vmvPolyStep_natDegree_and_leadingCoeff {P : Polynomial ℤ}
    (hdeg : 1 ≤ P.natDegree) {h : ℤ} (hh : h ≠ 0) :
    (vmvPolyStep P h).natDegree = P.natDegree - 1 ∧
      (vmvPolyStep P h).leadingCoeff = (P.natDegree : ℤ) * h * P.leadingCoeff := by
  have hP0 : P ≠ 0 := by
    intro h0
    subst h0
    simp at hdeg
  have hlc0 : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hcoeff0 : (vmvPolyStep P h).coeff (P.natDegree - 1) ≠ 0 := by
    rw [vmvPolyStep_coeff_pred hdeg h]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (by omega : P.natDegree ≠ 0)) hh) hlc0
  have hndeg : (vmvPolyStep P h).natDegree = P.natDegree - 1 := by
    refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero hcoeff0)
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    exact vmvPolyStep_coeff_eq_zero_of_le h (by omega)
  refine ⟨hndeg, ?_⟩
  rw [Polynomial.leadingCoeff, hndeg, vmvPolyStep_coeff_pred hdeg h]

private lemma vmvPolyIter_X_pow_natDegree_and_leadingCoeff {k : ℕ} :
    ∀ (j : ℕ) (_hj : j ≤ k) (h : Fin j → ℤ), (∏ i : Fin j, h i) ≠ 0 →
      (vmvPolyIter j h (Polynomial.X ^ k)).natDegree = k - j ∧
        (vmvPolyIter j h (Polynomial.X ^ k)).leadingCoeff =
          (Nat.descFactorial k j : ℤ) * ∏ i : Fin j, h i
  | 0, _, _, _ => by
      simp [vmvPolyIter]
  | j + 1, hj, h, hprod => by
      rw [Fin.prod_univ_castSucc] at hprod
      have hprod_init : (∏ i : Fin j, Fin.init h i) ≠ 0 := left_ne_zero_of_mul hprod
      have hlast : h (Fin.last j) ≠ 0 := right_ne_zero_of_mul hprod
      have ih := @vmvPolyIter_X_pow_natDegree_and_leadingCoeff k j (by omega) (Fin.init h) hprod_init
      have hdeg1 : 1 ≤ (vmvPolyIter j (Fin.init h) (Polynomial.X ^ k)).natDegree := by
        rw [ih.1]; omega
      have hstep := vmvPolyStep_natDegree_and_leadingCoeff hdeg1 hlast
      rw [vmvPolyIter]
      refine ⟨?_, ?_⟩
      · rw [hstep.1, ih.1]; omega
      · rw [hstep.2, ih.1, ih.2, Nat.descFactorial_succ, Fin.prod_univ_castSucc]
        have hinit : (∏ i : Fin j, Fin.init h i) = ∏ i : Fin j, h i.castSucc := rfl
        rw [hinit]
        push_cast
        ring

private lemma vmv_card_roots_Icc_le {Q : Polynomial ℤ} (hQ : Q ≠ 0) (N : ℕ) :
    ((Finset.Icc (1 : ℤ) N).filter (fun n => Q.eval n = 0)).card ≤ Q.natDegree := by
  let S := (Finset.Icc (1 : ℤ) N).filter (fun n => Q.eval n = 0)
  have hsub : S.val ⊆ Q.roots := by
    intro n hn
    rw [Finset.mem_val, Finset.mem_filter] at hn
    exact (Polynomial.mem_roots hQ).mpr hn.2
  have hle : S.val ≤ Q.roots := (Multiset.le_iff_subset S.nodup).mpr hsub
  exact (Multiset.card_le_card hle).trans (Polynomial.card_roots' Q)

private lemma vmv_sq_finset_sum_exp (S : Finset ℤ) (f : ℤ → ℤ) (α : ℝ) :
    ‖∑ n ∈ S, vmvE (α * (f n : ℝ))‖ ^ 2 =
      (∑ p ∈ S ×ˢ S, vmvE (α * ((f p.1 - f p.2 : ℤ) : ℝ))).re := by
  have hnorm : ((‖∑ n ∈ S, vmvE (α * (f n : ℝ))‖ ^ 2 : ℝ) : ℂ) =
      (∑ n ∈ S, vmvE (α * (f n : ℝ))) * star (∑ n ∈ S, vmvE (α * (f n : ℝ))) :=
    vmv_norm_sq_eq_mul_star _
  have hmul : (∑ n ∈ S, vmvE (α * (f n : ℝ))) * star (∑ n ∈ S, vmvE (α * (f n : ℝ))) =
      ∑ p ∈ S ×ˢ S, vmvE (α * ((f p.1 - f p.2 : ℤ) : ℝ)) := by
    rw [star_sum, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    rw [star_vmvE, ← vmvE_add]
    congr 1
    push_cast
    ring
  exact congrArg Complex.re (hnorm.trans hmul)

private lemma vmv_weyl_squaring_step (S : Finset ℤ) {N : ℕ} (hS : S ⊆ Finset.Icc (1 : ℤ) N)
    (P : Polynomial ℤ) (α : ℝ) :
    ‖∑ n ∈ S, vmvE (α * ((P.eval n : ℤ) : ℝ))‖ ^ 2 =
      (∑ h ∈ Finset.Ioo (-N : ℤ) N, ∑ n ∈ S.filter (fun n => n + h ∈ S),
        vmvE (α * (((vmvPolyStep P h).eval n : ℤ) : ℝ))).re := by
  rw [vmv_sq_finset_sum_exp S (fun n => P.eval n) α]
  congr 1
  let B := Finset.Ioo (-N : ℤ) N
  let Sigma := B.sigma (fun h => S.filter (fun n => n + h ∈ S))
  let φ : (Σ _h : ℤ, ℤ) → ℤ × ℤ := fun hn => (hn.2 + hn.1, hn.2)
  have hbij : (Sigma.image φ) = S ×ˢ S := by
    ext p
    simp only [Finset.mem_image, Finset.mem_sigma, Sigma, B, Finset.mem_Ioo,
      Finset.mem_filter, Finset.mem_product, φ]
    constructor
    · rintro ⟨⟨h, n⟩, ⟨⟨_, _⟩, hnS, hnhS⟩, hp⟩
      rw [← hp]
      exact ⟨hnhS, hnS⟩
    · rintro ⟨hp1, hp2⟩
      have hp1_mem := Finset.mem_Icc.mp (hS hp1)
      have hp2_mem := Finset.mem_Icc.mp (hS hp2)
      refine ⟨⟨p.1 - p.2, p.2⟩, ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, hp2, ?_⟩, ?_⟩
      · dsimp only; rw [add_comm, sub_add_cancel]; exact hp1
      · ext <;> simp
  have hφ_inj : Set.InjOn φ (Sigma : Set _) := by
    intro a _ b _ h
    simp only [φ, Prod.mk.injEq] at h
    rcases a with ⟨h1, n1⟩
    rcases b with ⟨h2, n2⟩
    have hn : n1 = n2 := h.2
    subst hn
    have hh : h1 = h2 := by linarith [h.1]
    subst hh
    rfl
  rw [← hbij, Finset.sum_image (fun a ha b hb h => hφ_inj ha hb h), Finset.sum_sigma]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun n _ => ?_
  simp only [φ, vmvPolyStep, Polynomial.eval_sub, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

private lemma vmvWeylDom_snoc (j : ℕ) (h : Fin j → ℤ) (h0 : ℤ) (N : ℕ) :
    vmvWeylDom (j + 1) (Fin.snoc (α := fun _ => ℤ) h h0) N =
      (vmvWeylDom j h N).filter (fun n => n + h0 ∈ vmvWeylDom j h N) := by
  change (vmvWeylDom j (Fin.init (Fin.snoc (α := fun _ => ℤ) h h0)) N).filter
      (fun n => n + (Fin.snoc (α := fun _ => ℤ) h h0) (Fin.last j) ∈
        vmvWeylDom j (Fin.init (Fin.snoc (α := fun _ => ℤ) h h0)) N) = _
  rw [Fin.init_snoc, Fin.snoc_last]

private lemma vmvPolyIter_snoc (j : ℕ) (h : Fin j → ℤ) (h0 : ℤ) (P : Polynomial ℤ) :
    vmvPolyIter (j + 1) (Fin.snoc (α := fun _ => ℤ) h h0) P =
      vmvPolyStep (vmvPolyIter j h P) h0 := by
  change vmvPolyStep (vmvPolyIter j (Fin.init (Fin.snoc (α := fun _ => ℤ) h h0)) P)
      ((Fin.snoc (α := fun _ => ℤ) h h0) (Fin.last j)) = _
  rw [Fin.init_snoc, Fin.snoc_last]

private lemma vmv_weyl_squaring_ineq (P : Polynomial ℤ) (α : ℝ) :
    ∀ (j : ℕ) (_hj : 1 ≤ j) (N : ℕ) (_hN : 1 ≤ N),
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, vmvE (α * ((P.eval n : ℤ) : ℝ))‖ ^ (2 ^ j) ≤
        (2 * (N : ℝ)) ^ (2 ^ j - j - 1) *
          (∑ h ∈ Fintype.piFinset (fun _ : Fin j => Finset.Ioo (-N : ℤ) N),
            ∑ n ∈ vmvWeylDom j h N, vmvE (α * (((vmvPolyIter j h P).eval n : ℤ) : ℝ))).re
  | 0, hj, _, _ => by omega
  | 1, _, N, _ => by
      have hexp : 2 ^ 1 - 1 - 1 = 0 := by norm_num
      rw [hexp, pow_zero, one_mul, pow_one]
      have hstep := vmv_weyl_squaring_step (Finset.Icc (1 : ℤ) N) le_rfl P α
      let I1 := Fintype.piFinset (fun _ : Fin 1 => Finset.Ioo (-N : ℤ) N)
      let φ : ℤ → Fin 1 → ℤ := fun h _ => h
      have hI1 : (Finset.Ioo (-N : ℤ) N).image φ = I1 := by
        ext f
        simp only [Finset.mem_image, I1, Fintype.mem_piFinset, Finset.mem_Ioo]
        constructor
        · rintro ⟨h, hh, rfl⟩ _
          exact hh
        · intro hf
          refine ⟨f 0, hf 0, ?_⟩
          ext i
          fin_cases i
          rfl
      have hφ_inj : Set.InjOn φ (Finset.Ioo (-N : ℤ) N : Set ℤ) := by
        intro a _ b _ h
        exact congrFun h 0
      rw [hstep]
      refine le_of_eq (congrArg Complex.re ?_)
      change _ = ∑ h ∈ I1, ∑ n ∈ vmvWeylDom 1 h N, vmvE (α * (((vmvPolyIter 1 h P).eval n : ℤ) : ℝ))
      rw [← hI1, Finset.sum_image (fun a ha b hb h => hφ_inj ha hb h)]
      refine Finset.sum_congr rfl fun h _ => ?_
      have hdom : vmvWeylDom 1 (φ h) N =
          (Finset.Icc (1 : ℤ) N).filter (fun n => n + h ∈ Finset.Icc (1 : ℤ) N) := rfl
      have hpoly : vmvPolyIter 1 (φ h) P = vmvPolyStep P h := rfl
      rw [hdom, hpoly]
  | j + 2, _, N, hN => by
      have ih := vmv_weyl_squaring_ineq P α (j + 1) (by omega) N hN
      have hsq :
          ‖∑ n ∈ Finset.Icc (1 : ℤ) N, vmvE (α * ((P.eval n : ℤ) : ℝ))‖ ^ (2 ^ (j + 2)) =
            (‖∑ n ∈ Finset.Icc (1 : ℤ) N, vmvE (α * ((P.eval n : ℤ) : ℝ))‖ ^ (2 ^ (j + 1))) ^ 2 := by
        rw [pow_succ, pow_mul]
      have h2N_nn : 0 ≤ (2 * (N : ℝ)) := by positivity
      let B := Finset.Ioo (-N : ℤ) N
      let Ij := Fintype.piFinset (fun _ : Fin (j + 1) => B)
      let innerSum : (Fin (j + 1) → ℤ) → ℂ := fun h =>
        ∑ n ∈ vmvWeylDom (j + 1) h N, vmvE (α * (((vmvPolyIter (j + 1) h P).eval n : ℤ) : ℝ))
      have hI_card : (Ij.card : ℝ) ≤ (2 * (N : ℝ)) ^ (j + 1) := by
        have hc : Ij.card = B.card ^ (j + 1) := by
          dsimp only [Ij]
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have hB : B.card ≤ 2 * N := by
          dsimp only [B]
          rw [Int.card_Ioo]
          omega
        rw [hc]
        exact_mod_cast Nat.pow_le_pow_left hB (j + 1)
      have hinner_cs :
          ((∑ h ∈ Ij, innerSum h).re) ^ 2 ≤
            (Ij.card : ℝ) * ∑ h ∈ Ij, ‖innerSum h‖ ^ 2 := by
        have hre_le : |(∑ h ∈ Ij, innerSum h).re| ≤ ∑ h ∈ Ij, ‖innerSum h‖ :=
          (Complex.abs_re_le_norm _).trans (norm_sum_le _ _)
        have hsq_re : ((∑ h ∈ Ij, innerSum h).re) ^ 2 ≤ (∑ h ∈ Ij, ‖innerSum h‖) ^ 2 := by
          rw [← sq_abs ((∑ h ∈ Ij, innerSum h).re)]
          exact pow_le_pow_left₀ (abs_nonneg _) hre_le 2
        exact hsq_re.trans sq_sum_le_card_mul_sum_sq
      have hsq_step : ∀ h ∈ Ij,
          ‖innerSum h‖ ^ 2 =
            (∑ h0 ∈ B, ∑ n ∈ vmvWeylDom (j + 2) (Fin.snoc (α := fun _ => ℤ) h h0) N,
              vmvE (α * (((vmvPolyIter (j + 2) (Fin.snoc (α := fun _ => ℤ) h h0) P).eval n : ℤ) : ℝ))).re := by
        intro h _
        dsimp only [innerSum]
        rw [vmv_weyl_squaring_step (vmvWeylDom (j + 1) h N) (vmvWeylDom_subset_Icc (j + 1) h N)
          (vmvPolyIter (j + 1) h P) α]
        refine congrArg Complex.re (Finset.sum_congr rfl fun h0 _ => ?_)
        rw [vmvWeylDom_snoc (j + 1) h h0 N, vmvPolyIter_snoc (j + 1) h h0 P]
      let Ij1 := Fintype.piFinset (fun _ : Fin (j + 2) => B)
      let ψ : (Fin (j + 1) → ℤ) × ℤ → Fin (j + 2) → ℤ := fun p => Fin.snoc p.1 p.2
      have hψ_img : (Ij ×ˢ B).image ψ = Ij1 := by
        ext f
        simp only [Finset.mem_image, Finset.mem_product, Ij, Ij1, Fintype.mem_piFinset, ψ]
        constructor
        · rintro ⟨⟨h, h0⟩, ⟨hh, hh0⟩, rfl⟩ i
          induction i using Fin.lastCases with
          | last => simpa using hh0
          | cast i => simpa using hh i
        · intro hf
          refine ⟨⟨Fin.init f, f (Fin.last (j + 1))⟩,
            ⟨fun i => hf i.castSucc, hf (Fin.last (j + 1))⟩, Fin.snoc_init_self f⟩
      have hψ_inj : Set.InjOn ψ ↑(Ij ×ˢ B) := by
        intro p₁ _ p₂ _ h
        ext i
        · have h1 := congrArg (fun f => Fin.init f) h
          dsimp only [ψ] at h1
          rw [Fin.init_snoc, Fin.init_snoc] at h1
          exact congrFun h1 i
        · have h2 := congrArg (fun f => f (Fin.last (j + 1))) h
          dsimp only [ψ] at h2
          rw [Fin.snoc_last, Fin.snoc_last] at h2
          exact h2
      have hsum_combine :
          ∑ h ∈ Ij, ‖innerSum h‖ ^ 2 =
            (∑ h ∈ Ij1, ∑ n ∈ vmvWeylDom (j + 2) h N,
              vmvE (α * (((vmvPolyIter (j + 2) h P).eval n : ℤ) : ℝ))).re := by
        have hstep1 : ∑ h ∈ Ij, ‖innerSum h‖ ^ 2 =
            ∑ h ∈ Ij, (∑ h0 ∈ B, ∑ n ∈ vmvWeylDom (j + 2) (ψ (h, h0)) N,
              vmvE (α * (((vmvPolyIter (j + 2) (ψ (h, h0)) P).eval n : ℤ) : ℝ))).re :=
          Finset.sum_congr rfl fun h hh => hsq_step h hh
        rw [hstep1, ← Complex.re_sum]
        refine congrArg Complex.re ?_
        rw [← hψ_img, Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hψ_inj hp₁ hp₂ h), Finset.sum_product]
      have hpow_arith : 2 * (2 ^ (j + 1) - (j + 1) - 1) + (j + 1) =
          2 ^ (j + 2) - (j + 2) - 1 := by
        have hge : j + 2 ≤ 2 ^ (j + 1) := vmv_succ_le_two_pow (j + 1)
        have hp1 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, mul_comm]
        have hp2 : 2 ^ (j + 2) = 4 * 2 ^ j := by rw [pow_succ, pow_succ]; ring
        omega
      calc ‖∑ n ∈ Finset.Icc (1 : ℤ) N, vmvE (α * ((P.eval n : ℤ) : ℝ))‖ ^ (2 ^ (j + 2))
          = (‖∑ n ∈ Finset.Icc (1 : ℤ) N, vmvE (α * ((P.eval n : ℤ) : ℝ))‖ ^ (2 ^ (j + 1))) ^ 2 := hsq
        _ ≤ ((2 * (N : ℝ)) ^ (2 ^ (j + 1) - (j + 1) - 1) * (∑ h ∈ Ij, innerSum h).re) ^ 2 :=
            pow_le_pow_left₀ (by positivity) ih 2
        _ = (2 * (N : ℝ)) ^ (2 * (2 ^ (j + 1) - (j + 1) - 1)) * ((∑ h ∈ Ij, innerSum h).re) ^ 2 := by
            rw [mul_pow, ← pow_mul, mul_comm _ 2]
        _ ≤ (2 * (N : ℝ)) ^ (2 * (2 ^ (j + 1) - (j + 1) - 1)) *
              ((Ij.card : ℝ) * ∑ h ∈ Ij, ‖innerSum h‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hinner_cs (by positivity)
        _ ≤ (2 * (N : ℝ)) ^ (2 * (2 ^ (j + 1) - (j + 1) - 1)) *
              ((2 * (N : ℝ)) ^ (j + 1) * ∑ h ∈ Ij, ‖innerSum h‖ ^ 2) := by
            have hsum_nn : 0 ≤ ∑ h ∈ Ij, ‖innerSum h‖ ^ 2 :=
              Finset.sum_nonneg fun _ _ => sq_nonneg _
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hI_card hsum_nn) (by positivity)
        _ = (2 * (N : ℝ)) ^ (2 ^ (j + 2) - (j + 2) - 1) *
              (∑ h ∈ Ij1, ∑ n ∈ vmvWeylDom (j + 2) h N,
                vmvE (α * (((vmvPolyIter (j + 2) h P).eval n : ℤ) : ℝ))).re := by
            rw [← mul_assoc, ← pow_add, hpow_arith, hsum_combine]

private lemma card_piFinset_int_divisors (j : ℕ) (N : ℕ) {m : ℤ} (hm : m ≠ 0) :
    ((Fintype.piFinset (fun _ : Fin j => Finset.Ioo (-N : ℤ) N)).filter
      (fun h : Fin j → ℤ => (∏ i : Fin j, h i) ∣ m)).card ≤
      (2 * m.natAbs.divisors.card) ^ j := by
  let Ij := Fintype.piFinset (fun _ : Fin j => Finset.Ioo (-N : ℤ) N)
  let D := (m.natAbs.divisors ×ˢ ({true, false} : Finset Bool))
  let F := Fintype.piFinset (fun _ : Fin j => D)
  let dec : (Fin j → ℕ × Bool) → (Fin j → ℤ) :=
    fun f i => if (f i).2 then ((f i).1 : ℤ) else -((f i).1 : ℤ)
  have hsub : Ij.filter (fun h => (∏ i : Fin j, h i) ∣ m) ⊆ F.image dec := by
    intro h hh
    simp only [Finset.mem_filter, Ij, Fintype.mem_piFinset] at hh
    rw [Finset.mem_image]
    have hdvd_i : ∀ i : Fin j, h i ∣ m := fun i =>
      dvd_trans (Finset.dvd_prod_of_mem h (Finset.mem_univ i)) hh.2
    have hne_i : ∀ i : Fin j, h i ≠ 0 := fun i hi => by
      have : (0 : ℤ) ∣ m := hi ▸ hdvd_i i
      exact hm (zero_dvd_iff.mp this)
    refine ⟨fun i => ((h i).natAbs, decide (0 ≤ h i)), ?_, ?_⟩
    · simp only [F, Fintype.mem_piFinset, D, Finset.mem_product, Nat.mem_divisors,
        Finset.mem_insert, Finset.mem_singleton]
      intro i
      exact ⟨⟨Int.natAbs_dvd_natAbs.mpr (hdvd_i i), Int.natAbs_ne_zero.mpr hm⟩, by cases h0 : decide (0 ≤ h i) <;> simp⟩
    · ext i
      dsimp only [dec]
      by_cases hnonneg : 0 ≤ h i
      · simp [hnonneg, Int.natAbs_of_nonneg hnonneg]
      · have hneg : h i < 0 := not_le.mp hnonneg
        simp [hnonneg, Int.ofNat_natAbs_of_nonpos hneg.le]
  calc (Ij.filter (fun h => (∏ i : Fin j, h i) ∣ m)).card
      ≤ (F.image dec).card := Finset.card_le_card hsub
    _ ≤ F.card := Finset.card_image_le
    _ = D.card ^ j := by
        dsimp only [F]
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = (2 * m.natAbs.divisors.card) ^ j := by
        dsimp only [D]
        rw [Finset.card_product, show ({true, false} : Finset Bool).card = 2 by decide, mul_comm]

private lemma card_piFinset_prod_eq_zero (j : ℕ) (N : ℕ) :
    ((Fintype.piFinset (fun _ : Fin j => Finset.Ioo (-N : ℤ) N)).filter
      (fun h : Fin j → ℤ => ∏ i : Fin j, h i = 0)).card ≤
      j * (2 * N) ^ (j - 1) := by
  cases j with
  | zero => simp
  | succ j =>
      let B := Finset.Ioo (-N : ℤ) N
      let Ij1 := Fintype.piFinset (fun _ : Fin (j + 1) => B)
      have hcov : Ij1.filter (fun h => ∏ i : Fin (j + 1), h i = 0) ⊆
          Finset.univ.biUnion (fun i₀ : Fin (j + 1) => Ij1.filter (fun h => h i₀ = 0)) := by
        intro h hh
        simp only [Finset.mem_filter] at hh
        rcases Finset.prod_eq_zero_iff.mp hh.2 with ⟨i₀, _, hi₀⟩
        exact Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hh.1, hi₀⟩⟩
      have hslice : ∀ i₀ : Fin (j + 1),
          (Ij1.filter (fun h => h i₀ = 0)).card ≤ (2 * N) ^ j := by
        intro i₀
        let rest := Fintype.piFinset (fun _ : Fin j => B)
        let ins : (Fin j → ℤ) → (Fin (j + 1) → ℤ) := fun g => Fin.insertNth i₀ 0 g
        have hsub : Ij1.filter (fun h => h i₀ = 0) ⊆ rest.image ins := by
          intro h hh
          simp only [Finset.mem_filter, Ij1, Fintype.mem_piFinset] at hh
          refine Finset.mem_image.mpr ⟨Fin.removeNth i₀ h, ?_, ?_⟩
          · simp only [rest, Fintype.mem_piFinset]
            intro r
            exact hh.1 (i₀.succAbove r)
          · ext t
            dsimp only [ins]
            by_cases ht : t = i₀
            · subst ht
              simpa [Fin.insertNth_apply_same] using hh.2.symm
            · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq ht
              rw [Fin.insertNth_apply_succAbove, Fin.removeNth_apply]
        calc (Ij1.filter (fun h => h i₀ = 0)).card
            ≤ (rest.image ins).card := Finset.card_le_card hsub
          _ ≤ rest.card := Finset.card_image_le
          _ = B.card ^ j := by
              dsimp only [rest]
              rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ (2 * N) ^ j := by
              have hB : B.card ≤ 2 * N := by
                dsimp only [B]
                rw [Int.card_Ioo]
                omega
              exact Nat.pow_le_pow_left hB j
      calc (Ij1.filter (fun h => ∏ i : Fin (j + 1), h i = 0)).card
          ≤ (Finset.univ.biUnion (fun i₀ : Fin (j + 1) =>
              Ij1.filter (fun h => h i₀ = 0))).card := Finset.card_le_card hcov
        _ ≤ ∑ i₀ : Fin (j + 1), (Ij1.filter (fun h => h i₀ = 0)).card := Finset.card_biUnion_le
        _ ≤ ∑ _i₀ : Fin (j + 1), (2 * N) ^ j := Finset.sum_le_sum fun i₀ _ => hslice i₀
        _ = (j + 1) * (2 * N) ^ ((j + 1) - 1) := by
            simp

/-- Partial Hua inequality: for `1 ≤ j ≤ k` and `ε > 0`, the `2^j`-th moment of the
degree-`k` exponential sum over `[1, N]` satisfies
`∫ α in (0 : ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, exp (2πi α n^k)‖ ^ (2 ^ j) ≤ C * N ^ (2^j - j + ε)`. -/
theorem hua_lemma_step {k j : ℕ} (hk : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∫ α in (0 : ℝ)..1,
        ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (2 * Real.pi * (α * (n : ℝ) ^ k) * Complex.I)‖ ^
          (2 ^ j) ≤
        C * (N : ℝ) ^ ((2 ^ j : ℝ) - (j : ℝ) + ε) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hj2
      · refine ⟨1, zero_lt_one, fun N => ?_⟩
        by_cases hN0 : N = 0
        · subst hN0
          simp only [Nat.cast_zero, Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1),
            Finset.sum_empty, norm_zero]
          rw [zero_pow (by norm_num)]
          simp only [intervalIntegral.integral_zero, one_mul]
          exact Real.rpow_nonneg le_rfl _
        · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
          have hrew : ∀ α : ℝ,
              ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (2 * Real.pi * (α * (n : ℝ) ^ k) * Complex.I)‖ ^
                  (2 ^ 1) =
                (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
                  vmvE (α * (((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ))).re := by
            intro α
            rw [pow_one]
            have hT : ∑ n ∈ Finset.Icc 1 N,
                Complex.exp (2 * Real.pi * (α * (n : ℝ) ^ k) * Complex.I) =
                ∑ n ∈ Finset.Icc 1 N, vmvE (α * ((n : ℤ) ^ k : ℝ)) := by
              refine Finset.sum_congr rfl fun n _ => ?_
              simp [vmvE]
            rw [hT]
            have hnorm : ((‖∑ n ∈ Finset.Icc 1 N, vmvE (α * ((n : ℤ) ^ k : ℝ))‖ ^ 2 : ℝ) : ℂ) =
                (∑ n ∈ Finset.Icc 1 N, vmvE (α * ((n : ℤ) ^ k : ℝ))) *
                  star (∑ n ∈ Finset.Icc 1 N, vmvE (α * ((n : ℤ) ^ k : ℝ))) :=
              vmv_norm_sq_eq_mul_star _
            have hmul :
                (∑ n ∈ Finset.Icc 1 N, vmvE (α * ((n : ℤ) ^ k : ℝ))) *
                    star (∑ n ∈ Finset.Icc 1 N, vmvE (α * ((n : ℤ) ^ k : ℝ))) =
                  ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
                    vmvE (α * (((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ)) := by
              rw [star_sum, Finset.sum_mul_sum, Finset.sum_product]
              refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
              rw [star_vmvE, ← vmvE_add]
              congr 1
              push_cast
              ring
            exact congrArg Complex.re (hnorm.trans hmul)
          simp_rw [hrew]
          have hint : IntervalIntegrable
              (fun α : ℝ => ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
                vmvE (α * (((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ)))
              MeasureTheory.volume 0 1 := by
            refine Continuous.intervalIntegrable ?_ 0 1
            refine continuous_finsetSum _ fun p _ => ?_
            exact continuous_vmvE.comp (continuous_id.mul continuous_const)
          rw [vmv_intervalIntegral_re hint]
          have hsum_int : ∀ α : ℝ,
              (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
                vmvE (α * (((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ))) =
              ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
                vmvE ((((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ) * α) := by
            intro α
            refine Finset.sum_congr rfl fun p _ => by rw [mul_comm]
          simp_rw [hsum_int]
          have hint2 : ∀ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
              IntervalIntegrable
                (fun α : ℝ => vmvE ((((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ) * α))
                MeasureTheory.volume 0 1 := fun p _ =>
            Continuous.intervalIntegrable
              (continuous_vmvE.comp (continuous_const.mul continuous_id)) 0 1
          rw [intervalIntegral.integral_finsetSum hint2]
          simp_rw [intervalIntegral_vmvE_int]
          rw [Complex.re_sum]
          have hdiag_le :
              ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
                (if (p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k = 0 then (1 : ℂ) else 0).re ≤ (N : ℝ) := by
            have hfilt :
                ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
                  (fun p : ℕ × ℕ => (p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k = 0)).card = N := by
              have heq : (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
                  (fun p : ℕ × ℕ => (p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k = 0) =
                  (Finset.Icc 1 N).image (fun n => (n, n)) := by
                ext ⟨x, y⟩
                simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image,
                  Finset.mem_Icc, Prod.mk.injEq]
                constructor
                · rintro ⟨⟨hx, hy⟩, hpow⟩
                  have heq_pow : x ^ k = y ^ k := by exact_mod_cast sub_eq_zero.mp hpow
                  have hxy : x = y := Nat.pow_left_injective (by omega : k ≠ 0) heq_pow
                  subst hxy
                  exact ⟨x, hx, rfl, rfl⟩
                · rintro ⟨n, hn, rfl, rfl⟩
                  exact ⟨⟨hn, hn⟩, sub_self _⟩
              rw [heq, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
                Nat.card_Icc]
              omega
            have hsum_eq :
                ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
                    (if (p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k = 0 then (1 : ℂ) else 0).re =
                  (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
                    (fun p : ℕ × ℕ => (p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k = 0)).card : ℝ) := by
              rw [Finset.card_filter, Nat.cast_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              split_ifs <;> simp
            rw [hsum_eq, hfilt]
          have hN_rpow : (N : ℝ) ≤ 1 * (N : ℝ) ^ ((2 ^ 1 : ℝ) - (1 : ℕ) + ε) := by
            rw [one_mul]
            have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
            calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (N : ℝ) ^ ((2 ^ 1 : ℝ) - (1 : ℕ) + ε) :=
                  Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num; linarith [hε])
          exact hdiag_le.trans hN_rpow
      · obtain ⟨j₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        have hj₀1 : 1 ≤ j₀ := by omega
        have hj₀_lt : j₀ < j₀ + 1 := Nat.lt_succ_self j₀
        have hj₀k : j₀ < k := by omega
        obtain ⟨C₀, hC₀_pos, hIH⟩ := ih j₀ hj₀_lt hj₀1 (by omega)
        let δ : ℝ := ε / ((j₀ : ℝ) * (k : ℝ))
        have hδ_pos : 0 < δ := by positivity
        obtain ⟨Cδ, hCδ_pos, hdiv_bd⟩ := vmv_card_divisors_le_rpow hδ_pos
        let C_zero : ℝ := ((j₀ : ℝ) + (k : ℝ)) * (2 : ℝ) ^ j₀ * C₀
        let C_nz_div : ℝ := (k : ℝ) * (2 * Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ)) ^ j₀
        let C : ℝ := (2 : ℝ) ^ (2 ^ j₀ - j₀ - 1) * (C_zero + C_nz_div)
        have hC_pos : 0 < C := by
          have hc0 : 0 < C_zero := by positivity
          have hcnz : 0 ≤ C_nz_div := by positivity
          have hz : 0 < C_zero + C_nz_div := add_pos_of_pos_of_nonneg hc0 hcnz
          have hpow : 0 < (2 : ℝ) ^ (2 ^ j₀ - j₀ - 1) := by positivity
          exact mul_pos hpow hz
        refine ⟨C, hC_pos, fun N => ?_⟩
        by_cases hN0 : N = 0
        · subst hN0
          have hIcc0 : Finset.Icc 1 0 = ∅ := by ext; simp
          simp only [hIcc0, Finset.sum_empty, norm_zero, Nat.cast_zero]
          rw [zero_pow (by positivity)]
          simp only [intervalIntegral.integral_zero]
          positivity
        · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
          have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
          have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
          let T : ℝ → ℂ := fun α =>
            ∑ n ∈ Finset.Icc 1 N, Complex.exp (2 * Real.pi * (α * (n : ℝ) ^ k) * Complex.I)
          let m₀ := 2 ^ (j₀ - 1)
          have hm₀_eq : 2 * m₀ = 2 ^ j₀ := by
            dsimp only [m₀]
            rw [← pow_succ']
            congr 1
            omega
          let S_N := Finset.Icc 1 N
          let Pj := Fintype.piFinset (fun _ : Fin m₀ => S_N)
          let Ij := Fintype.piFinset (fun _ : Fin j₀ => Finset.Ioo (-N : ℤ) N)
          let Q : (Fin j₀ → ℤ) → Polynomial ℤ := fun h => vmvPolyIter j₀ h (Polynomial.X ^ k)
          have hT_pow : ∀ α : ℝ,
              ((‖T α‖ ^ (2 ^ j₀) : ℝ) : ℂ) =
                ∑ x ∈ Pj, ∑ y ∈ Pj,
                  vmvE (α * ((∑ i : Fin m₀, (x i : ℤ) ^ k - ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ) : ℝ)) := by
            intro α
            have hT_eq : T α = ∑ n ∈ S_N, vmvE (α * ((n : ℤ) ^ k : ℝ)) := by
              dsimp only [T, S_N]
              refine Finset.sum_congr rfl fun n _ => ?_
              simp [vmvE]
            have hnorm2 : ((‖T α‖ ^ 2 : ℝ) : ℂ) =
                ∑ p ∈ S_N ×ˢ S_N, vmvE (α * (((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ)) := by
              rw [vmv_norm_sq_eq_mul_star, hT_eq, star_sum, Finset.sum_mul_sum, Finset.sum_product]
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
              rw [star_vmvE, ← vmvE_add]
              congr 1
              push_cast
              ring
            calc ((‖T α‖ ^ (2 ^ j₀) : ℝ) : ℂ)
                = (((‖T α‖ ^ 2 : ℝ) ^ m₀ : ℝ) : ℂ) := by
                    congr 1
                    rw [← pow_mul, hm₀_eq]
              _ = (((‖T α‖ ^ 2 : ℝ) : ℂ)) ^ m₀ := Complex.ofReal_pow _ m₀
              _ = (∑ p ∈ S_N ×ˢ S_N,
                    vmvE (α * (((p.1 : ℤ) ^ k - (p.2 : ℤ) ^ k : ℤ) : ℝ))) ^ m₀ := by
                    rw [hnorm2]
              _ = ∑ x ∈ Pj, ∑ y ∈ Pj,
                    vmvE (α * ((∑ i : Fin m₀, (x i : ℤ) ^ k - ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ) : ℝ)) := by
                    rw [Finset.sum_pow', ← Finset.sum_product']
                    let Qm := Fintype.piFinset (fun _ : Fin m₀ => S_N ×ˢ S_N)
                    let φ : (Fin m₀ → ℕ) × (Fin m₀ → ℕ) → Fin m₀ → ℕ × ℕ :=
                      fun p i => (p.1 i, p.2 i)
                    have hQm : (Pj ×ˢ Pj).image φ = Qm := by
                      ext f
                      simp only [Finset.mem_image, Finset.mem_product, Pj, Qm,
                        Fintype.mem_piFinset, Prod.exists]
                      constructor
                      · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩ i
                        exact ⟨hx i, hy i⟩
                      · intro hf
                        refine ⟨fun i => (f i).1, fun i => (f i).2,
                          ⟨fun i => (hf i).1, fun i => (hf i).2⟩, rfl⟩
                    have hφ_inj : Set.InjOn φ ↑(Pj ×ˢ Pj) := by
                      intro p₁ _ p₂ _ h
                      ext i
                      · exact congrArg (fun g => (g i).1) h
                      · exact congrArg (fun g => (g i).2) h
                    change (∑ p ∈ Qm, _) = _
                    rw [← hQm, Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hφ_inj hp₁ hp₂ h)]
                    refine Finset.sum_congr rfl fun p _ => ?_
                    dsimp only [φ]
                    have hsumE : ∀ g : Fin m₀ → ℝ,
                        (∏ i : Fin m₀, vmvE (g i)) = vmvE (∑ i : Fin m₀, g i) := by
                      intro g
                      induction Finset.univ (α := Fin m₀) using Finset.induction_on with
                      | empty => simp [vmvE_zero]
                      | insert a t ha ih' =>
                          rw [Finset.prod_insert ha, Finset.sum_insert ha, vmvE_add, ih']
                    rw [hsumE]
                    congr 1
                    push_cast
                    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          have hpointwise : ∀ α : ℝ,
              ‖T α‖ ^ (2 ^ (j₀ + 1)) ≤
                (2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) *
                  (∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj,
                    vmvE (α * ((((Q h).eval n + ∑ i : Fin m₀, (x i : ℤ) ^ k -
                      ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ)) : ℝ))).re := by
            intro α
            have hT_eq : T α = ∑ n ∈ Finset.Icc (1 : ℤ) N,
                vmvE (α * (((Polynomial.X ^ k : Polynomial ℤ).eval n : ℤ) : ℝ)) := by
              dsimp only [T]
              refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) (fun n : ℤ => n.toNat)
                (fun n hn => by
                  simp only [Finset.mem_Icc] at hn ⊢
                  omega)
                (fun n hn => by
                  simp only [Finset.mem_Icc] at hn ⊢
                  omega)
                (fun n _ => Int.toNat_natCast n)
                (fun n hn => by
                  simp only [Finset.mem_Icc] at hn
                  omega)
                (fun n hn => by
                  simp only [Finset.mem_Icc] at hn
                  simp [vmvE])
            have hweyl := vmv_weyl_squaring_ineq (Polynomial.X ^ k) α j₀ hj₀1 N hN1
            rw [← hT_eq] at hweyl
            have hpow_split : ‖T α‖ ^ (2 ^ (j₀ + 1)) = ‖T α‖ ^ (2 ^ j₀) * ‖T α‖ ^ (2 ^ j₀) := by
              rw [← pow_add]
              congr 1
              omega
            have hmul_weyl :
                ‖T α‖ ^ (2 ^ (j₀ + 1)) ≤
                  (2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) *
                    ((∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N,
                      vmvE (α * (((Q h).eval n : ℤ) : ℝ))).re * ‖T α‖ ^ (2 ^ j₀)) := by
              rw [hpow_split]
              calc ‖T α‖ ^ (2 ^ j₀) * ‖T α‖ ^ (2 ^ j₀)
                  ≤ ((2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) *
                      (∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N,
                        vmvE (α * (((Q h).eval n : ℤ) : ℝ))).re) * ‖T α‖ ^ (2 ^ j₀) :=
                      mul_le_mul_of_nonneg_right hweyl (by positivity)
                _ = _ := by ring
            have hre_mul :
                (∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N,
                    vmvE (α * (((Q h).eval n : ℤ) : ℝ))).re * ‖T α‖ ^ (2 ^ j₀) =
                  (∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj,
                    vmvE (α * ((((Q h).eval n + ∑ i : Fin m₀, (x i : ℤ) ^ k -
                      ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ)) : ℝ))).re := by
              have h1 : ∀ z : ℂ, z.re * ‖T α‖ ^ (2 ^ j₀) =
                  (z * ((‖T α‖ ^ (2 ^ j₀) : ℝ) : ℂ)).re := by
                intro z
                rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
              rw [h1, hT_pow α]
              congr 1
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun h _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [← vmvE_add]
              congr 1
              push_cast
              ring
            rw [hre_mul] at hmul_weyl
            exact hmul_weyl
          let F_sum : ℝ → ℂ := fun α =>
            ∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj,
              vmvE (α * (((Q h).eval n + ∑ i : Fin m₀, (x i : ℤ) ^ k -
                ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ) : ℝ))
          have hT_cont : Continuous T := by
            dsimp only [T]
            refine continuous_finsetSum _ fun n _ => ?_
            exact Complex.continuous_exp.comp
              (((continuous_const.mul (continuous_ofReal.mul continuous_const)).mul
                continuous_const))
          have hint_T : IntervalIntegrable (fun α : ℝ => ‖T α‖ ^ (2 ^ (j₀ + 1)))
              MeasureTheory.volume 0 1 :=
            Continuous.intervalIntegrable ((continuous_norm.comp hT_cont).pow _) 0 1
          have hint_F : IntervalIntegrable (fun α : ℝ => (2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) *
              (F_sum α).re) MeasureTheory.volume 0 1 := by
            refine Continuous.intervalIntegrable ?_ 0 1
            refine continuous_const.mul (Complex.continuous_re.comp ?_)
            refine continuous_finsetSum Ij fun h _ => continuous_finsetSum (vmvWeylDom j₀ h N) fun n _ =>
              continuous_finsetSum Pj fun x _ => continuous_finsetSum Pj fun y _ => ?_
            exact continuous_vmvE.comp (continuous_id.mul continuous_const)
          have hint_F_C : IntervalIntegrable F_sum MeasureTheory.volume 0 1 := by
            refine Continuous.intervalIntegrable ?_ 0 1
            refine continuous_finsetSum Ij fun h _ => continuous_finsetSum (vmvWeylDom j₀ h N) fun n _ =>
              continuous_finsetSum Pj fun x _ => continuous_finsetSum Pj fun y _ => ?_
            exact continuous_vmvE.comp (continuous_id.mul continuous_const)
          have hint_mono :
              ∫ α in (0 : ℝ)..1, ‖T α‖ ^ (2 ^ (j₀ + 1)) ≤
                (2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) * (∫ α in (0 : ℝ)..1, F_sum α).re := by
            have hm := intervalIntegral.integral_mono_on zero_le_one hint_T hint_F
              fun α _ => hpointwise α
            rw [intervalIntegral.integral_const_mul, vmv_intervalIntegral_re hint_F_C]
              at hm
            exact hm
          let ind : (Fin j₀ → ℤ) → ℤ → (Fin m₀ → ℕ) → (Fin m₀ → ℕ) → ℝ := fun h n x y =>
            if (Q h).eval n = ∑ i : Fin m₀, (y i : ℤ) ^ k - ∑ i : Fin m₀, (x i : ℤ) ^ k
            then 1 else 0
          have hF_eval : (∫ α in (0 : ℝ)..1, F_sum α).re =
              ∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y := by
            dsimp only [F_sum]
            have hrew_F : ∀ α : ℝ,
                (∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj,
                  vmvE (α * (((Q h).eval n + ∑ i : Fin m₀, (x i : ℤ) ^ k -
                    ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ) : ℝ))) =
                ∑ p ∈ (Ij ×ˢ Finset.Icc (1 : ℤ) N) ×ˢ (Pj ×ˢ Pj),
                  if p.1.2 ∈ vmvWeylDom j₀ p.1.1 N then
                    vmvE ((((Q p.1.1).eval p.1.2 + ∑ i : Fin m₀, (p.2.1 i : ℤ) ^ k -
                      ∑ i : Fin m₀, (p.2.2 i : ℤ) ^ k : ℤ) : ℝ) * α)
                  else (0 : ℂ) := by
              intro α
              simp_rw [Finset.sum_product]
              refine Finset.sum_congr rfl fun h _ => ?_
              have hsum_if : ∀ n : ℤ,
                  (∑ x ∈ Pj, ∑ y ∈ Pj,
                    if n ∈ vmvWeylDom j₀ h N then
                      vmvE ((((Q h).eval n + ∑ i : Fin m₀, (x i : ℤ) ^ k -
                        ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ) : ℝ) * α)
                    else (0 : ℂ)) =
                  if n ∈ vmvWeylDom j₀ h N then
                    ∑ x ∈ Pj, ∑ y ∈ Pj,
                      vmvE ((((Q h).eval n + ∑ i : Fin m₀, (x i : ℤ) ^ k -
                        ∑ i : Fin m₀, (y i : ℤ) ^ k : ℤ) : ℝ) * α)
                  else 0 := fun n => by split_ifs <;> simp
              simp_rw [hsum_if]
              rw [← Finset.sum_filter]
              have hfilt_eq : (Finset.Icc (1 : ℤ) N).filter (fun n => n ∈ vmvWeylDom j₀ h N) =
                  vmvWeylDom j₀ h N := by
                ext n
                simp only [Finset.mem_filter, and_iff_right_iff_imp]
                exact fun hn => vmvWeylDom_subset_Icc j₀ h N hn
              rw [hfilt_eq]
              refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ =>
                Finset.sum_congr rfl fun y _ => ?_
              rw [mul_comm]
            have hint_term : ∀ p ∈ (Ij ×ˢ Finset.Icc (1 : ℤ) N) ×ˢ (Pj ×ˢ Pj),
                IntervalIntegrable (fun α : ℝ =>
                  if p.1.2 ∈ vmvWeylDom j₀ p.1.1 N then
                    vmvE ((((Q p.1.1).eval p.1.2 + ∑ i : Fin m₀, (p.2.1 i : ℤ) ^ k -
                      ∑ i : Fin m₀, (p.2.2 i : ℤ) ^ k : ℤ) : ℝ) * α)
                  else (0 : ℂ)) MeasureTheory.volume 0 1 := by
              intro p _
              split_ifs
              · exact Continuous.intervalIntegrable
                  (continuous_vmvE.comp (continuous_const.mul continuous_id)) 0 1
              · exact intervalIntegrable_const
            simp_rw [hrew_F]
            rw [intervalIntegral.integral_finsetSum hint_term, Complex.re_sum]
            have heval_term : ∀ p ∈ (Ij ×ˢ Finset.Icc (1 : ℤ) N) ×ˢ (Pj ×ˢ Pj),
                (∫ α in (0 : ℝ)..1,
                  if p.1.2 ∈ vmvWeylDom j₀ p.1.1 N then
                    vmvE ((((Q p.1.1).eval p.1.2 + ∑ i : Fin m₀, (p.2.1 i : ℤ) ^ k -
                      ∑ i : Fin m₀, (p.2.2 i : ℤ) ^ k : ℤ) : ℝ) * α)
                  else (0 : ℂ)).re =
                  if p.1.2 ∈ vmvWeylDom j₀ p.1.1 N then ind p.1.1 p.1.2 p.2.1 p.2.2 else 0 := by
              intro p _
              split_ifs with hmem
              · rw [intervalIntegral_vmvE_int]
                have hiff : (Q p.1.1).eval p.1.2 + ∑ i : Fin m₀, (p.2.1 i : ℤ) ^ k -
                      ∑ i : Fin m₀, (p.2.2 i : ℤ) ^ k = 0 ↔
                    (Q p.1.1).eval p.1.2 =
                      ∑ i : Fin m₀, (p.2.2 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2.1 i : ℤ) ^ k := by
                  omega
                dsimp only [ind]
                by_cases h1 : (Q p.1.1).eval p.1.2 + ∑ i : Fin m₀, (p.2.1 i : ℤ) ^ k -
                    ∑ i : Fin m₀, (p.2.2 i : ℤ) ^ k = 0
                · simp [hiff.mp h1]
                · simp [h1, show (Q p.1.1).eval p.1.2 ≠
                      ∑ i : Fin m₀, (p.2.2 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2.1 i : ℤ) ^ k from
                      fun h2 => h1 (hiff.mpr h2)]
              · simp
            calc ∑ p ∈ (Ij ×ˢ Finset.Icc (1 : ℤ) N) ×ˢ (Pj ×ˢ Pj),
                    (∫ α in (0 : ℝ)..1,
                      if p.1.2 ∈ vmvWeylDom j₀ p.1.1 N then _ else (0 : ℂ)).re
                = ∑ p ∈ (Ij ×ˢ Finset.Icc (1 : ℤ) N) ×ˢ (Pj ×ˢ Pj),
                    if p.1.2 ∈ vmvWeylDom j₀ p.1.1 N then
                      ind p.1.1 p.1.2 p.2.1 p.2.2
                    else 0 := Finset.sum_congr rfl heval_term
              _ = ∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y := by
                  simp_rw [Finset.sum_product]
                  refine Finset.sum_congr rfl fun h _ => ?_
                  have hsum_if : ∀ n : ℤ,
                      (∑ x ∈ Pj, ∑ y ∈ Pj, if n ∈ vmvWeylDom j₀ h N then ind h n x y else 0) =
                        if n ∈ vmvWeylDom j₀ h N then ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y else 0 :=
                    fun n => by split_ifs <;> simp
                  simp_rw [hsum_if]
                  rw [← Finset.sum_filter]
                  have hfilt_eq : (Finset.Icc (1 : ℤ) N).filter (fun n => n ∈ vmvWeylDom j₀ h N) =
                      vmvWeylDom j₀ h N := by
                    ext n
                    simp only [Finset.mem_filter, and_iff_right_iff_imp]
                    exact fun hn => vmvWeylDom_subset_Icc j₀ h N hn
                  rw [hfilt_eq]
          let m_xy : (Fin m₀ → ℕ) × (Fin m₀ → ℕ) → ℤ :=
            fun p => ∑ i : Fin m₀, (p.2 i : ℤ) ^ k - ∑ i : Fin m₀, (p.1 i : ℤ) ^ k
          have hswap :
              ∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y ≤
                (∑ p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p = 0),
                    ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      if (Q h).eval n = 0 then (1 : ℝ) else 0) +
                (∑ p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0),
                    ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      if (Q h).eval n = m_xy p then (1 : ℝ) else 0) := by
            have hle1 :
                ∑ h ∈ Ij, ∑ n ∈ vmvWeylDom j₀ h N, ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y ≤
                  ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N, ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y := by
              refine Finset.sum_le_sum fun h _ => Finset.sum_le_sum_of_subset_of_nonneg
                (vmvWeylDom_subset_Icc j₀ h N) fun _ _ _ => ?_
              exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
                dsimp only [ind]; split_ifs <;> norm_num
            have hswap_eq :
                ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N, ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y =
                  ∑ p ∈ Pj ×ˢ Pj, ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    if (Q h).eval n = m_xy p then (1 : ℝ) else 0 := by
              calc ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N, ∑ x ∈ Pj, ∑ y ∈ Pj, ind h n x y
                  = ∑ hn ∈ Ij ×ˢ Finset.Icc (1 : ℤ) N, ∑ p ∈ Pj ×ˢ Pj, ind hn.1 hn.2 p.1 p.2 := by
                      rw [Finset.sum_product]
                      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun n _ => ?_
                      rw [Finset.sum_product]
                _ = ∑ p ∈ Pj ×ˢ Pj, ∑ hn ∈ Ij ×ˢ Finset.Icc (1 : ℤ) N, ind hn.1 hn.2 p.1 p.2 :=
                      Finset.sum_comm
                _ = ∑ p ∈ Pj ×ˢ Pj, ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      if (Q h).eval n = m_xy p then (1 : ℝ) else 0 := by
                      refine Finset.sum_congr rfl fun p _ => ?_
                      rw [Finset.sum_product]
            rw [← Finset.sum_filter_add_sum_filter_not (Pj ×ˢ Pj) (fun p => m_xy p = 0)] at hswap_eq
            have hcongr0 :
                ∑ p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p = 0),
                    ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) =
                  ∑ p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p = 0),
                    ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      if (Q h).eval n = 0 then (1 : ℝ) else 0 := by
              refine Finset.sum_congr rfl fun p hp => ?_
              rw [(Finset.mem_filter.mp hp).2]
            rw [hcongr0] at hswap_eq
            exact hle1.trans_eq hswap_eq
          have hdiag_hn :
              ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = 0 then (1 : ℝ) else 0) ≤
                ((j₀ : ℝ) + (k : ℝ)) * (2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀ := by
            let Ij0 := Ij.filter (fun h => ∏ i : Fin j₀, h i = 0)
            let Ij1 := Ij.filter (fun h => ∏ i : Fin j₀, h i ≠ 0)
            rw [← Finset.sum_filter_add_sum_filter_not Ij (fun h => ∏ i : Fin j₀, h i = 0)]
            have hpart1 :
                ∑ h ∈ Ij0, ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = 0 then (1 : ℝ) else 0) ≤
                  (j₀ : ℝ) * (2 * (N : ℝ)) ^ (j₀ - 1) * (N : ℝ) := by
              have hterm : ∀ h ∈ Ij0,
                  ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = 0 then (1 : ℝ) else 0) ≤
                    (N : ℝ) := by
                intro h _
                calc ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = 0 then (1 : ℝ) else 0)
                    ≤ ∑ _n ∈ Finset.Icc (1 : ℤ) N, (1 : ℝ) := by
                        refine Finset.sum_le_sum fun n _ => ?_
                        split_ifs <;> norm_num
                  _ = ((Finset.Icc (1 : ℤ) N).card : ℝ) := by simp
                  _ = (N : ℝ) := by
                        rw [Int.card_Icc]
                        have hsub : ((N : ℤ) + 1 - 1).toNat = N := by omega
                        rw [hsub]
              have hcard_le : (Ij0.card : ℝ) ≤ (j₀ : ℝ) * (2 * (N : ℝ)) ^ (j₀ - 1) := by
                have h := card_piFinset_prod_eq_zero j₀ N
                exact_mod_cast h
              calc ∑ h ∈ Ij0, _ ≤ ∑ _h ∈ Ij0, (N : ℝ) := Finset.sum_le_sum hterm
                _ = (Ij0.card : ℝ) * (N : ℝ) := by simp
                _ ≤ ((j₀ : ℝ) * (2 * (N : ℝ)) ^ (j₀ - 1)) * (N : ℝ) :=
                    mul_le_mul_of_nonneg_right hcard_le (Nat.cast_nonneg N)
            have hpart2 :
                ∑ h ∈ Ij1, ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = 0 then (1 : ℝ) else 0) ≤
                  (k : ℝ) * (2 * (N : ℝ)) ^ j₀ := by
              have hterm : ∀ h ∈ Ij1,
                  ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = 0 then (1 : ℝ) else 0) ≤
                    (k : ℝ) := by
                intro h hh
                have hprod_ne : (∏ i : Fin j₀, h i) ≠ 0 := (Finset.mem_filter.mp hh).2
                have hdeg_lc := @vmvPolyIter_X_pow_natDegree_and_leadingCoeff k j₀ hj₀k.le h hprod_ne
                have hQ_ne : Q h ≠ 0 := by
                  intro h0
                  have hlc : (Q h).leadingCoeff = 0 := by simp [h0]
                  rw [hdeg_lc.2] at hlc
                  have hdf : Nat.descFactorial k j₀ ≠ 0 :=
                    (Nat.descFactorial_pos.mpr (by omega : j₀ ≤ k)).ne'
                  exact mul_ne_zero (by exact_mod_cast hdf) hprod_ne hlc
                have hroots := vmv_card_roots_Icc_le hQ_ne N
                have hdeg_le : (Q h).natDegree ≤ k := by
                  dsimp only [Q]
                  rw [hdeg_lc.1]
                  exact Nat.sub_le k j₀
                have hsum_card :
                    ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = 0 then (1 : ℝ) else 0) =
                      (((Finset.Icc (1 : ℤ) N).filter (fun n => (Q h).eval n = 0)).card : ℝ) := by
                  rw [Finset.card_filter, Nat.cast_sum]
                  refine Finset.sum_congr rfl fun n _ => ?_
                  split_ifs <;> simp
                rw [hsum_card]
                exact_mod_cast hroots.trans hdeg_le
              have hcard_le : (Ij1.card : ℝ) ≤ (2 * (N : ℝ)) ^ j₀ := by
                have h1 : Ij1.card ≤ Ij.card := Finset.card_filter_le _ _
                have hc : Ij.card = (Finset.Ioo (-N : ℤ) N).card ^ j₀ := by
                  dsimp only [Ij]
                  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                have hB : (Finset.Ioo (-N : ℤ) N).card ≤ 2 * N := by
                  rw [Int.card_Ioo]; omega
                have h2 : Ij1.card ≤ (2 * N) ^ j₀ :=
                  h1.trans (hc ▸ Nat.pow_le_pow_left hB j₀)
                exact_mod_cast h2
              calc ∑ h ∈ Ij1, _ ≤ ∑ _h ∈ Ij1, (k : ℝ) := Finset.sum_le_sum hterm
                _ = (Ij1.card : ℝ) * (k : ℝ) := by simp
                _ ≤ (2 * (N : ℝ)) ^ j₀ * (k : ℝ) :=
                    mul_le_mul_of_nonneg_right hcard_le (Nat.cast_nonneg k)
                _ = (k : ℝ) * (2 * (N : ℝ)) ^ j₀ := mul_comm _ _
            have hpow_rewrite : (2 * (N : ℝ)) ^ (j₀ - 1) * (N : ℝ) ≤
                (2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀ := by
              rw [mul_pow]
              have hNpow : (N : ℝ) ^ (j₀ - 1) * (N : ℝ) = (N : ℝ) ^ j₀ := by
                conv_rhs => rw [show j₀ = (j₀ - 1) + 1 by omega]
                rw [pow_succ]
              have h2pow : (2 : ℝ) ^ (j₀ - 1) ≤ (2 : ℝ) ^ j₀ :=
                pow_le_pow_right₀ one_le_two (Nat.sub_le j₀ 1)
              calc (2 : ℝ) ^ (j₀ - 1) * (N : ℝ) ^ (j₀ - 1) * (N : ℝ)
                  = (2 : ℝ) ^ (j₀ - 1) * ((N : ℝ) ^ (j₀ - 1) * (N : ℝ)) := by ring
                _ = (2 : ℝ) ^ (j₀ - 1) * (N : ℝ) ^ j₀ := by rw [hNpow]
                _ ≤ (2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀ :=
                    mul_le_mul_of_nonneg_right h2pow (by positivity)
            calc ∑ h ∈ Ij0, _ + ∑ h ∈ Ij1, _
                ≤ (j₀ : ℝ) * ((2 * (N : ℝ)) ^ (j₀ - 1) * (N : ℝ)) + (k : ℝ) * (2 * (N : ℝ)) ^ j₀ := by
                    have := add_le_add hpart1 hpart2
                    linarith only [this]
              _ ≤ (j₀ : ℝ) * ((2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀) + (k : ℝ) * ((2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀) := by
                    have h1 : (j₀ : ℝ) * ((2 * (N : ℝ)) ^ (j₀ - 1) * (N : ℝ)) ≤
                        (j₀ : ℝ) * ((2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀) :=
                      mul_le_mul_of_nonneg_left hpow_rewrite (Nat.cast_nonneg j₀)
                    have h2 : (k : ℝ) * (2 * (N : ℝ)) ^ j₀ =
                        (k : ℝ) * ((2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀) := by rw [mul_pow]
                    linarith only [h1, h2]
              _ = ((j₀ : ℝ) + (k : ℝ)) * (2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀ := by ring
          have hdiag_xy :
              (((Pj ×ˢ Pj).filter (fun p => m_xy p = 0)).card : ℝ) ≤
                C₀ * (N : ℝ) ^ ((2 ^ j₀ : ℝ) - (j₀ : ℝ) + ε) := by
            have hT_int_eq :
                (((Pj ×ˢ Pj).filter (fun p => m_xy p = 0)).card : ℝ) =
                  ∫ α in (0 : ℝ)..1, ‖T α‖ ^ (2 ^ j₀) := by
              have hint_Tj : IntervalIntegrable
                  (fun α : ℝ => ∑ p ∈ Pj ×ˢ Pj,
                    vmvE (α * ((∑ i : Fin m₀, (p.1 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2 i : ℤ) ^ k : ℤ) : ℝ)))
                  MeasureTheory.volume 0 1 := by
                refine Continuous.intervalIntegrable ?_ 0 1
                refine continuous_finsetSum _ fun p _ => ?_
                exact continuous_vmvE.comp (continuous_id.mul continuous_const)
              have hre_T : ∀ α : ℝ, ‖T α‖ ^ (2 ^ j₀) =
                  (∑ p ∈ Pj ×ˢ Pj,
                    vmvE (α * ((∑ i : Fin m₀, (p.1 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2 i : ℤ) ^ k : ℤ) : ℝ))).re := by
                intro α
                have hc := congrArg Complex.re (hT_pow α)
                simp only [Complex.ofReal_re] at hc
                rw [hc, Finset.sum_product]
              simp_rw [hre_T]
              rw [vmv_intervalIntegral_re hint_Tj]
              have hswap_α : (fun α : ℝ => ∑ p ∈ Pj ×ˢ Pj,
                  vmvE (α * ((∑ i : Fin m₀, (p.1 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2 i : ℤ) ^ k : ℤ) : ℝ))) =
                  fun α : ℝ => ∑ p ∈ Pj ×ˢ Pj,
                    vmvE ((((∑ i : Fin m₀, (p.1 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2 i : ℤ) ^ k : ℤ) : ℝ)) * α) := by
                ext α
                refine Finset.sum_congr rfl fun p _ => by rw [mul_comm]
              have hint_prod : ∀ p ∈ Pj ×ˢ Pj, IntervalIntegrable
                  (fun α : ℝ =>
                    vmvE ((((∑ i : Fin m₀, (p.1 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2 i : ℤ) ^ k : ℤ) : ℝ)) * α))
                  MeasureTheory.volume 0 1 := fun p _ =>
                Continuous.intervalIntegrable
                  (continuous_vmvE.comp (continuous_const.mul continuous_id)) 0 1
              rw [hswap_α, intervalIntegral.integral_finsetSum hint_prod]
              simp_rw [intervalIntegral_vmvE_int, Complex.re_sum]
              rw [Finset.card_filter, Nat.cast_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              have hiff : ∑ i : Fin m₀, (p.1 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2 i : ℤ) ^ k = 0 ↔
                  m_xy p = 0 := by
                dsimp only [m_xy]
                omega
              by_cases h1 : ∑ i : Fin m₀, (p.1 i : ℤ) ^ k - ∑ i : Fin m₀, (p.2 i : ℤ) ^ k = 0
              · simp [h1, hiff.mp h1]
              · simp [h1, show m_xy p ≠ 0 from fun h2 => h1 (hiff.mpr h2)]
            rw [hT_int_eq]
            exact hIH N
          have hnz_term : ∀ p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0),
              ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) ≤
                C_nz_div * (N : ℝ) ^ ε := by
            intro p hp
            have hm_ne : m_xy p ≠ 0 := (Finset.mem_filter.mp hp).2
            have hp_mem : p ∈ Pj ×ˢ Pj := (Finset.mem_filter.mp hp).1
            have hm_nat_le : (m_xy p).natAbs ≤ m₀ * N ^ k := by
              have hp1 := Finset.mem_product.mp hp_mem
              have hb1 : ∀ g ∈ Pj, ∑ i : Fin m₀, (g i : ℤ) ^ k ≤ ((m₀ * N ^ k : ℕ) : ℤ) := by
                intro g hg
                simp only [Pj, Fintype.mem_piFinset, S_N, Finset.mem_Icc] at hg
                calc ∑ i : Fin m₀, (g i : ℤ) ^ k
                    ≤ ∑ _i : Fin m₀, (N : ℤ) ^ k := by
                        refine Finset.sum_le_sum fun i _ => ?_
                        exact pow_le_pow_left₀ (Nat.cast_nonneg _)
                          (by exact_mod_cast (hg i).2) k
                  _ = ((m₀ * N ^ k : ℕ) : ℤ) := by simp [mul_comm]
              have h01 : 0 ≤ ∑ i : Fin m₀, (p.1 i : ℤ) ^ k :=
                Finset.sum_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) k
              have h02 : 0 ≤ ∑ i : Fin m₀, (p.2 i : ℤ) ^ k :=
                Finset.sum_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) k
              have hbd1 := hb1 p.1 hp1.1
              have hbd2 := hb1 p.2 hp1.2
              have habs : |m_xy p| ≤ ((m₀ * N ^ k : ℕ) : ℤ) := by
                dsimp only [m_xy]
                rw [abs_le]
                constructor <;> linarith only [h01, h02, hbd1, hbd2]
              exact Int.ofNat_le.mp (Int.abs_eq_natAbs _ ▸ habs)
            have hm_nat_pos : 1 ≤ (m_xy p).natAbs := Int.natAbs_pos.mpr hm_ne
            have hdiv_rpow :
                ((m_xy p).natAbs.divisors.card : ℝ) ≤
                  Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ) * (N : ℝ) ^ ((k : ℝ) * δ) := by
              have h1 := hdiv_bd (m_xy p).natAbs hm_nat_pos
              have h2 : ((m_xy p).natAbs : ℝ) ≤ (m₀ : ℝ) * (N : ℝ) ^ k := by
                exact_mod_cast hm_nat_le
              have hm₀_le : (m₀ : ℝ) ≤ (2 : ℝ) ^ ((j₀ : ℝ) - 1) := by
                dsimp only [m₀]
                push_cast
                rw [← Real.rpow_natCast (2 : ℝ) (j₀ - 1), Nat.cast_sub hj₀1, Nat.cast_one]
              have h3 : ((m_xy p).natAbs : ℝ) ^ δ ≤
                  ((2 : ℝ) ^ ((j₀ : ℝ) - 1) * (N : ℝ) ^ (k : ℝ)) ^ δ := by
                refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hδ_pos.le
                calc ((m_xy p).natAbs : ℝ) ≤ (m₀ : ℝ) * (N : ℝ) ^ k := h2
                  _ ≤ (2 : ℝ) ^ ((j₀ : ℝ) - 1) * (N : ℝ) ^ k :=
                      mul_le_mul_of_nonneg_right hm₀_le (by positivity)
                  _ = (2 : ℝ) ^ ((j₀ : ℝ) - 1) * (N : ℝ) ^ (k : ℝ) := by
                      rw [Real.rpow_natCast]
              have h4 : ((2 : ℝ) ^ ((j₀ : ℝ) - 1) * (N : ℝ) ^ (k : ℝ)) ^ δ =
                  (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ) * (N : ℝ) ^ ((k : ℝ) * δ) := by
                rw [Real.mul_rpow (by positivity) (by positivity),
                  ← Real.rpow_mul zero_le_two, ← Real.rpow_mul hNR.le]
              calc ((m_xy p).natAbs.divisors.card : ℝ) ≤ Cδ * ((m_xy p).natAbs : ℝ) ^ δ := h1
                _ ≤ Cδ * ((2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ) * (N : ℝ) ^ ((k : ℝ) * δ)) :=
                    mul_le_mul_of_nonneg_left (h3.trans_eq h4) hCδ_pos.le
                _ = Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ) * (N : ℝ) ^ ((k : ℝ) * δ) := by ring
            have hfilter_h :
                ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) =
                  ∑ h ∈ Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p),
                    ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun h _ => ?_
              split_ifs with hdvd
              · rfl
              · refine Finset.sum_eq_zero fun n _ => ?_
                have hndvd := eval_prod_dvd_vmvPolyIter j₀ h (Polynomial.X ^ k) n
                have hne_eval : (Q h).eval n ≠ m_xy p := fun heq =>
                  hdvd (heq ▸ hndvd)
                simp [hne_eval]
            have hterm_n : ∀ h ∈ Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p),
                ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) ≤
                  (k : ℝ) := by
              intro h hh
              have hprod_ne : (∏ i : Fin j₀, h i) ≠ 0 := by
                intro h0
                have h0dvd := (Finset.mem_filter.mp hh).2
                rw [h0] at h0dvd
                exact hm_ne (zero_dvd_iff.mp h0dvd)
              have hdeg_lc := @vmvPolyIter_X_pow_natDegree_and_leadingCoeff k j₀ hj₀k.le h hprod_ne
              let Qm := Q h - Polynomial.C (m_xy p)
              have hdeg_Qm : Qm.natDegree = (Q h).natDegree := by
                have hdeg1 : 1 ≤ (Q h).natDegree := by
                  dsimp only [Q]; rw [hdeg_lc.1]; omega
                refine Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_
                rw [Polynomial.natDegree_C]
                exact hdeg1
              have hQm_deg_pos : 0 < Qm.natDegree := by
                rw [hdeg_Qm]; dsimp only [Q]; rw [hdeg_lc.1]; omega
              have hQm_ne : Qm ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hQm_deg_pos
              have hroots := vmv_card_roots_Icc_le hQm_ne N
              have hsum_card :
                  ∑ n ∈ Finset.Icc (1 : ℤ) N, (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) =
                    (((Finset.Icc (1 : ℤ) N).filter (fun n => Qm.eval n = 0)).card : ℝ) := by
                rw [Finset.card_filter, Nat.cast_sum]
                refine Finset.sum_congr rfl fun n _ => ?_
                have hev : Qm.eval n = 0 ↔ (Q h).eval n = m_xy p := by
                  dsimp only [Qm]
                  simp [sub_eq_zero]
                split_ifs with h1 h2 h2
                · simp
                · exact False.elim (h2 (hev.mpr h1))
                · exact False.elim (h1 (hev.mp h2))
                · simp
              rw [hsum_card]
              have hdeg_le : Qm.natDegree ≤ k := by
                rw [hdeg_Qm]; dsimp only [Q]; rw [hdeg_lc.1]; exact Nat.sub_le k j₀
              exact_mod_cast hroots.trans hdeg_le
            have hcard_h :
                ((Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p)).card : ℝ) ≤
                  (2 * Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ)) ^ j₀ * (N : ℝ) ^ ε := by
              have hc := card_piFinset_int_divisors j₀ N hm_ne
              have hcR : ((Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p)).card : ℝ) ≤
                  (2 * ((m_xy p).natAbs.divisors.card : ℝ)) ^ j₀ := by
                exact_mod_cast hc
              have hpow_le : (2 * ((m_xy p).natAbs.divisors.card : ℝ)) ^ j₀ ≤
                  (2 * (Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ) * (N : ℝ) ^ ((k : ℝ) * δ))) ^ j₀ :=
                pow_le_pow_left₀ (by positivity)
                  (mul_le_mul_of_nonneg_left hdiv_rpow zero_le_two) j₀
              have hrpow_j₀ : ((N : ℝ) ^ ((k : ℝ) * δ)) ^ j₀ = (N : ℝ) ^ ε := by
                rw [← Real.rpow_natCast ((N : ℝ) ^ ((k : ℝ) * δ)) j₀, ← Real.rpow_mul hNR.le]
                congr 1
                dsimp only [δ]
                have hj0 : (j₀ : ℝ) ≠ 0 := by exact_mod_cast (by omega : j₀ ≠ 0)
                have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
                field_simp [hj0, hk0]
              calc ((Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p)).card : ℝ)
                  ≤ (2 * ((m_xy p).natAbs.divisors.card : ℝ)) ^ j₀ := hcR
                _ ≤ (2 * (Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ) * (N : ℝ) ^ ((k : ℝ) * δ))) ^ j₀ :=
                    hpow_le
                _ = (2 * Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ)) ^ j₀ *
                      ((N : ℝ) ^ ((k : ℝ) * δ)) ^ j₀ := by rw [mul_pow]; ring
                _ = _ := by rw [hrpow_j₀]
            calc ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    (if (Q h).eval n = m_xy p then (1 : ℝ) else 0)
                = ∑ h ∈ Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p),
                    ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) := hfilter_h
              _ ≤ ∑ _h ∈ Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p), (k : ℝ) :=
                  Finset.sum_le_sum hterm_n
              _ = ((Ij.filter (fun h => (∏ i : Fin j₀, h i) ∣ m_xy p)).card : ℝ) * (k : ℝ) := by
                  simp
              _ ≤ ((2 * Cδ * (2 : ℝ) ^ (((j₀ : ℝ) - 1) * δ)) ^ j₀ * (N : ℝ) ^ ε) * (k : ℝ) :=
                  mul_le_mul_of_nonneg_right hcard_h (Nat.cast_nonneg k)
              _ = C_nz_div * (N : ℝ) ^ ε := by dsimp only [C_nz_div]; ring
          have hPj_card : (((Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0)).card : ℝ) ≤ (N : ℝ) ^ (2 ^ j₀) := by
            have h1 : ((Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0)).card ≤ (Pj ×ˢ Pj).card :=
              Finset.card_filter_le _ _
            have h2 : (Pj ×ˢ Pj).card = S_N.card ^ (2 * m₀) := by
              rw [Finset.card_product]
              have hPj : Pj.card = S_N.card ^ m₀ := by
                dsimp only [Pj]
                rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              rw [hPj, ← pow_add, ← two_mul]
            have hS : S_N.card = N := by
              dsimp only [S_N]
              rw [Nat.card_Icc]
              omega
            rw [hS, hm₀_eq] at h2
            exact_mod_cast h1.trans_eq h2
          have hsum_0_bound :
              (∑ _p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p = 0),
                  ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    if (Q h).eval n = 0 then (1 : ℝ) else 0) ≤
                C_zero * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) := by
            have h1 : ∑ _p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p = 0),
                  ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    (if (Q h).eval n = 0 then (1 : ℝ) else 0) =
                (((Pj ×ˢ Pj).filter (fun p => m_xy p = 0)).card : ℝ) *
                  ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    (if (Q h).eval n = 0 then (1 : ℝ) else 0) := by
              simp
            have hhn_nn : 0 ≤ ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                (if (Q h).eval n = 0 then (1 : ℝ) else 0) :=
              Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
            have hprod := mul_le_mul hdiag_xy hdiag_hn hhn_nn (by positivity)
            have hexp : (N : ℝ) ^ ((2 ^ j₀ : ℝ) - (j₀ : ℝ) + ε) * (N : ℝ) ^ j₀ =
                (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) := by
              rw [← Real.rpow_natCast (N : ℝ) j₀, ← Real.rpow_add hNR]
              congr 1
              ring
            calc _ = (((Pj ×ˢ Pj).filter (fun p => m_xy p = 0)).card : ℝ) *
                    ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                      (if (Q h).eval n = 0 then (1 : ℝ) else 0) := h1
              _ ≤ (C₀ * (N : ℝ) ^ ((2 ^ j₀ : ℝ) - (j₀ : ℝ) + ε)) *
                    (((j₀ : ℝ) + (k : ℝ)) * (2 : ℝ) ^ j₀ * (N : ℝ) ^ j₀) := hprod
              _ = C_zero * ((N : ℝ) ^ ((2 ^ j₀ : ℝ) - (j₀ : ℝ) + ε) * (N : ℝ) ^ j₀) := by
                    dsimp only [C_zero]; ring
              _ = C_zero * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) := by rw [hexp]
          have hsum_nz_bound :
              (∑ p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0),
                  ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    if (Q h).eval n = m_xy p then (1 : ℝ) else 0) ≤
                C_nz_div * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) := by
            have h1 : ∑ p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0),
                  ∑ h ∈ Ij, ∑ n ∈ Finset.Icc (1 : ℤ) N,
                    (if (Q h).eval n = m_xy p then (1 : ℝ) else 0) ≤
                ∑ _p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0), C_nz_div * (N : ℝ) ^ ε :=
              Finset.sum_le_sum hnz_term
            have h2 : ∑ _p ∈ (Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0), C_nz_div * (N : ℝ) ^ ε =
                (((Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0)).card : ℝ) * (C_nz_div * (N : ℝ) ^ ε) := by
              simp
            have hexp : (N : ℝ) ^ (2 ^ j₀) * (N : ℝ) ^ ε = (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) := by
              rw [← Real.rpow_natCast (N : ℝ) (2 ^ j₀), ← Real.rpow_add hNR]
              simp
            calc _ ≤ (((Pj ×ˢ Pj).filter (fun p => m_xy p ≠ 0)).card : ℝ) *
                    (C_nz_div * (N : ℝ) ^ ε) := h1.trans_eq h2
              _ ≤ (N : ℝ) ^ (2 ^ j₀) * (C_nz_div * (N : ℝ) ^ ε) :=
                  mul_le_mul_of_nonneg_right hPj_card (by positivity)
              _ = C_nz_div * ((N : ℝ) ^ (2 ^ j₀) * (N : ℝ) ^ ε) := by ring
              _ = C_nz_div * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) := by rw [hexp]
          have hF_tot :
              (∫ α in (0 : ℝ)..1, F_sum α).re ≤
                (C_zero + C_nz_div) * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) := by
            rw [hF_eval]
            have hsum := hswap.trans (add_le_add hsum_0_bound hsum_nz_bound)
            linarith only [hsum]
          have hpref_split :
              (2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) =
                (2 : ℝ) ^ (2 ^ j₀ - j₀ - 1) * (N : ℝ) ^ (2 ^ j₀ - j₀ - 1) := by
            rw [mul_pow]
          have hexp_final :
              (N : ℝ) ^ (2 ^ j₀ - j₀ - 1) * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε) =
                (N : ℝ) ^ ((2 ^ (j₀ + 1) : ℝ) - ((j₀ + 1 : ℕ) : ℝ) + ε) := by
            have hge1 : j₀ + 1 ≤ 2 ^ j₀ := vmv_succ_le_two_pow j₀
            rw [← Real.rpow_natCast (N : ℝ) (2 ^ j₀ - j₀ - 1), ← Real.rpow_add hNR]
            congr 1
            have hcast : ((2 ^ j₀ - j₀ - 1 : ℕ) : ℝ) = (2 ^ j₀ : ℝ) - (j₀ : ℝ) - 1 := by
              have hsub1 : 1 ≤ 2 ^ j₀ - j₀ := by omega
              rw [Nat.cast_sub hsub1, Nat.cast_sub (by omega : j₀ ≤ 2 ^ j₀)]
              simp
            rw [hcast]
            push_cast
            rw [pow_succ']
            ring
          calc ∫ α in (0 : ℝ)..1, ‖T α‖ ^ (2 ^ (j₀ + 1))
              ≤ (2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) * (∫ α in (0 : ℝ)..1, F_sum α).re := hint_mono
            _ ≤ (2 * (N : ℝ)) ^ (2 ^ j₀ - j₀ - 1) *
                  ((C_zero + C_nz_div) * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε)) :=
                mul_le_mul_of_nonneg_left hF_tot (by positivity)
            _ = (2 : ℝ) ^ (2 ^ j₀ - j₀ - 1) * (C_zero + C_nz_div) *
                  ((N : ℝ) ^ (2 ^ j₀ - j₀ - 1) * (N : ℝ) ^ ((2 ^ j₀ : ℝ) + ε)) := by
                rw [hpref_split]; ring
            _ = C * (N : ℝ) ^ ((2 ^ (j₀ + 1) : ℝ) - ((j₀ + 1 : ℕ) : ℝ) + ε) := by
                rw [hexp_final]

/-- Hua's lemma: for any degree `k ≥ 1` and `ε > 0`, there exists `C > 0` (independent of `N`)
such that `∫ α in (0 : ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, exp (2πi α n^k)‖^(2^k) ≤ C * N^(2^k - k + ε)`. -/
theorem hua_lemma (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∫ α in (0 : ℝ)..1,
        ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (2 * Real.pi * (α * (n : ℝ) ^ k) * Complex.I)‖ ^
          (2 ^ k) ≤
        C * (N : ℝ) ^ ((2 ^ k : ℝ) - (k : ℝ) + ε) := by
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨1, zero_lt_one, fun N => ?_⟩
    by_cases hN0 : N = 0
    · subst hN0
      simp only [Nat.cast_zero, Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1),
        Finset.sum_empty, norm_zero]
      rw [zero_pow (by norm_num)]
      simp only [intervalIntegral.integral_zero, mul_nonneg_iff_of_pos_left zero_lt_one]
      exact Real.rpow_nonneg le_rfl _
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have hbd : ∀ α : ℝ,
          ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (2 * Real.pi * (α * (n : ℝ) ^ 0) * Complex.I)‖ ^
              (2 ^ 0) ≤ (N : ℝ) := by
        intro α
        simp only [pow_zero, pow_one, mul_one]
        calc ‖∑ _n ∈ Finset.Icc 1 N, Complex.exp (2 * Real.pi * α * Complex.I)‖
            ≤ ∑ _n ∈ Finset.Icc 1 N, ‖Complex.exp (2 * Real.pi * α * Complex.I)‖ :=
                norm_sum_le _ _
          _ = ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
              refine Finset.sum_congr rfl fun _ _ => ?_
              exact norm_vmvE α
          _ = (N : ℝ) := by simp [Nat.card_Icc]
      calc ∫ α in (0 : ℝ)..1,
              ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (2 * Real.pi * (α * (n : ℝ) ^ 0) * Complex.I)‖ ^
                (2 ^ 0)
          ≤ ∫ _α in (0 : ℝ)..1, (N : ℝ) := by
              refine intervalIntegral.integral_mono_on zero_le_one ?_ intervalIntegrable_const
                fun α _ => hbd α
              refine Continuous.intervalIntegrable ?_ 0 1
              refine (continuous_norm.comp (continuous_finsetSum (Finset.Icc 1 N) fun n _ => ?_)).pow _
              exact Complex.continuous_exp.comp
                (((continuous_const.mul (continuous_ofReal.mul continuous_const)).mul
                  continuous_const))
        _ = (N : ℝ) := by simp
        _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ 1 * (N : ℝ) ^ ((2 ^ 0 : ℝ) - (0 : ℕ) + ε) := by
            rw [one_mul]
            exact Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num; linarith [hε])
  · exact hua_lemma_step (Nat.one_le_iff_ne_zero.mpr hk0) (Nat.one_le_iff_ne_zero.mpr hk0)
      le_rfl hε

/-! ## Complete polynomial exponential sums -/

/-- Complete exponential sum `S(q, a, k) = ∑_{x mod q} exp (2πi a x^k / q)`. -/
def completeExpSum (q a k : ℕ) : ℂ :=
  ∑ x ∈ Finset.range q, Complex.exp (2 * Real.pi * ((a : ℝ) * (x : ℝ) ^ k / (q : ℝ)) * Complex.I)

private lemma completeExpSum_eq_sum_vmvE (q a k : ℕ) :
    completeExpSum q a k = ∑ x ∈ Finset.range q, vmvE ((a : ℝ) * (x : ℝ) ^ k / (q : ℝ)) := by
  unfold completeExpSum
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp only [vmvE]
  push_cast
  rfl

private lemma completeExpSum_eq_of_modEq {q a₁ a₂ k : ℕ} (hq : 1 ≤ q) (hmod : a₁ ≡ a₂ [MOD q]) :
    completeExpSum q a₁ k = completeExpSum q a₂ k := by
  simp only [completeExpSum_eq_sum_vmvE]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdvd : (q : ℤ) ∣ ((a₁ : ℤ) - (a₂ : ℤ)) * (x : ℤ) ^ k :=
    dvd_mul_of_dvd_left (dvd_sub_comm.mp (Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod))) _
  rcases hdvd with ⟨m, hm⟩
  refine vmvE_eq_of_int_sub (m := m) ?_
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hmR : ((a₁ : ℝ) - (a₂ : ℝ)) * (x : ℝ) ^ k = (q : ℝ) * (m : ℝ) := by exact_mod_cast hm
  rw [← sub_div, ← sub_mul, hmR, mul_div_cancel_left₀ _ hq0]

/-- Linear complete exponential sum: `S(q, a, 1) = q` if `q ∣ a`, and `0` otherwise. -/
theorem completeExpSum_linear_eq {q : ℕ} (hq : 1 ≤ q) (a : ℕ) :
    completeExpSum q a 1 = if q ∣ a then (q : ℂ) else 0 := by
  rw [completeExpSum_eq_sum_vmvE]
  have hrew : ∀ x : ℕ, vmvE ((a : ℝ) * (x : ℝ) ^ 1 / (q : ℝ)) = vmvE ((a : ℤ) * (x : ℝ) / q) := by
    intro x
    simp
  simp_rw [hrew, completeExpSum_linear_int_eq q hq a]
  congr 1
  exact propext (by exact_mod_cast Int.natCast_dvd_natCast)

/-- Chinese Remainder Theorem multiplicativity of complete exponential sums: for `Coprime q₁ q₂`
and `1 ≤ k`, `S(q₁ * q₂, a, k) = S(q₁, a * q₂^(k - 1), k) * S(q₂, a * q₁^(k - 1), k)`. -/
theorem completeExpSum_mul_coprime {q₁ q₂ : ℕ} (hcop : Nat.Coprime q₁ q₂) (a : ℕ)
    {k : ℕ} (hk : 1 ≤ k) :
    completeExpSum (q₁ * q₂) a k =
      completeExpSum q₁ (a * q₂ ^ (k - 1)) k * completeExpSum q₂ (a * q₁ ^ (k - 1)) k := by
  by_cases hq₁ : q₁ = 0
  · subst hq₁; simp [completeExpSum]
  by_cases hq₂ : q₂ = 0
  · subst hq₂; simp [completeExpSum]
  have hq₁_pos : 0 < q₁ := Nat.pos_of_ne_zero hq₁
  have hq₂_pos : 0 < q₂ := Nat.pos_of_ne_zero hq₂
  have hq₁₂_pos : 0 < q₁ * q₂ := Nat.mul_pos hq₁_pos hq₂_pos
  let φ : ℕ × ℕ → ℕ := fun p => (p.1 * q₂ + p.2 * q₁) % (q₁ * q₂)
  have hφ_mem : ∀ p ∈ Finset.range q₁ ×ˢ Finset.range q₂, φ p ∈ Finset.range (q₁ * q₂) := by
    intro p _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq₁₂_pos)
  have hφ_inj : Set.InjOn φ ↑(Finset.range q₁ ×ˢ Finset.range q₂) := by
    intro p₁ hp₁ p₂ hp₂ h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
    have h1 : φ p₁ % q₁ = φ p₂ % q₁ := congrArg (· % q₁) h
    have h2 : φ p₁ % q₂ = φ p₂ % q₂ := congrArg (· % q₂) h
    have hm1 : ∀ p : ℕ × ℕ, φ p % q₁ = (p.1 * q₂) % q₁ := fun p => by
      dsimp only [φ]
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_right q₁ q₂), Nat.add_mul_mod_self_right]
    have hm2 : ∀ p : ℕ × ℕ, φ p % q₂ = (p.2 * q₁) % q₂ := fun p => by
      dsimp only [φ]
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_left q₂ q₁), add_comm, Nat.add_mul_mod_self_right]
    rw [hm1, hm1] at h1
    rw [hm2, hm2] at h2
    have heq1 : p₁.1 = p₂.1 := by
      rcases le_total p₁.1 p₂.1 with hle | hle
      · have hdvd : q₁ ∣ (p₂.1 - p₁.1) * q₂ := by
          have hmod_nat : p₁.1 * q₂ % q₁ = p₂.1 * q₂ % q₁ := h1
          have hdvd_z : (q₁ : ℤ) ∣ ((p₂.1 : ℤ) - (p₁.1 : ℤ)) * (q₂ : ℤ) := by
            have := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_nat)
            simpa [sub_mul] using this
          have hdvd_n : (q₁ : ℤ) ∣ (((p₂.1 - p₁.1) * q₂ : ℕ) : ℤ) := by
            simpa [Nat.cast_mul, Nat.cast_sub hle] using hdvd_z
          exact Int.natCast_dvd_natCast.mp hdvd_n
        have hsub_dvd : q₁ ∣ p₂.1 - p₁.1 := hcop.dvd_of_dvd_mul_right hdvd
        have hsub_eq : p₂.1 - p₁.1 = 0 := Nat.eq_zero_of_dvd_of_lt hsub_dvd (by omega)
        omega
      · have hdvd : q₁ ∣ (p₁.1 - p₂.1) * q₂ := by
          have hmod_nat : p₂.1 * q₂ % q₁ = p₁.1 * q₂ % q₁ := h1.symm
          have hdvd_z : (q₁ : ℤ) ∣ ((p₁.1 : ℤ) - (p₂.1 : ℤ)) * (q₂ : ℤ) := by
            have := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_nat)
            simpa [sub_mul] using this
          have hdvd_n : (q₁ : ℤ) ∣ (((p₁.1 - p₂.1) * q₂ : ℕ) : ℤ) := by
            simpa [Nat.cast_mul, Nat.cast_sub hle] using hdvd_z
          exact Int.natCast_dvd_natCast.mp hdvd_n
        have hsub_dvd : q₁ ∣ p₁.1 - p₂.1 := hcop.dvd_of_dvd_mul_right hdvd
        have hsub_eq : p₁.1 - p₂.1 = 0 := Nat.eq_zero_of_dvd_of_lt hsub_dvd (by omega)
        omega
    have heq2 : p₁.2 = p₂.2 := by
      rcases le_total p₁.2 p₂.2 with hle | hle
      · have hdvd : q₂ ∣ (p₂.2 - p₁.2) * q₁ := by
          have hmod_nat : p₁.2 * q₁ % q₂ = p₂.2 * q₁ % q₂ := h2
          have hdvd_z : (q₂ : ℤ) ∣ ((p₂.2 : ℤ) - (p₁.2 : ℤ)) * (q₁ : ℤ) := by
            have := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_nat)
            simpa [sub_mul] using this
          have hdvd_n : (q₂ : ℤ) ∣ (((p₂.2 - p₁.2) * q₁ : ℕ) : ℤ) := by
            simpa [Nat.cast_mul, Nat.cast_sub hle] using hdvd_z
          exact Int.natCast_dvd_natCast.mp hdvd_n
        have hsub_dvd : q₂ ∣ p₂.2 - p₁.2 := hcop.symm.dvd_of_dvd_mul_right hdvd
        have hsub_eq : p₂.2 - p₁.2 = 0 := Nat.eq_zero_of_dvd_of_lt hsub_dvd (by omega)
        omega
      · have hdvd : q₂ ∣ (p₁.2 - p₂.2) * q₁ := by
          have hmod_nat : p₂.2 * q₁ % q₂ = p₁.2 * q₁ % q₂ := h2.symm
          have hdvd_z : (q₂ : ℤ) ∣ ((p₁.2 : ℤ) - (p₂.2 : ℤ)) * (q₁ : ℤ) := by
            have := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_nat)
            simpa [sub_mul] using this
          have hdvd_n : (q₂ : ℤ) ∣ (((p₁.2 - p₂.2) * q₁ : ℕ) : ℤ) := by
            simpa [Nat.cast_mul, Nat.cast_sub hle] using hdvd_z
          exact Int.natCast_dvd_natCast.mp hdvd_n
        have hsub_dvd : q₂ ∣ p₁.2 - p₂.2 := hcop.symm.dvd_of_dvd_mul_right hdvd
        have hsub_eq : p₁.2 - p₂.2 = 0 := Nat.eq_zero_of_dvd_of_lt hsub_dvd (by omega)
        omega
    exact Prod.ext heq1 heq2
  have hφ_img : (Finset.range q₁ ×ˢ Finset.range q₂).image φ = Finset.range (q₁ * q₂) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
      exact hφ_mem p hp
    · rw [Finset.card_image_of_injOn hφ_inj, Finset.card_product,
        Finset.card_range, Finset.card_range, Finset.card_range]
  rw [completeExpSum_eq_sum_vmvE, ← hφ_img, Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hφ_inj hp₁ hp₂ h)]
  rw [Finset.sum_product, completeExpSum_eq_sum_vmvE, completeExpSum_eq_sum_vmvE,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => ?_
  rw [← vmvE_add]
  have hmod_pow : (φ (x₁, x₂) : ℤ) ^ k ≡ (x₁ * q₂ + x₂ * q₁ : ℤ) ^ k [ZMOD (q₁ * q₂ : ℤ)] := by
    refine Int.ModEq.pow k ?_
    change ((φ (x₁, x₂) : ℕ) : ℤ) ≡ ((x₁ * q₂ + x₂ * q₁ : ℕ) : ℤ) [ZMOD ((q₁ * q₂ : ℕ) : ℤ)]
    exact Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  have hcross : ((x₁ * q₂ + x₂ * q₁ : ℤ) ^ k - ((x₁ * q₂ : ℤ) ^ k + (x₂ * q₁ : ℤ) ^ k)) ≡
      0 [ZMOD (q₁ * q₂ : ℤ)] := by
    rw [Int.modEq_zero_iff_dvd]
    have hbin : (x₁ * q₂ + x₂ * q₁ : ℤ) ^ k - ((x₁ * q₂ : ℤ) ^ k + (x₂ * q₁ : ℤ) ^ k) =
        ∑ j ∈ Finset.range (k - 1),
          (k.choose (j + 1) : ℤ) * (x₁ * q₂ : ℤ) ^ (j + 1) * (x₂ * q₁ : ℤ) ^ (k - (j + 1)) := by
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', hk'⟩
      have hk1 : k = k' + 1 := hk'
      rw [hk1, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
      simp only [Nat.sub_self, pow_zero, mul_one, one_mul, Nat.choose_self,
        Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.add_sub_cancel]
      have hsum_eq :
          ∑ j ∈ Finset.range k', (x₁ * q₂ : ℤ) ^ (j + 1) * (x₂ * q₁ : ℤ) ^ (k' + 1 - (j + 1)) *
              ((k' + 1).choose (j + 1) : ℤ) =
            ∑ j ∈ Finset.range k', ((k' + 1).choose (j + 1) : ℤ) * (x₁ * q₂ : ℤ) ^ (j + 1) *
              (x₂ * q₁ : ℤ) ^ (k' + 1 - (j + 1)) :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [hsum_eq]
      ring
    rw [hbin]
    refine Finset.dvd_sum fun j hj => ?_
    have hj_lt : j < k - 1 := Finset.mem_range.mp hj
    have hpow1 : (q₁ : ℤ) ∣ (x₂ * q₁ : ℤ) ^ (k - (j + 1)) := by
      have hexp : k - (j + 1) = (k - (j + 1) - 1) + 1 := by omega
      rw [hexp, pow_succ]
      exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    have hpow2 : (q₂ : ℤ) ∣ (x₁ * q₂ : ℤ) ^ (j + 1) := by
      rw [pow_succ]
      exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    have hmul : (q₁ * q₂ : ℤ) ∣ (x₁ * q₂ : ℤ) ^ (j + 1) * (x₂ * q₁ : ℤ) ^ (k - (j + 1)) := by
      rw [mul_comm (q₁ : ℤ) (q₂ : ℤ)]
      exact mul_dvd_mul hpow2 hpow1
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right hmul _
  have hdvd_tot : (q₁ * q₂ : ℤ) ∣
      (a : ℤ) * ((φ (x₁, x₂) : ℤ) ^ k - ((x₁ * q₂ : ℤ) ^ k + (x₂ * q₁ : ℤ) ^ k)) := by
    refine dvd_mul_of_dvd_right ?_ _
    have hd1 : (q₁ * q₂ : ℤ) ∣ (φ (x₁, x₂) : ℤ) ^ k - (x₁ * q₂ + x₂ * q₁ : ℤ) ^ k :=
      dvd_sub_comm.mp (Int.modEq_iff_dvd.mp hmod_pow)
    have hd2 : (q₁ * q₂ : ℤ) ∣ (x₁ * q₂ + x₂ * q₁ : ℤ) ^ k - ((x₁ * q₂ : ℤ) ^ k + (x₂ * q₁ : ℤ) ^ k) :=
      Int.modEq_zero_iff_dvd.mp hcross
    have hsum := dvd_add hd1 hd2
    simpa [sub_add_sub_cancel] using hsum
  rcases hdvd_tot with ⟨m, hm⟩
  refine vmvE_eq_of_int_sub (m := m) ?_
  have hq₁0 : (q₁ : ℝ) ≠ 0 := by exact_mod_cast hq₁
  have hq₂0 : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq₂
  have hq₁₂0 : ((q₁ * q₂ : ℕ) : ℝ) ≠ 0 := by positivity
  have hmR : (a : ℝ) * (((φ (x₁, x₂) : ℕ) : ℝ) ^ k -
      (((x₁ : ℝ) * q₂) ^ k + ((x₂ : ℝ) * q₁) ^ k)) = (q₁ : ℝ) * q₂ * (m : ℝ) := by
    exact_mod_cast hm
  have hpow_split1 : ((x₁ : ℝ) * q₂) ^ k = (q₂ : ℝ) * (q₂ : ℝ) ^ (k - 1) * (x₁ : ℝ) ^ k := by
    rw [mul_pow, mul_comm ((x₁ : ℝ) ^ k) _]
    congr 1
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hpow_split2 : ((x₂ : ℝ) * q₁) ^ k = (q₁ : ℝ) * (q₁ : ℝ) ^ (k - 1) * (x₂ : ℝ) ^ k := by
    rw [mul_pow, mul_comm ((x₂ : ℝ) ^ k) _]
    congr 1
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  push_cast
  field_simp [hq₁0, hq₂0]
  rw [hpow_split1, hpow_split2] at hmR
  linarith only [hmR]

/-- Quadratic complete exponential sum bound: for `q ≥ 1` and `Coprime a q`,
`‖S(q, a, 2)‖ ≤ √(2 q)`. -/
theorem completeExpSum_quadratic_bound {q : ℕ} (hq : 1 ≤ q) {a : ℕ} (hcop : Nat.Coprime a q) :
    ‖completeExpSum q a 2‖ ≤ Real.sqrt (2 * (q : ℝ)) := by
  have hq0 : q ≠ 0 := by omega
  have hq_pos : 0 < q := hq
  have hsq : ‖completeExpSum q a 2‖ ^ 2 ≤ 2 * (q : ℝ) := by
    have hnorm : ((‖completeExpSum q a 2‖ ^ 2 : ℝ) : ℂ) =
        completeExpSum q a 2 * star (completeExpSum q a 2) :=
      vmv_norm_sq_eq_mul_star _
    have hmul : completeExpSum q a 2 * star (completeExpSum q a 2) =
        ∑ h ∈ Finset.range q, vmvE ((a : ℝ) * (h : ℝ) ^ 2 / (q : ℝ)) *
          ∑ y ∈ Finset.range q, vmvE (((a * (2 * h) : ℤ) : ℝ) * (y : ℝ) / q) := by
      rw [completeExpSum_eq_sum_vmvE, star_sum, Finset.sum_mul_sum]
      have hswap : ∀ y ∈ Finset.range q,
          ∑ x ∈ Finset.range q,
            vmvE ((a : ℝ) * (x : ℝ) ^ 2 / q) * star (vmvE ((a : ℝ) * (y : ℝ) ^ 2 / q)) =
          ∑ h ∈ Finset.range q,
            vmvE ((a : ℝ) * (((y + h) % q : ℕ) : ℝ) ^ 2 / q) *
              star (vmvE ((a : ℝ) * (y : ℝ) ^ 2 / q)) := by
        intro y _
        let ψ : ℕ → ℕ := fun h => (y + h) % q
        have hψ_inj : Set.InjOn ψ (Finset.range q : Set ℕ) := by
          intro h₁ hh₁ h₂ hh₂ heq
          rw [Finset.mem_coe, Finset.mem_range] at hh₁ hh₂
          have hmod : y + h₁ ≡ y + h₂ [MOD q] := heq
          have hmod' : h₁ ≡ h₂ [MOD q] := Nat.ModEq.add_left_cancel' y hmod
          exact Nat.ModEq.eq_of_lt_of_lt hmod' hh₁ hh₂
        have hψ_img : (Finset.range q).image ψ = Finset.range q := by
          refine Finset.eq_of_subset_of_card_le ?_ ?_
          · intro x hx
            rcases Finset.mem_image.mp hx with ⟨h, _, rfl⟩
            exact Finset.mem_range.mpr (Nat.mod_lt _ hq_pos)
          · rw [Finset.card_image_of_injOn hψ_inj]
        conv_lhs => rw [← hψ_img, Finset.sum_image (fun h₁ hh₁ h₂ hh₂ h => hψ_inj hh₁ hh₂ h)]
      calc ∑ x ∈ Finset.range q, ∑ y ∈ Finset.range q,
              vmvE ((a : ℝ) * (x : ℝ) ^ 2 / q) * star (vmvE ((a : ℝ) * (y : ℝ) ^ 2 / q))
          = ∑ y ∈ Finset.range q, ∑ x ∈ Finset.range q,
              vmvE ((a : ℝ) * (x : ℝ) ^ 2 / q) * star (vmvE ((a : ℝ) * (y : ℝ) ^ 2 / q)) :=
              Finset.sum_comm
        _ = ∑ y ∈ Finset.range q, ∑ h ∈ Finset.range q,
              vmvE ((a : ℝ) * (((y + h) % q : ℕ) : ℝ) ^ 2 / q) *
                star (vmvE ((a : ℝ) * (y : ℝ) ^ 2 / q)) := Finset.sum_congr rfl hswap
        _ = ∑ h ∈ Finset.range q, ∑ y ∈ Finset.range q,
              vmvE ((a : ℝ) * (((y + h) % q : ℕ) : ℝ) ^ 2 / q) *
                star (vmvE ((a : ℝ) * (y : ℝ) ^ 2 / q)) := Finset.sum_comm
        _ = ∑ h ∈ Finset.range q, vmvE ((a : ℝ) * (h : ℝ) ^ 2 / q) *
              ∑ y ∈ Finset.range q, vmvE (((a * (2 * h) : ℤ) : ℝ) * (y : ℝ) / q) := by
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [star_vmvE, ← vmvE_add, ← vmvE_add]
            have hmod : (((y + h) % q : ℕ) : ℤ) ^ 2 ≡ (y + h : ℤ) ^ 2 [ZMOD (q : ℤ)] :=
              Int.ModEq.pow 2 (Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _))
            have hdvd : (q : ℤ) ∣
                (a : ℤ) * ((((y + h) % q : ℕ) : ℤ) ^ 2 - (y : ℤ) ^ 2) -
                  ((a : ℤ) * (h : ℤ) ^ 2 + (a * (2 * h) : ℤ) * (y : ℤ)) := by
              have hd : (q : ℤ) ∣ (((y + h) % q : ℕ) : ℤ) ^ 2 - (y + h : ℤ) ^ 2 :=
                dvd_sub_comm.mp (Int.modEq_iff_dvd.mp hmod)
              have hmul_d : (q : ℤ) ∣ (a : ℤ) * ((((y + h) % q : ℕ) : ℤ) ^ 2 - (y + h : ℤ) ^ 2) :=
                dvd_mul_of_dvd_right hd _
              convert hmul_d using 1
              ring
            rcases hdvd with ⟨m, hm⟩
            refine vmvE_eq_of_int_sub (m := m) ?_
            have hqR0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
            have hmR : (a : ℝ) * ((((y + h) % q : ℕ) : ℝ) ^ 2 - (y : ℝ) ^ 2) -
                ((a : ℝ) * (h : ℝ) ^ 2 + ((a * (2 * h) : ℤ) : ℝ) * (y : ℝ)) =
                (q : ℝ) * (m : ℝ) := by exact_mod_cast hm
            field_simp [hqR0]
            linarith only [hmR]
    have hre : ‖completeExpSum q a 2‖ ^ 2 =
        (∑ h ∈ Finset.range q, vmvE ((a : ℝ) * (h : ℝ) ^ 2 / q) *
          (if (q : ℤ) ∣ (a * (2 * h) : ℤ) then (q : ℂ) else 0)).re := by
      have hc := congrArg Complex.re (hnorm.trans hmul)
      simp only [Complex.ofReal_re] at hc
      rw [hc]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [completeExpSum_linear_int_eq q hq (a * (2 * h))]
    rw [hre, Complex.re_sum]
    have hfilt_sub : (Finset.range q).filter (fun h : ℕ => (q : ℤ) ∣ (a * (2 * h) : ℤ)) ⊆
        ({0, q / 2} : Finset ℕ) := by
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_range] at hh
      have hdvd_N : q ∣ a * (2 * h) := by exact_mod_cast hh.2
      have hdvd_2h : q ∣ 2 * h := (hcop.symm.dvd_of_dvd_mul_left hdvd_N)
      rcases hdvd_2h with ⟨m, hm⟩
      have hm_lt : m < 2 := by
        by_contra hm2
        have h1 : 2 ≤ m := not_lt.mp hm2
        have h2 : 2 * q ≤ q * m := by nlinarith only [hq_pos, h1]
        linarith only [hm, h2, hh.1]
      rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
      · have h0 : h = 0 := by omega
        simp [h0]
      · have hq2 : h = q / 2 := by omega
        simp [hq2]
    calc ∑ h ∈ Finset.range q,
            (vmvE ((a : ℝ) * (h : ℝ) ^ 2 / q) *
              (if (q : ℤ) ∣ (a * (2 * h) : ℤ) then (q : ℂ) else 0)).re
        ≤ ∑ h ∈ Finset.range q,
            if (q : ℤ) ∣ (a * (2 * h) : ℤ) then (q : ℝ) else 0 := by
          refine Finset.sum_le_sum fun h _ => ?_
          split_ifs with hd
          · refine (Complex.re_le_norm _).trans ?_
            rw [norm_mul, norm_vmvE, one_mul, Complex.norm_natCast]
          · simp
      _ = ∑ _h ∈ (Finset.range q).filter (fun h : ℕ => (q : ℤ) ∣ (a * (2 * h) : ℤ)), (q : ℝ) := by
          rw [Finset.sum_filter]
      _ = (((Finset.range q).filter (fun h : ℕ => (q : ℤ) ∣ (a * (2 * h) : ℤ))).card : ℝ) * (q : ℝ) := by
          simp
      _ ≤ (({0, q / 2} : Finset ℕ).card : ℝ) * (q : ℝ) := by
          gcongr
      _ ≤ 2 * (q : ℝ) := by
          have hcard2 : ({0, q / 2} : Finset ℕ).card ≤ 2 :=
            (Finset.card_insert_le _ _).trans (by simp)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard2) (Nat.cast_nonneg q)
  exact Real.le_sqrt_of_sq_le hsq

/-- Complete exponential sum bound modulo a prime `p`: for prime `p`, `p ∤ a`, and `k ≥ 1`,
`‖S(p, a, k)‖ ≤ k * √p`. -/
theorem completeExpSum_prime_bound {p : ℕ} (hp : p.Prime) {a : ℕ} (hpa : ¬ p ∣ a)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖completeExpSum p a k‖ ≤ (k : ℝ) * Real.sqrt (p : ℝ) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hp_pos : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hk_pos : 0 < k := hk
  have hsum_sq_le :
      ∑ c ∈ (Finset.range p).erase 0, ‖completeExpSum p c k‖ ^ 2 ≤
        (p : ℝ) * ((p : ℝ) - 1) * ((k : ℝ) - 1) := by
    have hnorm_sum :
        ∑ c ∈ Finset.range p, ‖completeExpSum p c k‖ ^ 2 =
          (∑ x ∈ Finset.range p, ∑ y ∈ Finset.range p,
            if (p : ℤ) ∣ (x : ℤ) ^ k - (y : ℤ) ^ k then (p : ℝ) else 0) := by
      have hre_c : ∀ c : ℕ, ‖completeExpSum p c k‖ ^ 2 =
          (completeExpSum p c k * star (completeExpSum p c k)).re := fun c => by
        have h1 : ((‖completeExpSum p c k‖ ^ 2 : ℝ) : ℂ) =
            completeExpSum p c k * star (completeExpSum p c k) :=
          vmv_norm_sq_eq_mul_star _
        simpa only [Complex.ofReal_re] using congrArg Complex.re h1
      simp_rw [hre_c, ← Complex.re_sum]
      have hswap :
          ∑ c ∈ Finset.range p, completeExpSum p c k * star (completeExpSum p c k) =
            ∑ x ∈ Finset.range p, ∑ y ∈ Finset.range p,
              ∑ c ∈ Finset.range p, vmvE ((((x : ℤ) ^ k - (y : ℤ) ^ k : ℤ) : ℝ) * (c : ℝ) / p) := by
        have hexp : ∀ c : ℕ, completeExpSum p c k * star (completeExpSum p c k) =
            ∑ x ∈ Finset.range p, ∑ y ∈ Finset.range p,
              vmvE ((((x : ℤ) ^ k - (y : ℤ) ^ k : ℤ) : ℝ) * (c : ℝ) / p) := by
          intro c
          rw [completeExpSum_eq_sum_vmvE, star_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [star_vmvE, ← vmvE_add]
          congr 1
          push_cast
          ring
        simp_rw [hexp]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
      rw [hswap]
      simp_rw [completeExpSum_linear_int_eq p hp_pos]
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
    have hcount_sols :
        ((Finset.range p ×ˢ Finset.range p).filter
          (fun xy : ℕ × ℕ => (p : ℤ) ∣ (xy.1 : ℤ) ^ k - (xy.2 : ℤ) ^ k)).card ≤
          1 + (p - 1) * k := by
      have hdvd_iff : ∀ x y : ℕ,
          (p : ℤ) ∣ (x : ℤ) ^ k - (y : ℤ) ^ k ↔ (x : ZMod p) ^ k = (y : ZMod p) ^ k := by
        intro x y
        rw [dvd_sub_comm, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
        push_cast
        rfl
      have hzero : ∀ y ∈ Finset.range p, y = 0 →
          ((Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ k - (y : ℤ) ^ k)).card ≤ 1 := by
        intro y _ hy
        subst hy
        have hsub : (Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ k - (0 : ℤ) ^ k) ⊆ {0} := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hx ⊢
          have hz : (x : ZMod p) ^ k = 0 := by
            have := (hdvd_iff x 0).mp hx.2
            simpa [zero_pow (by omega : k ≠ 0)] using this
          have hpow_z : ∀ n : ℕ, 1 ≤ n → (x : ZMod p) ^ n = 0 → (x : ZMod p) = 0 := by
            intro n hn hzn
            induction n with
            | zero => omega
            | succ n' ih =>
                by_cases hn' : n' = 0
                · subst hn'; simpa using hzn
                · rw [pow_succ] at hzn
                  rcases mul_eq_zero.mp hzn with h0 | h0
                  · exact ih (by omega) h0
                  · exact h0
          have hx0 : (x : ZMod p) = 0 := hpow_z k hk hz
          have hdvd_x : p ∣ x := (ZMod.natCast_eq_zero_iff x p).mp hx0
          exact Nat.eq_zero_of_dvd_of_lt hdvd_x hx.1
        exact (Finset.card_le_card hsub).trans (by simp)
      have hnz : ∀ y ∈ (Finset.range p).erase 0,
          ((Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ k - (y : ℤ) ^ k)).card ≤ k := by
        intro y _
        let P : Polynomial (ZMod p) := Polynomial.X ^ k - Polynomial.C ((y : ZMod p) ^ k)
        let S := (Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ k - (y : ℤ) ^ k)
        let f : ℕ → ZMod p := fun x => (x : ZMod p)
        have hf_inj : Set.InjOn f (S : Set ℕ) := by
          intro x₁ hx₁ x₂ hx₂ h
          have hx₁_lt : x₁ < p := (Finset.mem_range.mp (Finset.mem_filter.mp hx₁).1)
          have hx₂_lt : x₂ < p := (Finset.mem_range.mp (Finset.mem_filter.mp hx₂).1)
          have : NeZero p := ⟨hp.ne_zero⟩
          have hv := congrArg ZMod.val h
          simp only [f] at hv
          rw [ZMod.val_natCast_of_lt hx₁_lt, ZMod.val_natCast_of_lt hx₂_lt] at hv
          exact hv
        have hsub : (S.image f).val ⊆ P.roots := by
          intro z hz
          rw [Finset.mem_val, Finset.mem_image] at hz
          rcases hz with ⟨x, hx, rfl⟩
          have hx' := (Finset.mem_filter.mp hx).2
          have hpow := (hdvd_iff x y).mp hx'
          refine (Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hk_pos _)).mpr ?_
          simp only [f, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C, hpow, sub_self]
        have hle : (S.image f).val ≤ P.roots := (Multiset.le_iff_subset (S.image f).nodup).mpr hsub
        calc S.card = (S.image f).card := (Finset.card_image_of_injOn hf_inj).symm
          _ ≤ Multiset.card P.roots := Multiset.card_le_card hle
          _ ≤ k := Polynomial.card_roots_X_pow_sub_C hk_pos ((y : ZMod p) ^ k)
      have hcard_prod :
          ((Finset.range p ×ˢ Finset.range p).filter
            (fun xy : ℕ × ℕ => (p : ℤ) ∣ (xy.1 : ℤ) ^ k - (xy.2 : ℤ) ^ k)).card =
            ∑ y ∈ Finset.range p,
              ((Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ k - (y : ℤ) ^ k)).card := by
        rw [Finset.card_filter, Finset.sum_product_right]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.card_filter]
      rw [hcard_prod, ← Finset.add_sum_erase (Finset.range p) _ (Finset.mem_range.mpr hp_pos)]
      have h0_le : ((Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ k - (0 : ℤ) ^ k)).card ≤ 1 :=
        hzero 0 (Finset.mem_range.mpr hp_pos) rfl
      have h1_le : ∑ y ∈ (Finset.range p).erase 0,
            ((Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ k - (y : ℤ) ^ k)).card ≤
          (p - 1) * k := by
        calc _ ≤ ∑ _y ∈ (Finset.range p).erase 0, k := Finset.sum_le_sum hnz
          _ = ((Finset.range p).erase 0).card * k := by simp
          _ = (p - 1) * k := by
              rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hp_pos), Finset.card_range]
      exact Nat.add_le_add h0_le h1_le
    have hsum_all_le :
        ∑ c ∈ Finset.range p, ‖completeExpSum p c k‖ ^ 2 ≤
          (p : ℝ) * (1 + ((p : ℝ) - 1) * (k : ℝ)) := by
      rw [hnorm_sum, ← Finset.sum_product']
      have heq :
          (∑ xy ∈ Finset.range p ×ˢ Finset.range p,
              if (p : ℤ) ∣ (xy.1 : ℤ) ^ k - (xy.2 : ℤ) ^ k then (p : ℝ) else 0) =
            (((Finset.range p ×ˢ Finset.range p).filter
              (fun xy : ℕ × ℕ => (p : ℤ) ∣ (xy.1 : ℤ) ^ k - (xy.2 : ℤ) ^ k)).card : ℝ) *
              (p : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [heq, mul_comm _ (p : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg p)
      have hcast : ((1 + (p - 1) * k : ℕ) : ℝ) = 1 + ((p : ℝ) - 1) * (k : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      rw [← hcast]
      exact_mod_cast hcount_sols
    have hc0 : ‖completeExpSum p 0 k‖ ^ 2 = (p : ℝ) ^ 2 := by
      have h0 : completeExpSum p 0 k = (p : ℂ) := by
        simp [completeExpSum]
      rw [h0, Complex.norm_natCast]
    rw [← Finset.add_sum_erase (Finset.range p) (fun c => ‖completeExpSum p c k‖ ^ 2)
      (Finset.mem_range.mpr hp_pos), hc0] at hsum_all_le
    linarith only [hsum_all_le]
  let T := (Finset.range p).erase 0
  let orbMap : ℕ → ℕ := fun t => (a * t ^ k) % p
  let Orb := T.image orbMap
  have hOrb_sub : Orb ⊆ T := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨t, ht, rfl⟩
    simp only [T, Finset.mem_erase, Finset.mem_range] at ht ⊢
    refine ⟨?_, Nat.mod_lt _ hp_pos⟩
    intro h0
    have hdvd : p ∣ a * t ^ k := Nat.dvd_of_mod_eq_zero h0
    rcases hp.dvd_mul.mp hdvd with ha | htk
    · exact hpa ha
    · have hpt : p ∣ t := hp.dvd_of_dvd_pow htk
      exact ht.1 (Nat.eq_zero_of_dvd_of_lt hpt ht.2)
  have hOrb_eq : ∀ c ∈ Orb, completeExpSum p c k = completeExpSum p a k := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨t, ht, rfl⟩
    have ht' := Finset.mem_erase.mp ht
    have hpt : ¬ p ∣ t := fun hd => ht'.1 (Nat.eq_zero_of_dvd_of_lt hd (Finset.mem_range.mp ht'.2))
    rw [completeExpSum_eq_of_modEq hp_pos (Nat.mod_modEq (a * t ^ k) p)]
    let mulT : ℕ → ℕ := fun x => (t * x) % p
    have hmulT_inj : Set.InjOn mulT (Finset.range p : Set ℕ) := by
      intro x₁ hx₁ x₂ hx₂ heq
      rw [Finset.mem_coe, Finset.mem_range] at hx₁ hx₂
      rcases le_total x₁ x₂ with hle | hle
      · have hdvd : p ∣ (x₂ - x₁) * t := by
          have hmod_nat : t * x₁ % p = t * x₂ % p := heq
          have hdvd_z : (p : ℤ) ∣ ((x₂ : ℤ) - (x₁ : ℤ)) * (t : ℤ) := by
            have := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_nat)
            simpa [mul_sub, sub_mul, mul_comm] using this
          have hdvd_n : (p : ℤ) ∣ (((x₂ - x₁) * t : ℕ) : ℤ) := by
            simpa [Nat.cast_mul, Nat.cast_sub hle] using hdvd_z
          exact Int.natCast_dvd_natCast.mp hdvd_n
        have hsub_dvd : p ∣ x₂ - x₁ :=
          (hp.coprime_iff_not_dvd.mpr hpt).dvd_of_dvd_mul_right hdvd
        have hsub_eq : x₂ - x₁ = 0 := Nat.eq_zero_of_dvd_of_lt hsub_dvd (by omega)
        omega
      · have hdvd : p ∣ (x₁ - x₂) * t := by
          have hmod_nat : t * x₂ % p = t * x₁ % p := heq.symm
          have hdvd_z : (p : ℤ) ∣ ((x₁ : ℤ) - (x₂ : ℤ)) * (t : ℤ) := by
            have := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_nat)
            simpa [mul_sub, sub_mul, mul_comm] using this
          have hdvd_n : (p : ℤ) ∣ (((x₁ - x₂) * t : ℕ) : ℤ) := by
            simpa [Nat.cast_mul, Nat.cast_sub hle] using hdvd_z
          exact Int.natCast_dvd_natCast.mp hdvd_n
        have hsub_dvd : p ∣ x₁ - x₂ :=
          (hp.coprime_iff_not_dvd.mpr hpt).dvd_of_dvd_mul_right hdvd
        have hsub_eq : x₁ - x₂ = 0 := Nat.eq_zero_of_dvd_of_lt hsub_dvd (by omega)
        omega
    have hmulT_img : (Finset.range p).image mulT = Finset.range p := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨x, _, rfl⟩
        exact Finset.mem_range.mpr (Nat.mod_lt _ hp_pos)
      · rw [Finset.card_image_of_injOn hmulT_inj]
    conv_rhs => rw [completeExpSum_eq_sum_vmvE, ← hmulT_img,
      Finset.sum_image (fun x₁ hx₁ x₂ hx₂ h => hmulT_inj hx₁ hx₂ h)]
    rw [completeExpSum_eq_sum_vmvE]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hmod_pow : ((a * (mulT x) ^ k : ℕ) : ℤ) ≡ ((a * t ^ k * x ^ k : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
      refine Int.natCast_modEq_iff.mpr ?_
      have hx : mulT x ≡ t * x [MOD p] := Nat.mod_modEq (t * x) p
      have hxk := hx.pow k
      calc a * (mulT x) ^ k ≡ a * (t * x) ^ k [MOD p] := Nat.ModEq.mul_left a hxk
        _ = a * t ^ k * x ^ k := by rw [mul_pow, mul_assoc]
    rcases Int.modEq_iff_dvd.mp hmod_pow.symm with ⟨m, hm⟩
    symm
    refine vmvE_eq_of_int_sub (m := m) ?_
    have hp0R : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hmR : (a : ℝ) * ((mulT x : ℕ) : ℝ) ^ k - ((a * t ^ k : ℕ) : ℝ) * (x : ℝ) ^ k =
        (p : ℝ) * (m : ℝ) := by
      have hm' : (a : ℤ) * ((mulT x : ℕ) : ℤ) ^ k - ((a * t ^ k : ℕ) : ℤ) * (x : ℤ) ^ k =
          (p : ℤ) * m := by
        simpa [Nat.cast_mul, Nat.cast_pow] using hm
      exact_mod_cast hm'
    field_simp [hp0R]
    linarith only [hmR]
  have hOrb_card : p - 1 ≤ Orb.card * k := by
    have hfiber : ∀ c ∈ Orb, (T.filter (fun t => orbMap t = c)).card ≤ k := by
      intro c _
      let S := T.filter (fun t => orbMap t = c)
      let f : ℕ → ZMod p := fun t => (t : ZMod p)
      let P : Polynomial (ZMod p) := Polynomial.X ^ k - Polynomial.C ((c : ZMod p) * (a : ZMod p)⁻¹)
      have hf_inj : Set.InjOn f (S : Set ℕ) := by
        intro t₁ ht₁ t₂ ht₂ h
        have ht₁_lt : t₁ < p := Finset.mem_range.mp (Finset.mem_erase.mp (Finset.mem_filter.mp ht₁).1).2
        have ht₂_lt : t₂ < p := Finset.mem_range.mp (Finset.mem_erase.mp (Finset.mem_filter.mp ht₂).1).2
        have : NeZero p := ⟨hp.ne_zero⟩
        have hv := congrArg ZMod.val h
        simp only [f] at hv
        rw [ZMod.val_natCast_of_lt ht₁_lt, ZMod.val_natCast_of_lt ht₂_lt] at hv
        exact hv
      have hsub : (S.image f).val ⊆ P.roots := by
        intro z hz
        rw [Finset.mem_val, Finset.mem_image] at hz
        rcases hz with ⟨t, ht, rfl⟩
        have ht' := (Finset.mem_filter.mp ht).2
        have ha0 : (a : ZMod p) ≠ 0 := by
          intro h0
          exact hpa ((ZMod.natCast_eq_zero_iff a p).mp h0)
        have hmod : ((a * t ^ k : ℕ) : ZMod p) = (c : ZMod p) := by
          dsimp only [orbMap] at ht'
          rw [← ht', ZMod.natCast_mod]
        have hpow : (t : ZMod p) ^ k = (c : ZMod p) * (a : ZMod p)⁻¹ := by
          have ha_mul : (a : ZMod p) * (t : ZMod p) ^ k = (c : ZMod p) := by
            simpa [Nat.cast_mul, Nat.cast_pow] using hmod
          rw [← ha_mul, mul_comm (a : ZMod p), mul_assoc, mul_inv_cancel₀ ha0, mul_one]
        refine (Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hk_pos _)).mpr ?_
        simp only [f, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, hpow, sub_self]
      have hle : (S.image f).val ≤ P.roots := (Multiset.le_iff_subset (S.image f).nodup).mpr hsub
      calc S.card = (S.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ Multiset.card P.roots := Multiset.card_le_card hle
        _ ≤ k := Polynomial.card_roots_X_pow_sub_C hk_pos _
    calc p - 1 = T.card := by
          dsimp only [T]
          rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hp_pos), Finset.card_range]
      _ = ∑ c ∈ Orb, (T.filter (fun t => orbMap t = c)).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext t
            simp only [Finset.mem_biUnion, Finset.mem_filter, Orb, Finset.mem_image]
            constructor
            · intro ht
              exact ⟨orbMap t, ⟨t, ht, rfl⟩, ht, rfl⟩
            · rintro ⟨_, _, ht, _⟩
              exact ht
          · intro c₁ _ c₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro t ht₁ ht₂
            exact hne ((Finset.mem_filter.mp ht₁).2.symm.trans (Finset.mem_filter.mp ht₂).2)
      _ ≤ ∑ _c ∈ Orb, k := Finset.sum_le_sum hfiber
      _ = Orb.card * k := by simp
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith only [this]
  have hsq_bound : ‖completeExpSum p a k‖ ^ 2 ≤ (k : ℝ) ^ 2 * (p : ℝ) := by
    have hsum_orb : (Orb.card : ℝ) * ‖completeExpSum p a k‖ ^ 2 ≤
        ∑ c ∈ T, ‖completeExpSum p c k‖ ^ 2 := by
      have heq_orb : (Orb.card : ℝ) * ‖completeExpSum p a k‖ ^ 2 =
          ∑ c ∈ Orb, ‖completeExpSum p c k‖ ^ 2 := by
        rw [Finset.sum_congr rfl fun c hc => by rw [hOrb_eq c hc]]
        simp
      rw [heq_orb]
      exact Finset.sum_le_sum_of_subset_of_nonneg hOrb_sub fun _ _ _ => sq_nonneg _
    have h1 : ((p : ℝ) - 1) * ‖completeExpSum p a k‖ ^ 2 ≤
        (k : ℝ) * ((Orb.card : ℝ) * ‖completeExpSum p a k‖ ^ 2) := by
      have hOrbR : (p : ℝ) - 1 ≤ (Orb.card : ℝ) * (k : ℝ) := by
        have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        rw [← hcast]
        exact_mod_cast hOrb_card
      calc ((p : ℝ) - 1) * ‖completeExpSum p a k‖ ^ 2
          ≤ ((Orb.card : ℝ) * (k : ℝ)) * ‖completeExpSum p a k‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hOrbR (sq_nonneg _)
        _ = (k : ℝ) * ((Orb.card : ℝ) * ‖completeExpSum p a k‖ ^ 2) := by ring
    have h2 : (k : ℝ) * ((Orb.card : ℝ) * ‖completeExpSum p a k‖ ^ 2) ≤
        (k : ℝ) * ((p : ℝ) * ((p : ℝ) - 1) * ((k : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (hsum_orb.trans hsum_sq_le) (Nat.cast_nonneg k)
    have h3 : ((p : ℝ) - 1) * ‖completeExpSum p a k‖ ^ 2 ≤
        ((p : ℝ) - 1) * ((k : ℝ) ^ 2 * (p : ℝ)) := by
      have hk1 : (k : ℝ) * ((k : ℝ) - 1) ≤ (k : ℝ) ^ 2 := by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith only [hk0]
      calc ((p : ℝ) - 1) * ‖completeExpSum p a k‖ ^ 2
          ≤ (k : ℝ) * ((p : ℝ) * ((p : ℝ) - 1) * ((k : ℝ) - 1)) := h1.trans h2
        _ = ((p : ℝ) - 1) * ((k : ℝ) * ((k : ℝ) - 1) * (p : ℝ)) := by ring
        _ ≤ ((p : ℝ) - 1) * ((k : ℝ) ^ 2 * (p : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hp1_pos.le
            exact mul_le_mul_of_nonneg_right hk1 (Nat.cast_nonneg p)
    exact le_of_mul_le_mul_left h3 hp1_pos
  have hsqrt : ‖completeExpSum p a k‖ ≤ Real.sqrt ((k : ℝ) ^ 2 * (p : ℝ)) :=
    Real.le_sqrt_of_sq_le hsq_bound
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)] at hsqrt
  exact hsqrt

private lemma vmv_two_mul_le_two_pow (τ : ℕ) : 2 * τ ≤ 2 ^ τ := by
  induction τ with
  | zero => norm_num
  | succ t ih =>
      rcases t with _ | t'
      · norm_num
      · rw [pow_succ']
        omega

/-- Intermediate prime-power complete exponential sum evaluation: for prime `p`, `p ∤ a`, `p ∤ k`,
and `2 ≤ α ≤ k`, `S(p^α, a, k) = p^(α - 1)`. -/
theorem completeExpSum_prime_pow_intermediate {p : ℕ} (hp : p.Prime) {a : ℕ} (hpa : ¬ p ∣ a)
    {k : ℕ} (hpk : ¬ p ∣ k) {α : ℕ} (hα2 : 2 ≤ α) (hαk : α ≤ k) :
    completeExpSum (p ^ α) a k = (p : ℂ) ^ (α - 1) := by
  have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hp_pos : 0 < p := hp.pos
  let S := Finset.range (p ^ α)
  let S_div := S.filter (fun x => p ∣ x)
  let S_ndiv := S.filter (fun x => ¬ p ∣ x)
  rw [completeExpSum_eq_sum_vmvE, ← Finset.sum_filter_add_sum_filter_not S (fun x => p ∣ x)]
  have hpart1 : ∑ x ∈ S_div, vmvE ((a : ℝ) * (x : ℝ) ^ k / (p ^ α : ℕ)) = (p : ℂ) ^ (α - 1) := by
    have hbij : ((Finset.range (p ^ (α - 1))).image (fun u => p * u)) = S_div := by
      ext x
      simp only [Finset.mem_image, Finset.mem_range, S_div, Finset.mem_filter, S]
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨?_, dvd_mul_right p u⟩
        calc p * u < p * p ^ (α - 1) := Nat.mul_lt_mul_of_pos_left hu hp_pos
          _ = p ^ α := by
              conv_rhs => rw [show α = (α - 1) + 1 by omega, pow_succ']
      · rintro ⟨hx, ⟨u, rfl⟩⟩
        refine ⟨u, ?_, rfl⟩
        have hmul : p * u < p * p ^ (α - 1) := by
          calc p * u < p ^ α := hx
            _ = p * p ^ (α - 1) := by conv_lhs => rw [show α = (α - 1) + 1 by omega, pow_succ']
        exact Nat.lt_of_mul_lt_mul_left hmul
    have hinj : Set.InjOn (fun u => p * u) (Finset.range (p ^ (α - 1)) : Set ℕ) := fun u₁ _ u₂ _ h =>
      Nat.eq_of_mul_eq_mul_left hp_pos h
    rw [← hbij, Finset.sum_image (fun u₁ hu₁ u₂ hu₂ h => hinj hu₁ hu₂ h)]
    have hone : ∀ u ∈ Finset.range (p ^ (α - 1)),
        vmvE ((a : ℝ) * ((p * u : ℕ) : ℝ) ^ k / (p ^ α : ℕ)) = 1 := by
      intro u _
      refine (vmvE_eq_one_iff_int _).mpr ⟨(a * p ^ (k - α) * u ^ k : ℤ), ?_⟩
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hsplit : (p : ℝ) ^ k = (p : ℝ) ^ α * (p : ℝ) ^ (k - α) := by
        rw [← pow_add, Nat.add_sub_cancel' hαk]
      push_cast
      rw [mul_pow, hsplit]
      field_simp [hp0]
    rw [Finset.sum_congr rfl hone]
    simp [Nat.cast_pow]
  have hpart2 : ∑ x ∈ S_ndiv, vmvE ((a : ℝ) * (x : ℝ) ^ k / (p ^ α : ℕ)) = 0 := by
    let Y := (Finset.range (p ^ (α - 1))).filter (fun y => ¬ p ∣ y)
    let φ : ℕ × ℕ → ℕ := fun yz => yz.1 + p ^ (α - 1) * yz.2
    have hφ_img : (Y ×ˢ Finset.range p).image φ = S_ndiv := by
      ext x
      simp only [Finset.mem_image, Finset.mem_product, Y, Finset.mem_filter, Finset.mem_range,
        S_ndiv, S, φ]
      constructor
      · rintro ⟨⟨y, z⟩, ⟨⟨hy, hpy⟩, hz⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · calc y + p ^ (α - 1) * z
              < p ^ (α - 1) + p ^ (α - 1) * z := by omega
            _ = p ^ (α - 1) * (z + 1) := by ring
            _ ≤ p ^ (α - 1) * p := Nat.mul_le_mul_left _ hz
            _ = p ^ α := by conv_rhs => rw [show α = (α - 1) + 1 by omega, pow_succ]
        · intro hdvd
          have hd_pow : p ∣ p ^ (α - 1) := dvd_pow_self p (by omega)
          have hd_mul : p ∣ p ^ (α - 1) * z := dvd_mul_of_dvd_left hd_pow z
          exact hpy ((Nat.dvd_add_left hd_mul).mp hdvd)
      · rintro ⟨hx, hpx⟩
        refine ⟨⟨x % p ^ (α - 1), x / p ^ (α - 1)⟩, ⟨⟨Nat.mod_lt _ (pow_pos hp_pos _), ?_⟩, ?_⟩,
          Nat.mod_add_div x (p ^ (α - 1))⟩
        · intro hdvd
          have hd_pow : p ∣ p ^ (α - 1) := dvd_pow_self p (by omega)
          have hd_mul : p ∣ p ^ (α - 1) * (x / p ^ (α - 1)) := dvd_mul_of_dvd_left hd_pow _
          have hsum_dvd : p ∣ x % p ^ (α - 1) + p ^ (α - 1) * (x / p ^ (α - 1)) :=
            dvd_add hdvd hd_mul
          rw [Nat.mod_add_div] at hsum_dvd
          exact hpx hsum_dvd
        · have hx' : x < p ^ (α - 1) * p := by
            calc x < p ^ α := hx
              _ = p ^ (α - 1) * p := by conv_lhs => rw [show α = (α - 1) + 1 by omega, pow_succ]
          exact Nat.div_lt_of_lt_mul ((mul_comm (p ^ (α - 1)) p) ▸ hx')
    have hφ_inj : Set.InjOn φ ↑(Y ×ˢ Finset.range p) := by
      intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
      have hp1_lt : p₁.1 < p ^ (α - 1) := Finset.mem_range.mp (Finset.mem_filter.mp hp₁.1).1
      have hp2_lt : p₂.1 < p ^ (α - 1) := Finset.mem_range.mp (Finset.mem_filter.mp hp₂.1).1
      have h1 : p₁.1 = p₂.1 := by
        have hm1 : φ p₁ % p ^ (α - 1) = p₁.1 := by
          dsimp only [φ]
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hp1_lt
        have hm2 : φ p₂ % p ^ (α - 1) = p₂.1 := by
          dsimp only [φ]
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hp2_lt
        rw [← hm1, ← hm2, heq]
      have h2 : p₁.2 = p₂.2 := by
        have hd1 : φ p₁ / p ^ (α - 1) = p₁.2 := by
          dsimp only [φ]
          rw [Nat.add_mul_div_left _ _ (pow_pos hp_pos _), Nat.div_eq_of_lt hp1_lt, zero_add]
        have hd2 : φ p₂ / p ^ (α - 1) = p₂.2 := by
          dsimp only [φ]
          rw [Nat.add_mul_div_left _ _ (pow_pos hp_pos _), Nat.div_eq_of_lt hp2_lt, zero_add]
        rw [← hd1, ← hd2, heq]
      exact Prod.ext h1 h2
    rw [← hφ_img, Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hφ_inj hp₁ hp₂ h), Finset.sum_product]
    refine Finset.sum_eq_zero fun y hy => ?_
    have hpy : ¬ p ∣ y := (Finset.mem_filter.mp hy).2
    have hbin : ∀ z : ℕ, ∃ m : ℤ,
        ((y + p ^ (α - 1) * z : ℕ) : ℤ) ^ k -
          ((y : ℤ) ^ k + (k : ℤ) * (y : ℤ) ^ (k - 1) * ((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ)) =
          ((p ^ α : ℕ) : ℤ) * m := by
      intro z
      have hpow_z : ((y + p ^ (α - 1) * z : ℕ) : ℤ) ^ k =
          ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℤ) * (y : ℤ) ^ (k - j) * (((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ)) ^ j := by
        push_cast
        rw [add_comm (y : ℤ) _, add_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hpow_z, Finset.sum_range_succ']
      simp only [pow_zero, mul_one, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', hk'⟩
      have hsucc : ∑ j ∈ Finset.range k,
          ((k.choose (j + 1) : ℤ) * (y : ℤ) ^ (k - (j + 1)) *
            (((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ)) ^ (j + 1)) =
          (k : ℤ) * (y : ℤ) ^ (k - 1) * ((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ) +
            ∑ j ∈ Finset.range k',
              (((k' + 1).choose (j + 2) : ℤ) * (y : ℤ) ^ ((k' + 1) - (j + 2)) *
                (((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ)) ^ (j + 2)) := by
        have hk1 : k = k' + 1 := hk'
        rw [hk1, Finset.sum_range_succ']
        have hterm0 :
            ((k' + 1).choose (0 + 1) : ℤ) * (y : ℤ) ^ ((k' + 1) - (0 + 1)) *
                (((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ)) ^ (0 + 1) =
              ((k' + 1 : ℕ) : ℤ) * (y : ℤ) ^ ((k' + 1) - 1) * ((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ) := by
          simp only [zero_add, Nat.choose_one_right, pow_one]
          ring
        rw [hterm0, add_comm]
      rw [hsucc]
      have hdvd : ((p ^ α : ℕ) : ℤ) ∣
          ∑ j ∈ Finset.range k',
            (((k' + 1).choose (j + 2) : ℤ) * (y : ℤ) ^ ((k' + 1) - (j + 2)) *
              (((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ)) ^ (j + 2)) := by
        refine Finset.dvd_sum fun j _ => ?_
        rw [mul_pow]
        push_cast
        rw [← pow_mul]
        have hexp : α ≤ (α - 1) * (j + 2) := by
          calc α ≤ (α - 1) * 2 := by omega
            _ ≤ (α - 1) * (j + 2) := Nat.mul_le_mul_left _ (by omega)
        have hp_dvd : (p : ℤ) ^ α ∣ (p : ℤ) ^ ((α - 1) * (j + 2)) := by
          exact_mod_cast Nat.pow_dvd_pow p hexp
        have hdvd1 : (p : ℤ) ^ α ∣ (p : ℤ) ^ ((α - 1) * (j + 2)) * (z : ℤ) ^ (j + 2) :=
          dvd_mul_of_dvd_left hp_dvd _
        exact dvd_mul_of_dvd_right hdvd1 _
      rcases hdvd with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      linarith only [hm]
    have hsplit_sum :
        ∑ z ∈ Finset.range p, vmvE ((a : ℝ) * ((φ (y, z) : ℕ) : ℝ) ^ k / (p ^ α : ℕ)) =
          vmvE ((a : ℝ) * (y : ℝ) ^ k / (p ^ α : ℕ)) *
            ∑ z ∈ Finset.range p, vmvE (((a * k * y ^ (k - 1) : ℤ) : ℝ) * (z : ℝ) / p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← vmvE_add]
      rcases hbin z with ⟨m, hm⟩
      refine vmvE_eq_of_int_sub (m := (a : ℤ) * m) ?_
      have hp0R : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpa0R : ((p ^ α : ℕ) : ℝ) ≠ 0 := by positivity
      have hmR : ((a : ℝ) * ((φ (y, z) : ℕ) : ℝ) ^ k -
          ((a : ℝ) * (y : ℝ) ^ k + (a * k * y ^ (k - 1) : ℝ) * ((p ^ (α - 1) : ℕ) : ℝ) * (z : ℝ))) =
          ((p ^ α : ℕ) : ℝ) * ((a : ℤ) * m : ℤ) := by
        have hm' : (a : ℤ) * (((φ (y, z) : ℕ) : ℤ) ^ k -
            ((y : ℤ) ^ k + (k : ℤ) * (y : ℤ) ^ (k - 1) * ((p ^ (α - 1) : ℕ) : ℤ) * (z : ℤ))) =
            ((p ^ α : ℕ) : ℤ) * ((a : ℤ) * m) := by
          dsimp only [φ]
          rw [hm]
          ring
        have := congrArg (Int.cast (R := ℝ)) hm'
        push_cast at this
        push_cast
        linarith only [this]
      have hdiv : (p : ℝ) ^ α = (p : ℝ) * (p : ℝ) ^ (α - 1) := by
        conv_lhs => rw [show α = (α - 1) + 1 by omega, pow_succ']
      push_cast at hmR ⊢
      rw [hdiv] at hmR ⊢
      field_simp [hp0R, pow_ne_zero (α - 1) hp0R]
      linarith only [hmR]
    rw [hsplit_sum, completeExpSum_linear_int_eq p hp_pos]
    have hndvd : ¬ (p : ℤ) ∣ (a * k * y ^ (k - 1) : ℤ) := by
      intro hd
      have hdN : p ∣ a * k * y ^ (k - 1) := by exact_mod_cast hd
      rcases hp.dvd_mul.mp hdN with hak | hyk
      · rcases hp.dvd_mul.mp hak with ha | hk'
        · exact hpa ha
        · exact hpk hk'
      · exact hpy (hp.dvd_of_dvd_pow hyk)
    simp only [hndvd, ↓reduceIte, mul_zero]
  rw [hpart1, hpart2, add_zero]

/-- Prime-power reduction identity for complete exponential sums: for prime `p`, `p ∤ a`,
`k ≥ 1`, `p^τ ∣ k`, `¬ p^(τ+1) ∣ k`, and `α ≥ max k (2 τ + 2)`,
`S(p^α, a, k) = p^(k - 1) * S(p^(α - k), a, k)`. -/
theorem completeExpSum_prime_pow_reduction {p : ℕ} (hp : p.Prime) {a : ℕ} (hpa : ¬ p ∣ a)
    {k : ℕ} (hk : 1 ≤ k) {τ : ℕ} (hτ1 : p ^ τ ∣ k) (hτ2 : ¬ p ^ (τ + 1) ∣ k)
    {α : ℕ} (hαk : k ≤ α) (hατ : 2 * τ + 2 ≤ α) :
    completeExpSum (p ^ α) a k = (p : ℂ) ^ (k - 1) * completeExpSum (p ^ (α - k)) a k := by
  have hp_pos : 0 < p := hp.pos
  have hα2 : 2 ≤ α := by omega
  let S := Finset.range (p ^ α)
  let S_div := S.filter (fun x => p ∣ x)
  let S_ndiv := S.filter (fun x => ¬ p ∣ x)
  rw [completeExpSum_eq_sum_vmvE, ← Finset.sum_filter_add_sum_filter_not S (fun x => p ∣ x)]
  have hpart1 :
      ∑ x ∈ S_div, vmvE ((a : ℝ) * (x : ℝ) ^ k / (p ^ α : ℕ)) =
        (p : ℂ) ^ (k - 1) * completeExpSum (p ^ (α - k)) a k := by
    let U := Finset.range (p ^ (α - k)) ×ˢ Finset.range (p ^ (k - 1))
    let ψ : ℕ × ℕ → ℕ := fun uq => p * (uq.1 + p ^ (α - k) * uq.2)
    have hψ_img : U.image ψ = S_div := by
      ext x
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, U, S_div, Finset.mem_filter,
        S, ψ]
      constructor
      · rintro ⟨⟨u₀, q₀⟩, ⟨hu₀, hq₀⟩, rfl⟩
        refine ⟨?_, dvd_mul_right p _⟩
        have hlt_in : u₀ + p ^ (α - k) * q₀ < p ^ (α - 1) := by
          calc u₀ + p ^ (α - k) * q₀
              < p ^ (α - k) + p ^ (α - k) * q₀ := by omega
            _ = p ^ (α - k) * (q₀ + 1) := by ring
            _ ≤ p ^ (α - k) * p ^ (k - 1) := Nat.mul_le_mul_left _ hq₀
            _ = p ^ (α - 1) := by rw [← pow_add]; congr 1; omega
        calc p * (u₀ + p ^ (α - k) * q₀) < p * p ^ (α - 1) := Nat.mul_lt_mul_of_pos_left hlt_in hp_pos
          _ = p ^ α := by conv_rhs => rw [show α = (α - 1) + 1 by omega, pow_succ']
      · rintro ⟨hx, ⟨u, rfl⟩⟩
        have hu_lt : u < p ^ (α - 1) := by
          have h1 : p * u < p * p ^ (α - 1) := by
            calc p * u < p ^ α := hx
              _ = p * p ^ (α - 1) := by conv_lhs => rw [show α = (α - 1) + 1 by omega, pow_succ']
          exact Nat.lt_of_mul_lt_mul_left h1
        refine ⟨⟨u % p ^ (α - k), u / p ^ (α - k)⟩,
          ⟨Nat.mod_lt _ (pow_pos hp_pos _), ?_⟩, ?_⟩
        · have h1 : u < p ^ (α - k) * p ^ (k - 1) := by
            rw [← pow_add]
            convert hu_lt using 2
            omega
          exact Nat.div_lt_of_lt_mul ((mul_comm (p ^ (α - k)) (p ^ (k - 1))) ▸ h1)
        · rw [Nat.mod_add_div]
    have hψ_inj : Set.InjOn ψ ↑U := by
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, U] at hp₁ hp₂
      have heq' : p₁.1 + p ^ (α - k) * p₁.2 = p₂.1 + p ^ (α - k) * p₂.2 :=
        Nat.eq_of_mul_eq_mul_left hp_pos heq
      have h1 : p₁.1 = p₂.1 := by
        have hm1 : (p₁.1 + p ^ (α - k) * p₁.2) % p ^ (α - k) = p₁.1 := by
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hp₁.1
        have hm2 : (p₂.1 + p ^ (α - k) * p₂.2) % p ^ (α - k) = p₂.1 := by
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hp₂.1
        rw [← hm1, ← hm2, heq']
      have h2 : p₁.2 = p₂.2 := by
        have hd1 : (p₁.1 + p ^ (α - k) * p₁.2) / p ^ (α - k) = p₁.2 := by
          rw [Nat.add_mul_div_left _ _ (pow_pos hp_pos _), Nat.div_eq_of_lt hp₁.1, zero_add]
        have hd2 : (p₂.1 + p ^ (α - k) * p₂.2) / p ^ (α - k) = p₂.2 := by
          rw [Nat.add_mul_div_left _ _ (pow_pos hp_pos _), Nat.div_eq_of_lt hp₂.1, zero_add]
        rw [← hd1, ← hd2, heq']
      exact Prod.ext h1 h2
    rw [← hψ_img, Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hψ_inj hp₁ hp₂ h), Finset.sum_product]
    have hterm : ∀ u₀ ∈ Finset.range (p ^ (α - k)), ∀ q₀ ∈ Finset.range (p ^ (k - 1)),
        vmvE ((a : ℝ) * ((ψ (u₀, q₀) : ℕ) : ℝ) ^ k / (p ^ α : ℕ)) =
          vmvE ((a : ℝ) * (u₀ : ℝ) ^ k / (p ^ (α - k) : ℕ)) := by
      intro u₀ _ q₀ _
      have hmod_pow : ((u₀ + p ^ (α - k) * q₀ : ℕ) : ℤ) ^ k ≡ (u₀ : ℤ) ^ k [ZMOD ((p ^ (α - k) : ℕ) : ℤ)] := by
        refine Int.ModEq.pow k ?_
        rw [Int.natCast_modEq_iff, Nat.ModEq, Nat.add_mul_mod_self_left]
      rcases Int.modEq_iff_dvd.mp hmod_pow with ⟨m, hm⟩
      refine vmvE_eq_of_int_sub (m := -(a : ℤ) * m) ?_
      have hmR : (u₀ : ℝ) ^ k - ((u₀ : ℝ) + ((p ^ (α - k) : ℕ) : ℝ) * q₀) ^ k =
          ((p ^ (α - k) : ℕ) : ℝ) * (m : ℝ) := by exact_mod_cast hm
      have hp0R : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hsplit : (p : ℝ) ^ α = (p : ℝ) ^ k * (p : ℝ) ^ (α - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hαk]
      dsimp only [ψ]
      push_cast
      rw [mul_pow, hsplit]
      have hpow_ne : (p : ℝ) ^ k ≠ 0 := pow_ne_zero k hp0R
      have hsub_ne : (p : ℝ) ^ (α - k) ≠ 0 := pow_ne_zero (α - k) hp0R
      rw [mul_comm ((p : ℝ) ^ k) (((u₀ : ℝ) + (p : ℝ) ^ (α - k) * q₀) ^ k),
        ← mul_assoc (a : ℝ), mul_comm ((p : ℝ) ^ k) ((p : ℝ) ^ (α - k)),
        mul_div_mul_right _ _ hpow_ne, ← sub_div, ← mul_sub]
      push_cast at hmR
      have hmR' : ((u₀ : ℝ) + (p : ℝ) ^ (α - k) * (q₀ : ℝ)) ^ k - (u₀ : ℝ) ^ k =
          (p : ℝ) ^ (α - k) * (-m : ℝ) := by
        linarith only [hmR]
      rw [hmR']
      have hcancel : (a : ℝ) * ((p : ℝ) ^ (α - k) * (-m : ℝ)) / (p : ℝ) ^ (α - k) =
          -((a : ℝ) * (m : ℝ)) := by
        rw [mul_comm ((p : ℝ) ^ (α - k)) _, ← mul_assoc, mul_div_cancel_right₀ _ hsub_ne]
        ring
      rw [hcancel]
      ring
    calc ∑ u₀ ∈ Finset.range (p ^ (α - k)), ∑ q₀ ∈ Finset.range (p ^ (k - 1)),
            vmvE ((a : ℝ) * ((ψ (u₀, q₀) : ℕ) : ℝ) ^ k / (p ^ α : ℕ))
        = ∑ u₀ ∈ Finset.range (p ^ (α - k)), ∑ _q₀ ∈ Finset.range (p ^ (k - 1)),
            vmvE ((a : ℝ) * (u₀ : ℝ) ^ k / (p ^ (α - k) : ℕ)) := by
            refine Finset.sum_congr rfl fun u₀ hu₀ => Finset.sum_congr rfl fun q₀ hq₀ =>
              hterm u₀ hu₀ q₀ hq₀
      _ = ∑ u₀ ∈ Finset.range (p ^ (α - k)),
            (p : ℂ) ^ (k - 1) * vmvE ((a : ℝ) * (u₀ : ℝ) ^ k / (p ^ (α - k) : ℕ)) := by
            refine Finset.sum_congr rfl fun u₀ _ => ?_
            simp [Nat.cast_pow]
      _ = (p : ℂ) ^ (k - 1) * completeExpSum (p ^ (α - k)) a k := by
            rw [← Finset.mul_sum, completeExpSum_eq_sum_vmvE]
  have hpart2 : ∑ x ∈ S_ndiv, vmvE ((a : ℝ) * (x : ℝ) ^ k / (p ^ α : ℕ)) = 0 := by
    let t := α - τ - 1
    have ht1 : 1 ≤ t := by omega
    have ht_lt : t < α := by omega
    have hα_split : t + (τ + 1) = α := by omega
    let Y := (Finset.range (p ^ t)).filter (fun y => ¬ p ∣ y)
    let φ : ℕ × ℕ → ℕ := fun yz => yz.1 + p ^ t * yz.2
    have hφ_img : (Y ×ˢ Finset.range (p ^ (τ + 1))).image φ = S_ndiv := by
      ext x
      simp only [Finset.mem_image, Finset.mem_product, Y, Finset.mem_filter, Finset.mem_range,
        S_ndiv, S, φ]
      constructor
      · rintro ⟨⟨y, z⟩, ⟨⟨hy, hpy⟩, hz⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · calc y + p ^ t * z < p ^ t + p ^ t * z := by omega
            _ = p ^ t * (z + 1) := by ring
            _ ≤ p ^ t * p ^ (τ + 1) := Nat.mul_le_mul_left _ hz
            _ = p ^ α := by rw [← pow_add, hα_split]
        · intro hdvd
          have hd_pow : p ∣ p ^ t := dvd_pow_self p (by omega)
          have hd_mul : p ∣ p ^ t * z := dvd_mul_of_dvd_left hd_pow z
          exact hpy ((Nat.dvd_add_left hd_mul).mp hdvd)
      · rintro ⟨hx, hpx⟩
        refine ⟨⟨x % p ^ t, x / p ^ t⟩, ⟨⟨Nat.mod_lt _ (pow_pos hp_pos _), ?_⟩, ?_⟩,
          Nat.mod_add_div x (p ^ t)⟩
        · intro hdvd
          have hd_pow : p ∣ p ^ t := dvd_pow_self p (by omega)
          have hd_mul : p ∣ p ^ t * (x / p ^ t) := dvd_mul_of_dvd_left hd_pow _
          have hsum_dvd : p ∣ x % p ^ t + p ^ t * (x / p ^ t) := dvd_add hdvd hd_mul
          rw [Nat.mod_add_div] at hsum_dvd
          exact hpx hsum_dvd
        · have hx' : x < p ^ t * p ^ (τ + 1) := by
            calc x < p ^ α := hx
              _ = p ^ t * p ^ (τ + 1) := by rw [← pow_add, hα_split]
          exact Nat.div_lt_of_lt_mul ((mul_comm (p ^ t) (p ^ (τ + 1))) ▸ hx')
    have hφ_inj : Set.InjOn φ ↑(Y ×ˢ Finset.range (p ^ (τ + 1))) := by
      intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
      have hp1_lt : p₁.1 < p ^ t := Finset.mem_range.mp (Finset.mem_filter.mp hp₁.1).1
      have hp2_lt : p₂.1 < p ^ t := Finset.mem_range.mp (Finset.mem_filter.mp hp₂.1).1
      have h1 : p₁.1 = p₂.1 := by
        have hm1 : φ p₁ % p ^ t = p₁.1 := by
          dsimp only [φ]
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hp1_lt
        have hm2 : φ p₂ % p ^ t = p₂.1 := by
          dsimp only [φ]
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hp2_lt
        rw [← hm1, ← hm2, heq]
      have h2 : p₁.2 = p₂.2 := by
        have hd1 : φ p₁ / p ^ t = p₁.2 := by
          dsimp only [φ]
          rw [Nat.add_mul_div_left _ _ (pow_pos hp_pos _), Nat.div_eq_of_lt hp1_lt, zero_add]
        have hd2 : φ p₂ / p ^ t = p₂.2 := by
          dsimp only [φ]
          rw [Nat.add_mul_div_left _ _ (pow_pos hp_pos _), Nat.div_eq_of_lt hp2_lt, zero_add]
        rw [← hd1, ← hd2, heq]
      exact Prod.ext h1 h2
    rcases hτ1 with ⟨m, hm_k⟩
    have hpm : ¬ p ∣ m := by
      intro hpm
      apply hτ2
      rcases hpm with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [hm_k, hr, pow_succ]
      ring
    rw [← hφ_img, Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => hφ_inj hp₁ hp₂ h), Finset.sum_product]
    refine Finset.sum_eq_zero fun y hy => ?_
    have hpy : ¬ p ∣ y := (Finset.mem_filter.mp hy).2
    have hbin : ∀ z : ℕ, ∃ q₀ : ℤ,
        ((φ (y, z) : ℕ) : ℤ) ^ k -
          ((y : ℤ) ^ k + (k : ℤ) * (y : ℤ) ^ (k - 1) * ((p ^ t : ℕ) : ℤ) * (z : ℤ)) =
          ((p ^ α : ℕ) : ℤ) * q₀ := by
      intro z
      dsimp only [φ]
      have hpow_z : ((y + p ^ t * z : ℕ) : ℤ) ^ k =
          ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℤ) * (y : ℤ) ^ (k - j) * (((p ^ t : ℕ) : ℤ) * (z : ℤ)) ^ j := by
        push_cast
        rw [add_comm (y : ℤ) _, add_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hpow_z, Finset.sum_range_succ']
      simp only [pow_zero, mul_one, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', hk'⟩
      have hsucc : ∑ j ∈ Finset.range k,
          ((k.choose (j + 1) : ℤ) * (y : ℤ) ^ (k - (j + 1)) *
            (((p ^ t : ℕ) : ℤ) * (z : ℤ)) ^ (j + 1)) =
          (k : ℤ) * (y : ℤ) ^ (k - 1) * ((p ^ t : ℕ) : ℤ) * (z : ℤ) +
            ∑ j ∈ Finset.range k',
              (((k' + 1).choose (j + 2) : ℤ) * (y : ℤ) ^ ((k' + 1) - (j + 2)) *
                (((p ^ t : ℕ) : ℤ) * (z : ℤ)) ^ (j + 2)) := by
        have hk1 : k = k' + 1 := hk'
        rw [hk1, Finset.sum_range_succ']
        have hterm0 :
            ((k' + 1).choose (0 + 1) : ℤ) * (y : ℤ) ^ ((k' + 1) - (0 + 1)) *
                (((p ^ t : ℕ) : ℤ) * (z : ℤ)) ^ (0 + 1) =
              ((k' + 1 : ℕ) : ℤ) * (y : ℤ) ^ ((k' + 1) - 1) * ((p ^ t : ℕ) : ℤ) * (z : ℤ) := by
          simp only [zero_add, Nat.choose_one_right, pow_one]
          ring
        rw [hterm0, add_comm]
      rw [hsucc]
      have hdvd : ((p ^ α : ℕ) : ℤ) ∣
          ∑ j ∈ Finset.range k',
            (((k' + 1).choose (j + 2) : ℤ) * (y : ℤ) ^ ((k' + 1) - (j + 2)) *
              (((p ^ t : ℕ) : ℤ) * (z : ℤ)) ^ (j + 2)) := by
        refine Finset.dvd_sum fun j _ => ?_
        rw [mul_pow]
        have hexp : α ≤ t * (j + 2) := by
          have ht2 : α ≤ t * 2 := by dsimp only [t]; omega
          exact ht2.trans (Nat.mul_le_mul_left t (by omega))
        have hp_dvd : (p ^ α : ℤ) ∣ (p : ℤ) ^ (t * (j + 2)) := by
          exact_mod_cast Nat.pow_dvd_pow p hexp
        have hdvd1 : ((p ^ α : ℕ) : ℤ) ∣ (((p ^ t : ℕ) : ℤ) ^ (j + 2)) * (z : ℤ) ^ (j + 2) := by
          push_cast
          rw [← pow_mul]
          exact dvd_mul_of_dvd_left hp_dvd _
        exact dvd_mul_of_dvd_right hdvd1 _
      rcases hdvd with ⟨q₀, hq₀⟩
      refine ⟨q₀, ?_⟩
      linarith only [hq₀]
    have hsplit_sum :
        ∑ z ∈ Finset.range (p ^ (τ + 1)), vmvE ((a : ℝ) * ((φ (y, z) : ℕ) : ℝ) ^ k / (p ^ α : ℕ)) =
          vmvE ((a : ℝ) * (y : ℝ) ^ k / (p ^ α : ℕ)) *
            ∑ z ∈ Finset.range (p ^ (τ + 1)),
              vmvE (((a * m * y ^ (k - 1) * p ^ τ : ℤ) : ℝ) * (z : ℝ) / (p ^ (τ + 1) : ℕ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← vmvE_add]
      rcases hbin z with ⟨q₀, hq₀⟩
      refine vmvE_eq_of_int_sub (m := (a : ℤ) * q₀) ?_
      have hp0R : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hdiv : (p : ℝ) ^ α = (p : ℝ) ^ t * (p : ℝ) ^ (τ + 1) := by
        rw [← pow_add, hα_split]
      have hkR : (k : ℝ) = (p : ℝ) ^ τ * (m : ℝ) := by exact_mod_cast hm_k
      have hmR : (a : ℝ) * ((φ (y, z) : ℕ) : ℝ) ^ k -
          ((a : ℝ) * (y : ℝ) ^ k +
            ((a : ℝ) * m * (y : ℝ) ^ (k - 1) * (p : ℝ) ^ τ) * ((p ^ t : ℕ) : ℝ) * (z : ℝ)) =
          ((p ^ α : ℕ) : ℝ) * ((a : ℤ) * q₀ : ℤ) := by
        have hm' : (a : ℤ) * (((φ (y, z) : ℕ) : ℤ) ^ k -
            ((y : ℤ) ^ k + (k : ℤ) * (y : ℤ) ^ (k - 1) * ((p ^ t : ℕ) : ℤ) * (z : ℤ))) =
            ((p ^ α : ℕ) : ℤ) * ((a : ℤ) * q₀) := by
          rw [hq₀]
          ring
        have := congrArg (Int.cast (R := ℝ)) hm'
        push_cast at this
        rw [hkR] at this
        push_cast
        linarith only [this]
      push_cast at hmR ⊢
      rw [hdiv] at hmR ⊢
      field_simp [hp0R, pow_ne_zero t hp0R, pow_ne_zero (τ + 1) hp0R]
      linarith only [hmR]
    rw [hsplit_sum, completeExpSum_linear_int_eq (p ^ (τ + 1)) (pow_pos hp_pos _)]
    have hndvd : ¬ ((p ^ (τ + 1) : ℕ) : ℤ) ∣ (a * m * y ^ (k - 1) * p ^ τ : ℤ) := by
      intro hd
      have hdN : p ^ (τ + 1) ∣ a * m * y ^ (k - 1) * p ^ τ := by exact_mod_cast hd
      have hd' : p * p ^ τ ∣ (a * m * y ^ (k - 1)) * p ^ τ := by
        simpa [pow_succ', mul_comm] using hdN
      have hpdvd : p ∣ a * m * y ^ (k - 1) :=
        (Nat.mul_dvd_mul_iff_right (pow_pos hp_pos τ)).mp hd'
      rcases hp.dvd_mul.mp hpdvd with ham | hyk
      · rcases hp.dvd_mul.mp ham with ha | hm'
        · exact hpa ha
        · exact hpm hm'
      · exact hpy (hp.dvd_of_dvd_pow hyk)
    simp only [hndvd, ↓reduceIte, mul_zero]
  rw [hpart1, hpart2, add_zero]

private lemma completeExpSum_prime_pow_bound {k : ℕ} (hk3 : 3 ≤ k) {p : ℕ} (hp : p.Prime) :
    ∀ (α a : ℕ), 1 ≤ α → ¬ p ∣ a →
      ‖completeExpSum (p ^ α) a k‖ ≤
        (if p < k ^ 6 then (k : ℝ) ^ 18 else 1) * ((p ^ α : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  have hk_pos : 0 < k := by omega
  have hk0R : (k : ℝ) ≠ 0 := by exact_mod_cast hk_pos.ne'
  have hp_pos : 0 < p := hp.pos
  have hp1R : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hexp_nn : 0 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk_pos) (by positivity)
    linarith only [this]
  have hstep_alg : ∀ α₀ : ℕ, k ≤ α₀ →
      (p : ℝ) ^ (k - 1) * ((p ^ (α₀ - k) : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) =
        ((p ^ α₀ : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    intro α₀ hαk
    push_cast
    rw [← Real.rpow_natCast (p : ℝ) (k - 1), ← Real.rpow_natCast (p : ℝ) (α₀ - k),
      ← Real.rpow_natCast (p : ℝ) α₀, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p),
      ← Real.rpow_add (by positivity : (0 : ℝ) < p)]
    congr 1
    have h1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have h2 : ((α₀ - k : ℕ) : ℝ) = (α₀ : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hαk]
    rw [h1, h2]
    field_simp [hk0R]
    ring
  intro α
  induction α using Nat.strongRecOn with
  | ind α ih =>
      intro a hα hpa
      by_cases hpl : k ^ 6 ≤ p
      · simp only [not_lt.mpr hpl, ↓reduceIte, one_mul]
        have hpk : ¬ p ∣ k := by
          apply Nat.not_dvd_of_pos_of_lt hk_pos
          have hk2 : k < k ^ 6 := by
            calc k = k * 1 := (mul_one k).symm
              _ < k * k ^ 5 := Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow (by omega) (by omega)) hk_pos
              _ = k ^ 6 := by ring
          exact hk2.trans_le hpl
        rcases Nat.eq_or_lt_of_le hα with rfl | hα2
        · rw [pow_one]
          have hp_prime_bd := completeExpSum_prime_bound hp hpa (by omega : 1 ≤ k)
          have hk6R : (k : ℝ) ^ 6 ≤ (p : ℝ) := by exact_mod_cast hpl
          have hk_rpow : (k : ℝ) ≤ (p : ℝ) ^ (1 / 6 : ℝ) := by
            calc (k : ℝ) = ((k : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := by
                  rw [← Real.rpow_natCast (k : ℝ) 6, ← Real.rpow_mul (Nat.cast_nonneg k)]
                  norm_num
              _ ≤ (p : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) hk6R (by norm_num)
          have hsqrt : Real.sqrt (p : ℝ) = (p : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow p
          have h23 : (2 / 3 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
            have hk3R : (3 : ℝ) ≤ k := by exact_mod_cast hk3
            have h1k : 1 / (k : ℝ) ≤ 1 / 3 :=
              one_div_le_one_div_of_le (by norm_num) hk3R
            linarith only [h1k]
          calc ‖completeExpSum p a k‖ ≤ (k : ℝ) * Real.sqrt (p : ℝ) := hp_prime_bd
            _ ≤ (p : ℝ) ^ (1 / 6 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by
                rw [hsqrt]
                exact mul_le_mul_of_nonneg_right hk_rpow (by positivity)
            _ = (p : ℝ) ^ (2 / 3 : ℝ) := by
                rw [← Real.rpow_add (by positivity : (0 : ℝ) < p)]
                norm_num
            _ ≤ (p : ℝ) ^ (1 - 1 / (k : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le hp1R h23
        · by_cases hαk : α ≤ k
          · rw [completeExpSum_prime_pow_intermediate hp hpa hpk hα2 hαk, norm_pow,
              Complex.norm_natCast]
            push_cast
            rw [← Real.rpow_natCast (p : ℝ) (α - 1), ← Real.rpow_natCast (p : ℝ) α,
              ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
            refine Real.rpow_le_rpow_of_exponent_le hp1R ?_
            have h1 : ((α - 1 : ℕ) : ℝ) = (α : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ α), Nat.cast_one]
            rw [h1]
            have hα_div : (α : ℝ) / (k : ℝ) ≤ 1 :=
              (div_le_one (by exact_mod_cast hk_pos)).mpr (by exact_mod_cast hαk)
            have heq : (α : ℝ) * (1 - 1 / (k : ℝ)) = (α : ℝ) - (α : ℝ) / (k : ℝ) := by ring
            linarith only [hα_div, heq]
          · have hα_gt : k < α := not_le.mp hαk
            have hτ1 : p ^ 0 ∣ k := by simp
            have hτ2 : ¬ p ^ (0 + 1) ∣ k := by simpa using hpk
            have hred := completeExpSum_prime_pow_reduction hp hpa (by omega : 1 ≤ k) hτ1 hτ2
              hα_gt.le (by omega : 2 * 0 + 2 ≤ α)
            rw [hred, norm_mul, norm_pow, Complex.norm_natCast]
            have ih' := ih (α - k) (by omega) a (by omega) hpa
            simp only [not_lt.mpr hpl, ↓reduceIte, one_mul] at ih'
            calc (p : ℝ) ^ (k - 1) * ‖completeExpSum (p ^ (α - k)) a k‖
                ≤ (p : ℝ) ^ (k - 1) * ((p ^ (α - k) : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) :=
                    mul_le_mul_of_nonneg_left ih' (by positivity)
              _ = ((p ^ α : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) := hstep_alg α hα_gt.le
      · have hlt : p < k ^ 6 := not_le.mp hpl
        simp only [hlt, ↓reduceIte]
        let τ := k.factorization p
        have hτ1 : p ^ τ ∣ k := Nat.ordProj_dvd k p
        have hτ2 : ¬ p ^ (τ + 1) ∣ k := by
          rw [hp.pow_dvd_iff_le_factorization hk_pos.ne']
          exact Nat.not_succ_le_self τ
        have h2τ_le : 2 ^ τ ≤ p ^ τ := Nat.pow_le_pow_left hp.two_le τ
        have hpτ_le : p ^ τ ≤ k := Nat.le_of_dvd hk_pos hτ1
        have h2τ_bd : 2 * τ + 2 ≤ 3 * k := by
          have := vmv_two_mul_le_two_pow τ
          omega
        by_cases hsmall : α < max k (2 * τ + 2)
        · have hα_lt : α < 3 * k := lt_of_lt_of_le hsmall (max_le (by omega) h2τ_bd)
          have htriv : ‖completeExpSum (p ^ α) a k‖ ≤ ((p ^ α : ℕ) : ℝ) := by
            rw [completeExpSum_eq_sum_vmvE]
            calc ‖∑ x ∈ Finset.range (p ^ α), vmvE ((a : ℝ) * (x : ℝ) ^ k / (p ^ α : ℕ))‖
                ≤ ∑ x ∈ Finset.range (p ^ α), ‖vmvE ((a : ℝ) * (x : ℝ) ^ k / (p ^ α : ℕ))‖ :=
                    norm_sum_le _ _
              _ = ∑ _x ∈ Finset.range (p ^ α), (1 : ℝ) := by
                    refine Finset.sum_congr rfl fun _ _ => norm_vmvE _
              _ = ((p ^ α : ℕ) : ℝ) := by simp
          have hsplit : ((p ^ α : ℕ) : ℝ) =
              ((p ^ α : ℕ) : ℝ) ^ (1 / (k : ℝ)) * ((p ^ α : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) := by
            have hpos : (0 : ℝ) < ((p ^ α : ℕ) : ℝ) := by exact_mod_cast pow_pos hp_pos α
            rw [← Real.rpow_add hpos]
            simp
          have hfac : ((p ^ α : ℕ) : ℝ) ^ (1 / (k : ℝ)) ≤ (k : ℝ) ^ 18 := by
            push_cast
            rw [← Real.rpow_natCast (p : ℝ) α, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
            have hexp_le : (α : ℝ) * (1 / (k : ℝ)) ≤ 3 := by
              have hαR : (α : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast hα_lt.le
              calc (α : ℝ) * (1 / (k : ℝ)) = (α : ℝ) / (k : ℝ) := by ring
                _ ≤ (3 * (k : ℝ)) / (k : ℝ) :=
                    div_le_div_of_nonneg_right hαR (Nat.cast_nonneg k)
                _ = 3 := by field_simp [hk0R]
            have hp_ltR : (p : ℝ) ≤ (k : ℝ) ^ 6 := by exact_mod_cast hlt.le
            calc (p : ℝ) ^ ((α : ℝ) * (1 / (k : ℝ)))
                ≤ (p : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1R hexp_le
              _ = (p : ℝ) ^ (3 : ℕ) := Real.rpow_natCast (p : ℝ) 3
              _ ≤ ((k : ℝ) ^ (6 : ℕ)) ^ (3 : ℕ) :=
                  pow_le_pow_left₀ (by positivity) hp_ltR 3
              _ = (k : ℝ) ^ 18 := by ring
          calc ‖completeExpSum (p ^ α) a k‖ ≤ ((p ^ α : ℕ) : ℝ) := htriv
            _ = ((p ^ α : ℕ) : ℝ) ^ (1 / (k : ℝ)) * ((p ^ α : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) := hsplit
            _ ≤ (k : ℝ) ^ 18 * ((p ^ α : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) :=
                mul_le_mul_of_nonneg_right hfac (by positivity)
        · have hbig : max k (2 * τ + 2) ≤ α := not_lt.mp hsmall
          have hαk : k ≤ α := (le_max_left _ _).trans hbig
          have hατ : 2 * τ + 2 ≤ α := (le_max_right _ _).trans hbig
          have hred := completeExpSum_prime_pow_reduction hp hpa (by omega : 1 ≤ k) hτ1 hτ2
            hαk hατ
          rw [hred, norm_mul, norm_pow, Complex.norm_natCast]
          rcases Nat.eq_or_lt_of_le hαk with hα_eq | hα_gt
          · have hs1 : completeExpSum (p ^ (α - k)) a k = 1 := by
              rw [← hα_eq, Nat.sub_self, pow_zero]
              simp [completeExpSum, show k ≠ 0 by omega]
            have hk18 : 1 ≤ (k : ℝ) ^ 18 := by
              have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
              exact one_le_pow₀ hk1R
            have hnorm_eq : (p : ℝ) ^ (k - 1) = ((p ^ α : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) := by
              have hstep0 := hstep_alg α hαk
              rw [show α - k = 0 by omega, pow_zero, Nat.cast_one, Real.one_rpow, mul_one] at hstep0
              exact hstep0
            rw [hs1, norm_one, mul_one, hnorm_eq]
            exact le_mul_of_one_le_left (by positivity) hk18
          · have ih' := ih (α - k) (by omega) a (by omega) hpa
            simp only [hlt, ↓reduceIte] at ih'
            calc (p : ℝ) ^ (k - 1) * ‖completeExpSum (p ^ (α - k)) a k‖
                ≤ (p : ℝ) ^ (k - 1) * ((k : ℝ) ^ 18 * ((p ^ (α - k) : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ))) :=
                    mul_le_mul_of_nonneg_left ih' (by positivity)
              _ = (k : ℝ) ^ 18 * ((p : ℝ) ^ (k - 1) * ((p ^ (α - k) : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ))) := by
                    ring
              _ = (k : ℝ) ^ 18 * ((p ^ α : ℕ) : ℝ) ^ (1 - 1 / (k : ℝ)) := by
                    rw [hstep_alg α hαk]

/-- Sharp complete exponential sum bound: for `k ≥ 1`, there exists `C > 0` (depending only on
`k`) such that for all `q ≥ 1` and `Coprime a q`, `‖S(q, a, k)‖ ≤ C * q^(1 - 1/k)`. -/
theorem completeExpSum_bound {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ), 1 ≤ q → Nat.Coprime a q →
      ‖completeExpSum q a k‖ ≤ C * (q : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  by_cases hk1 : k = 1
  · subst hk1
    refine ⟨1, zero_lt_one, fun q a hq hcop => ?_⟩
    simp only [Nat.cast_one, div_one, sub_self, Real.rpow_zero, mul_one]
    rw [completeExpSum_linear_eq hq a]
    by_cases hq1 : q = 1
    · subst hq1
      simp
    · have hndvd : ¬ q ∣ a := by
        intro hd
        have : q ∣ Nat.gcd a q := Nat.dvd_gcd hd dvd_rfl
        rw [hcop.gcd_eq_one] at this
        exact hq1 (Nat.dvd_one.mp this)
      simp only [hndvd, ↓reduceIte, norm_zero, zero_le_one]
  by_cases hk2 : k = 2
  · subst hk2
    refine ⟨Real.sqrt 2, Real.sqrt_pos.mpr zero_lt_two, fun q a hq hcop => ?_⟩
    calc ‖completeExpSum q a 2‖ ≤ Real.sqrt (2 * (q : ℝ)) :=
          completeExpSum_quadratic_bound hq hcop
      _ = Real.sqrt 2 * Real.sqrt (q : ℝ) := Real.sqrt_mul zero_le_two q
      _ = Real.sqrt 2 * (q : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) := by
          congr 1
          rw [Real.sqrt_eq_rpow]
          congr 1
          norm_num
  have hk3 : 3 ≤ k := by omega
  let B : ℝ := (k : ℝ) ^ 18
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB1 : 1 ≤ B := one_le_pow₀ hk1R
  have hmain : ∀ (q a : ℕ), 1 ≤ q → Nat.Coprime a q →
      ‖completeExpSum q a k‖ ≤
        (∏ _p ∈ q.primeFactors.filter (· < k ^ 6), B) * (q : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    intro q
    induction q using Nat.strongRecOn with
    | ind q ih =>
        intro a hq hcop
        by_cases hq1 : q = 1
        · subst hq1
          simp only [Nat.primeFactors_one, Finset.filter_empty, Finset.prod_empty,
            Nat.cast_one, Real.one_rpow, mul_one]
          rw [completeExpSum_eq_sum_vmvE, Finset.range_one, Finset.sum_singleton]
          exact (norm_vmvE _).le
        · have hq2 : 2 ≤ q := by omega
          let p := q.minFac
          have hp : p.Prime := Nat.minFac_prime hq1
          let q₁ := p ^ q.factorization p
          let q₂ := q / q₁
          have hq_mul : q₁ * q₂ = q := Nat.ordProj_mul_ordCompl_eq_self q p
          have hq0 : q ≠ 0 := by omega
          have hcop_p : Nat.Coprime p q₂ := Nat.coprime_ordCompl hp hq0
          have hcop12 : Nat.Coprime q₁ q₂ := hcop_p.pow_left (q.factorization p)
          have hq₂_pos : 1 ≤ q₂ := Nat.ordCompl_pos p hq0
          have hp_dvd : p ∣ q := Nat.minFac_dvd q
          have hfac_pos : 1 ≤ q.factorization p := (hp.dvd_iff_one_le_factorization hq0).mp hp_dvd
          have hp_le_q₁ : p ≤ q₁ := by
            have h1 : p ^ 1 ≤ p ^ (q.factorization p) := Nat.pow_le_pow_right hp.pos hfac_pos
            simpa [q₁] using h1
          have hq₂_lt : q₂ < q := by
            calc q₂ = 1 * q₂ := (one_mul q₂).symm
              _ < p * q₂ := Nat.mul_lt_mul_of_pos_right hp.one_lt hq₂_pos
              _ ≤ q₁ * q₂ := Nat.mul_le_mul_right q₂ hp_le_q₁
              _ = q := hq_mul
          have hmul := completeExpSum_mul_coprime hcop12 a hk
          rw [hq_mul] at hmul
          have hpa : ¬ p ∣ a := by
            intro h
            have hd : p ∣ Nat.gcd a q := Nat.dvd_gcd h hp_dvd
            rw [hcop.gcd_eq_one] at hd
            exact hp.ne_one (Nat.dvd_one.mp hd)
          have hpq₂ : ¬ p ∣ q₂ := Nat.not_dvd_ordCompl hp hq0
          have hpa1 : ¬ p ∣ a * q₂ ^ (k - 1) := by
            intro hd
            rcases hp.dvd_mul.mp hd with ha | hq₂'
            · exact hpa ha
            · exact hpq₂ (hp.dvd_of_dvd_pow hq₂')
          have hcop_a2 : Nat.Coprime a q₂ := by
            have hq₂_dvd : q₂ ∣ q := Nat.ordCompl_dvd q p
            exact hcop.coprime_dvd_right hq₂_dvd
          have hcop2 : Nat.Coprime (a * q₁ ^ (k - 1)) q₂ :=
            hcop_a2.mul_left (hcop12.pow_left (k - 1))
          have hbd1 := completeExpSum_prime_pow_bound hk3 hp (q.factorization p) (a * q₂ ^ (k - 1))
            hfac_pos hpa1
          have hbd2 := ih q₂ hq₂_lt (a * q₁ ^ (k - 1)) hq₂_pos hcop2
          have hq₁0 : q₁ ≠ 0 := (Nat.ordProj_pos q p).ne'
          have hq₂0 : q₂ ≠ 0 := by omega
          have hpf : q.primeFactors = insert p q₂.primeFactors := by
            rw [← hq_mul, Nat.primeFactors_mul hq₁0 hq₂0]
            have hq₁_pf : q₁.primeFactors = {p} := Nat.primeFactors_prime_pow (by omega : q.factorization p ≠ 0) hp
            rw [hq₁_pf, Finset.singleton_union]
          have hp_not_mem : p ∉ q₂.primeFactors := fun hm =>
            hpq₂ (Nat.dvd_of_mem_primeFactors hm)
          have hfilt :
              q.primeFactors.filter (· < k ^ 6) =
                if p < k ^ 6 then insert p (q₂.primeFactors.filter (· < k ^ 6))
                else q₂.primeFactors.filter (· < k ^ 6) := by
            rw [hpf]
            ext r
            simp only [Finset.mem_filter, Finset.mem_insert]
            split_ifs with hlt <;> simp only [Finset.mem_insert, Finset.mem_filter]
            · constructor
              · rintro ⟨rfl | hr, hrlt⟩
                · exact Or.inl rfl
                · exact Or.inr ⟨hr, hrlt⟩
              · rintro (rfl | ⟨hr, hrlt⟩)
                · exact ⟨Or.inl rfl, hlt⟩
                · exact ⟨Or.inr hr, hrlt⟩
            · constructor
              · rintro ⟨rfl | hr, hrlt⟩
                · exact False.elim (hlt hrlt)
                · exact ⟨hr, hrlt⟩
              · rintro ⟨hr, hrlt⟩
                exact ⟨Or.inr hr, hrlt⟩
          have hp_not_filt : p ∉ q₂.primeFactors.filter (· < k ^ 6) := fun h =>
            hp_not_mem (Finset.mem_filter.mp h).1
          have hprod_eq :
              ∏ _r ∈ q.primeFactors.filter (· < k ^ 6), B =
                (if p < k ^ 6 then B else 1) *
                  ∏ _r ∈ q₂.primeFactors.filter (· < k ^ 6), B := by
            rw [hfilt]
            split_ifs with hlt
            · rw [Finset.prod_insert hp_not_filt]
            · rw [one_mul]
          have hqrpow : (q : ℝ) ^ (1 - 1 / (k : ℝ)) =
              (q₁ : ℝ) ^ (1 - 1 / (k : ℝ)) * (q₂ : ℝ) ^ (1 - 1 / (k : ℝ)) := by
            rw [← hq_mul]
            push_cast
            exact Real.mul_rpow (Nat.cast_nonneg q₁) (Nat.cast_nonneg q₂)
          rw [hmul, norm_mul, hprod_eq, hqrpow]
          have hbd1' : ‖completeExpSum q₁ (a * q₂ ^ (k - 1)) k‖ ≤
              (if p < k ^ 6 then B else 1) * (q₁ : ℝ) ^ (1 - 1 / (k : ℝ)) := by
            simpa [q₁, B] using hbd1
          calc ‖completeExpSum q₁ (a * q₂ ^ (k - 1)) k‖ * ‖completeExpSum q₂ (a * q₁ ^ (k - 1)) k‖
              ≤ ((if p < k ^ 6 then B else 1) * (q₁ : ℝ) ^ (1 - 1 / (k : ℝ))) *
                  ((∏ _r ∈ q₂.primeFactors.filter (· < k ^ 6), B) *
                    (q₂ : ℝ) ^ (1 - 1 / (k : ℝ))) :=
                  mul_le_mul hbd1' hbd2 (norm_nonneg _) (by positivity)
            _ = _ := by ring
  let U : Finset ℕ := (Finset.range (k ^ 6)).filter Nat.Prime
  let C : ℝ := ∏ _p ∈ U, B
  have hC_pos : 0 < C := Finset.prod_pos fun _ _ => lt_of_lt_of_le zero_lt_one hB1
  refine ⟨C, hC_pos, fun q a hq hcop => ?_⟩
  have hsub : q.primeFactors.filter (· < k ^ 6) ⊆ U := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  have hprod_le : ∏ _p ∈ q.primeFactors.filter (· < k ^ 6), B ≤ C :=
    prod_const_le_of_subset_of_one_le hsub hB1
  exact (hmain q a hq hcop).trans (mul_le_mul_of_nonneg_right hprod_le (by positivity))

/-- Epsilon-relaxed complete exponential sum bound: for `k ≥ 1` and `ε ≥ 0`, there exists `C > 0`
such that for all `q ≥ 1` and `Coprime a q`, `‖S(q, a, k)‖ ≤ C * q^(1 - 1/k + ε)`. -/
theorem completeExpSum_bound_rpow {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ), 1 ≤ q → Nat.Coprime a q →
      ‖completeExpSum q a k‖ ≤ C * (q : ℝ) ^ (1 - 1 / (k : ℝ) + ε) := by
  obtain ⟨C, hC_pos, hC⟩ := completeExpSum_bound hk
  refine ⟨C, hC_pos, fun q a hq hcop => ?_⟩
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrpow : (q : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ (q : ℝ) ^ (1 - 1 / (k : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq1R (by linarith only [hε])
  exact (hC q a hq hcop).trans (mul_le_mul_of_nonneg_left hrpow hC_pos.le)

end AnalyticNumberTheory.ExponentialSums
