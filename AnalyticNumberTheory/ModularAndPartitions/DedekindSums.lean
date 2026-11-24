/-
Copyright (c) 2026 AnalyticNumberTheory-Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Dedekind Sums and Dedekind's Reciprocity Law

This file develops the theory of the periodic sawtooth function `((x))` and Dedekind sums
`s(h, k)`, culminating in a complete proof of Dedekind's reciprocity law:

- The sawtooth function `sawtoothEta x := if x = ⌊x⌋ then 0 else Int.fract x - 1 / 2`, its
  1-periodicity, oddness `((-x)) = -((x))`, strict bound `|((x))| < 1 / 2`, and Raabe's
  distribution identity `∑_{r=0}^{k-1} (((x + r) / k)) = ((x))`.
- The Dedekind sum `dedekindSum h k := ∑_{r=1}^{k-1} ((r / k)) * ((h * r / k))`.
- Basic symmetries and values: `s(-h, k) = -s(h, k)`, congruence invariance modulo `k`,
  homogeneity `s(g * h, g * k) = s(h, k)`, modular inverse symmetry `s(h', k) = s(h, k)`
  when `h * h' ≡ 1 [ZMOD k]`, vanishing for `k ≤ 2`, the explicit formula
  `s(1, k) = (k - 1) * (k - 2) / (12 * k)`, and the denominator integrality `6 * k * s(h, k) ∈ ℤ`
  (and hence `12 * k * s(h, k) ∈ ℤ`).
- Complete proof of Dedekind's reciprocity law: for coprime `h, k ≥ 1`,
  `12 * h * k * (s(h, k) + s(k, h)) = h ^ 2 + k ^ 2 + 1 - 3 * h * k`.
-/

noncomputable section

open Finset

namespace AnalyticNumberTheory.ModularAndPartitions

section SumHelpers

private lemma sum_range_cast_id (k : ℕ) :
    ∑ r ∈ Finset.range k, (r : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma sum_range_cast_sq (k : ℕ) :
    ∑ r ∈ Finset.range k, (r : ℝ) ^ 2 =
      (k : ℝ) * ((k : ℝ) - 1) * (2 * (k : ℝ) - 1) / 6 := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma sum_Icc_cast_id (k : ℕ) :
    ∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h0 : Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
    ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hid := sum_range_cast_id k
  rw [h0, Finset.sum_insert (by simp), Nat.cast_zero, zero_add] at hid
  exact hid

private lemma sum_Icc_cast_sq (k : ℕ) :
    ∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2 =
      (k : ℝ) * ((k : ℝ) - 1) * (2 * (k : ℝ) - 1) / 6 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h0 : Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
    ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hsq := sum_range_cast_sq k
  rw [h0, Finset.sum_insert (by simp), Nat.cast_zero, sq, mul_zero, zero_add] at hsq
  exact hsq

end SumHelpers

section SawtoothEta

/-- The normalized sawtooth function `((x))`, equal to `0` at integers and `Int.fract x - 1 / 2`
otherwise. -/
def sawtoothEta (x : ℝ) : ℝ :=
  if x = (⌊x⌋ : ℝ) then 0 else Int.fract x - 1 / 2

/-- Characterization of `sawtoothEta` in terms of `Int.fract x = 0`. -/
theorem sawtoothEta_eq_ite_fract (x : ℝ) :
    sawtoothEta x = if Int.fract x = 0 then 0 else Int.fract x - 1 / 2 := by
  have hiff : x = (⌊x⌋ : ℝ) ↔ Int.fract x = 0 := by
    rw [Int.fract, sub_eq_zero]
  simp only [sawtoothEta, hiff]

/-- `sawtoothEta` vanishes at every integer. -/
@[simp]
theorem sawtoothEta_intCast (n : ℤ) : sawtoothEta (n : ℝ) = 0 := by
  simp [sawtoothEta_eq_ite_fract]

/-- `sawtoothEta` vanishes at every natural number. -/
@[simp]
theorem sawtoothEta_natCast (n : ℕ) : sawtoothEta (n : ℝ) = 0 := by
  simpa using sawtoothEta_intCast (n : ℤ)

/-- `sawtoothEta 0 = 0`. -/
@[simp]
theorem sawtoothEta_zero : sawtoothEta 0 = 0 := by
  simpa using sawtoothEta_natCast 0

/-- `sawtoothEta 1 = 0`. -/
@[simp]
theorem sawtoothEta_one : sawtoothEta 1 = 0 := by
  simpa using sawtoothEta_natCast 1

/-- `sawtoothEta (1 / 2) = 0`. -/
@[simp]
theorem sawtoothEta_half : sawtoothEta (1 / 2 : ℝ) = 0 := by
  have hfract : Int.fract (1 / 2 : ℝ) = 1 / 2 :=
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  rw [sawtoothEta_eq_ite_fract, hfract]
  split_ifs <;> ring

/-- Formula for `sawtoothEta` away from the integers. -/
theorem sawtoothEta_of_fract_ne_zero {x : ℝ} (hx : Int.fract x ≠ 0) :
    sawtoothEta x = Int.fract x - 1 / 2 := by
  simp only [sawtoothEta_eq_ite_fract, hx, ↓reduceIte]

/-- Formula for `sawtoothEta` on the open unit interval `(0, 1)`. -/
theorem sawtoothEta_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    sawtoothEta x = x - 1 / 2 := by
  have hfract : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0.le, hx1⟩
  rw [sawtoothEta_of_fract_ne_zero (by rw [hfract]; exact hx0.ne'), hfract]

/-- `sawtoothEta` is `1`-periodic on `ℝ`. -/
theorem sawtoothEta_periodic : Function.Periodic sawtoothEta 1 := by
  intro x
  simp [sawtoothEta_eq_ite_fract]

/-- Integer shift invariance of `sawtoothEta`. -/
@[simp]
theorem sawtoothEta_add_intCast (x : ℝ) (n : ℤ) : sawtoothEta (x + n) = sawtoothEta x := by
  simp [sawtoothEta_eq_ite_fract]

/-- Natural number shift invariance of `sawtoothEta`. -/
@[simp]
theorem sawtoothEta_add_natCast (x : ℝ) (n : ℕ) : sawtoothEta (x + n) = sawtoothEta x := by
  simp [sawtoothEta_eq_ite_fract]

/-- Subtraction of an integer leaves `sawtoothEta` unchanged. -/
@[simp]
theorem sawtoothEta_sub_intCast (x : ℝ) (n : ℤ) : sawtoothEta (x - n) = sawtoothEta x := by
  simp [sawtoothEta_eq_ite_fract]

/-- Subtraction of a natural number leaves `sawtoothEta` unchanged. -/
@[simp]
theorem sawtoothEta_sub_natCast (x : ℝ) (n : ℕ) : sawtoothEta (x - n) = sawtoothEta x := by
  simp [sawtoothEta_eq_ite_fract]

/-- `sawtoothEta` is an odd function: `((-x)) = -((x))`. -/
theorem sawtoothEta_neg (x : ℝ) : sawtoothEta (-x) = -sawtoothEta x := by
  by_cases hx : Int.fract x = 0
  · have hnx : Int.fract (-x) = 0 := Int.fract_neg_eq_zero.mpr hx
    simp [sawtoothEta_eq_ite_fract, hx, hnx]
  · have hnx : Int.fract (-x) ≠ 0 := mt Int.fract_neg_eq_zero.mp hx
    rw [sawtoothEta_of_fract_ne_zero hx, sawtoothEta_of_fract_ne_zero hnx, Int.fract_neg hx]
    ring

/-- Strict bound `|sawtoothEta x| < 1 / 2` for all `x : ℝ`. -/
theorem abs_sawtoothEta_lt (x : ℝ) : |sawtoothEta x| < 1 / 2 := by
  by_cases hx : Int.fract x = 0
  · simp only [sawtoothEta_eq_ite_fract, hx, ↓reduceIte, abs_zero]
    norm_num
  · rw [sawtoothEta_of_fract_ne_zero hx, abs_lt]
    have hpos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
    have hlt : Int.fract x < 1 := Int.fract_lt_one x
    constructor <;> linarith

/-- Non-strict bound `|sawtoothEta x| ≤ 1 / 2` for all `x : ℝ`. -/
theorem abs_sawtoothEta_le (x : ℝ) : |sawtoothEta x| ≤ 1 / 2 :=
  (abs_sawtoothEta_lt x).le

/-- Congruence invariance of `sawtoothEta (a / k)` modulo `k`. -/
theorem sawtoothEta_div_eq_of_modEq {a b : ℤ} {k : ℕ} (h : a ≡ b [ZMOD k]) :
    sawtoothEta ((a : ℝ) / k) = sawtoothEta ((b : ℝ) / k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp h
    have hab : (a : ℝ) / k = (b : ℝ) / k + ((-q : ℤ) : ℝ) := by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hqR : (b : ℝ) - a = (k : ℝ) * q := by exact_mod_cast hq
      field_simp [hk0]
      push_cast
      linarith
    rw [hab, sawtoothEta_add_intCast]

/-- **Raabe's distribution identity** for the sawtooth function: for any `k ≥ 1` and `x : ℝ`,
`∑ r ∈ Finset.range k, sawtoothEta ((x + r) / k) = sawtoothEta x`. -/
theorem sum_range_sawtoothEta_add_div {k : ℕ} (hk : 0 < k) (x : ℝ) :
    ∑ r ∈ Finset.range k, sawtoothEta ((x + r) / k) = sawtoothEta x := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  let f : ℤ → ℕ → ℕ := fun n r => (n + r).natMod k
  have hf_mem : ∀ n r, f n r ∈ Finset.range k := fun n r =>
    Finset.mem_range.mpr (@Int.natMod_lt (n + r) k (by positivity))
  have hf_inj : ∀ n, Set.InjOn (f n) (Finset.range k) := by
    intro n r₁ hr₁ r₂ hr₂ hfeq
    have h1 : (n + r₁) % k = (n + r₂) % k := by
      have h' := congrArg (Nat.cast : ℕ → ℤ) hfeq
      dsimp [f] at h'
      rwa [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)),
           Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))] at h'
    have hmod : (r₁ : ℤ) ≡ r₂ [ZMOD k] := by
      have := Int.ModEq.add_left (-n) (show (n + r₁ : ℤ) ≡ n + r₂ [ZMOD k] from h1)
      simpa [add_assoc] using this
    have hr₁' : (r₁ : ℤ) % k = r₁ :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hr₁)
    have hr₂' : (r₂ : ℤ) % k = r₂ :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hr₂)
    have : (r₁ : ℤ) = r₂ := by rw [← hr₁', ← hr₂']; exact hmod
    exact Int.ofNat.inj this
  have hf_surj : ∀ (n : ℤ) (j : ℕ), j ∈ Finset.range k → ∃ r ∈ Finset.range k, f n r = j := by
    intro n j hj
    have hj' : j < k := Finset.mem_range.mp hj
    refine ⟨((j : ℤ) - n).natMod k,
      Finset.mem_range.mpr (@Int.natMod_lt ((j : ℤ) - n) k (by positivity)), ?_⟩
    dsimp [f]
    have hmod : (n + (((j : ℤ) - n).natMod k : ℤ)) % k = (j : ℤ) := by
      have h1 : (((j : ℤ) - n).natMod k : ℤ) = (j - n) % k := by
        rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
      rw [h1, Int.add_emod, Int.emod_emod, ← Int.add_emod, add_sub_cancel,
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj')]
    rw [Int.natMod, hmod, Int.toNat_natCast]
  by_cases hx : Int.fract x = 0
  · obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.mp hx
    rw [← hn, sawtoothEta_intCast]
    have hterm : ∀ r ∈ Finset.range k,
        sawtoothEta (((n : ℝ) + r) / k) = sawtoothEta (((f n r : ℕ) : ℝ) / k) := by
      intro r _
      have hmodEq : n + (r : ℤ) ≡ (f n r : ℤ) [ZMOD k] := by
        dsimp [f]
        rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
        exact (Int.mod_modEq (n + r) k).symm
      have hs := sawtoothEta_div_eq_of_modEq hmodEq
      simpa [Int.cast_add, Int.cast_natCast] using hs
    rw [Finset.sum_congr rfl hterm]
    have hbij :
        ∑ r ∈ Finset.range k, sawtoothEta (((f n r : ℕ) : ℝ) / k) =
          ∑ j ∈ Finset.range k, sawtoothEta ((j : ℝ) / k) :=
      Finset.sum_bij (fun r _ => f n r) (fun r _ => hf_mem n r) (hf_inj n)
        (fun j hj => let ⟨r, hr, hfr⟩ := hf_surj n j hj; ⟨r, hr, hfr⟩) (fun _ _ => rfl)
    rw [hbij, Finset.sum_range_eq_add_Ico _ hk, Nat.cast_zero, zero_div, sawtoothEta_zero,
        zero_add]
    have hIco : ∀ j ∈ Finset.Ico 1 k, sawtoothEta ((j : ℝ) / k) = (j : ℝ) / k - 1 / 2 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      apply sawtoothEta_of_Ioo
      · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
        positivity
      · have hjk : (j : ℝ) < k := by exact_mod_cast hj.2
        exact (div_lt_one (by positivity)).mpr hjk
    rw [Finset.sum_congr rfl hIco, Finset.sum_sub_distrib, ← Finset.sum_div]
    have hIco_sum : ∑ j ∈ Finset.Ico 1 k, (j : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
      have h0 : ∑ j ∈ Finset.range k, (j : ℝ) = (0 : ℝ) + ∑ j ∈ Finset.Ico 1 k, (j : ℝ) := by
        rw [Finset.sum_range_eq_add_Ico _ hk, Nat.cast_zero]
      linarith [sum_range_cast_id k]
    rw [hIco_sum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk]
    push_cast
    field_simp [hkR]
    ring
  · set n : ℤ := ⌊x⌋
    set y : ℝ := Int.fract x
    have hy0 : 0 < y := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
    have hy1 : y < 1 := Int.fract_lt_one x
    have hxy : x = (n : ℝ) + y := (Int.floor_add_fract x).symm
    have hterm : ∀ r ∈ Finset.range k,
        sawtoothEta ((x + r) / k) = (((f n r : ℕ) : ℝ) / k + y / k - 1 / 2) := by
      intro r _
      set j : ℕ := f n r
      have hj_lt : j < k := Finset.mem_range.mp (hf_mem n r)
      set q : ℤ := (n + r) / k
      have hdiv : (n : ℤ) + r = k * q + j := by
        have hjz : (j : ℤ) = (n + r) % k := by
          dsimp [j, f]
          rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
        rw [hjz]
        exact (Int.mul_ediv_add_emod (n + r) k).symm
      have hxrk : (x + r) / k = (q : ℝ) + ((j : ℝ) + y) / k := by
        have hdivR : (n : ℝ) + r = (k : ℝ) * q + j := by exact_mod_cast hdiv
        rw [hxy]
        field_simp [hkR]
        linarith
      have hfrac_pos : 0 < ((j : ℝ) + y) / k := by positivity
      have hfrac_lt : ((j : ℝ) + y) / k < 1 := by
        have hj1 : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj_lt
        rw [div_lt_one (by positivity)]
        linarith
      rw [hxrk, add_comm (q : ℝ), sawtoothEta_add_intCast, sawtoothEta_of_Ioo hfrac_pos hfrac_lt]
      ring
    rw [Finset.sum_congr rfl hterm]
    have hbij :
        ∑ r ∈ Finset.range k, (((f n r : ℕ) : ℝ) / k + y / k - 1 / 2) =
          ∑ j ∈ Finset.range k, ((j : ℝ) / k + y / k - 1 / 2) :=
      Finset.sum_bij (fun r _ => f n r) (fun r _ => hf_mem n r) (hf_inj n)
        (fun j hj => let ⟨r, hr, hfr⟩ := hf_surj n j hj; ⟨r, hr, hfr⟩) (fun _ _ => rfl)
    rw [hbij, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
        sum_range_cast_id k, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, sawtoothEta_of_fract_ne_zero hx]
    field_simp [hkR]
    ring

/-- The sum of `sawtoothEta ((h * r) / k)` over `r ∈ Icc 1 (k - 1)` is zero for any `h : ℤ` and `k : ℕ`. -/
theorem sum_Icc_sawtoothEta_mul_div (h : ℤ) (k : ℕ) :
    ∑ r ∈ Finset.Icc 1 (k - 1), sawtoothEta ((h : ℝ) * r / k) = 0 := by
  set S : ℝ := ∑ r ∈ Finset.Icc 1 (k - 1), sawtoothEta ((h : ℝ) * r / k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [S]
  have hrev : S = ∑ r ∈ Finset.Icc 1 (k - 1), sawtoothEta ((h : ℝ) * ((k - r : ℕ) : ℝ) / k) := by
    refine Finset.sum_bij (fun r _ => k - r) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_Icc] at hr ⊢
      omega
    · intro r₁ hr₁ r₂ hr₂ heq
      rw [Finset.mem_Icc] at hr₁ hr₂
      omega
    · intro s hs
      rw [Finset.mem_Icc] at hs
      refine ⟨k - s, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro r hr
      rw [Finset.mem_Icc] at hr
      have : k - (k - r) = r := by omega
      rw [this]
  have hneg : ∀ r ∈ Finset.Icc 1 (k - 1),
      sawtoothEta ((h : ℝ) * ((k - r : ℕ) : ℝ) / k) = -sawtoothEta ((h : ℝ) * r / k) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hrk : r ≤ k := by omega
    rw [Nat.cast_sub hrk]
    have hkR : (k : ℝ) ≠ 0 := by positivity
    have heq : (h : ℝ) * ((k : ℝ) - r) / k = -((h : ℝ) * r / k) + (h : ℤ) := by
      field_simp [hkR]
      ring
    rw [heq, sawtoothEta_add_intCast, sawtoothEta_neg]
  have hS : S = -S := by
    calc S = ∑ r ∈ Finset.Icc 1 (k - 1), sawtoothEta ((h : ℝ) * ((k - r : ℕ) : ℝ) / k) := hrev
      _ = ∑ r ∈ Finset.Icc 1 (k - 1), -sawtoothEta ((h : ℝ) * r / k) :=
        Finset.sum_congr rfl hneg
      _ = -S := by simp [S, Finset.sum_neg_distrib]
  linarith

end SawtoothEta

section DedekindSum

/-- The Dedekind sum `s(h, k) = ∑_{r=1}^{k-1} ((r / k)) * ((h * r / k))`. -/
def dedekindSum (h : ℤ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (k - 1), sawtoothEta ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k)

/-- Expressing `dedekindSum h k` as a sum over `Finset.range k`. -/
theorem dedekindSum_eq_sum_range (h : ℤ) (k : ℕ) :
    dedekindSum h k =
      ∑ r ∈ Finset.range k, sawtoothEta ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [dedekindSum]
  · unfold dedekindSum
    have hIco : Finset.Ico 1 k = Finset.Icc 1 (k - 1) := by
      ext r; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.sum_range_eq_add_Ico _ hk, Nat.cast_zero, zero_div, sawtoothEta_zero, zero_mul,
        zero_add, hIco]

/-- Simplification `dedekindSum h k = ∑_{r=1}^{k-1} (r / k) * ((h * r / k))` for `k ≥ 1`. -/
theorem dedekindSum_eq_sum_div_mul (h : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    dedekindSum h k = ∑ r ∈ Finset.Icc 1 (k - 1), ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k) := by
  unfold dedekindSum
  have hterm : ∀ r ∈ Finset.Icc 1 (k - 1),
      sawtoothEta ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k) =
        ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k) - (1 / 2 : ℝ) * sawtoothEta ((h : ℝ) * r / k) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr0 : 0 < (r : ℝ) / k := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr.1
      have : (0 : ℝ) < k := by positivity
      positivity
    have hr1 : (r : ℝ) / k < 1 := by
      have hrk : r < k := by omega
      have : (r : ℝ) < k := by exact_mod_cast hrk
      exact (div_lt_one (by positivity)).mpr this
    rw [sawtoothEta_of_Ioo hr0 hr1]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_Icc_sawtoothEta_mul_div h k, mul_zero, sub_zero]

/-- `dedekindSum 0 k = 0`. -/
@[simp]
theorem dedekindSum_zero_left (k : ℕ) : dedekindSum 0 k = 0 := by
  simp [dedekindSum]

/-- `dedekindSum h 0 = 0`. -/
@[simp]
theorem dedekindSum_zero_right (h : ℤ) : dedekindSum h 0 = 0 := by
  simp [dedekindSum]

/-- `dedekindSum h 1 = 0`. -/
@[simp]
theorem dedekindSum_one_right (h : ℤ) : dedekindSum h 1 = 0 := by
  simp [dedekindSum]

/-- `dedekindSum h 2 = 0`. -/
@[simp]
theorem dedekindSum_two_right (h : ℤ) : dedekindSum h 2 = 0 := by
  simp only [dedekindSum, Nat.reduceSub, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one,
    Nat.cast_ofNat]
  norm_num

/-- `dedekindSum h k = 0` whenever `k ≤ 2`. -/
theorem dedekindSum_eq_zero_of_le_two (h : ℤ) {k : ℕ} (hk : k ≤ 2) : dedekindSum h k = 0 := by
  interval_cases k <;> simp

/-- Oddness in the first argument: `s(-h, k) = -s(h, k)`. -/
theorem dedekindSum_neg (h : ℤ) (k : ℕ) : dedekindSum (-h) k = -dedekindSum h k := by
  simp only [dedekindSum, Int.cast_neg, neg_mul, neg_div, sawtoothEta_neg, mul_neg,
    Finset.sum_neg_distrib]

/-- Congruence invariance in the first argument: `h ≡ h' [ZMOD k] → s(h, k) = s(h', k)`. -/
theorem dedekindSum_congr {h h' : ℤ} {k : ℕ} (hmod : h ≡ h' [ZMOD k]) :
    dedekindSum h k = dedekindSum h' k := by
  unfold dedekindSum
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have hmul : h * (r : ℤ) ≡ h' * r [ZMOD k] := hmod.mul_right (r : ℤ)
  simpa [Int.cast_mul, Int.cast_natCast] using sawtoothEta_div_eq_of_modEq hmul

/-- Periodicity in the first argument: `s(h + k, k) = s(h, k)`. -/
theorem dedekindSum_add_nat (h : ℤ) (k : ℕ) : dedekindSum (h + k) k = dedekindSum h k := by
  apply dedekindSum_congr
  rw [Int.modEq_iff_dvd]
  exact ⟨-1, by ring⟩

/-- General shift invariance in the first argument: `s(h + m * k, k) = s(h, k)`. -/
theorem dedekindSum_add_int (h m : ℤ) (k : ℕ) : dedekindSum (h + m * k) k = dedekindSum h k := by
  apply dedekindSum_congr
  rw [Int.modEq_iff_dvd]
  exact ⟨-m, by ring⟩

/-- Scaling invariance of Dedekind sums: `s(g * h, g * k) = s(h, k)` for `g ≥ 1`. -/
theorem dedekindSum_mul_scale {g : ℕ} (hg : 0 < g) (h : ℤ) (k : ℕ) :
    dedekindSum ((g : ℤ) * h) (g * k) = dedekindSum h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [dedekindSum_eq_sum_range, dedekindSum_eq_sum_range]
  have hprod : Finset.range (g * k) =
      (Finset.range k ×ˢ Finset.range g).image (fun p => p.1 + k * p.2) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_image, Finset.mem_product]
    constructor
    · intro hn
      refine ⟨⟨n % k, n / k⟩, ⟨Nat.mod_lt n hk, ?_⟩, ?_⟩
      · exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
      · rw [add_comm, Nat.div_add_mod]
    · rintro ⟨⟨r₁, q⟩, ⟨hr₁, hq⟩, rfl⟩
      have h1 : r₁ + k * q < k + k * q := Nat.add_lt_add_right hr₁ _
      have h2 : k * (q + 1) ≤ k * g := Nat.mul_le_mul_left k hq
      linarith
  have hinj : ∀ a ∈ Finset.range k ×ˢ Finset.range g,
      ∀ b ∈ Finset.range k ×ˢ Finset.range g,
        a.1 + k * a.2 = b.1 + k * b.2 → a = b := by
    intro ⟨r₁, q₁⟩ h₁ ⟨r₂, q₂⟩ h₂ heq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h₁ h₂
    have hmod : (r₁ + k * q₁) % k = (r₂ + k * q₂) % k := congrArg (· % k) heq
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₁.1,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₂.1] at hmod
    have hq : k * q₁ = k * q₂ := by linarith
    have hq' : q₁ = q₂ := Nat.eq_of_mul_eq_mul_left hk hq
    exact Prod.ext hmod hq'
  rw [hprod, Finset.sum_image hinj, Finset.sum_product]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hgR : (g : ℝ) ≠ 0 := by positivity
  have hterm : ∀ q ∈ Finset.range g,
      sawtoothEta (((r₁ + k * q : ℕ) : ℝ) / ((g * k : ℕ) : ℝ)) *
        sawtoothEta (((g : ℤ) * h : ℤ) * ((r₁ + k * q : ℕ) : ℝ) / ((g * k : ℕ) : ℝ)) =
      sawtoothEta ((((r₁ : ℝ) / k) + q) / g) * sawtoothEta ((h : ℝ) * r₁ / k) := by
    intro q _
    have h1 : (((r₁ + k * q : ℕ) : ℝ) / ((g * k : ℕ) : ℝ)) = (((r₁ : ℝ) / k) + q) / g := by
      push_cast
      field_simp [hkR, hgR]
    have h2 : (((g : ℤ) * h : ℤ) * ((r₁ + k * q : ℕ) : ℝ) / ((g * k : ℕ) : ℝ)) =
        (h : ℝ) * r₁ / k + ((h * q : ℤ) : ℝ) := by
      push_cast
      field_simp [hkR, hgR]
    rw [h1, h2, sawtoothEta_add_intCast]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_range_sawtoothEta_add_div hg]

/-- Modular inverse symmetry: if `h * h' ≡ 1 [ZMOD k]`, then `s(h', k) = s(h, k)`. -/
theorem dedekindSum_inv {h h' : ℤ} {k : ℕ} (hinv : h * h' ≡ 1 [ZMOD k]) :
    dedekindSum h' k = dedekindSum h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [dedekindSum_eq_sum_range, dedekindSum_eq_sum_range]
  let f : ℕ → ℕ := fun r => (h' * r).natMod k
  have hf_mem : ∀ r ∈ Finset.range k, f r ∈ Finset.range k := fun r _ =>
    Finset.mem_range.mpr (@Int.natMod_lt (h' * r) k (by positivity))
  have hf_inj : Set.InjOn f (Finset.range k) := by
    intro r₁ hr₁ r₂ hr₂ heq
    have hmod1 : (h' * r₁ : ℤ) ≡ h' * r₂ [ZMOD k] := by
      have h1 : (f r₁ : ℤ) = (h' * r₁) % k := by
        dsimp [f]; rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
      have h2 : (f r₂ : ℤ) = (h' * r₂) % k := by
        dsimp [f]; rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
      have h3 := congrArg (Nat.cast : ℕ → ℤ) heq
      rw [h1, h2] at h3
      exact h3
    have hmul : h * (h' * r₁) ≡ h * (h' * r₂) [ZMOD k] := hmod1.mul_left h
    have hL : h * (h' * r₁) ≡ r₁ [ZMOD k] := by
      rw [← mul_assoc]
      simpa using hinv.mul_right (r₁ : ℤ)
    have hR : h * (h' * r₂) ≡ r₂ [ZMOD k] := by
      rw [← mul_assoc]
      simpa using hinv.mul_right (r₂ : ℤ)
    have hr12 : (r₁ : ℤ) ≡ r₂ [ZMOD k] := hL.symm.trans (hmul.trans hR)
    have hr₁' : (r₁ : ℤ) % k = r₁ :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hr₁)
    have hr₂' : (r₂ : ℤ) % k = r₂ :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hr₂)
    have : (r₁ : ℤ) = r₂ := by rw [← hr₁', ← hr₂']; exact hr12
    exact Int.ofNat.inj this
  have hf_surj : ∀ s ∈ Finset.range k, ∃ r, ∃ (_ : r ∈ Finset.range k), f r = s := by
    intro s hs
    refine ⟨(h * s).natMod k,
      Finset.mem_range.mpr (@Int.natMod_lt (h * s) k (by positivity)), ?_⟩
    dsimp [f]
    have h1 : (((h * s).natMod k : ℕ) : ℤ) = (h * s) % k := by
      rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
    have hmod : h' * ((h * s).natMod k : ℤ) ≡ s [ZMOD k] := by
      have hstep1 : h' * ((h * s).natMod k : ℤ) ≡ h' * (h * s) [ZMOD k] := by
        rw [h1]
        exact (Int.mod_modEq (h * s) k).mul_left h'
      have hstep2 : h' * (h * s) ≡ s [ZMOD k] := by
        rw [← mul_assoc, mul_comm h' h]
        simpa using hinv.mul_right (s : ℤ)
      exact hstep1.trans hstep2
    have hs' : (s : ℤ) % k = s :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hs)
    have hfin : (h' * ((h * s).natMod k : ℤ)) % k = s :=
      Eq.trans hmod hs'
    rw [Int.natMod, hfin, Int.toNat_natCast]
  refine Finset.sum_bij (fun r _ => f r) hf_mem hf_inj hf_surj ?_
  intro r _
  have h1 : (f r : ℤ) ≡ h' * r [ZMOD k] := by
    dsimp [f]
    rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
    exact Int.mod_modEq (h' * r) k
  have h2 : h * (f r : ℤ) ≡ r [ZMOD k] := by
    have := h1.mul_left h
    rw [← mul_assoc] at this
    have h3 : (h * h') * r ≡ 1 * r [ZMOD k] := hinv.mul_right (r : ℤ)
    simpa using this.trans h3
  have hs1 := sawtoothEta_div_eq_of_modEq h1.symm
  have hs2 := sawtoothEta_div_eq_of_modEq h2
  have hc1 : ((h' * (r : ℤ) : ℤ) : ℝ) / k = (h' : ℝ) * r / k := by push_cast; ring
  have hc2 : ((h * (f r : ℤ) : ℤ) : ℝ) / k = (h : ℝ) * (f r : ℕ) / k := by push_cast; ring
  rw [hc1] at hs1
  rw [hc2] at hs2
  simp only [Int.cast_natCast] at hs1 hs2
  rw [hs1, hs2, mul_comm]

/-- Negative modular inverse symmetry: if `h * h' ≡ -1 [ZMOD k]`, then `s(h', k) = -s(h, k)`. -/
theorem dedekindSum_neg_inv {h h' : ℤ} {k : ℕ} (hinv : h * h' ≡ -1 [ZMOD k]) :
    dedekindSum h' k = -dedekindSum h k := by
  have hinv' : (-h) * h' ≡ 1 [ZMOD k] := by
    have := hinv.neg
    simpa using this
  rw [dedekindSum_inv hinv', dedekindSum_neg]

/-- If `h ^ 2 ≡ -1 [ZMOD k]`, then `dedekindSum h k = 0`. -/
theorem dedekindSum_eq_zero_of_sq_modEq_neg_one {h : ℤ} {k : ℕ} (hsq : h ^ 2 ≡ -1 [ZMOD k]) :
    dedekindSum h k = 0 := by
  have hinv : h * h ≡ -1 [ZMOD k] := by simpa [sq] using hsq
  have heq : dedekindSum h k = -dedekindSum h k := dedekindSum_neg_inv hinv
  linarith

/-- Explicit formula `s(1, k) = (k - 1) * (k - 2) / (12 * k)`. -/
theorem dedekindSum_one_left (k : ℕ) :
    dedekindSum 1 k = ((k : ℝ) - 1) * ((k : ℝ) - 2) / (12 * (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [dedekindSum_eq_sum_div_mul 1 hk]
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hterm : ∀ r ∈ Finset.Icc 1 (k - 1),
      ((r : ℝ) / k) * sawtoothEta (((1 : ℤ) : ℝ) * r / k) =
        (r : ℝ) ^ 2 / (k : ℝ) ^ 2 - (r : ℝ) / (2 * (k : ℝ)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr0 : 0 < (r : ℝ) / k := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr.1
      positivity
    have hr1 : (r : ℝ) / k < 1 := by
      have hrk : r < k := by omega
      have : (r : ℝ) < k := by exact_mod_cast hrk
      exact (div_lt_one (by positivity)).mpr this
    have h1r : ((1 : ℤ) : ℝ) * r / k = (r : ℝ) / k := by ring
    rw [h1r, sawtoothEta_of_Ioo hr0 hr1]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      sum_Icc_cast_id k, sum_Icc_cast_sq k]
  field_simp [hkR]
  ring

/-- Explicit formula for `s(2, k)` when `k` is odd: `s(2, k) = (k - 1) * (k - 5) / (24 * k)`. -/
theorem dedekindSum_two_left {k : ℕ} (hk : Odd k) :
    dedekindSum 2 k = ((k : ℝ) - 1) * ((k : ℝ) - 5) / (24 * (k : ℝ)) := by
  have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by rintro rfl; simp at hk))
  rcases eq_or_lt_of_le hk_pos with hk1 | hk_gt1
  · rw [← hk1]; norm_num
  have hk_ge3 : 3 ≤ k := by
    have hmod : k % 2 = 1 := Nat.odd_iff.mp hk
    omega
  rw [dedekindSum_eq_sum_div_mul 2 hk_pos]
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hhalf : k = 2 * (k / 2) + 1 := by
    have hmod : k % 2 = 1 := Nat.odd_iff.mp hk
    have hdiv : 2 * (k / 2) + k % 2 = k := Nat.div_add_mod k 2
    omega
  have hterm : ∀ r ∈ Finset.Icc 1 (k - 1),
      ((r : ℝ) / k) * sawtoothEta (((2 : ℤ) : ℝ) * r / k) =
        (2 * (r : ℝ) ^ 2 / (k : ℝ) ^ 2 - (r : ℝ) / (2 * (k : ℝ))) -
          (if k / 2 < r then (r : ℝ) / k else 0) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have h2r : ((2 : ℤ) : ℝ) * r / k = 2 * (r : ℝ) / k := by push_cast; ring
    rw [h2r]
    by_cases hlt : r ≤ k / 2
    · have h0 : 0 < 2 * (r : ℝ) / k := by
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr.1
        positivity
      have h1 : 2 * (r : ℝ) / k < 1 := by
        have : 2 * r < k := by omega
        have : 2 * (r : ℝ) < k := by exact_mod_cast this
        rw [div_lt_one (by positivity)]; exact this
      have hnot : ¬ k / 2 < r := by omega
      simp only [sawtoothEta_of_Ioo h0 h1, hnot, ↓reduceIte]
      ring
    · have hgt : k / 2 < r := by omega
      have h0 : 0 < 2 * (r : ℝ) / k - ((1 : ℤ) : ℝ) := by
        have : k < 2 * r := by omega
        have : (k : ℝ) < 2 * (r : ℝ) := by exact_mod_cast this
        rw [sub_pos, Int.cast_one, lt_div_iff₀ (by positivity)]
        linarith
      have h1 : 2 * (r : ℝ) / k - ((1 : ℤ) : ℝ) < 1 := by
        have : r < k := by omega
        have : (r : ℝ) < k := by exact_mod_cast this
        rw [Int.cast_one, sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
        linarith
      have hshift : sawtoothEta (2 * (r : ℝ) / k) = sawtoothEta (2 * (r : ℝ) / k - ((1 : ℤ) : ℝ)) := by
        rw [sawtoothEta_sub_intCast]
      rw [hshift, sawtoothEta_of_Ioo h0 h1, Int.cast_one]
      simp only [hgt, ↓reduceIte]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum]
  have htail : ∑ r ∈ Finset.Icc 1 (k - 1), (if k / 2 < r then (r : ℝ) / k else 0) =
      ((k : ℝ) - 1) * (3 * (k : ℝ) - 1) / (8 * (k : ℝ)) := by
    have hsplit : Finset.Icc 1 (k - 1) =
        Finset.Icc 1 (k / 2) ∪ Finset.Icc (k / 2 + 1) (k - 1) := by
      ext r; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc 1 (k / 2)) (Finset.Icc (k / 2 + 1) (k - 1)) := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      rw [Finset.mem_Icc] at hr1 hr2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hleft : ∑ r ∈ Finset.Icc 1 (k / 2), (if k / 2 < r then (r : ℝ) / k else 0) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.mem_Icc] at hr
      have hnot : ¬ k / 2 < r := by omega
      simp only [hnot, ↓reduceIte]
    have hright : ∑ r ∈ Finset.Icc (k / 2 + 1) (k - 1), (if k / 2 < r then (r : ℝ) / k else 0) =
        ∑ r ∈ Finset.Icc (k / 2 + 1) (k - 1), (r : ℝ) / k := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_Icc] at hr
      have hlt : k / 2 < r := by omega
      simp only [hlt, ↓reduceIte]
    rw [hleft, zero_add, hright, ← Finset.sum_div]
    have hsum_lo : ∑ r ∈ Finset.range (k / 2 + 1), (r : ℝ) =
        ((k / 2 + 1 : ℕ) : ℝ) * ((k / 2 : ℕ) : ℝ) / 2 := by
      rw [sum_range_cast_id (k / 2 + 1)]
      push_cast
      ring
    have hsum_hi : ∑ r ∈ Finset.Icc (k / 2 + 1) (k - 1), (r : ℝ) =
        ∑ r ∈ Finset.range k, (r : ℝ) - ∑ r ∈ Finset.range (k / 2 + 1), (r : ℝ) := by
      have hunion : Finset.range k = Finset.range (k / 2 + 1) ∪ Finset.Icc (k / 2 + 1) (k - 1) := by
        ext r; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj' : Disjoint (Finset.range (k / 2 + 1)) (Finset.Icc (k / 2 + 1) (k - 1)) := by
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        rw [Finset.mem_range] at hr1
        rw [Finset.mem_Icc] at hr2
        omega
      rw [hunion, Finset.sum_union hdisj']
      ring
    have hm_cast : ((k / 2 : ℕ) : ℝ) = ((k : ℝ) - 1) / 2 := by
      have : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hhalf
      linarith
    rw [hsum_hi, sum_range_cast_id k, hsum_lo]
    push_cast
    rw [hm_cast]
    field_simp [hkR]
    ring
  rw [sum_Icc_cast_id k, sum_Icc_cast_sq k, htail]
  field_simp [hkR]
  ring

/-- Denominator bound: `6 * k * dedekindSum h k` is always an integer. -/
theorem six_mul_dedekindSum_int (h : ℤ) (k : ℕ) :
    ∃ m : ℤ, (6 * (k : ℝ)) * dedekindSum h k = m := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, by simp⟩
  rw [dedekindSum_eq_sum_div_mul h hk]
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hmul : (6 * (k : ℝ)) * ∑ r ∈ Finset.Icc 1 (k - 1), ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k) =
      ∑ r ∈ Finset.Icc 1 (k - 1), 6 * (r : ℝ) * sawtoothEta ((h : ℝ) * r / k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp [hkR]
  rw [hmul]
  have hterm : ∀ r ∈ Finset.Icc 1 (k - 1),
      6 * (r : ℝ) * sawtoothEta ((h : ℝ) * r / k) =
        6 * (h : ℝ) * (r : ℝ) ^ 2 / k - 6 * (r : ℝ) * (⌊(h : ℝ) * r / k⌋ : ℝ) - 3 * (r : ℝ) +
          (if (h : ℝ) * r / k = (⌊(h : ℝ) * r / k⌋ : ℝ) then 3 * (r : ℝ) else 0) := by
    intro r _
    unfold sawtoothEta
    split_ifs with heq
    · have hfl : (⌊(h : ℝ) * r / k⌋ : ℝ) = (h : ℝ) * r / k := heq.symm
      rw [hfl]
      ring
    · rw [Int.fract]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
  have hid_int : ∃ A : ℤ, ∑ r ∈ Finset.Icc 1 (k - 1), (3 : ℝ) * r = (A : ℝ) := by
    have hsum : ∑ r ∈ Finset.range k, r = k * (k - 1) / 2 := by
      simpa using Finset.sum_range_id k
    have hsumIcc : ∑ r ∈ Finset.Icc 1 (k - 1), r = k * (k - 1) / 2 := by
      have h0 : Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
        ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [h0, Finset.sum_insert (by simp), zero_add] at hsum
      exact hsum
    refine ⟨3 * ((k * (k - 1) / 2 : ℕ) : ℤ), ?_⟩
    rw [← Finset.mul_sum, ← Nat.cast_sum, hsumIcc, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hsq_int : ∃ B : ℤ, ∑ r ∈ Finset.Icc 1 (k - 1), 6 * (h : ℝ) * (r : ℝ) ^ 2 / k = (B : ℝ) := by
    refine ⟨h * ((k : ℤ) - 1) * (2 * (k : ℤ) - 1), ?_⟩
    have hfactor : ∑ r ∈ Finset.Icc 1 (k - 1), 6 * (h : ℝ) * (r : ℝ) ^ 2 / k =
        (6 * (h : ℝ) / k) * ∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [hfactor, sum_Icc_cast_sq k]
    push_cast
    field_simp [hkR]
  have hfl_int : ∃ C : ℤ,
      ∑ r ∈ Finset.Icc 1 (k - 1), 6 * (r : ℝ) * (⌊(h : ℝ) * r / k⌋ : ℝ) = (C : ℝ) := by
    refine ⟨∑ r ∈ Finset.Icc 1 (k - 1), 6 * (r : ℤ) * ⌊(h : ℝ) * r / k⌋, ?_⟩
    push_cast
    rfl
  have hite_int : ∃ D : ℤ,
      ∑ r ∈ Finset.Icc 1 (k - 1),
        (if (h : ℝ) * r / k = (⌊(h : ℝ) * r / k⌋ : ℝ) then 3 * (r : ℝ) else 0) = (D : ℝ) := by
    refine ⟨∑ r ∈ Finset.Icc 1 (k - 1),
      (if (h : ℝ) * r / k = (⌊(h : ℝ) * r / k⌋ : ℝ) then 3 * (r : ℤ) else 0), ?_⟩
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> simp
  obtain ⟨A, hA⟩ := hid_int
  obtain ⟨B, hB⟩ := hsq_int
  obtain ⟨C, hC⟩ := hfl_int
  obtain ⟨D, hD⟩ := hite_int
  refine ⟨B - C - A + D, ?_⟩
  rw [hA, hB, hC, hD]
  push_cast
  ring

/-- `12 * k * dedekindSum h k` is always an integer. -/
theorem twelve_mul_dedekindSum_int (h : ℤ) (k : ℕ) :
    ∃ m : ℤ, (12 * (k : ℝ)) * dedekindSum h k = m := by
  obtain ⟨m, hm⟩ := six_mul_dedekindSum_int h k
  refine ⟨2 * m, ?_⟩
  have heq : (12 * (k : ℝ)) * dedekindSum h k = 2 * ((6 * (k : ℝ)) * dedekindSum h k) := by ring
  rw [heq, hm]
  push_cast
  ring

end DedekindSum

section ReciprocityLaw

/-- Auxiliary identity for Dedekind's reciprocity law: for coprime `h, k ≥ 1`,
`2 * h * s(h, k) + ∑_{r=1}^{k-1} ⌊hr/k⌋ * (⌊hr/k⌋ + 1) = (1 + h^2) / k^2 * ∑ r^2 - (1 / k) * ∑ r`. -/
private lemma two_mul_dedekindSum_add_floor_prod {h k : ℕ} (_hh : 1 ≤ h) (hk : 1 ≤ k)
    (hcop : Nat.Coprime h k) :
    2 * (h : ℝ) * dedekindSum h k +
        ∑ r ∈ Finset.Icc 1 (k - 1),
          ((h * r / k : ℕ) : ℝ) * (((h * r / k : ℕ) : ℝ) + 1) =
      ((1 + (h : ℝ) ^ 2) / (k : ℝ) ^ 2) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2) -
        (1 / (k : ℝ)) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  let I : ℝ := ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((h : ℝ) * r / k)) ^ 2
  have hnot_int : ∀ r ∈ Finset.Icc 1 (k - 1), ¬ k ∣ h * r := by
    intro r hr hdvd
    rw [Finset.mem_Icc] at hr
    have hdivr : k ∣ r := hcop.symm.dvd_of_dvd_mul_left hdvd
    have hle : k ≤ r := Nat.le_of_dvd hr.1 hdivr
    omega
  have hI_way1 : I =
      (1 / (k : ℝ) ^ 2) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2) -
        (1 / (k : ℝ)) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ)) +
        ((k : ℝ) - 1) / 4 := by
    let f : ℕ → ℕ := fun r => (h * r) % k
    have hf_sub : (Finset.Icc 1 (k - 1)).image f ⊆ Finset.Icc 1 (k - 1) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
      rw [Finset.mem_Icc]
      have hpos : 0 < (h * r) % k := Nat.pos_of_ne_zero fun h0 =>
        hnot_int r hr (Nat.dvd_of_mod_eq_zero h0)
      have hlt : (h * r) % k ≤ k - 1 := by
        have := Nat.mod_lt (h * r) hk
        omega
      exact ⟨hpos, hlt⟩
    have hf_inj : Set.InjOn f (Finset.Icc 1 (k - 1)) := by
      intro r₁ hr₁ r₂ hr₂ heq
      simp only [Finset.mem_coe, Finset.mem_Icc] at hr₁ hr₂
      have hmod : h * r₁ ≡ h * r₂ [MOD k] := heq
      have hmod' : r₁ ≡ r₂ [MOD k] := hmod.cancel_left_of_coprime hcop.symm
      have hr₁' : r₁ % k = r₁ := Nat.mod_eq_of_lt (by omega)
      have hr₂' : r₂ % k = r₂ := Nat.mod_eq_of_lt (by omega)
      change r₁ % k = r₂ % k at hmod'
      rwa [hr₁', hr₂'] at hmod'
    have himg_eq : (Finset.Icc 1 (k - 1)).image f = Finset.Icc 1 (k - 1) :=
      Finset.eq_of_subset_of_card_le hf_sub (by rw [Finset.card_image_of_injOn hf_inj])
    have hperm : I = ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((r : ℝ) / k)) ^ 2 := by
      calc I = ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((f r : ℝ) / k)) ^ 2 := by
            dsimp [I]
            refine Finset.sum_congr rfl fun r _ => ?_
            have hmodEq : ((h : ℤ) * r) ≡ (f r : ℤ) [ZMOD k] := by
              change ((h * r : ℕ) : ℤ) ≡ ((h * r) % k : ℕ) [ZMOD k]
              exact_mod_cast (Nat.mod_modEq (h * r) k).symm
            have hs := sawtoothEta_div_eq_of_modEq hmodEq
            simp only [Int.cast_natCast] at hs
            have hcast' : (((h : ℤ) * r : ℤ) : ℝ) / k = (h : ℝ) * r / k := by push_cast; ring
            rw [← hcast', hs]
        _ = ∑ y ∈ (Finset.Icc 1 (k - 1)).image f, (sawtoothEta ((y : ℝ) / k)) ^ 2 := by
            symm
            exact Finset.sum_image (f := fun y : ℕ => (sawtoothEta ((y : ℝ) / k)) ^ 2)
              fun x hx y hy hxy => hf_inj hx hy hxy
        _ = ∑ y ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((y : ℝ) / k)) ^ 2 := by rw [himg_eq]
    rw [hperm]
    have hterm : ∀ r ∈ Finset.Icc 1 (k - 1),
        (sawtoothEta ((r : ℝ) / k)) ^ 2 =
          (r : ℝ) ^ 2 / (k : ℝ) ^ 2 - (r : ℝ) / (k : ℝ) + 1 / 4 := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hr0 : 0 < (r : ℝ) / k := by
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr.1
        positivity
      have hr1 : (r : ℝ) / k < 1 := by
        have : r < k := by omega
        have : (r : ℝ) < k := by exact_mod_cast this
        exact (div_lt_one (by positivity)).mpr this
      rw [sawtoothEta_of_Ioo hr0 hr1]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_div, ← Finset.sum_div, Finset.sum_const, Nat.card_Icc,
        nsmul_eq_mul, Nat.add_sub_cancel, Nat.cast_sub hk]
    ring
  have hI_way2 : I =
      2 * (h : ℝ) * dedekindSum h k -
        ((h : ℝ) ^ 2 / (k : ℝ) ^ 2) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2) +
        (∑ r ∈ Finset.Icc 1 (k - 1),
          ((h * r / k : ℕ) : ℝ) * (((h * r / k : ℕ) : ℝ) + 1)) +
        ((k : ℝ) - 1) / 4 := by
    have hfl_eq : ∀ r ∈ Finset.Icc 1 (k - 1),
        sawtoothEta ((h : ℝ) * r / k) =
          (h : ℝ) * r / k - ((h * r / k : ℕ) : ℝ) - 1 / 2 := by
      intro r hr
      have hdiv : h * r = k * (h * r / k) + (h * r) % k := (Nat.div_add_mod (h * r) k).symm
      have hmod_pos : 0 < (h * r) % k := Nat.pos_of_ne_zero fun h0 =>
        hnot_int r hr (Nat.dvd_of_mod_eq_zero h0)
      have hmod_lt : (h * r) % k < k := Nat.mod_lt (h * r) hk
      have hsplit : (h : ℝ) * r / k = (((h * r) % k : ℕ) : ℝ) / k + ((h * r / k : ℕ) : ℤ) := by
        have hdivR : (h : ℝ) * r = (k : ℝ) * (h * r / k : ℕ) + ((h * r) % k : ℕ) := by
          exact_mod_cast hdiv
        rw [hdivR, Int.cast_natCast]
        field_simp [hkR]
        ring
      have hfrac0 : 0 < (((h * r) % k : ℕ) : ℝ) / k := by
        have : (1 : ℝ) ≤ ((h * r) % k : ℕ) := by exact_mod_cast hmod_pos
        positivity
      have hfrac1 : (((h * r) % k : ℕ) : ℝ) / k < 1 := by
        have : (((h * r) % k : ℕ) : ℝ) < k := by exact_mod_cast hmod_lt
        exact (div_lt_one (by positivity)).mpr this
      rw [hsplit, sawtoothEta_add_intCast, sawtoothEta_of_Ioo hfrac0 hfrac1, Int.cast_natCast]
      have hdivR : (h : ℝ) * r = (k : ℝ) * (h * r / k : ℕ) + ((h * r) % k : ℕ) := by
        exact_mod_cast hdiv
      have hmodR : (((h * r) % k : ℕ) : ℝ) = (h : ℝ) * r - (k : ℝ) * (h * r / k : ℕ) := by linarith
      rw [hmodR]
      field_simp [hkR]
      ring
    have hterm : ∀ r ∈ Finset.Icc 1 (k - 1),
        (sawtoothEta ((h : ℝ) * r / k)) ^ 2 =
          2 * (h : ℝ) * (((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k)) -
            ((h : ℝ) ^ 2 / (k : ℝ) ^ 2) * (r : ℝ) ^ 2 +
            ((h * r / k : ℕ) : ℝ) * (((h * r / k : ℕ) : ℝ) + 1) + 1 / 4 := by
      intro r hr
      have hse := hfl_eq r hr
      set a : ℝ := (h : ℝ) * r / k
      set q : ℝ := ((h * r / k : ℕ) : ℝ)
      have ha_sq : (a - q - 1 / 2) ^ 2 =
          2 * a * (a - q - 1 / 2) - a ^ 2 + q * (q + 1) + 1 / 4 := by ring
      rw [hse]
      change (a - q - 1 / 2) ^ 2 = _
      rw [ha_sq, ← hse]
      dsimp [a, q]
      ring
    dsimp [I]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, Nat.cast_sub hk]
    have hdsum : ∑ r ∈ Finset.Icc 1 (k - 1), ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k) =
        dedekindSum (h : ℤ) k := by
      rw [dedekindSum_eq_sum_div_mul (h : ℤ) hk]
      simp
    rw [hdsum]
    ring
  have heq : 2 * (h : ℝ) * dedekindSum h k -
        ((h : ℝ) ^ 2 / (k : ℝ) ^ 2) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2) +
        (∑ r ∈ Finset.Icc 1 (k - 1),
          ((h * r / k : ℕ) : ℝ) * (((h * r / k : ℕ) : ℝ) + 1)) +
        ((k : ℝ) - 1) / 4 =
      (1 / (k : ℝ) ^ 2) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2) -
        (1 / (k : ℝ)) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ)) +
        ((k : ℝ) - 1) / 4 := hI_way2.symm.trans hI_way1
  have heq2 : 2 * (h : ℝ) * dedekindSum h k +
      ∑ r ∈ Finset.Icc 1 (k - 1),
        ((h * r / k : ℕ) : ℝ) * (((h * r / k : ℕ) : ℝ) + 1) =
      (1 / (k : ℝ) ^ 2) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2) +
      ((h : ℝ) ^ 2 / (k : ℝ) ^ 2) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ) ^ 2) -
      (1 / (k : ℝ)) * (∑ r ∈ Finset.Icc 1 (k - 1), (r : ℝ)) := by linarith
  rw [heq2]
  ring

/-- Evaluation of the floor-product sum `∑_{r=1}^{k-1} ⌊hr/k⌋ * (⌊hr/k⌋ + 1)` in terms of
`dedekindSum k h`. -/
private lemma sum_floor_mul_succ_eq {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hcop : Nat.Coprime h k) :
    ∑ r ∈ Finset.Icc 1 (k - 1),
        ((h * r / k : ℕ) : ℝ) * (((h * r / k : ℕ) : ℝ) + 1) =
      2 * (h : ℝ) * dedekindSum k h +
        (k : ℝ) * (h : ℝ) * ((h : ℝ) - 1) -
        (h : ℝ) * ((h : ℝ) - 1) / 2 -
        (k : ℝ) * ((h : ℝ) - 1) * (2 * (h : ℝ) - 1) / 3 := by
  have hhR : (h : ℝ) ≠ 0 := by positivity
  have h1 : ∀ n : ℕ, ((n : ℝ) * ((n : ℝ) + 1)) = 2 * ∑ s ∈ Finset.Icc 1 n, (s : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have ih' : 2 * ∑ x ∈ Finset.Icc 1 m, (x : ℝ) = (m : ℝ) * ((m : ℝ) + 1) := ih.symm
      push_cast
      linarith
  have hbound : ∀ r ∈ Finset.Icc 1 (k - 1), h * r / k ≤ h - 1 := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hlt : r * h < k * h := Nat.mul_lt_mul_of_pos_right (by omega) hh
    have hdiv_lt : h * r / k < h := by
      rw [mul_comm] at hlt
      exact Nat.div_lt_of_lt_mul hlt
    omega
  have hstep1 :
      ∑ r ∈ Finset.Icc 1 (k - 1),
          ((h * r / k : ℕ) : ℝ) * (((h * r / k : ℕ) : ℝ) + 1) =
        2 * ∑ r ∈ Finset.Icc 1 (k - 1),
          ∑ s ∈ Finset.Icc 1 (h - 1), (if s * k ≤ h * r then (s : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [h1 (h * r / k)]
    congr 1
    have hsub : Finset.Icc 1 (h * r / k) =
        (Finset.Icc 1 (h - 1)).filter (fun s => s * k ≤ h * r) := by
      ext s
      simp only [Finset.mem_Icc, Finset.mem_filter]
      constructor
      · intro hs
        have hsb : s ≤ h - 1 := hs.2.trans (hbound r hr)
        have hsk : s * k ≤ h * r := (Nat.le_div_iff_mul_le hk).mp hs.2
        exact ⟨⟨hs.1, hsb⟩, hsk⟩
      · rintro ⟨hs, hsk⟩
        exact ⟨hs.1, (Nat.le_div_iff_mul_le hk).mpr hsk⟩
    rw [hsub, Finset.sum_filter]
  rw [hstep1, Finset.sum_comm]
  have hcount : ∀ s ∈ Finset.Icc 1 (h - 1),
      ∑ r ∈ Finset.Icc 1 (k - 1), (if s * k ≤ h * r then (s : ℝ) else 0) =
        (s : ℝ) * ((k : ℝ) - 1 - ((s * k / h : ℕ) : ℝ)) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hne : ∀ r ∈ Finset.Icc 1 (k - 1), s * k ≠ h * r := by
      intro r _ heq
      have hdvd : h ∣ s * k := ⟨r, heq⟩
      have hds : h ∣ s := hcop.dvd_of_dvd_mul_right hdvd
      have hle : h ≤ s := Nat.le_of_dvd hs.1 hds
      omega
    have hlt_k : s * k / h ≤ k - 1 := by
      have hsk_lt : s * k < h * k := Nat.mul_lt_mul_of_pos_right (by omega) hk
      have hdiv_lt : s * k / h < k := Nat.div_lt_of_lt_mul hsk_lt
      omega
    have hfilt : (Finset.Icc 1 (k - 1)).filter (fun r => s * k ≤ h * r) =
        Finset.Icc (s * k / h + 1) (k - 1) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hr, hle⟩
        have hlt : s * k < h * r := lt_of_le_of_ne hle (hne r (Finset.mem_Icc.mpr hr))
        have hdiv : s * k / h < r := (Nat.div_lt_iff_lt_mul hh).mpr (by linarith)
        exact ⟨hdiv, hr.2⟩
      · intro hr
        have h1r : 1 ≤ r := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hr.1
        have hdiv : s * k / h < r := Nat.lt_of_succ_le hr.1
        have hlt : s * k < h * r := by linarith [(Nat.div_lt_iff_lt_mul hh).mp hdiv]
        exact ⟨⟨h1r, hr.2⟩, hlt.le⟩
    rw [← Finset.sum_filter, hfilt, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : k - 1 + 1 - (s * k / h + 1) = k - 1 - s * k / h := by omega
    rw [hcard, Nat.cast_sub hlt_k, Nat.cast_sub hk]
    ring
  rw [Finset.sum_congr rfl hcount]
  have hdedekind :
      2 * (h : ℝ) * dedekindSum k h =
        (2 * (k : ℝ) / (h : ℝ)) * (∑ s ∈ Finset.Icc 1 (h - 1), (s : ℝ) ^ 2) -
          2 * (∑ s ∈ Finset.Icc 1 (h - 1), (s : ℝ) * ((s * k / h : ℕ) : ℝ)) -
          ∑ s ∈ Finset.Icc 1 (h - 1), (s : ℝ) := by
    rw [dedekindSum_eq_sum_div_mul (k : ℤ) hh, Finset.mul_sum]
    have hnot_int_s : ∀ s ∈ Finset.Icc 1 (h - 1), ¬ h ∣ k * s := by
      intro s hs hdvd
      rw [Finset.mem_Icc] at hs
      have hds : h ∣ s := hcop.dvd_of_dvd_mul_left hdvd
      have hle : h ≤ s := Nat.le_of_dvd hs.1 hds
      omega
    have hterm_s : ∀ s ∈ Finset.Icc 1 (h - 1),
        2 * (h : ℝ) * (((s : ℝ) / h) * sawtoothEta (((k : ℤ) : ℝ) * s / h)) =
          (2 * (k : ℝ) / (h : ℝ)) * (s : ℝ) ^ 2 -
            2 * (s : ℝ) * ((s * k / h : ℕ) : ℝ) - (s : ℝ) := by
      intro s hs
      have hdiv : s * k = h * (s * k / h) + (s * k) % h := (Nat.div_add_mod (s * k) h).symm
      have hmod_pos : 0 < (s * k) % h := Nat.pos_of_ne_zero fun h0 =>
        hnot_int_s s hs (by rw [mul_comm]; exact Nat.dvd_of_mod_eq_zero h0)
      have hmod_lt : (s * k) % h < h := Nat.mod_lt (s * k) hh
      have hsplit : ((k : ℤ) : ℝ) * s / h =
          (((s * k) % h : ℕ) : ℝ) / h + ((s * k / h : ℕ) : ℤ) := by
        have hdivR : (s : ℝ) * k = (h : ℝ) * (s * k / h : ℕ) + ((s * k) % h : ℕ) := by
          exact_mod_cast hdiv
        have hksc : ((k : ℤ) : ℝ) * s = (s : ℝ) * k := by push_cast; ring
        rw [hksc, hdivR, Int.cast_natCast]
        field_simp [hhR]
        ring
      have hfrac0 : 0 < (((s * k) % h : ℕ) : ℝ) / h := by
        have : (1 : ℝ) ≤ ((s * k) % h : ℕ) := by exact_mod_cast hmod_pos
        positivity
      have hfrac1 : (((s * k) % h : ℕ) : ℝ) / h < 1 := by
        have : (((s * k) % h : ℕ) : ℝ) < h := by exact_mod_cast hmod_lt
        exact (div_lt_one (by positivity)).mpr this
      rw [hsplit, sawtoothEta_add_intCast, sawtoothEta_of_Ioo hfrac0 hfrac1]
      have hdivR : (s : ℝ) * k = (h : ℝ) * (s * k / h : ℕ) + ((s * k) % h : ℕ) := by
        exact_mod_cast hdiv
      have hmodR : (((s * k) % h : ℕ) : ℝ) = (s : ℝ) * k - (h : ℝ) * (s * k / h : ℕ) := by linarith
      rw [hmodR]
      field_simp [hhR]
    rw [Finset.sum_congr rfl hterm_s, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have hmul2 : ∑ s ∈ Finset.Icc 1 (h - 1), 2 * (s : ℝ) * ((s * k / h : ℕ) : ℝ) =
        2 * ∑ s ∈ Finset.Icc 1 (h - 1), (s : ℝ) * ((s * k / h : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by ring
    rw [hmul2]
  have hexpand :
      2 * ∑ s ∈ Finset.Icc 1 (h - 1), (s : ℝ) * ((k : ℝ) - 1 - ((s * k / h : ℕ) : ℝ)) =
        2 * ((k : ℝ) - 1) * (∑ s ∈ Finset.Icc 1 (h - 1), (s : ℝ)) -
          2 * (∑ s ∈ Finset.Icc 1 (h - 1), (s : ℝ) * ((s * k / h : ℕ) : ℝ)) := by
    have hsub : ∀ s ∈ Finset.Icc 1 (h - 1),
        (s : ℝ) * ((k : ℝ) - 1 - ((s * k / h : ℕ) : ℝ)) =
          ((k : ℝ) - 1) * (s : ℝ) - (s : ℝ) * ((s * k / h : ℕ) : ℝ) := fun s _ => by ring
    rw [Finset.sum_congr rfl hsub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hexpand]
  rw [sum_Icc_cast_id h, sum_Icc_cast_sq h] at hdedekind
  rw [sum_Icc_cast_id h]
  field_simp [hhR] at hdedekind ⊢
  linarith

/-- **Dedekind's Reciprocity Law** (polynomial identity form): for coprime positive integers
`h, k ≥ 1`, `12 * h * k * (s(h, k) + s(k, h)) = h ^ 2 + k ^ 2 + 1 - 3 * h * k`. -/
theorem dedekind_reciprocity {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (hcop : Nat.Coprime h k) :
    12 * (h : ℝ) * (k : ℝ) * (dedekindSum h k + dedekindSum k h) =
      (h : ℝ) ^ 2 + (k : ℝ) ^ 2 + 1 - 3 * (h : ℝ) * (k : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hmain := two_mul_dedekindSum_add_floor_prod hh hk hcop
  have hfl := sum_floor_mul_succ_eq hh hk hcop
  rw [hfl, sum_Icc_cast_id k, sum_Icc_cast_sq k] at hmain
  have hmul : 6 * (k : ℝ) * (2 * (h : ℝ) * dedekindSum h k + 2 * (h : ℝ) * dedekindSum k h) =
      12 * (h : ℝ) * (k : ℝ) * (dedekindSum h k + dedekindSum k h) := by ring
  rw [← hmul]
  have hmain6 :
      6 * (k : ℝ) * (2 * (h : ℝ) * dedekindSum h k +
          (2 * (h : ℝ) * dedekindSum k h + (k : ℝ) * (h : ℝ) * ((h : ℝ) - 1) -
            (h : ℝ) * ((h : ℝ) - 1) / 2 -
            (k : ℝ) * ((h : ℝ) - 1) * (2 * (h : ℝ) - 1) / 3)) =
        6 * (k : ℝ) * (((1 + (h : ℝ) ^ 2) / (k : ℝ) ^ 2) *
            ((k : ℝ) * ((k : ℝ) - 1) * (2 * (k : ℝ) - 1) / 6) -
          (1 / (k : ℝ)) * ((k : ℝ) * ((k : ℝ) - 1) / 2)) := congrArg (6 * (k : ℝ) * ·) hmain
  field_simp [hkR] at hmain6
  linarith

/-- **Dedekind's Reciprocity Law** (rational sum form): for coprime positive integers `h, k ≥ 1`,
`s(h, k) + s(k, h) = -1 / 4 + (h / k + k / h + 1 / (h * k)) / 12`. -/
theorem dedekind_reciprocity_div {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (hcop : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h =
      -1 / 4 + ((h : ℝ) / k + (k : ℝ) / h + 1 / ((h : ℝ) * k)) / 12 := by
  have hhR : (h : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hrec := dedekind_reciprocity hh hk hcop
  field_simp [hhR, hkR]
  linarith

/-- **Dedekind's Reciprocity Law** for positive integers `h, k : ℤ`. -/
theorem dedekind_reciprocity_int {h k : ℤ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Int.gcd h k = 1) :
    12 * (h : ℝ) * (k : ℝ) * (dedekindSum h k.natAbs + dedekindSum k h.natAbs) =
      (h : ℝ) ^ 2 + (k : ℝ) ^ 2 + 1 - 3 * (h : ℝ) * (k : ℝ) := by
  obtain ⟨hn, rfl⟩ := Int.eq_ofNat_of_zero_le hh.le
  obtain ⟨kn, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
  have hnp : 1 ≤ hn := by omega
  have hkp : 1 ≤ kn := by omega
  have hcn : Nat.Coprime hn kn := by simpa [Int.gcd] using hcop
  simpa using dedekind_reciprocity hnp hkp hcn

/-- Cauchy-Schwarz / permutation bound: for coprime `h` and `k ≥ 1`,
`|dedekindSum h k| ≤ dedekindSum 1 k`. -/
theorem abs_dedekindSum_le_one_left {h : ℤ} {k : ℕ} (hk : 1 ≤ k) (hcop : IsCoprime h (k : ℤ)) :
    |dedekindSum h k| ≤ dedekindSum 1 k := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hcs : ∀ r ∈ Finset.Icc 1 (k - 1),
      |sawtoothEta ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k)| ≤
        ((sawtoothEta ((r : ℝ) / k)) ^ 2 + (sawtoothEta ((h : ℝ) * r / k)) ^ 2) / 2 := by
    intro r _
    rw [abs_mul]
    nlinarith [sq_nonneg (|sawtoothEta ((r : ℝ) / k)| - |sawtoothEta ((h : ℝ) * r / k)|),
      sq_abs (sawtoothEta ((r : ℝ) / k)), sq_abs (sawtoothEta ((h : ℝ) * r / k))]
  have hsum_le : |dedekindSum h k| ≤
      ((∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((r : ℝ) / k)) ^ 2) +
       (∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((h : ℝ) * r / k)) ^ 2)) / 2 := by
    calc |dedekindSum h k|
        ≤ ∑ r ∈ Finset.Icc 1 (k - 1),
            |sawtoothEta ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.Icc 1 (k - 1),
            ((sawtoothEta ((r : ℝ) / k)) ^ 2 + (sawtoothEta ((h : ℝ) * r / k)) ^ 2) / 2 :=
          Finset.sum_le_sum hcs
      _ = ((∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((r : ℝ) / k)) ^ 2) +
           (∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((h : ℝ) * r / k)) ^ 2)) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hperm : ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((h : ℝ) * r / k)) ^ 2 =
      ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((r : ℝ) / k)) ^ 2 := by
    let f : ℕ → ℕ := fun r => (h * (r : ℤ)).natMod k
    have hnot_dvd : ∀ r ∈ Finset.Icc 1 (k - 1), ¬ ((k : ℤ) ∣ h * r) := by
      intro r hr hdvd
      rw [Finset.mem_Icc] at hr
      have hk_dvd : (k : ℤ) ∣ r := hcop.symm.dvd_of_dvd_mul_left hdvd
      have hle : k ≤ r := Int.ofNat_le.mp (Int.le_of_dvd (by exact_mod_cast hr.1) hk_dvd)
      omega
    have hf_sub : (Finset.Icc 1 (k - 1)).image f ⊆ Finset.Icc 1 (k - 1) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
      rw [Finset.mem_Icc]
      have hmod_ne : (h * (r : ℤ)) % k ≠ 0 := fun h0 =>
        hnot_dvd r hr (Int.dvd_of_emod_eq_zero h0)
      have hpos_z : 0 < (h * (r : ℤ)) % k :=
        lt_of_le_of_ne (Int.emod_nonneg _ (by positivity)) (Ne.symm hmod_ne)
      have hpos : 0 < f r := by
        dsimp [f]
        rw [Int.natMod]
        omega
      have hlt : f r ≤ k - 1 := by
        have hlt_k : f r < k := @Int.natMod_lt (h * (r : ℤ)) k (by positivity)
        omega
      exact ⟨hpos, hlt⟩
    have hf_inj : Set.InjOn f (Finset.Icc 1 (k - 1)) := by
      intro r₁ hr₁ r₂ hr₂ heq
      simp only [Finset.mem_coe, Finset.mem_Icc] at hr₁ hr₂
      have hmod1 : (h * (r₁ : ℤ)) % k = (h * (r₂ : ℤ)) % k := by
        have h1 : ((f r₁ : ℕ) : ℤ) = (h * (r₁ : ℤ)) % k := by
          dsimp [f]; rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
        have h2 : ((f r₂ : ℕ) : ℤ) = (h * (r₂ : ℤ)) % k := by
          dsimp [f]; rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
        rw [← h1, ← h2, heq]
      have hdvd : (k : ℤ) ∣ h * ((r₁ : ℤ) - r₂) := by
        have hmodEq : h * (r₁ : ℤ) ≡ h * (r₂ : ℤ) [ZMOD k] := hmod1
        rw [Int.modEq_iff_dvd] at hmodEq
        have : h * ((r₁ : ℤ) - r₂) = -(h * r₂ - h * r₁) := by ring
        rw [this]
        exact dvd_neg.mpr hmodEq
      have hdvd_diff : (k : ℤ) ∣ (r₁ : ℤ) - r₂ := hcop.symm.dvd_of_dvd_mul_left hdvd
      have hdiff_lt : |(r₁ : ℤ) - r₂| < k := by
        rw [abs_lt]
        constructor <;> omega
      obtain ⟨q, hq⟩ := hdvd_diff
      have hq0 : q = 0 := by nlinarith [abs_lt.mp hdiff_lt]
      have hzero : (r₁ : ℤ) - r₂ = 0 := by rw [hq, hq0, mul_zero]
      omega
    have himg_eq : (Finset.Icc 1 (k - 1)).image f = Finset.Icc 1 (k - 1) :=
      Finset.eq_of_subset_of_card_le hf_sub (by rw [Finset.card_image_of_injOn hf_inj])
    calc ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((h : ℝ) * r / k)) ^ 2
        = ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((f r : ℝ) / k)) ^ 2 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hmodEq : h * (r : ℤ) ≡ (f r : ℤ) [ZMOD k] := by
            dsimp [f]
            rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
            exact (Int.mod_modEq (h * r) k).symm
          have hs := sawtoothEta_div_eq_of_modEq hmodEq
          simp only [Int.cast_natCast] at hs
          have hcast : ((h * (r : ℤ) : ℤ) : ℝ) / k = (h : ℝ) * r / k := by push_cast; ring
          rw [← hcast, hs]
      _ = ∑ y ∈ (Finset.Icc 1 (k - 1)).image f, (sawtoothEta ((y : ℝ) / k)) ^ 2 := by
          symm
          exact Finset.sum_image (f := fun y : ℕ => (sawtoothEta ((y : ℝ) / k)) ^ 2)
            fun x hx y hy hxy => hf_inj hx hy hxy
      _ = ∑ y ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((y : ℝ) / k)) ^ 2 := by rw [himg_eq]
  have h1k : ∑ r ∈ Finset.Icc 1 (k - 1), (sawtoothEta ((r : ℝ) / k)) ^ 2 = dedekindSum 1 k := by
    unfold dedekindSum
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 : ((1 : ℤ) : ℝ) * r / k = (r : ℝ) / k := by ring
    rw [h1, sq]
  rw [hperm, h1k] at hsum_le
  linarith

/-- Elementary upper bound `|dedekindSum h k| ≤ (k - 1) / 4` for `k ≥ 1`. -/
theorem abs_dedekindSum_le (h : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    |dedekindSum h k| ≤ ((k : ℝ) - 1) / 4 := by
  unfold dedekindSum
  calc |∑ r ∈ Finset.Icc 1 (k - 1), sawtoothEta ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k)|
      ≤ ∑ r ∈ Finset.Icc 1 (k - 1),
          |sawtoothEta ((r : ℝ) / k) * sawtoothEta ((h : ℝ) * r / k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Finset.Icc 1 (k - 1), (1 / 4 : ℝ) := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [abs_mul]
        calc |sawtoothEta ((r : ℝ) / k)| * |sawtoothEta ((h : ℝ) * r / k)|
            ≤ (1 / 2) * (1 / 2) :=
              mul_le_mul (abs_sawtoothEta_le _) (abs_sawtoothEta_le _) (abs_nonneg _) (by norm_num)
          _ = 1 / 4 := by norm_num
    _ = ((k : ℝ) - 1) / 4 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, Nat.cast_sub hk]
        ring

end ReciprocityLaw

end AnalyticNumberTheory.ModularAndPartitions
