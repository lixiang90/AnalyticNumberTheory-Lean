/-
Copyright (c) 2026 AnalyticNumberTheory-Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ZetaValues
import AnalyticNumberTheory.AnalyticTools.Gamma.InfiniteProducts

/-!
# Integer Partitions, Euler's Pentagonal Number Theorem, and Asymptotics

This file develops the analytic and combinatorial theory of the unrestricted integer
partition function `p(n)`:

- The partition function `partitionCount n := Fintype.card (Nat.Partition n)`, restricted
  partition counts `restrictedPartitionCount n m`, exact small values `p(0)..p(6)`,
  monotonicity, the combinatorial divisor-sum identity
  `n * p(n) = ∑_{l=1}^n σ(l) * p(n - l)`, and bridges to Mathlib's `Nat.Partition.genFun`.
- Analytic generating function identity `∑' n, p(n) * x ^ n = (∏' k, (1 - x ^ (k + 1)))⁻¹`
  for `‖x‖ < 1` (both in `ℂ` and in `ℝ`).
- Jacobi's triple product identity, Euler's pentagonal number theorem
  `∏' k, (1 - x ^ (k + 1)) = 1 + ∑' m : ℕ+, (-1) ^ m * (x ^ (m*(3*m-1)/2) + x ^ (m*(3*m+1)/2))`,
  and Euler's recurrence for `p(n)`.
- Saddle-point logarithm series `log F(e^{-t}) = ∑' m : ℕ+, 1 / (m * (e^{mt} - 1))`,
  the sharp elementary upper bound `p(n) < exp (π * √(2 * n / 3))` for `n ≥ 1`, and
  exponential lower bounds `exp (c * √n) ≤ p(n)`.
- Circle-method integral representations of `p(n)` over `[0, 1]` and `C(0, r)`, radial
  maximum and minor-arc decay bounds, the Hardy–Ramanujan asymptotic formula
  `p(n) ~ (1 / (4 * n * √3)) * exp (π * √(2 * n / 3))`, and the Rademacher series
  framework with the proof that the Rademacher series implies the Hardy–Ramanujan asymptotic.
-/

noncomputable section

open Finset Filter Asymptotics Topology MeasureTheory
open scoped BigOperators Nat PowerSeries PowerSeries.WithPiTopology

namespace AnalyticNumberTheory.ModularAndPartitions

section PartitionCount

/-- The unrestricted partition function `p(n)`, counting the number of integer partitions of `n`. -/
def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

/-- Bridge to Mathlib's `Fintype.card (Nat.Partition n)`. -/
theorem partitionCount_eq_card (n : ℕ) : partitionCount n = Fintype.card (Nat.Partition n) := rfl

/-- `partitionCount 0 = 1`. -/
@[simp]
theorem partitionCount_zero : partitionCount 0 = 1 := by
  rw [partitionCount, Fintype.card_unique]

/-- `partitionCount 1 = 1`. -/
@[simp]
theorem partitionCount_one : partitionCount 1 = 1 := by
  rw [partitionCount, Fintype.card_unique]

/-- `partitionCount n` is strictly positive for all `n`. -/
theorem partitionCount_pos (n : ℕ) : 0 < partitionCount n := by
  rw [partitionCount]
  exact Fintype.card_pos

/-- `partitionCount` is monotonically non-decreasing (`p(n) ≤ p(n + 1)`). -/
theorem partitionCount_mono_succ (n : ℕ) : partitionCount n ≤ partitionCount (n + 1) := by
  classical
  have hinj : Function.Injective (fun p : Nat.Partition n =>
      ((Nat.Partition.partitionWithPartEquiv (n := n + 1) (a := 1) le_rfl (by omega)).symm p).1) := by
    intro p₁ p₂ heq
    have hparts : (1 ::ₘ p₁.parts) = (1 ::ₘ p₂.parts) := by
      have h1 := congrArg Nat.Partition.parts heq
      rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts,
          Nat.Partition.partitionWithPartEquiv_symm_apply_parts] at h1
      exact h1
    exact Nat.Partition.ext (Multiset.cons_inj_right 1 |>.mp hparts)
  simpa [partitionCount] using Fintype.card_le_of_injective _ hinj

/-- `partitionCount` is monotonically non-decreasing: `m ≤ n → p(m) ≤ p(n)`. -/
theorem partitionCount_mono {m n : ℕ} (h : m ≤ n) : partitionCount m ≤ partitionCount n := by
  induction h with
  | refl => exact le_rfl
  | @step k _ ih => exact ih.trans (partitionCount_mono_succ k)

/-- The number of partitions of `n` whose parts are all at most `m`. -/
def restrictedPartitionCount (n m : ℕ) : ℕ :=
  #(Nat.Partition.restricted n (· ≤ m))

/-- There is a unique partition of `0` with all parts at most `m`. -/
@[simp]
theorem restrictedPartitionCount_zero_left (m : ℕ) : restrictedPartitionCount 0 m = 1 := by
  rw [restrictedPartitionCount]
  have huniv : Nat.Partition.restricted 0 (· ≤ m) = Finset.univ := by
    ext p
    simp [Nat.Partition.restricted]
  rw [huniv, Finset.card_univ, Fintype.card_unique]

/-- For `n ≥ 1`, there are no partitions of `n` with all parts at most `0`. -/
@[simp]
theorem restrictedPartitionCount_zero_right {n : ℕ} (hn : 1 ≤ n) :
    restrictedPartitionCount n 0 = 0 := by
  rw [restrictedPartitionCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hne : p.parts ≠ 0 := by
    intro h0
    have hsum := p.parts_sum
    rw [h0, Multiset.sum_zero] at hsum
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  have ha0 := p.parts_pos ha
  have hale := hp a ha
  omega

/-- `restrictedPartitionCount n m ≤ partitionCount n`. -/
theorem restrictedPartitionCount_le (n m : ℕ) :
    restrictedPartitionCount n m ≤ partitionCount n := by
  rw [restrictedPartitionCount, partitionCount, ← Finset.card_univ]
  exact Finset.card_le_univ _

/-- When `n ≤ m`, every partition of `n` has all parts at most `m`, so
`restrictedPartitionCount n m = partitionCount n`. -/
theorem restrictedPartitionCount_eq_of_le {n m : ℕ} (hnm : n ≤ m) :
    restrictedPartitionCount n m = partitionCount n := by
  rw [restrictedPartitionCount, partitionCount, ← Finset.card_univ]
  congr 1
  ext p
  simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  intro i hi
  exact (Nat.Partition.le_of_mem_parts hi).trans hnm

/-- Recurrence for `restrictedPartitionCount` on the upper bound `m + 1`. -/
theorem restrictedPartitionCount_succ (n m : ℕ) :
    restrictedPartitionCount n (m + 1) =
      restrictedPartitionCount n m +
        (if m + 1 ≤ n then restrictedPartitionCount (n - (m + 1)) (m + 1) else 0) := by
  classical
  set S := Nat.Partition.restricted n (· ≤ m + 1)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun p : Nat.Partition n => m + 1 ∈ p.parts)
  have hnot : S.filter (fun p => m + 1 ∉ p.parts) = Nat.Partition.restricted n (· ≤ m) := by
    ext p
    simp only [S, Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hle, hnotmem⟩ i hi
      have h1 := hle i hi
      have hne : i ≠ m + 1 := fun h => hnotmem (h ▸ hi)
      omega
    · intro hle
      refine ⟨fun i hi => (hle i hi).trans (Nat.le_succ m), fun hmem => ?_⟩
      have := hle (m + 1) hmem
      omega
  have hmem : #(S.filter (fun p => m + 1 ∈ p.parts)) =
      if m + 1 ≤ n then restrictedPartitionCount (n - (m + 1)) (m + 1) else 0 := by
    split_ifs with hmn
    · rw [restrictedPartitionCount]
      refine Finset.card_bij
        (fun p hp =>
          let hp' : m + 1 ∈ p.parts := (Finset.mem_filter.mp hp).2
          Nat.Partition.partitionWithPartEquiv (by omega : 1 ≤ m + 1) hmn ⟨p, hp'⟩)
        ?_ ?_ ?_
      · intro p hp
        simp only [S, Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        intro i hi
        have hip : i ∈ p.parts :=
          Multiset.mem_of_le (Multiset.erase_le (m + 1) p.parts) hi
        exact hp.1 i hip
      · intro p₁ hp₁ p₂ hp₂ heq
        have hp₁' : m + 1 ∈ p₁.parts := (Finset.mem_filter.mp hp₁).2
        have hp₂' : m + 1 ∈ p₂.parts := (Finset.mem_filter.mp hp₂).2
        have hinj := (Nat.Partition.partitionWithPartEquiv (by omega : 1 ≤ m + 1) hmn).injective heq
        exact congrArg Subtype.val hinj
      · intro q hq
        simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        let e := Nat.Partition.partitionWithPartEquiv (by omega : 1 ≤ m + 1) hmn
        refine ⟨(e.symm q).1, ?_, ?_⟩
        · simp only [S, Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun i hi => ?_, (e.symm q).2⟩
          rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts] at hi
          rcases Multiset.mem_cons.mp hi with rfl | hiq
          · exact le_rfl
          · exact hq i hiq
        · exact Equiv.apply_symm_apply e q
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have hp' : m + 1 ∈ p.parts := (Finset.mem_filter.mp hp).2
      exact hmn (Nat.Partition.le_of_mem_parts hp')
  simp_rw [restrictedPartitionCount] at hmem ⊢
  rw [← hsplit, add_comm, hnot, hmem]

private def partRecFuel : ℕ → ℕ → ℕ → ℕ
  | _, 0, _ => 1
  | _, _ + 1, 0 => 0
  | 0, _ + 1, _ + 1 => 0
  | f + 1, n + 1, m + 1 =>
      partRecFuel f (n + 1) m +
        if m + 1 ≤ n + 1 then partRecFuel f (n + 1 - (m + 1)) (m + 1) else 0

private lemma restrictedPartitionCount_eq_partRecFuel (f n m : ℕ) (hf : n + m ≤ f) :
    restrictedPartitionCount n m = partRecFuel f n m := by
  induction f generalizing n m with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    simp [partRecFuel]
  | succ f ih =>
    rcases n with _ | n
    · simp [partRecFuel]
    · rcases m with _ | m
      · simp [partRecFuel]
      · rw [restrictedPartitionCount_succ, partRecFuel]
        rw [ih (n + 1) m (by omega)]
        split_ifs with hle
        · rw [ih (n + 1 - (m + 1)) (m + 1) (by omega)]
        · rfl

/-- `partitionCount 2 = 2`. -/
theorem partitionCount_two : partitionCount 2 = 2 := by
  rw [← restrictedPartitionCount_eq_of_le (le_refl 2),
      restrictedPartitionCount_eq_partRecFuel 4 2 2 (by omega)]
  rfl

/-- `partitionCount 3 = 3`. -/
theorem partitionCount_three : partitionCount 3 = 3 := by
  rw [← restrictedPartitionCount_eq_of_le (le_refl 3),
      restrictedPartitionCount_eq_partRecFuel 6 3 3 (by omega)]
  rfl

/-- `partitionCount 4 = 5`. -/
theorem partitionCount_four : partitionCount 4 = 5 := by
  rw [← restrictedPartitionCount_eq_of_le (le_refl 4),
      restrictedPartitionCount_eq_partRecFuel 8 4 4 (by omega)]
  rfl

/-- `partitionCount 5 = 7`. -/
theorem partitionCount_five : partitionCount 5 = 7 := by
  rw [← restrictedPartitionCount_eq_of_le (le_refl 5),
      restrictedPartitionCount_eq_partRecFuel 10 5 5 (by omega)]
  rfl

/-- `partitionCount 6 = 11`. -/
theorem partitionCount_six : partitionCount 6 = 11 := by
  rw [← restrictedPartitionCount_eq_of_le (le_refl 6),
      restrictedPartitionCount_eq_partRecFuel 12 6 6 (by omega)]
  rfl

/-- Coefficient bridge to Mathlib's `Nat.Partition.genFun`. -/
theorem coeff_genFun_one (n : ℕ) :
    (Nat.Partition.genFun (fun _ _ => (1 : ℝ))).coeff n = (partitionCount n : ℝ) := by
  simp [Nat.Partition.coeff_genFun, partitionCount]

/-- Formal power series identity in `ℝ⟦X⟧`:
`Nat.Partition.genFun (fun _ _ => 1) * ∏' i, (1 - X ^ (i + 1)) = 1`. -/
theorem genFun_one_mul_tprod_eq_one :
    Nat.Partition.genFun (fun _ _ => (1 : ℝ)) *
        ∏' i : ℕ, (1 - (PowerSeries.X : ℝ⟦X⟧) ^ (i + 1)) = 1 := by
  rw [Nat.Partition.genFun_eq_tprod]
  have hm1 : Multipliable fun i : ℕ =>
      (1 : ℝ⟦X⟧) + ∑' j : ℕ, (1 : ℝ) • (PowerSeries.X : ℝ⟦X⟧) ^ ((i + 1) * (j + 1)) :=
    Nat.Partition.multipliable_genFun (fun _ _ => (1 : ℝ))
  have hm2 : Multipliable fun i : ℕ => (1 : ℝ⟦X⟧) - (PowerSeries.X : ℝ⟦X⟧) ^ (i + 1) :=
    PowerSeries.WithPiTopology.multipliable_one_sub_X_pow (R := ℝ)
  rw [← hm1.tprod_mul hm2]
  have hterm : ∀ i : ℕ,
      ((1 : ℝ⟦X⟧) + ∑' j : ℕ, (1 : ℝ) • (PowerSeries.X : ℝ⟦X⟧) ^ ((i + 1) * (j + 1))) *
        ((1 : ℝ⟦X⟧) - (PowerSeries.X : ℝ⟦X⟧) ^ (i + 1)) = 1 := by
    intro i
    have hsum : (1 : ℝ⟦X⟧) + ∑' j : ℕ, (1 : ℝ) • (PowerSeries.X : ℝ⟦X⟧) ^ ((i + 1) * (j + 1)) =
        ∑' j : ℕ, (PowerSeries.X : ℝ⟦X⟧) ^ ((i + 1) * j) := by
      have hs : Summable fun j : ℕ => (PowerSeries.X : ℝ⟦X⟧) ^ ((i + 1) * j) := by
        simp_rw [pow_mul]
        exact PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero (by simp)
      rw [hs.tsum_eq_zero_add]
      simp [one_smul, pow_mul]
    rw [hsum]
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  have h1 : (fun b : ℕ =>
      ((1 : ℝ⟦X⟧) + ∑' j : ℕ, (1 : ℝ) • (PowerSeries.X : ℝ⟦X⟧) ^ ((b + 1) * (j + 1))) *
        ((1 : ℝ⟦X⟧) - (PowerSeries.X : ℝ⟦X⟧) ^ (b + 1))) = fun _ => 1 :=
    funext hterm
  rw [h1, tprod_one]

/-- Combinatorial divisor-sum recurrence for the partition function:
`n * p(n) = ∑_{l=1}^n σ(l) * p(n - l)`. -/
theorem mul_partitionCount_eq_sum_divisor (n : ℕ) :
    n * partitionCount n =
      ∑ l ∈ Finset.Icc 1 n, (∑ d ∈ Nat.divisors l, d) * partitionCount (n - l) := by
  classical
  have hP : n * partitionCount n = ∑ _p : Nat.Partition n, n := by
    simp [partitionCount, mul_comm]
  have hsum_p : ∀ p : Nat.Partition n,
      n = ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, if k ≤ p.parts.count d then d else 0 := by
    intro p
    have hsub : p.parts.toFinset ⊆ Finset.Icc 1 n := by
      intro d hd
      rw [Multiset.mem_toFinset] at hd
      exact Finset.mem_Icc.mpr ⟨p.parts_pos hd, Nat.Partition.le_of_mem_parts hd⟩
    have hn_eq : n = ∑ d ∈ Finset.Icc 1 n, p.parts.count d * d := by
      calc n = p.parts.sum := p.parts_sum.symm
        _ = ∑ d ∈ p.parts.toFinset, p.parts.count d * d := by
            simpa [smul_eq_mul] using Finset.sum_multiset_count p.parts
        _ = ∑ d ∈ Finset.Icc 1 n, p.parts.count d * d := by
            refine Finset.sum_subset hsub ?_
            intro d _ hd
            rw [Multiset.mem_toFinset] at hd
            simp [Multiset.count_eq_zero.mpr hd]
    conv_lhs => rw [hn_eq]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hcnt_le : p.parts.count d ≤ n := by
      calc p.parts.count d ≤ p.parts.count d * d := Nat.le_mul_of_pos_right _ hd.1
        _ ≤ ∑ x ∈ Finset.Icc 1 n, p.parts.count x * x :=
            Finset.single_le_sum (f := fun x => p.parts.count x * x)
              (fun x _ => Nat.zero_le _) (Finset.mem_Icc.mpr hd)
        _ = n := hn_eq.symm
    have hfilt : (Finset.Icc 1 n).filter (fun k => k ≤ p.parts.count d) =
        Finset.Icc 1 (p.parts.count d) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [← Finset.sum_filter, hfilt, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
        Nat.add_sub_cancel]
  rw [hP]
  have hsum_all :
      (∑ _p : Nat.Partition n, n) =
        ∑ d ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n, ∑ k ∈ Finset.Icc 1 n,
          if k ≤ p.parts.count d then d else 0 := by
    calc (∑ _p : Nat.Partition n, n)
        = ∑ p : Nat.Partition n, ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
            if k ≤ p.parts.count d then d else 0 := Finset.sum_congr rfl fun p _ => hsum_p p
      _ = ∑ d ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n, ∑ k ∈ Finset.Icc 1 n,
            if k ≤ p.parts.count d then d else 0 := Finset.sum_comm
  rw [hsum_all]
  have hswap1 :
      ∑ d ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n, ∑ k ∈ Finset.Icc 1 n,
          (if k ≤ p.parts.count d then d else 0) =
        ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
          d * #(Finset.univ.filter fun p : Nat.Partition n => k ≤ p.parts.count d) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hite : ∀ p : Nat.Partition n,
        (if k ≤ p.parts.count d then d else 0) =
          (if k ≤ p.parts.count d then 1 else 0) * d := fun p => by
      split_ifs <;> simp
    simp_rw [hite, ← Finset.sum_mul, Finset.sum_boole]
    simp [mul_comm]
  rw [hswap1]
  have hcard : ∀ d ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
      #(Finset.univ.filter fun p : Nat.Partition n => k ≤ p.parts.count d) =
        if d * k ≤ n then partitionCount (n - d * k) else 0 := by
    intro d hd k hk
    rw [Finset.mem_Icc] at hd hk
    split_ifs with hdk
    · rw [partitionCount, ← Finset.card_univ]
      refine Finset.card_bij
        (fun p hp =>
          ⟨p.parts - Multiset.replicate k d,
           fun hi => p.parts_pos (Multiset.mem_of_le tsub_le_self hi),
           by
             have hle : Multiset.replicate k d ≤ p.parts := by
               rw [Multiset.le_iff_count]
               intro a
               by_cases ha : a = d
               · subst ha
                 simpa [Multiset.count_replicate] using (Finset.mem_filter.mp hp).2
               · simp [Multiset.count_replicate, Ne.symm ha]
             have hsum := congrArg Multiset.sum (tsub_add_cancel_of_le hle)
             rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_comm k d,
                 p.parts_sum] at hsum
             omega⟩)
        ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro p₁ hp₁ p₂ hp₂ heq
        have hle1 : Multiset.replicate k d ≤ p₁.parts := by
          rw [Multiset.le_iff_count]
          intro a; by_cases ha : a = d
          · subst ha; simpa [Multiset.count_replicate] using (Finset.mem_filter.mp hp₁).2
          · simp [Multiset.count_replicate, Ne.symm ha]
        have hle2 : Multiset.replicate k d ≤ p₂.parts := by
          rw [Multiset.le_iff_count]
          intro a; by_cases ha : a = d
          · subst ha; simpa [Multiset.count_replicate] using (Finset.mem_filter.mp hp₂).2
          · simp [Multiset.count_replicate, Ne.symm ha]
        have hp_eq := congrArg (fun q : Nat.Partition (n - d * k) => q.parts + Multiset.replicate k d) heq
        dsimp at hp_eq
        rw [tsub_add_cancel_of_le hle1, tsub_add_cancel_of_le hle2] at hp_eq
        exact Nat.Partition.ext hp_eq
      · intro q _
        refine ⟨⟨q.parts + Multiset.replicate k d,
          fun {i} hi => by
            rcases Multiset.mem_add.mp hi with hiq | hir
            · exact q.parts_pos hiq
            · rw [Multiset.mem_replicate.mp hir |>.2]; exact hd.1,
          by
            rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_comm k d, q.parts_sum]
            omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Multiset.count_add, Multiset.count_replicate_self]
          omega
        · exact Nat.Partition.ext (by simp)
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hle : Multiset.replicate k d ≤ p.parts := by
        rw [Multiset.le_iff_count]
        intro a; by_cases ha : a = d
        · subst ha; simpa [Multiset.count_replicate] using hp
        · simp [Multiset.count_replicate, Ne.symm ha]
      have hsum := congrArg Multiset.sum (tsub_add_cancel_of_le hle)
      rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_comm k d, p.parts_sum] at hsum
      omega
  have hlhs :
      ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
          d * #(Finset.univ.filter fun p : Nat.Partition n => k ≤ p.parts.count d) =
        ∑ p ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => p.1 * p.2 ≤ n),
          p.1 * partitionCount (n - p.1 * p.2) := by
    have hinner : ∀ d ∈ Finset.Icc 1 n,
        ∑ k ∈ Finset.Icc 1 n,
            d * #(Finset.univ.filter fun p : Nat.Partition n => k ≤ p.parts.count d) =
          ∑ k ∈ Finset.Icc 1 n, if d * k ≤ n then d * partitionCount (n - d * k) else 0 := by
      intro d hd
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hcard d hd k hk]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_product']
    rw [← Finset.sum_filter]
  rw [hlhs]
  have hrhs :
      ∑ l ∈ Finset.Icc 1 n, (∑ d ∈ Nat.divisors l, d) * partitionCount (n - l) =
        ∑ x ∈ (Finset.Icc 1 n).sigma (fun l => Nat.divisors l),
          x.2 * partitionCount (n - x.1) := by
    simp_rw [Finset.sum_mul, Finset.sum_sigma']
  rw [hrhs]
  refine Finset.sum_bij
    (fun p hp => ⟨p.1 * p.2, p.1⟩)
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    have hmul_pos : 1 ≤ p.1 * p.2 := Nat.mul_pos hp.1.1.1 hp.1.2.1
    exact ⟨⟨hmul_pos, hp.2⟩, ⟨p.2, rfl⟩, by omega⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
    injection heq with hprod hd
    have hp1 : p₁.1 = p₂.1 := by simpa using hd
    have hpos : 0 < p₁.1 := hp₁.1.1.1
    have hp2 : p₁.2 = p₂.2 := Nat.eq_of_mul_eq_mul_left hpos (by rw [← hp1] at hprod; exact hprod)
    exact Prod.ext hp1 hp2
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    rcases hx with ⟨⟨hl1, hln⟩, ⟨k, hlk⟩, hl0⟩
    have hd_pos : 0 < x.2 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlk; omega
    have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlk; omega
    have hd_le : x.2 ≤ n := by
      have : x.2 ≤ x.2 * k := Nat.le_mul_of_pos_right _ hk_pos
      omega
    have hk_le : k ≤ n := by
      have : k ≤ x.2 * k := Nat.le_mul_of_pos_left _ hd_pos
      omega
    refine ⟨(x.2, k), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨hd_pos, hd_le⟩, ⟨hk_pos, hk_le⟩⟩, by rw [← hlk]; exact hln⟩
    · exact Sigma.ext hlk.symm (by simp)
  · intro p _
    rfl

end PartitionCount

section GeneratingFunction

/-- The complex partition generating function `F(z) = (∏' k, (1 - z ^ (k + 1)))⁻¹`. -/
def partitionGenFun (z : ℂ) : ℂ :=
  (∏' k : ℕ, (1 - z ^ (k + 1)))⁻¹

/-- The real partition generating function `F(x) = (∏' k, (1 - x ^ (k + 1)))⁻¹`. -/
def partitionGenFunReal (x : ℝ) : ℝ :=
  (∏' k : ℕ, (1 - x ^ (k + 1)))⁻¹

/-- For `‖z‖ < 1`, `∑' k, ‖-z ^ (k + 1)‖` is summable. -/
theorem summable_norm_neg_pow_succ {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ => ‖-z ^ (k + 1)‖ := by
  have hgeom : Summable fun k : ℕ => ‖z‖ ^ k := summable_geometric_of_lt_one (norm_nonneg _) hz
  simpa [norm_neg, norm_pow, pow_succ] using hgeom.mul_right ‖z‖

/-- For `‖z‖ < 1`, the infinite product `∏' k, (1 - z ^ (k + 1))` converges. -/
theorem multipliable_one_sub_pow {z : ℂ} (hz : ‖z‖ < 1) :
    Multipliable fun k : ℕ => (1 : ℂ) - z ^ (k + 1) := by
  simpa [sub_eq_add_neg] using
    AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm
      (summable_norm_neg_pow_succ hz)

/-- For `‖z‖ < 1`, the infinite product `∏' k, (1 - z ^ (k + 1))` is nonzero. -/
theorem tprod_one_sub_pow_ne_zero {z : ℂ} (hz : ‖z‖ < 1) :
    ∏' k : ℕ, ((1 : ℂ) - z ^ (k + 1)) ≠ 0 := by
  have hne : ∀ k : ℕ, (1 : ℂ) + (-z ^ (k + 1)) ≠ 0 := by
    intro k hk
    have hnorm : ‖z‖ ^ (k + 1) = 1 := by
      have h1 : z ^ (k + 1) = 1 := by linear_combination -hk
      simpa [norm_pow] using congrArg norm h1
    have hlt : ‖z‖ ^ (k + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hz (Nat.succ_ne_zero k)
    linarith
  simpa [sub_eq_add_neg] using
    AnalyticNumberTheory.AnalyticTools.Gamma.tprod_one_add_ne_zero
      (summable_norm_neg_pow_succ hz) hne

/-- For `|x| < 1` in `ℝ`, the infinite product `∏' k, (1 - x ^ (k + 1))` converges and is nonzero. -/
theorem multipliable_one_sub_pow_real {x : ℝ} (hx : |x| < 1) :
    Multipliable fun k : ℕ => (1 : ℝ) - x ^ (k + 1) := by
  have hgeom : Summable fun k : ℕ => ‖-x ^ (k + 1)‖ := by
    have hg : Summable fun k : ℕ => |x| ^ k := summable_geometric_of_lt_one (abs_nonneg _) hx
    simpa [Real.norm_eq_abs, abs_neg, abs_pow, pow_succ] using hg.mul_right |x|
  simpa [sub_eq_add_neg] using
    AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm hgeom

/-- For `|x| < 1` in `ℝ`, `∏' k, (1 - x ^ (k + 1)) ≠ 0`. -/
theorem tprod_one_sub_pow_real_ne_zero {x : ℝ} (hx : |x| < 1) :
    ∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) ≠ 0 := by
  have hne : ∀ k : ℕ, (1 : ℝ) + (-x ^ (k + 1)) ≠ 0 := by
    intro k hk
    have h1 : |x| ^ (k + 1) = 1 := by
      have : x ^ (k + 1) = 1 := by linarith
      simpa [abs_pow] using congrArg abs this
    have hlt : |x| ^ (k + 1) < 1 := pow_lt_one₀ (abs_nonneg _) hx (Nat.succ_ne_zero k)
    linarith
  have hgeom : Summable fun k : ℕ => ‖-x ^ (k + 1)‖ := by
    have hg : Summable fun k : ℕ => |x| ^ k := summable_geometric_of_lt_one (abs_nonneg _) hx
    simpa [Real.norm_eq_abs, abs_neg, abs_pow, pow_succ] using hg.mul_right |x|
  simpa [sub_eq_add_neg] using
    AnalyticNumberTheory.AnalyticTools.Gamma.tprod_one_add_ne_zero hgeom hne

/-- Compatibility between complex and real partition generating functions for `|x| < 1`. -/
theorem partitionGenFun_ofReal {x : ℝ} (hx : |x| < 1) :
    partitionGenFun (x : ℂ) = (partitionGenFunReal x : ℂ) := by
  unfold partitionGenFun partitionGenFunReal
  have hm := multipliable_one_sub_pow_real hx
  have hprod : HasProd (fun k : ℕ => ((1 : ℂ) - (x : ℂ) ^ (k + 1)))
      ((∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) : ℝ) : ℂ) := by
    have hc := (Complex.continuous_ofReal.tendsto _).comp hm.hasProd
    refine hc.congr fun s => ?_
    simp only [Function.comp_apply, Complex.ofReal_prod, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_pow]
  rw [hprod.tprod_eq]
  push_cast
  rfl

/-- For `‖z‖ < 1`, `(∏' k, (1 - z ^ (k + 1)))⁻¹ = ∏' k, (1 - z ^ (k + 1))⁻¹`. -/
theorem partitionGenFun_eq_tprod_inv {z : ℂ} (hz : ‖z‖ < 1) :
    HasProd (fun k : ℕ => ((1 : ℂ) - z ^ (k + 1))⁻¹) (partitionGenFun z) := by
  have hm := multipliable_one_sub_pow hz
  have hnez := tprod_one_sub_pow_ne_zero hz
  have hinv := (continuousAt_inv₀ hnez).tendsto.comp hm.hasProd
  refine hinv.congr fun s => ?_
  simp [Finset.prod_inv_distrib]

/-- Combinatorial identity expressing `restrictedPartitionCount n (M + 1)` as a Cauchy convolution
of `restrictedPartitionCount · M` with multiples of `M + 1`. -/
theorem restrictedPartitionCount_succ_eq_sum_dvd (n M : ℕ) :
    restrictedPartitionCount n (M + 1) =
      ∑ a ∈ Finset.range (n + 1),
        restrictedPartitionCount a M * (if M + 1 ∣ n - a then 1 else 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [restrictedPartitionCount_succ]
    rw [Finset.sum_range_succ, Nat.sub_self]
    simp only [dvd_zero, ↓reduceIte, mul_one]
    rw [add_comm]
    congr 1
    by_cases hmn : M + 1 ≤ n
    · simp only [hmn, ↓reduceIte]
      have hlt : n - (M + 1) < n := by omega
      rw [ih (n - (M + 1)) hlt]
      have hsplit : Finset.range n =
          Finset.range (n - (M + 1) + 1) ∪ Finset.Ico (n - (M + 1) + 1) n := by
        ext a; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (n - (M + 1) + 1)) (Finset.Ico (n - (M + 1) + 1) n) := by
        rw [Finset.disjoint_left]; intro a h1 h2
        rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
      rw [hsplit, Finset.sum_union hdisj]
      have hzero : ∑ a ∈ Finset.Ico (n - (M + 1) + 1) n,
          restrictedPartitionCount a M * (if M + 1 ∣ n - a then 1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        rw [Finset.mem_Ico] at ha
        have hnot : ¬ M + 1 ∣ n - a := by
          intro ⟨q, hq⟩
          rcases Nat.eq_zero_or_pos q with rfl | hqpos
          · omega
          · have : M + 1 ≤ n - a := by
              rw [hq]; exact Nat.le_mul_of_pos_right _ hqpos
            omega
        simp [hnot]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      have ha_le : a ≤ n - (M + 1) := by omega
      have hdvd_iff : M + 1 ∣ n - a ↔ M + 1 ∣ (n - (M + 1)) - a := by
        have heq : n - a = (M + 1) + (n - (M + 1) - a) := by omega
        rw [heq, Nat.dvd_add_self_left]
      simp [hdvd_iff]
    · simp only [hmn, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [Finset.mem_range] at ha
      have hnot : ¬ M + 1 ∣ n - a := by
        intro ⟨q, hq⟩
        rcases Nat.eq_zero_or_pos q with rfl | hqpos
        · omega
        · have : M + 1 ≤ n - a := by
            rw [hq]; exact Nat.le_mul_of_pos_right _ hqpos
          omega
      simp [hnot]

/-- Generating function for partitions with parts at most `M`, valid for `‖z‖ < 1`. -/
theorem hasSum_restrictedPartitionCount (M : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (restrictedPartitionCount n M : ℂ) * z ^ n)
      (∏ k ∈ Finset.range M, ((1 : ℂ) - z ^ (k + 1))⁻¹) ∧
    Summable (fun n : ℕ => ‖(restrictedPartitionCount n M : ℂ) * z ^ n‖) := by
  induction M with
  | zero =>
    have hs : HasSum (fun n : ℕ => (restrictedPartitionCount n 0 : ℂ) * z ^ n) 1 := by
      have hs0 := hasSum_single (0 : ℕ) (f := fun n : ℕ => (restrictedPartitionCount n 0 : ℂ) * z ^ n)
        fun n hn => by simp [restrictedPartitionCount_zero_right (Nat.one_le_iff_ne_zero.mpr hn)]
      simpa using hs0
    have hnorm : Summable (fun n : ℕ => ‖(restrictedPartitionCount n 0 : ℂ) * z ^ n‖) := by
      refine (hasSum_single (0 : ℕ)
        (f := fun n : ℕ => ‖(restrictedPartitionCount n 0 : ℂ) * z ^ n‖) fun n hn => ?_).summable
      simp [restrictedPartitionCount_zero_right (Nat.one_le_iff_ne_zero.mpr hn)]
    exact ⟨by simpa using hs, hnorm⟩
  | succ M ih =>
    obtain ⟨ih_sum, ih_norm⟩ := ih
    let g : ℕ → ℂ := fun b => (if M + 1 ∣ b then (1 : ℂ) else 0) * z ^ b
    have hg_norm : Summable fun b : ℕ => ‖g b‖ := by
      have hgeom : Summable fun b : ℕ => ‖z‖ ^ b := summable_geometric_of_lt_one (norm_nonneg _) hz
      refine hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) fun b => ?_
      dsimp [g]
      rw [norm_mul, norm_pow]
      split_ifs
      · simp
      · simp [pow_nonneg (norm_nonneg z)]
    have hg_sum : HasSum g ((1 : ℂ) - z ^ (M + 1))⁻¹ := by
      have hpow : ‖z ^ (M + 1)‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (Nat.succ_ne_zero M)
      have hgeom : HasSum (fun j : ℕ => (z ^ (M + 1)) ^ j) ((1 : ℂ) - z ^ (M + 1))⁻¹ :=
        hasSum_geometric_of_norm_lt_one hpow
      refine (Function.Injective.hasSum_iff (g := fun j : ℕ => (M + 1) * j) (f := g) ?_ ?_).mp ?_
      · intro a b hab
        exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos M) hab
      · intro b hb
        simp only [Set.mem_range, not_exists] at hb
        have hnot : ¬ M + 1 ∣ b := fun ⟨j, hj⟩ => hb j hj.symm
        simp [g, hnot]
      · refine hgeom.congr_fun fun j => ?_
        simp [g, pow_mul]
    have hmul := hasSum_sum_range_mul_of_summable_norm ih_norm hg_norm
    have hmul_norm := summable_norm_sum_mul_range_of_summable_norm ih_norm hg_norm
    have heq_fn : (fun n : ℕ => ∑ a ∈ Finset.range (n + 1),
        ((restrictedPartitionCount a M : ℂ) * z ^ a) * g (n - a)) =
        (fun n : ℕ => (restrictedPartitionCount n (M + 1) : ℂ) * z ^ n) := by
      ext n
      calc ∑ a ∈ Finset.range (n + 1),
            ((restrictedPartitionCount a M : ℂ) * z ^ a) * g (n - a)
          = ∑ a ∈ Finset.range (n + 1),
              ((restrictedPartitionCount a M * (if M + 1 ∣ n - a then 1 else 0) : ℕ) : ℂ) *
                z ^ n := by
            refine Finset.sum_congr rfl fun a ha => ?_
            have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            dsimp [g]
            split_ifs with hdvd
            · push_cast
              rw [one_mul, mul_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' han]
            · simp
        _ = (restrictedPartitionCount n (M + 1) : ℂ) * z ^ n := by
            rw [← Finset.sum_mul, ← Nat.cast_sum, restrictedPartitionCount_succ_eq_sum_dvd]
    have hmul' : HasSum (fun n : ℕ => (restrictedPartitionCount n (M + 1) : ℂ) * z ^ n)
        ((∑' n : ℕ, (restrictedPartitionCount n M : ℂ) * z ^ n) * ∑' n : ℕ, g n) :=
      heq_fn ▸ hmul
    have hmul_norm' : Summable fun n : ℕ => ‖(restrictedPartitionCount n (M + 1) : ℂ) * z ^ n‖ := by
      refine hmul_norm.congr fun n => ?_
      exact congrArg norm (congrFun heq_fn n)
    rw [ih_sum.tsum_eq, hg_sum.tsum_eq] at hmul'
    rw [Finset.prod_range_succ]
    exact ⟨hmul', hmul_norm'⟩

/-- Absolute summability of `∑' n, (partitionCount n : ℝ) * r ^ n` for `0 ≤ r < 1`. -/
theorem summable_partitionCount_mul_pow_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => (partitionCount n : ℝ) * r ^ n := by
  have hrC : ‖(r : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range N, (partitionCount n : ℝ) * r ^ n ≤
      (∏' k : ℕ, ((1 : ℝ) - r ^ (k + 1)))⁻¹ := by
    intro N
    obtain ⟨hsum, _⟩ := hasSum_restrictedPartitionCount N hrC
    have hsumR : HasSum (fun n : ℕ => (restrictedPartitionCount n N : ℝ) * r ^ n)
        (∏ k ∈ Finset.range N, ((1 : ℝ) - r ^ (k + 1))⁻¹) := by
      have hprodC : (∏ k ∈ Finset.range N, ((1 : ℂ) - (r : ℂ) ^ (k + 1))⁻¹) =
          ((∏ k ∈ Finset.range N, ((1 : ℝ) - r ^ (k + 1))⁻¹ : ℝ) : ℂ) := by
        simp only [Complex.ofReal_prod, Complex.ofReal_inv, Complex.ofReal_sub,
          Complex.ofReal_one, Complex.ofReal_pow]
      rw [hprodC] at hsum
      have hc := (Complex.continuous_re.tendsto _).comp hsum
      rw [Complex.ofReal_re] at hc
      exact hc.congr fun s => by
        simp only [Function.comp_apply, Complex.re_sum, ← Complex.ofReal_natCast,
          ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hle1 : ∑ n ∈ Finset.range N, (partitionCount n : ℝ) * r ^ n =
        ∑ n ∈ Finset.range N, (restrictedPartitionCount n N : ℝ) * r ^ n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnN : n ≤ N := (Finset.mem_range.mp hn).le
      rw [restrictedPartitionCount_eq_of_le hnN]
    have hle2 : ∑ n ∈ Finset.range N, (restrictedPartitionCount n N : ℝ) * r ^ n ≤
        ∏ k ∈ Finset.range N, ((1 : ℝ) - r ^ (k + 1))⁻¹ := by
      exact hsumR.summable.sum_le_tsum (Finset.range N)
        (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 n)) |>.trans_eq hsumR.tsum_eq
    have hle3 : ∏ k ∈ Finset.range N, ((1 : ℝ) - r ^ (k + 1))⁻¹ ≤
        (∏' k : ℕ, ((1 : ℝ) - r ^ (k + 1)))⁻¹ := by
      have hm := multipliable_one_sub_pow_real (by rwa [abs_of_nonneg hr0])
      have hpos : 0 < ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 1)) := by
        have hne := tprod_one_sub_pow_real_ne_zero (by rwa [abs_of_nonneg hr0])
        have hnonneg : 0 ≤ ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 1)) := by
          refine ge_of_tendsto hm.hasProd (Eventually.of_forall fun s => Finset.prod_nonneg fun k _ => ?_)
          have : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr0 hr1.le
          linarith
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      have hprod_le : ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 1)) ≤
          ∏ k ∈ Finset.range N, ((1 : ℝ) - r ^ (k + 1)) := by
        refine le_of_tendsto hm.hasProd ?_
        refine Filter.eventually_atTop.mpr ⟨Finset.range N, fun s hs => ?_⟩
        rw [← Finset.prod_sdiff hs]
        have htail : ∏ k ∈ s \ Finset.range N, ((1 : ℝ) - r ^ (k + 1)) ≤ 1 := by
          refine Finset.prod_le_one₀ (fun k _ => ?_) (fun k _ => ?_)
          · have hpow : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr0 hr1.le
            linarith
          · have hpow : 0 ≤ r ^ (k + 1) := pow_nonneg hr0 (k + 1)
            linarith
        have hfront : 0 ≤ ∏ k ∈ Finset.range N, ((1 : ℝ) - r ^ (k + 1)) :=
          Finset.prod_nonneg fun k _ => by have hpow : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr0 hr1.le; linarith
        calc (∏ k ∈ s \ Finset.range N, (1 - r ^ (k + 1))) *
              ∏ k ∈ Finset.range N, (1 - r ^ (k + 1))
            ≤ 1 * ∏ k ∈ Finset.range N, (1 - r ^ (k + 1)) :=
              mul_le_mul_of_nonneg_right htail hfront
          _ = ∏ k ∈ Finset.range N, (1 - r ^ (k + 1)) := one_mul _
      rw [Finset.prod_inv_distrib]
      exact inv_anti₀ hpos hprod_le
    exact hle1.le.trans (hle2.trans hle3)
  exact summable_of_sum_range_le (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 n)) hbound

/-- Absolute summability of `∑' n, (partitionCount n : ℂ) * z ^ n` for `‖z‖ < 1`. -/
theorem summable_norm_partitionCount_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖(partitionCount n : ℂ) * z ^ n‖ := by
  have hs := summable_partitionCount_mul_pow_real (norm_nonneg z) hz
  simpa [norm_mul, norm_pow] using hs

/-- Summability of `fun n => (partitionCount n : ℂ) * z ^ n` for `‖z‖ < 1`. -/
theorem summable_partitionCount_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (partitionCount n : ℂ) * z ^ n :=
  (summable_norm_partitionCount_mul_pow hz).of_norm

/-- **Partition Generating Function Identity** (`ℂ` version):
for `‖z‖ < 1`, `HasSum (fun n => (partitionCount n : ℂ) * z ^ n) ((∏' k, (1 - z ^ (k + 1)))⁻¹)`. -/
theorem hasSum_partitionCount_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (partitionCount n : ℂ) * z ^ n) (partitionGenFun z) := by
  have hs := summable_partitionCount_mul_pow hz
  suffices h : ∑' n : ℕ, (partitionCount n : ℂ) * z ^ n = partitionGenFun z by
    rw [← h]; exact hs.hasSum
  have hprod : Tendsto (fun M : ℕ => ∏ k ∈ Finset.range M, ((1 : ℂ) - z ^ (k + 1))⁻¹)
      atTop (𝓝 (partitionGenFun z)) :=
    (partitionGenFun_eq_tprod_inv hz).tendsto_prod_nat
  have hsum_tendsto :
      Tendsto (fun M : ℕ => ∑' n : ℕ, (restrictedPartitionCount n M : ℂ) * z ^ n)
        atTop (𝓝 (∑' n : ℕ, (partitionCount n : ℂ) * z ^ n)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hsR := summable_partitionCount_mul_pow_real (norm_nonneg z) hz
    have htail_lim : Tendsto (fun M : ℕ =>
        (∑' n : ℕ, (partitionCount n : ℝ) * ‖z‖ ^ n) -
          ∑ n ∈ Finset.range M, (partitionCount n : ℝ) * ‖z‖ ^ n) atTop (𝓝 0) := by
      have hpart : Tendsto (fun M : ℕ =>
          ∑ n ∈ Finset.range M, (partitionCount n : ℝ) * ‖z‖ ^ n)
          atTop (𝓝 (∑' n : ℕ, (partitionCount n : ℝ) * ‖z‖ ^ n)) :=
        hsR.hasSum.tendsto_sum_nat
      simpa [sub_self] using (tendsto_const_nhds (x := ∑' n : ℕ, (partitionCount n : ℝ) * ‖z‖ ^ n)).sub hpart
    obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp htail_lim) ε hε
    refine ⟨M₀, fun M hM => ?_⟩
    obtain ⟨hM_sum, hM_norm⟩ := hasSum_restrictedPartitionCount M hz
    have hM_summable : Summable fun n : ℕ => (restrictedPartitionCount n M : ℂ) * z ^ n :=
      hM_sum.summable
    have hdiff :
        (∑' n : ℕ, (restrictedPartitionCount n M : ℂ) * z ^ n) -
          (∑' n : ℕ, (partitionCount n : ℂ) * z ^ n) =
        ∑' n : ℕ, ((restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)) * z ^ n := by
      rw [← hM_summable.tsum_sub hs]
      refine tsum_congr fun n => by ring
    rw [dist_eq_norm, hdiff]
    have hnorm_sum :
        ‖∑' n : ℕ, ((restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)) * z ^ n‖ ≤
          ∑' n : ℕ, (if M ≤ n then (partitionCount n : ℝ) * ‖z‖ ^ n else 0) := by
      have hterm_le : ∀ n : ℕ,
          ‖((restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)) * z ^ n‖ ≤
            (if M ≤ n then (partitionCount n : ℝ) * ‖z‖ ^ n else 0) := by
        intro n
        by_cases hnM : M ≤ n
        · simp only [hnM, ↓reduceIte, norm_mul, norm_pow]
          have hsub_le : ‖(restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)‖ ≤
              (partitionCount n : ℝ) := by
            have hleR : (restrictedPartitionCount n M : ℝ) ≤ partitionCount n := by
              exact_mod_cast restrictedPartitionCount_le n M
            have hcast : ((restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)) =
                (((restrictedPartitionCount n M : ℝ) - partitionCount n : ℝ) : ℂ) := by
              norm_cast
            rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hleR)]
            have h0 : (0 : ℝ) ≤ restrictedPartitionCount n M := Nat.cast_nonneg _
            linarith
          exact mul_le_mul_of_nonneg_right hsub_le (pow_nonneg (norm_nonneg _) _)
        · have hn_lt : n ≤ M := by omega
          simp only [hnM, ↓reduceIte]
          rw [restrictedPartitionCount_eq_of_le hn_lt]
          simp
      have hs_ite : Summable fun n : ℕ => if M ≤ n then (partitionCount n : ℝ) * ‖z‖ ^ n else 0 :=
        hsR.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
          (fun n => by split_ifs; exact le_rfl; positivity)
      have hs_diff_norm :
          Summable fun n : ℕ => ‖((restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)) * z ^ n‖ :=
        hs_ite.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le
      calc ‖∑' n : ℕ, ((restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)) * z ^ n‖
          ≤ ∑' n : ℕ, ‖((restrictedPartitionCount n M : ℂ) - (partitionCount n : ℂ)) * z ^ n‖ :=
            norm_tsum_le_tsum_norm hs_diff_norm
        _ ≤ ∑' n : ℕ, (if M ≤ n then (partitionCount n : ℝ) * ‖z‖ ^ n else 0) :=
            hs_diff_norm.tsum_le_tsum hterm_le hs_ite
    have htail_eq :
        ∑' n : ℕ, (if M ≤ n then (partitionCount n : ℝ) * ‖z‖ ^ n else 0) =
          (∑' n : ℕ, (partitionCount n : ℝ) * ‖z‖ ^ n) -
            ∑ n ∈ Finset.range M, (partitionCount n : ℝ) * ‖z‖ ^ n := by
      have hsum_add := hsR.sum_add_tsum_nat_add M
      have hite_shift :
          ∑' n : ℕ, (if M ≤ n then (partitionCount n : ℝ) * ‖z‖ ^ n else 0) =
            ∑' n : ℕ, (partitionCount (n + M) : ℝ) * ‖z‖ ^ (n + M) := by
        have h1 : ∀ n : ℕ, (if M ≤ n + M then (partitionCount (n + M) : ℝ) * ‖z‖ ^ (n + M) else 0) =
            (partitionCount (n + M) : ℝ) * ‖z‖ ^ (n + M) := fun n => by
          simp only [Nat.le_add_left M n, ↓reduceIte]
        have hinj : Function.Injective (fun n : ℕ => n + M) := fun a b h => Nat.add_right_cancel h
        have hsupp : Function.support (fun n : ℕ =>
            if M ≤ n then (partitionCount n : ℝ) * ‖z‖ ^ n else 0) ⊆
              Set.range (fun k : ℕ => k + M) := by
          intro n hn
          rw [Function.mem_support] at hn
          by_cases hle : M ≤ n
          · exact ⟨n - M, Nat.sub_add_cancel hle⟩
          · simp [hle] at hn
        have heq := (Function.Injective.tsum_eq hinj hsupp).symm
        simpa [h1] using heq
      rw [hite_shift]
      linarith
    have hM_dist := hM₀ M hM
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by
      have := hsR.sum_le_tsum (Finset.range M) (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg z) n))
      linarith)] at hM_dist
    linarith
  have heq_seq : (fun M : ℕ => ∑' n : ℕ, (restrictedPartitionCount n M : ℂ) * z ^ n) =
      (fun M : ℕ => ∏ k ∈ Finset.range M, ((1 : ℂ) - z ^ (k + 1))⁻¹) := by
    ext M
    exact (hasSum_restrictedPartitionCount M hz).1.tsum_eq
  rw [heq_seq] at hsum_tendsto
  exact tendsto_nhds_unique hsum_tendsto hprod

/-- **Partition Generating Function Identity** (`ℂ` `tsum` form):
for `‖z‖ < 1`, `∑' n, (partitionCount n : ℂ) * z ^ n = (∏' k, (1 - z ^ (k + 1)))⁻¹`. -/
theorem tsum_partitionCount_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' n : ℕ, (partitionCount n : ℂ) * z ^ n = (∏' k : ℕ, ((1 : ℂ) - z ^ (k + 1)))⁻¹ :=
  (hasSum_partitionCount_mul_pow hz).tsum_eq

/-- **Partition Generating Function Identity** (`ℝ` `HasSum` form):
for `|x| < 1`, `HasSum (fun n => (partitionCount n : ℝ) * x ^ n) ((∏' k, (1 - x ^ (k + 1)))⁻¹)`. -/
theorem hasSum_partitionCount_mul_pow_real {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (partitionCount n : ℝ) * x ^ n) (partitionGenFunReal x) := by
  have hxC : ‖(x : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hsum := hasSum_partitionCount_mul_pow hxC
  rw [partitionGenFun_ofReal hx] at hsum
  have hc := (Complex.continuous_re.tendsto _).comp hsum
  rw [Complex.ofReal_re] at hc
  exact hc.congr fun s => by
    simp only [Function.comp_apply, Complex.re_sum, ← Complex.ofReal_natCast,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Partition Generating Function Identity** (`ℝ` `tsum` form):
for `|x| < 1`, `∑' n, (partitionCount n : ℝ) * x ^ n = (∏' k, (1 - x ^ (k + 1)))⁻¹`. -/
theorem tsum_partitionCount_mul_pow_real {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, (partitionCount n : ℝ) * x ^ n = (∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)))⁻¹ :=
  (hasSum_partitionCount_mul_pow_real hx).tsum_eq

end GeneratingFunction

section JacobiTripleProductAndPentagonal

/-- Finite `q`-Pochhammer product `∏_{i=0}^{n-1} (1 - q ^ (i + 1))`. -/
def qProd (q : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ Finset.range n, ((1 : ℂ) - q ^ (i + 1))

/-- Gaussian `q`-binomial coefficient `[N choose j]_q`. -/
def qBinom (q : ℂ) (N j : ℕ) : ℂ :=
  if j ≤ N then qProd q N / (qProd q j * qProd q (N - j)) else 0

private lemma qProd_zero (q : ℂ) : qProd q 0 = 1 := by simp [qProd]

private lemma qProd_succ (q : ℂ) (n : ℕ) : qProd q (n + 1) = qProd q n * (1 - q ^ (n + 1)) := by
  simp [qProd, Finset.prod_range_succ]

private lemma qProd_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) : qProd q n ≠ 0 := by
  induction n with
  | zero => simp [qProd]
  | succ m ih =>
    rw [qProd_succ]
    refine mul_ne_zero ih ?_
    intro h0
    have h1 : q ^ (m + 1) = 1 := by linear_combination -h0
    have hnorm : ‖q‖ ^ (m + 1) = 1 := by simpa [norm_pow] using congrArg norm h1
    have hlt : ‖q‖ ^ (m + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero m)
    linarith

private lemma qBinom_zero_right {q : ℂ} (hq : ‖q‖ < 1) (N : ℕ) : qBinom q N 0 = 1 := by
  simp [qBinom, qProd_zero, div_self (qProd_ne_zero hq N)]

private lemma qBinom_self {q : ℂ} (hq : ‖q‖ < 1) (N : ℕ) : qBinom q N N = 1 := by
  simp [qBinom, qProd_zero, div_self (qProd_ne_zero hq N)]

private lemma qBinom_gt {q : ℂ} (N j : ℕ) (hj : N < j) : qBinom q N j = 0 := by
  simp [qBinom, not_le.mpr hj]

private lemma qBinom_succ_succ_right {q : ℂ} (hq : ‖q‖ < 1) {N j : ℕ} (hj : j ≤ N) :
    qBinom q (N + 1) (j + 1) = qBinom q N (j + 1) + q ^ (N - j) * qBinom q N j := by
  rcases eq_or_lt_of_le hj with rfl | hjlt
  · simp [qBinom_self hq, qBinom_gt _ _ (Nat.lt_succ_self _)]
  · have hj1 : j + 1 ≤ N := hjlt
    have hN1 : j + 1 ≤ N + 1 := by omega
    have hsub : N + 1 - (j + 1) = N - j := by omega
    have hsub' : N - j = (N - (j + 1)) + 1 := by omega
    simp only [qBinom, hN1, hj1, hj, ↓reduceIte, hsub]
    have hP1 := qProd_ne_zero hq N
    have hP2 := qProd_ne_zero hq (j + 1)
    have hP3 := qProd_ne_zero hq (N - j)
    have hP4 := qProd_ne_zero hq j
    have hP5 := qProd_ne_zero hq (N - (j + 1))
    have hqN : qProd q (N + 1) = qProd q N * (1 - q ^ (N + 1)) := qProd_succ q N
    have hqj : qProd q (j + 1) = qProd q j * (1 - q ^ (j + 1)) := qProd_succ q j
    have hqNj : qProd q (N - j) = qProd q (N - (j + 1)) * (1 - q ^ (N - j)) := by
      conv_lhs => rw [hsub', qProd_succ]
      rw [← hsub']
    rw [hqN]
    field_simp [hP1, hP2, hP3, hP4, hP5]
    rw [hqj, hqNj]
    have hexp : q ^ (j + 1) * q ^ (N - j) = q ^ (N + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [← hexp]
    ring

/-- Finite `q`-binomial theorem: for `‖q‖ < 1` and `z : ℂ`,
`∏ k ∈ range N, (1 + z * q ^ k) = ∑ j ∈ range (N + 1), qBinom q N j * q ^ (j * (j - 1) / 2) * z ^ j`. -/
theorem prod_range_one_add_mul_pow {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) (N : ℕ) :
    ∏ k ∈ Finset.range N, (1 + z * q ^ k) =
      ∑ j ∈ Finset.range (N + 1), qBinom q N j * q ^ (j * (j - 1) / 2) * z ^ j := by
  induction N with
  | zero => simp [qBinom_zero_right hq]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, mul_add, mul_one, mul_comm _ (z * q ^ N)]
    have h1 :
        ∑ j ∈ Finset.range (N + 1), qBinom q N j * q ^ (j * (j - 1) / 2) * z ^ j =
          qBinom q N 0 * q ^ 0 * z ^ 0 +
            ∑ j ∈ Finset.range N, qBinom q N (j + 1) * q ^ ((j + 1) * j / 2) * z ^ (j + 1) := by
      rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos N), Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    have h2 :
        z * q ^ N *
            ∑ j ∈ Finset.range (N + 1), qBinom q N j * q ^ (j * (j - 1) / 2) * z ^ j =
          ∑ j ∈ Finset.range N,
            (q ^ (N - j) * qBinom q N j) * q ^ ((j + 1) * j / 2) * z ^ (j + 1) +
              qBinom q N N * q ^ ((N + 1) * N / 2) * z ^ (N + 1) := by
      rw [Finset.mul_sum, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hjN : j ≤ N := (Finset.mem_range.mp hj).le
        have hexp : j * (j - 1) / 2 + N = (j + 1) * j / 2 + (N - j) := by
          rcases j with _ | j
          · simp
          · have hdiv : (j + 1 + 1) * (j + 1) / 2 = (j + 1) * j / 2 + (j + 1) := by
              rw [show (j + 1 + 1) * (j + 1) = (j + 1) * j + 2 * (j + 1) by ring,
                  Nat.add_mul_div_left _ _ (by norm_num)]
            simp only [Nat.add_sub_cancel]
            omega
        calc z * q ^ N * (qBinom q N j * q ^ (j * (j - 1) / 2) * z ^ j)
            = qBinom q N j * (q ^ (j * (j - 1) / 2 + N)) * (z ^ (j + 1)) := by
              rw [pow_add, pow_succ']; ring
          _ = qBinom q N j * (q ^ ((j + 1) * j / 2 + (N - j))) * z ^ (j + 1) := by rw [hexp]
          _ = (q ^ (N - j) * qBinom q N j) * q ^ ((j + 1) * j / 2) * z ^ (j + 1) := by
              rw [pow_add]; ring
      · have hexp : N * (N - 1) / 2 + N = (N + 1) * N / 2 := by
          rcases N with _ | N
          · simp
          · have hid : (N + 2) * (N + 1) = (N + 1) * N + 2 * (N + 1) := by ring
            rw [Nat.add_sub_cancel, hid, Nat.add_mul_div_left _ _ (by norm_num)]
        calc z * q ^ N * (qBinom q N N * q ^ (N * (N - 1) / 2) * z ^ N)
            = qBinom q N N * q ^ (N * (N - 1) / 2 + N) * z ^ (N + 1) := by
              rw [pow_add, pow_succ']; ring
          _ = qBinom q N N * q ^ ((N + 1) * N / 2) * z ^ (N + 1) := by rw [hexp]
    have hsplit_rhs :
        ∑ j ∈ Finset.range (N + 2), qBinom q (N + 1) j * q ^ (j * (j - 1) / 2) * z ^ j =
          qBinom q (N + 1) 0 * q ^ 0 * z ^ 0 +
            ∑ j ∈ Finset.range N,
              qBinom q (N + 1) (j + 1) * q ^ ((j + 1) * j / 2) * z ^ (j + 1) +
            qBinom q (N + 1) (N + 1) * q ^ ((N + 1) * N / 2) * z ^ (N + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ (Nat.succ_pos N),
          Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    rw [h2, h1, hsplit_rhs]
    have hmid :
        (∑ j ∈ Finset.range N, qBinom q N (j + 1) * q ^ ((j + 1) * j / 2) * z ^ (j + 1)) +
          ∑ j ∈ Finset.range N,
            (q ^ (N - j) * qBinom q N j) * q ^ ((j + 1) * j / 2) * z ^ (j + 1) =
        ∑ j ∈ Finset.range N,
          qBinom q (N + 1) (j + 1) * q ^ ((j + 1) * j / 2) * z ^ (j + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N := (Finset.mem_range.mp hj).le
      rw [qBinom_succ_succ_right hq hjN]
      ring
    rw [qBinom_zero_right hq, qBinom_zero_right hq, qBinom_self hq, qBinom_self hq]
    linear_combination hmid

/-- Finite Jacobi triple product identity for `M : ℕ`, `q ≠ 0`, `‖q‖ < 1`, `x ≠ 0`. -/
private lemma finite_jacobi_triple_product {q x : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (hx : x ≠ 0)
    (M : ℕ) :
    qProd (q ^ 2) M *
        ∏ m ∈ Finset.range M, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)) =
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (qProd (q ^ 2) M * qBinom (q ^ 2) (2 * M) (M + k).toNat) *
          q ^ (k.natAbs ^ 2) * x ^ k := by
  have hq2_norm : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [qProd_zero, qBinom_zero_right hq2_norm]
  let z : ℂ := x * (q ^ (2 * M - 1))⁻¹
  have hqbin := prod_range_one_add_mul_pow hq2_norm z (2 * M)
  have hlhs :
      ∏ k ∈ Finset.range (2 * M), (1 + z * (q ^ 2) ^ k) =
        x ^ M * (q ^ (M ^ 2))⁻¹ *
          ∏ m ∈ Finset.range M, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)) := by
    have hsplit : Finset.range (2 * M) = Finset.range M ∪ Finset.Ico M (2 * M) := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range M) (Finset.Ico M (2 * M)) := by
      rw [Finset.disjoint_left]; intro k h1 h2
      rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
    rw [hsplit, Finset.prod_union hdisj]
    have hhi : ∏ k ∈ Finset.Ico M (2 * M), (1 + z * (q ^ 2) ^ k) =
        ∏ m ∈ Finset.range M, (1 + x * q ^ (2 * m + 1)) := by
      refine Finset.prod_bij (fun k hk => k - M) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Ico] at hk; exact Finset.mem_range.mpr (by omega)
      · intro a ha b hb heq; rw [Finset.mem_Ico] at ha hb; omega
      · intro m hm; rw [Finset.mem_range] at hm
        exact ⟨M + m, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        rw [Finset.mem_Ico] at hk
        have hqpow : (q ^ (2 * M - 1))⁻¹ * (q ^ 2) ^ k = q ^ (2 * (k - M) + 1) := by
          have hpow_ne : q ^ (2 * M - 1) ≠ 0 := pow_ne_zero _ hq0
          rw [← pow_mul, inv_mul_eq_iff_eq_mul₀ hpow_ne, ← pow_add]
          congr 1
          omega
        simp only [z, mul_assoc, hqpow]
    have hlo : ∏ k ∈ Finset.range M, (1 + z * (q ^ 2) ^ k) =
        x ^ M * (q ^ (M ^ 2))⁻¹ * ∏ m ∈ Finset.range M, (1 + x⁻¹ * q ^ (2 * m + 1)) := by
      have hterm : ∀ m ∈ Finset.range M,
          (1 + z * (q ^ 2) ^ (M - 1 - m)) =
            (x * (q ^ (2 * m + 1))⁻¹) * (1 + x⁻¹ * q ^ (2 * m + 1)) := by
        intro m hm
        rw [Finset.mem_range] at hm
        have hqpow : z * (q ^ 2) ^ (M - 1 - m) = x * (q ^ (2 * m + 1))⁻¹ := by
          dsimp [z]
          have h1 : (q ^ 2) ^ (M - 1 - m) = q ^ (2 * (M - 1 - m)) := by rw [← pow_mul]
          rw [h1, mul_assoc]
          congr 1
          have hne1 : q ^ (2 * M - 1) ≠ 0 := pow_ne_zero _ hq0
          have hne2 : q ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ hq0
          rw [inv_mul_eq_iff_eq_mul₀ hne1, eq_mul_inv_iff_mul_eq₀ hne2, ← pow_add]
          congr 1
          omega
        rw [hqpow]
        have hq2 : q ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ hq0
        field_simp [hx, hq2]
        ring
      have hrev : ∏ k ∈ Finset.range M, (1 + z * (q ^ 2) ^ k) =
          ∏ m ∈ Finset.range M, (1 + z * (q ^ 2) ^ (M - 1 - m)) := by
        refine Finset.prod_bij (fun k _ => M - 1 - k) ?_ ?_ ?_ ?_
        · intro k hk; rw [Finset.mem_range] at hk ⊢; omega
        · intro a ha b hb heq; rw [Finset.mem_range] at ha hb; omega
        · intro m hm; rw [Finset.mem_range] at hm
          exact ⟨M - 1 - m, Finset.mem_range.mpr (by omega), by omega⟩
        · intro k hk; rw [Finset.mem_range] at hk; congr 3; omega
      rw [hrev, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.card_range, Finset.prod_inv_distrib]
      have hqsum : ∏ m ∈ Finset.range M, q ^ (2 * m + 1) = q ^ (M ^ 2) := by
        have hsum_odd : ∀ K : ℕ, ∑ m ∈ Finset.range K, (2 * m + 1) = K ^ 2 := by
          intro K
          induction K with
          | zero => simp
          | succ n ihn => rw [Finset.sum_range_succ, ihn]; ring
        rw [Finset.prod_pow_eq_pow_sum, hsum_odd M]
      rw [hqsum]
    rw [hlo, hhi, Finset.prod_mul_distrib]
    ring
  have hrhs :
      ∑ j ∈ Finset.range (2 * M + 1), qBinom (q ^ 2) (2 * M) j * (q ^ 2) ^ (j * (j - 1) / 2) * z ^ j =
        x ^ M * (q ^ (M ^ 2))⁻¹ *
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            qBinom (q ^ 2) (2 * M) (M + k).toNat * q ^ (k.natAbs ^ 2) * x ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => (j : ℤ) - M) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]
      omega
    · intro a _ b _ heq
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      refine ⟨(M + k).toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      rw [Finset.mem_range] at hj
      have hj_toNat : (M + ((j : ℤ) - M)).toNat = j := by omega
      rw [hj_toNat]
      have hqpow : (q ^ 2) ^ (j * (j - 1) / 2) * ((q ^ (2 * M - 1))⁻¹) ^ j =
          (q ^ (M ^ 2))⁻¹ * q ^ (((j : ℤ) - M).natAbs ^ 2) := by
        have h1 : (q ^ 2) ^ (j * (j - 1) / 2) = q ^ (j * (j - 1)) := by
          rw [← pow_mul]
          congr 1
          have hdvd : 2 ∣ j * (j - 1) := by
            rcases j with _ | j
            · simp
            · simpa [Nat.add_sub_cancel, mul_comm] using Nat.even_mul_succ_self j |>.two_dvd
          omega
        rw [h1, inv_pow, ← pow_mul]
        have hne1 : q ^ ((2 * M - 1) * j) ≠ 0 := pow_ne_zero _ hq0
        have hne2 : q ^ (M ^ 2) ≠ 0 := pow_ne_zero _ hq0
        rw [mul_inv_eq_iff_eq_mul₀ hne1, mul_assoc ((q ^ (M ^ 2))⁻¹), eq_inv_mul_iff_mul_eq₀ hne2, ← pow_add, ← pow_add]
        congr 1
        have hnat : |((j : ℤ) - M)| ^ 2 = ((j : ℤ) - M) ^ 2 := sq_abs _
        have hj_eq : (j : ℤ) * ((j - 1 : ℕ) : ℤ) = (j : ℤ) * ((j : ℤ) - 1) := by
          rcases j with _ | j
          · simp
          · push_cast; ring
        have hM_eq : ((2 * M - 1 : ℕ) : ℤ) = 2 * (M : ℤ) - 1 := by
          have : 1 ≤ 2 * M := by omega
          omega
        have hnat_eq : M ^ 2 + j * (j - 1) = ((j : ℤ) - M).natAbs ^ 2 + (2 * M - 1) * j := by
          have hz : ((M ^ 2 + j * (j - 1) : ℕ) : ℤ) =
              ((((j : ℤ) - M).natAbs ^ 2 + (2 * M - 1) * j : ℕ) : ℤ) := by
            push_cast
            rw [hnat, hj_eq, hM_eq]
            ring
          exact Int.ofNat.inj hz
        exact hnat_eq
      have hxpow : x ^ M * x ^ ((j : ℤ) - M) = x ^ (j : ℤ) := by
        rw [← zpow_natCast x M, ← zpow_add₀ hx]
        congr 1
        omega
      calc qBinom (q ^ 2) (2 * M) j * (q ^ 2) ^ (j * (j - 1) / 2) * z ^ j
          = qBinom (q ^ 2) (2 * M) j * ((q ^ 2) ^ (j * (j - 1) / 2) * ((q ^ (2 * M - 1))⁻¹) ^ j) *
              x ^ j := by
            dsimp [z]; rw [mul_pow]; ring
        _ = qBinom (q ^ 2) (2 * M) j * ((q ^ (M ^ 2))⁻¹ * q ^ (((j : ℤ) - M).natAbs ^ 2)) *
              (x ^ M * x ^ ((j : ℤ) - M)) := by
            rw [hqpow, ← zpow_natCast x j, hxpow]
        _ = x ^ M * (q ^ (M ^ 2))⁻¹ *
              (qBinom (q ^ 2) (2 * M) j * q ^ (((j : ℤ) - M).natAbs ^ 2) * x ^ ((j : ℤ) - M)) := by
            ring
  rw [hlhs, hrhs] at hqbin
  have hcancel : x ^ M * (q ^ (M ^ 2))⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hx) (inv_ne_zero (pow_ne_zero _ hq0))
  have hprod_eq := mul_left_cancel₀ hcancel hqbin
  have hfinal := congrArg (qProd (q ^ 2) M * ·) hprod_eq
  rw [Finset.mul_sum] at hfinal
  refine hfinal.trans (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-- **Jacobi's Triple Product Identity**:
for `q, x ∈ ℂ` with `q ≠ 0`, `‖q‖ < 1`, and `x ≠ 0`,
`(∏' m, (1 - q ^ (2 * (m + 1)))) * ∏' m, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)) = ∑' k : ℤ, q ^ (k.natAbs ^ 2) * x ^ k`. -/
theorem jacobi_triple_product {q x : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (hx : x ≠ 0) :
    (∏' m : ℕ, ((1 : ℂ) - q ^ (2 * (m + 1)))) *
        (∏' m : ℕ, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1))) =
      ∑' k : ℤ, q ^ (k.natAbs ^ 2) * x ^ k := by
  have hq2_norm : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  have hm1 : Multipliable fun m : ℕ => (1 : ℂ) - q ^ (2 * (m + 1)) := by
    simpa [pow_mul] using multipliable_one_sub_pow hq2_norm
  have hm2 : Multipliable fun m : ℕ => (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)) := by
    have hsum : Summable fun m : ℕ =>
        ‖(x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)‖ := by
      have hq_sq : ‖q‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg q) hq1 (by norm_num)
      have hgeom1 : Summable fun m : ℕ => ‖q‖ ^ (2 * m + 1) := by
        have hg := summable_geometric_of_lt_one (sq_nonneg ‖q‖) hq_sq
        simpa [pow_succ, pow_mul] using hg.mul_right ‖q‖
      have hgeom2 : Summable fun m : ℕ => ‖q‖ ^ (4 * m + 2) := by
        have hg := summable_geometric_of_lt_one (sq_nonneg ‖q‖) hq_sq
        refine hg.of_nonneg_of_le (fun _ => pow_nonneg (norm_nonneg _) _) fun m => ?_
        have hle : 2 * m ≤ 4 * m + 2 := by omega
        simpa [pow_mul] using pow_le_pow_of_le_one (norm_nonneg q) hq1.le hle
      refine (hgeom1.mul_left ‖x + x⁻¹‖ |>.add hgeom2).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
      calc ‖(x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)‖
          ≤ ‖(x + x⁻¹) * q ^ (2 * m + 1)‖ + ‖q ^ (4 * m + 2)‖ := norm_add_le _ _
        _ = ‖x + x⁻¹‖ * ‖q‖ ^ (2 * m + 1) + ‖q‖ ^ (4 * m + 2) := by simp [norm_pow]
    have heq : ∀ m : ℕ, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)) =
        1 + ((x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)) := by
      intro m
      have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
      have hqpow : q ^ (2 * m + 1) * q ^ (2 * m + 1) = q ^ (4 * m + 2) := by
        rw [← pow_add]; congr 1; omega
      calc (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1))
          = 1 + (x + x⁻¹) * q ^ (2 * m + 1) + (x * x⁻¹) * (q ^ (2 * m + 1) * q ^ (2 * m + 1)) := by ring
        _ = 1 + ((x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)) := by rw [hxx, one_mul, hqpow]; ring
    simp_rw [heq]
    exact AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm hsum
  have hlhs_tend :
      Tendsto (fun M : ℕ =>
          qProd (q ^ 2) M *
            ∏ m ∈ Finset.range M, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)))
        atTop
        (𝓝 ((∏' m : ℕ, ((1 : ℂ) - q ^ (2 * (m + 1)))) *
          (∏' m : ℕ, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1))))) := by
    have ht1 : Tendsto (fun M : ℕ => qProd (q ^ 2) M) atTop
        (𝓝 (∏' m : ℕ, ((1 : ℂ) - q ^ (2 * (m + 1))))) := by
      have hc := hm1.hasProd.tendsto_prod_nat
      refine hc.congr fun M => ?_
      simp [qProd, pow_mul]
    have ht2 : Tendsto (fun M : ℕ =>
        ∏ m ∈ Finset.range M, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)))
        atTop (𝓝 (∏' m : ℕ, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)))) :=
      hm2.hasProd.tendsto_prod_nat
    exact ht1.mul ht2
  let a : ℤ → ℂ := fun k => q ^ (k.natAbs ^ 2) * x ^ k
  have ha_sum : Summable fun k : ℤ => ‖a k‖ := by
    have hnat : Summable fun k : ℕ => ‖a (k : ℤ)‖ := by
      have hgeom : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have hq_tend : Tendsto (fun k : ℕ => ‖q‖ ^ k * max ‖x‖ ‖x⁻¹‖) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq1).mul_const _
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hq_tend.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2))
      rw [← summable_nat_add_iff (N + 1)]
      refine ((summable_nat_add_iff (N + 1)).mpr hgeom).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
      have hqle : ‖q‖ ^ (k + (N + 1)) * ‖x‖ ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg (norm_nonneg _) _)).trans (hN (k + (N + 1)) (by omega))
      dsimp [a]
      rw [show ((k : ℤ) + ((N : ℤ) + 1)) = ((k + (N + 1) : ℕ) : ℤ) by push_cast; ring,
          norm_mul, norm_pow, zpow_natCast, norm_pow, Int.natAbs_natCast]
      have hpow : ‖q‖ ^ ((k + (N + 1)) ^ 2) * ‖x‖ ^ (k + (N + 1)) = (‖q‖ ^ (k + (N + 1)) * ‖x‖) ^ (k + (N + 1)) := by
        rw [mul_pow, ← pow_mul, sq]
      rw [hpow]
      exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) hqle (k + (N + 1))
    have hneg : Summable fun k : ℕ => ‖a (-((k : ℤ) + 1))‖ := by
      have hgeom : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have hq_tend : Tendsto (fun k : ℕ => ‖q‖ ^ k * max ‖x‖ ‖x⁻¹‖) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq1).mul_const _
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hq_tend.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2))
      rw [← summable_nat_add_iff (N + 1)]
      refine ((summable_nat_add_iff (N + 1)).mpr hgeom).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
      have hqle : ‖q‖ ^ (k + (N + 1) + 1) * ‖x⁻¹‖ ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (pow_nonneg (norm_nonneg _) _)).trans (hN (k + (N + 1) + 1) (by omega))
      dsimp [a]
      have hneg_id : -(↑k + (↑N + 1) + 1 : ℤ) = -((k + (N + 1) + 1 : ℕ) : ℤ) := by
        push_cast; ring
      have hna : (-((k + (N + 1) + 1 : ℕ) : ℤ)).natAbs = k + (N + 1) + 1 := by omega
      rw [hneg_id, hna, norm_mul, norm_pow, zpow_neg, norm_inv, zpow_natCast, norm_pow, ← inv_pow]
      have hpow : ‖q‖ ^ ((k + (N + 1) + 1) ^ 2) * ‖x‖⁻¹ ^ (k + (N + 1) + 1) =
          (‖q‖ ^ (k + (N + 1) + 1) * ‖x⁻¹‖) ^ (k + (N + 1) + 1) := by
        rw [norm_inv, mul_pow, ← pow_mul, sq]
      rw [hpow]
      calc (‖q‖ ^ (k + (N + 1) + 1) * ‖x⁻¹‖) ^ (k + (N + 1) + 1)
          ≤ (1 / 2 : ℝ) ^ (k + (N + 1) + 1) :=
            pow_le_pow_left₀ (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) hqle (k + (N + 1) + 1)
        _ ≤ (1 / 2 : ℝ) ^ (k + (N + 1)) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact Summable.of_nat_of_neg_add_one hnat hneg
  have ha_summable : Summable a := ha_sum.of_norm
  let B₀ : ℝ := ∏' m : ℕ, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1)))
  let B₁ : ℝ := ∏' m : ℕ, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1)))
  have hB₀_pos : 0 < B₀ := by
    have hq2_abs : |‖q‖ ^ 2| < 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [norm_nonneg q]
    have hne := tprod_one_sub_pow_real_ne_zero hq2_abs
    have hm := multipliable_one_sub_pow_real hq2_abs
    have hnonneg : 0 ≤ B₀ := by
      change 0 ≤ ∏' m : ℕ, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1)))
      have hm' : Multipliable fun m : ℕ => ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1))) := by
        simpa [pow_mul] using hm
      refine ge_of_tendsto hm'.hasProd (Eventually.of_forall fun s => Finset.prod_nonneg fun m _ => ?_)
      have hle : (‖q‖ ^ 2) ^ (m + 1) ≤ 1 := pow_le_one₀ (sq_nonneg _) (by nlinarith [norm_nonneg q])
      simpa [pow_mul] using hle
    have hB₀_ne : B₀ ≠ 0 := by simpa [B₀, pow_mul] using hne
    exact lt_of_le_of_ne hnonneg (Ne.symm hB₀_ne)
  have hB₁_pos : 0 < B₁ := by
    have hq_sq : ‖q‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg q) hq1 (by norm_num)
    have hgeom : Summable fun m : ℕ => ‖q‖ ^ (2 * (m + 1)) := by
      have hg := summable_geometric_of_lt_one (sq_nonneg ‖q‖) hq_sq
      exact (hg.mul_right (‖q‖ ^ 2)).congr fun m => by rw [← pow_succ, ← pow_mul]
    have hgeom_norm : Summable fun m : ℕ => ‖‖q‖ ^ (2 * (m + 1))‖ :=
      hgeom.congr fun m => by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    have hm := AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm hgeom_norm
    have hge1 : 1 ≤ B₁ := by
      change 1 ≤ ∏' m : ℕ, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1)))
      refine ge_of_tendsto hm.hasProd (Eventually.of_forall fun s => Finset.one_le_prod₀ fun m _ => ?_)
      linarith [pow_nonneg (norm_nonneg q) (2 * (m + 1))]
    linarith
  have hqProd_lo : ∀ n : ℕ, B₀ ≤ ‖qProd (q ^ 2) n‖ := by
    intro n
    have hq2_abs : |‖q‖ ^ 2| < 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [norm_nonneg q]
    have hm := multipliable_one_sub_pow_real hq2_abs
    have hm' : Multipliable fun m : ℕ => ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1))) := by
      simpa [pow_mul] using hm
    have hB_le : B₀ ≤ ∏ m ∈ Finset.range n, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1))) := by
      change ∏' m : ℕ, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1))) ≤ ∏ m ∈ Finset.range n, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1)))
      refine le_of_tendsto hm'.hasProd (Filter.eventually_atTop.mpr ⟨Finset.range n, fun s hs => ?_⟩)
      rw [← Finset.prod_sdiff hs]
      have htail : ∏ m ∈ s \ Finset.range n, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1))) ≤ 1 := by
        refine Finset.prod_le_one₀ (fun m _ => ?_) (fun m _ => ?_)
        · have hle : ‖q‖ ^ (2 * (m + 1)) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq1.le
          linarith
        · have hnn : 0 ≤ ‖q‖ ^ (2 * (m + 1)) := pow_nonneg (norm_nonneg q) (2 * (m + 1))
          linarith
      have hfront : 0 ≤ ∏ m ∈ Finset.range n, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1))) :=
        Finset.prod_nonneg fun m _ => by
          have hle : ‖q‖ ^ (2 * (m + 1)) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq1.le
          linarith
      exact mul_le_of_le_one_left hfront htail
    have hnorm_lo : ∏ m ∈ Finset.range n, ((1 : ℝ) - ‖q‖ ^ (2 * (m + 1))) ≤ ‖qProd (q ^ 2) n‖ := by
      rw [qProd, norm_prod]
      refine Finset.prod_le_prod₀ (fun m _ => ?_) fun m _ => ?_
      · have hle : ‖q‖ ^ (2 * (m + 1)) ≤ 1 := pow_le_one₀ (norm_nonneg _) hq1.le
        linarith
      · have := norm_sub_norm_le (1 : ℂ) ((q ^ 2) ^ (m + 1))
        simpa [norm_one, norm_pow, ← pow_mul] using this
    exact hB_le.trans hnorm_lo
  have hqProd_hi : ∀ n : ℕ, ‖qProd (q ^ 2) n‖ ≤ B₁ := by
    intro n
    have hq_sq : ‖q‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg q) hq1 (by norm_num)
    have hgeom : Summable fun m : ℕ => ‖q‖ ^ (2 * (m + 1)) := by
      have hg := summable_geometric_of_lt_one (sq_nonneg ‖q‖) hq_sq
      exact (hg.mul_right (‖q‖ ^ 2)).congr fun m => by rw [← pow_succ, ← pow_mul]
    have hgeom_norm : Summable fun m : ℕ => ‖‖q‖ ^ (2 * (m + 1))‖ :=
      hgeom.congr fun m => by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    have hm := AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm hgeom_norm
    have hnorm_hi : ‖qProd (q ^ 2) n‖ ≤ ∏ m ∈ Finset.range n, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1))) := by
      rw [qProd, norm_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun m _ => ?_
      calc ‖(1 : ℂ) - (q ^ 2) ^ (m + 1)‖
          ≤ ‖(1 : ℂ)‖ + ‖(q ^ 2) ^ (m + 1)‖ := norm_sub_le _ _
        _ = 1 + ‖q‖ ^ (2 * (m + 1)) := by simp [norm_pow, ← pow_mul]
    have hprod_le : ∏ m ∈ Finset.range n, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1))) ≤ B₁ := by
      change ∏ m ∈ Finset.range n, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1))) ≤ ∏' m : ℕ, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1)))
      refine ge_of_tendsto hm.hasProd (Filter.eventually_atTop.mpr ⟨Finset.range n, fun s hs => ?_⟩)
      rw [← Finset.prod_sdiff hs]
      have htail : 1 ≤ ∏ m ∈ s \ Finset.range n, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1))) :=
        Finset.one_le_prod₀ fun m _ => by linarith [pow_nonneg (norm_nonneg q) (2 * (m + 1))]
      have hfront : 0 ≤ ∏ m ∈ Finset.range n, ((1 : ℝ) + ‖q‖ ^ (2 * (m + 1))) :=
        Finset.prod_nonneg fun m _ => by linarith [pow_nonneg (norm_nonneg q) (2 * (m + 1))]
      exact le_mul_of_one_le_left hfront htail
    exact hnorm_hi.trans hprod_le
  let C : ℕ → ℤ → ℂ := fun M k => qProd (q ^ 2) M * qBinom (q ^ 2) (2 * M) (M + k).toNat
  let K₀ : ℝ := B₁ ^ 2 / B₀ ^ 2
  have hC_bound : ∀ M : ℕ, ∀ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ‖C M k‖ ≤ K₀ := by
    intro M k hk
    rw [Finset.mem_Icc] at hk
    have hjk : (M + k).toNat ≤ 2 * M := by omega
    have hsub : 2 * M - (M + k).toNat = (M - k).toNat := by omega
    dsimp [C, qBinom]
    simp only [hjk, ↓reduceIte]
    rw [hsub, ← mul_div_assoc, norm_div, norm_mul, norm_mul]
    have hnum : ‖qProd (q ^ 2) M‖ * ‖qProd (q ^ 2) (2 * M)‖ ≤ B₁ ^ 2 := by
      nlinarith [hqProd_hi M, hqProd_hi (2 * M), norm_nonneg (qProd (q ^ 2) M),
        norm_nonneg (qProd (q ^ 2) (2 * M))]
    have hden : B₀ ^ 2 ≤ ‖qProd (q ^ 2) (M + k).toNat‖ * ‖qProd (q ^ 2) (M - k).toNat‖ := by
      nlinarith [hqProd_lo (M + k).toNat, hqProd_lo (M - k).toNat]
    exact div_le_div₀ (sq_nonneg B₁) hnum (sq_pos_of_pos hB₀_pos) hden
  have hC_tend : ∀ k : ℤ, Tendsto (fun M : ℕ => C M k) atTop (𝓝 (1 : ℂ)) := by
    intro k
    let P : ℂ := ∏' m : ℕ, ((1 : ℂ) - q ^ (2 * (m + 1)))
    have hP_ne : P ≠ 0 := by simpa [P, pow_mul] using tprod_one_sub_pow_ne_zero hq2_norm
    have hP_tend : Tendsto (fun n : ℕ => qProd (q ^ 2) n) atTop (𝓝 P) := by
      refine (hm1.hasProd.tendsto_prod_nat).congr fun n => ?_
      simp [qProd, pow_mul]
    have hP_2M : Tendsto (fun M : ℕ => qProd (q ^ 2) (2 * M)) atTop (𝓝 P) :=
      hP_tend.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩)
    have hP_plus : Tendsto (fun M : ℕ => qProd (q ^ 2) (M + k).toNat) atTop (𝓝 P) :=
      hP_tend.comp (tendsto_atTop_atTop.mpr fun b => ⟨b + k.natAbs, fun a ha => by omega⟩)
    have hP_minus : Tendsto (fun M : ℕ => qProd (q ^ 2) (M - k).toNat) atTop (𝓝 P) :=
      hP_tend.comp (tendsto_atTop_atTop.mpr fun b => ⟨b + k.natAbs, fun a ha => by omega⟩)
    have hlim1 : Tendsto (fun M : ℕ => qProd (q ^ 2) M * qProd (q ^ 2) (2 * M) /
        (qProd (q ^ 2) (M + k).toNat * qProd (q ^ 2) (M - k).toNat))
        atTop (𝓝 ((P * P) / (P * P))) :=
      (hP_tend.mul hP_2M).div (hP_plus.mul hP_minus) (mul_ne_zero hP_ne hP_ne)
    rw [div_self (mul_ne_zero hP_ne hP_ne)] at hlim1
    refine hlim1.congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨k.natAbs, fun M hM => ?_⟩
    have hjk : (M + k).toNat ≤ 2 * M := by omega
    have hsub : 2 * M - (M + k).toNat = (M - k).toNat := by omega
    dsimp [C, qBinom]
    simp only [hjk, ↓reduceIte]
    rw [hsub, mul_div_assoc]
  have hrhs_tend :
      Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), C M k * a k)
        atTop (𝓝 (∑' k : ℤ, a k)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hK₀ : 0 ≤ K₀ := by positivity
    have hfin : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖a k‖)
        atTop (𝓝 (∑' k : ℤ, ‖a k‖)) := by
      have ht := ha_sum.hasSum
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨s, hs⟩ := Metric.tendsto_atTop.mp ht δ hδ
      have hbd : ∃ N : ℕ, s ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        refine ⟨Finset.sup s Int.natAbs, fun k hk => ?_⟩
        have hle : k.natAbs ≤ Finset.sup s Int.natAbs := Finset.le_sup hk
        rw [Finset.mem_Icc]
        omega
      obtain ⟨N₀, hN₀⟩ := hbd
      refine ⟨N₀, fun N hN => ?_⟩
      have hsN : s ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) :=
        hN₀.trans (Finset.Icc_subset_Icc (by omega) (by omega))
      exact hs _ hsN
    have htail_lim : Tendsto (fun N : ℕ =>
        (∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖a k‖) atTop (𝓝 0) := by
      simpa [sub_self] using (tendsto_const_nhds (x := ∑' k : ℤ, ‖a k‖)).sub hfin
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp htail_lim)
      (ε / (2 * (K₀ + 1))) (by positivity)
    have htail_small : (∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖ <
        ε / (2 * (K₀ + 1)) := by
      have hd := hN₀ N₀ le_rfl
      have hle_tsum : ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖ ≤ ∑' k : ℤ, ‖a k‖ :=
        ha_sum.sum_le_tsum _ fun _ _ => norm_nonneg _
      rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle_tsum)] at hd
    have hhead_tend : Tendsto (fun M : ℕ =>
        ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), (C M k - 1) * a k) atTop (𝓝 0) := by
      have hterm0 : ∀ k : ℤ, Tendsto (fun M : ℕ => (C M k - 1) * a k) atTop (𝓝 0) := fun k => by
        simpa [sub_self, zero_mul] using
          ((hC_tend k).sub (tendsto_const_nhds (x := (1 : ℂ)))).mul_const (a k)
      have hsum_tend : ∀ s : Finset ℤ,
          Tendsto (fun M : ℕ => ∑ k ∈ s, (C M k - 1) * a k) atTop (𝓝 0) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert k s hk ih =>
          simp_rw [Finset.sum_insert hk]
          simpa [zero_add] using (hterm0 k).add ih
      exact hsum_tend _
    obtain ⟨M₁, hM₁⟩ := (Metric.tendsto_atTop.mp hhead_tend) (ε / 2) (half_pos hε)
    refine ⟨max N₀ M₁, fun M hM => ?_⟩
    have hN₀M : N₀ ≤ M := (le_max_left _ _).trans hM
    have hM₁M : M₁ ≤ M := (le_max_right _ _).trans hM
    have hIcc_sub : Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) :=
      Finset.Icc_subset_Icc (by omega) (by omega)
    have hsplit1 :
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), C M k * a k =
          (∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k) +
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k := by
      rw [← Finset.sum_sdiff hIcc_sub, add_comm]
    have hsplit2 :
        ∑' k : ℤ, a k =
          (∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k) +
            ∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k) := by
      have hsub_summ : Summable fun k : ℤ =>
          if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k :=
        (ha_sum.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun k => by split_ifs; simp; exact le_rfl)).of_norm
      have hite_summ : Summable fun k : ℤ =>
          if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then a k else (0 : ℂ) :=
        summable_of_ne_finset_zero (s := Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)) fun k hk => by simp [hk]
      have hadd := hite_summ.tsum_add hsub_summ
      have hsum_eq : (fun k : ℤ =>
          (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then a k else 0) +
            (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then 0 else a k)) = a := by
        ext k; split_ifs <;> simp
      have hite_tsum : (∑' k : ℤ, if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then a k else (0 : ℂ)) =
          ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k := by
        rw [tsum_eq_sum (s := Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)) (fun k hk => by simp [hk])]
        exact Finset.sum_congr rfl fun k hk => by simp [hk]
      rw [hsum_eq, hite_tsum] at hadd
      exact hadd
    have hhead_norm : ‖∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k -
        ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k‖ < ε / 2 := by
      have heq :
          ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k -
            ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k =
          ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), (C M k - 1) * a k := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [heq]
      simpa [dist_zero_right] using hM₁ M hM₁M
    have htail1_norm :
        ‖∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k‖ ≤
          K₀ * ((∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖) := by
      have h1 :
          ‖∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k‖ ≤
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), K₀ * ‖a k‖ := by
        calc ‖∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k‖
            ≤ ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ),
                ‖C M k * a k‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ),
                K₀ * ‖a k‖ := by
              refine Finset.sum_le_sum fun k hk => ?_
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (hC_bound M k (Finset.sdiff_subset hk)) (norm_nonneg _)
      rw [← Finset.mul_sum] at h1
      have hsum_tail :
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖ ≤
            (∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖ := by
        have hadd := Finset.sum_sdiff hIcc_sub (f := fun k => ‖a k‖)
        have hle := ha_sum.sum_le_tsum (Finset.Icc (-(M : ℤ)) (M : ℤ)) fun _ _ => norm_nonneg _
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_left hsum_tail hK₀)
    have htail2_norm :
        ‖∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k)‖ ≤
          (∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖ := by
      have hsub_summ : Summable fun k : ℤ =>
          ‖if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k‖ :=
        ha_sum.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => by split_ifs <;> simp
      have hite_summ : Summable fun k : ℤ =>
          if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then ‖a k‖ else 0 :=
        summable_of_ne_finset_zero (s := Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)) fun k hk => by simp [hk]
      have hadd := hite_summ.tsum_add hsub_summ
      have hsum_eq : (fun k : ℤ =>
          (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then ‖a k‖ else 0) +
            ‖if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k‖) =
          fun k => ‖a k‖ := by
        ext k; split_ifs <;> simp
      have hite_tsum : (∑' k : ℤ, if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then ‖a k‖ else 0) =
          ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖ := by
        rw [tsum_eq_sum (s := Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)) (fun k hk => by simp [hk])]
        exact Finset.sum_congr rfl fun k hk => by simp [hk]
      rw [hsum_eq, hite_tsum] at hadd
      calc ‖∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k)‖
          ≤ ∑' k : ℤ, ‖if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k‖ :=
            norm_tsum_le_tsum_norm hsub_summ
        _ = (∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖ := by linarith
    have htail_comb :
        ‖∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k‖ +
          ‖∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k)‖ < ε / 2 := by
      have h1 :
          (K₀ + 1) * ((∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖) < ε / 2 := by
        calc (K₀ + 1) * ((∑' k : ℤ, ‖a k‖) - ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖a k‖)
            < (K₀ + 1) * (ε / (2 * (K₀ + 1))) :=
              mul_lt_mul_of_pos_left htail_small (by positivity)
          _ = ε / 2 := by field_simp [show K₀ + 1 ≠ 0 by positivity]
      linarith
    rw [dist_eq_norm, hsplit1, hsplit2]
    have htri :
        ‖(∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k +
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k) -
          (∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k +
            ∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k))‖ ≤
          ‖∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k -
              ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k‖ +
            (‖∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k‖ +
              ‖∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k)‖) := by
      have heq :
          (∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k +
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k) -
          (∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k +
            ∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k)) =
          (∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k -
            ∑ k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), a k) +
          (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), C M k * a k -
            ∑' k : ℤ, (if k ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) then (0 : ℂ) else a k)) := by ring
      rw [heq]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    linarith
  have heq_fn :
      (fun M : ℕ =>
          qProd (q ^ 2) M *
            ∏ m ∈ Finset.range M, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1))) =
        (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), C M k * a k) := by
    ext M
    simpa [C, a, mul_assoc] using finite_jacobi_triple_product hq0 hq1 hx M
  rw [heq_fn] at hlhs_tend
  exact tendsto_nhds_unique hlhs_tend hrhs_tend

/-- Summability of the pentagonal series `∑' m : ℕ+, (-1) ^ m * (z ^ pent₁(m) + z ^ pent₂(m))`
for `‖z‖ < 1`. -/
theorem summable_pentagonal_complex {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun m : ℕ+ =>
      (-1 : ℂ) ^ (m : ℕ) *
        (z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) + z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) := by
  have hgeom : Summable fun m : ℕ => ‖z‖ ^ m := summable_geometric_of_lt_one (norm_nonneg _) hz
  have h1 : Summable fun m : ℕ+ => ‖z‖ ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) := by
    refine (hgeom.comp_injective PNat.coe_injective).of_nonneg_of_le
      (fun _ => pow_nonneg (norm_nonneg _) _) fun m => ?_
    have hm1 : 1 ≤ (m : ℕ) := m.pos
    have hle : (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) - 1) / 2 := by
      rcases eq_or_lt_of_le hm1 with hm_eq | hm_gt
      · simp [← hm_eq]
      · have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) - 1) := by
          rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
        omega
    exact pow_le_pow_of_le_one (norm_nonneg z) hz.le hle
  have h2 : Summable fun m : ℕ+ => ‖z‖ ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2) := by
    refine (hgeom.comp_injective PNat.coe_injective).of_nonneg_of_le
      (fun _ => pow_nonneg (norm_nonneg _) _) fun m => ?_
    have hm1 : 1 ≤ (m : ℕ) := m.pos
    have hle : (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) + 1) / 2 := by
      have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) + 1) := by
        rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
      omega
    exact pow_le_pow_of_le_one (norm_nonneg z) hz.le hle
  refine (h1.add h2).of_norm_bounded fun m => ?_
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact (norm_add_le _ _).trans (by simp [norm_pow])

/-- **Euler's Pentagonal Number Theorem** (`ℂ` version):
for `‖z‖ < 1`,
`∏' k, (1 - z ^ (k + 1)) = 1 + ∑' m : ℕ+, (-1) ^ m * (z ^ (m * (3 * m - 1) / 2) + z ^ (m * (3 * m + 1) / 2))`. -/
theorem euler_pentagonal_complex {z : ℂ} (hz : ‖z‖ < 1) :
    ∏' k : ℕ, ((1 : ℂ) - z ^ (k + 1)) =
      1 + ∑' m : ℕ+, (-1 : ℂ) ^ (m : ℕ) *
        (z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) + z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) := by
  by_cases hz0 : z = 0
  · subst hz0
    have hprod : ∏' k : ℕ, ((1 : ℂ) - (0 : ℂ) ^ (k + 1)) = 1 := by simp
    have hzero : ∀ m : ℕ+, (-1 : ℂ) ^ (m : ℕ) *
        ((0 : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) +
          (0 : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) = 0 := by
      intro m
      have hm1 : 1 ≤ (m : ℕ) * (3 * (m : ℕ) - 1) / 2 := by
        have hm := m.pos
        have hm1 : 1 ≤ (m : ℕ) := m.pos
        have : 2 ≤ (m : ℕ) * (3 * (m : ℕ) - 1) := by
          rcases eq_or_lt_of_le hm1 with h1 | hgt
          · simp [← h1]
          · have h3 : 2 ≤ 3 * (m : ℕ) - 1 := by omega
            nlinarith
        omega
      have hm2 : 1 ≤ (m : ℕ) * (3 * (m : ℕ) + 1) / 2 := by
        have hm := m.pos
        have : 2 ≤ (m : ℕ) * (3 * (m : ℕ) + 1) := by nlinarith
        omega
      simp [zero_pow (by omega : (m : ℕ) * (3 * (m : ℕ) - 1) / 2 ≠ 0),
            zero_pow (by omega : (m : ℕ) * (3 * (m : ℕ) + 1) / 2 ≠ 0)]
    have hsum : (∑' m : ℕ+, (-1 : ℂ) ^ (m : ℕ) *
        ((0 : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) +
          (0 : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2))) = 0 := by
      simp [hzero]
    rw [hprod, hsum, add_zero]
  let r : ℂ := Complex.exp (Complex.log z / 2)
  have hr2 : r ^ 2 = z := by
    dsimp [r]
    rw [sq, ← Complex.exp_add, add_halves, Complex.exp_log hz0]
  have hr_norm : ‖r‖ < 1 := by
    have hsq : ‖r‖ ^ 2 < 1 := by rwa [← hr2, norm_pow] at hz
    nlinarith [norm_nonneg r]
  have hr0 : r ≠ 0 := Complex.exp_ne_zero _
  let q : ℂ := r ^ 3
  let x : ℂ := -r⁻¹
  have hq0 : q ≠ 0 := pow_ne_zero _ hr0
  have hq1 : ‖q‖ < 1 := by
    rw [show ‖q‖ = ‖r‖ ^ 3 by simp [q, norm_pow]]
    exact pow_lt_one₀ (norm_nonneg _) hr_norm (by norm_num)
  have hx0 : x ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hr0)
  have hjtp := jacobi_triple_product hq0 hq1 hx0
  have hq2_eq : ∀ m : ℕ, (1 : ℂ) - q ^ (2 * (m + 1)) = 1 - z ^ (3 * m + 3) := by
    intro m
    have hpow : q ^ (2 * (m + 1)) = z ^ (3 * m + 3) := by
      dsimp [q]
      rw [← pow_mul, ← hr2, ← pow_mul]
      congr 1; ring
    rw [hpow]
  have hx_eq : ∀ m : ℕ, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)) =
      (1 - z ^ (3 * m + 1)) * (1 - z ^ (3 * m + 2)) := by
    intro m
    have hp1 : x * q ^ (2 * m + 1) = -z ^ (3 * m + 1) := by
      dsimp [x, q]
      rw [← pow_mul, neg_mul]
      congr 1
      have h1 : 3 * (2 * m + 1) = 1 + 2 * (3 * m + 1) := by ring
      rw [h1, pow_add, pow_one, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul, pow_mul, hr2]
    have hp2 : x⁻¹ * q ^ (2 * m + 1) = -z ^ (3 * m + 2) := by
      dsimp [x, q]
      rw [inv_neg, inv_inv, neg_mul, ← pow_mul]
      congr 1
      rw [← pow_succ', ← hr2, ← pow_mul]
      congr 1; ring
    rw [hp1, hp2]
    ring
  have hlhs_eq :
      (∏' m : ℕ, ((1 : ℂ) - q ^ (2 * (m + 1)))) *
          (∏' m : ℕ, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1))) =
        ∏' k : ℕ, ((1 : ℂ) - z ^ (k + 1)) := by
    have hz3 : ‖z ^ 3‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (by norm_num)
    have hm_all := multipliable_one_sub_pow hz
    have hm_mod0 : Multipliable fun m : ℕ => (1 : ℂ) - z ^ (3 * m + 3) := by
      simpa [show ∀ m : ℕ, (z ^ 3) ^ (m + 1) = z ^ (3 * m + 3) from fun m => by
        rw [← pow_mul, show 3 * (m + 1) = 3 * m + 3 by ring]] using multipliable_one_sub_pow hz3
    have hm_mod12 : Multipliable fun m : ℕ => (1 - z ^ (3 * m + 1)) * (1 - z ^ (3 * m + 2)) := by
      simp_rw [← hx_eq]
      have hsum : Summable fun m : ℕ => ‖(x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)‖ := by
        have hq_sq : ‖q‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg q) hq1 (by norm_num)
        have hg1 : Summable fun m : ℕ => ‖q‖ ^ (2 * m + 1) := by
          have hg := summable_geometric_of_lt_one (sq_nonneg ‖q‖) hq_sq
          simpa [pow_succ, pow_mul] using hg.mul_right ‖q‖
        have hg2 : Summable fun m : ℕ => ‖q‖ ^ (4 * m + 2) := by
          have hg := summable_geometric_of_lt_one (sq_nonneg ‖q‖) hq_sq
          refine hg.of_nonneg_of_le (fun _ => pow_nonneg (norm_nonneg _) _) fun m => ?_
          simpa [pow_mul] using pow_le_pow_of_le_one (norm_nonneg q) hq1.le (by omega : 2 * m ≤ 4 * m + 2)
        refine (hg1.mul_left ‖x + x⁻¹‖ |>.add hg2).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
        calc ‖(x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)‖
            ≤ ‖(x + x⁻¹) * q ^ (2 * m + 1)‖ + ‖q ^ (4 * m + 2)‖ := norm_add_le _ _
          _ = ‖x + x⁻¹‖ * ‖q‖ ^ (2 * m + 1) + ‖q‖ ^ (4 * m + 2) := by simp [norm_pow]
      have heq : ∀ m : ℕ, (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1)) =
          1 + ((x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)) := by
        intro m
        have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
        have hqpow : q ^ (2 * m + 1) * q ^ (2 * m + 1) = q ^ (4 * m + 2) := by
          rw [← pow_add]; congr 1; omega
        calc (1 + x * q ^ (2 * m + 1)) * (1 + x⁻¹ * q ^ (2 * m + 1))
            = 1 + (x + x⁻¹) * q ^ (2 * m + 1) + (x * x⁻¹) * (q ^ (2 * m + 1) * q ^ (2 * m + 1)) := by ring
          _ = 1 + ((x + x⁻¹) * q ^ (2 * m + 1) + q ^ (4 * m + 2)) := by rw [hxx, one_mul, hqpow]; ring
      simp_rw [heq]
      exact AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm hsum
    have ht_lhs : Tendsto (fun N : ℕ =>
        (∏ m ∈ Finset.range N, ((1 : ℂ) - z ^ (3 * m + 3))) *
          ∏ m ∈ Finset.range N, (1 - z ^ (3 * m + 1)) * (1 - z ^ (3 * m + 2)))
        atTop (𝓝 ((∏' m : ℕ, ((1 : ℂ) - z ^ (3 * m + 3))) *
          ∏' m : ℕ, (1 - z ^ (3 * m + 1)) * (1 - z ^ (3 * m + 2)))) :=
      hm_mod0.hasProd.tendsto_prod_nat.mul hm_mod12.hasProd.tendsto_prod_nat
    have ht_rhs : Tendsto (fun N : ℕ => ∏ k ∈ Finset.range (3 * N), ((1 : ℂ) - z ^ (k + 1)))
        atTop (𝓝 (∏' k : ℕ, ((1 : ℂ) - z ^ (k + 1)))) :=
      hm_all.hasProd.tendsto_prod_nat.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩)
    have hfin_eq : ∀ N : ℕ,
        (∏ m ∈ Finset.range N, ((1 : ℂ) - z ^ (3 * m + 3))) *
          (∏ m ∈ Finset.range N, (1 - z ^ (3 * m + 1)) * (1 - z ^ (3 * m + 2))) =
          ∏ k ∈ Finset.range (3 * N), ((1 : ℂ) - z ^ (k + 1)) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.mul_succ, Finset.prod_range_succ,
            Finset.prod_range_succ, Finset.prod_range_succ]
        calc ((∏ m ∈ Finset.range N, (1 - z ^ (3 * m + 3))) * (1 - z ^ (3 * N + 3))) *
              ((∏ m ∈ Finset.range N, (1 - z ^ (3 * m + 1)) * (1 - z ^ (3 * m + 2))) *
                ((1 - z ^ (3 * N + 1)) * (1 - z ^ (3 * N + 2))))
            = ((∏ m ∈ Finset.range N, (1 - z ^ (3 * m + 3))) *
                (∏ m ∈ Finset.range N, (1 - z ^ (3 * m + 1)) * (1 - z ^ (3 * m + 2)))) *
                (1 - z ^ (3 * N + 1)) * (1 - z ^ (3 * N + 2)) * (1 - z ^ (3 * N + 3)) := by ring
          _ = (∏ k ∈ Finset.range (3 * N), (1 - z ^ (k + 1))) *
                (1 - z ^ (3 * N + 1)) * (1 - z ^ (3 * N + 2)) * (1 - z ^ (3 * N + 3)) := by rw [ih]
    simp_rw [hq2_eq, hx_eq]
    exact tendsto_nhds_unique (ht_lhs.congr hfin_eq) ht_rhs
  have hrhs_eq :
      (∑' k : ℤ, q ^ (k.natAbs ^ 2) * x ^ k) =
        1 + ∑' m : ℕ+, (-1 : ℂ) ^ (m : ℕ) *
          (z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) + z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) := by
    have hp_term : ∀ m : ℕ+,
        q ^ ((m : ℕ) ^ 2) * x ^ ((m : ℕ) : ℤ) =
          (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) := by
      intro m
      dsimp [q, x]
      rw [zpow_natCast, neg_eq_neg_one_mul, mul_pow, ← pow_mul, inv_pow]
      have hne : r ^ (m : ℕ) ≠ 0 := pow_ne_zero _ hr0
      have hpow : r ^ (3 * (m : ℕ) ^ 2) * (r ^ (m : ℕ))⁻¹ =
          z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) := by
        rw [mul_inv_eq_iff_eq_mul₀ hne, ← hr2, ← pow_mul, ← pow_add]
        congr 1
        have hdvd : 2 ∣ (m : ℕ) * (3 * (m : ℕ) - 1) := by
          rcases Nat.even_or_odd (m : ℕ) with ⟨t, ht⟩ | ⟨t, ht⟩
          · rw [ht]; exact ⟨t * (3 * (t + t) - 1), by ring⟩
          · have hm1 : 1 ≤ (m : ℕ) := m.pos
            have hev : Even (3 * (m : ℕ) - 1) := by
              rw [ht]; refine ⟨3 * t + 1, by omega⟩
            rcases hev with ⟨s, hs⟩
            rw [hs]; exact ⟨(m : ℕ) * s, by ring⟩
        have hm1 : 1 ≤ (m : ℕ) := m.pos
        have h31 : 1 ≤ 3 * (m : ℕ) := by omega
        have h2e : 2 * ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) = (m : ℕ) * (3 * (m : ℕ) - 1) :=
          Nat.mul_div_cancel' hdvd
        zify [hm1, h31] at h2e ⊢
        nlinarith
      rw [← hpow]
      ring
    have hn_term : ∀ m : ℕ+,
        q ^ ((m : ℕ) ^ 2) * x ^ (-((m : ℕ) : ℤ)) =
          (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2) := by
      intro m
      dsimp [q, x]
      rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_inv, neg_eq_neg_one_mul, mul_pow, ← pow_mul]
      have hpow : r ^ (3 * (m : ℕ) ^ 2) * r ^ (m : ℕ) =
          z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2) := by
        rw [← hr2, ← pow_mul, ← pow_add]
        congr 1
        have hdvd : 2 ∣ (m : ℕ) * (3 * (m : ℕ) + 1) := by
          rcases Nat.even_or_odd (m : ℕ) with ⟨t, ht⟩ | ⟨t, ht⟩
          · rw [ht]; exact ⟨t * (3 * (t + t) + 1), by ring⟩
          · rw [ht]; exact ⟨(2 * t + 1) * (3 * t + 2), by ring⟩
        have h2e : 2 * ((m : ℕ) * (3 * (m : ℕ) + 1) / 2) = (m : ℕ) * (3 * (m : ℕ) + 1) :=
          Nat.mul_div_cancel' hdvd
        zify at h2e ⊢
        nlinarith
      rw [← hpow]
      ring
    have hsumm_p1 : Summable fun m : ℕ+ =>
        (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) := by
      have hgeom : Summable fun m : ℕ => ‖z‖ ^ m := summable_geometric_of_lt_one (norm_nonneg _) hz
      have hnorm : Summable fun m : ℕ+ =>
          ‖(-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2)‖ := by
        refine (hgeom.comp_injective PNat.coe_injective).of_nonneg_of_le
          (fun _ => norm_nonneg _) fun m => ?_
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
        have hm1 : 1 ≤ (m : ℕ) := m.pos
        have hle : (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) - 1) / 2 := by
          rcases eq_or_lt_of_le hm1 with hm_eq | hm_gt
          · simp [← hm_eq]
          · have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) - 1) := by
              rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
            omega
        exact pow_le_pow_of_le_one (norm_nonneg z) hz.le hle
      exact hnorm.of_norm
    have hsumm_p2 : Summable fun m : ℕ+ =>
        (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2) := by
      have hgeom : Summable fun m : ℕ => ‖z‖ ^ m := summable_geometric_of_lt_one (norm_nonneg _) hz
      have hnorm : Summable fun m : ℕ+ =>
          ‖(-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)‖ := by
        refine (hgeom.comp_injective PNat.coe_injective).of_nonneg_of_le
          (fun _ => norm_nonneg _) fun m => ?_
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
        have hm1 : 1 ≤ (m : ℕ) := m.pos
        have hle : (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) + 1) / 2 := by
          have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) + 1) := by
            rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
          omega
        exact pow_le_pow_of_le_one (norm_nonneg z) hz.le hle
      exact hnorm.of_norm
    let e : ℕ ≃ ℕ+ :=
      { toFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
        invFun := fun p => (p : ℕ) - 1
        left_inv := fun m => by simp
        right_inv := fun p => PNat.eq (by have := p.pos; dsimp; omega) }
    have hnat_pos : HasSum (fun n : ℕ => q ^ (((n : ℤ) + 1).natAbs ^ 2) * x ^ ((n : ℤ) + 1))
        (∑' m : ℕ+, (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2)) := by
      have hp1 := (e.hasSum_iff (f := fun m : ℕ+ =>
          (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2))).mpr hsumm_p1.hasSum
      refine hp1.congr_fun fun n => ?_
      have hna : (((n : ℤ) + 1).natAbs) = n + 1 := by omega
      have hzi : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      change q ^ (((n : ℤ) + 1).natAbs ^ 2) * x ^ ((n : ℤ) + 1) =
        (-1 : ℂ) ^ (n + 1) * z ^ ((n + 1) * (3 * (n + 1) - 1) / 2)
      rw [hna, hzi]
      exact hp_term ⟨n + 1, Nat.succ_pos n⟩
    have hnat_neg : HasSum (fun n : ℕ => q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * x ^ (-((n : ℤ) + 1)))
        (∑' m : ℕ+, (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) := by
      have hp2 := (e.hasSum_iff (f := fun m : ℕ+ =>
          (-1 : ℂ) ^ (m : ℕ) * z ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2))).mpr hsumm_p2.hasSum
      refine hp2.congr_fun fun n => ?_
      have hna : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      have hzi : (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
      change q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * x ^ (-((n : ℤ) + 1)) =
        (-1 : ℂ) ^ (n + 1) * z ^ ((n + 1) * (3 * (n + 1) + 1) / 2)
      rw [hna, hzi]
      exact hn_term ⟨n + 1, Nat.succ_pos n⟩
    have hzero_val : q ^ ((0 : ℤ).natAbs ^ 2) * x ^ (0 : ℤ) = 1 := by simp
    have hZ := (HasSum.of_add_one_of_neg_add_one
      (f := fun k : ℤ => q ^ (k.natAbs ^ 2) * x ^ k) hnat_pos hnat_neg).tsum_eq
    rw [hZ, hzero_val, add_right_comm, add_comm _ (1 : ℂ), ← hsumm_p1.tsum_add hsumm_p2]
    congr 1
    exact tsum_congr fun m => by ring
  rw [← hlhs_eq, hjtp, hrhs_eq]

/-- Summability of the real pentagonal series for `|x| < 1`. -/
theorem summable_pentagonal_real {x : ℝ} (hx : |x| < 1) :
    Summable fun m : ℕ+ =>
      (-1 : ℝ) ^ (m : ℕ) *
        (x ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) + x ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) := by
  have hxC : ‖(x : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hs := summable_pentagonal_complex hxC
  have hc : Summable fun m : ℕ+ => ((-1 : ℂ) ^ (m : ℕ) *
      ((x : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) +
        (x : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2))).re :=
    Complex.reCLM.summable hs
  refine hc.congr fun m => ?_
  simp only [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_pow,
    ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Euler's Pentagonal Number Theorem** (`ℝ` version):
for `|x| < 1`,
`∏' k, (1 - x ^ (k + 1)) = 1 + ∑' m : ℕ+, (-1) ^ m * (x ^ (m * (3 * m - 1) / 2) + x ^ (m * (3 * m + 1) / 2))`. -/
theorem euler_pentagonal_real {x : ℝ} (hx : |x| < 1) :
    ∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) =
      1 + ∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) *
        (x ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) + x ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) := by
  have hxC : ‖(x : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hC := euler_pentagonal_complex hxC
  have hlhs : ∏' k : ℕ, ((1 : ℂ) - (x : ℂ) ^ (k + 1)) =
      ((∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) : ℝ) : ℂ) := by
    have hm := multipliable_one_sub_pow_real hx
    have hc := (Complex.continuous_ofReal.tendsto _).comp hm.hasProd
    have hp : HasProd (fun k : ℕ => ((1 : ℂ) - (x : ℂ) ^ (k + 1)))
        ((∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) : ℝ) : ℂ) := by
      refine hc.congr fun s => ?_
      simp only [Function.comp_apply, Complex.ofReal_prod, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_pow]
    exact hp.tprod_eq
  have hrhs : (1 : ℂ) + ∑' m : ℕ+, (-1 : ℂ) ^ (m : ℕ) *
        ((x : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) +
          (x : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) =
      ((1 + ∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) *
        (x ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) + x ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) : ℝ) : ℂ) := by
    have hs := summable_pentagonal_real hx
    have hc := (Complex.continuous_ofReal.tendsto _).comp hs.hasSum
    have hsum : HasSum (fun m : ℕ+ => (-1 : ℂ) ^ (m : ℕ) *
        ((x : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) +
          (x : ℂ) ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)))
        ((∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) *
          (x ^ ((m : ℕ) * (3 * (m : ℕ) - 1) / 2) + x ^ ((m : ℕ) * (3 * (m : ℕ) + 1) / 2)) : ℝ) : ℂ) := by
      refine hc.congr fun s => ?_
      simp only [Function.comp_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_add]
    rw [hsum.tsum_eq]
    norm_cast
  rw [hlhs, hrhs] at hC
  exact Complex.ofReal_inj.mp hC

/-- Power-series coefficient extraction: if `∑' n, c n * x ^ n = 0` on `(-r, r)` (`r > 0`)
and `∑' n, |c n| * (r / 2) ^ n < ∞`, then `c n = 0` for all `n`. -/
theorem tsum_pow_eq_zero_imp_coeff_eq_zero {c : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (hs : Summable fun n : ℕ => |c n| * (r / 2) ^ n)
    (hzero : ∀ x : ℝ, |x| < r → ∑' n : ℕ, c n * x ^ n = 0) :
    ∀ n : ℕ, c n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_contra hcn
    have hcn_pos : 0 < |c n| := abs_pos.mpr hcn
    have hs_tail : Summable fun m : ℕ => |c (n + 1 + m)| * (r / 2) ^ m := by
      have hshift : Summable fun m : ℕ => |c (n + 1 + m)| * (r / 2) ^ (n + 1 + m) :=
        ((summable_nat_add_iff (n + 1)).mpr hs).congr fun m => by rw [add_comm m (n + 1)]
      have hpow_ne : (r / 2) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by positivity)
      have hdiv := hshift.div_const ((r / 2) ^ (n + 1))
      refine hdiv.congr fun m => ?_
      rw [pow_add, mul_comm ((r / 2) ^ (n + 1)), ← mul_assoc, mul_div_cancel_right₀ _ hpow_ne]
    obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = ∑' m : ℕ, |c (n + 1 + m)| * (r / 2) ^ m := ⟨_, rfl⟩
    have hM : 0 ≤ M := hM_def ▸ tsum_nonneg fun m => mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _)
    obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x = min (r / 4) (|c n| / (2 * (M + 1))) := ⟨_, rfl⟩
    have hx_pos : 0 < x := hx_def ▸ lt_min (by positivity) (by positivity)
    have hx_lt_half : x < r / 2 := hx_def ▸ (min_le_left _ _).trans_lt (by linarith)
    have hx_lt_r : |x| < r := by rw [abs_of_pos hx_pos]; linarith
    have hx_sum : Summable fun k : ℕ => c k * x ^ k := by
      have hx_sum_norm : Summable fun k : ℕ => ‖c k * x ^ k‖ := by
        refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx_pos]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx_pos.le hx_lt_half.le k) (abs_nonneg _)
      exact hx_sum_norm.of_norm
    have h0 := hzero x hx_lt_r
    have hsplit := hx_sum.sum_add_tsum_nat_add n
    have hhead : ∑ k ∈ Finset.range n, c k * x ^ k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [ih k (Finset.mem_range.mp hk), zero_mul]
    rw [hhead, zero_add] at hsplit
    have htail_sum : Summable fun m : ℕ => c (n + m) * x ^ (n + m) := by
      have h0' : Summable fun m : ℕ => c (m + n) * x ^ (m + n) := (summable_nat_add_iff n).mpr hx_sum
      exact h0'.congr fun m => by rw [add_comm n m]
    have hsplit2 := htail_sum.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one, add_zero] at hsplit2
    have htail1 : ∑' m : ℕ, c (n + (m + 1)) * x ^ (n + (m + 1)) =
        x ^ n * (x * ∑' m : ℕ, c (n + 1 + m) * x ^ m) := by
      have hs_m : Summable fun m : ℕ => c (n + 1 + m) * x ^ m := by
        have hs_m_norm : Summable fun m : ℕ => ‖c (n + 1 + m) * x ^ m‖ := by
          refine hs_tail.of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx_pos]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx_pos.le hx_lt_half.le m) (abs_nonneg _)
        exact hs_m_norm.of_norm
      rw [← hs_m.tsum_mul_left, ← (hs_m.mul_left x).tsum_mul_left]
      refine tsum_congr fun m => ?_
      have hid : n + (m + 1) = n + 1 + m := by omega
      rw [hid, pow_add, pow_add, pow_one]
      ring
    rw [htail1] at hsplit2
    have hcomm : (∑' i : ℕ, c (i + n) * x ^ (i + n)) = ∑' i : ℕ, c (n + i) * x ^ (n + i) :=
      tsum_congr fun i => by rw [add_comm i n]
    have hzero_n : c n * x ^ n + x ^ n * (x * ∑' m : ℕ, c (n + 1 + m) * x ^ m) = 0 := by
      linarith only [h0, hsplit, hcomm, hsplit2]
    have hfact : x ^ n * (c n + x * ∑' m : ℕ, c (n + 1 + m) * x ^ m) = 0 := by linarith
    have hcn_eq : c n = -(x * ∑' m : ℕ, c (n + 1 + m) * x ^ m) := by
      have h1 : c n + x * ∑' m : ℕ, c (n + 1 + m) * x ^ m = 0 :=
        (mul_eq_zero.mp hfact).resolve_left (pow_ne_zero n hx_pos.ne')
      linarith
    have htail_le : |∑' m : ℕ, c (n + 1 + m) * x ^ m| ≤ M := by
      have hs_m_abs : Summable fun m : ℕ => |c (n + 1 + m) * x ^ m| :=
        hs_tail.of_nonneg_of_le (fun _ => abs_nonneg _) fun m => by
          rw [abs_mul, abs_pow, abs_of_pos hx_pos]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx_pos.le hx_lt_half.le m) (abs_nonneg _)
      have hs_m_norm : Summable fun m : ℕ => ‖c (n + 1 + m) * x ^ m‖ :=
        hs_m_abs.congr fun m => (Real.norm_eq_abs _).symm
      have hbd_norm : ‖∑' m : ℕ, c (n + 1 + m) * x ^ m‖ ≤ ∑' m : ℕ, ‖c (n + 1 + m) * x ^ m‖ :=
        norm_tsum_le_tsum_norm hs_m_norm
      rw [Real.norm_eq_abs] at hbd_norm
      have htsum_abs : ∑' m : ℕ, ‖c (n + 1 + m) * x ^ m‖ = ∑' m : ℕ, |c (n + 1 + m) * x ^ m| :=
        tsum_congr fun m => Real.norm_eq_abs _
      calc |∑' m : ℕ, c (n + 1 + m) * x ^ m|
          ≤ ∑' m : ℕ, |c (n + 1 + m) * x ^ m| := htsum_abs ▸ hbd_norm
        _ ≤ ∑' m : ℕ, |c (n + 1 + m)| * (r / 2) ^ m := hs_m_abs.tsum_le_tsum (fun m => by
            rw [abs_mul, abs_pow, abs_of_pos hx_pos]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx_pos.le hx_lt_half.le m) (abs_nonneg _)) hs_tail
        _ = M := hM_def.symm
    have hcn_le : |c n| ≤ x * M := by
      rw [hcn_eq, abs_neg, abs_mul, abs_of_pos hx_pos]
      exact mul_le_mul_of_nonneg_left htail_le hx_pos.le
    have hx_le : x ≤ |c n| / (2 * (M + 1)) := hx_def ▸ min_le_right _ _
    have hcontra : |c n| ≤ |c n| / 2 := by
      calc |c n| ≤ x * M := hcn_le
        _ ≤ (|c n| / (2 * (M + 1))) * M := mul_le_mul_of_nonneg_right hx_le hM
        _ ≤ (|c n| / (2 * (M + 1))) * (M + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = |c n| / 2 := by field_simp [show M + 1 ≠ 0 by positivity]
    linarith

private lemma pentagonal1_strictMono :
    StrictMono (fun m : ℕ+ => (m : ℕ) * (3 * (m : ℕ) - 1) / 2) := by
  intro a b hab
  have ha : 1 ≤ (a : ℕ) := a.pos
  have hb : 1 ≤ (b : ℕ) := b.pos
  have h1 : (a : ℕ) * (3 * (a : ℕ) - 1) + 2 ≤ (b : ℕ) * (3 * (b : ℕ) - 1) := by
    have hab1 : ((a : ℕ) : ℤ) + 1 ≤ (b : ℕ) := by exact_mod_cast hab
    zify [show 1 ≤ 3 * (a : ℕ) by omega, show 1 ≤ 3 * (b : ℕ) by omega]
    nlinarith
  calc (a : ℕ) * (3 * (a : ℕ) - 1) / 2
      < ((a : ℕ) * (3 * (a : ℕ) - 1) + 2) / 2 := by
        rw [Nat.add_div_right _ (by decide)]; exact Nat.lt_succ_self _
    _ ≤ (b : ℕ) * (3 * (b : ℕ) - 1) / 2 := Nat.div_le_div_right h1

private lemma pentagonal2_strictMono :
    StrictMono (fun m : ℕ+ => (m : ℕ) * (3 * (m : ℕ) + 1) / 2) := by
  intro a b hab
  have h1 : (a : ℕ) * (3 * (a : ℕ) + 1) + 2 ≤ (b : ℕ) * (3 * (b : ℕ) + 1) := by
    have hab1 : (a : ℕ) + 1 ≤ (b : ℕ) := hab
    nlinarith
  calc (a : ℕ) * (3 * (a : ℕ) + 1) / 2
      < ((a : ℕ) * (3 * (a : ℕ) + 1) + 2) / 2 := by
        rw [Nat.add_div_right _ (by decide)]; exact Nat.lt_succ_self _
    _ ≤ (b : ℕ) * (3 * (b : ℕ) + 1) / 2 := Nat.div_le_div_right h1

private def pentRecCoeff (b : ℕ) : ℝ :=
  if b = 0 then 1
  else ∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m *
    ((if m * (3 * m - 1) / 2 = b then 1 else 0) + (if m * (3 * m + 1) / 2 = b then 1 else 0))

private lemma pentRecCoeff_bound (b : ℕ) : |pentRecCoeff b| ≤ 2 := by
  by_cases hb0 : b = 0
  · simp [pentRecCoeff, hb0]
  · rw [pentRecCoeff]
    simp only [hb0, ↓reduceIte]
    have htri :
        |∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m *
          ((if m * (3 * m - 1) / 2 = b then 1 else 0) + (if m * (3 * m + 1) / 2 = b then 1 else 0))| ≤
          (∑ m ∈ Finset.Icc 1 b, (if m * (3 * m - 1) / 2 = b then (1 : ℝ) else 0)) +
            (∑ m ∈ Finset.Icc 1 b, (if m * (3 * m + 1) / 2 = b then (1 : ℝ) else 0)) := by
      calc |∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m *
            ((if m * (3 * m - 1) / 2 = b then 1 else 0) +
              (if m * (3 * m + 1) / 2 = b then 1 else 0))|
          ≤ ∑ m ∈ Finset.Icc 1 b, |(-1 : ℝ) ^ m *
            ((if m * (3 * m - 1) / 2 = b then 1 else 0) +
              (if m * (3 * m + 1) / 2 = b then 1 else 0))| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ m ∈ Finset.Icc 1 b,
            ((if m * (3 * m - 1) / 2 = b then (1 : ℝ) else 0) +
              (if m * (3 * m + 1) / 2 = b then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
            split_ifs <;> norm_num
        _ = (∑ m ∈ Finset.Icc 1 b, (if m * (3 * m - 1) / 2 = b then (1 : ℝ) else 0)) +
            (∑ m ∈ Finset.Icc 1 b, (if m * (3 * m + 1) / 2 = b then (1 : ℝ) else 0)) :=
            Finset.sum_add_distrib
    have hcard1 : ∑ m ∈ Finset.Icc 1 b, (if m * (3 * m - 1) / 2 = b then (1 : ℝ) else 0) ≤ 1 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hsub : ((Finset.Icc 1 b).filter (fun m => m * (3 * m - 1) / 2 = b)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro m₁ hm₁ m₂ hm₂
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm₁ hm₂
        have hinj : (⟨m₁, hm₁.1.1⟩ : ℕ+) = ⟨m₂, hm₂.1.1⟩ :=
          pentagonal1_strictMono.injective (hm₁.2.trans hm₂.2.symm)
        exact congrArg PNat.val hinj
      exact_mod_cast hsub
    have hcard2 : ∑ m ∈ Finset.Icc 1 b, (if m * (3 * m + 1) / 2 = b then (1 : ℝ) else 0) ≤ 1 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hsub : ((Finset.Icc 1 b).filter (fun m => m * (3 * m + 1) / 2 = b)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro m₁ hm₁ m₂ hm₂
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm₁ hm₂
        have hinj : (⟨m₁, hm₁.1.1⟩ : ℕ+) = ⟨m₂, hm₂.1.1⟩ :=
          pentagonal2_strictMono.injective (hm₁.2.trans hm₂.2.symm)
        exact congrArg PNat.val hinj
      exact_mod_cast hsub
    linarith only [htri, hcard1, hcard2]

private lemma pentRecCoeff_summable {x : ℝ} (hx : |x| < 1) :
    Summable fun b : ℕ => |pentRecCoeff b| * |x| ^ b := by
  have hg := summable_geometric_of_lt_one (abs_nonneg x) hx
  refine (hg.mul_left 2).of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
    fun b => mul_le_mul_of_nonneg_right (pentRecCoeff_bound b) (pow_nonneg (abs_nonneg _) _)

private lemma pentRecCoeff_tsum_aux {x : ℝ} (hx : |x| < 1) (p : ℕ+ → ℕ)
    (hp_inj : Function.Injective p)
    (hp_pos : ∀ m : ℕ+, 1 ≤ p m)
    (hp_le : ∀ m : ℕ+, (m : ℕ) ≤ p m)
    (q : ℕ → ℕ) (hq : ∀ m : ℕ+, p m = q (m : ℕ)) (hq0 : q 0 = 0) :
    (∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) * x ^ p m =
      ∑' b : ℕ, (if b = 0 then (0 : ℝ) else
        ∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m * (if q m = b then 1 else 0)) * x ^ b) ∧
    Summable (fun b : ℕ => (if b = 0 then (0 : ℝ) else
        ∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m * (if q m = b then 1 else 0)) * x ^ b) := by
  let g : ℕ → ℝ := fun b =>
    (if b = 0 then (0 : ℝ) else
      ∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m * (if q m = b then 1 else 0)) * x ^ b
  have hsupp : Function.support g ⊆ Set.range p := by
    intro b hb
    rw [Function.mem_support] at hb
    by_contra hnot
    rw [Set.mem_range, not_exists] at hnot
    apply hb
    dsimp [g]
    split_ifs with hb0
    · simp
    · refine mul_eq_zero_of_left (Finset.sum_eq_zero fun m hm => ?_) _
      rw [Finset.mem_Icc] at hm
      have hne : q m ≠ b := fun heq => hnot ⟨m, hm.1⟩ ((hq ⟨m, hm.1⟩).trans heq)
      simp [hne]
  have hgp : ∀ m : ℕ+, g (p m) = (-1 : ℝ) ^ (m : ℕ) * x ^ p m := by
    intro m
    have hm1 : 1 ≤ p m := hp_pos m
    have hm_le : (m : ℕ) ≤ p m := hp_le m
    dsimp [g]
    have hp_ne : p m ≠ 0 := by omega
    simp only [hp_ne, ↓reduceIte]
    rw [Finset.sum_eq_single (m : ℕ) ?_ ?_]
    · simp [hq m]
    · intro k _ hkm
      by_cases hk0 : k = 0
      · simp [hk0, hq0, hp_ne.symm]
      · have hne : q k ≠ p m := fun heq => by
          have hinj : (⟨k, Nat.pos_of_ne_zero hk0⟩ : ℕ+) = m :=
            hp_inj ((hq ⟨k, Nat.pos_of_ne_zero hk0⟩).trans heq)
          exact hkm (congrArg PNat.val hinj)
        simp [hne]
    · intro hm_not
      exfalso; exact hm_not (Finset.mem_Icc.mpr ⟨m.pos, hm_le⟩)
  have heq : ∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) * x ^ p m = ∑' b : ℕ, g b := by
    have hts := (hp_inj.tsum_eq hsupp).symm
    change ∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) * x ^ p m = ∑' b : ℕ, g b
    rw [hts]
    exact tsum_congr fun m => (hgp m).symm
  have hsum : Summable g := by
    have hs := (summable_geometric_of_lt_one (abs_nonneg x) hx).mul_left 1
    have hnorm : Summable fun b : ℕ => ‖g b‖ := by
      refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun b => ?_
      dsimp [g]
      rw [abs_mul, abs_pow]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (abs_nonneg x) b)
      split_ifs with hb0
      · simp
      · calc |∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m * (if q m = b then 1 else 0)|
            ≤ ∑ m ∈ Finset.Icc 1 b, (if q m = b then (1 : ℝ) else 0) := by
              calc |∑ m ∈ Finset.Icc 1 b, (-1 : ℝ) ^ m * (if q m = b then 1 else 0)|
                  ≤ ∑ m ∈ Finset.Icc 1 b, |(-1 : ℝ) ^ m * (if q m = b then 1 else 0)| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = ∑ m ∈ Finset.Icc 1 b, (if q m = b then (1 : ℝ) else 0) := by
                    refine Finset.sum_congr rfl fun m _ => ?_
                    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
                    split_ifs <;> norm_num
          _ ≤ 1 := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
              have hsub : ((Finset.Icc 1 b).filter (fun m => q m = b)).card ≤ 1 := by
                rw [Finset.card_le_one]
                intro m₁ hm₁ m₂ hm₂
                simp only [Finset.mem_filter, Finset.mem_Icc] at hm₁ hm₂
                exact congrArg PNat.val (hp_inj
                  ((hq ⟨m₁, hm₁.1.1⟩).trans (hm₁.2.trans hm₂.2.symm |>.trans (hq ⟨m₂, hm₂.1.1⟩).symm)))
              exact_mod_cast hsub
    exact hnorm.of_norm
  exact ⟨heq, hsum⟩

private lemma pentRecCoeff_tsum {x : ℝ} (hx : |x| < 1) :
    ∑' b : ℕ, pentRecCoeff b * x ^ b = ∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) := by
  let p1 : ℕ+ → ℕ := fun m => (m : ℕ) * (3 * (m : ℕ) - 1) / 2
  let p2 : ℕ+ → ℕ := fun m => (m : ℕ) * (3 * (m : ℕ) + 1) / 2
  rw [euler_pentagonal_real hx]
  have hsp1 : Summable fun m : ℕ+ => (-1 : ℝ) ^ (m : ℕ) * x ^ p1 m := by
    have hg := summable_geometric_of_lt_one (abs_nonneg x) hx
    have hnorm : Summable fun m : ℕ+ => ‖(-1 : ℝ) ^ (m : ℕ) * x ^ p1 m‖ := by
      refine (hg.comp_injective PNat.coe_injective).of_nonneg_of_le
        (fun _ => norm_nonneg _) fun m => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow]
      have hm1 : 1 ≤ (m : ℕ) := m.pos
      have hle : (m : ℕ) ≤ p1 m := by
        rcases eq_or_lt_of_le hm1 with hm_eq | hm_gt
        · simp [p1, ← hm_eq]
        · have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) - 1) := by
            rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
          dsimp [p1]; omega
      exact pow_le_pow_of_le_one (abs_nonneg x) hx.le hle
    exact hnorm.of_norm
  have hsp2 : Summable fun m : ℕ+ => (-1 : ℝ) ^ (m : ℕ) * x ^ p2 m := by
    have hg := summable_geometric_of_lt_one (abs_nonneg x) hx
    have hnorm : Summable fun m : ℕ+ => ‖(-1 : ℝ) ^ (m : ℕ) * x ^ p2 m‖ := by
      refine (hg.comp_injective PNat.coe_injective).of_nonneg_of_le
        (fun _ => norm_nonneg _) fun m => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow]
      have hm1 : 1 ≤ (m : ℕ) := m.pos
      have hle : (m : ℕ) ≤ p2 m := by
        have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) + 1) := by
          rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
        dsimp [p2]; omega
      exact pow_le_pow_of_le_one (abs_nonneg x) hx.le hle
    exact hnorm.of_norm
  have hp1_aux := pentRecCoeff_tsum_aux hx p1 pentagonal1_strictMono.injective
    (fun m => by
      have hm : 1 ≤ (m : ℕ) := m.pos
      have : 2 ≤ (m : ℕ) * (3 * (m : ℕ) - 1) := by
        rcases eq_or_lt_of_le hm with h1 | hgt
        · simp [← h1]
        · have h3 : 2 ≤ 3 * (m : ℕ) - 1 := by omega
          have : (m : ℕ) * 2 ≤ (m : ℕ) * (3 * (m : ℕ) - 1) := Nat.mul_le_mul_left (m : ℕ) h3
          omega
      dsimp [p1]; omega)
    (fun m => by
      have hm : 1 ≤ (m : ℕ) := m.pos
      rcases eq_or_lt_of_le hm with h1 | hgt
      · simp [p1, ← h1]
      · have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) - 1) := by
          rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
        dsimp [p1]; omega)
    (fun m => m * (3 * m - 1) / 2) (fun _ => rfl) rfl
  have hp2_aux := pentRecCoeff_tsum_aux hx p2 pentagonal2_strictMono.injective
    (fun m => by
      have hm : 1 ≤ (m : ℕ) := m.pos
      have h3 : 2 ≤ 3 * (m : ℕ) + 1 := by omega
      have : (m : ℕ) * 2 ≤ (m : ℕ) * (3 * (m : ℕ) + 1) := Nat.mul_le_mul_left (m : ℕ) h3
      dsimp [p2]; omega)
    (fun m => by
      have hm : 1 ≤ (m : ℕ) := m.pos
      have : 2 * (m : ℕ) ≤ (m : ℕ) * (3 * (m : ℕ) + 1) := by
        rw [mul_comm 2]; exact Nat.mul_le_mul_left (m : ℕ) (by omega)
      dsimp [p2]; omega)
    (fun m => m * (3 * m + 1) / 2) (fun _ => rfl) rfl
  have h0_sum : Summable fun b : ℕ => (if b = 0 then (1 : ℝ) else 0) * x ^ b :=
    (hasSum_single 0 fun b hb => by simp [hb]).summable
  have hsum_add : 1 + ∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) * (x ^ p1 m + x ^ p2 m) =
      ∑' b : ℕ, pentRecCoeff b * x ^ b := by
    have hp12 : ∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) * (x ^ p1 m + x ^ p2 m) =
        (∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) * x ^ p1 m) +
          ∑' m : ℕ+, (-1 : ℝ) ^ (m : ℕ) * x ^ p2 m := by
      rw [← hsp1.tsum_add hsp2]
      refine tsum_congr fun m => by ring
    rw [hp12, hp1_aux.1, hp2_aux.1]
    have h0_val : (1 : ℝ) = ∑' b : ℕ, (if b = 0 then (1 : ℝ) else 0) * x ^ b := by
      rw [tsum_eq_single 0]
      · simp
      · intro b hb; simp [hb]
    rw [← hp1_aux.2.tsum_add hp2_aux.2]
    nth_rw 1 [h0_val]
    rw [← h0_sum.tsum_add (hp1_aux.2.add hp2_aux.2)]
    refine tsum_congr fun b => ?_
    rw [pentRecCoeff]
    split_ifs with hb0
    · simp [hb0]
    · rw [zero_mul, zero_add, ← add_mul, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun m _ => by ring
  exact hsum_add.symm

private def pentConvDiff (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), (partitionCount k : ℝ) * pentRecCoeff (n - k)) - (if n = 0 then 1 else 0)

private lemma pentConvDiff_zero {x : ℝ} (hx : |x| < 1 / 2) :
    ∑' n : ℕ, pentConvDiff n * x ^ n = 0 := by
  have hx1 : |x| < 1 := hx.trans (by norm_num)
  have hp_norm : Summable fun k : ℕ => ‖(partitionCount k : ℝ) * x ^ k‖ := by
    have hs := summable_partitionCount_mul_pow_real (abs_nonneg x) hx1
    refine hs.congr fun k => ?_
    conv_rhs => rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (partitionCount k))]
  have hc_norm : Summable fun b : ℕ => ‖pentRecCoeff b * x ^ b‖ := by
    refine (pentRecCoeff_summable hx1).congr fun b => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have hmul := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hp_norm hc_norm
  have hprod_one : (∑' k : ℕ, (partitionCount k : ℝ) * x ^ k) * (∑' b : ℕ, pentRecCoeff b * x ^ b) = 1 := by
    rw [tsum_partitionCount_mul_pow_real hx1, pentRecCoeff_tsum hx1]
    exact inv_mul_cancel₀ (tprod_one_sub_pow_real_ne_zero hx1)
  rw [hprod_one] at hmul
  have hcauchy_summ : Summable fun n : ℕ =>
      (∑ k ∈ Finset.range (n + 1), (partitionCount k : ℝ) * pentRecCoeff (n - k)) * x ^ n := by
    refine (summable_norm_sum_mul_range_of_summable_norm hp_norm hc_norm).of_norm.congr fun n => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' hkn]
  have h1_summ : Summable fun n : ℕ => (if n = 0 then (1 : ℝ) else 0) * x ^ n :=
    (hasSum_single 0 fun n hn => by simp [hn]).summable
  have hd_sum : ∑' n : ℕ, pentConvDiff n * x ^ n =
      (∑' n : ℕ, (∑ k ∈ Finset.range (n + 1), (partitionCount k : ℝ) * pentRecCoeff (n - k)) * x ^ n) -
        ∑' n : ℕ, (if n = 0 then (1 : ℝ) else 0) * x ^ n := by
    rw [← hcauchy_summ.tsum_sub h1_summ]
    refine tsum_congr fun n => by rw [pentConvDiff]; ring
  have h1_val : ∑' n : ℕ, (if n = 0 then (1 : ℝ) else 0) * x ^ n = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [hn]
  have hcauchy_val :
      ∑' n : ℕ, (∑ k ∈ Finset.range (n + 1), (partitionCount k : ℝ) * pentRecCoeff (n - k)) * x ^ n = 1 := by
    rw [hmul]
    refine tsum_congr fun n => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' hkn]
  rw [hd_sum, hcauchy_val, h1_val, sub_self]

private lemma pentConvDiff_summ :
    Summable fun n : ℕ => |pentConvDiff n| * (1 / 4 : ℝ) ^ n := by
  have hq_norm : Summable fun k : ℕ => ‖(partitionCount k : ℝ) * (1 / 4 : ℝ) ^ k‖ := by
    have hs := summable_partitionCount_mul_pow_real (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    refine hs.congr fun k => ?_
    conv_rhs =>
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (partitionCount k)),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hc_norm : Summable fun b : ℕ => ‖pentRecCoeff b * (1 / 4 : ℝ) ^ b‖ := by
    refine (pentRecCoeff_summable (x := (1 / 4 : ℝ)) (by norm_num)).congr fun b => ?_
    conv_rhs => rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have hcs := summable_norm_sum_mul_range_of_summable_norm hq_norm hc_norm
  have hcs' : Summable fun n : ℕ =>
      |∑ k ∈ Finset.range (n + 1), (partitionCount k : ℝ) * pentRecCoeff (n - k)| * (1 / 4 : ℝ) ^ n := by
    refine hcs.congr fun n => ?_
    rw [Real.norm_eq_abs, ← abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n),
        ← abs_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' hkn]
  have h1_s : Summable fun n : ℕ => (if n = 0 then (1 : ℝ) else 0) * (1 / 4 : ℝ) ^ n :=
    (hasSum_single 0 fun n hn => by simp [hn]).summable
  refine (hcs'.add h1_s).of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (by positivity))
    fun n => ?_
  have htri : |pentConvDiff n| ≤ |∑ k ∈ Finset.range (n + 1), (partitionCount k : ℝ) * pentRecCoeff (n - k)| +
      (if n = 0 then (1 : ℝ) else 0) := by
    rw [pentConvDiff]
    refine (abs_sub _ _).trans ?_
    split_ifs <;> norm_num
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right htri (by positivity)

private lemma pentConvDiff_sum_eq (n : ℕ) :
    ∑ b ∈ Finset.Icc 1 n, (partitionCount (n - b) : ℝ) * pentRecCoeff b =
      -∑ m ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (m - 1) *
        ((if m * (3 * m - 1) / 2 ≤ n then (partitionCount (n - m * (3 * m - 1) / 2) : ℝ) else 0) +
         (if m * (3 * m + 1) / 2 ≤ n then (partitionCount (n - m * (3 * m + 1) / 2) : ℝ) else 0)) := by
  have hinner : ∀ b ∈ Finset.Icc 1 n,
      (partitionCount (n - b) : ℝ) * pentRecCoeff b =
        ∑ m ∈ Finset.Icc 1 n, (-1 : ℝ) ^ m * (partitionCount (n - b) : ℝ) *
          ((if m * (3 * m - 1) / 2 = b then 1 else 0) +
            (if m * (3 * m + 1) / 2 = b then 1 else 0)) := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hb0 : b ≠ 0 := by omega
    rw [pentRecCoeff]
    simp only [hb0, ↓reduceIte, Finset.mul_sum]
    have hsplit : Finset.Icc 1 n = Finset.Icc 1 b ∪ Finset.Icc (b + 1) n := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 b) (Finset.Icc (b + 1) n) := by
      rw [Finset.disjoint_left]; intro m h1 h2
      rw [Finset.mem_Icc] at h1 h2; omega
    rw [hsplit, Finset.sum_union hdisj]
    have hzero_hi : ∑ m ∈ Finset.Icc (b + 1) n, (-1 : ℝ) ^ m * (partitionCount (n - b) : ℝ) *
        ((if m * (3 * m - 1) / 2 = b then 1 else 0) +
          (if m * (3 * m + 1) / 2 = b then 1 else 0)) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      have hm_le1 : b < m * (3 * m - 1) / 2 := by
        have h3 : 2 ≤ 3 * m - 1 := by omega
        have : m * 2 ≤ m * (3 * m - 1) := Nat.mul_le_mul_left m h3
        omega
      have hm_le2 : b < m * (3 * m + 1) / 2 := by
        have h3 : 2 ≤ 3 * m + 1 := by omega
        have : m * 2 ≤ m * (3 * m + 1) := Nat.mul_le_mul_left m h3
        omega
      simp [hm_le1.ne', hm_le2.ne']
    rw [hzero_hi, add_zero]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have hm1 : (-1 : ℝ) ^ m = -((-1 : ℝ) ^ (m - 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [pow_succ]
  have hs1 : (∑ b ∈ Finset.Icc 1 n, (partitionCount (n - b) : ℝ) *
      (if m * (3 * m - 1) / 2 = b then (1 : ℝ) else 0)) =
      if m * (3 * m - 1) / 2 ≤ n then (partitionCount (n - m * (3 * m - 1) / 2) : ℝ) else 0 := by
    have hp_pos : 1 ≤ m * (3 * m - 1) / 2 := by
      rcases eq_or_lt_of_le hm.1 with h1 | hgt
      · simp [← h1]
      · have h3 : 2 ≤ 3 * m - 1 := by omega
        have : m * 2 ≤ m * (3 * m - 1) := Nat.mul_le_mul_left m h3
        omega
    split_ifs with hle
    · rw [Finset.sum_eq_single (m * (3 * m - 1) / 2)]
      · simp
      · intro b _ hne; simp [Ne.symm hne]
      · intro hnot; exfalso; exact hnot (Finset.mem_Icc.mpr ⟨hp_pos, hle⟩)
    · refine Finset.sum_eq_zero fun b hb => ?_
      rw [Finset.mem_Icc] at hb
      have hne : m * (3 * m - 1) / 2 ≠ b := by omega
      simp [hne]
  have hs2 : (∑ b ∈ Finset.Icc 1 n, (partitionCount (n - b) : ℝ) *
      (if m * (3 * m + 1) / 2 = b then (1 : ℝ) else 0)) =
      if m * (3 * m + 1) / 2 ≤ n then (partitionCount (n - m * (3 * m + 1) / 2) : ℝ) else 0 := by
    have hp_pos : 1 ≤ m * (3 * m + 1) / 2 := by
      have h3 : 2 ≤ 3 * m + 1 := by omega
      have : m * 2 ≤ m * (3 * m + 1) := Nat.mul_le_mul_left m h3
      omega
    split_ifs with hle
    · rw [Finset.sum_eq_single (m * (3 * m + 1) / 2)]
      · simp
      · intro b _ hne; simp [Ne.symm hne]
      · intro hnot; exfalso; exact hnot (Finset.mem_Icc.mpr ⟨hp_pos, hle⟩)
    · refine Finset.sum_eq_zero fun b hb => ?_
      rw [Finset.mem_Icc] at hb
      have hne : m * (3 * m + 1) / 2 ≠ b := by omega
      simp [hne]
  have hsplit_sum :
      (∑ b ∈ Finset.Icc 1 n, (-1 : ℝ) ^ m * (partitionCount (n - b) : ℝ) *
        ((if m * (3 * m - 1) / 2 = b then 1 else 0) +
          (if m * (3 * m + 1) / 2 = b then 1 else 0))) =
        (-1 : ℝ) ^ m *
          ((∑ b ∈ Finset.Icc 1 n, (partitionCount (n - b) : ℝ) *
            (if m * (3 * m - 1) / 2 = b then 1 else 0)) +
           (∑ b ∈ Finset.Icc 1 n, (partitionCount (n - b) : ℝ) *
            (if m * (3 * m + 1) / 2 = b then 1 else 0))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit_sum, hs1, hs2, hm1]
  ring

/-- **Euler's Recurrence** for the partition function `p(n)`:
for `n ≥ 1`, `p(n) = ∑_{m=1}^n (-1) ^ (m - 1) * (p(n - m*(3m-1)/2) + p(n - m*(3m+1)/2))`
(omitting terms where the pentagonal index exceeds `n`). -/
theorem euler_partition_recurrence {n : ℕ} (hn : 1 ≤ n) :
    (partitionCount n : ℤ) =
      ∑ m ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (m - 1) *
        ((if m * (3 * m - 1) / 2 ≤ n then (partitionCount (n - m * (3 * m - 1) / 2) : ℤ) else 0) +
         (if m * (3 * m + 1) / 2 ≤ n then (partitionCount (n - m * (3 * m + 1) / 2) : ℤ) else 0)) := by
  have hs_half : Summable fun n : ℕ => |pentConvDiff n| * ((1 / 2 : ℝ) / 2) ^ n :=
    pentConvDiff_summ.congr fun n => by rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) / 2 by norm_num]
  have hdn := tsum_pow_eq_zero_imp_coeff_eq_zero (r := 1 / 2) (by norm_num) hs_half
    (fun _ hx => pentConvDiff_zero hx) n
  have hn0 : n ≠ 0 := by omega
  rw [pentConvDiff] at hdn
  simp only [hn0, ↓reduceIte, sub_zero, Finset.sum_range_succ, Nat.sub_self] at hdn
  have hc0 : pentRecCoeff 0 = 1 := by simp [pentRecCoeff]
  rw [hc0, mul_one] at hdn
  have hrew : ∑ k ∈ Finset.range n, (partitionCount k : ℝ) * pentRecCoeff (n - k) =
      ∑ b ∈ Finset.Icc 1 n, (partitionCount (n - b) : ℝ) * pentRecCoeff b := by
    refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
    · intro k₁ hk₁ k₂ hk₂ heq; rw [Finset.mem_range] at hk₁ hk₂; omega
    · intro b hb; rw [Finset.mem_Icc] at hb
      refine ⟨n - b, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk; rw [Finset.mem_range] at hk; rw [Nat.sub_sub_self hk.le]
  rw [hrew, pentConvDiff_sum_eq] at hdn
  have heqR : (partitionCount n : ℝ) =
      ∑ m ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (m - 1) *
        ((if m * (3 * m - 1) / 2 ≤ n then (partitionCount (n - m * (3 * m - 1) / 2) : ℝ) else 0) +
         (if m * (3 * m + 1) / 2 ≤ n then (partitionCount (n - m * (3 * m + 1) / 2) : ℝ) else 0)) := by
    linarith only [hdn]
  have heqCast :
      ((partitionCount n : ℤ) : ℝ) =
        ((∑ m ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (m - 1) *
          ((if m * (3 * m - 1) / 2 ≤ n then (partitionCount (n - m * (3 * m - 1) / 2) : ℤ) else 0) +
           (if m * (3 * m + 1) / 2 ≤ n then (partitionCount (n - m * (3 * m + 1) / 2) : ℤ) else 0)) : ℤ) : ℝ) := by
    push_cast
    refine heqR.trans (Finset.sum_congr rfl fun m _ => ?_)
    split_ifs <;> simp
  exact Int.cast_inj.mp heqCast

end JacobiTripleProductAndPentagonal

section AsymptoticBounds

/-- Positivity of `partitionGenFunReal x` for `0 ≤ x < 1`. -/
theorem partitionGenFunReal_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < partitionGenFunReal x := by
  have hx : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have hm := multipliable_one_sub_pow_real hx
  have hne := tprod_one_sub_pow_real_ne_zero hx
  have hnonneg : 0 ≤ ∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) := by
    refine ge_of_tendsto hm.hasProd (Eventually.of_forall fun s => Finset.prod_nonneg fun k _ => ?_)
    have : x ^ (k + 1) ≤ 1 := pow_le_one₀ hx0 hx1.le
    linarith
  have hpos : 0 < ∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1)) := lt_of_le_of_ne hnonneg (Ne.symm hne)
  exact inv_pos.mpr hpos

/-- For `0 ≤ x < 1`, `-Real.log (1 - x ^ (k + 1))` has the Taylor series `∑' m : ℕ+, x ^ ((k + 1) * m) / m`. -/
private lemma hasSum_neg_log_one_sub_pow {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasSum (fun m : ℕ => y ^ (m + 1) / ((m : ℝ) + 1)) (-Real.log (1 - y)) := by
  have hyC : ‖(y : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0] using hy1
  have hC := Complex.hasSum_taylorSeries_neg_log' hyC
  have hlog_re : (-Complex.log (1 - (y : ℂ))).re = -Real.log (1 - y) := by
    have hpos : 0 < 1 - y := by linarith
    have hc : (1 : ℂ) - (y : ℂ) = ((1 - y : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, ← Complex.ofReal_log hpos.le, Complex.neg_re, Complex.ofReal_re]
  have hc := (Complex.continuous_re.tendsto _).comp hC
  rw [hlog_re] at hc
  exact hc.congr fun s => by
    simp only [Function.comp_apply, Complex.re_sum, ← Complex.ofReal_natCast,
      ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_pow,
      ← Complex.ofReal_div, Complex.ofReal_re]

/-- Exact series formula for the logarithm of the partition generating function at `x = exp (-t)`:
for `t > 0`, `Real.log (partitionGenFunReal (Real.exp (-t))) = ∑' m : ℕ+, 1 / (m * (Real.exp (m * t) - 1))`. -/
theorem log_partitionGenFunReal_eq_tsum {t : ℝ} (ht : 0 < t) :
    Real.log (partitionGenFunReal (Real.exp (-t))) =
      ∑' m : ℕ+, (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) := by
  set x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos (-t)
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hx_abs : |x| < 1 := by rwa [abs_of_pos hx0]
  have hfac_pos : ∀ k : ℕ, 0 < (1 : ℝ) - x ^ (k + 1) := fun k => by
    have : x ^ (k + 1) < 1 := pow_lt_one₀ hx0.le hx1 (Nat.succ_ne_zero k)
    linarith
  have hm := multipliable_one_sub_pow_real hx_abs
  have hne := tprod_one_sub_pow_real_ne_zero hx_abs
  have hlog_prod :
      HasSum (fun k : ℕ => -Real.log ((1 : ℝ) - x ^ (k + 1)))
        (Real.log (partitionGenFunReal x)) := by
    have hcont : ContinuousAt Real.log (∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1))) :=
      Real.continuousAt_log hne
    have htend := (hcont.tendsto.comp hm.hasProd).neg
    have hlog_inv : -Real.log (∏' k : ℕ, ((1 : ℝ) - x ^ (k + 1))) = Real.log (partitionGenFunReal x) := by
      rw [partitionGenFunReal, Real.log_inv]
    rw [hlog_inv] at htend
    refine htend.congr fun s => ?_
    dsimp only [Function.comp_apply]
    rw [Real.log_prod (fun k _ => (hfac_pos k).ne'), Finset.sum_neg_distrib]
  have hlog_eq : Real.log (partitionGenFunReal x) = ∑' k : ℕ, -Real.log ((1 : ℝ) - x ^ (k + 1)) :=
    hlog_prod.tsum_eq.symm
  have hdouble_summ : Summable fun p : ℕ × ℕ => x ^ ((p.1 + 1) * (p.2 + 1)) / ((p.2 : ℝ) + 1) := by
    have hg1 : Summable fun k : ℕ => x ^ (k + 1) :=
      (summable_geometric_of_lt_one hx0.le hx1).mul_right x |>.congr fun k => by rw [pow_succ]
    have hg2 : Summable fun m : ℕ => x ^ m := summable_geometric_of_lt_one hx0.le hx1
    have hprod_s : Summable fun p : ℕ × ℕ => x ^ (p.1 + 1) * x ^ p.2 :=
      hg1.mul_of_nonneg hg2 (fun _ => pow_nonneg hx0.le _) (fun _ => pow_nonneg hx0.le _)
    refine hprod_s.of_nonneg_of_le (fun _ => by positivity) fun ⟨k, m⟩ => ?_
    have hexp : k + 1 + m ≤ (k + 1) * (m + 1) := by nlinarith
    have hle1 : x ^ ((k + 1) * (m + 1)) ≤ x ^ (k + 1 + m) :=
      pow_le_pow_of_le_one hx0.le hx1.le hexp
    have hden : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    calc x ^ ((k + 1) * (m + 1)) / ((m : ℝ) + 1)
        ≤ x ^ ((k + 1) * (m + 1)) / 1 := div_le_div_of_nonneg_left (pow_nonneg hx0.le _) (by norm_num) hden
      _ = x ^ ((k + 1) * (m + 1)) := div_one _
      _ ≤ x ^ (k + 1 + m) := hle1
      _ = x ^ (k + 1) * x ^ m := pow_add x (k + 1) m
  have hterm_log : ∀ k : ℕ, -Real.log ((1 : ℝ) - x ^ (k + 1)) =
      ∑' m : ℕ, x ^ ((k + 1) * (m + 1)) / ((m : ℝ) + 1) := by
    intro k
    have hy0 : 0 ≤ x ^ (k + 1) := pow_nonneg hx0.le _
    have hy1 : x ^ (k + 1) < 1 := pow_lt_one₀ hx0.le hx1 (Nat.succ_ne_zero k)
    have hs := hasSum_neg_log_one_sub_pow hy0 hy1
    rw [← hs.tsum_eq]
    refine tsum_congr fun m => by rw [pow_mul]
  rw [hlog_eq]
  simp_rw [hterm_log]
  let F : ℕ → ℕ → ℝ := fun k m => x ^ ((k + 1) * (m + 1)) / ((m : ℝ) + 1)
  have hF : Summable (Function.uncurry F) := hdouble_summ
  change (∑' k : ℕ, ∑' m : ℕ, F k m) = _
  rw [← hF.tsum_comm]
  have hinner : ∀ m : ℕ,
      (∑' k : ℕ, x ^ ((k + 1) * (m + 1)) / ((m : ℝ) + 1)) =
        (1 : ℝ) / (((m : ℝ) + 1) * (Real.exp (((m : ℝ) + 1) * t) - 1)) := by
    intro m
    have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hxm1 : x ^ (m + 1) < 1 := pow_lt_one₀ hx0.le hx1 (Nat.succ_ne_zero m)
    have hgeom := (hasSum_geometric_of_lt_one (pow_nonneg hx0.le (m + 1)) hxm1).tsum_eq
    have hdiv : (∑' k : ℕ, x ^ ((k + 1) * (m + 1)) / ((m : ℝ) + 1)) =
        (x ^ (m + 1) / (1 - x ^ (m + 1))) / ((m : ℝ) + 1) := by
      have heq : ∀ k : ℕ, x ^ ((k + 1) * (m + 1)) / ((m : ℝ) + 1) =
          ((x ^ (m + 1)) ^ k * x ^ (m + 1)) / ((m : ℝ) + 1) := fun k => by
        rw [add_mul, one_mul, pow_add, mul_comm k (m + 1), pow_mul]
      rw [tsum_congr heq, tsum_div_const, tsum_mul_right, hgeom]
      ring
    rw [hdiv]
    have hexp_mul : x ^ (m + 1) = Real.exp (-(((m : ℝ) + 1) * t)) := by
      dsimp [x]
      rw [← Real.exp_nat_mul]
      congr 1; push_cast; ring
    have hexp_inv : x ^ (m + 1) = (Real.exp (((m : ℝ) + 1) * t))⁻¹ := by
      rw [hexp_mul, Real.exp_neg]
    have hexp_gt : 1 < Real.exp (((m : ℝ) + 1) * t) :=
      Real.one_lt_exp_iff.mpr (mul_pos hm_pos ht)
    rw [hexp_inv]
    field_simp [show Real.exp (((m : ℝ) + 1) * t) ≠ 0 by positivity,
      show Real.exp (((m : ℝ) + 1) * t) - 1 ≠ 0 by linarith]
  dsimp only [F]
  simp_rw [hinner]
  let e : ℕ ≃ ℕ+ :=
    { toFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
      invFun := fun p => (p : ℕ) - 1
      left_inv := fun m => by simp
      right_inv := fun p => PNat.eq (by have := p.pos; dsimp; omega) }
  rw [← e.tsum_eq (fun p : ℕ+ => (1 : ℝ) / ((p : ℝ) * (Real.exp ((p : ℝ) * t) - 1)))]
  refine tsum_congr fun m => ?_
  change (1 : ℝ) / (((m : ℝ) + 1) * (Real.exp (((m : ℝ) + 1) * t) - 1)) =
    (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * (Real.exp (((m + 1 : ℕ) : ℝ) * t) - 1))
  push_cast; rfl

/-- Saddle-point upper bound: for `t > 0`,
`Real.log (partitionGenFunReal (Real.exp (-t))) < Real.pi ^ 2 / (6 * t)`. -/
theorem log_partitionGenFunReal_lt {t : ℝ} (ht : 0 < t) :
    Real.log (partitionGenFunReal (Real.exp (-t))) < Real.pi ^ 2 / (6 * t) := by
  rw [log_partitionGenFunReal_eq_tsum ht]
  have hzeta : HasSum (fun m : ℕ+ => (1 : ℝ) / ((m : ℝ) ^ 2 * t)) (Real.pi ^ 2 / (6 * t)) := by
    have hz := hasSum_zeta_two
    have h1 : HasSum (fun m : ℕ => ((1 : ℝ) / (m : ℝ) ^ 2) / t) ((Real.pi ^ 2 / 6) / t) :=
      hz.div_const t
    have h2 : HasSum (fun m : ℕ => (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * t)) (Real.pi ^ 2 / (6 * t)) := by
      have h1' : HasSum (fun m : ℕ => ((1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2) / t) (Real.pi ^ 2 / (6 * t)) := by
        rw [hasSum_nat_add_iff 1 (f := fun m : ℕ => ((1 : ℝ) / (m : ℝ) ^ 2) / t)]
        rw [div_div] at h1
        simpa using h1
      refine h1'.congr_fun fun m => ?_
      push_cast
      rw [div_div, add_comm (m : ℝ) 1]
    let e : ℕ ≃ ℕ+ :=
      { toFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
        invFun := fun p => (p : ℕ) - 1
        left_inv := fun m => by simp
        right_inv := fun p => PNat.eq (by have := p.pos; dsimp; omega) }
    refine (e.hasSum_iff (f := fun m : ℕ+ => (1 : ℝ) / ((m : ℝ) ^ 2 * t))).mp ?_
    refine h2.congr_fun fun m => ?_
    change (1 : ℝ) / (((m + 1 : ℕ) : ℝ) ^ 2 * t) = (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * t)
    push_cast; rfl
  have hterm_lt : ∀ m : ℕ+,
      (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) < (1 : ℝ) / ((m : ℝ) ^ 2 * t) := by
    intro m
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hmt_pos : 0 < (m : ℝ) * t := mul_pos hm_pos ht
    have hexp_gt : (m : ℝ) * t < Real.exp ((m : ℝ) * t) - 1 := by
      linarith [Real.add_one_lt_exp hmt_pos.ne']
    have hden : (m : ℝ) ^ 2 * t < (m : ℝ) * (Real.exp ((m : ℝ) * t) - 1) := by
      nlinarith
    exact one_div_lt_one_div_of_lt (by positivity) hden
  have hsumm1 : Summable fun m : ℕ+ => (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) := by
    refine hzeta.summable.of_nonneg_of_le (fun m => ?_) fun m => (hterm_lt m).le
    have hmt : 0 < (m : ℝ) * t := by positivity
    have : 1 < Real.exp ((m : ℝ) * t) := Real.one_lt_exp_iff.mpr hmt
    positivity
  have hle : ∑' m : ℕ+, (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) ≤
      ∑' m : ℕ+, (1 : ℝ) / ((m : ℝ) ^ 2 * t) :=
    hsumm1.tsum_le_tsum (fun m => (hterm_lt m).le) hzeta.summable
  have hne : ∑' m : ℕ+, (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) ≠
      ∑' m : ℕ+, (1 : ℝ) / ((m : ℝ) ^ 2 * t) := by
    intro heq
    have hdiff_zero :
        ∑' m : ℕ+, ((1 : ℝ) / ((m : ℝ) ^ 2 * t) -
          (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1))) = 0 := by
      rw [hzeta.summable.tsum_sub hsumm1, heq, sub_self]
    have hpos1 : (0 : ℝ) < (1 : ℝ) / ((1 : ℝ) ^ 2 * t) -
        (1 : ℝ) / ((1 : ℝ) * (Real.exp ((1 : ℝ) * t) - 1)) :=
      sub_pos.mpr (hterm_lt 1)
    have hle_sum :
        (1 : ℝ) / ((1 : ℝ) ^ 2 * t) - (1 : ℝ) / ((1 : ℝ) * (Real.exp ((1 : ℝ) * t) - 1)) ≤
          ∑' m : ℕ+, ((1 : ℝ) / ((m : ℝ) ^ 2 * t) -
            (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1))) := by
      have hsumm_diff := hzeta.summable.sub hsumm1
      have h1 : (1 : ℝ) / ((1 : ℝ) ^ 2 * t) - (1 : ℝ) / ((1 : ℝ) * (Real.exp ((1 : ℝ) * t) - 1)) =
          ∑ m ∈ ({1} : Finset ℕ+),
            ((1 : ℝ) / ((m : ℝ) ^ 2 * t) - (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1))) := by
        simp
      rw [h1]
      exact hsumm_diff.sum_le_tsum _ fun m _ => sub_nonneg.mpr (hterm_lt m).le
    linarith
  rw [hzeta.tsum_eq] at hle hne
  exact lt_of_le_of_ne hle hne

/-- Saddle-point lower bound: for `0 < t ≤ 1 / 2`,
`Real.pi ^ 2 / (6 * t) - Real.log (1 / t) - 3 ≤ Real.log (partitionGenFunReal (Real.exp (-t)))`. -/
theorem log_partitionGenFunReal_ge {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    Real.pi ^ 2 / (6 * t) - Real.log (1 / t) - 3 ≤
      Real.log (partitionGenFunReal (Real.exp (-t))) := by
  rw [log_partitionGenFunReal_eq_tsum ht0]
  have hzeta : Summable fun m : ℕ+ => (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) := by
    have hz := hasSum_zeta_two.summable
    have h1 : Summable fun m : ℕ => (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * t) := by
      have hz' : Summable fun m : ℕ => ((1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2) / t :=
        (summable_nat_add_iff 1 (f := fun m : ℕ => ((1 : ℝ) / (m : ℝ) ^ 2) / t)).mpr (hz.div_const t)
      refine hz'.congr fun m => ?_
      push_cast
      rw [div_div, add_comm (m : ℝ) 1]
    let e : ℕ ≃ ℕ+ :=
      { toFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
        invFun := fun p => (p : ℕ) - 1
        left_inv := fun m => by simp
        right_inv := fun p => PNat.eq (by have := p.pos; dsimp; omega) }
    have h2 : Summable fun m : ℕ+ => (1 : ℝ) / ((m : ℝ) ^ 2 * t) :=
      (e.summable_iff (f := fun m : ℕ+ => (1 : ℝ) / ((m : ℝ) ^ 2 * t))).mp
        (h1.congr fun m => by
          change (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * t) = (1 : ℝ) / (((m + 1 : ℕ) : ℝ) ^ 2 * t)
          push_cast; rfl)
    refine h2.of_nonneg_of_le (fun m => by
      have : 1 < Real.exp ((m : ℝ) * t) := Real.one_lt_exp_iff.mpr (by positivity)
      positivity) fun m => ?_
    have hmt : 0 < (m : ℝ) * t := by positivity
    have hexp_gt : (m : ℝ) * t < Real.exp ((m : ℝ) * t) - 1 := by
      linarith [Real.add_one_lt_exp hmt.ne']
    have hden : (m : ℝ) ^ 2 * t ≤ (m : ℝ) * (Real.exp ((m : ℝ) * t) - 1) := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) hden
  set K : ℕ := Nat.floor (1 / t)
  have hK1 : 2 ≤ K := by
    have h2 : (2 : ℝ) ≤ 1 / t := by
      rw [le_div_iff₀ ht0]; linarith
    exact Nat.le_floor h2
  have hK_gt : 1 / t < (K : ℝ) + 1 := Nat.lt_floor_add_one (1 / t)
  let S : Finset ℕ+ := (Finset.Icc 1 K).attach.map
    ⟨fun m => ⟨m.1, (Finset.mem_Icc.mp m.2).1⟩, fun a b h => by ext; simpa using congrArg PNat.val h⟩
  have hsum_le_tsum :
      ∑ m ∈ S, (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) ≤
        ∑' m : ℕ+, (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) :=
    hzeta.sum_le_tsum S fun m _ => by
      have : 1 < Real.exp ((m : ℝ) * t) := Real.one_lt_exp_iff.mpr (by positivity)
      positivity
  have hterm_ge : ∀ m : ℕ+,
      (1 : ℝ) / ((m : ℝ) ^ 2 * t) - (1 : ℝ) / (m : ℝ) ≤
        (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) := by
    intro m
    have hmt : 0 < (m : ℝ) * t := by positivity
    have hexp_pos : 0 < Real.exp ((m : ℝ) * t) - 1 := by
      linarith [Real.one_lt_exp_iff.mpr hmt]
    have h1 : (1 - (m : ℝ) * t) * Real.exp ((m : ℝ) * t) ≤ 1 := by
      have hneg := Real.add_one_le_exp (-((m : ℝ) * t))
      rw [Real.exp_neg] at hneg
      have hexp0 : 0 < Real.exp ((m : ℝ) * t) := Real.exp_pos _
      rw [← one_div, le_div_iff₀ hexp0] at hneg
      linarith
    have hineq : (m : ℝ) * t ≥ (1 - (m : ℝ) * t) * (Real.exp ((m : ℝ) * t) - 1) := by linarith
    have hinv_le : 1 / ((m : ℝ) * t) - 1 ≤ 1 / (Real.exp ((m : ℝ) * t) - 1) := by
      rw [sub_le_iff_le_add, one_div, one_div]
      field_simp [hmt.ne', hexp_pos.ne']
      linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    calc (1 : ℝ) / ((m : ℝ) ^ 2 * t) - (1 : ℝ) / (m : ℝ)
        = (1 / ((m : ℝ) * t) - 1) / (m : ℝ) := by field_simp [hm_pos.ne', ht0.ne']
      _ ≤ (1 / (Real.exp ((m : ℝ) * t) - 1)) / (m : ℝ) :=
          div_le_div_of_nonneg_right hinv_le hm_pos.le
      _ = (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) := by rw [div_div, mul_comm]
  have hsum_Icc :
      ∑ m ∈ S, ((1 : ℝ) / ((m : ℝ) ^ 2 * t) - (1 : ℝ) / (m : ℝ)) =
        (1 / t) * (∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2) -
          ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) := by
    have heq1 : ∀ (f : ℕ → ℝ),
        (∑ m ∈ S, f (m : ℕ)) = ∑ m ∈ Finset.Icc 1 K, f m := by
      intro f
      dsimp [S]
      simp only [Finset.sum_map]
      exact Finset.sum_attach (Finset.Icc 1 K) f
    rw [Finset.sum_sub_distrib, heq1 (fun m => (1 : ℝ) / ((m : ℝ) ^ 2 * t)),
        heq1 (fun m => (1 : ℝ) / (m : ℝ))]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by ring
  have hzeta_tail :
      Real.pi ^ 2 / 6 - 1 / (K : ℝ) ≤ ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 := by
    have hz := hasSum_zeta_two
    have hsplit := hz.summable.sum_add_tsum_nat_add (K + 1)
    rw [hz.tsum_eq] at hsplit
    have hhead : ∑ i ∈ Finset.range (K + 1), (1 : ℝ) / (i : ℝ) ^ 2 =
        ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 := by
      rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos K), Nat.cast_zero, sq, mul_zero, div_zero,
          zero_add]
      have hIco : Finset.Ico 1 (K + 1) = Finset.Icc 1 K := by
        ext m; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [hIco]
    have htail_le : ∑' i : ℕ, (1 : ℝ) / ((i + (K + 1) : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
      have htele : HasSum (fun i : ℕ => (1 : ℝ) / ((i + K : ℕ) : ℝ) - 1 / ((i + K + 1 : ℕ) : ℝ))
          (1 / (K : ℝ)) := by
        have hKpos : (0 : ℝ) < K := by positivity
        have hlim : Tendsto (fun N : ℕ => (1 : ℝ) / (K : ℝ) - 1 / ((N + K : ℕ) : ℝ))
            atTop (𝓝 (1 / (K : ℝ))) := by
          have ht0' : Tendsto (fun N : ℕ => (1 : ℝ) / ((N + K : ℕ) : ℝ)) atTop (𝓝 0) := by
            refine tendsto_const_nhds.div_atTop ?_
            exact tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun N => Nat.le_add_right N K) tendsto_id)
          simpa using tendsto_const_nhds.sub ht0'
        rw [hasSum_iff_tendsto_nat_of_nonneg]
        · refine hlim.congr fun N => ?_
          induction N with
          | zero => simp
          | succ n ihn =>
            rw [Finset.sum_range_succ, ← ihn, show n + 1 + K = n + K + 1 by omega]
            push_cast
            ring
        · intro i
          have h1 : (K : ℝ) ≤ (i + K : ℕ) := by exact_mod_cast Nat.le_add_left K i
          have h2 : ((i + K : ℕ) : ℝ) ≤ ((i + K + 1 : ℕ) : ℝ) := by push_cast; linarith
          exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) h2)
      have hs_t : Summable fun i : ℕ => (1 : ℝ) / ((i + (K + 1) : ℕ) : ℝ) ^ 2 :=
        (summable_nat_add_iff (K + 1)).mpr hz.summable
      have hle_i : ∀ i : ℕ,
          (1 : ℝ) / ((i + (K + 1) : ℕ) : ℝ) ^ 2 ≤
            (1 : ℝ) / ((i + K : ℕ) : ℝ) - 1 / ((i + K + 1 : ℕ) : ℝ) := by
        intro i
        have h1 : (0 : ℝ) < ((i + K : ℕ) : ℝ) := by
          have : 1 ≤ i + K := by omega
          exact_mod_cast this
        have h2 : ((i + K + 1 : ℕ) : ℝ) = ((i + K : ℕ) : ℝ) + 1 := by push_cast; ring
        have h3 : ((i + (K + 1) : ℕ) : ℝ) = ((i + K + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [h3, h2]
        have hnum : 1 / ((i + K : ℕ) : ℝ) - 1 / (((i + K : ℕ) : ℝ) + 1) =
            1 / (((i + K : ℕ) : ℝ) * (((i + K : ℕ) : ℝ) + 1)) := by
          field_simp [h1.ne', show ((i + K : ℕ) : ℝ) + 1 ≠ 0 by positivity]
          ring
        rw [hnum]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      exact (hs_t.tsum_le_tsum hle_i htele.summable).trans_eq htele.tsum_eq
    rw [hhead] at hsplit
    linarith
  have hharm_le : ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log (K : ℝ) := by
    have hlog_step : ∀ m : ℕ, 1 ≤ m → (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      intro m hm
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
      have h1 : Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) = Real.log (m : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) :=
        Real.log_div hm_pos.ne' (by positivity)
      have h3 : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp [show (m : ℝ) + 1 ≠ 0 by positivity]; ring
      linarith
    have hind : ∀ N : ℕ, 1 ≤ N → ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log (N : ℝ) := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hsplit, Finset.sum_insert (by simp)]
        linarith [ih, hlog_step k hk]
    exact hind K (by omega)
  have hK_le : (K : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have hlogK_le : Real.log (K : ℝ) ≤ Real.log (1 / t) :=
    Real.log_le_log (by positivity) hK_le
  have ht_inv_k : (1 / t) * (1 / (K : ℝ)) ≤ 2 := by
    have hK_gt' : 1 < ((K : ℝ) + 1) * t := (div_lt_iff₀ ht0).mp hK_gt
    have h2 : (2 : ℝ) ≤ K := by exact_mod_cast hK1
    rw [div_mul_div_comm, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  calc Real.pi ^ 2 / (6 * t) - Real.log (1 / t) - 3
      ≤ (1 / t) * (Real.pi ^ 2 / 6 - 1 / (K : ℝ)) - (1 + Real.log (K : ℝ)) := by
        have hcalc : (1 / t) * (Real.pi ^ 2 / 6 - 1 / (K : ℝ)) - (1 + Real.log (K : ℝ)) =
            Real.pi ^ 2 / (6 * t) - (1 / t) * (1 / (K : ℝ)) - 1 - Real.log (K : ℝ) := by ring
        rw [hcalc]
        linarith
    _ ≤ (1 / t) * (∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2) -
          ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) := by
        gcongr
    _ = ∑ m ∈ S, ((1 : ℝ) / ((m : ℝ) ^ 2 * t) - (1 : ℝ) / (m : ℝ)) := hsum_Icc.symm
    _ ≤ ∑ m ∈ S, (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) :=
        Finset.sum_le_sum fun m _ => hterm_ge m
    _ ≤ ∑' m : ℕ+, (1 : ℝ) / ((m : ℝ) * (Real.exp ((m : ℝ) * t) - 1)) := hsum_le_tsum

/-- **Elementary Saddle-Point Upper Bound**:
for all `n ≥ 1`, `partitionCount n < Real.exp (Real.pi * Real.sqrt (2 * n / 3))`. -/
theorem partitionCount_lt_exp {n : ℕ} (hn : 1 ≤ n) :
    (partitionCount n : ℝ) < Real.exp (Real.pi * Real.sqrt (2 * (n : ℝ) / 3)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := Real.pi / Real.sqrt (6 * (n : ℝ))
  have ht : 0 < t := by positivity
  set x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hx_abs : |x| < 1 := by rwa [abs_of_pos hx0]
  have hs := summable_partitionCount_mul_pow_real hx0.le hx1
  have hgen := tsum_partitionCount_mul_pow_real hx_abs
  have hstrict : (partitionCount n : ℝ) * x ^ n < partitionGenFunReal x := by
    have h0_pos : 0 < (partitionCount 0 : ℝ) * x ^ 0 := by simp
    have hsub : (partitionCount 0 : ℝ) * x ^ 0 + (partitionCount n : ℝ) * x ^ n ≤
        ∑' m : ℕ, (partitionCount m : ℝ) * x ^ m := by
      have hset : ∑ m ∈ ({0, n} : Finset ℕ), (partitionCount m : ℝ) * x ^ m =
          (partitionCount 0 : ℝ) * x ^ 0 + (partitionCount n : ℝ) * x ^ n := by
        rw [Finset.sum_pair (by omega)]
      rw [← hset]
      exact hs.sum_le_tsum {0, n} fun m _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0.le _)
    rw [hgen] at hsub
    change (partitionCount 0 : ℝ) * x ^ 0 + (partitionCount n : ℝ) * x ^ n ≤ partitionGenFunReal x at hsub
    linarith
  have hlog : Real.log ((partitionCount n : ℝ) * x ^ n) < Real.log (partitionGenFunReal x) :=
    Real.log_lt_log (mul_pos (by exact_mod_cast partitionCount_pos n) (pow_pos hx0 n)) hstrict
  have hlog_lhs : Real.log ((partitionCount n : ℝ) * x ^ n) =
      Real.log (partitionCount n : ℝ) - (n : ℝ) * t := by
    rw [Real.log_mul (by exact_mod_cast (partitionCount_pos n).ne') (pow_ne_zero n hx0.ne'),
        Real.log_pow, Real.log_exp]
    ring
  have hlog_ub := log_partitionGenFunReal_lt ht
  have hpi_eq : (n : ℝ) * t + Real.pi ^ 2 / (6 * t) = Real.pi * Real.sqrt (2 * (n : ℝ) / 3) := by
    dsimp [t]
    have hsq6 : Real.sqrt (6 * (n : ℝ)) ≠ 0 := by positivity
    have hcalc1 : (n : ℝ) * (Real.pi / Real.sqrt (6 * (n : ℝ))) +
        Real.pi ^ 2 / (6 * (Real.pi / Real.sqrt (6 * (n : ℝ)))) =
        Real.pi * ((n : ℝ) / Real.sqrt (6 * (n : ℝ)) + Real.sqrt (6 * (n : ℝ)) / 6) := by
      field_simp [hsq6, Real.pi_ne_zero]
    have hcalc2 : (n : ℝ) / Real.sqrt (6 * (n : ℝ)) + Real.sqrt (6 * (n : ℝ)) / 6 =
        Real.sqrt (2 * (n : ℝ) / 3) := by
      have hsq_pos : 0 < Real.sqrt (6 * (n : ℝ)) := by positivity
      have hsq_sq : Real.sqrt (6 * (n : ℝ)) ^ 2 = 6 * (n : ℝ) := Real.sq_sqrt (by positivity)
      have hr : (n : ℝ) / Real.sqrt (6 * (n : ℝ)) + Real.sqrt (6 * (n : ℝ)) / 6 =
          Real.sqrt (6 * (n : ℝ)) / 3 := by
        have hnum : 6 * (n : ℝ) + Real.sqrt (6 * (n : ℝ)) ^ 2 =
            2 * Real.sqrt (6 * (n : ℝ)) ^ 2 := by linarith [hsq_sq]
        calc (n : ℝ) / Real.sqrt (6 * (n : ℝ)) + Real.sqrt (6 * (n : ℝ)) / 6
            = (6 * (n : ℝ) + Real.sqrt (6 * (n : ℝ)) ^ 2) / (6 * Real.sqrt (6 * (n : ℝ))) := by
              field_simp [hsq_pos.ne']
          _ = (2 * Real.sqrt (6 * (n : ℝ)) ^ 2) / (6 * Real.sqrt (6 * (n : ℝ))) := by
              rw [hnum]
          _ = Real.sqrt (6 * (n : ℝ)) / 3 := by
              field_simp [hsq_pos.ne']; ring
      rw [hr]
      have h23 : Real.sqrt (6 * (n : ℝ)) = 3 * Real.sqrt (2 * (n : ℝ) / 3) := by
        rw [show (6 * (n : ℝ)) = 3 ^ 2 * (2 * (n : ℝ) / 3) by ring,
            Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      rw [h23]
      ring
    rw [hcalc1, hcalc2]
  have hlog_p : Real.log (partitionCount n : ℝ) < Real.pi * Real.sqrt (2 * (n : ℝ) / 3) := by
    linarith [hlog, hlog_lhs, hlog_ub, hpi_eq]
  calc (partitionCount n : ℝ) = Real.exp (Real.log (partitionCount n : ℝ)) :=
        (Real.exp_log (by exact_mod_cast partitionCount_pos n)).symm
    _ < Real.exp (Real.pi * Real.sqrt (2 * (n : ℝ) / 3)) := Real.exp_lt_exp.mpr hlog_p

/-- Non-strict upper bound `partitionCount n ≤ Real.exp (Real.pi * Real.sqrt (2 * n / 3))`
for all `n : ℕ`. -/
theorem partitionCount_le_exp (n : ℕ) :
    (partitionCount n : ℝ) ≤ Real.exp (Real.pi * Real.sqrt (2 * (n : ℝ) / 3)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (partitionCount_lt_exp hn).le

/-- Combinatorial lower bound `2 ^ (Nat.sqrt n / 2) ≤ partitionCount n` for all `n : ℕ`. -/
theorem two_pow_le_partitionCount (n : ℕ) :
    2 ^ (Nat.sqrt n / 2) ≤ partitionCount n := by
  set m : ℕ := Nat.sqrt n / 2
  have hm_sq : 4 * m ^ 2 ≤ n := by
    have h1 : 2 * m ≤ Nat.sqrt n := Nat.mul_div_le (Nat.sqrt n) 2
    have h2 : (Nat.sqrt n) ^ 2 ≤ n := by simpa [sq] using Nat.sqrt_le n
    nlinarith
  have hm_sum : ∑ i ∈ Finset.Icc 2 (m + 1), i ≤ n := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · simp [hm0]
    · have hsum_le : ∑ i ∈ Finset.Icc 2 (m + 1), i ≤ m * (m + 1) := by
        have hconst : ∑ _i ∈ Finset.Icc 2 (m + 1), (m + 1) = m * (m + 1) := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]; rfl
        calc ∑ i ∈ Finset.Icc 2 (m + 1), i
            ≤ ∑ _i ∈ Finset.Icc 2 (m + 1), (m + 1) :=
              Finset.sum_le_sum fun i hi => (Finset.mem_Icc.mp hi).2
          _ = m * (m + 1) := hconst
      have h4m : m * (m + 1) ≤ 4 * m ^ 2 := by nlinarith
      exact hsum_le.trans (h4m.trans hm_sq)
  have hcard_pow : (Finset.Icc 2 (m + 1)).powerset.card = 2 ^ m := by
    rw [Finset.card_powerset, Nat.card_Icc]
    rfl
  rw [← hcard_pow, partitionCount]
  let f : {S : Finset ℕ // S ∈ (Finset.Icc 2 (m + 1)).powerset} → Nat.Partition n :=
    fun S =>
      { parts := S.1.val + Multiset.replicate (n - ∑ i ∈ S.1, i) 1
        parts_pos := fun {a} ha => by
          rcases Multiset.mem_add.mp ha with haS | ha1
          · have hmem : a ∈ Finset.Icc 2 (m + 1) :=
              Finset.mem_powerset.mp S.2 (Finset.mem_def.mpr haS)
            have h2 := (Finset.mem_Icc.mp hmem).1
            omega
          · rw [(Multiset.mem_replicate.mp ha1).2]; norm_num
        parts_sum := by
          have hsub : S.1 ⊆ Finset.Icc 2 (m + 1) := Finset.mem_powerset.mp S.2
          have hle : ∑ i ∈ S.1, i ≤ n :=
            (Finset.sum_le_sum_of_subset hsub).trans hm_sum
          rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
          have hS_sum : ∑ i ∈ S.1, i = S.1.val.sum := by
            rw [Finset.sum, Multiset.map_id']
          rw [← hS_sum]
          omega }
  have hinj : Function.Injective f := by
    intro S₁ S₂ heq
    have hparts := congrArg Nat.Partition.parts heq
    have hfilt := congrArg (Multiset.filter (· ≠ 1)) hparts
    have hf1 : (S₁.1.val + Multiset.replicate (n - ∑ i ∈ S₁.1, i) 1).filter (· ≠ 1) = S₁.1.val := by
      rw [Multiset.filter_add, Multiset.filter_eq_self.mpr, Multiset.filter_eq_nil.mpr, add_zero]
      · intro a ha; simp [(Multiset.mem_replicate.mp ha).2]
      · intro a ha
        have hmem := Finset.mem_Icc.mp (Finset.mem_powerset.mp S₁.2 (Finset.mem_def.mpr ha))
        omega
    have hf2 : (S₂.1.val + Multiset.replicate (n - ∑ i ∈ S₂.1, i) 1).filter (· ≠ 1) = S₂.1.val := by
      rw [Multiset.filter_add, Multiset.filter_eq_self.mpr, Multiset.filter_eq_nil.mpr, add_zero]
      · intro a ha; simp [(Multiset.mem_replicate.mp ha).2]
      · intro a ha
        have hmem := Finset.mem_Icc.mp (Finset.mem_powerset.mp S₂.2 (Finset.mem_def.mpr ha))
        omega
    dsimp [f] at hfilt
    rw [hf1, hf2] at hfilt
    exact Subtype.ext (Finset.val_inj.mp hfilt)
  simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Exponential lower bound for `n ≥ 4`:
`Real.exp ((Real.log 2 / 4) * Real.sqrt n) ≤ partitionCount n`. -/
theorem exp_sqrt_le_partitionCount {n : ℕ} (hn : 4 ≤ n) :
    Real.exp ((Real.log 2 / 4) * Real.sqrt (n : ℝ)) ≤ (partitionCount n : ℝ) := by
  set s : ℕ := Nat.sqrt n
  have hs_ge2 : 2 ≤ s := by
    have : 2 ^ 2 ≤ n := by omega
    exact Nat.le_sqrt.mpr this
  have hlt : n < (s + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt n
  have hs_bound : s + 1 ≤ 4 * (s / 2) := by omega
  have hn_lt_sq : (n : ℝ) < (4 * ((s / 2 : ℕ) : ℝ)) ^ 2 := by
    have h1 : n < (4 * (s / 2)) ^ 2 := lt_of_lt_of_le hlt (Nat.pow_le_pow_left hs_bound 2)
    exact_mod_cast h1
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ 4 * ((s / 2 : ℕ) : ℝ) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, hn_lt_sq.le⟩
  have hpow : (2 : ℝ) ^ (s / 2) ≤ (partitionCount n : ℝ) := by
    exact_mod_cast two_pow_le_partitionCount n
  have hexp_eq : Real.exp (((s / 2 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ (s / 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hexp_le : Real.exp ((Real.log 2 / 4) * Real.sqrt (n : ℝ)) ≤
      Real.exp (((s / 2 : ℕ) : ℝ) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  exact hexp_le.trans (hexp_eq.le.trans hpow)

/-- Logarithmic lower bound for `n ≥ 4`:
`(Real.log 2 / 4) * Real.sqrt n ≤ Real.log (partitionCount n)`. -/
theorem log_partitionCount_ge {n : ℕ} (hn : 4 ≤ n) :
    (Real.log 2 / 4) * Real.sqrt (n : ℝ) ≤ Real.log (partitionCount n : ℝ) := by
  have hle := exp_sqrt_le_partitionCount hn
  have hpos : 0 < (partitionCount n : ℝ) := by exact_mod_cast partitionCount_pos n
  calc (Real.log 2 / 4) * Real.sqrt (n : ℝ)
      = Real.log (Real.exp ((Real.log 2 / 4) * Real.sqrt (n : ℝ))) := (Real.log_exp _).symm
    _ ≤ Real.log (partitionCount n : ℝ) := Real.log_le_log (Real.exp_pos _) hle

/-- Saddle-point lower bound on `Real.log (partitionCount n)`: for any `ε > 0`, eventually
`(Real.pi / Real.sqrt 6 - ε) * Real.sqrt n ≤ Real.log (partitionCount n)`. -/
theorem log_partitionCount_saddle_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Real.pi / Real.sqrt 6 - ε) * Real.sqrt (n : ℝ) ≤ Real.log (partitionCount n : ℝ) := by
  set c₀ : ℝ := Real.pi / Real.sqrt 6
  have hc₀ : 0 < c₀ := by positivity
  by_cases hneg : c₀ - ε ≤ 0
  · refine Eventually.of_forall fun n => ?_
    have h1 : (1 : ℝ) ≤ (partitionCount n : ℝ) := by exact_mod_cast partitionCount_pos n
    have hlog : 0 ≤ Real.log (partitionCount n : ℝ) := Real.log_nonneg h1
    have hnonpos : (c₀ - ε) * Real.sqrt (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (Real.sqrt_nonneg _)
    exact hnonpos.trans hlog
  push Not at hneg
  let η : ℝ := min (1 / 2) (ε / (2 * c₀))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hη_bound : c₀ / (1 + η) ≥ c₀ - ε / 2 := by
    have h1 : η ≤ ε / (2 * c₀) := min_le_right _ _
    have h2 : c₀ * η ≤ ε / 2 := by
      calc c₀ * η ≤ c₀ * (ε / (2 * c₀)) := mul_le_mul_of_nonneg_left h1 hc₀.le
        _ = ε / 2 := by field_simp [hc₀.ne']
    have h3 : (c₀ - ε / 2) * (1 + η) ≤ c₀ := by nlinarith
    exact (le_div_iff₀ (by linarith)).mpr h3
  set A : ℝ := Real.pi * Real.sqrt (2 / 3)
  have hA_eq : A = 2 * c₀ := by
    dsimp [A, c₀]
    have h6 : Real.sqrt 6 = 3 * Real.sqrt (2 / 3) := by
      rw [show (6 : ℝ) = 3 ^ 2 * (2 / 3) by ring, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by norm_num)]
    rw [h6]
    field_simp [show Real.sqrt (2 / 3) ≠ 0 by positivity]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hpi_sq : Real.pi ^ 2 / 6 = c₀ ^ 2 := by
    dsimp [c₀]; rw [div_pow, Real.sq_sqrt (by norm_num)]
  have hgap : (1 - η) < 1 / (1 + η) := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith [sq_pos_of_pos hη0]
  set δ : ℝ := (1 / (1 + η) - (1 - η)) * c₀
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hgap) hc₀
  have hsqrt_atTop : Tendsto Real.sqrt atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun B =>
      ⟨max 0 B ^ 2, fun x hx => (le_max_right 0 B).trans (Real.le_sqrt_of_sq_le hx)⟩
  have ht_small : ∀ᶠ n : ℕ in Filter.atTop,
      Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ)) ≤ 1 / 2 := by
    have hsq_tend : Tendsto (fun n : ℕ => Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ)))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (hsqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)))
    exact hsq_tend.eventually (Iic_mem_nhds (by norm_num))
  have hlog_sqrt_tend : Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (_root_.isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine (h1.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp [Real.sqrt_eq_rpow]
  have htail_dom : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (4 * (1 + η) / η) + 2 * Real.log (n : ℝ) + 3 ≤ δ * Real.sqrt (n : ℝ) := by
    have htend : Tendsto (fun n : ℕ =>
        (Real.log (4 * (1 + η) / η) + 3) / Real.sqrt (n : ℝ) +
          2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (Real.log (4 * (1 + η) / η) + 3) / Real.sqrt (n : ℝ))
          atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (hsqrt_atTop.comp tendsto_natCast_atTop_atTop)
      simpa using h1.add (hlog_sqrt_tend.const_mul 2)
    filter_upwards [htend.eventually (Iic_mem_nhds hδ), eventually_ge_atTop 1] with n hn1 hn2
    have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn2)
    have hmul := mul_le_mul_of_nonneg_right hn1 hsq.le
    have hcalc : ((Real.log (4 * (1 + η) / η) + 3) / Real.sqrt (n : ℝ) +
          2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ) =
        Real.log (4 * (1 + η) / η) + 2 * Real.log (n : ℝ) + 3 := by
      field_simp [hsq.ne']
      ring
    linarith
  have hlog_dom : ∀ᶠ n : ℕ in Filter.atTop,
      (ε / 2) * Real.sqrt (n : ℝ) ≥
        Real.log (1 / (1 - Real.exp (-(Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ)))))) +
        Real.log (1 / (Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ)))) + 3 + Real.log 2 := by
    have ht_ev : ∀ᶠ n : ℕ in Filter.atTop,
        Real.log (1 / (1 - Real.exp (-(Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ)))))) +
          Real.log (1 / (Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ)))) + 3 + Real.log 2 ≤
        2 * Real.log (n : ℝ) + 10 := by
      filter_upwards [ht_small, eventually_ge_atTop 4] with n hts hn
      have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
      set t : ℝ := Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ))
      have ht0 : 0 < t := by positivity
      have hexp_lt1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have h1mt : 1 - Real.exp (-t) ≥ t / 2 := by
        have hexp1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
        have hinv : Real.exp (-t) ≤ 1 / (1 + t) := by
          rw [Real.exp_neg, one_div]; exact inv_anti₀ (by positivity) hexp1
        have h2 : 1 / (1 + t) ≤ 1 - t / 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hts]
        linarith [hinv.trans h2]
      have hinv_t : 1 / (1 - Real.exp (-t)) ≤ 2 / t := by
        rw [div_le_div_iff₀ (sub_pos.mpr hexp_lt1) ht0]
        linarith
      have hlog1 : Real.log (1 / (1 - Real.exp (-t))) ≤ Real.log (2 / t) :=
        Real.log_le_log (div_pos one_pos (sub_pos.mpr hexp_lt1)) hinv_t
      have hpi_eta2 : 2 ≤ Real.pi * (1 + η) := by nlinarith [hη0, Real.pi_gt_three]
      have h2t : 2 / t ≤ Real.sqrt (6 * (n : ℝ)) := by
        dsimp [t]
        rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [Real.sqrt_nonneg (6 * (n : ℝ)), hpi_eta2]
      have hlog1' : Real.log (2 / t) ≤ Real.log (Real.sqrt (6 * (n : ℝ))) :=
        Real.log_le_log (by positivity) h2t
      have hlog2 : Real.log (1 / t) ≤ Real.log (Real.sqrt (6 * (n : ℝ))) := by
        apply Real.log_le_log (by positivity)
        dsimp [t]
        rw [one_div_div]
        apply div_le_self (Real.sqrt_nonneg _)
        nlinarith [hpi_eta2]
      have hsq_le_3n : Real.sqrt (6 * (n : ℝ)) ≤ 3 * (n : ℝ) := by
        refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        nlinarith
      have hlog_sq : Real.log (Real.sqrt (6 * (n : ℝ))) ≤ Real.log 3 + Real.log (n : ℝ) := by
        calc Real.log (Real.sqrt (6 * (n : ℝ)))
            ≤ Real.log (3 * (n : ℝ)) := Real.log_le_log (by positivity) hsq_le_3n
          _ = Real.log 3 + Real.log (n : ℝ) := Real.log_mul (by norm_num) (by positivity)
      have hlog3_le : Real.log 3 ≤ 2 := by
        have h3e2 : (3 : ℝ) ≤ Real.exp 2 := by
          have h1 := Real.add_one_le_exp (1 : ℝ)
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith
        calc Real.log 3 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h3e2
          _ = 2 := Real.log_exp 2
      have hlog2_le : Real.log 2 ≤ 1 := by
        have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) this
          _ = 1 := Real.log_exp 1
      linarith
    have hsqrt_dom : ∀ᶠ n : ℕ in Filter.atTop, 2 * Real.log (n : ℝ) + 10 ≤ (ε / 2) * Real.sqrt (n : ℝ) := by
      have htend_in : Tendsto (fun n : ℕ =>
          2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) + 10 / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
        have h10 : Tendsto (fun n : ℕ => (10 : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (hsqrt_atTop.comp tendsto_natCast_atTop_atTop)
        simpa using (hlog_sqrt_tend.const_mul 2).add h10
      filter_upwards [htend_in.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < ε / 2)),
        eventually_ge_atTop 1] with n hn1 hn2
      have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn2)
      have hmul := mul_le_mul_of_nonneg_right hn1 hsq.le
      have hcalc : (2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) + 10 / Real.sqrt (n : ℝ)) *
          Real.sqrt (n : ℝ) = 2 * Real.log (n : ℝ) + 10 := by
        field_simp [hsq.ne']
      linarith
    filter_upwards [ht_ev, hsqrt_dom] with n h1 h2
    exact h1.trans h2
  filter_upwards [ht_small, htail_dom, eventually_ge_atTop 4, hlog_dom] with n hts htd hn4 hldom
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hsqn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  set t : ℝ := Real.pi * (1 + η) / Real.sqrt (6 * (n : ℝ))
  have ht0 : 0 < t := by positivity
  set x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hx_abs : |x| < 1 := by rwa [abs_of_pos hx0]
  have hs := summable_partitionCount_mul_pow_real hx0.le hx1
  have hgen := tsum_partitionCount_mul_pow_real hx_abs
  have hgen_ge := log_partitionGenFunReal_ge ht0 hts
  have hsplit := hs.sum_add_tsum_nat_add (n + 1)
  rw [hgen] at hsplit
  have hhead_le : ∑ m ∈ Finset.range (n + 1), (partitionCount m : ℝ) * x ^ m ≤
      (partitionCount n : ℝ) / (1 - x) := by
    calc ∑ m ∈ Finset.range (n + 1), (partitionCount m : ℝ) * x ^ m
        ≤ ∑ m ∈ Finset.range (n + 1), (partitionCount n : ℝ) * x ^ m := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast partitionCount_mono hmn)
            (pow_nonneg hx0.le _)
      _ = (partitionCount n : ℝ) * ∑ m ∈ Finset.range (n + 1), x ^ m := by rw [← Finset.mul_sum]
      _ ≤ (partitionCount n : ℝ) * (∑' m : ℕ, x ^ m) := by
          have hg := summable_geometric_of_lt_one hx0.le hx1
          exact mul_le_mul_of_nonneg_left
            (hg.sum_le_tsum (Finset.range (n + 1)) fun _ _ => pow_nonneg hx0.le _)
            (Nat.cast_nonneg _)
      _ = (partitionCount n : ℝ) / (1 - x) := by
          rw [(hasSum_geometric_of_lt_one hx0.le hx1).tsum_eq, div_eq_mul_inv]
  have htail_term : ∀ k : ℕ,
      (partitionCount (n + 1 + k) : ℝ) * x ^ (n + 1 + k) ≤
        Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) *
          (Real.exp (-((η / (1 + η)) * t))) ^ k := by
    intro k
    have hm_gt : n ≤ n + 1 + k := by omega
    have hupper := partitionCount_le_exp (n + 1 + k)
    have hA_t : A = 2 * t * Real.sqrt (n : ℝ) / (1 + η) := by
      dsimp [t, A]
      have h6 : Real.sqrt (6 * (n : ℝ)) = Real.sqrt 6 * Real.sqrt (n : ℝ) :=
        Real.sqrt_mul (by norm_num) _
      have h6' : Real.sqrt 6 = 3 * Real.sqrt (2 / 3) := by
        rw [show (6 : ℝ) = 3 ^ 2 * (2 / 3) by ring, Real.sqrt_mul (by norm_num),
            Real.sqrt_sq (by norm_num)]
      rw [h6, h6']
      field_simp [hsqn.ne', show Real.sqrt (2 / 3) ≠ 0 by positivity, show (1 + η) ≠ 0 by linarith]
      rw [Real.sq_sqrt (by norm_num)]
      ring
    have hdiff_sq :
        A * Real.sqrt ((n + 1 + k : ℕ) : ℝ) - ((n + 1 + k : ℕ) : ℝ) * t ≤
          (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) - (k : ℝ) * ((η / (1 + η)) * t) := by
      set m : ℕ := n + 1 + k
      have hm_ge : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_gt
      have hsm : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hm_ge
      have hsum_pos : 0 < Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) := by positivity
      have hdiff_sqrt :
          (Real.sqrt (m : ℝ) - Real.sqrt (n : ℝ)) * (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ)) =
            (m : ℝ) - (n : ℝ) := by
        have h1 := Real.sq_sqrt (Nat.cast_nonneg m)
        have h2 := Real.sq_sqrt (Nat.cast_nonneg n)
        nlinarith only [h1, h2]
      have hquot : A / (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ)) ≤ t / (1 + η) := by
        have hden : 2 * Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) := by
          linarith only [hsm]
        have hA2 : A / (2 * Real.sqrt (n : ℝ)) = t / (1 + η) := by
          rw [hA_t]
          field_simp [hsqn.ne', show 1 + η ≠ 0 by linarith]
        rw [← hA2]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      have hlin : A * (Real.sqrt (m : ℝ) - Real.sqrt (n : ℝ)) ≤
          (t / (1 + η)) * ((m : ℝ) - (n : ℝ)) := by
        calc A * (Real.sqrt (m : ℝ) - Real.sqrt (n : ℝ))
            = (A / (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ))) *
                ((Real.sqrt (m : ℝ) - Real.sqrt (n : ℝ)) * (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ))) := by
              field_simp [hsum_pos.ne']
          _ = (A / (Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ))) * ((m : ℝ) - (n : ℝ)) := by
              rw [hdiff_sqrt]
          _ ≤ (t / (1 + η)) * ((m : ℝ) - (n : ℝ)) :=
              mul_le_mul_of_nonneg_right hquot (by linarith only [hm_ge])
      have hmn_k : (k : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
        dsimp [m]; push_cast; linarith
      have hstep : A * Real.sqrt (m : ℝ) - (m : ℝ) * t ≤
          (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) - ((η / (1 + η)) * t) * ((m : ℝ) - (n : ℝ)) := by
        have heq : (t / (1 + η)) * ((m : ℝ) - (n : ℝ)) - ((m : ℝ) - (n : ℝ)) * t =
            -((η / (1 + η)) * t) * ((m : ℝ) - (n : ℝ)) := by
          field_simp [show 1 + η ≠ 0 by linarith]; ring
        linarith only [hlin, heq]
      have hk_mul : (k : ℝ) * ((η / (1 + η)) * t) ≤ ((η / (1 + η)) * t) * ((m : ℝ) - (n : ℝ)) := by
        rw [mul_comm (k : ℝ)]
        exact mul_le_mul_of_nonneg_left hmn_k (by positivity)
      linarith only [hstep, hk_mul]
    have hxpow : x ^ (n + 1 + k) = Real.exp (-(((n + 1 + k : ℕ) : ℝ) * t)) := by
      dsimp [x]; rw [← Real.exp_nat_mul]; congr 1; ring
    have hrhs_pow :
        Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) *
            (Real.exp (-((η / (1 + η)) * t))) ^ k =
          Real.exp ((A * Real.sqrt (n : ℝ) - (n : ℝ) * t) - (k : ℝ) * ((η / (1 + η)) * t)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    have hA_arg : Real.pi * Real.sqrt (2 * ((n + 1 + k : ℕ) : ℝ) / 3) =
        A * Real.sqrt ((n + 1 + k : ℕ) : ℝ) := by
      dsimp [A]
      rw [show 2 * ((n + 1 + k : ℕ) : ℝ) / 3 = (2 / 3) * ((n + 1 + k : ℕ) : ℝ) by ring,
          Real.sqrt_mul (by norm_num)]
      ring
    have hupperA : (partitionCount (n + 1 + k) : ℝ) ≤ Real.exp (A * Real.sqrt ((n + 1 + k : ℕ) : ℝ)) :=
      hA_arg ▸ hupper
    rw [hxpow, hrhs_pow]
    calc (partitionCount (n + 1 + k) : ℝ) * Real.exp (-(((n + 1 + k : ℕ) : ℝ) * t))
        ≤ Real.exp (A * Real.sqrt ((n + 1 + k : ℕ) : ℝ)) *
            Real.exp (-(((n + 1 + k : ℕ) : ℝ) * t)) :=
          mul_le_mul_of_nonneg_right hupperA (Real.exp_pos _).le
      _ = Real.exp (A * Real.sqrt ((n + 1 + k : ℕ) : ℝ) - ((n + 1 + k : ℕ) : ℝ) * t) := by
          rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ Real.exp ((A * Real.sqrt (n : ℝ) - (n : ℝ) * t) - (k : ℝ) * ((η / (1 + η)) * t)) :=
          Real.exp_le_exp.mpr hdiff_sq
  have htail_summ_shift : Summable fun k : ℕ => (partitionCount (n + 1 + k) : ℝ) * x ^ (n + 1 + k) :=
    ((summable_nat_add_iff (n + 1)).mpr hs).congr fun k => by rw [add_comm k (n + 1)]
  have hgeom_tail : HasSum (fun k : ℕ =>
      Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) * (Real.exp (-((η / (1 + η)) * t))) ^ k)
      (Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) / (1 - Real.exp (-((η / (1 + η)) * t)))) := by
    have hlt1 : Real.exp (-((η / (1 + η)) * t)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < (η / (1 + η)) * t := by positivity
      linarith)
    have hg := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hlt1).mul_left
      (Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t))
    simpa [div_eq_mul_inv] using hg
  have htail_le : ∑' k : ℕ, (partitionCount (n + 1 + k) : ℝ) * x ^ (n + 1 + k) ≤
      Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) / (1 - Real.exp (-((η / (1 + η)) * t))) := by
    have hs1 := htail_summ_shift.tsum_le_tsum htail_term hgeom_tail.summable
    exact hs1.trans_eq hgeom_tail.tsum_eq
  have ht_exp_A : A * Real.sqrt (n : ℝ) - (n : ℝ) * t = (1 - η) * c₀ * Real.sqrt (n : ℝ) := by
    have hnt : (n : ℝ) * t = (1 + η) * c₀ * Real.sqrt (n : ℝ) := by
      dsimp [t, c₀]
      have h6 : Real.sqrt (6 * (n : ℝ)) = Real.sqrt 6 * Real.sqrt (n : ℝ) :=
        Real.sqrt_mul (by norm_num) _
      have hsq : (n : ℝ) = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := (Real.mul_self_sqrt (by linarith)).symm
      rw [h6]
      nth_rw 1 [hsq]
      field_simp [hsqn.ne', show Real.sqrt 6 ≠ 0 by positivity]
    rw [hA_eq, hnt]
    ring
  have hF_exp_ge : Real.pi ^ 2 / (6 * t) = (1 / (1 + η)) * c₀ * Real.sqrt (n : ℝ) := by
    dsimp [t, c₀]
    have h6 : Real.sqrt (6 * (n : ℝ)) = Real.sqrt 6 * Real.sqrt (n : ℝ) :=
      Real.sqrt_mul (by norm_num) _
    have h6sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    rw [h6]
    field_simp [hsqn.ne', show Real.sqrt 6 ≠ 0 by positivity, show 1 + η ≠ 0 by linarith,
      Real.pi_ne_zero]
    exact h6sq
  have h1m_ge : 1 - Real.exp (-((η / (1 + η)) * t)) ≥ ((η / (1 + η)) * t) / 2 := by
    have hsmall : (η / (1 + η)) * t ≤ 1 / 2 := by
      have hη_le : η / (1 + η) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc (η / (1 + η)) * t ≤ 1 * t := mul_le_mul_of_nonneg_right hη_le ht0.le
        _ = t := one_mul t
        _ ≤ 1 / 2 := hts
    have hexp1 : 1 + ((η / (1 + η)) * t) ≤ Real.exp ((η / (1 + η)) * t) := by
      linarith only [Real.add_one_le_exp ((η / (1 + η)) * t)]
    have hinv : Real.exp (-((η / (1 + η)) * t)) ≤ 1 / (1 + ((η / (1 + η)) * t)) := by
      rw [Real.exp_neg, one_div]; exact inv_anti₀ (by positivity) hexp1
    have h2 : 1 / (1 + ((η / (1 + η)) * t)) ≤ 1 - ((η / (1 + η)) * t) / 2 := by
      have hu0 : 0 ≤ (η / (1 + η)) * t := by positivity
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hsmall, hu0]
    linarith only [hinv, h2]
  have hden_pos : 0 < 1 - Real.exp (-((η / (1 + η)) * t)) := by
    have : 0 < ((η / (1 + η)) * t) / 2 := by positivity
    linarith
  have htail_half :
      Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) / (1 - Real.exp (-((η / (1 + η)) * t))) ≤
        (1 / 2) * partitionGenFunReal x := by
    have hF_pos := partitionGenFunReal_pos hx0.le hx1
    rw [← Real.log_le_log_iff (by positivity) (by positivity)]
    rw [Real.log_div (Real.exp_pos _).ne' hden_pos.ne', Real.log_exp,
        Real.log_mul (by norm_num) hF_pos.ne']
    have h1 : -Real.log (1 - Real.exp (-((η / (1 + η)) * t))) ≤
        Real.log (2 * (1 + η) / (η * t)) := by
      have hle : (1 - Real.exp (-((η / (1 + η)) * t)))⁻¹ ≤ 2 * (1 + η) / (η * t) := by
        rw [inv_le_iff_one_le_mul₀ hden_pos]
        calc 1 = (2 * (1 + η) / (η * t)) * (((η / (1 + η)) * t) / 2) := by
              field_simp [hη0.ne', ht0.ne', show 1 + η ≠ 0 by linarith]
          _ ≤ (2 * (1 + η) / (η * t)) * (1 - Real.exp (-((η / (1 + η)) * t))) :=
              mul_le_mul_of_nonneg_left h1m_ge (by positivity)
      rw [← Real.log_inv]
      exact Real.log_le_log (inv_pos.mpr hden_pos) hle
    have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    have h2_exact : Real.log (2 * (1 + η) / (η * t)) + Real.log (1 / t) + Real.log 2 ≤
        Real.log (4 * (1 + η) / η) + 2 * Real.log (n : ℝ) := by
      have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      have ht_inv_le_n : 1 / t ≤ (n : ℝ) := by
        dsimp [t]
        rw [one_div_div]
        have hpi3 : 3 < Real.pi := Real.pi_gt_three
        have hpi_eta3 : 3 ≤ Real.pi * (1 + η) := by nlinarith only [hη0, hpi3]
        have hsq6 : Real.sqrt (6 * (n : ℝ)) ≤ 3 * (n : ℝ) := by
          refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
          nlinarith only [hn4R]
        calc Real.sqrt (6 * (n : ℝ)) / (Real.pi * (1 + η))
            ≤ Real.sqrt (6 * (n : ℝ)) / 3 :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) hpi_eta3
          _ ≤ (3 * (n : ℝ)) / 3 := div_le_div_of_nonneg_right hsq6 (by norm_num)
          _ = (n : ℝ) := by ring
      have hprod_le : (2 * (1 + η) / (η * t)) * (1 / t) * 2 ≤ (4 * (1 + η) / η) * (n : ℝ) ^ 2 := by
        have heq : 2 * (1 + η) / (η * t) * (1 / t) * 2 = (4 * (1 + η) / η) * (1 / t) ^ 2 := by
          field_simp [hη0.ne', ht0.ne']
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht_inv_le_n 2) (by positivity)
      rw [← Real.log_mul (by positivity) (by positivity),
          ← Real.log_mul (by positivity) (by norm_num)]
      have hlog_bd : Real.log ((2 * (1 + η) / (η * t)) * (1 / t) * 2) ≤
          Real.log ((4 * (1 + η) / η) * (n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) hprod_le
      have hlog_rhs : Real.log ((4 * (1 + η) / η) * (n : ℝ) ^ 2) =
          Real.log (4 * (1 + η) / η) + 2 * Real.log (n : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        norm_num
      exact hlog_bd.trans_eq hlog_rhs
    have hdelta_eq : (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) - Real.pi ^ 2 / (6 * t) = -(δ * Real.sqrt (n : ℝ)) := by
      rw [ht_exp_A, hF_exp_ge]
      dsimp [δ]
      ring
    linarith only [hgen_ge, h1, h2_exact, htd, hdelta_eq, hlog_half]
  have hp_ge : (1 / 2) * partitionGenFunReal x ≤ (partitionCount n : ℝ) / (1 - x) := by
    have htsum_eq : ∑' k : ℕ, (partitionCount (k + (n + 1)) : ℝ) * x ^ (k + (n + 1)) =
        ∑' k : ℕ, (partitionCount (n + 1 + k) : ℝ) * x ^ (n + 1 + k) :=
      tsum_congr fun k => by rw [add_comm k (n + 1)]
    have hsplit' : ∑ i ∈ Finset.range (n + 1), (partitionCount i : ℝ) * x ^ i +
        ∑' i : ℕ, (partitionCount (i + (n + 1)) : ℝ) * x ^ (i + (n + 1)) = partitionGenFunReal x :=
      hsplit
    have h1 : partitionGenFunReal x ≤ (partitionCount n : ℝ) / (1 - x) +
        Real.exp (A * Real.sqrt (n : ℝ) - (n : ℝ) * t) / (1 - Real.exp (-((η / (1 + η)) * t))) := by
      linarith only [hsplit', htsum_eq, hhead_le, htail_le]
    linarith only [h1, htail_half]
  have h1mx_pos : 0 < 1 - x := by linarith only [hx1]
  have hp_mul : (1 / 2) * partitionGenFunReal x * (1 - x) ≤ (partitionCount n : ℝ) := by
    have := mul_le_mul_of_nonneg_right hp_ge h1mx_pos.le
    rwa [div_mul_cancel₀ _ h1mx_pos.ne'] at this
  have hF_pos := partitionGenFunReal_pos hx0.le hx1
  have hlog_p : Real.log ((1 / 2) * partitionGenFunReal x * (1 - x)) ≤ Real.log (partitionCount n : ℝ) :=
    Real.log_le_log (by positivity) hp_mul
  have hlog_expand : Real.log ((1 / 2) * partitionGenFunReal x * (1 - x)) =
      Real.log (partitionGenFunReal x) - Real.log (1 / (1 - x)) - Real.log 2 := by
    rw [Real.log_mul (by positivity) h1mx_pos.ne', Real.log_mul (by norm_num) hF_pos.ne',
        Real.log_div one_pos.ne' two_ne_zero, Real.log_div one_pos.ne' h1mx_pos.ne', Real.log_one]
    ring
  rw [hlog_expand] at hlog_p
  have hmain_ge : c₀ / (1 + η) * Real.sqrt (n : ℝ) -
      (Real.log (1 / (1 - x)) + Real.log (1 / t) + 3 + Real.log 2) ≤
      Real.log (partitionCount n : ℝ) := by
    have h1 : c₀ / (1 + η) * Real.sqrt (n : ℝ) = Real.pi ^ 2 / (6 * t) := by
      rw [hF_exp_ge, div_eq_mul_inv, one_div, mul_comm c₀ _]
    linarith only [hgen_ge, hlog_p, h1]
  have h1 : (c₀ - ε / 2) * Real.sqrt (n : ℝ) ≤ c₀ / (1 + η) * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hη_bound hsqn.le
  linarith only [hmain_ge, h1, hldom]

end AsymptoticBounds

section CircleMethodAndRademacher

/-- Additive character `e(α) = exp(2πi α)`. -/
private def eChar (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * α * Complex.I)

private lemma intervalIntegral_eChar_int (m : ℤ) :
    ∫ α in (0 : ℝ)..1, eChar (α * (m : ℝ)) = if m = 0 then (1 : ℂ) else 0 := by
  by_cases hm : m = 0
  · simp [hm, eChar]
  · simp only [hm, ↓reduceIte]
    let c : ℂ := 2 * Real.pi * (m : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          (Int.cast_ne_zero.mpr hm))
        Complex.I_ne_zero
    let F : ℝ → ℂ := fun α => eChar (α * (m : ℝ)) / c
    have he_eq : ∀ α : ℝ, eChar (α * (m : ℝ)) = Complex.exp (c * (α : ℂ)) := fun α => by
      dsimp [eChar, c]; congr 1; push_cast; ring
    have hderiv : ∀ α ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (eChar (α * (m : ℝ))) α := by
      intro α _
      have hlin : HasDerivAt (fun t : ℝ => c * (t : ℂ)) (c * 1) α :=
        ((hasDerivAt_id α).ofReal_comp).const_mul c
      have hF : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c)
          (Complex.exp (c * (α : ℂ)) * (c * 1) / c) α := hlin.cexp.div_const c
      have hF_eq : (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c) = F := by
        ext t; simp [F, he_eq t]
      rw [hF_eq] at hF
      convert hF using 1
      rw [he_eq α, mul_one, mul_div_cancel_right₀ _ hc]
    have hint : IntervalIntegrable (fun α : ℝ => eChar (α * (m : ℝ))) volume 0 1 := by
      have hcont : Continuous fun α : ℝ => eChar (α * (m : ℝ)) := by
        dsimp [eChar]; fun_prop
      exact hcont.intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h1 : eChar ((1 : ℝ) * (m : ℝ)) = 1 := by
      dsimp [eChar]
      push_cast
      rw [one_mul, show (2 : ℂ) * Real.pi * (m : ℂ) * Complex.I =
          (m : ℂ) * (2 * Real.pi * Complex.I) by ring,
          Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    have h0 : eChar ((0 : ℝ) * (m : ℝ)) = 1 := by simp [eChar]
    dsimp [F]
    rw [h1, h0, sub_self]

/-- **Circle-Method Fourier Integral Representation** of `partitionCount n` on `[0, 1]`:
for `0 < r < 1`,
`(partitionCount n : ℂ) = r ^ (-n : ℤ) * ∫ θ in 0..1, partitionGenFun (r * exp (2πi θ)) * exp (-2πi n θ)`. -/
theorem partitionCount_eq_intervalIntegral {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (partitionCount n : ℂ) =
      (r : ℂ) ^ (-(n : ℤ)) *
        ∫ θ in (0 : ℝ)..1,
          partitionGenFun ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) *
            Complex.exp (-2 * Real.pi * (n : ℝ) * θ * Complex.I) := by
  let f : ℝ → ℂ := fun θ =>
    (r : ℂ) ^ (-(n : ℤ)) *
      partitionGenFun ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) *
      Complex.exp (-2 * Real.pi * (n : ℝ) * θ * Complex.I)
  let S : ℕ → ℝ → ℂ := fun N θ =>
    (r : ℂ) ^ (-(n : ℤ)) *
      (∑ m ∈ Finset.range N,
        (partitionCount m : ℂ) * ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ m) *
      Complex.exp (-2 * Real.pi * (n : ℝ) * θ * Complex.I)
  have hnorm_z : ∀ θ : ℝ, ‖(r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)‖ = r := by
    intro θ
    have hexp_eq : (2 * Real.pi * (θ : ℂ) * Complex.I) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hexp_eq,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsR := summable_partitionCount_mul_pow_real hr0.le hr1
  have hunif : TendstoUniformlyOn S f atTop (Set.uIcc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hrn_pos : 0 < r ^ (-(n : ℤ)) := zpow_pos hr0 _
    have htail_lim : Tendsto (fun N : ℕ =>
        (∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
          ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m) atTop (𝓝 0) := by
      simpa [sub_self] using (tendsto_const_nhds (x := ∑' m : ℕ, (partitionCount m : ℝ) * r ^ m)).sub
        hsR.hasSum.tendsto_sum_nat
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp htail_lim) (ε / r ^ (-(n : ℤ))) (by positivity)
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun N hN θ _ => ?_⟩
    have hz : ‖(r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)‖ < 1 := by
      rw [hnorm_z θ]; exact hr1
    have hgen := tsum_partitionCount_mul_pow hz
    have hsC := summable_partitionCount_mul_pow hz
    have hsub_sum :
        partitionGenFun ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) -
          ∑ m ∈ Finset.range N,
            (partitionCount m : ℂ) * ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ m =
          ∑' k : ℕ, (partitionCount (k + N) : ℂ) *
            ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ (k + N) := by
      rw [partitionGenFun, ← hgen, ← hsC.sum_add_tsum_nat_add N]
      ring
    have hnorm_e : ‖Complex.exp (-2 * Real.pi * (n : ℝ) * θ * Complex.I)‖ = 1 := by
      have hexp_eq : (-2 * Real.pi * ((n : ℝ) : ℂ) * (θ : ℂ) * Complex.I) =
          ((-2 * Real.pi * n * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hexp_eq, Complex.norm_exp_ofReal_mul_I]
    have hnorm_rn : ‖(r : ℂ) ^ (-(n : ℤ))‖ = r ^ (-(n : ℤ)) := by
      rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hdiff_eq : f θ - S N θ =
        (r : ℂ) ^ (-(n : ℤ)) *
          (partitionGenFun ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) -
            ∑ m ∈ Finset.range N,
              (partitionCount m : ℂ) * ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ m) *
          Complex.exp (-2 * Real.pi * (n : ℝ) * θ * Complex.I) := by
      dsimp [f, S]; ring
    rw [dist_eq_norm, hdiff_eq, norm_mul, norm_mul, hnorm_rn, hnorm_e, mul_one,
        hsub_sum]
    have hshift_R : Summable fun k : ℕ => (partitionCount (k + N) : ℝ) * r ^ (k + N) :=
      (summable_nat_add_iff N).mpr hsR
    have hshift_C : Summable fun k : ℕ => ‖(partitionCount (k + N) : ℂ) *
        ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ (k + N)‖ := by
      refine hshift_R.congr fun k => ?_
      rw [norm_mul, norm_pow, hnorm_z θ, Complex.norm_natCast]
    have hnorm_le :
        ‖∑' k : ℕ, (partitionCount (k + N) : ℂ) *
            ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ (k + N)‖ ≤
          (∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
            ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m := by
      calc ‖∑' k : ℕ, (partitionCount (k + N) : ℂ) *
              ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ (k + N)‖
          ≤ ∑' k : ℕ, ‖(partitionCount (k + N) : ℂ) *
              ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ (k + N)‖ :=
            norm_tsum_le_tsum_norm hshift_C
        _ = ∑' k : ℕ, (partitionCount (k + N) : ℝ) * r ^ (k + N) := by
            refine tsum_congr fun k => ?_
            rw [norm_mul, norm_pow, hnorm_z θ, Complex.norm_natCast]
        _ = (∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
              ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m := by
            have := hsR.sum_add_tsum_nat_add N
            linarith
    have hN0 := hN₀ N hN
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by
      have := hsR.sum_le_tsum (Finset.range N) fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0.le _)
      linarith)] at hN0
    calc r ^ (-(n : ℤ)) * ‖∑' k : ℕ, (partitionCount (k + N) : ℂ) *
            ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) ^ (k + N)‖
        ≤ r ^ (-(n : ℤ)) * ((∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
            ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m) :=
          mul_le_mul_of_nonneg_left hnorm_le hrn_pos.le
      _ < r ^ (-(n : ℤ)) * (ε / r ^ (-(n : ℤ))) := mul_lt_mul_of_pos_left hN0 hrn_pos
      _ = ε := mul_div_cancel₀ _ hrn_pos.ne'
  have hcontS : ∀ N : ℕ, ContinuousOn (S N) (Set.uIcc 0 1) := by
    intro N
    refine Continuous.continuousOn ?_
    dsimp [S]
    have harg1 : Continuous fun θ : ℝ => (r : ℂ) * Complex.exp (2 * Real.pi * (θ : ℂ) * Complex.I) :=
      continuous_const.fun_mul (Complex.continuous_exp.comp
        ((continuous_const.fun_mul Complex.continuous_ofReal).fun_mul continuous_const))
    have hsum : Continuous fun θ : ℝ =>
        ∑ m ∈ Finset.range N, (partitionCount m : ℂ) * ((r : ℂ) * Complex.exp (2 * Real.pi * (θ : ℂ) * Complex.I)) ^ m := by
      have hrec : ∀ s : Finset ℕ, Continuous fun θ : ℝ =>
          ∑ m ∈ s, (partitionCount m : ℂ) * ((r : ℂ) * Complex.exp (2 * Real.pi * (θ : ℂ) * Complex.I)) ^ m := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [continuous_const]
        | @insert m s hm ih =>
          simp_rw [Finset.sum_insert hm]
          exact (continuous_const.fun_mul (harg1.pow m)).fun_add ih
      exact hrec (Finset.range N)
    have harg2 : Continuous fun θ : ℝ => Complex.exp (-2 * Real.pi * (n : ℝ) * (θ : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp
        ((continuous_const.fun_mul Complex.continuous_ofReal).fun_mul continuous_const)
    exact (continuous_const.fun_mul hsum).fun_mul harg2
  have htend_int : Tendsto (fun N : ℕ => ∫ θ in (0 : ℝ)..1, S N θ) atTop
      (𝓝 (∫ θ in (0 : ℝ)..1, f θ)) :=
    hunif.tendsto_intervalIntegral_of_continuousOn (Eventually.of_forall hcontS)
  have hS_val : ∀ N : ℕ, n < N → ∫ θ in (0 : ℝ)..1, S N θ = (partitionCount n : ℂ) := by
    intro N hN
    have hexpand : ∀ θ : ℝ, S N θ = ∑ m ∈ Finset.range N,
        ((partitionCount m : ℂ) * (r : ℂ) ^ ((m : ℤ) - n)) * eChar (θ * (((m : ℤ) - n : ℤ) : ℝ)) := by
      intro θ
      dsimp [S, eChar]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h1 : ((r : ℂ) * Complex.exp (2 * Real.pi * (θ : ℂ) * Complex.I)) ^ m =
          (r : ℂ) ^ m * Complex.exp (2 * Real.pi * (m : ℂ) * (θ : ℂ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul,
            show (m : ℕ) * (2 * Real.pi * (θ : ℂ) * Complex.I) =
              2 * Real.pi * (m : ℂ) * (θ : ℂ) * Complex.I by ring]
      have hr_pow : (r : ℂ) ^ (-(n : ℤ)) * (r : ℂ) ^ m = (r : ℂ) ^ ((m : ℤ) - n) := by
        rw [← zpow_natCast (r : ℂ) m, ← zpow_add₀ (Complex.ofReal_ne_zero.mpr hr0.ne')]
        exact congrArg ((r : ℂ) ^ ·) (by omega)
      have hexp_mul : Complex.exp (2 * Real.pi * (m : ℂ) * (θ : ℂ) * Complex.I) *
          Complex.exp (-2 * Real.pi * (n : ℂ) * (θ : ℂ) * Complex.I) =
          Complex.exp (2 * Real.pi * ((θ * (((m : ℤ) - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        exact congrArg Complex.exp (by push_cast; ring)
      rw [h1]
      calc (r : ℂ) ^ (-(n : ℤ)) *
            ((partitionCount m : ℂ) *
              ((r : ℂ) ^ m * Complex.exp (2 * Real.pi * (m : ℂ) * (θ : ℂ) * Complex.I))) *
            Complex.exp (-2 * Real.pi * (n : ℂ) * (θ : ℂ) * Complex.I)
          = (partitionCount m : ℂ) * ((r : ℂ) ^ (-(n : ℤ)) * (r : ℂ) ^ m) *
              (Complex.exp (2 * Real.pi * (m : ℂ) * (θ : ℂ) * Complex.I) *
                Complex.exp (-2 * Real.pi * (n : ℂ) * (θ : ℂ) * Complex.I)) := by ring
        _ = (partitionCount m : ℂ) * (r : ℂ) ^ ((m : ℤ) - n) *
              Complex.exp (2 * Real.pi * ((θ * (((m : ℤ) - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
            rw [hr_pow, hexp_mul]
    simp_rw [hexpand]
    rw [intervalIntegral.integral_finsetSum]
    · have hterm : ∀ m ∈ Finset.range N,
          ∫ θ in (0 : ℝ)..1, ((partitionCount m : ℂ) * (r : ℂ) ^ ((m : ℤ) - n)) *
            eChar (θ * (((m : ℤ) - n : ℤ) : ℝ)) =
            if m = n then (partitionCount n : ℂ) else 0 := by
        intro m _
        rw [intervalIntegral.integral_const_mul, intervalIntegral_eChar_int ((m : ℤ) - n)]
        by_cases hmn : m = n
        · subst hmn; simp
        · have hz : (m : ℤ) - n ≠ 0 := by omega
          simp [hz, hmn]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      simp only [Finset.mem_range.mpr hN, ↓reduceIte]
    · intro m _
      have hcont : Continuous fun θ : ℝ =>
          ((partitionCount m : ℂ) * (r : ℂ) ^ ((m : ℤ) - n)) *
            eChar (θ * (((m : ℤ) - n : ℤ) : ℝ)) :=
        continuous_const.fun_mul (Complex.continuous_exp.comp
          ((continuous_const.fun_mul (Complex.continuous_ofReal.comp
            (continuous_id.fun_mul continuous_const))).fun_mul continuous_const))
      exact hcont.intervalIntegrable 0 1
  have htend_const : Tendsto (fun N : ℕ => ∫ θ in (0 : ℝ)..1, S N θ) atTop (𝓝 (partitionCount n : ℂ)) :=
    tendsto_atTop_of_eventually_const (i₀ := n + 1) fun N hN => hS_val N (by omega)
  have heq_int : ∫ θ in (0 : ℝ)..1, f θ = (partitionCount n : ℂ) :=
    tendsto_nhds_unique htend_int htend_const
  have heq_f : ∀ θ : ℝ, f θ = (r : ℂ) ^ (-(n : ℤ)) *
      (partitionGenFun ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)) *
        Complex.exp (-2 * Real.pi * (n : ℝ) * θ * Complex.I)) := fun θ => by
    dsimp [f]; ring
  simp_rw [heq_f] at heq_int
  rw [← heq_int, intervalIntegral.integral_const_mul]

/-- **Cauchy Integral Representation** of `partitionCount n`:
for `0 < r < 1`, `(partitionCount n : ℂ) = (1 / (2πi)) * ∮ z in C(0, r), partitionGenFun z / z ^ (n + 1)`. -/
theorem partitionCount_eq_circleIntegral {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (partitionCount n : ℂ) =
      (1 / (2 * Real.pi * Complex.I)) *
        ∮ z in C(0, r), partitionGenFun z / z ^ (n + 1) := by
  let S : ℕ → ℂ → ℂ := fun N z =>
    (∑ m ∈ Finset.range N, (partitionCount m : ℂ) * z ^ m) / z ^ (n + 1)
  have hsR := summable_partitionCount_mul_pow_real hr0.le hr1
  have hunif : TendstoUniformlyOn S (fun z => partitionGenFun z / z ^ (n + 1))
      atTop (Metric.sphere 0 r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hrn_pos : 0 < r ^ (n + 1) := pow_pos hr0 _
    have htail_lim : Tendsto (fun N : ℕ =>
        (∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
          ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m) atTop (𝓝 0) := by
      simpa [sub_self] using (tendsto_const_nhds (x := ∑' m : ℕ, (partitionCount m : ℝ) * r ^ m)).sub
        hsR.hasSum.tendsto_sum_nat
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp htail_lim) (ε * r ^ (n + 1)) (by positivity)
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun N hN z hz => ?_⟩
    have hz_norm : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hz_lt1 : ‖z‖ < 1 := hz_norm.symm ▸ hr1
    have hgen := tsum_partitionCount_mul_pow hz_lt1
    have hsC := summable_partitionCount_mul_pow hz_lt1
    have hsub_sum :
        partitionGenFun z - ∑ m ∈ Finset.range N, (partitionCount m : ℂ) * z ^ m =
          ∑' k : ℕ, (partitionCount (k + N) : ℂ) * z ^ (k + N) := by
      rw [partitionGenFun, ← hgen, ← hsC.sum_add_tsum_nat_add N]
      ring
    have hdiff_eq : (partitionGenFun z / z ^ (n + 1)) - S N z =
        (partitionGenFun z - ∑ m ∈ Finset.range N, (partitionCount m : ℂ) * z ^ m) / z ^ (n + 1) := by
      dsimp [S]; ring
    rw [dist_eq_norm, hdiff_eq, norm_div, norm_pow, hz_norm, hsub_sum]
    have hshift_R : Summable fun k : ℕ => (partitionCount (k + N) : ℝ) * r ^ (k + N) :=
      (summable_nat_add_iff N).mpr hsR
    have hshift_C : Summable fun k : ℕ => ‖(partitionCount (k + N) : ℂ) * z ^ (k + N)‖ := by
      refine hshift_R.congr fun k => ?_
      rw [norm_mul, norm_pow, hz_norm, Complex.norm_natCast]
    have hnorm_le :
        ‖∑' k : ℕ, (partitionCount (k + N) : ℂ) * z ^ (k + N)‖ ≤
          (∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
            ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m := by
      calc ‖∑' k : ℕ, (partitionCount (k + N) : ℂ) * z ^ (k + N)‖
          ≤ ∑' k : ℕ, ‖(partitionCount (k + N) : ℂ) * z ^ (k + N)‖ :=
            norm_tsum_le_tsum_norm hshift_C
        _ = ∑' k : ℕ, (partitionCount (k + N) : ℝ) * r ^ (k + N) := by
            refine tsum_congr fun k => ?_
            rw [norm_mul, norm_pow, hz_norm, Complex.norm_natCast]
        _ = (∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
              ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m := by
            have := hsR.sum_add_tsum_nat_add N
            linarith
    have hN0 := hN₀ N hN
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by
      have := hsR.sum_le_tsum (Finset.range N) fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0.le _)
      linarith)] at hN0
    calc ‖∑' k : ℕ, (partitionCount (k + N) : ℂ) * z ^ (k + N)‖ / r ^ (n + 1)
        ≤ ((∑' m : ℕ, (partitionCount m : ℝ) * r ^ m) -
            ∑ m ∈ Finset.range N, (partitionCount m : ℝ) * r ^ m) / r ^ (n + 1) :=
          div_le_div_of_nonneg_right hnorm_le hrn_pos.le
      _ < (ε * r ^ (n + 1)) / r ^ (n + 1) := div_lt_div_of_pos_right hN0 hrn_pos
      _ = ε := mul_div_cancel_right₀ _ hrn_pos.ne'
  have hcontS : ∀ N : ℕ, ContinuousOn (S N) (Metric.sphere 0 r) := by
    intro N z hz
    have hz_ne : z ≠ 0 := by
      intro h0; subst h0
      rw [Metric.mem_sphere, dist_zero_right, norm_zero] at hz
      linarith
    have hcd : ContinuousAt (S N) z := by
      dsimp [S]
      have hsum : ContinuousAt (fun z : ℂ => ∑ m ∈ Finset.range N, (partitionCount m : ℂ) * z ^ m) z := by
        have hrec : ∀ s : Finset ℕ, ContinuousAt (fun z : ℂ => ∑ m ∈ s, (partitionCount m : ℂ) * z ^ m) z := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp [continuousAt_const]
          | @insert m s hm ih =>
            simp_rw [Finset.sum_insert hm]
            exact (continuousAt_const.fun_mul (continuousAt_id.pow m)).fun_add ih
        exact hrec (Finset.range N)
      exact hsum.div₀ (continuousAt_id.pow (n + 1)) (pow_ne_zero _ hz_ne)
    exact hcd.continuousWithinAt
  have htend_int : Tendsto (fun N : ℕ => ∮ z in C(0, r), S N z) atTop
      (𝓝 (∮ z in C(0, r), partitionGenFun z / z ^ (n + 1))) :=
    hunif.tendsto_circleIntegral_of_continuousOn hr0.le (Eventually.of_forall hcontS)
  have hS_val : ∀ N : ℕ, n < N →
      ∮ z in C(0, r), S N z = (2 * Real.pi * Complex.I) * (partitionCount n : ℂ) := by
    intro N hN
    have hexpand : ∀ z : ℂ, z ≠ 0 →
        S N z = ∑ m ∈ Finset.range N, (partitionCount m : ℂ) * (z - 0) ^ ((m : ℤ) - n - 1) := by
      intro z hz
      dsimp [S]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [sub_zero, mul_div_assoc, ← zpow_natCast z m, ← zpow_natCast z (n + 1), ← zpow_sub₀ hz]
      exact congrArg (fun k : ℤ => (partitionCount m : ℂ) * z ^ k) (by omega)
    have hcongr : ∮ z in C(0, r), S N z =
        ∮ z in C(0, r), ∑ m ∈ Finset.range N, (partitionCount m : ℂ) * (z - 0) ^ ((m : ℤ) - n - 1) := by
      refine circleIntegral.integral_congr hr0.le fun z hz => ?_
      have hz_ne : z ≠ 0 := by
        intro h0; subst h0; rw [Metric.mem_sphere, dist_zero_right, norm_zero] at hz; linarith
      exact hexpand z hz_ne
    rw [hcongr]
    have hint_sum : ∮ z in C(0, r),
        ∑ m ∈ Finset.range N, (partitionCount m : ℂ) * (z - 0) ^ ((m : ℤ) - n - 1) =
        ∑ m ∈ Finset.range N,
          ∮ z in C(0, r), (partitionCount m : ℂ) * (z - 0) ^ ((m : ℤ) - n - 1) := by
      unfold circleIntegral
      have hterm_eq : ∀ θ : ℝ,
          deriv (circleMap 0 r) θ •
            (∑ m ∈ Finset.range N,
              (partitionCount m : ℂ) * (circleMap 0 r θ - 0) ^ ((m : ℤ) - n - 1)) =
            ∑ m ∈ Finset.range N,
              deriv (circleMap 0 r) θ •
                ((partitionCount m : ℂ) * (circleMap 0 r θ - 0) ^ ((m : ℤ) - n - 1)) := by
        intro θ
        rw [smul_eq_mul, Finset.mul_sum]
        rfl
      simp_rw [hterm_eq]
      refine intervalIntegral.integral_finsetSum fun m _ => ?_
      have hci : CircleIntegrable (fun z => (partitionCount m : ℂ) * (z - 0) ^ ((m : ℤ) - n - 1)) 0 r := by
        refine (ContinuousOn.circleIntegrable hr0.le) ?_
        intro z hz
        have hz_ne : z ≠ 0 := by
          intro h0; subst h0; rw [Metric.mem_sphere, dist_zero_right, norm_zero] at hz; linarith
        exact (continuousAt_const.fun_mul
          (ContinuousAt.zpow₀ (continuousAt_id.fun_sub continuousAt_const) ((m : ℤ) - n - 1)
            (Or.inl (by dsimp; rwa [sub_zero])))).continuousWithinAt
      exact hci.out
    rw [hint_sum]
    have hterm_val : ∀ m ∈ Finset.range N,
        (∮ z in C(0, r), (partitionCount m : ℂ) * (z - 0) ^ ((m : ℤ) - n - 1)) =
          if m = n then (2 * Real.pi * Complex.I) * (partitionCount n : ℂ) else 0 := by
      intro m _
      rw [circleIntegral.integral_const_mul]
      by_cases hmn : m = n
      · subst hmn
        have hexp : ((m : ℤ) - m - 1) = (-1 : ℤ) := by ring
        rw [hexp]
        simp only [↓reduceIte]
        have h1 : ∀ z : ℂ, (z - 0) ^ (-1 : ℤ) = (z - 0)⁻¹ := fun z => zpow_neg_one _
        simp_rw [h1]
        rw [circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hr0)]
        ring
      · simp only [hmn, ↓reduceIte]
        have hexp : ((m : ℤ) - n - 1) ≠ -1 := by omega
        have h0 := circleIntegral.integral_sub_zpow_of_ne hexp (c := 0) (w := 0) (R := r)
        rw [h0, mul_zero]
    rw [Finset.sum_congr rfl hterm_val, Finset.sum_ite_eq']
    simp only [Finset.mem_range.mpr hN, ↓reduceIte]
  have htend_const : Tendsto (fun N : ℕ => ∮ z in C(0, r), S N z) atTop
      (𝓝 ((2 * Real.pi * Complex.I) * (partitionCount n : ℂ))) :=
    tendsto_atTop_of_eventually_const (i₀ := n + 1) fun N hN => hS_val N (by omega)
  have heq_c := tendsto_nhds_unique htend_int htend_const
  rw [heq_c]
  have h2piI : (2 * Real.pi * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp [h2piI]

/-- Radial maximum principle for the partition generating function:
for `‖z‖ < 1`, `‖partitionGenFun z‖ ≤ partitionGenFunReal ‖z‖`. -/
theorem norm_partitionGenFun_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖partitionGenFun z‖ ≤ partitionGenFunReal ‖z‖ := by
  rw [partitionGenFun, ← tsum_partitionCount_mul_pow hz]
  have hs := summable_norm_partitionCount_mul_pow hz
  have hgenR := tsum_partitionCount_mul_pow_real (x := ‖z‖)
    (by simpa [abs_of_nonneg (norm_nonneg z)] using hz)
  calc ‖∑' n : ℕ, (partitionCount n : ℂ) * z ^ n‖
      ≤ ∑' n : ℕ, ‖(partitionCount n : ℂ) * z ^ n‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℕ, (partitionCount n : ℝ) * ‖z‖ ^ n := by
        refine tsum_congr fun n => ?_
        rw [norm_mul, norm_pow, Complex.norm_natCast]
    _ = partitionGenFunReal ‖z‖ := hgenR

/-- Exact modulus identity on the circle:
`‖1 - r * exp (2πi θ)‖ ^ 2 = (1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2`. -/
theorem norm_one_sub_mul_cexp_sq (r θ : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I)‖ ^ 2 =
      (1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2 := by
  have hexp : Complex.exp (2 * Real.pi * (θ : ℂ) * Complex.I) =
      (Real.cos (2 * Real.pi * θ) : ℂ) + (Real.sin (2 * Real.pi * θ) : ℂ) * Complex.I := by
    have h := Complex.exp_mul_I (2 * Real.pi * (θ : ℂ))
    rw [show 2 * Real.pi * (θ : ℂ) * Complex.I = (2 * Real.pi * (θ : ℂ)) * Complex.I by ring, h]
    push_cast; rfl
  rw [hexp, Complex.sq_norm]
  have hre : ((1 : ℂ) - (r : ℂ) * ((Real.cos (2 * Real.pi * θ) : ℂ) +
      (Real.sin (2 * Real.pi * θ) : ℂ) * Complex.I)).re = 1 - r * Real.cos (2 * Real.pi * θ) := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.add_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, zero_mul, add_zero]
  have him : ((1 : ℂ) - (r : ℂ) * ((Real.cos (2 * Real.pi * θ) : ℂ) +
      (Real.sin (2 * Real.pi * θ) : ℂ) * Complex.I)).im = -(r * Real.sin (2 * Real.pi * θ)) := by
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, add_zero, zero_mul, zero_add, zero_sub]
  rw [Complex.normSq_apply, hre, him]
  have hcos : Real.cos (2 * Real.pi * θ) = 1 - 2 * Real.sin (Real.pi * θ) ^ 2 := by
    rw [show 2 * Real.pi * θ = 2 * (Real.pi * θ) by ring, Real.cos_two_mul', Real.cos_sq']
    ring
  have htrig : Real.cos (2 * Real.pi * θ) ^ 2 + Real.sin (2 * Real.pi * θ) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  calc (1 - r * Real.cos (2 * Real.pi * θ)) * (1 - r * Real.cos (2 * Real.pi * θ)) +
        -(r * Real.sin (2 * Real.pi * θ)) * -(r * Real.sin (2 * Real.pi * θ))
      = 1 - 2 * r * Real.cos (2 * Real.pi * θ) +
          r ^ 2 * (Real.cos (2 * Real.pi * θ) ^ 2 + Real.sin (2 * Real.pi * θ) ^ 2) := by ring
    _ = 1 - 2 * r * (1 - 2 * Real.sin (Real.pi * θ) ^ 2) + r ^ 2 * 1 := by rw [htrig, hcos]
    _ = (1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * θ) ^ 2 := by ring

/-- Minor-arc decay bound on the circle `|z| = r`:
for `0 < r < 1` and `θ : ℝ`,
`‖partitionGenFun (r * exp (2πi θ))‖ ≤ partitionGenFunReal r * ((1 - r) / √((1 - r)^2 + 4r sin^2(πθ)))`. -/
theorem norm_partitionGenFun_circle_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    ‖partitionGenFun ((r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I))‖ ≤
      partitionGenFunReal r *
        ((1 - r) / Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2)) := by
  obtain ⟨z, hz_def⟩ : ∃ z : ℂ, z = (r : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) := ⟨_, rfl⟩
  have hnorm_z : ‖z‖ = r := by
    rw [hz_def]
    have hexp_eq : (2 * Real.pi * (θ : ℂ) * Complex.I) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hexp_eq,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  have hz : ‖z‖ < 1 := hnorm_z.symm ▸ hr1
  have hr_abs : |r| < 1 := by rwa [abs_of_pos hr0]
  have hmC := multipliable_one_sub_pow hz
  have hmR := multipliable_one_sub_pow_real hr_abs
  have hneC := tprod_one_sub_pow_ne_zero hz
  have hneR := tprod_one_sub_pow_real_ne_zero hr_abs
  have hfac_pos : ∀ k : ℕ, 0 < (1 : ℝ) - r ^ (k + 1) := fun k => by
    have : r ^ (k + 1) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero k)
    linarith
  have h0_ne : (1 : ℂ) - z ≠ 0 := by
    intro h0
    have hnorm : ‖z‖ = 1 := by
      have : z = 1 := by linear_combination -h0
      simpa using congrArg norm this
    linarith
  have hmC' : Multipliable fun k : ℕ => (1 : ℂ) - z ^ (k + 2) := by
    have hsC' : Summable fun k : ℕ => ‖-z ^ (k + 2)‖ := by
      simpa only [add_assoc] using (summable_nat_add_iff 1).mpr (summable_norm_neg_pow_succ hz)
    simpa [sub_eq_add_neg] using
      AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm hsC'
  have hmR' : Multipliable fun k : ℕ => (1 : ℝ) - r ^ (k + 2) := by
    have hsR' : Summable fun k : ℕ => ‖-r ^ (k + 2)‖ := by
      have hg : Summable fun k : ℕ => ‖-r ^ (k + 1)‖ := by
        have hgeom : Summable fun k : ℕ => |r| ^ k := summable_geometric_of_lt_one (abs_nonneg _) hr_abs
        simpa [Real.norm_eq_abs, abs_neg, abs_pow, pow_succ] using hgeom.mul_right |r|
      simpa only [add_assoc] using (summable_nat_add_iff 1).mpr hg
    simpa [sub_eq_add_neg] using
      AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_norm hsR'
  have hsplitC : ∏' k : ℕ, ((1 : ℂ) - z ^ (k + 1)) =
      ((1 : ℂ) - z) * ∏' k : ℕ, ((1 : ℂ) - z ^ (k + 2)) := by
    simpa only [Nat.zero_add, pow_one] using tprod_eq_zero_mul' (f := fun k : ℕ => (1 : ℂ) - z ^ (k + 1)) hmC'
  have hsplitR : ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 1)) =
      (1 - r) * ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)) := by
    simpa only [Nat.zero_add, pow_one] using tprod_eq_zero_mul' (f := fun k : ℕ => (1 : ℝ) - r ^ (k + 1)) hmR'
  have htail_ge : ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)) ≤
      ‖∏' k : ℕ, ((1 : ℂ) - z ^ (k + 2))‖ := by
    have htC : Tendsto (fun N : ℕ => ‖∏ k ∈ Finset.range N, ((1 : ℂ) - z ^ (k + 2))‖)
        atTop (𝓝 ‖∏' k : ℕ, ((1 : ℂ) - z ^ (k + 2))‖) :=
      (hmC'.hasProd.tendsto_prod_nat).norm
    have htR : Tendsto (fun N : ℕ => ∏ k ∈ Finset.range N, ((1 : ℝ) - r ^ (k + 2)))
        atTop (𝓝 (∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)))) :=
      hmR'.hasProd.tendsto_prod_nat
    refine le_of_tendsto_of_tendsto htR htC (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun k _ => (hfac_pos (k + 1)).le) fun k _ => ?_
    have htri := norm_sub_norm_le (1 : ℂ) (z ^ (k + 2))
    simpa [norm_one, norm_pow, hnorm_z] using htri
  have htailR_pos : 0 < ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)) := by
    have hprod_ne : (1 - r) * ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)) ≠ 0 := by
      rw [← hsplitR]; exact hneR
    have hne' : ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)) ≠ 0 := right_ne_zero_of_mul hprod_ne
    have hnonneg : 0 ≤ ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)) := by
      exact ge_of_tendsto hmR'.hasProd (Eventually.of_forall fun s =>
        Finset.prod_nonneg fun k _ => (hfac_pos (k + 1)).le)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne')
  have hnorm_z1 : ‖(1 : ℂ) - z‖ = Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2) := by
    rw [hz_def, ← norm_one_sub_mul_cexp_sq r θ]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hden_pos : 0 < Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2) := by
    rw [← hnorm_z1]; exact norm_pos_iff.mpr h0_ne
  rw [← hz_def, partitionGenFun, partitionGenFunReal, norm_inv, hsplitC, hsplitR, norm_mul, hnorm_z1]
  have hinv_le : (Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2) *
      ‖∏' k : ℕ, ((1 : ℂ) - z ^ (k + 2))‖)⁻¹ ≤
      (Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2) *
        ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)))⁻¹ :=
    inv_anti₀ (mul_pos hden_pos htailR_pos) (mul_le_mul_of_nonneg_left htail_ge hden_pos.le)
  calc (Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2) *
        ‖∏' k : ℕ, ((1 : ℂ) - z ^ (k + 2))‖)⁻¹
      ≤ (Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2) *
          ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)))⁻¹ := hinv_le
    _ = ((1 - r) * ∏' k : ℕ, ((1 : ℝ) - r ^ (k + 2)))⁻¹ *
          ((1 - r) / Real.sqrt ((1 - r) ^ 2 + 4 * r * (Real.sin (Real.pi * θ)) ^ 2)) := by
        field_simp [hden_pos.ne', htailR_pos.ne', show 1 - r ≠ 0 by linarith]

/-- The Hardy–Ramanujan leading asymptotic term `(1 / (4 * n * √3)) * exp (π * √(2 * n / 3))`. -/
def hardyRamanujanMainTerm (n : ℕ) : ℝ :=
  (1 / (4 * (n : ℝ) * Real.sqrt 3)) * Real.exp (Real.pi * Real.sqrt (2 * (n : ℝ) / 3))

/-- **The Hardy–Ramanujan Asymptotic Formula** for `p(n)`:
`partitionCount n ~ (1 / (4 * n * √3)) * exp (π * √(2 * n / 3))` as `n → ∞`. -/
def HardyRamanujanAsymptotic : Prop :=
  (fun n : ℕ => (partitionCount n : ℝ)) ~[Filter.atTop] hardyRamanujanMainTerm

/-- The `k`-th Rademacher analytic term `ψ_k(n)` in the exact convergent expansion of `p(n)`. -/
def rademacherPsi (k n : ℕ) : ℝ :=
  (1 / (Real.pi * Real.sqrt 2)) *
    deriv (fun x : ℝ => Real.sinh ((Real.pi / (k : ℝ)) * Real.sqrt (2 * x / 3)) / Real.sqrt x)
      ((n : ℝ) - 1 / 24)

/-- Closed-form derivative evaluation of `rademacherPsi k n` for `k ≥ 1` and `n ≥ 1`. -/
theorem rademacherPsi_eq {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    rademacherPsi k n =
      (1 / (2 * Real.pi * Real.sqrt 2 * (Real.sqrt ((n : ℝ) - 1 / 24)) ^ 3)) *
        (((Real.pi / (k : ℝ)) * Real.sqrt (2 / 3)) * Real.sqrt ((n : ℝ) - 1 / 24) *
            Real.cosh (((Real.pi / (k : ℝ)) * Real.sqrt (2 / 3)) * Real.sqrt ((n : ℝ) - 1 / 24)) -
          Real.sinh (((Real.pi / (k : ℝ)) * Real.sqrt (2 / 3)) * Real.sqrt ((n : ℝ) - 1 / 24))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hx0 : 0 < (n : ℝ) - 1 / 24 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨x₀, hx0_def⟩ : ∃ x₀ : ℝ, x₀ = (n : ℝ) - 1 / 24 := ⟨_, rfl⟩
  have hx0' : 0 < x₀ := hx0_def ▸ hx0
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = Real.sqrt x₀ := ⟨_, rfl⟩
  have hu : 0 < u := hu_def ▸ Real.sqrt_pos.mpr hx0'
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (Real.pi / (k : ℝ)) * Real.sqrt (2 / 3) := ⟨_, rfl⟩
  have hsqrt_deriv : HasDerivAt Real.sqrt (1 / (2 * u)) x₀ := by
    rw [hu_def]; exact Real.hasDerivAt_sqrt hx0'.ne'
  have hnum_deriv : HasDerivAt (fun x : ℝ => Real.sinh (c * Real.sqrt x))
      (Real.cosh (c * u) * (c * (1 / (2 * u)))) x₀ := by
    have h1 : HasDerivAt (fun x : ℝ => c * Real.sqrt x) (c * (1 / (2 * u))) x₀ :=
      hsqrt_deriv.const_mul c
    convert h1.sinh using 1
    rw [← hu_def]
  have hdiv_deriv := hnum_deriv.fun_div hsqrt_deriv (by rw [← hu_def]; exact hu.ne')
  have hloc : (fun x : ℝ => Real.sinh ((Real.pi / (k : ℝ)) * Real.sqrt (2 * x / 3)) / Real.sqrt x) =ᶠ[𝓝 x₀]
      (fun x : ℝ => Real.sinh (c * Real.sqrt x) / Real.sqrt x) := by
    filter_upwards [eventually_gt_nhds hx0'] with x hx
    have hsq : Real.sqrt (2 * x / 3) = Real.sqrt (2 / 3) * Real.sqrt x := by
      rw [show 2 * x / 3 = (2 / 3) * x by ring, Real.sqrt_mul (by norm_num)]
    rw [hsq, hc_def]
    ring_nf
  have hderiv_val :
      deriv (fun x : ℝ => Real.sinh ((Real.pi / (k : ℝ)) * Real.sqrt (2 * x / 3)) / Real.sqrt x) x₀ =
        (c * u * Real.cosh (c * u) - Real.sinh (c * u)) / (2 * u ^ 3) := by
    rw [hloc.deriv_eq, hdiv_deriv.deriv, ← hu_def]
    field_simp [hu.ne']
  rw [rademacherPsi, ← hx0_def, hderiv_val, hu_def, hc_def, hx0_def]
  ring

/-- The leading Rademacher term `rademacherPsi 1 n` is asymptotically equivalent to
`hardyRamanujanMainTerm n` as `n → ∞`. -/
theorem rademacherPsi_one_isEquivalent :
    (fun n : ℕ => rademacherPsi 1 n) ~[Filter.atTop] hardyRamanujanMainTerm := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · set c : ℝ := Real.pi * Real.sqrt (2 / 3)
    have hc_pos : 0 < c := by positivity
    have hconst : c / (4 * Real.pi * Real.sqrt 2) = 1 / (4 * Real.sqrt 3) := by
      dsimp [c]
      have h23 : Real.sqrt (2 / 3) = Real.sqrt 2 / Real.sqrt 3 := Real.sqrt_div (by norm_num) 3
      rw [h23]
      field_simp [Real.pi_ne_zero, show Real.sqrt 2 ≠ 0 by positivity, show Real.sqrt 3 ≠ 0 by positivity]
    have hquot : ∀ᶠ n : ℕ in Filter.atTop,
        rademacherPsi 1 n / hardyRamanujanMainTerm n =
          ((n : ℝ) / ((n : ℝ) - 1 / 24)) *
            Real.exp (c * (Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ))) *
            (1 + Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24)) -
              (1 - Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24))) /
                (c * Real.sqrt ((n : ℝ) - 1 / 24))) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hx0 : 0 < (n : ℝ) - 1 / 24 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      set u : ℝ := Real.sqrt ((n : ℝ) - 1 / 24)
      have hu_pos : 0 < u := Real.sqrt_pos.mpr hx0
      have hu_sq : u ^ 2 = (n : ℝ) - 1 / 24 := Real.sq_sqrt hx0.le
      have hpsi := rademacherPsi_eq (k := 1) (n := n) le_rfl hn
      have hc1 : (Real.pi / ((1 : ℕ) : ℝ)) * Real.sqrt (2 / 3) = c := by simp [c]
      rw [hc1] at hpsi
      have hcosh : Real.cosh (c * u) = (Real.exp (c * u) + Real.exp (-(c * u))) / 2 :=
        Real.cosh_eq _
      have hsinh : Real.sinh (c * u) = (Real.exp (c * u) - Real.exp (-(c * u))) / 2 :=
        Real.sinh_eq _
      have hexp_sq : Real.exp (-(c * u)) = Real.exp (c * u) * Real.exp (-2 * c * u) := by
        rw [← Real.exp_add]; congr 1; ring
      have hnum : c * u * Real.cosh (c * u) - Real.sinh (c * u) =
          (c * u / 2) * Real.exp (c * u) *
            (1 + Real.exp (-2 * c * u) - (1 - Real.exp (-2 * c * u)) / (c * u)) := by
        rw [hcosh, hsinh, hexp_sq]
        field_simp [hc_pos.ne', hu_pos.ne']
      have hrhs_exp : Real.pi * Real.sqrt (2 * (n : ℝ) / 3) = c * Real.sqrt (n : ℝ) := by
        dsimp [c]
        rw [show 2 * (n : ℝ) / 3 = (2 / 3) * (n : ℝ) by ring, Real.sqrt_mul (by norm_num)]
        ring
      rw [hpsi, hnum, hardyRamanujanMainTerm, hrhs_exp]
      have hexp_diff : Real.exp (c * u) / Real.exp (c * Real.sqrt (n : ℝ)) =
          Real.exp (c * (u - Real.sqrt (n : ℝ))) := by
        rw [← Real.exp_sub]; congr 1; ring
      have hpow3 : u / u ^ 3 = 1 / u ^ 2 := by
        field_simp [hu_pos.ne']
      calc ((1 / (2 * Real.pi * Real.sqrt 2 * u ^ 3)) *
              ((c * u / 2) * Real.exp (c * u) *
                (1 + Real.exp (-2 * c * u) - (1 - Real.exp (-2 * c * u)) / (c * u)))) /
            ((1 / (4 * (n : ℝ) * Real.sqrt 3)) * Real.exp (c * Real.sqrt (n : ℝ)))
          = ((c / (4 * Real.pi * Real.sqrt 2)) / (1 / (4 * Real.sqrt 3))) *
              ((n : ℝ) * (u / u ^ 3)) *
              (Real.exp (c * u) / Real.exp (c * Real.sqrt (n : ℝ))) *
              (1 + Real.exp (-2 * c * u) - (1 - Real.exp (-2 * c * u)) / (c * u)) := by
            field_simp [Real.pi_ne_zero, show Real.sqrt 2 ≠ 0 by positivity,
              show Real.sqrt 3 ≠ 0 by positivity, hu_pos.ne', hn_pos.ne',
              (Real.exp_pos (c * Real.sqrt (n : ℝ))).ne']
            ring
        _ = ((n : ℝ) / ((n : ℝ) - 1 / 24)) *
              Real.exp (c * (u - Real.sqrt (n : ℝ))) *
              (1 + Real.exp (-2 * c * u) - (1 - Real.exp (-2 * c * u)) / (c * u)) := by
            rw [hconst, div_self (by positivity), one_mul, hpow3, hu_sq, hexp_diff]
            ring
    have hsqrt_atTop : Tendsto Real.sqrt atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun B =>
        ⟨max 0 B ^ 2, fun x hx => (le_max_right 0 B).trans (Real.le_sqrt_of_sq_le hx)⟩
    have ht1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1 / 24)) atTop (𝓝 1) := by
      have hdiv : Tendsto (fun n : ℕ => 1 / (1 - 1 / (24 * (n : ℝ)))) atTop (𝓝 1) := by
        have ht0 : Tendsto (fun n : ℕ => 1 / (24 * (n : ℝ))) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num))
        have hsub : Tendsto (fun n : ℕ => 1 - 1 / (24 * (n : ℝ))) atTop (𝓝 1) := by
          simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub ht0
        have hdiv1 := (tendsto_const_nhds (x := (1 : ℝ))).div hsub one_ne_zero
        rw [div_one] at hdiv1
        exact hdiv1
      refine hdiv.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp [hn0]
    have ht2 : Tendsto (fun n : ℕ => Real.exp (c * (Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ))))
        atTop (𝓝 1) := by
      have hdiff0 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
        have hbd : ∀ᶠ n : ℕ in Filter.atTop,
            |Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ)| ≤ 1 / (24 * Real.sqrt (n : ℝ)) := by
          filter_upwards [eventually_ge_atTop 1] with n hn
          have hx0 : 0 ≤ (n : ℝ) - 1 / 24 := by
            have : (1 : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          have hsqn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
          have hmul : (Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ)) *
              (Real.sqrt ((n : ℝ) - 1 / 24) + Real.sqrt (n : ℝ)) = -(1 / 24) := by
            have h1 := Real.sq_sqrt hx0
            have h2 := Real.sq_sqrt (Nat.cast_nonneg n)
            nlinarith
          have hsum_ge : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) - 1 / 24) + Real.sqrt (n : ℝ) := by
            linarith [Real.sqrt_nonneg ((n : ℝ) - 1 / 24)]
          have heq : Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ) =
              -(1 / 24) / (Real.sqrt ((n : ℝ) - 1 / 24) + Real.sqrt (n : ℝ)) := by
            rw [eq_div_iff (by positivity)]
            exact hmul
          rw [heq, abs_div, abs_neg, abs_of_pos (by norm_num), abs_of_pos (by positivity)]
          exact div_le_div_of_nonneg_left (by norm_num) hsqn hsum_ge |>.trans_eq (by ring)
        have hzero : Tendsto (fun n : ℕ => 1 / (24 * Real.sqrt (n : ℝ))) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            ((hsqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
        exact squeeze_zero_norm' hbd hzero
      have hmul0 : Tendsto (fun n : ℕ => c * (Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using hdiff0.const_mul c
      have hexp := (Real.continuous_exp.tendsto 0).comp hmul0
      rw [Real.exp_zero] at hexp
      exact hexp
    have ht3 : Tendsto (fun n : ℕ =>
        1 + Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24)) -
          (1 - Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24))) /
            (c * Real.sqrt ((n : ℝ) - 1 / 24))) atTop (𝓝 1) := by
      have hu_atTop : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) - 1 / 24)) atTop atTop :=
        hsqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      have hexp0 : Tendsto (fun n : ℕ => Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24))) atTop (𝓝 0) := by
        have hneg : Tendsto (fun n : ℕ => -2 * c * Real.sqrt ((n : ℝ) - 1 / 24)) atTop atBot := by
          have : (fun n : ℕ => -2 * c * Real.sqrt ((n : ℝ) - 1 / 24)) =
              fun n : ℕ => -(2 * c * Real.sqrt ((n : ℝ) - 1 / 24)) := by ext n; ring
          rw [this]
          exact tendsto_neg_atTop_atBot.comp (hu_atTop.const_mul_atTop (by positivity))
        exact Real.tendsto_exp_atBot.comp hneg
      have hdiv0 : Tendsto (fun n : ℕ =>
          (1 - Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24))) /
            (c * Real.sqrt ((n : ℝ) - 1 / 24))) atTop (𝓝 0) := by
        have hnum : Tendsto (fun n : ℕ => 1 - Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24)))
            atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hexp0
        have hden : Tendsto (fun n : ℕ => c * Real.sqrt ((n : ℝ) - 1 / 24)) atTop atTop :=
          hu_atTop.const_mul_atTop hc_pos
        exact hnum.div_atTop hden
      simpa using (tendsto_const_nhds.add hexp0).sub hdiv0
    have hmul3 : Tendsto (fun n : ℕ =>
        ((n : ℝ) / ((n : ℝ) - 1 / 24)) *
          Real.exp (c * (Real.sqrt ((n : ℝ) - 1 / 24) - Real.sqrt (n : ℝ))) *
          (1 + Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24)) -
            (1 - Real.exp (-2 * c * Real.sqrt ((n : ℝ) - 1 / 24))) /
              (c * Real.sqrt ((n : ℝ) - 1 / 24)))) atTop (𝓝 1) := by
      simpa using (ht1.mul ht2).mul ht3
    exact hmul3.congr' (hquot.mono fun n hn => hn.symm)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [hardyRamanujanMainTerm]
    positivity

/-- The Rademacher Kloosterman-type exponential sum `A_k(n)` parameterized by a Dedekind sum
function `s : ℤ → ℕ → ℝ`. -/
def rademacherKloostermanSum (s : ℤ → ℕ → ℝ) (k n : ℕ) : ℂ :=
  ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
    Complex.exp (Real.pi * Complex.I * (s h k : ℂ) -
      2 * Real.pi * Complex.I * (n : ℂ) * (h : ℂ) / (k : ℂ))

/-- For `k = 1`, `rademacherKloostermanSum s 1 n = 1` whenever `s 0 1 = 0`. -/
theorem rademacherKloostermanSum_one (s : ℤ → ℕ → ℝ) (hs0 : s 0 1 = 0) (n : ℕ) :
    rademacherKloostermanSum s 1 n = 1 := by
  unfold rademacherKloostermanSum
  have hfilt : (Finset.range 1).filter (fun h => Nat.Coprime h 1) = {0} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.lt_one_iff]
    constructor
    · rintro ⟨rfl, _⟩; rfl
    · rintro rfl; simp
  rw [hfilt, Finset.sum_singleton]
  simp [hs0]

/-- Trivial triangle-inequality bound `‖rademacherKloostermanSum s k n‖ ≤ k`. -/
theorem norm_rademacherKloostermanSum_le (s : ℤ → ℕ → ℝ) (k n : ℕ) :
    ‖rademacherKloostermanSum s k n‖ ≤ (k : ℝ) := by
  unfold rademacherKloostermanSum
  calc ‖∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
          Complex.exp (Real.pi * Complex.I * (s h k : ℂ) -
            2 * Real.pi * Complex.I * (n : ℂ) * (h : ℂ) / (k : ℂ))‖
      ≤ ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
          ‖Complex.exp (Real.pi * Complex.I * (s h k : ℂ) -
            2 * Real.pi * Complex.I * (n : ℂ) * (h : ℂ) / (k : ℂ))‖ := norm_sum_le _ _
    _ = ∑ _h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k), (1 : ℝ) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        have harg : Real.pi * Complex.I * (s h k : ℂ) -
            2 * Real.pi * Complex.I * (n : ℂ) * (h : ℂ) / (k : ℂ) =
            ((Real.pi * s h k - 2 * Real.pi * n * h / k : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [harg, Complex.norm_exp_ofReal_mul_I]
    _ = (((Finset.range k).filter (fun h => Nat.Coprime h k)).card : ℝ) := by simp
    _ ≤ (k : ℝ) := by
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_range k)

/-- **Rademacher Convergent Series Formula** for `partitionCount n`, parameterized by the
Dedekind sum `s : ℤ → ℕ → ℝ`. -/
def RademacherSeriesFormula (s : ℤ → ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    HasSum (fun k : ℕ+ =>
      (Real.sqrt (k : ℝ) : ℂ) * rademacherKloostermanSum s k n * (rademacherPsi k n : ℂ))
      (partitionCount n : ℂ)

private lemma rademacher_sinh_bound {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ y * Real.cosh y - Real.sinh y ∧ y * Real.cosh y - Real.sinh y ≤ (y ^ 3 / 3) * Real.cosh y := by
  have h1 : ∀ t : ℝ, 0 ≤ t → Real.sinh t ≤ t * Real.cosh t := by
    intro t ht
    let g : ℝ → ℝ := fun s => s * Real.cosh s - Real.sinh s
    have hg0 : g 0 = 0 := by simp [g]
    have hg_deriv : ∀ s : ℝ, HasDerivAt g (s * Real.sinh s) s := by
      intro s
      have hd := ((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)
      convert hd using 1
      · ext t'; rfl
      · dsimp only [id]; ring
    have hnonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ s * Real.sinh s := fun s hs =>
      mul_nonneg hs.1 (Real.sinh_nonneg_iff.mpr hs.1)
    have hmono : g 0 ≤ g t := by
      have hdiff : DifferentiableOn ℝ g (Set.Icc 0 t) := fun s _ => (hg_deriv s).differentiableAt.differentiableWithinAt
      have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hdiff.continuousOn
        (fun s hs => ((hg_deriv s).differentiableAt).differentiableWithinAt)
        fun s hs => by
          rw [(hg_deriv s).deriv]
          exact hnonneg s (interior_subset hs)
      exact hm (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
    linarith [hg0]
  refine ⟨by linarith [h1 y hy], ?_⟩
  let f : ℝ → ℝ := fun t => t ^ 3 / 3 * Real.cosh y - (t * Real.cosh t - Real.sinh t)
  have hf0 : f 0 = 0 := by simp [f]
  have hf_deriv : ∀ t : ℝ, HasDerivAt f (t ^ 2 * Real.cosh y - t * Real.sinh t) t := by
    intro t
    have h1d : HasDerivAt (fun t : ℝ => t ^ 3 / 3 * Real.cosh y) (t ^ 2 * Real.cosh y) t := by
      have h := ((hasDerivAt_pow 3 t).div_const 3).mul_const (Real.cosh y)
      convert h using 1; ring
    have h2d : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t) (t * Real.sinh t) t := by
      have h := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      convert h using 1
      · ext s; rfl
      · dsimp only [id]; ring
    exact h1d.sub h2d
  have hnonneg_f : ∀ t ∈ Set.Icc 0 y, 0 ≤ t ^ 2 * Real.cosh y - t * Real.sinh t := by
    intro t ht
    have hsinh := h1 t ht.1
    have hcosh_le : Real.cosh t ≤ Real.cosh y :=
      Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg ht.1, abs_of_nonneg hy]; exact ht.2)
    nlinarith [ht.1]
  have hmono_f : f 0 ≤ f y := by
    have hdiff : ContinuousOn f (Set.Icc 0 y) := by dsimp [f]; fun_prop
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 y) hdiff
      (fun t _ => (hf_deriv t).differentiableAt.differentiableWithinAt)
      fun t ht => by
        rw [(hf_deriv t).deriv]
        exact hnonneg_f t (interior_subset ht)
    exact hm (Set.left_mem_Icc.mpr hy) (Set.right_mem_Icc.mpr hy) hy
  dsimp [f] at hf0 hmono_f
  linarith

/-- **Structural Bridge**: `RademacherSeriesFormula s` implies `HardyRamanujanAsymptotic` whenever
`s 0 1 = 0`. -/
theorem hardyRamanujanAsymptotic_of_rademacher {s : ℤ → ℕ → ℝ} (hs0 : s 0 1 = 0)
    (hR : RademacherSeriesFormula s) : HardyRamanujanAsymptotic := by
  have hc_pos : 0 < Real.pi * Real.sqrt (2 / 3) := by positivity
  set c : ℝ := Real.pi * Real.sqrt (2 / 3)
  have htail_bound : ∀ n : ℕ, 1 ≤ n →
      |(partitionCount n : ℝ) - rademacherPsi 1 n| ≤
        (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) *
          ∑' k : ℕ+, (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro n hn
    have hhas := hR n hn
    have hk1 : (Real.sqrt (1 : ℝ) : ℂ) * rademacherKloostermanSum s 1 n *
        (rademacherPsi 1 n : ℂ) = (rademacherPsi 1 n : ℂ) := by
      simp [rademacherKloostermanSum_one s hs0 n]
    have hsub_has : HasSum (fun k : ℕ+ =>
        if k = 1 then (0 : ℂ)
        else (Real.sqrt (k : ℝ) : ℂ) * rademacherKloostermanSum s k n * (rademacherPsi k n : ℂ))
        ((partitionCount n : ℂ) - (rademacherPsi 1 n : ℂ)) := by
      have hsingle : HasSum (fun k : ℕ+ => if k = 1 then (rademacherPsi 1 n : ℂ) else 0)
          (rademacherPsi 1 n : ℂ) := hasSum_ite_eq 1 _
      have hdiff := hhas.sub hsingle
      refine hdiff.congr_fun fun k => ?_
      by_cases hk : k = 1
      · subst hk; simp only [↓reduceIte, PNat.val_ofNat, Nat.cast_one]; rw [hk1, sub_self]
      · simp [hk]
    have hx0 : 0 < (n : ℝ) - 1 / 24 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    set u : ℝ := Real.sqrt ((n : ℝ) - 1 / 24)
    have hu_pos : 0 < u := Real.sqrt_pos.mpr hx0
    have hu_le : u ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have hterm_bd : ∀ k : ℕ+,
        ‖if k = 1 then (0 : ℂ)
         else (Real.sqrt (k : ℝ) : ℂ) * rademacherKloostermanSum s k n * (rademacherPsi k n : ℂ)‖ ≤
          (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) *
            (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
      intro k
      by_cases hk : k = 1
      · subst hk; simp; positivity
      · simp only [hk, ↓reduceIte]
        have hk2 : 2 ≤ (k : ℕ) := by
          have hne1 : (k : ℕ) ≠ 1 := fun h => hk (PNat.coe_injective h)
          have := k.pos; omega
        have hkR : (0 : ℝ) < (k : ℝ) := by positivity
        have hpsi := rademacherPsi_eq k.pos hn
        set y : ℝ := (c / (k : ℝ)) * u
        have hy0 : 0 ≤ y := by positivity
        have hsb := rademacher_sinh_bound hy0
        have hcosh_le : Real.cosh y ≤ Real.exp (c * Real.sqrt (n : ℝ) / 2) := by
          have hy_le : y ≤ c * Real.sqrt (n : ℝ) / 2 := by
            have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
            calc (c / (k : ℝ)) * u ≤ (c / 2) * u :=
                  mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hc_pos.le (by norm_num) hkR2) hu_pos.le
              _ ≤ (c / 2) * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hu_le (by positivity)
              _ = c * Real.sqrt (n : ℝ) / 2 := by ring
          have hcos_exp : Real.cosh y ≤ Real.exp y := by
            rw [Real.cosh_eq]
            have hneg : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
            linarith
          exact hcos_exp.trans (Real.exp_le_exp.mpr hy_le)
        have hpsi_nonneg : 0 ≤ rademacherPsi k n := by
          rw [hpsi]
          have hcy : ((Real.pi / (k : ℝ)) * Real.sqrt (2 / 3)) * u = y := by
            dsimp [y, c]; ring
          rw [hcy]
          exact mul_nonneg (by positivity) hsb.1
        have hpsi_le : rademacherPsi k n ≤
            (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) / (k : ℝ) ^ 3 := by
          rw [hpsi]
          have hcy : ((Real.pi / (k : ℝ)) * Real.sqrt (2 / 3)) * u = y := by
            dsimp [y, c]; ring
          rw [hcy]
          have h1 : (y ^ 3 / 3) * Real.cosh y ≤
              (c ^ 3 * u ^ 3 / (3 * (k : ℝ) ^ 3)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) := by
            have hy3 : y ^ 3 / 3 = c ^ 3 * u ^ 3 / (3 * (k : ℝ) ^ 3) := by dsimp [y]; ring
            rw [hy3]
            exact mul_le_mul_of_nonneg_left hcosh_le (by positivity)
          calc (1 / (2 * Real.pi * Real.sqrt 2 * u ^ 3)) * (y * Real.cosh y - Real.sinh y)
              ≤ (1 / (2 * Real.pi * Real.sqrt 2 * u ^ 3)) * ((y ^ 3 / 3) * Real.cosh y) :=
                mul_le_mul_of_nonneg_left hsb.2 (by positivity)
            _ ≤ (1 / (2 * Real.pi * Real.sqrt 2 * u ^ 3)) *
                  ((c ^ 3 * u ^ 3 / (3 * (k : ℝ) ^ 3)) * Real.exp (c * Real.sqrt (n : ℝ) / 2)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) / (k : ℝ) ^ 3 := by
                field_simp [hu_pos.ne', hkR.ne', Real.pi_ne_zero, show Real.sqrt 2 ≠ 0 by positivity]
                ring
        have hnorm_eq :
            ‖(Real.sqrt (k : ℝ) : ℂ) * rademacherKloostermanSum s k n * (rademacherPsi k n : ℂ)‖ =
              Real.sqrt (k : ℝ) * ‖rademacherKloostermanSum s k n‖ * rademacherPsi k n := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpsi_nonneg]
        have hrpow : Real.sqrt (k : ℝ) * (k : ℝ) / (k : ℝ) ^ 3 = (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
          have h12 : Real.sqrt (k : ℝ) = (k : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
          have hk3 : (k : ℝ) ^ (3 : ℕ) = (k : ℝ) ^ (3 : ℝ) := by
            rw [← Real.rpow_natCast]; norm_num
          calc Real.sqrt (k : ℝ) * (k : ℝ) / (k : ℝ) ^ 3
              = (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) / (k : ℝ) ^ (3 : ℝ) := by rw [h12, hk3]
            _ = (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (1 : ℝ) / (k : ℝ) ^ (3 : ℝ) := by rw [Real.rpow_one]
            _ = (k : ℝ) ^ (1 / 2 + 1 - 3 : ℝ) := by
                rw [← Real.rpow_add hkR, ← Real.rpow_sub hkR]
            _ = (k : ℝ) ^ (-(3 / 2 : ℝ)) := by congr 1; norm_num
        rw [hnorm_eq]
        calc Real.sqrt (k : ℝ) * ‖rademacherKloostermanSum s k n‖ * rademacherPsi k n
            ≤ Real.sqrt (k : ℝ) * (k : ℝ) *
                ((c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) / (k : ℝ) ^ 3) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (norm_rademacherKloostermanSum_le s k n) (Real.sqrt_nonneg _))
                hpsi_le hpsi_nonneg (by positivity)
          _ = (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) *
                (Real.sqrt (k : ℝ) * (k : ℝ) / (k : ℝ) ^ 3) := by ring
          _ = (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) *
                (k : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [hrpow]
    have hsumm_rpow : Summable fun k : ℕ+ => (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
      have hN : Summable fun k : ℕ => ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      have hN' : Summable fun k : ℕ => (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
        refine hN.congr fun k => ?_
        rw [Real.rpow_neg (Nat.cast_nonneg k)]
      exact hN'.comp_injective PNat.coe_injective
    have hsumm_rhs := hsumm_rpow.mul_left ((c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2))
    have hsumm_lhs : Summable fun k : ℕ+ =>
        ‖if k = 1 then (0 : ℂ)
         else (Real.sqrt (k : ℝ) : ℂ) * rademacherKloostermanSum s k n * (rademacherPsi k n : ℂ)‖ :=
      hsumm_rhs.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bd
    have hcast : |(partitionCount n : ℝ) - rademacherPsi 1 n| =
        ‖(partitionCount n : ℂ) - (rademacherPsi 1 n : ℂ)‖ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hcast, ← hsub_has.tsum_eq]
    calc ‖∑' k : ℕ+, if k = 1 then (0 : ℂ)
            else (Real.sqrt (k : ℝ) : ℂ) * rademacherKloostermanSum s k n * (rademacherPsi k n : ℂ)‖
        ≤ ∑' k : ℕ+, ‖if k = 1 then (0 : ℂ)
            else (Real.sqrt (k : ℝ) : ℂ) * rademacherKloostermanSum s k n * (rademacherPsi k n : ℂ)‖ :=
          norm_tsum_le_tsum_norm hsumm_lhs
      _ ≤ ∑' k : ℕ+, (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) *
            (k : ℝ) ^ (-(3 / 2 : ℝ)) :=
          hsumm_lhs.tsum_le_tsum hterm_bd hsumm_rhs
      _ = (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) *
            ∑' k : ℕ+, (k : ℝ) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
  let K : ℝ := (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * ∑' k : ℕ+, (k : ℝ) ^ (-(3 / 2 : ℝ))
  have hlittle : (fun n : ℕ => (partitionCount n : ℝ) - rademacherPsi 1 n) =o[Filter.atTop]
      hardyRamanujanMainTerm := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg (by positivity) (tsum_nonneg fun k => by positivity)
    have htend0 : Tendsto (fun n : ℕ =>
        4 * Real.sqrt 3 * K * (n : ℝ) * Real.exp (-(c * Real.sqrt (n : ℝ) / 2))) atTop (𝓝 0) := by
      have hsqrt_atTop : Tendsto Real.sqrt atTop atTop :=
        Filter.tendsto_atTop_atTop.mpr fun B =>
          ⟨max 0 B ^ 2, fun x hx => (le_max_right 0 B).trans (Real.le_sqrt_of_sq_le hx)⟩
      have h1 : Tendsto (fun u : ℝ => u ^ 2 * Real.exp (-(c / 2 * u))) atTop (𝓝 0) :=
        (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (c / 2) (by positivity)).congr
          fun u => by simp [neg_mul]
      have h2 := (h1.comp (hsqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul
        (4 * Real.sqrt 3 * K)
      have h2' : Tendsto (fun n : ℕ =>
          4 * Real.sqrt 3 * K * (Real.sqrt (n : ℝ) ^ 2 * Real.exp (-(c / 2 * Real.sqrt (n : ℝ))))) atTop (𝓝 0) := by
        simpa [Function.comp_apply, mul_zero] using h2
      refine h2'.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
      simp only [hsq]
      ring_nf
    filter_upwards [htend0.eventually (Iic_mem_nhds hε), eventually_ge_atTop 1] with n hn1 hn2
    have hbd := htail_bound n hn2
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn2
    have hhr_pos : 0 < hardyRamanujanMainTerm n := by
      dsimp [hardyRamanujanMainTerm]; positivity
    have hhr_eq : hardyRamanujanMainTerm n =
        (1 / (4 * (n : ℝ) * Real.sqrt 3)) * Real.exp (c * Real.sqrt (n : ℝ)) := by
      dsimp [hardyRamanujanMainTerm, c]
      rw [show 2 * (n : ℝ) / 3 = (2 / 3) * (n : ℝ) by ring, Real.sqrt_mul (by norm_num)]
      ring_nf
    have hnorm1 : ‖(partitionCount n : ℝ) - rademacherPsi 1 n‖ ≤
        K * Real.exp (c * Real.sqrt (n : ℝ) / 2) := by
      rw [Real.norm_eq_abs]
      calc |(partitionCount n : ℝ) - rademacherPsi 1 n|
          ≤ (c ^ 3 / (6 * Real.pi * Real.sqrt 2)) * Real.exp (c * Real.sqrt (n : ℝ) / 2) *
              ∑' k : ℕ+, (k : ℝ) ^ (-(3 / 2 : ℝ)) := hbd
        _ = K * Real.exp (c * Real.sqrt (n : ℝ) / 2) := by dsimp [K]; ring
    have hquot_eq : K * Real.exp (c * Real.sqrt (n : ℝ) / 2) =
        (4 * Real.sqrt 3 * K * (n : ℝ) * Real.exp (-(c * Real.sqrt (n : ℝ) / 2))) *
          ‖hardyRamanujanMainTerm n‖ := by
      rw [Real.norm_eq_abs, abs_of_pos hhr_pos, hhr_eq]
      have hexp : Real.exp (-(c * Real.sqrt (n : ℝ) / 2)) * Real.exp (c * Real.sqrt (n : ℝ)) =
          Real.exp (c * Real.sqrt (n : ℝ) / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      calc K * Real.exp (c * Real.sqrt (n : ℝ) / 2)
          = K * (Real.exp (-(c * Real.sqrt (n : ℝ) / 2)) * Real.exp (c * Real.sqrt (n : ℝ))) := by
            rw [hexp]
        _ = (4 * Real.sqrt 3 * K * (n : ℝ) * Real.exp (-(c * Real.sqrt (n : ℝ) / 2))) *
              ((1 / (4 * (n : ℝ) * Real.sqrt 3)) * Real.exp (c * Real.sqrt (n : ℝ))) := by
            field_simp [hn_pos.ne', show Real.sqrt 3 ≠ 0 by positivity]

    calc ‖(partitionCount n : ℝ) - rademacherPsi 1 n‖
        ≤ K * Real.exp (c * Real.sqrt (n : ℝ) / 2) := hnorm1
      _ = (4 * Real.sqrt 3 * K * (n : ℝ) * Real.exp (-(c * Real.sqrt (n : ℝ) / 2))) *
            ‖hardyRamanujanMainTerm n‖ := hquot_eq
      _ ≤ ε * ‖hardyRamanujanMainTerm n‖ := mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)
  have hfin := rademacherPsi_one_isEquivalent.add_isLittleO hlittle
  exact hfin.congr_left (Filter.Eventually.of_forall fun n => by dsimp; ring)

end CircleMethodAndRademacher

end AnalyticNumberTheory.ModularAndPartitions



