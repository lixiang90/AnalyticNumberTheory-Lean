import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PhragmenLindelof
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.Summation.EulerMaclaurin

/-!
# Functional Equation, Continuation, and Convexity Bounds for Dirichlet L-Functions

This file develops the global analytic theory of Dirichlet L-functions `L(s, χ)` modulo `q ≥ 1`
(`DirichletCharacter.LFunction χ s`):

1. **Analytic continuation & Abel / Euler–Maclaurin continuation**:
   - Meromorphic continuation of `L(s, χ)` to `ℂ` (holomorphic for `s ≠ 1`, and entire when
     `χ ≠ 1`), plus level-change and trivial-character bridge to `ζ(s)`.
   - First-order Abel / Euler–Maclaurin integral representation
     `L(s, χ) = s * ∫ t in Ioi 1, S_χ(t) * t^(-s-1)` valid for all `Re s > 0` when `χ ≠ 1`.
   - Second-order continuation formulas valid for `Re s > -1` (yielding polynomial vertical
     growth on strips for `L(s, χ)` and `(s - 1) * ζ(s)`).

2. **Completed L-function and functional equation**:
   - Parity exponent `κ ∈ {0, 1}`, Gamma factor `π^(-(s+κ)/2) Γ((s+κ)/2)`, completed L-function
     `completedLFunction χ s`, unit-modulus root number `rootNumber χ`, and the symmetric and
     asymmetric functional equations for primitive characters relating `χ` and `star χ`.

3. **Uniform Phragmén–Lindelöf convexity strip bounds**:
   - Uniform convexity estimate
     `‖L(σ + t*I, χ)‖ ≤ C * (q * (|t| + 2))^((1 - σ)/2 + ε)`
     for `σ ∈ [0, 1]` (both for `χ ≠ 1` and for `χ = 1` with `|t| ≥ 1`), proved via
     Rademacher's Gamma-weight trick, Stirling's formula, and Phragmén–Lindelöf on `[-δ, 1 + δ]`.

4. **Upper bound at `s = 1`**:
   - For non-principal characters `χ ≠ 1` modulo `q ≥ 2`, `‖L(1, χ)‖ ≤ log q + 1 ≤ 2 * log (q + 2)`.
-/

noncomputable section

open Complex MeasureTheory Filter
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open scoped Topology BigOperators Classical

namespace AnalyticNumberTheory.DirichletLFunctions

section Helpers

private lemma norm_cpow_ofReal_exponent {z : ℂ} (hz : z ≠ 0) (c : ℝ) :
    ‖z ^ (c : ℂ)‖ = ‖z‖ ^ c := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  have hre : (Complex.log z * (c : ℂ)).re = (Complex.log z).re * c := by simp
  rw [hre, Complex.log_re, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

private lemma norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnR]

private lemma ofReal_cpow_hasDerivAt {t : ℝ} (ht : 0 < t) (w : ℂ) :
    HasDerivAt (fun x : ℝ ↦ (x : ℂ) ^ w) (w * (t : ℂ) ^ (w - 1)) t := by
  have hmem : (t : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [ht]))
  simpa [mul_comm] using (HasDerivAt.cpow_const (hasDerivAt_id (t : ℂ)) hmem).comp_ofReal

private lemma log_le_rpow_div (t : ℝ) (ht : 1 ≤ t) {η : ℝ} (hη : 0 < η) :
    Real.log t ≤ t ^ η / η := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : η * Real.log t = Real.log (t ^ η) := (Real.log_rpow ht_pos η).symm
  have h2 : Real.log (t ^ η) ≤ t ^ η - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht_pos η)
  rw [le_div_iff₀' hη]
  linarith

private lemma rpow_le_exp_of_nonneg {x B : ℝ} (hx : 1 ≤ x) (hB : 0 ≤ B) :
    x ^ B ≤ Real.exp (B * x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.rpow_def_of_pos hx_pos]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx_pos).trans (by linarith)
  linarith [mul_le_mul_of_nonneg_left hlog hB]

private lemma finset_prod_rpow (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p ∈ s, 0 ≤ f p) (r : ℝ) :
    (∏ p ∈ s, f p) ^ r = ∏ p ∈ s, (f p) ^ r := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a (Finset.mem_insert_self a s))
        (Finset.prod_nonneg fun p hp ↦ hf p (Finset.mem_insert_of_mem hp)),
      ih fun p hp ↦ hf p (Finset.mem_insert_of_mem hp)]

private lemma prod_euler_factor_norm_le (q : ℕ) (c : ℕ → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1)
    {σ t : ℝ} (hσ : 0 ≤ σ) :
    ‖∏ p ∈ q.primeFactors, (1 - c p * (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))‖ ≤
      (2 : ℝ) ^ q.primeFactors.card := by
  let f : ℕ → ℂ := fun p ↦ 1 - c p * (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
  have hind : ∀ s : Finset ℕ, (∀ p ∈ s, ‖f p‖ ≤ 2) → ‖∏ p ∈ s, f p‖ ≤ (2 : ℝ) ^ s.card := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      exact (norm_mul_le _ _).trans
        (mul_le_mul (hs a (Finset.mem_insert_self a s))
          (ih fun p hp ↦ hs p (Finset.mem_insert_of_mem hp))
          (norm_nonneg _) (by norm_num))
  refine hind q.primeFactors fun p hp ↦ ?_
  have hp_pos := (Nat.prime_of_mem_primeFactors hp).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have hp_pow : ‖(p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ 1 := by
    rw [norm_natCast_cpow_of_pos hp_pos]
    have hre : (-((σ : ℂ) + (t : ℂ) * I)).re = -σ := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  dsimp only [f]
  calc
    ‖1 - c p * (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
        ≤ ‖(1 : ℂ)‖ + ‖c p * (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ := norm_sub_le _ _
    _ ≤ 1 + 1 * 1 := by
        rw [norm_one, norm_mul]
        exact add_le_add le_rfl (mul_le_mul (hc p) hp_pow (norm_nonneg _) zero_le_one)
    _ = 2 := by norm_num

private lemma prod_two_le_rpow {η : ℝ} (hη : 0 < η) (q : ℕ) (hq : 0 < q) :
    (2 : ℝ) ^ q.primeFactors.card ≤
      (2 : ℝ) ^ (Nat.ceil ((2 : ℝ) ^ (1 / η))) * (q : ℝ) ^ η := by
  let B : ℝ := (2 : ℝ) ^ (1 / η)
  let s₁ : Finset ℕ := q.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) < B)
  let s₂ : Finset ℕ := q.primeFactors.filter (fun p : ℕ ↦ B ≤ (p : ℝ))
  have hpart : q.primeFactors = s₁ ∪ s₂ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, s₁, s₂]
    by_cases h : (p : ℝ) < B
    · simp [h]
    · simp [h, not_lt.mp h]
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter, s₁, s₂] at h1 h2
    linarith
  have hs₁_card : s₁.card ≤ Nat.ceil B := by
    have hsub : s₁ ⊆ Finset.range (Nat.ceil B) := by
      intro p hp
      simp only [Finset.mem_filter, s₁] at hp
      simp only [Finset.mem_range]
      have hp_lt_ceil : (p : ℝ) < (Nat.ceil B : ℝ) := lt_of_lt_of_le hp.2 (Nat.le_ceil B)
      exact_mod_cast hp_lt_ceil
    exact (Finset.card_le_card hsub).trans (by simp)
  have hs₂_le : ∏ p ∈ s₂, ((2 : ℝ) / (p : ℝ) ^ η) ≤ 1 := by
    have hprod_le_one : ∀ s : Finset ℕ,
        (∀ p ∈ s, 0 ≤ (2 : ℝ) / (p : ℝ) ^ η ∧ (2 : ℝ) / (p : ℝ) ^ η ≤ 1) →
          ∏ p ∈ s, ((2 : ℝ) / (p : ℝ) ^ η) ≤ 1 := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        have h1 := hs a (Finset.mem_insert_self a s)
        have h2 := ih fun p hp ↦ hs p (Finset.mem_insert_of_mem hp)
        nlinarith
    refine hprod_le_one s₂ fun p hp ↦ ?_
    simp only [Finset.mem_filter, s₂] at hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp.1
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
    have hp_rpow_pos : 0 < (p : ℝ) ^ η := Real.rpow_pos_of_pos hp_pos η
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hp_rpow_pos]
    calc
      (2 : ℝ) = ((2 : ℝ) ^ (1 / η)) ^ η := by
        rw [← Real.rpow_mul two_pos.le, one_div_mul_cancel hη.ne', Real.rpow_one]
      _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hp.2 hη.le
  have hs₁_le : ∏ p ∈ s₁, ((2 : ℝ) / (p : ℝ) ^ η) ≤ (2 : ℝ) ^ (Nat.ceil B) := by
    calc
      ∏ p ∈ s₁, ((2 : ℝ) / (p : ℝ) ^ η) ≤ ∏ _p ∈ s₁, (2 : ℝ) := by
        have hle_prod : ∀ s : Finset ℕ, (∀ p ∈ s, 0 ≤ (2 : ℝ) / (p : ℝ) ^ η ∧
            (2 : ℝ) / (p : ℝ) ^ η ≤ 2) →
            ∏ p ∈ s, ((2 : ℝ) / (p : ℝ) ^ η) ≤ ∏ _p ∈ s, (2 : ℝ) := by
          intro s hs
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha]
            have h1 := hs a (Finset.mem_insert_self a s)
            have h2 := ih fun p hp ↦ hs p (Finset.mem_insert_of_mem hp)
            exact mul_le_mul h1.2 h2
              (Finset.prod_nonneg fun p hp ↦ (hs p (Finset.mem_insert_of_mem hp)).1)
              (by norm_num)
        refine hle_prod s₁ fun p hp ↦ ?_
        simp only [Finset.mem_filter, s₁] at hp
        have hp_prime := Nat.prime_of_mem_primeFactors hp.1
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp_prime.one_lt.le
        have hrpow1 : (1 : ℝ) ≤ (p : ℝ) ^ η := Real.one_le_rpow hp1 hη.le
        exact ⟨by positivity, div_le_self (by norm_num) hrpow1⟩
      _ = (2 : ℝ) ^ s₁.card := by simp
      _ ≤ (2 : ℝ) ^ Nat.ceil B := pow_le_pow_right₀ (by norm_num) hs₁_card
  have hprod_p : (∏ p ∈ q.primeFactors, (p : ℝ)) ^ η ≤ (q : ℝ) ^ η := by
    have hnat : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    have hreal : ∏ p ∈ q.primeFactors, (p : ℝ) ≤ (q : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast hnat
    exact Real.rpow_le_rpow (Finset.prod_nonneg fun p _ ↦ Nat.cast_nonneg p) hreal hη.le
  have hratio : ∏ p ∈ q.primeFactors, ((2 : ℝ) / (p : ℝ) ^ η) ≤ (2 : ℝ) ^ Nat.ceil B := by
    rw [hpart, Finset.prod_union hdisj]
    calc
      (∏ p ∈ s₁, ((2 : ℝ) / (p : ℝ) ^ η)) * (∏ p ∈ s₂, ((2 : ℝ) / (p : ℝ) ^ η))
          ≤ (2 : ℝ) ^ Nat.ceil B * 1 :=
            mul_le_mul hs₁_le hs₂_le (Finset.prod_nonneg fun p _ ↦ by positivity) (by positivity)
      _ = (2 : ℝ) ^ Nat.ceil B := mul_one _
  have hfactor : (2 : ℝ) ^ q.primeFactors.card =
      (∏ p ∈ q.primeFactors, ((2 : ℝ) / (p : ℝ) ^ η)) * (∏ p ∈ q.primeFactors, (p : ℝ)) ^ η := by
    rw [finset_prod_rpow q.primeFactors (fun p ↦ (p : ℝ)) (fun p _ ↦ Nat.cast_nonneg p) η,
      ← Finset.prod_mul_distrib]
    calc
      (2 : ℝ) ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (2 : ℝ) := by simp
      _ = ∏ p ∈ q.primeFactors, ((2 : ℝ) / (p : ℝ) ^ η * (p : ℝ) ^ η) := by
          refine Finset.prod_congr rfl fun p hp ↦ ?_
          have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
          have hp_rpow : (p : ℝ) ^ η ≠ 0 := (Real.rpow_pos_of_pos hp_pos η).ne'
          field_simp [hp_rpow]
  rw [hfactor]
  exact mul_le_mul hratio hprod_p (Real.rpow_nonneg (Finset.prod_nonneg fun p _ ↦ Nat.cast_nonneg p) _)
    (by positivity)

private lemma sum_Ico_succ_sub_eq {E : Type*} [AddCommGroup E] (f : ℕ → E) {M N : ℕ}
    (hMN : M ≤ N) :
    ∑ k ∈ Finset.Ico M N, (f (k + 1) - f k) = f N - f M := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ K hMK ih =>
    rw [Finset.sum_Ico_succ_top hMK, ih]
    abel

private lemma ae_ne_real (a : ℝ) : ∀ᵐ t ∂volume, t ≠ a := by
  rw [ae_iff]
  simp

private lemma sum_intervalIntegrable_adjacent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    ∀ N : ℕ, 1 ≤ N →
      (∀ n ∈ Finset.Ico 1 N, IntervalIntegrable g volume (n : ℝ) ((n + 1 : ℕ) : ℝ)) →
        ∑ n ∈ Finset.Ico 1 N, ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), g t =
          ∫ t in (1 : ℝ)..(N : ℝ), g t := by
  intro N hN hg
  have hint := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)) (f := g) (n := N - 1)
  have heq_sum : ∑ k ∈ Finset.range (N - 1),
      ∫ t in ((k + 1 : ℕ) : ℝ)..(((k + 1) + 1 : ℕ) : ℝ), g t =
      ∑ n ∈ Finset.Ico 1 N, ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), g t := by
    refine Finset.sum_bij (fun k _ ↦ k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ico]; omega
    · intro k₁ _ k₂ _ h; omega
    · intro n hn; simp only [Finset.mem_Ico] at hn
      refine ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _; rfl
  rw [← heq_sum]
  have hint' := hint fun k hk ↦
    hg (k + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  simpa [Nat.sub_add_cancel hN] using hint'

private lemma sum_Icc_one_rpow_neg_le_one_add_inv {σ : ℝ} (hσ : 0 < σ) :
    ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 + σ)) ≤ 1 + 1 / σ := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; positivity
  · have hsum_le : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 + σ)) ≤
        1 + ∫ t in (1 : ℝ)..(N : ℝ), t ^ (-(1 + σ)) := by
      have hsplit : Finset.Icc 1 N = insert 1 (Finset.Ioc 1 N) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
      rw [hsplit, Finset.sum_insert (by simp), Nat.cast_one, Real.one_rpow]
      gcongr
      have hstep : ∑ n ∈ Finset.Ioc 1 N, (n : ℝ) ^ (-(1 + σ)) ≤
          ∑ n ∈ Finset.Ico 1 N, ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), t ^ (-(1 + σ)) := by
        have hbij : ∑ n ∈ Finset.Ioc 1 N, (n : ℝ) ^ (-(1 + σ)) =
            ∑ n ∈ Finset.Ico 1 N, ((n + 1 : ℕ) : ℝ) ^ (-(1 + σ)) := by
          refine Finset.sum_bij (fun n _ ↦ n - 1) ?_ ?_ ?_ ?_
          · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_Ico]; omega
          · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ioc] at hn₁ hn₂; omega
          · intro k hk; simp only [Finset.mem_Ico] at hk
            refine ⟨k + 1, by simp only [Finset.mem_Ioc]; omega, by omega⟩
          · intro n hn; simp only [Finset.mem_Ioc] at hn; congr 2; omega
        rw [hbij]
        refine Finset.sum_le_sum fun n hn ↦ ?_
        simp only [Finset.mem_Ico] at hn
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn.1
        have hle : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
        have hconst : ((n + 1 : ℕ) : ℝ) ^ (-(1 + σ)) =
            ∫ _t in (n : ℝ)..((n + 1 : ℕ) : ℝ), ((n + 1 : ℕ) : ℝ) ^ (-(1 + σ)) := by
          rw [intervalIntegral.integral_const, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
            smul_eq_mul, one_mul]
        rw [hconst]
        refine intervalIntegral.integral_mono_on hle intervalIntegrable_const ?_ fun t ht ↦ ?_
        · exact ContinuousOn.intervalIntegrable (fun t ht ↦ by
            refine (Real.continuousAt_rpow_const t (-(1 + σ)) (Or.inl ?_)).continuousWithinAt
            rw [Set.uIcc_of_le hle] at ht
            linarith [ht.1])
        · exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hn_pos ht.1) ht.2 (by linarith)
      have hcomb := sum_intervalIntegrable_adjacent (fun t : ℝ ↦ t ^ (-(1 + σ))) N hN fun n hn ↦ by
        simp only [Finset.mem_Ico] at hn
        have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
        rw [Set.uIcc_of_le hle] at ht
        refine (Real.continuousAt_rpow_const t (-(1 + σ)) (Or.inl ?_)).continuousWithinAt
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn.1
        linarith [ht.1]
      exact hstep.trans hcomb.le
    have hint_val : ∫ t in (1 : ℝ)..(N : ℝ), t ^ (-(1 + σ)) ≤ 1 / σ := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hint := integral_rpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -(1 + σ))
        (Or.inr ⟨by linarith, fun hx ↦ by rw [Set.uIcc_of_le hN1] at hx; linarith [hx.1]⟩)
      rw [hint, show -(1 + σ) + 1 = -σ by ring, Real.one_rpow]
      have hN_nonneg : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg N) (-σ)
      rw [show ((N : ℝ) ^ (-σ) - 1) / (-σ) = (1 - (N : ℝ) ^ (-σ)) / σ by ring]
      exact div_le_div_of_nonneg_right (by linarith) hσ.le
    linarith

private lemma norm_LSeries_le_one_add_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hsumm : LSeriesSummable (fun n : ℕ ↦ χ n) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hnorm_summ : Summable (fun n : ℕ ↦ ‖LSeries.term (fun k ↦ χ k) s n‖) := hsumm.norm
  have hle_tsum : ‖LSeries (fun n ↦ χ n) s‖ ≤ ∑' n : ℕ, ‖LSeries.term (fun k ↦ χ k) s n‖ :=
    norm_tsum_le_tsum_norm hnorm_summ
  have hσ_pos : 0 < s.re - 1 := sub_pos.mpr hs
  have hbound : ∑' n : ℕ, ‖LSeries.term (fun k ↦ χ k) s n‖ ≤ 1 + 1 / (s.re - 1) := by
    have hterm : ∀ n : ℕ, ‖LSeries.term (fun k ↦ χ k) s n‖ ≤
        if n = 0 then 0 else (n : ℝ) ^ (-s.re) := by
      intro n
      by_cases hn : n = 0
      · simp [hn, LSeries.term]
      · simp only [hn, ite_false, LSeries.term_of_ne_zero hn]
        rw [norm_div, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
          Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
        exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
    have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), ‖LSeries.term (fun k ↦ χ k) s n‖ ≤
        1 + 1 / (s.re - 1) := by
      intro N
      calc
        ∑ n ∈ Finset.range (N + 1), ‖LSeries.term (fun k ↦ χ k) s n‖
            ≤ ∑ n ∈ Finset.range (N + 1), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-s.re)) :=
              Finset.sum_le_sum fun n _ ↦ hterm n
        _ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s.re) := by
              rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1)]
              simp only [ite_true, zero_add]
              have hico : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
                ext n; simp [Finset.mem_Ico, Finset.mem_Icc]
              rw [hico]
              refine Finset.sum_congr rfl fun n hn ↦ ?_
              have hnz : n ≠ 0 := by simp only [Finset.mem_Icc] at hn; omega
              simp [hnz]
        _ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 + (s.re - 1))) := by
              refine Finset.sum_congr rfl fun n _ ↦ ?_
              ring_nf
        _ ≤ 1 + 1 / (s.re - 1) := sum_Icc_one_rpow_neg_le_one_add_inv hσ_pos N
    refine Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _) fun k ↦ ?_
    cases k with
    | zero => simp; positivity
    | succ N => exact hpart N
  exact hle_tsum.trans hbound

private lemma norm_riemannZeta_le_one_add_inv {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  have h := norm_LSeries_le_one_add_inv (1 : DirichletCharacter ℂ 1) hs
  rwa [DirichletCharacter.LFunction_modOne_eq] at h

private lemma integral_Ioi_bounded_log_cpow_differentiableOn
    {V : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hV_bound : ∀ t : ℝ, ‖V t‖ ≤ M)
    (hV_meas : Measurable V) :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-z - 2))
      {z : ℂ | -1 < z.re} := by
  let F : ℂ → ℝ → ℂ := fun z t ↦ V t * (t : ℂ) ^ (-z - 2)
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    intro z
    have hpow : Measurable (fun t : ℝ ↦ (t : ℂ) ^ (-z - 2)) :=
      Complex.continuous_ofReal.measurable.pow_const (-z - 2)
    exact (hV_meas.mul hpow).aestronglyMeasurable
  have hF_int : ∀ z : ℂ, -1 < z.re → IntegrableOn (F z) (Set.Ioi (1 : ℝ)) := by
    intro z hz
    have hint_bound : IntegrableOn (fun t : ℝ ↦ M * t ^ (-z.re - 2)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -z.re - 2) (by linarith) zero_lt_one).const_mul M
    refine hint_bound.mono' (hF_meas z) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-z - 2).re = -z.re - 2 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hV_bound t) (Real.rpow_nonneg ht0.le _)
  intro z₀ hz₀
  have hz₀' : -1 < z₀.re := hz₀
  let r := (z₀.re + 1) / 2
  have hr : 0 < r := half_pos (by linarith)
  have hball_mem : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  let σ₀ := z₀.re - r
  have hσ₀ : -1 < σ₀ := by dsimp only [σ₀, r]; linarith
  let F' : ℂ → ℝ → ℂ := fun z t ↦ V t * (-(Complex.log (t : ℂ)) * (t : ℂ) ^ (-z - 2))
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hlog : Measurable (fun t : ℝ ↦ -Complex.log (t : ℂ)) :=
      (Complex.measurable_log.comp Complex.continuous_ofReal.measurable).neg
    have hpow : Measurable (fun t : ℝ ↦ (t : ℂ) ^ (-z₀ - 2)) :=
      Complex.continuous_ofReal.measurable.pow_const (-z₀ - 2)
    exact (hV_meas.mul (hlog.mul hpow)).aestronglyMeasurable
  let η := (σ₀ + 1) / 2
  have hη : 0 < η := half_pos (by linarith)
  let bound : ℝ → ℝ := fun t ↦ M / η * t ^ (-σ₀ + η - 2)
  have hbound_int : IntegrableOn bound (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -σ₀ + η - 2) (by dsimp only [η]; linarith)
      zero_lt_one).const_mul _
  have hF_meas_nhds : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    Filter.Eventually.of_forall hF_meas
  have hbound_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r, ‖F' z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hzr : σ₀ ≤ z.re := by
      have hd : ‖z - z₀‖ < r := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz
      have hre_diff : |z.re - z₀.re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm (z - z₀)
      dsimp only [σ₀]
      linarith [(abs_le.mp (hre_diff.trans hd.le)).1]
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_neg, ← Complex.ofReal_log ht0.le, Complex.norm_real,
      Real.norm_of_nonneg hlog_nn, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-z - 2).re = -z.re - 2 := by simp
    rw [hre]
    have hrpow_le : t ^ (-z.re - 2) ≤ t ^ (-σ₀ - 2) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have hlog_le : Real.log t ≤ t ^ η / η := log_le_rpow_div t ht1.le hη
    calc
      ‖V t‖ * (Real.log t * t ^ (-z.re - 2))
          ≤ M * ((t ^ η / η) * t ^ (-σ₀ - 2)) :=
            mul_le_mul (hV_bound t)
              (mul_le_mul hlog_le hrpow_le (by positivity) (by positivity))
              (by positivity) hM
      _ = M / η * (t ^ η * t ^ (-σ₀ - 2)) := by ring
      _ = M / η * t ^ (-σ₀ + η - 2) := by
            rw [← Real.rpow_add ht0]
            ring_nf
  have hdiff_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r, HasDerivAt (F · t) (F' z t) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z _
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hinner_d : HasDerivAt (fun w : ℂ ↦ -w - 2) (-1) z :=
      ((hasDerivAt_id z).neg).sub_const 2
    have hcpow := HasDerivAt.const_cpow (c := (t : ℂ)) hinner_d (Or.inl htc)
    convert hcpow.const_mul (V t) using 1
    dsimp only [F']
    ring
  have hderiv_int := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    hball_mem hF_meas_nhds (hF_int z₀ hz₀') hF'_meas hbound_ae hbound_int hdiff_ae).2
  exact hderiv_int.differentiableAt.differentiableWithinAt

end Helpers

section ContinuationAndEulerMaclaurin

/-- Analytic continuation of `DirichletCharacter.LFunction χ`: differentiable at every `s ≠ 1`,
and entire whenever `χ ≠ 1`. -/
theorem differentiableAt_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
  DirichletCharacter.differentiableAt_LFunction χ s hs

/-- For non-principal `χ ≠ 1`, `DirichletCharacter.LFunction χ` is entire on `ℂ`. -/
theorem differentiable_LFunction_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  DirichletCharacter.differentiable_LFunction hχ

/-- For `Re s > 1`, `DirichletCharacter.LFunction χ s` equals the Dirichlet series `LSeries (χ ·) s`. -/
theorem LFunction_eq_LSeries_of_one_lt_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = LSeries (fun n ↦ χ n) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

/-- Level-change Euler-factor identity for `LFunction`. -/
theorem LFunction_changeLevel_eq {d q : ℕ} [NeZero d] [NeZero q] (hdq : d ∣ q)
    (χ : DirichletCharacter ℂ d) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdq χ) s =
      DirichletCharacter.LFunction χ s * ∏ p ∈ q.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) :=
  DirichletCharacter.LFunction_changeLevel hdq χ h

/-- Principal L-function equals Euler-stripped Riemann zeta for `s ≠ 1`. -/
theorem LFunction_one_eq_mul_riemannZeta {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
  DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs

private theorem sum_Ioc_period_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ioc M (M + q), χ n = 0 := by
  have hshift : ∑ n ∈ Finset.Ioc M (M + q), χ n = ∑ a ∈ Finset.range q, χ (M + 1 + a : ℕ) := by
    refine Finset.sum_bij (fun n _ ↦ n - (M + 1)) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_range]; omega
    · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ioc] at hn₁ hn₂; omega
    · intro a ha; simp only [Finset.mem_range] at ha
      refine ⟨M + 1 + a, by simp only [Finset.mem_Ioc]; omega, by omega⟩
    · intro n hn; simp only [Finset.mem_Ioc] at hn; congr 2; omega
  rw [hshift]
  have hz : ∑ a ∈ Finset.range q, χ (M + 1 + a : ℕ) =
      ∑ a : ZMod q, χ (((M + 1 : ℕ) : ZMod q) + a) := by
    symm
    have hbij : ∑ a : ZMod q, χ (((M + 1 : ℕ) : ZMod q) + a) =
        ∑ a ∈ Finset.range q, χ (((M + 1 : ℕ) : ZMod q) + (a : ZMod q)) := by
      refine Finset.sum_bij (fun a _ ↦ a.val) ?_ ?_ ?_ ?_
      · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
      · intro a₁ _ a₂ _ h; exact ZMod.val_injective q h
      · intro b hb
        exact ⟨(b : ZMod q), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)⟩
      · intro a _; simp
    rw [hbij]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    push_cast
    rfl
  rw [hz]
  exact (Equiv.sum_comp (Equiv.addLeft ((M + 1 : ℕ) : ZMod q)) χ).trans
    (χ.sum_eq_zero_of_ne_one hχ)

private def partialCharSum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, χ k

private lemma partialCharSum_add_period {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (n : ℕ) :
    partialCharSum χ (n + q) = partialCharSum χ n := by
  have hsplit : Finset.Icc 1 (n + q) = Finset.Icc 1 n ∪ Finset.Ioc n (n + q) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Ioc n (n + q)) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  rw [partialCharSum, hsplit, Finset.sum_union hdisj, sum_Ioc_period_eq_zero hχ n, add_zero]
  rfl

private lemma partialCharSum_mod_period {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (n : ℕ) :
    partialCharSum χ n = partialCharSum χ (n % q) := by
  have hdiv : ∀ k : ℕ, partialCharSum χ (n % q + q * k) = partialCharSum χ (n % q) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, ← add_assoc, partialCharSum_add_period hχ, ih]
  have hn : n = n % q + q * (n / q) := (Nat.mod_add_div n q).symm
  conv_lhs => rw [hn]
  exact hdiv (n / q)

private lemma norm_partialCharSum_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (n : ℕ) :
    ‖partialCharSum χ n‖ ≤ q := by
  rw [partialCharSum_mod_period hχ n, partialCharSum]
  have hle_q : n % q ≤ q := (Nat.mod_lt n (NeZero.pos q)).le
  calc
    ‖∑ k ∈ Finset.Icc 1 (n % q), χ k‖
        ≤ ∑ k ∈ Finset.Icc 1 (n % q), ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 (n % q), (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ χ.norm_le_one _
    _ = ((n % q : ℕ) : ℝ) := by simp [Nat.card_Icc]
    _ ≤ (q : ℝ) := Nat.cast_le.mpr hle_q

/-- A nonprincipal character has sum zero on each complete period. The remaining
incomplete period in a partial sum contributes at most its modulus. -/
theorem norm_sum_Icc_char_le_modulus {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (n : ℕ) : ‖∑ m ∈ Finset.Icc 1 n, χ m‖ ≤ q :=
  norm_partialCharSum_le hχ n

private lemma norm_partialCharSum_le_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖partialCharSum χ ⌊t⌋₊‖ ≤ t := by
  calc
    ‖partialCharSum χ ⌊t⌋₊‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ χ.norm_le_one _
    _ = (⌊t⌋₊ : ℝ) := by simp [Nat.card_Icc]
    _ ≤ t := Nat.floor_le ht

/-- **First-order Abel / Euler–Maclaurin continuation** of `DirichletCharacter.LFunction χ s` to
`Re s > 0` for non-principal characters `χ ≠ 1`. -/
theorem LFunction_eq_mul_integral_of_zero_lt_re {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ), (partialCharSum χ ⌊t⌋₊) * (t : ℂ) ^ (-s - 1) := by
  let S : ℝ → ℂ := fun t ↦ partialCharSum χ ⌊t⌋₊
  let F : ℂ → ℝ → ℂ := fun z t ↦ S t * (t : ℂ) ^ (-z - 1)
  have hS_meas : Measurable S :=
    (measurable_from_top (f := fun n : ℕ ↦ partialCharSum χ n)).comp Nat.measurable_floor
  have hS_bound : ∀ t : ℝ, ‖S t‖ ≤ (q : ℝ) := fun t ↦ norm_partialCharSum_le hχ ⌊t⌋₊
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    intro z
    have hpow : Measurable (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1)) :=
      Complex.continuous_ofReal.measurable.pow_const (-z - 1)
    exact (hS_meas.mul hpow).aestronglyMeasurable
  have hF_int : ∀ z : ℂ, 0 < z.re → IntegrableOn (F z) (Set.Ioi (1 : ℝ)) := by
    intro z hz
    have hint_bound : IntegrableOn (fun t : ℝ ↦ (q : ℝ) * t ^ (-z.re - 1)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -z.re - 1) (by linarith) zero_lt_one).const_mul (q : ℝ)
    refine hint_bound.mono' (hF_meas z) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-z - 1).re = -z.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hS_bound t) (Real.rpow_nonneg ht0.le _)
  let I : ℂ → ℂ := fun z ↦ z * ∫ t in Set.Ioi (1 : ℝ), F z t
  have hI_diff : DifferentiableOn ℂ I {z : ℂ | 0 < z.re} := by
    intro z₀ hz₀
    have hz₀' : 0 < z₀.re := hz₀
    let r := z₀.re / 2
    have hr : 0 < r := half_pos hz₀'
    have hball_mem : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
    let F' : ℂ → ℝ → ℂ := fun z t ↦ S t * (-(Complex.log (t : ℂ)) * (t : ℂ) ^ (-z - 1))
    have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hlog : Measurable (fun t : ℝ ↦ -Complex.log (t : ℂ)) :=
        (Complex.measurable_log.comp Complex.continuous_ofReal.measurable).neg
      have hpow : Measurable (fun t : ℝ ↦ (t : ℂ) ^ (-z₀ - 1)) :=
        Complex.continuous_ofReal.measurable.pow_const (-z₀ - 1)
      exact (hS_meas.mul (hlog.mul hpow)).aestronglyMeasurable
    let η := r / 2
    have hη : 0 < η := half_pos hr
    let bound : ℝ → ℝ := fun t ↦ (q : ℝ) / η * t ^ (-r + η - 1)
    have hbound_int : IntegrableOn bound (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -r + η - 1) (by dsimp only [η]; linarith)
        zero_lt_one).const_mul _
    have hF_meas_nhds : ∀ᶠ z in 𝓝 z₀,
        AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi (1 : ℝ))) :=
      Filter.Eventually.of_forall hF_meas
    have hbound_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ∀ z ∈ Metric.ball z₀ r, ‖F' z t‖ ≤ bound t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht1
      have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hzr : r ≤ z.re := by
        have hd : ‖z - z₀‖ < r := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz
        have hre_diff : |z.re - z₀.re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm (z - z₀)
        dsimp only [r] at *
        linarith [(abs_le.mp (hre_diff.trans hd.le)).1]
      dsimp only [F', bound]
      rw [norm_mul, norm_mul, norm_neg, ← Complex.ofReal_log ht0.le, Complex.norm_real,
        Real.norm_of_nonneg hlog_nn, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-z - 1).re = -z.re - 1 := by simp
      rw [hre]
      have hrpow_le : t ^ (-z.re - 1) ≤ t ^ (-r - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
      have hlog_le : Real.log t ≤ t ^ η / η := log_le_rpow_div t ht1.le hη
      calc
        ‖S t‖ * (Real.log t * t ^ (-z.re - 1))
            ≤ (q : ℝ) * ((t ^ η / η) * t ^ (-r - 1)) :=
              mul_le_mul (hS_bound t)
                (mul_le_mul hlog_le hrpow_le (by positivity) (by positivity))
                (by positivity) (by positivity)
        _ = (q : ℝ) / η * (t ^ η * t ^ (-r - 1)) := by ring
        _ = (q : ℝ) / η * t ^ (-r + η - 1) := by
              rw [← Real.rpow_add ht0]
              ring_nf
    have hdiff_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ∀ z ∈ Metric.ball z₀ r, HasDerivAt (F · t) (F' z t) z := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z _
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      have hinner_d : HasDerivAt (fun w : ℂ ↦ -w - 1) (-1) z :=
        ((hasDerivAt_id z).neg).sub_const 1
      have hcpow := HasDerivAt.const_cpow (c := (t : ℂ)) hinner_d (Or.inl htc)
      convert hcpow.const_mul (S t) using 1
      dsimp only [F']
      ring
    have hderiv_int := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi (1 : ℝ)))
      hball_mem hF_meas_nhds (hF_int z₀ hz₀') hF'_meas hbound_ae hbound_int hdiff_ae).2
    exact ((hasDerivAt_id z₀).mul hderiv_int).differentiableAt.differentiableWithinAt
  have heq_on_right : ∀ z : ℂ, 1 < z.re → DirichletCharacter.LFunction χ z = I z := by
    intro z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    have hsumm : LSeriesSummable (fun k ↦ χ k) z :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz
    have htend_series : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 1 N, χ k * (k : ℂ) ^ (-z))
        atTop (𝓝 (LSeries (fun k ↦ χ k) z)) := by
      have ht := hsumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      refine ht.congr fun N ↦ ?_
      rw [Function.comp_apply, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1), LSeries.term_zero, zero_add]
      have hico : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
        ext k; simp [Finset.mem_Ico, Finset.mem_Icc]
      rw [hico]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hknz : k ≠ 0 := by simp only [Finset.mem_Icc] at hk; omega
      rw [LSeries.term_of_ne_zero hknz, div_eq_mul_inv, Complex.cpow_neg]
    have hsum_abel : ∀ N : ℕ, 1 ≤ N →
        ∑ k ∈ Finset.Icc 1 N, χ k * (k : ℂ) ^ (-z) =
          partialCharSum χ N * (N : ℂ) ^ (-z) +
            z * ∫ t in (1 : ℝ)..(N : ℝ), S t * (t : ℂ) ^ (-z - 1) := by
      intro N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hab := abel_summation_Icc_one_hasDerivAt (fun k ↦ χ k)
        (f := fun t : ℝ ↦ (t : ℂ) ^ (-z))
        (f' := fun t : ℝ ↦ -z * (t : ℂ) ^ (-z - 1)) hN1
        (fun t ht ↦ ofReal_cpow_hasDerivAt (lt_of_lt_of_le zero_lt_one ht.1) (-z))
        (ContinuousOn.mul continuousOn_const
          (Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦
            Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [ht.1]))))
      have hfloor : (⌊(N : ℝ)⌋₊) = N := Nat.floor_natCast N
      rw [hfloor] at hab
      simp only [Complex.ofReal_natCast] at hab
      rw [hab, sub_eq_add_neg, ← intervalIntegral.integral_neg]
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      change -(partialCharSum χ ⌊t⌋₊ * (-z * (t : ℂ) ^ (-z - 1))) =
        z * (S t * (t : ℂ) ^ (-z - 1))
      dsimp only [S]
      ring
    have htend_rhs : Tendsto
        (fun N : ℕ ↦ partialCharSum χ N * (N : ℂ) ^ (-z) +
          z * ∫ t in (1 : ℝ)..(N : ℝ), S t * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (I z)) := by
      have hz_pos : 0 < z.re := by linarith
      have hbd_tend : Tendsto (fun N : ℕ ↦ partialCharSum χ N * (N : ℂ) ^ (-z))
          atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (g := fun N : ℕ ↦ (q : ℝ) * (N : ℝ) ^ (-z.re))
          (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) ?_
        · rw [norm_mul]
          by_cases hN0 : N = 0
          · subst hN0; simp [partialCharSum]; positivity
          · rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN0)]
            simp only [neg_re]
            exact mul_le_mul_of_nonneg_right (norm_partialCharSum_le hχ N) (by positivity)
        · have hr : Tendsto (fun N : ℕ ↦ (q : ℝ) * (N : ℝ) ^ (-z.re)) atTop (𝓝 ((q : ℝ) * 0)) :=
            tendsto_const_nhds.mul
              ((tendsto_rpow_neg_atTop hz_pos).comp tendsto_natCast_atTop_atTop)
          simpa using hr
      have hint_tend : Tendsto (fun N : ℕ ↦ z * ∫ t in (1 : ℝ)..(N : ℝ), S t * (t : ℂ) ^ (-z - 1))
          atTop (𝓝 (I z)) :=
        tendsto_const_nhds.mul
          (intervalIntegral_tendsto_integral_Ioi 1 (hF_int z hz_pos) tendsto_natCast_atTop_atTop)
      simpa using hbd_tend.add hint_tend
    have htend_abel : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 1 N, χ k * (k : ℂ) ^ (-z))
        atTop (𝓝 (I z)) := by
      refine htend_rhs.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hsum_abel N hN).symm
    exact tendsto_nhds_unique htend_series htend_abel
  have hopen : IsOpen {z : ℂ | 0 < z.re} := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage Complex.continuous_re
  have hconn : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 0 < z.re} :=
    (differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd hopen
  have hI_an : AnalyticOnNhd ℂ I {z : ℂ | 0 < z.re} := hI_diff.analyticOnNhd hopen
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] I := by
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      ((isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ))).preimage Complex.continuous_re).mem_nhds
        (by norm_num)
    exact Filter.eventually_of_mem hmem heq_on_right
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hI_an hconn (by norm_num) hev hs

private theorem LFunction_eq_second_order_integral {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∃ (cχ : ℂ) (V : ℝ → ℂ),
      ‖cχ‖ ≤ (q : ℝ) ∧
      (∀ t : ℝ, ‖V t‖ ≤ 4 * (q : ℝ) ^ 2) ∧
      ∀ {s : ℂ}, -1 < s.re →
        DirichletCharacter.LFunction χ s =
          cχ + s * (s + 1) * ∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-s - 2) := by
  let cχ : ℂ := (∑ j ∈ Finset.range q, partialCharSum χ j) / (q : ℂ)
  let T₀ : ℕ → ℂ := fun n ↦ partialCharSum χ n - cχ
  let V : ℝ → ℂ := fun t ↦
    (∑ j ∈ Finset.Ico 1 ⌊t⌋₊, T₀ j) + ((Int.fract t : ℝ) : ℂ) * T₀ ⌊t⌋₊
  have hcχ_norm : ‖cχ‖ ≤ (q : ℝ) := by
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    dsimp only [cχ]
    rw [norm_div, Complex.norm_natCast]
    refine div_le_of_le_mul₀ hq_pos.le (by positivity) ?_
    calc
      ‖∑ j ∈ Finset.range q, partialCharSum χ j‖
          ≤ ∑ j ∈ Finset.range q, ‖partialCharSum χ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range q, (q : ℝ) := Finset.sum_le_sum fun j _ ↦ norm_partialCharSum_le hχ j
      _ = (q : ℝ) * (q : ℝ) := by simp
  have hT₀_norm : ∀ n : ℕ, ‖T₀ n‖ ≤ 2 * (q : ℝ) := by
    intro n
    calc
      ‖partialCharSum χ n - cχ‖ ≤ ‖partialCharSum χ n‖ + ‖cχ‖ := norm_sub_le _ _
      _ ≤ (q : ℝ) + (q : ℝ) := add_le_add (norm_partialCharSum_le hχ n) hcχ_norm
      _ = 2 * (q : ℝ) := by ring
  have hT₀_mod : ∀ n : ℕ, T₀ n = T₀ (n % q) := fun n ↦ by
    simp only [T₀, partialCharSum_mod_period hχ n]
  have hT₀_period_sum : ∀ a : ℕ, ∑ j ∈ Finset.Ico a (a + q), T₀ j = 0 := by
    intro a
    have hshift : ∑ j ∈ Finset.Ico a (a + q), T₀ j = ∑ r ∈ Finset.range q, T₀ (a + r) := by
      refine Finset.sum_bij (fun j _ ↦ j - a) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj; simp only [Finset.mem_range]; omega
      · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
      · intro r hr; simp only [Finset.mem_range] at hr
        exact ⟨a + r, by simp only [Finset.mem_Ico]; omega, by omega⟩
      · intro j hj; simp only [Finset.mem_Ico] at hj; congr 1; omega
    have hbij : ∑ r ∈ Finset.range q, T₀ (a + r) = ∑ r ∈ Finset.range q, T₀ r := by
      have hmod_z : ∑ r ∈ Finset.range q, T₀ (a + r) =
          ∑ r : ZMod q, T₀ ((a : ZMod q) + r).val := by
        symm
        refine Finset.sum_bij (fun r _ ↦ r.val) ?_ ?_ ?_ ?_
        · intro r _; exact Finset.mem_range.mpr (ZMod.val_lt r)
        · intro r₁ _ r₂ _ h; exact ZMod.val_injective q h
        · intro r hr
          exact ⟨(r : ZMod q), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)⟩
        · intro r _
          rw [hT₀_mod (a + r.val)]
          congr 1
          have hz : ((a : ZMod q) + r).val = (a + r.val) % q := by
            rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_add_mod]
          exact hz
      have hcomp := Equiv.sum_comp (Equiv.addLeft (a : ZMod q)) (fun x : ZMod q ↦ T₀ x.val)
      simp only [Equiv.coe_addLeft] at hcomp
      rw [hmod_z, hcomp]
      refine Finset.sum_bij (fun r _ ↦ r.val) ?_ ?_ ?_ ?_
      · intro r _; exact Finset.mem_range.mpr (ZMod.val_lt r)
      · intro r₁ _ r₂ _ h; exact ZMod.val_injective q h
      · intro r hr
        exact ⟨(r : ZMod q), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)⟩
      · intro _ _; rfl
    rw [hshift, hbij]
    simp only [T₀, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.pos q).ne'
    simp only [cχ]
    field_simp [hqC]
    ring
  have hsum_T₀_bound : ∀ m : ℕ, ‖∑ j ∈ Finset.Ico 1 m, T₀ j‖ ≤ 2 * (q : ℝ) ^ 2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hm : m ≤ q + 1
      · calc
          ‖∑ j ∈ Finset.Ico 1 m, T₀ j‖ ≤ ∑ j ∈ Finset.Ico 1 m, ‖T₀ j‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.Ico 1 m, (2 * (q : ℝ)) := Finset.sum_le_sum fun j _ ↦ hT₀_norm j
          _ = ((m - 1 : ℕ) : ℝ) * (2 * (q : ℝ)) := by simp [Nat.card_Ico]
          _ ≤ (q : ℝ) * (2 * (q : ℝ)) :=
              mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) (by positivity)
          _ = 2 * (q : ℝ) ^ 2 := by ring
      · have hm_gt : q + 1 < m := not_le.mp hm
        have hsplit : Finset.Ico 1 m = Finset.Ico 1 (m - q) ∪ Finset.Ico (m - q) m := by
          ext j; simp only [Finset.mem_Ico, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Ico 1 (m - q)) (Finset.Ico (m - q) m) := by
          rw [Finset.disjoint_left]; intro j h1 h2
          simp only [Finset.mem_Ico] at h1 h2; omega
        have hq_pos : 0 < q := NeZero.pos q
        have hper : ∑ j ∈ Finset.Ico (m - q) m, T₀ j = 0 := by
          simpa [show m - q + q = m by omega] using hT₀_period_sum (m - q)
        rw [hsplit, Finset.sum_union hdisj, hper, add_zero]
        exact ih (m - q) (by omega)
  have hV_bound : ∀ t : ℝ, ‖V t‖ ≤ 4 * (q : ℝ) ^ 2 := by
    intro t
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hfr_le : |Int.fract t| ≤ 1 := by
      rw [abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    calc
      ‖V t‖ ≤ ‖∑ j ∈ Finset.Ico 1 ⌊t⌋₊, T₀ j‖ + ‖((Int.fract t : ℝ) : ℂ) * T₀ ⌊t⌋₊‖ :=
          norm_add_le _ _
      _ ≤ 2 * (q : ℝ) ^ 2 + |Int.fract t| * ‖T₀ ⌊t⌋₊‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (hsum_T₀_bound _) le_rfl
      _ ≤ 2 * (q : ℝ) ^ 2 + 1 * (2 * (q : ℝ)) :=
          add_le_add le_rfl (mul_le_mul hfr_le (hT₀_norm _) (norm_nonneg _) zero_le_one)
      _ ≤ 4 * (q : ℝ) ^ 2 := by nlinarith [hq1]
  have hV_meas : Measurable V :=
    ((measurable_from_top (f := fun m : ℕ ↦ ∑ j ∈ Finset.Ico 1 m, T₀ j)).comp
      Nat.measurable_floor).add
      ((Complex.continuous_ofReal.measurable.comp measurable_fract).mul
        ((measurable_from_top (f := T₀)).comp Nat.measurable_floor))
  let J : ℂ → ℂ := fun z ↦
    cχ + z * (z + 1) * ∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-z - 2)
  have hJ_diff : DifferentiableOn ℂ J {z : ℂ | -1 < z.re} := by
    have hint_diff := integral_Ioi_bounded_log_cpow_differentiableOn
      (by positivity : (0 : ℝ) ≤ 4 * (q : ℝ) ^ 2) hV_bound hV_meas
    intro z hz
    have h1 : DifferentiableWithinAt ℂ (fun w : ℂ ↦ w * (w + 1)) {w : ℂ | -1 < w.re} z :=
      ((differentiableAt_id (𝕜 := ℂ)).mul
        ((differentiableAt_id (𝕜 := ℂ)).add_const (1 : ℂ))).differentiableWithinAt
    have h2 := hint_diff z hz
    exact (differentiableWithinAt_const cχ).add (h1.mul h2)
  have heq_on_right : ∀ z : ℂ, 1 < z.re → DirichletCharacter.LFunction χ z = J z := by
    intro z hz
    have hz_pos : 0 < z.re := by linarith
    rw [LFunction_eq_mul_integral_of_zero_lt_re hχ hz_pos]
    have hF₁_int : IntegrableOn (fun t : ℝ ↦ partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1))
        (Set.Ioi (1 : ℝ)) := by
      refine (integrableOn_Ioi_rpow_of_lt (a := -z.re - 1) (by linarith) zero_lt_one).const_mul (q : ℝ)
        |>.mono' ?_ ?_
      · exact (((measurable_from_top (f := fun n : ℕ ↦ partialCharSum χ n)).comp
          Nat.measurable_floor).mul (Complex.continuous_ofReal.measurable.pow_const (-z - 1))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [sub_re, neg_re, one_re]
        exact mul_le_mul_of_nonneg_right (norm_partialCharSum_le hχ _) (Real.rpow_nonneg ht0.le _)
    have hF₂_int : IntegrableOn (fun t : ℝ ↦ V t * (t : ℂ) ^ (-z - 2)) (Set.Ioi (1 : ℝ)) := by
      refine (integrableOn_Ioi_rpow_of_lt (a := -z.re - 2) (by linarith) zero_lt_one).const_mul
        (4 * (q : ℝ) ^ 2) |>.mono' ?_ ?_
      · exact (hV_meas.mul (Complex.continuous_ofReal.measurable.pow_const (-z - 2))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [sub_re, neg_re, re_ofNat]
        exact mul_le_mul_of_nonneg_right (hV_bound t) (Real.rpow_nonneg ht0.le _)
    have hT₀_int_Ioi : IntegrableOn (fun t : ℝ ↦ T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1))
        (Set.Ioi (1 : ℝ)) := by
      refine (integrableOn_Ioi_rpow_of_lt (a := -z.re - 1) (by linarith) zero_lt_one).const_mul
        (2 * (q : ℝ)) |>.mono' ?_ ?_
      · exact (((measurable_from_top (f := T₀)).comp Nat.measurable_floor).mul
          (Complex.continuous_ofReal.measurable.pow_const (-z - 1))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [sub_re, neg_re, one_re]
        exact mul_le_mul_of_nonneg_right (hT₀_norm _) (Real.rpow_nonneg ht0.le _)
    have hseg : ∀ n : ℕ, 1 ≤ n →
        ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) =
          V ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℂ) ^ (-z - 1) -
            V (n : ℝ) * (n : ℂ) ^ (-z - 1) +
            (z + 1) * ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), V t * (t : ℂ) ^ (-z - 2) := by
      intro n hn
      let u : ℝ → ℂ := fun t ↦ (∑ j ∈ Finset.Ico 1 n, T₀ j) + ((t - (n : ℝ) : ℝ) : ℂ) * T₀ n
      let v : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-z - 1)
      have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hmin : min (n : ℝ) ((n + 1 : ℕ) : ℝ) = n := min_eq_left hle
      have hu_cont : ContinuousOn u (Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ)) :=
        (continuous_const.add ((Complex.continuous_ofReal.comp
          (continuous_id.sub continuous_const)).mul continuous_const)).continuousOn
      have hv_cont : ContinuousOn v (Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
        rw [Set.uIcc_of_le hle]
        refine Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦ ?_
        exact Complex.mem_slitPlane_iff.mpr
          (Or.inl (by simp; linarith [ht.1, show (0 : ℝ) < n by positivity]))
      have hu_deriv : ∀ t ∈ Set.Ioo (min (n : ℝ) ((n + 1 : ℕ) : ℝ)) (max (n : ℝ) ((n + 1 : ℕ) : ℝ)),
          HasDerivAt u (T₀ n) t := by
        intro t _
        have h1 : HasDerivAt (fun x : ℝ ↦ ((x - (n : ℝ) : ℝ) : ℂ)) 1 t := by
          simpa using ((hasDerivAt_id t).sub_const (n : ℝ)).ofReal_comp
        convert (hasDerivAt_const t (∑ j ∈ Finset.Ico 1 n, T₀ j)).add (h1.mul_const (T₀ n))
          using 1
        simp
      have hv_deriv : ∀ t ∈ Set.Ioo (min (n : ℝ) ((n + 1 : ℕ) : ℝ)) (max (n : ℝ) ((n + 1 : ℕ) : ℝ)),
          HasDerivAt v ((-z - 1) * (t : ℂ) ^ (-z - 2)) t := by
        intro t ht
        rw [hmin] at ht
        have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg n) ht.1
        convert ofReal_cpow_hasDerivAt ht0 (-z - 1) using 1
        ring_nf
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        hu_cont hv_cont hu_deriv hv_deriv
        intervalIntegrable_const
        ((ContinuousOn.mul continuousOn_const
          (Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦ by
            rw [Set.uIcc_of_le hle] at ht
            exact Complex.mem_slitPlane_iff.mpr
              (Or.inl (by simp; linarith [ht.1, show (0 : ℝ) < n by positivity])))).intervalIntegrable)
      have huv_lhs :
          ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) =
            ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), T₀ n * v t := by
        refine intervalIntegral.integral_congr_ae ?_
        have hne : ∀ᵐ t ∂volume, t ≠ ((n + 1 : ℕ) : ℝ) := ae_ne_real _
        filter_upwards [hne] with t htne htmem
        rw [Set.uIoc_of_le hle] at htmem
        have ht_ico : t ∈ Set.Ico (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
          ⟨htmem.1.le, lt_of_le_of_ne htmem.2 htne⟩
        have hfl : ⌊t⌋₊ = n := Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) ht_ico.1) |>.mpr
          ⟨ht_ico.1, by exact_mod_cast ht_ico.2⟩
        rw [hfl]
      have huv_rhs :
          ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), u t * ((-z - 1) * (t : ℂ) ^ (-z - 2)) =
            (-z - 1) * ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), V t * (t : ℂ) ^ (-z - 2) := by
        have hcon :
            ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), u t * ((-z - 1) * (t : ℂ) ^ (-z - 2)) =
              ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), (-z - 1) * (V t * (t : ℂ) ^ (-z - 2)) := by
          refine intervalIntegral.integral_congr_ae ?_
          have hne : ∀ᵐ t ∂volume, t ≠ ((n + 1 : ℕ) : ℝ) := ae_ne_real _
          filter_upwards [hne] with t htne htmem
          rw [Set.uIoc_of_le hle] at htmem
          have ht_ico : t ∈ Set.Ico (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
            ⟨htmem.1.le, lt_of_le_of_ne htmem.2 htne⟩
          have hflN : ⌊t⌋₊ = n := Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) ht_ico.1) |>.mpr
            ⟨ht_ico.1, by exact_mod_cast ht_ico.2⟩
          have hflZ : ⌊t⌋ = (n : ℤ) := Int.floor_eq_iff.mpr
            ⟨by exact_mod_cast ht_ico.1, by exact_mod_cast ht_ico.2⟩
          have hVt : V t = u t := by
            dsimp only [V, u]
            rw [hflN, Int.fract, hflZ]
            rfl
          rw [hVt]
          ring
        rw [hcon, intervalIntegral.integral_const_mul]
      have hVn : V (n : ℝ) = u (n : ℝ) := by
        simp [V, u]
      have hVn1 : V ((n + 1 : ℕ) : ℝ) = u ((n + 1 : ℕ) : ℝ) := by
        dsimp only [V, u]
        rw [Nat.floor_natCast, Int.fract_natCast]
        simp only [Complex.ofReal_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_left, Complex.ofReal_one, one_mul]
        rw [← Finset.sum_Ico_succ_top hn]
      rw [huv_lhs]
      have hibp' : ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), T₀ n * v t =
          u ((n + 1 : ℕ) : ℝ) * v ((n + 1 : ℕ) : ℝ) - u (n : ℝ) * v (n : ℝ) -
            ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), u t * ((-z - 1) * (t : ℂ) ^ (-z - 2)) := by
        conv_lhs =>
          rw [← sub_sub_cancel
            (u ((n + 1 : ℕ) : ℝ) * v ((n + 1 : ℕ) : ℝ) - u (n : ℝ) * v (n : ℝ))
            (∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), T₀ n * v t)]
        rw [← hibp]
      rw [hibp', huv_rhs, ← hVn, ← hVn1]
      dsimp only [v]
      simp only [Complex.ofReal_natCast]
      ring
    have hfinite_eq : ∀ N : ℕ, 1 ≤ N →
        z * ∫ t in (1 : ℝ)..(N : ℝ), partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) =
          cχ * (1 - (N : ℂ) ^ (-z)) +
            z * (V (N : ℝ) * (N : ℂ) ^ (-z - 1)) +
            z * (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), V t * (t : ℂ) ^ (-z - 2) := by
      intro N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hint_pow : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1)) volume 1 N := by
        refine (Complex.continuous_ofReal.continuousOn.cpow_const fun x hx ↦ ?_).intervalIntegrable
        rw [Set.uIcc_of_le hN1] at hx
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [hx.1]))
      have hint_T₀ : IntervalIntegrable (fun t : ℝ ↦ T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1)) volume 1 N :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hN1).mpr
          (hT₀_int_Ioi.mono_set Set.Ioc_subset_Ioi_self)
      have hsplit_S :
          ∫ t in (1 : ℝ)..(N : ℝ), partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) =
            cχ * (∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1)) +
              ∫ t in (1 : ℝ)..(N : ℝ), T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) := by
        have hsub_eq : ∀ t : ℝ, partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) =
            cχ * (t : ℂ) ^ (-z - 1) + T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) := fun t ↦ by
          dsimp only [T₀]; ring
        rw [intervalIntegral.integral_congr (fun t _ ↦ hsub_eq t),
          intervalIntegral.integral_add (hint_pow.const_mul cχ) hint_T₀,
          intervalIntegral.integral_const_mul]
      have hint_pow_val : z * (cχ * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1)) =
          cχ * (1 - (N : ℂ) ^ (-z)) := by
        have hftc : ∫ t in (1 : ℝ)..(N : ℝ), (-z) * (t : ℂ) ^ (-z - 1) =
            (N : ℂ) ^ (-z) - (1 : ℂ) ^ (-z) := by
          convert intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun t : ℝ ↦ (t : ℂ) ^ (-z))
            (fun t ht ↦ by
              rw [Set.uIcc_of_le hN1] at ht
              exact ofReal_cpow_hasDerivAt (lt_of_lt_of_le zero_lt_one ht.1) (-z))
            (hint_pow.const_mul (-z)) using 1
        rw [intervalIntegral.integral_const_mul, Complex.one_cpow] at hftc
        have hi : z * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1) = 1 - (N : ℂ) ^ (-z) := by
          linear_combination -hftc
        calc
          z * (cχ * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1))
              = cχ * (z * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1)) := by ring
          _ = cχ * (1 - (N : ℂ) ^ (-z)) := by rw [hi]
      have hsum_T₀_int :
          ∫ t in (1 : ℝ)..(N : ℝ), T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) =
            V (N : ℝ) * (N : ℂ) ^ (-z - 1) +
              (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), V t * (t : ℂ) ^ (-z - 2) := by
        have hL1 := sum_intervalIntegrable_adjacent
          (fun t : ℝ ↦ T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1)) N hN fun n hn ↦ by
            simp only [Finset.mem_Ico] at hn
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
            have hn_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
            exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn_le).mpr
              (hT₀_int_Ioi.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hn1)))
        have hR1 := sum_intervalIntegrable_adjacent
          (fun t : ℝ ↦ V t * (t : ℂ) ^ (-z - 2)) N hN fun n hn ↦ by
            simp only [Finset.mem_Ico] at hn
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
            have hn_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
            exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn_le).mpr
              (hF₂_int.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hn1)))
        have hV1 : V (1 : ℝ) = 0 := by
          dsimp only [V]
          rw [Nat.floor_one, Finset.Ico_self, Finset.sum_empty, zero_add, Int.fract_one]
          simp
        rw [← hL1, ← hR1]
        have hseg_sum :
            ∑ n ∈ Finset.Ico 1 N, ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), T₀ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1) =
              (∑ n ∈ Finset.Ico 1 N,
                (V ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℂ) ^ (-z - 1) -
                  V (n : ℝ) * (n : ℂ) ^ (-z - 1))) +
              (z + 1) * ∑ n ∈ Finset.Ico 1 N,
                ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), V t * (t : ℂ) ^ (-z - 2) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n hn ↦ ?_
          simp only [Finset.mem_Ico] at hn
          exact hseg n hn.1
        rw [hseg_sum, sum_Ico_succ_sub_eq (fun n ↦ V (n : ℝ) * (n : ℂ) ^ (-z - 1)) hN]
        simp only [Nat.cast_one, hV1, zero_mul, sub_zero]
      rw [hsplit_S]
      rw [mul_add z]
      rw [hint_pow_val, hsum_T₀_int]
      ring
    have htend_lhs : Tendsto
        (fun N : ℕ ↦ z * ∫ t in (1 : ℝ)..(N : ℝ), partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (z * ∫ t in Set.Ioi (1 : ℝ), partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1))) :=
      tendsto_const_nhds.mul
        (intervalIntegral_tendsto_integral_Ioi 1 hF₁_int tendsto_natCast_atTop_atTop)
    have htend_rhs : Tendsto
        (fun N : ℕ ↦ cχ * (1 - (N : ℂ) ^ (-z)) +
          z * (V (N : ℝ) * (N : ℂ) ^ (-z - 1)) +
          z * (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), V t * (t : ℂ) ^ (-z - 2))
        atTop (𝓝 (J z)) := by
      have htend_N1 : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-z)) atTop (𝓝 0) := by
        have hnz : -z ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this; linarith
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (g := fun N : ℕ ↦ (N : ℝ) ^ (-z.re))
          (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) ?_
        · by_cases hN0 : N = 0
          · subst hN0; simp [Complex.zero_cpow hnz]; positivity
          · rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN0)]; simp
        · exact (tendsto_rpow_neg_atTop hz_pos).comp tendsto_natCast_atTop_atTop
      have htend_cχ : Tendsto (fun N : ℕ ↦ cχ * (1 - (N : ℂ) ^ (-z))) atTop (𝓝 cχ) := by
        simpa using (tendsto_const_nhds (x := cχ)).mul
          ((tendsto_const_nhds (x := (1 : ℂ))).sub htend_N1)
      have htend_Vbd : Tendsto (fun N : ℕ ↦ z * (V (N : ℝ) * (N : ℂ) ^ (-z - 1))) atTop (𝓝 0) := by
        have hnz1 : -z - 1 ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this; linarith
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (g := fun N : ℕ ↦ ‖z‖ * (4 * (q : ℝ) ^ 2 * (N : ℝ) ^ (-(z.re + 1))))
          (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) ?_
        · rw [norm_mul, norm_mul]
          by_cases hN0 : N = 0
          · subst hN0
            simp [Complex.zero_cpow hnz1]
            positivity
          · rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN0)]
            have hre_eq : (-z - 1).re = -(z.re + 1) := by simp; ring
            rw [hre_eq]
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hV_bound _) (by positivity)) (norm_nonneg _)
        · have hre_pos : 0 < z.re + 1 := by linarith
          have hr : Tendsto (fun N : ℕ ↦ ‖z‖ * (4 * (q : ℝ) ^ 2 * (N : ℝ) ^ (-(z.re + 1))))
              atTop (𝓝 (‖z‖ * (4 * (q : ℝ) ^ 2 * 0))) :=
            tendsto_const_nhds.mul (tendsto_const_nhds.mul
              ((tendsto_rpow_neg_atTop hre_pos).comp tendsto_natCast_atTop_atTop))
          simpa using hr
      have htend_Vint : Tendsto
          (fun N : ℕ ↦ z * (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), V t * (t : ℂ) ^ (-z - 2))
          atTop (𝓝 (z * (z + 1) * ∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-z - 2))) :=
        tendsto_const_nhds.mul
          (intervalIntegral_tendsto_integral_Ioi 1 hF₂_int tendsto_natCast_atTop_atTop)
      have hcomb := (htend_cχ.add htend_Vbd).add htend_Vint
      have hlim : cχ + 0 + z * (z + 1) * ∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-z - 2) = J z := by
        dsimp only [J]; ring
      exact hlim ▸ hcomb
    have htend_rhs' : Tendsto
        (fun N : ℕ ↦ z * ∫ t in (1 : ℝ)..(N : ℝ), partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-z - 1))
        atTop (𝓝 (J z)) := by
      refine htend_rhs.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hfinite_eq N hN).symm
    exact tendsto_nhds_unique htend_lhs htend_rhs'
  have hopen : IsOpen {z : ℂ | -1 < z.re} :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).preimage Complex.continuous_re
  have hconn : IsPreconnected {z : ℂ | -1 < z.re} := (convex_halfSpace_re_gt (-1)).isPreconnected
  have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | -1 < z.re} :=
    (differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd hopen
  have hJ_an : AnalyticOnNhd ℂ J {z : ℂ | -1 < z.re} := hJ_diff.analyticOnNhd hopen
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] J := by
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      ((isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ))).preimage Complex.continuous_re).mem_nhds
        (by norm_num)
    exact Filter.eventually_of_mem hmem heq_on_right
  refine ⟨cχ, V, hcχ_norm, hV_bound, fun {s} hs ↦ ?_⟩
  exact hL_an.eqOn_of_preconnected_of_eventuallyEq hJ_an hconn (by norm_num) hev hs

/-- Polynomial vertical growth of `DirichletCharacter.LFunction χ` on `Re s ≥ -1/2` for
`χ ≠ 1`. -/
theorem norm_LFunction_strip_poly_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs_lo : -(1 / 2 : ℝ) ≤ s.re) (hs_hi : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q + 48 * (q : ℝ) ^ 2) * (|s.im| + 2) ^ 2 := by
  obtain ⟨cχ, V, hcχ, hV, heq⟩ := LFunction_eq_second_order_integral hχ
  have hs_gt : -1 < s.re := by linarith
  rw [heq hs_gt]
  have hint_le : ‖∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-s - 2)‖ ≤ 8 * (q : ℝ) ^ 2 := by
    have hint_real : IntegrableOn (fun t : ℝ ↦ (4 * (q : ℝ) ^ 2) * t ^ (-s.re - 2))
        (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) zero_lt_one).const_mul _
    calc
      ‖∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-s - 2)‖
          ≤ ∫ t in Set.Ioi (1 : ℝ), ‖V t * (t : ℂ) ^ (-s - 2)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), (4 * (q : ℝ) ^ 2) * t ^ (-s.re - 2) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
            hint_real ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := lt_trans zero_lt_one ht
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp only [sub_re, neg_re, re_ofNat]
          exact mul_le_mul_of_nonneg_right (hV t) (Real.rpow_nonneg ht0.le _)
      _ = (4 * (q : ℝ) ^ 2) * ∫ t in Set.Ioi (1 : ℝ), t ^ (-s.re - 2) := integral_const_mul _ _
      _ = (4 * (q : ℝ) ^ 2) * (-(1 : ℝ) ^ (-s.re - 2 + 1) / (-s.re - 2 + 1)) := by
          rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      _ = (4 * (q : ℝ) ^ 2) / (s.re + 1) := by
          rw [Real.one_rpow, show -s.re - 2 + 1 = -(s.re + 1) by ring]
          have hne : s.re + 1 ≠ 0 := by linarith
          field_simp [hne]
      _ ≤ (4 * (q : ℝ) ^ 2) / (1 / 2) := div_le_div_of_nonneg_left (by positivity) (by norm_num)
          (by linarith)
      _ = 8 * (q : ℝ) ^ 2 := by ring
  have hs_norm : ‖s‖ ≤ 2 * (|s.im| + 2) := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ ≤ 2 + |s.im| := add_le_add (abs_le.mpr ⟨by linarith, hs_hi⟩) le_rfl
      _ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
  have hs1_norm : ‖s + 1‖ ≤ 3 * (|s.im| + 2) := by
    calc
      ‖s + 1‖ ≤ |s.re + 1| + |s.im| := by simpa using norm_le_abs_re_add_abs_im (s + 1)
      _ ≤ 3 + |s.im| := add_le_add (abs_le.mpr ⟨by linarith, by linarith⟩) le_rfl
      _ ≤ 3 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
  have h1_le_sq : 1 ≤ (|s.im| + 2) ^ 2 := by nlinarith [abs_nonneg s.im]
  calc
    ‖cχ + s * (s + 1) * ∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-s - 2)‖
        ≤ ‖cχ‖ + ‖s * (s + 1) * ∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-s - 2)‖ :=
          norm_add_le _ _
    _ = ‖cχ‖ + ‖s‖ * ‖s + 1‖ * ‖∫ t in Set.Ioi (1 : ℝ), V t * (t : ℂ) ^ (-s - 2)‖ := by
          simp only [norm_mul, mul_assoc]
    _ ≤ q + (2 * (|s.im| + 2)) * (3 * (|s.im| + 2)) * (8 * (q : ℝ) ^ 2) := by
          refine add_le_add hcχ ?_
          exact mul_le_mul (mul_le_mul hs_norm hs1_norm (norm_nonneg _) (by positivity))
            hint_le (norm_nonneg _) (by positivity)
    _ = q + 48 * (q : ℝ) ^ 2 * (|s.im| + 2) ^ 2 := by ring
    _ ≤ q * (|s.im| + 2) ^ 2 + 48 * (q : ℝ) ^ 2 * (|s.im| + 2) ^ 2 := by
          nlinarith [h1_le_sq, show (0 : ℝ) ≤ q by positivity]
    _ = (q + 48 * (q : ℝ) ^ 2) * (|s.im| + 2) ^ 2 := by ring

private theorem riemannZeta₁_eq_second_order_integral {s : ℂ} (hs : -1 < s.re) :
    riemannZeta₁ s =
      s - (s - 1) / 2 -
        (s - 1) * s * (s + 1) *
          ∫ t in Set.Ioi (1 : ℝ), ((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2) := by
  let B : ℝ → ℂ := fun t ↦ ((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ)
  have hB_bound : ∀ t : ℝ, ‖B t‖ ≤ 1 / 6 := by
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hb := bernoulliKernel_two_abs_le t
    calc
      |bernoulliKernel 2 t - 1 / 12| ≤ |bernoulliKernel 2 t| + |-(1 / 12 : ℝ)| := by
          simpa [sub_eq_add_neg] using abs_add_le (bernoulliKernel 2 t) (-(1 / 12 : ℝ))
      _ ≤ 1 / 12 + 1 / 12 := by norm_num at *; linarith
      _ = 1 / 6 := by norm_num
  have hB_meas : Measurable B :=
    Complex.continuous_ofReal.measurable.comp
      ((continuous_bernoulliKernel (by norm_num : (2 : ℕ) ≠ 1)).measurable.sub_const _)
  let J : ℂ → ℂ := fun z ↦
    z - (z - 1) / 2 -
      (z - 1) * z * (z + 1) * ∫ t in Set.Ioi (1 : ℝ), B t * (t : ℂ) ^ (-z - 2)
  have hJ_diff : DifferentiableOn ℂ J {z : ℂ | -1 < z.re} := by
    have hint_diff := integral_Ioi_bounded_log_cpow_differentiableOn
      (by norm_num : (0 : ℝ) ≤ 1 / 6) hB_bound hB_meas
    intro z hz
    have hpoly₁ : DifferentiableAt ℂ (fun w : ℂ ↦ w - (w - 1) / 2) z := by fun_prop
    have hpoly₂ : DifferentiableAt ℂ (fun w : ℂ ↦ (w - 1) * w * (w + 1)) z := by fun_prop
    exact (hpoly₁.differentiableWithinAt).sub
      ((hpoly₂.differentiableWithinAt).mul (hint_diff z hz))
  have heq_on_right : ∀ z : ℂ, 1 < z.re → riemannZeta₁ z = J z := by
    intro z hz
    have hz_ne1 : z ≠ 1 := by
      intro h; rw [h] at hz; simp at hz
    have hz_pos : 0 < z.re := by linarith
    have hzeta1 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz_ne1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz_ne1),
        one_mul]
    rw [hzeta1]
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hz; linarith
    have hsumm : Summable (fun n : ℕ ↦ 1 / (n : ℂ) ^ z) := by
      have h := Real.summable_nat_rpow_inv.mpr hz
      refine Summable.of_norm_bounded h fun n ↦ ?_
      by_cases hn0 : n = 0
      · subst hn0
        simp [Complex.zero_cpow hz0, Real.zero_rpow hz_pos.ne']
      · rw [norm_div, norm_one, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0), one_div,
          ← Real.rpow_neg (Nat.cast_nonneg n)]
    have htend_series : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-z))
        atTop (𝓝 (riemannZeta z)) := by
      rw [zeta_eq_tsum_one_div_nat_cpow hz]
      have ht := hsumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      refine ht.congr fun N ↦ ?_
      rw [Function.comp_apply, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1)]
      have h0 : 1 / ((0 : ℕ) : ℂ) ^ z = 0 := by
        simp [Complex.zero_cpow hz0]
      rw [h0, zero_add]
      have hico : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
        ext k; simp [Finset.mem_Ico, Finset.mem_Icc]
      rw [hico]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [one_div, Complex.cpow_neg]
    have hB_int_Ioi : IntegrableOn (fun t : ℝ ↦ B t * (t : ℂ) ^ (-z - 2)) (Set.Ioi (1 : ℝ)) := by
      refine (integrableOn_Ioi_rpow_of_lt (a := -z.re - 2) (by linarith) zero_lt_one).const_mul
        (1 / 6 : ℝ) |>.mono' ?_ ?_
      · exact (hB_meas.mul (Complex.continuous_ofReal.measurable.pow_const (-z - 2))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [sub_re, neg_re, re_ofNat]
        exact mul_le_mul_of_nonneg_right (hB_bound t) (Real.rpow_nonneg ht0.le _)
    have hsaw_int_Ioi : IntegrableOn (fun t : ℝ ↦ (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))
        (Set.Ioi (1 : ℝ)) := by
      have hsaw_meas : Measurable (fun t : ℝ ↦ (sawtooth t : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp (measurable_fract.sub_const _)
      refine (integrableOn_Ioi_rpow_of_lt (a := -z.re - 1) (by linarith) zero_lt_one).const_mul
        (1 : ℝ) |>.mono' ?_ ?_
      · exact (hsaw_meas.mul (Complex.continuous_ofReal.measurable.pow_const (-z - 1))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hsaw_le : |sawtooth t| ≤ 1 := by
          rw [sawtooth, abs_le]
          constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]
        simp only [sub_re, neg_re, one_re]
        exact mul_le_mul_of_nonneg_right hsaw_le (Real.rpow_nonneg ht0.le _)
    have hseg : ∀ n : ℕ, 1 ≤ n →
        ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) =
          (z + 1) * ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), B t * (t : ℂ) ^ (-z - 2) := by
      intro n hn
      let u : ℝ → ℂ := fun t ↦ ((((t - (n : ℝ)) ^ 2 - (t - (n : ℝ))) / 2 : ℝ) : ℂ)
      let v : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-z - 1)
      have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hmin : min (n : ℝ) ((n + 1 : ℕ) : ℝ) = n := min_eq_left hle
      have hu_cont : ContinuousOn u (Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
        refine (Complex.continuous_ofReal.comp ?_).continuousOn
        fun_prop
      have hv_cont : ContinuousOn v (Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
        rw [Set.uIcc_of_le hle]
        refine Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦ ?_
        exact Complex.mem_slitPlane_iff.mpr
          (Or.inl (by simp; linarith [ht.1, show (0 : ℝ) < n by positivity]))
      have hu_deriv : ∀ t ∈ Set.Ioo (min (n : ℝ) ((n + 1 : ℕ) : ℝ)) (max (n : ℝ) ((n + 1 : ℕ) : ℝ)),
          HasDerivAt u (((t - (n : ℝ) - 1 / 2 : ℝ) : ℂ)) t := by
        intro t _
        have hlin : HasDerivAt (fun x : ℝ ↦ x - (n : ℝ)) 1 t := (hasDerivAt_id t).sub_const _
        have hsq : HasDerivAt (fun x : ℝ ↦ (x - (n : ℝ)) ^ 2) (2 * (t - (n : ℝ)) ^ (2 - 1) * 1) t :=
          hlin.pow 2
        have hreal : HasDerivAt (fun x : ℝ ↦ ((x - (n : ℝ)) ^ 2 - (x - (n : ℝ))) / 2)
            (t - (n : ℝ) - 1 / 2) t := by
          convert ((hsq.sub hlin).div_const 2) using 1
          ring
        exact hreal.ofReal_comp
      have hv_deriv : ∀ t ∈ Set.Ioo (min (n : ℝ) ((n + 1 : ℕ) : ℝ)) (max (n : ℝ) ((n + 1 : ℕ) : ℝ)),
          HasDerivAt v ((-z - 1) * (t : ℂ) ^ (-z - 2)) t := by
        intro t ht
        rw [hmin] at ht
        have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg n) ht.1
        convert ofReal_cpow_hasDerivAt ht0 (-z - 1) using 1
        ring_nf
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        hu_cont hv_cont hu_deriv hv_deriv
        (ContinuousOn.intervalIntegrable (by fun_prop))
        ((ContinuousOn.mul continuousOn_const
          (Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦ by
            rw [Set.uIcc_of_le hle] at ht
            exact Complex.mem_slitPlane_iff.mpr
              (Or.inl (by simp; linarith [ht.1, show (0 : ℝ) < n by positivity])))).intervalIntegrable)
      have hlhs_eq :
          ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) =
            ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), ((t - (n : ℝ) - 1 / 2 : ℝ) : ℂ) * v t := by
        refine intervalIntegral.integral_congr_ae ?_
        have hne : ∀ᵐ t ∂volume, t ≠ ((n + 1 : ℕ) : ℝ) := ae_ne_real _
        filter_upwards [hne] with t htne htmem
        rw [Set.uIoc_of_le hle] at htmem
        have ht_ico : t ∈ Set.Ico (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
          ⟨htmem.1.le, lt_of_le_of_ne htmem.2 htne⟩
        have hflZ : ⌊t⌋ = (n : ℤ) := Int.floor_eq_iff.mpr
          ⟨by exact_mod_cast ht_ico.1, by exact_mod_cast ht_ico.2⟩
        have hsaw : sawtooth t = t - (n : ℝ) - 1 / 2 := by
          rw [sawtooth, Int.fract, hflZ, Int.cast_natCast]
        rw [hsaw]
      have hrhs_eq :
          ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), u t * ((-z - 1) * (t : ℂ) ^ (-z - 2)) =
            (-z - 1) * ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), B t * (t : ℂ) ^ (-z - 2) := by
        have hcon :
            ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), u t * ((-z - 1) * (t : ℂ) ^ (-z - 2)) =
              ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), (-z - 1) * (B t * (t : ℂ) ^ (-z - 2)) := by
          refine intervalIntegral.integral_congr_ae ?_
          have hne : ∀ᵐ t ∂volume, t ≠ ((n + 1 : ℕ) : ℝ) := ae_ne_real _
          filter_upwards [hne] with t htne htmem
          rw [Set.uIoc_of_le hle] at htmem
          have ht_ico : t ∈ Set.Ico (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
            ⟨htmem.1.le, lt_of_le_of_ne htmem.2 htne⟩
          have hflZ : ⌊t⌋ = (n : ℤ) := Int.floor_eq_iff.mpr
            ⟨by exact_mod_cast ht_ico.1, by exact_mod_cast ht_ico.2⟩
          have hBt : B t = u t := by
            dsimp only [B, u]
            rw [bernoulliKernel_two, Int.fract, hflZ, Int.cast_natCast]
            congr 1
            ring
          rw [hBt]
          ring
        rw [hcon, intervalIntegral.integral_const_mul]
      have hun : u (n : ℝ) = 0 := by simp [u]
      have hun1 : u ((n + 1 : ℕ) : ℝ) = 0 := by simp [u]
      rw [hlhs_eq]
      have hibp' : ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), ((t - (n : ℝ) - 1 / 2 : ℝ) : ℂ) * v t =
          u ((n + 1 : ℕ) : ℝ) * v ((n + 1 : ℕ) : ℝ) - u (n : ℝ) * v (n : ℝ) -
            ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), u t * ((-z - 1) * (t : ℂ) ^ (-z - 2)) := by
        conv_lhs =>
          rw [← sub_sub_cancel
            (u ((n + 1 : ℕ) : ℝ) * v ((n + 1 : ℕ) : ℝ) - u (n : ℝ) * v (n : ℝ))
            (∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), ((t - (n : ℝ) - 1 / 2 : ℝ) : ℂ) * v t)]
        rw [← hibp]
      rw [hibp', hun, hun1, zero_mul, zero_mul, sub_self, zero_sub, hrhs_eq]
      ring
    have hsum_abel : ∀ N : ℕ, 1 ≤ N →
        (z - 1) * ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-z) =
          (z - 1) * ((N : ℂ) ^ (1 - z) / (1 - z)) + z - (z - 1) * (1 - (N : ℂ) ^ (-z)) / 2 -
            (z - 1) * z * (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), B t * (t : ℂ) ^ (-z - 2) := by
      intro N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hab := abel_summation_Icc_one_hasDerivAt (fun _ : ℕ ↦ (1 : ℂ))
        (f := fun t : ℝ ↦ (t : ℂ) ^ (-z))
        (f' := fun t : ℝ ↦ -z * (t : ℂ) ^ (-z - 1)) hN1
        (fun t ht ↦ ofReal_cpow_hasDerivAt (lt_of_lt_of_le zero_lt_one ht.1) (-z))
        (ContinuousOn.mul continuousOn_const
          (Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦
            Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [ht.1]))))
      simp only [one_mul] at hab
      have hsum1 : ∑ _k ∈ Finset.Icc 1 N, (1 : ℂ) = (N : ℂ) := by
        simp [Nat.card_Icc]
      rw [Nat.floor_natCast, hsum1] at hab
      have hint_pow0 : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1)) volume 1 N := by
        refine (Complex.continuous_ofReal.continuousOn.cpow_const fun x hx ↦ ?_).intervalIntegrable
        rw [Set.uIcc_of_le hN1] at hx
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [hx.1]))
      have hint_pow1 : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ (-z)) volume 1 N := by
        refine (Complex.continuous_ofReal.continuousOn.cpow_const fun x hx ↦ ?_).intervalIntegrable
        rw [Set.uIcc_of_le hN1] at hx
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [hx.1]))
      have hint_saw : IntervalIntegrable (fun t : ℝ ↦ (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1)) volume 1 N :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hN1).mpr
          (hsaw_int_Ioi.mono_set Set.Ioc_subset_Ioi_self)
      have hfloor_split :
          ∫ t in (1 : ℝ)..(N : ℝ), (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (-z * (t : ℂ) ^ (-z - 1)) =
            (-z) * ((∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z)) -
              (1 / 2 : ℂ) * (∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1)) -
              ∫ t in (1 : ℝ)..(N : ℝ), (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
        have hcon1 :
            ∫ t in (1 : ℝ)..(N : ℝ), (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (-z * (t : ℂ) ^ (-z - 1)) =
              (-z) * ∫ t in (1 : ℝ)..(N : ℝ), ((t : ℂ) ^ (-z) -
                ((1 / 2 : ℂ) * (t : ℂ) ^ (-z - 1) + (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1))) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun t ht ↦ ?_
          rw [Set.uIcc_of_le hN1] at ht
          have ht0 : 0 ≤ t := by linarith [ht.1]
          have ht_pos : 0 < t := by linarith [ht.1]
          have hcard : ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ) = ((⌊t⌋₊ : ℝ) : ℂ) := by
            simp [Nat.card_Icc]
          have hfl_eq : (⌊t⌋₊ : ℝ) = t - sawtooth t - 1 / 2 := by
            have hflZ : (⌊t⌋₊ : ℤ) = ⌊t⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr ht0)
            rw [sawtooth, Int.fract, ← hflZ, Int.cast_natCast]
            ring
          have hcpow_mul : (t : ℂ) * (t : ℂ) ^ (-z - 1) = (t : ℂ) ^ (-z) := by
            have h1 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
            conv_lhs => lhs; rw [← Complex.cpow_one (t : ℂ)]
            rw [← Complex.cpow_add _ _ h1]
            congr 1
            ring
          rw [hcard, hfl_eq]
          push_cast
          calc
            ((t : ℂ) - ((sawtooth t : ℝ) : ℂ) - 1 / 2) * (-z * (t : ℂ) ^ (-z - 1))
                = (-z) * ((t : ℂ) * (t : ℂ) ^ (-z - 1) -
                    ((1 / 2 : ℂ) * (t : ℂ) ^ (-z - 1) + ((sawtooth t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))) := by
                  ring
            _ = (-z) * ((t : ℂ) ^ (-z) -
                  ((1 / 2 : ℂ) * (t : ℂ) ^ (-z - 1) + ((sawtooth t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))) := by
                  rw [hcpow_mul]
        rw [hcon1, intervalIntegral.integral_sub hint_pow1 ((hint_pow0.const_mul (1 / 2 : ℂ)).add hint_saw),
          intervalIntegral.integral_add (hint_pow0.const_mul (1 / 2 : ℂ)) hint_saw,
          intervalIntegral.integral_const_mul]
        ring
      have hftc_z : ∫ t in (1 : ℝ)..(N : ℝ), (1 - z) * (t : ℂ) ^ (-z) = (N : ℂ) ^ (1 - z) - 1 := by
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht ↦ by
            rw [Set.uIcc_of_le hN1] at ht
            convert ofReal_cpow_hasDerivAt (lt_of_lt_of_le zero_lt_one ht.1) (1 - z) using 2
            ring)
          (hint_pow1.const_mul (1 - z))
        simpa [Complex.one_cpow] using h
      rw [intervalIntegral.integral_const_mul] at hftc_z
      have hftc_0 : ∫ t in (1 : ℝ)..(N : ℝ), (-z) * (t : ℂ) ^ (-z - 1) = (N : ℂ) ^ (-z) - 1 := by
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht ↦ by
            rw [Set.uIcc_of_le hN1] at ht
            exact ofReal_cpow_hasDerivAt (lt_of_lt_of_le zero_lt_one ht.1) (-z))
          (hint_pow0.const_mul (-z))
        simpa [Complex.one_cpow] using h
      rw [intervalIntegral.integral_const_mul] at hftc_0
      have hB_sum :
          ∫ t in (1 : ℝ)..(N : ℝ), (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1) =
            (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), B t * (t : ℂ) ^ (-z - 2) := by
        have hL1 := sum_intervalIntegrable_adjacent
          (fun t : ℝ ↦ (sawtooth t : ℂ) * (t : ℂ) ^ (-z - 1)) N hN fun n hn ↦ by
            simp only [Finset.mem_Ico] at hn
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
            have hn_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
            exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn_le).mpr
              (hsaw_int_Ioi.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hn1)))
        have hR1 := sum_intervalIntegrable_adjacent
          (fun t : ℝ ↦ B t * (t : ℂ) ^ (-z - 2)) N hN fun n hn ↦ by
            simp only [Finset.mem_Ico] at hn
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
            have hn_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
            exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn_le).mpr
              (hB_int_Ioi.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hn1)))
        rw [← hL1, ← hR1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun n hn ↦ hseg n (Finset.mem_Ico.mp hn).1
      have hN_pow : (N : ℂ) * (N : ℂ) ^ (-z) = (N : ℂ) ^ (1 - z) := by
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        conv_lhs => lhs; rw [← Complex.cpow_one (N : ℂ)]
        rw [← Complex.cpow_add _ _ hN0]
        congr 1
      have h1z_ne : 1 - z ≠ 0 := sub_ne_zero.mpr hz_ne1.symm
      have hi1 : ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z) = ((N : ℂ) ^ (1 - z) - 1) / (1 - z) := by
        rw [eq_div_iff h1z_ne, mul_comm]; exact hftc_z
      have hi0 : z * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1) = 1 - (N : ℂ) ^ (-z) := by
        linear_combination -hftc_0
      simp only [Complex.ofReal_natCast] at hab
      rw [hab, hfloor_split, hN_pow, hi1, hB_sum]
      calc
        (z - 1) * ((N : ℂ) ^ (1 - z) - -z * (((N : ℂ) ^ (1 - z) - 1) / (1 - z) -
            1 / 2 * (∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1)) -
            (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), B t * (t : ℂ) ^ (-z - 2)))
            = (z - 1) * ((N : ℂ) ^ (1 - z) + z * (((N : ℂ) ^ (1 - z) - 1) / (1 - z))) -
                (z - 1) * (z * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-z - 1)) / 2 -
                (z - 1) * z * (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), B t * (t : ℂ) ^ (-z - 2) := by
              ring
        _ = (z - 1) * ((N : ℂ) ^ (1 - z) / (1 - z)) + z - (z - 1) * (1 - (N : ℂ) ^ (-z)) / 2 -
              (z - 1) * z * (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), B t * (t : ℂ) ^ (-z - 2) := by
            rw [hi0]
            field_simp [h1z_ne]
            ring
    have htend_lhs : Tendsto (fun N : ℕ ↦ (z - 1) * ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-z))
        atTop (𝓝 ((z - 1) * riemannZeta z)) :=
      tendsto_const_nhds.mul htend_series
    have htend_rhs : Tendsto
        (fun N : ℕ ↦ (z - 1) * ((N : ℂ) ^ (1 - z) / (1 - z)) + z -
          (z - 1) * (1 - (N : ℂ) ^ (-z)) / 2 -
          (z - 1) * z * (z + 1) * ∫ t in (1 : ℝ)..(N : ℝ), B t * (t : ℂ) ^ (-z - 2))
        atTop (𝓝 (J z)) := by
      have htend_N1z : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (1 - z)) atTop (𝓝 0) := by
        have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr hz_ne1.symm
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (g := fun N : ℕ ↦ (N : ℝ) ^ (-(z.re - 1)))
          (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) ?_
        · by_cases hN0 : N = 0
          · subst hN0
            simp [Complex.zero_cpow h1z]
            positivity
          · rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN0)]
            have hre_eq : (1 - z).re = -(z.re - 1) := by simp
            rw [hre_eq]
        · have hre_neg : 0 < z.re - 1 := sub_pos.mpr hz
          exact (tendsto_rpow_neg_atTop hre_neg).comp tendsto_natCast_atTop_atTop
      have htend_Nz : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-z)) atTop (𝓝 0) := by
        have hnz : -z ≠ 0 := neg_ne_zero.mpr hz0
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (g := fun N : ℕ ↦ (N : ℝ) ^ (-z.re))
          (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) ?_
        · by_cases hN0 : N = 0
          · subst hN0; simp [Complex.zero_cpow hnz]; positivity
          · rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN0)]; simp
        · exact (tendsto_rpow_neg_atTop hz_pos).comp tendsto_natCast_atTop_atTop
      have htend_int : Tendsto (fun N : ℕ ↦ ∫ t in (1 : ℝ)..(N : ℝ), B t * (t : ℂ) ^ (-z - 2))
          atTop (𝓝 (∫ t in Set.Ioi (1 : ℝ), B t * (t : ℂ) ^ (-z - 2))) :=
        intervalIntegral_tendsto_integral_Ioi 1 hB_int_Ioi tendsto_natCast_atTop_atTop
      have hcomb := (((tendsto_const_nhds (x := z - 1)).mul (htend_N1z.div_const (1 - z))).add
        (tendsto_const_nhds (x := z))).sub
        (((tendsto_const_nhds (x := z - 1)).mul ((tendsto_const_nhds (x := (1 : ℂ))).sub htend_Nz)).div_const
          2) |>.sub
        ((tendsto_const_nhds (x := (z - 1) * z * (z + 1))).mul htend_int)
      simpa [J] using hcomb
    have htend_rhs' : Tendsto (fun N : ℕ ↦ (z - 1) * ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-z))
        atTop (𝓝 (J z)) := by
      refine htend_rhs.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hsum_abel N hN).symm
    exact tendsto_nhds_unique htend_lhs htend_rhs'
  have hopen : IsOpen {z : ℂ | -1 < z.re} :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).preimage Complex.continuous_re
  have hconn : IsPreconnected {z : ℂ | -1 < z.re} := (convex_halfSpace_re_gt (-1)).isPreconnected
  have hZ_an : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | -1 < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  have hJ_an : AnalyticOnNhd ℂ J {z : ℂ | -1 < z.re} := hJ_diff.analyticOnNhd hopen
  have hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] J := by
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      ((isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ))).preimage Complex.continuous_re).mem_nhds
        (by norm_num)
    exact Filter.eventually_of_mem hmem heq_on_right
  exact hZ_an.eqOn_of_preconnected_of_eventuallyEq hJ_an hconn (by norm_num) hev hs

/-- Cubic height growth of pole-cleared zeta on the closed strip −1/2 ≤ Re(s) ≤ 2. -/
theorem norm_riemannZeta₁_strip_poly_le {s : ℂ}
    (hs_lo : -(1 / 2 : ℝ) ≤ s.re) (hs_hi : s.re ≤ 2) :
    ‖riemannZeta₁ s‖ ≤ 10 * (|s.im| + 2) ^ 3 := by
  have hs_gt : -1 < s.re := by linarith
  rw [riemannZeta₁_eq_second_order_integral hs_gt]
  have hint_le :
      ‖∫ t in Set.Ioi (1 : ℝ), ((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2)‖ ≤
        1 / 3 := by
    have hint_real : IntegrableOn (fun t : ℝ ↦ (1 / 6 : ℝ) * t ^ (-s.re - 2)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) zero_lt_one).const_mul _
    calc
      ‖∫ t in Set.Ioi (1 : ℝ), ((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2)‖
          ≤ ∫ t in Set.Ioi (1 : ℝ), ‖((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2)‖ :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), (1 / 6 : ℝ) * t ^ (-s.re - 2) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
            hint_real ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := lt_trans zero_lt_one ht
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp only [sub_re, neg_re, re_ofNat]
          have hB_le : |bernoulliKernel 2 t - 1 / 12| ≤ 1 / 6 := by
            have hb := bernoulliKernel_two_abs_le t
            calc
              |bernoulliKernel 2 t - 1 / 12| ≤ |bernoulliKernel 2 t| + |-(1 / 12 : ℝ)| := by
                  simpa [sub_eq_add_neg] using abs_add_le (bernoulliKernel 2 t) (-(1 / 12 : ℝ))
              _ ≤ 1 / 6 := by norm_num at *; linarith
          exact mul_le_mul_of_nonneg_right hB_le (Real.rpow_nonneg ht0.le _)
      _ = (1 / 6 : ℝ) * ∫ t in Set.Ioi (1 : ℝ), t ^ (-s.re - 2) := integral_const_mul _ _
      _ = (1 / 6 : ℝ) * (-(1 : ℝ) ^ (-s.re - 2 + 1) / (-s.re - 2 + 1)) := by
          rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      _ = (1 / 6 : ℝ) / (s.re + 1) := by
          rw [Real.one_rpow, show -s.re - 2 + 1 = -(s.re + 1) by ring]
          have hne : s.re + 1 ≠ 0 := by linarith
          field_simp [hne]
      _ ≤ (1 / 6 : ℝ) / (1 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = 1 / 3 := by norm_num
  have hs_norm : ‖s‖ ≤ 2 * (|s.im| + 2) := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ ≤ 2 + |s.im| := add_le_add (abs_le.mpr ⟨by linarith, hs_hi⟩) le_rfl
      _ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
  have hsm1_norm : ‖s - 1‖ ≤ 2 * (|s.im| + 2) := by
    calc
      ‖s - 1‖ ≤ |s.re - 1| + |s.im| := by simpa using norm_le_abs_re_add_abs_im (s - 1)
      _ ≤ 2 + |s.im| := add_le_add (abs_le.mpr ⟨by linarith, by linarith⟩) le_rfl
      _ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
  have hsp1_norm : ‖s + 1‖ ≤ 3 * (|s.im| + 2) := by
    calc
      ‖s + 1‖ ≤ |s.re + 1| + |s.im| := by simpa using norm_le_abs_re_add_abs_im (s + 1)
      _ ≤ 3 + |s.im| := add_le_add (abs_le.mpr ⟨by linarith, by linarith⟩) le_rfl
      _ ≤ 3 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
  have h1_le_sq : 1 ≤ (|s.im| + 2) ^ 2 := by nlinarith [abs_nonneg s.im]
  calc
    ‖s - (s - 1) / 2 - (s - 1) * s * (s + 1) *
        ∫ t in Set.Ioi (1 : ℝ), ((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2)‖
        ≤ ‖s - (s - 1) / 2‖ + ‖(s - 1) * s * (s + 1) *
            ∫ t in Set.Ioi (1 : ℝ), ((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2)‖ :=
          norm_sub_le _ _
    _ ≤ (‖s‖ + ‖s - 1‖ / 2) +
          (‖s - 1‖ * ‖s‖ * ‖s + 1‖) *
            ‖∫ t in Set.Ioi (1 : ℝ), ((bernoulliKernel 2 t - 1 / 12 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2)‖ := by
          refine add_le_add ?_ ?_
          · exact (norm_sub_le _ _).trans (by rw [norm_div, Complex.norm_ofNat])
          · simp only [norm_mul, mul_assoc]
            exact le_rfl
    _ ≤ (2 * (|s.im| + 2) + (|s.im| + 2)) +
          (2 * (|s.im| + 2)) * (2 * (|s.im| + 2)) * (3 * (|s.im| + 2)) * (1 / 3) := by
          refine add_le_add (by linarith) ?_
          exact mul_le_mul
            (mul_le_mul (mul_le_mul hsm1_norm hs_norm (norm_nonneg _) (by positivity))
              hsp1_norm (norm_nonneg _) (by positivity))
            hint_le (norm_nonneg _) (by positivity)
    _ = 3 * (|s.im| + 2) + 4 * (|s.im| + 2) ^ 3 := by ring
    _ ≤ 3 * (|s.im| + 2) ^ 3 + 4 * (|s.im| + 2) ^ 3 := by
          nlinarith [h1_le_sq, show (0 : ℝ) ≤ |s.im| + 2 by positivity]
    _ ≤ 10 * (|s.im| + 2) ^ 3 := by nlinarith [h1_le_sq, show (0 : ℝ) ≤ |s.im| + 2 by positivity]

end ContinuationAndEulerMaclaurin

section CompletedAndFunctionalEquation

/-- Parity exponent `κ ∈ {0, 1}`: `0` when `χ` is even (`χ (-1) = 1`) and `1` when `χ` is odd
(`χ (-1) = -1`). -/
def parityExp {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ :=
  if χ.Even then 0 else 1

/-- `parityExp` is `0` for even characters. -/
theorem parityExp_of_even {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Even) :
    parityExp χ = 0 := by simp [parityExp, hχ]

/-- `parityExp` is `1` for odd characters. -/
theorem parityExp_of_odd {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Odd) :
    parityExp χ = 1 := by simp [parityExp, hχ.not_even]

/-- `parityExp (star χ) = parityExp χ` because `(star χ) (-1) = star (χ (-1)) = χ (-1)`. -/
@[simp]
theorem parityExp_star {q : ℕ} (χ : DirichletCharacter ℂ q) :
    parityExp (star χ) = parityExp χ := by
  have heven : (star χ).Even ↔ χ.Even := by
    rw [DirichletCharacter.Even, DirichletCharacter.Even]
    constructor
    · intro h
      have hsq : star (χ (-1)) = (1 : ℂ) := by simpa using h
      simpa using congrArg star hsq
    · intro h
      simp [h]
  simp [parityExp, heven]

/-- `DirichletCharacter.gammaFactor χ s = Complex.Gammaℝ (s + parityExp χ)`. -/
theorem gammaFactor_eq_Gammaℝ {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    DirichletCharacter.gammaFactor χ s = Complex.Gammaℝ (s + (parityExp χ : ℂ)) := by
  rcases χ.even_or_odd with hχ | hχ
  · simp [hχ.gammaFactor_def, parityExp_of_even hχ]
  · simp [hχ.gammaFactor_def, parityExp_of_odd hχ]

/-- Explicit Gamma-factor formula:
`DirichletCharacter.gammaFactor χ s = π^(-(s + κ)/2) * Γ((s + κ)/2)`. -/
theorem gammaFactor_eq_pi_mul_Gamma {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    DirichletCharacter.gammaFactor χ s =
      (Real.pi : ℂ) ^ (-(s + (parityExp χ : ℂ)) / 2) *
        Complex.Gamma ((s + (parityExp χ : ℂ)) / 2) := by
  rw [gammaFactor_eq_Gammaℝ, Complex.Gammaℝ_def]

/-- Relation between `LFunction` and `completedLFunction` for `s ≠ 0 ∨ q ≠ 1`. -/
theorem LFunction_eq_completed_div_gammaFactor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : s ≠ 0 ∨ q ≠ 1) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s / DirichletCharacter.gammaFactor χ s :=
  DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hs

/-- Multiplicative form `completedLFunction χ s = LFunction χ s * gammaFactor χ s` whenever
`gammaFactor χ s ≠ 0` (and `s ≠ 0 ∨ q ≠ 1`). -/
theorem completedLFunction_eq_mul_gammaFactor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 0 ∨ q ≠ 1)
    (hg : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  rw [LFunction_eq_completed_div_gammaFactor χ s hs, div_mul_cancel₀ _ hg]

/-- `completedLFunction χ s` is differentiable away from `{0, 1}` (entire when `χ ≠ 1`). -/
theorem differentiableAt_completedLFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs₀ : s ≠ 0 ∨ q ≠ 1) (hs₁ : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (DirichletCharacter.completedLFunction χ) s :=
  DirichletCharacter.differentiableAt_completedLFunction χ s hs₀ hs₁

/-- For non-principal `χ ≠ 1`, `completedLFunction χ` is entire on `ℂ`. -/
theorem differentiable_completedLFunction_of_ne_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
  DirichletCharacter.differentiable_completedLFunction hχ

/-- The root number of a primitive Dirichlet character has absolute value `1`. -/
theorem norm_rootNumber_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    ‖DirichletCharacter.rootNumber χ‖ = 1 :=
  DirichletCharacter.norm_rootNumber hχ

/-- **Functional equation for completed primitive Dirichlet L-functions**:
`completedLFunction χ (1 - s) = q^(s - 1/2) * rootNumber χ * completedLFunction (star χ) s`. -/
theorem completedLFunction_one_sub_primitive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      (q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction (star χ) s := by
  rw [MulChar.star_eq_inv]
  exact hχ.completedLFunction_one_sub s

/-- **Asymmetric functional equation** for `DirichletCharacter.LFunction χ`:
for a primitive character `χ` modulo `q` and `s : ℂ` with `1 - s ≠ 0 ∨ q ≠ 1`, `s ≠ 0 ∨ q ≠ 1`,
and `gammaFactor (star χ) s ≠ 0`,
`LFunction χ (1 - s) = q^(s - 1/2) * rootNumber χ * (gammaFactor (star χ) s / gammaFactor χ (1 - s)) * LFunction (star χ) s`. -/
theorem LFunction_one_sub_primitive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h1s : 1 - s ≠ 0 ∨ q ≠ 1) (hs : s ≠ 0 ∨ q ≠ 1)
    (hg2 : DirichletCharacter.gammaFactor (star χ) s ≠ 0) :
    DirichletCharacter.LFunction χ (1 - s) =
      (q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
        (DirichletCharacter.gammaFactor (star χ) s / DirichletCharacter.gammaFactor χ (1 - s)) *
        DirichletCharacter.LFunction (star χ) s := by
  rw [LFunction_eq_completed_div_gammaFactor χ (1 - s) h1s,
    completedLFunction_one_sub_primitive hχ s,
    completedLFunction_eq_mul_gammaFactor (star χ) hs hg2]
  ring

end CompletedAndFunctionalEquation

section ConvexityStripBounds

private noncomputable def rademacherWeight (δ : ℝ) (s : ℂ) : ℂ :=
  (Complex.Gamma ((s + 3) / 4) / Complex.Gamma ((3 + (δ : ℂ) - s) / 4)) *
    (s + 3) ^ (-((1 / 2 + δ / 4 : ℝ) : ℂ))

private lemma rademacherWeight_differentiableOn {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    DifferentiableOn ℂ (rademacherWeight δ) {s : ℂ | -1 < s.re ∧ s.re < 2} := by
  intro s hs
  have hgam1 : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma ((w + 3) / 4)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m hm ↦ ?_).comp s (by fun_prop)
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hs.1]
  have hgam2_ne : ∀ m : ℕ, (3 + (δ : ℂ) - s) / 4 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hs.2, hδ0]
  have hgam2 : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma ((3 + (δ : ℂ) - w) / 4)) s :=
    (Complex.differentiableAt_Gamma _ hgam2_ne).comp s (by fun_prop)
  have hcpow : DifferentiableAt ℂ (fun w : ℂ ↦ (w + 3) ^ (-((1 / 2 + δ / 4 : ℝ) : ℂ))) s := by
    refine (differentiableAt_id.add_const 3).cpow_const ?_
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [hs.1]))
  exact ((hgam1.div hgam2 (Complex.Gamma_ne_zero hgam2_ne)).mul hcpow).differentiableWithinAt

private lemma rademacherWeight_ne_zero {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (-δ) (1 + δ)) :
    rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hz3 : z + 3 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [z] at this
    linarith [hσ.1]
  have hne1 : ∀ m : ℕ, (z + 3) / 4 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp [z] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hσ.1]
  have hne2 : ∀ m : ℕ, (3 + (δ : ℂ) - z) / 4 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp [z] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hσ.2]
  dsimp only [rademacherWeight]
  refine mul_ne_zero (div_ne_zero (Complex.Gamma_ne_zero hne1) (Complex.Gamma_ne_zero hne2)) ?_
  rw [Complex.cpow_def_of_ne_zero hz3]
  exact Complex.exp_ne_zero _

private lemma norm_rademacherWeight_strip_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ m₁ M₁ : ℝ, 0 < m₁ ∧
      ∀ {σ t : ℝ}, σ ∈ Set.Icc (-δ) (1 + δ) →
        m₁ * (|t| + 2) ^ ((σ - 1 - δ) / 2) ≤ ‖rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I)‖ ∧
        ‖rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M₁ * (|t| + 2) ^ ((σ - 1 - δ) / 2) := by
  obtain ⟨c_γ, C_γ, hc_pos, hc_le, hst⟩ := norm_complex_gamma_strip_bounds (1 / 2) 2
  have hC_pos : 0 < C_γ := lt_of_lt_of_le hc_pos hc_le
  have hcompact_dom : IsCompact (Set.Icc (-δ) (1 + δ) ×ˢ Set.Icc (-4 : ℝ) 4) :=
    isCompact_Icc.prod isCompact_Icc
  let fnorm : ℝ × ℝ → ℝ := fun p ↦ ‖rademacherWeight δ ((p.1 : ℂ) + (p.2 : ℂ) * I)‖
  have hcont : ContinuousOn fnorm (Set.Icc (-δ) (1 + δ) ×ˢ Set.Icc (-4 : ℝ) 4) := by
    have hdiff := rademacherWeight_differentiableOn hδ0 hδ1
    have hmap : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hsub : Set.MapsTo (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * I)
        (Set.Icc (-δ) (1 + δ) ×ˢ Set.Icc (-4 : ℝ) 4) {s : ℂ | -1 < s.re ∧ s.re < 2} := by
      intro p hp
      simp only [Set.mem_prod, Set.mem_Icc] at hp
      have hre : ((p.1 : ℂ) + (p.2 : ℂ) * I).re = p.1 := by simp
      rw [Set.mem_ofPred_eq, hre]
      constructor <;> linarith [hp.1.1, hp.1.2]
    exact (hdiff.continuousOn.comp hmap.continuousOn hsub).norm
  have hne : (Set.Icc (-δ) (1 + δ) ×ˢ Set.Icc (-4 : ℝ) 4).Nonempty :=
    ⟨(0, 0), ⟨by linarith, by linarith⟩, by norm_num⟩
  obtain ⟨p_min, hp_min_mem, hp_min⟩ := hcompact_dom.exists_isMinOn hne hcont
  obtain ⟨p_max, _, hp_max⟩ := hcompact_dom.exists_isMaxOn hne hcont
  have hm₀_pos : 0 < fnorm p_min := by
    rw [norm_pos_iff]
    exact rademacherWeight_ne_zero hδ0 hδ1 hp_min_mem.1
  let m_small := fnorm p_min / 6
  let M_small := 6 * fnorm p_max
  let m_large := (c_γ / C_γ) * (1 / 6) * (1 / 3)
  let M_large := (C_γ / c_γ) * 6 * 2
  refine ⟨min m_small m_large, max M_small M_large, lt_min (by positivity) (by positivity), ?_⟩
  intro σ t hσ
  have hexp_range : -1 ≤ (σ - 1 - δ) / 2 ∧ (σ - 1 - δ) / 2 ≤ 0 := by
    constructor <;> linarith [hσ.1, hσ.2]
  by_cases ht4 : |t| ≤ 4
  · have hmem : (σ, t) ∈ Set.Icc (-δ) (1 + δ) ×ˢ Set.Icc (-4 : ℝ) 4 :=
      ⟨hσ, abs_le.mp ht4⟩
    have ht2_hi : |t| + 2 ≤ 6 := by linarith
    have hrpow_lo : (1 / 6 : ℝ) ≤ (|t| + 2) ^ ((σ - 1 - δ) / 2) := by
      have h1 : (|t| + 2 : ℝ) ^ (-1 : ℝ) ≤ (|t| + 2) ^ ((σ - 1 - δ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hexp_range.1
      have h2 : (6 : ℝ) ^ (-1 : ℝ) ≤ (|t| + 2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [abs_nonneg t]) ht2_hi (by norm_num)
      have h3 : (6 : ℝ) ^ (-1 : ℝ) = 1 / 6 := by norm_num
      exact h3.symm.trans_le (h2.trans h1)
    have hrpow_hi : (|t| + 2) ^ ((σ - 1 - δ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) hexp_range.2
    constructor
    · calc
        min m_small m_large * (|t| + 2) ^ ((σ - 1 - δ) / 2)
            ≤ m_small * 1 := mul_le_mul (min_le_left _ _) hrpow_hi (by positivity) (by positivity)
        _ ≤ fnorm p_min := by dsimp only [m_small]; linarith
        _ ≤ fnorm (σ, t) := hp_min hmem
    · calc
        fnorm (σ, t) ≤ fnorm p_max := hp_max hmem
        _ ≤ M_small * (1 / 6) := by dsimp only [M_small]; linarith
        _ ≤ max M_small M_large * (|t| + 2) ^ ((σ - 1 - δ) / 2) :=
            mul_le_mul (le_max_left _ _) hrpow_lo (by positivity) (by positivity)
  · have ht_gt : 4 < |t| := lt_of_not_ge ht4
    have ht4_ge1 : 1 ≤ |t / 4| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith
    have ht4_neg_ge1 : 1 ≤ |-t / 4| := by
      simpa [neg_div, abs_neg] using ht4_ge1
    have hσ1_mem : (σ + 3) / 4 ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      constructor <;> linarith [hσ.1, hσ.2]
    have hσ2_mem : (3 + δ - σ) / 4 ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      constructor <;> linarith [hσ.1, hσ.2]
    have hgam1 := hst hσ1_mem ht4_ge1
    have hgam2 := hst hσ2_mem ht4_neg_ge1
    have heq1 : (((σ : ℂ) + (t : ℂ) * I + 3) / 4) =
        (((σ + 3) / 4 : ℝ) : ℂ) + ((t / 4 : ℝ) : ℂ) * I := by
      push_cast; ring
    have heq2 : ((3 + (δ : ℂ) - ((σ : ℂ) + (t : ℂ) * I)) / 4) =
        (((3 + δ - σ) / 4 : ℝ) : ℂ) + ((-t / 4 : ℝ) : ℂ) * I := by
      push_cast; ring
    have habs_eq : |-t / 4| = |t / 4| := by rw [neg_div, abs_neg]
    rw [habs_eq] at hgam2
    have hz3 : ((σ : ℂ) + (t : ℂ) * I + 3) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith [hσ.1]
    have hnorm_rad :
        ‖rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I)‖ =
          (‖Complex.Gamma (((σ + 3) / 4 : ℝ) + ((t / 4 : ℝ) : ℂ) * I)‖ /
            ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖) *
            ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) := by
      dsimp only [rademacherWeight]
      rw [norm_mul, norm_div, heq1, heq2, ← Complex.ofReal_neg, norm_cpow_ofReal_exponent hz3]
    have ht4_pos : 0 < |t / 4| := by linarith
    have hexp_diff :
        |t / 4| ^ ((σ + 3) / 4 - 1 / 2) / |t / 4| ^ ((3 + δ - σ) / 4 - 1 / 2) =
          |t / 4| ^ ((σ - δ / 2) / 2) := by
      rw [← Real.rpow_sub ht4_pos]
      congr 1; ring
    have hgam_ratio_lo : (c_γ / C_γ) * |t / 4| ^ ((σ - δ / 2) / 2) ≤
        ‖Complex.Gamma (((σ + 3) / 4 : ℝ) + ((t / 4 : ℝ) : ℂ) * I)‖ /
          ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖ := by
      rw [← hexp_diff]
      have hden_pos : 0 < ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖ := by
        refine norm_pos_iff.mpr (Complex.Gamma_ne_zero fun m hm ↦ ?_)
        have hre := congrArg Complex.re hm
        simp at hre
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith [hσ.2]
      have hbd_pos : 0 < C_γ * Real.exp (-(Real.pi / 2) * |t / 4|) * |t / 4| ^ ((3 + δ - σ) / 4 - 1 / 2) := by
        positivity
      calc
        c_γ / C_γ * (|t / 4| ^ ((σ + 3) / 4 - 1 / 2) / |t / 4| ^ ((3 + δ - σ) / 4 - 1 / 2))
            = (c_γ * Real.exp (-(Real.pi / 2) * |t / 4|) * |t / 4| ^ ((σ + 3) / 4 - 1 / 2)) /
                (C_γ * Real.exp (-(Real.pi / 2) * |t / 4|) * |t / 4| ^ ((3 + δ - σ) / 4 - 1 / 2)) := by
              have hexp_ne : Real.exp (-(Real.pi / 2) * |t / 4|) ≠ 0 := Real.exp_ne_zero _
              field_simp [hexp_ne, hC_pos.ne']
        _ ≤ ‖Complex.Gamma (((σ + 3) / 4 : ℝ) + ((t / 4 : ℝ) : ℂ) * I)‖ /
              ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖ :=
            div_le_div₀ (by positivity) hgam1.1 hden_pos hgam2.2
    have hgam_ratio_hi :
        ‖Complex.Gamma (((σ + 3) / 4 : ℝ) + ((t / 4 : ℝ) : ℂ) * I)‖ /
          ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖ ≤
          (C_γ / c_γ) * |t / 4| ^ ((σ - δ / 2) / 2) := by
      rw [← hexp_diff]
      have hbd_pos : 0 < c_γ * Real.exp (-(Real.pi / 2) * |t / 4|) * |t / 4| ^ ((3 + δ - σ) / 4 - 1 / 2) := by
        positivity
      calc
        ‖Complex.Gamma (((σ + 3) / 4 : ℝ) + ((t / 4 : ℝ) : ℂ) * I)‖ /
            ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖
            ≤ (C_γ * Real.exp (-(Real.pi / 2) * |t / 4|) * |t / 4| ^ ((σ + 3) / 4 - 1 / 2)) /
                (c_γ * Real.exp (-(Real.pi / 2) * |t / 4|) * |t / 4| ^ ((3 + δ - σ) / 4 - 1 / 2)) :=
              div_le_div₀ (by positivity) hgam1.2 hbd_pos hgam2.1
        _ = C_γ / c_γ * (|t / 4| ^ ((σ + 3) / 4 - 1 / 2) / |t / 4| ^ ((3 + δ - σ) / 4 - 1 / 2)) := by
              have hexp_ne : Real.exp (-(Real.pi / 2) * |t / 4|) ≠ 0 := Real.exp_ne_zero _
              field_simp [hexp_ne, hc_pos.ne']
    have ht4_cmp_lo : (|t| + 2) / 6 ≤ |t / 4| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith
    have ht4_cmp_hi : |t / 4| ≤ |t| + 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith
    have hpow_z3_lo : (|t| + 2) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I + 3‖ := by
      have hsq : ((|t| + 2) / 2) ^ 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        have hre_eq : ((σ : ℂ) + (t : ℂ) * I + 3).re = σ + 3 := by simp
        have him_eq : ((σ : ℂ) + (t : ℂ) * I + 3).im = t := by simp
        rw [hre_eq, him_eq]
        have h1 : (11 / 4 : ℝ) ≤ σ + 3 := by linarith [hσ.1]
        nlinarith [sq_nonneg (|t| - 2 / 3), sq_abs t]
      exact le_of_sq_le_sq hsq (norm_nonneg _)
    have hpow_z3_hi : ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ≤ 3 * (|t| + 2) := by
      have hre : ((σ : ℂ) + (t : ℂ) * I + 3).re = σ + 3 := by simp
      have him : ((σ : ℂ) + (t : ℂ) * I + 3).im = t := by simp
      calc
        ‖(σ : ℂ) + (t : ℂ) * I + 3‖
            ≤ |((σ : ℂ) + (t : ℂ) * I + 3).re| + |((σ : ℂ) + (t : ℂ) * I + 3).im| :=
              norm_le_abs_re_add_abs_im _
        _ = |σ + 3| + |t| := by rw [hre, him]
        _ ≤ 5 + |t| := add_le_add (abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩) le_rfl
        _ ≤ 3 * (|t| + 2) := by linarith [abs_nonneg t]
    have hα_range : -1 ≤ (σ - δ / 2) / 2 ∧ (σ - δ / 2) / 2 ≤ 1 := by
      constructor <;> linarith [hσ.1, hσ.2, hδ0, hδ1]
    have ht4_sandwich :
        (1 / 6 : ℝ) * (|t| + 2) ^ ((σ - δ / 2) / 2) ≤ |t / 4| ^ ((σ - δ / 2) / 2) ∧
          |t / 4| ^ ((σ - δ / 2) / 2) ≤ 6 * (|t| + 2) ^ ((σ - δ / 2) / 2) := by
      rcases le_or_gt 0 ((σ - δ / 2) / 2) with hα | hα
      · have h1 : ((|t| + 2) / 6) ^ ((σ - δ / 2) / 2) ≤ |t / 4| ^ ((σ - δ / 2) / 2) :=
          Real.rpow_le_rpow (by positivity) ht4_cmp_lo hα
        have h2 : |t / 4| ^ ((σ - δ / 2) / 2) ≤ (|t| + 2) ^ ((σ - δ / 2) / 2) :=
          Real.rpow_le_rpow ht4_pos.le ht4_cmp_hi hα
        have hdiv_eq : ((|t| + 2) / 6) ^ ((σ - δ / 2) / 2) =
            (1 / 6 : ℝ) ^ ((σ - δ / 2) / 2) * (|t| + 2) ^ ((σ - δ / 2) / 2) := by
          rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity), one_div, mul_comm]
        have h6_lo : (1 / 6 : ℝ) ≤ (1 / 6 : ℝ) ^ ((σ - δ / 2) / 2) := by
          have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 6)
            (by norm_num : (1 / 6 : ℝ) ≤ 1) hα_range.2
          simpa using h
        constructor
        · calc
            (1 / 6 : ℝ) * (|t| + 2) ^ ((σ - δ / 2) / 2)
                ≤ (1 / 6 : ℝ) ^ ((σ - δ / 2) / 2) * (|t| + 2) ^ ((σ - δ / 2) / 2) :=
                  mul_le_mul_of_nonneg_right h6_lo (by positivity)
            _ = ((|t| + 2) / 6) ^ ((σ - δ / 2) / 2) := hdiv_eq.symm
            _ ≤ |t / 4| ^ ((σ - δ / 2) / 2) := h1
        · calc
            |t / 4| ^ ((σ - δ / 2) / 2) ≤ 1 * (|t| + 2) ^ ((σ - δ / 2) / 2) := by simpa using h2
            _ ≤ 6 * (|t| + 2) ^ ((σ - δ / 2) / 2) :=
                mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      · have h1 : (|t| + 2) ^ ((σ - δ / 2) / 2) ≤ |t / 4| ^ ((σ - δ / 2) / 2) :=
          Real.rpow_le_rpow_of_nonpos ht4_pos ht4_cmp_hi hα.le
        have h2 : |t / 4| ^ ((σ - δ / 2) / 2) ≤ ((|t| + 2) / 6) ^ ((σ - δ / 2) / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) ht4_cmp_lo hα.le
        have hdiv_eq : ((|t| + 2) / 6) ^ ((σ - δ / 2) / 2) =
            (6 : ℝ) ^ (-((σ - δ / 2) / 2)) * (|t| + 2) ^ ((σ - δ / 2) / 2) := by
          rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_neg_one (6 : ℝ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
          ring_nf
        have h6_hi : (6 : ℝ) ^ (-((σ - δ / 2) / 2)) ≤ 6 := by
          have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6)
            (show -((σ - δ / 2) / 2) ≤ (1 : ℝ) by linarith [hα_range.1])
          simpa using h
        constructor
        · calc
            (1 / 6 : ℝ) * (|t| + 2) ^ ((σ - δ / 2) / 2)
                ≤ 1 * (|t| + 2) ^ ((σ - δ / 2) / 2) :=
                  mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ ≤ |t / 4| ^ ((σ - δ / 2) / 2) := by simpa using h1
        · calc
            |t / 4| ^ ((σ - δ / 2) / 2)
                ≤ (6 : ℝ) ^ (-((σ - δ / 2) / 2)) * (|t| + 2) ^ ((σ - δ / 2) / 2) := by
                  rwa [← hdiv_eq]
            _ ≤ 6 * (|t| + 2) ^ ((σ - δ / 2) / 2) :=
                mul_le_mul_of_nonneg_right h6_hi (by positivity)
    have hc_neg : -(1 / 2 + δ / 4) ≤ 0 := by linarith
    have hc_lo_bound : -1 ≤ -(1 / 2 + δ / 4) := by linarith
    have hz3_rpow_lo :
        (1 / 3 : ℝ) * (|t| + 2) ^ (-(1 / 2 + δ / 4)) ≤
          ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) := by
      have h1 : (3 * (|t| + 2)) ^ (-(1 / 2 + δ / 4)) ≤
          ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) :=
        Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz3) hpow_z3_hi hc_neg
      rw [Real.mul_rpow (by norm_num) (by positivity)] at h1
      have h3_lo : (1 / 3 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 + δ / 4)) := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hc_lo_bound
        rwa [Real.rpow_neg_one, ← one_div] at h
      exact (mul_le_mul_of_nonneg_right h3_lo (by positivity)).trans h1
    have hz3_rpow_hi :
        ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) ≤
          2 * (|t| + 2) ^ (-(1 / 2 + δ / 4)) := by
      have h1 : ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) ≤
          ((|t| + 2) / 2) ^ (-(1 / 2 + δ / 4)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hpow_z3_lo hc_neg
      have hdiv_eq : ((|t| + 2) / 2) ^ (-(1 / 2 + δ / 4)) =
          (2 : ℝ) ^ (1 / 2 + δ / 4) * (|t| + 2) ^ (-(1 / 2 + δ / 4)) := by
        rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_neg_one (2 : ℝ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring_nf
      have h2_hi : (2 : ℝ) ^ (1 / 2 + δ / 4) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : 1 / 2 + δ / 4 ≤ 1)
        simpa using h
      exact h1.trans (hdiv_eq ▸ mul_le_mul_of_nonneg_right h2_hi (by positivity))
    have hexp_combine :
        (|t| + 2) ^ ((σ - δ / 2) / 2) * (|t| + 2) ^ (-(1 / 2 + δ / 4)) =
          (|t| + 2) ^ ((σ - 1 - δ) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1; ring
    constructor
    · calc
        min m_small m_large * (|t| + 2) ^ ((σ - 1 - δ) / 2)
            ≤ m_large * (|t| + 2) ^ ((σ - 1 - δ) / 2) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = ((c_γ / C_γ) * ((1 / 6 : ℝ) * (|t| + 2) ^ ((σ - δ / 2) / 2))) *
              ((1 / 3 : ℝ) * (|t| + 2) ^ (-(1 / 2 + δ / 4))) := by
              rw [← hexp_combine]
              dsimp only [m_large]; ring
        _ ≤ ((c_γ / C_γ) * |t / 4| ^ ((σ - δ / 2) / 2)) *
              ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left ht4_sandwich.1 (by positivity))
                hz3_rpow_lo (by positivity) (by positivity)
        _ ≤ (‖Complex.Gamma (((σ + 3) / 4 : ℝ) + ((t / 4 : ℝ) : ℂ) * I)‖ /
              ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖) *
              ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) :=
              mul_le_mul_of_nonneg_right hgam_ratio_lo (by positivity)
        _ = ‖rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I)‖ := hnorm_rad.symm
    · calc
        ‖rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I)‖
            = (‖Complex.Gamma (((σ + 3) / 4 : ℝ) + ((t / 4 : ℝ) : ℂ) * I)‖ /
                ‖Complex.Gamma (((3 + δ - σ) / 4 : ℝ) + ((-t / 4 : ℝ) : ℂ) * I)‖) *
                ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) := hnorm_rad
        _ ≤ ((C_γ / c_γ) * |t / 4| ^ ((σ - δ / 2) / 2)) *
              ‖(σ : ℂ) + (t : ℂ) * I + 3‖ ^ (-(1 / 2 + δ / 4)) :=
              mul_le_mul_of_nonneg_right hgam_ratio_hi (by positivity)
        _ ≤ ((C_γ / c_γ) * (6 * (|t| + 2) ^ ((σ - δ / 2) / 2))) *
              (2 * (|t| + 2) ^ (-(1 / 2 + δ / 4))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left ht4_sandwich.2 (by positivity))
                hz3_rpow_hi (by positivity) (by positivity)
        _ = M_large * (|t| + 2) ^ ((σ - 1 - δ) / 2) := by
              rw [← hexp_combine]
              dsimp only [M_large]; ring
        _ ≤ max M_small M_large * (|t| + 2) ^ ((σ - 1 - δ) / 2) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private lemma continuous_norm_gamma_vertical {σ' c : ℝ} (hσ' : ∀ m : ℕ, σ' ≠ -(m : ℝ)) :
    Continuous fun t : ℝ ↦ ‖Complex.Gamma ((σ' : ℂ) + ((c * t : ℝ) : ℂ) * I)‖ := by
  rw [continuous_iff_continuousAt]
  intro t
  have hdiff : DifferentiableAt ℂ Complex.Gamma ((σ' : ℂ) + ((c * t : ℝ) : ℂ) * I) := by
    refine Complex.differentiableAt_Gamma _ fun m hm ↦ ?_
    have hre := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
      sub_zero, add_zero, neg_re, natCast_re] at hre
    exact hσ' m hre
  have hmap : Continuous fun x : ℝ ↦ (σ' : ℂ) + ((c * x : ℝ) : ℂ) * I :=
    continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const)
  exact ContinuousAt.comp (g := fun z : ℂ ↦ ‖Complex.Gamma z‖)
    (f := fun x : ℝ ↦ (σ' : ℂ) + ((c * x : ℝ) : ℂ) * I)
    hdiff.continuousAt.norm hmap.continuousAt

private lemma gammaFactor_funcEq_ratio_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ M_Γ : ℝ, 0 < M_Γ ∧
      ∀ (κ : ℕ), κ ≤ 1 → ∀ t : ℝ,
        ‖Complex.Gammaℝ ((1 + (δ : ℂ)) - (t : ℂ) * I + (κ : ℂ))‖ /
          ‖Complex.Gammaℝ ((-(δ : ℂ)) + (t : ℂ) * I + (κ : ℂ))‖ ≤
          M_Γ * (|t| + 2) ^ (1 / 2 + δ) := by
  obtain ⟨c_γ, C_γ, hc_pos, hc_le, hst⟩ := norm_complex_gamma_strip_bounds (-1 / 2) 2
  have hC_pos : 0 < C_γ := lt_of_lt_of_le hc_pos hc_le
  have hcompact_κ : ∀ κ : ℕ, κ ≤ 1 → ∃ Mκ : ℝ, 0 < Mκ ∧
      ∀ t ∈ Set.Icc (-2 : ℝ) 2,
        ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
          ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖ ≤ Mκ := by
    intro κ hκ
    let g : ℝ → ℝ := fun t ↦
      ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
        ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖
    have hσ_den : ∀ m : ℕ, (-δ + (κ : ℝ)) / 2 ≠ -(m : ℝ) := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · simp only [Nat.cast_zero, neg_zero] at hm
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hκ with rfl | rfl
        · simp at hm; linarith
        · simp at hm; linarith
      · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
        have hκ1 : (κ : ℝ) ≤ 1 := Nat.cast_le.mpr hκ
        linarith
    have hg_cont : Continuous g := by
      refine Continuous.div ?_ ?_ fun t ↦ norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero fun m hm ↦ ?_)
      · refine continuous_norm_gamma_vertical fun m hm ↦ ?_
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
        linarith
      · exact continuous_norm_gamma_vertical hσ_den
      · have hre := congrArg Complex.re hm
        simp at hre
        exact hσ_den m hre
    have hne : (Set.Icc (-2 : ℝ) 2).Nonempty := ⟨0, by norm_num⟩
    obtain ⟨t_max, _, ht_max⟩ := isCompact_Icc.exists_isMaxOn hne hg_cont.continuousOn
    refine ⟨max (g t_max) 1, by positivity, fun t ht ↦ ?_⟩
    exact (ht_max ht).trans (le_max_left _ _)
  obtain ⟨M₀, hM₀_pos, hM₀⟩ := hcompact_κ 0 (by omega)
  obtain ⟨M₁, hM₁_pos, hM₁⟩ := hcompact_κ 1 (by omega)
  let M_Γ := max (max M₀ M₁) (C_γ / c_γ)
  refine ⟨M_Γ, by positivity, fun κ hκ t ↦ ?_⟩
  have heq_num : Complex.Gammaℝ ((1 + (δ : ℂ)) - (t : ℂ) * I + (κ : ℂ)) =
      (Real.pi : ℂ) ^ (-((1 + (δ : ℂ)) - (t : ℂ) * I + (κ : ℂ)) / 2) *
        Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I) := by
    rw [Complex.Gammaℝ_def]; congr 2; push_cast; ring
  have heq_den : Complex.Gammaℝ ((-(δ : ℂ)) + (t : ℂ) * I + (κ : ℂ)) =
      (Real.pi : ℂ) ^ (-((-(δ : ℂ)) + (t : ℂ) * I + (κ : ℂ)) / 2) *
        Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I) := by
    rw [Complex.Gammaℝ_def]; congr 2; push_cast; ring
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_num : ‖(Real.pi : ℂ) ^ (-((1 + (δ : ℂ)) - (t : ℂ) * I + (κ : ℂ)) / 2)‖ =
      Real.pi ^ (-(1 + δ + (κ : ℝ)) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi_pos]
    congr 1; simp
  have hpi_den : ‖(Real.pi : ℂ) ^ (-((-(δ : ℂ)) + (t : ℂ) * I + (κ : ℂ)) / 2)‖ =
      Real.pi ^ (-(-δ + (κ : ℝ)) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi_pos]
    congr 1; simp
  have hpi_ratio : Real.pi ^ (-(1 + δ + (κ : ℝ)) / 2) / Real.pi ^ (-(-δ + (κ : ℝ)) / 2) ≤ 1 := by
    rw [← Real.rpow_sub hpi_pos]
    have hexp : -(1 + δ + (κ : ℝ)) / 2 - (-(-δ + (κ : ℝ)) / 2) = -(1 / 2 + δ) := by ring
    rw [hexp]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
  rw [heq_num, heq_den, norm_mul, norm_mul, hpi_num, hpi_den]
  have hdiv_split :
      (Real.pi ^ (-(1 + δ + (κ : ℝ)) / 2) *
          ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖) /
        (Real.pi ^ (-(-δ + (κ : ℝ)) / 2) *
          ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖) =
        (Real.pi ^ (-(1 + δ + (κ : ℝ)) / 2) / Real.pi ^ (-(-δ + (κ : ℝ)) / 2)) *
          (‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
            ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖) := by
    ring
  rw [hdiv_split]
  have hgam_le :
      ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
        ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖ ≤
        M_Γ * (|t| + 2) ^ (1 / 2 + δ) := by
    have ht2_ge1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have hrpow_ge1 : (1 : ℝ) ≤ (|t| + 2) ^ (1 / 2 + δ) :=
      Real.one_le_rpow ht2_ge1 (by linarith)
    by_cases ht2 : |t| ≤ 2
    · have ht_mem : t ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp ht2
      have hM_le :
          ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
            ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖ ≤
            max M₀ M₁ := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hκ with rfl | rfl
        · exact (hM₀ t ht_mem).trans (le_max_left _ _)
        · exact (hM₁ t ht_mem).trans (le_max_right _ _)
      calc
        ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
            ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖
            ≤ max M₀ M₁ * 1 := by simpa using hM_le
        _ ≤ M_Γ * (|t| + 2) ^ (1 / 2 + δ) :=
            mul_le_mul (le_max_left _ _) hrpow_ge1 zero_le_one (by positivity)
    · have ht_gt : 2 < |t| := lt_of_not_ge ht2
      have ht2_ge1' : 1 ≤ |1 / 2 * t| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith
      have hneg_ge1 : 1 ≤ |-1 / 2 * t| := by
        simpa [neg_div, abs_neg] using ht2_ge1'
      have hσ1_mem : (1 + δ + (κ : ℝ)) / 2 ∈ Set.Icc (-1 / 2 : ℝ) 2 := by
        have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
        have hκ1 : (κ : ℝ) ≤ 1 := Nat.cast_le.mpr hκ
        constructor <;> linarith
      have hσ2_mem : (-δ + (κ : ℝ)) / 2 ∈ Set.Icc (-1 / 2 : ℝ) 2 := by
        have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
        have hκ1 : (κ : ℝ) ≤ 1 := Nat.cast_le.mpr hκ
        constructor <;> linarith
      have hgam1 := hst hσ1_mem hneg_ge1
      have hgam2 := hst hσ2_mem ht2_ge1'
      have habs_eq : |-1 / 2 * t| = |1 / 2 * t| := by
        rw [← abs_neg (1 / 2 * t)]
        congr 1; ring
      rw [habs_eq] at hgam1
      have hden_pos : 0 < c_γ * Real.exp (-(Real.pi / 2) * |1 / 2 * t|) *
          |1 / 2 * t| ^ ((-δ + (κ : ℝ)) / 2 - 1 / 2) := by positivity
      have hgam_div :
          ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
            ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖ ≤
            (C_γ / c_γ) * |1 / 2 * t| ^ (1 / 2 + δ) := by
        have hexp_diff :
            |1 / 2 * t| ^ ((1 + δ + (κ : ℝ)) / 2 - 1 / 2) /
              |1 / 2 * t| ^ ((-δ + (κ : ℝ)) / 2 - 1 / 2) =
              |1 / 2 * t| ^ (1 / 2 + δ) := by
          rw [← Real.rpow_sub (by linarith)]
          congr 1; ring
        calc
          ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
              ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖
              ≤ (C_γ * Real.exp (-(Real.pi / 2) * |1 / 2 * t|) *
                    |1 / 2 * t| ^ ((1 + δ + (κ : ℝ)) / 2 - 1 / 2)) /
                  (c_γ * Real.exp (-(Real.pi / 2) * |1 / 2 * t|) *
                    |1 / 2 * t| ^ ((-δ + (κ : ℝ)) / 2 - 1 / 2)) :=
                div_le_div₀ (by positivity) hgam1.2 hden_pos hgam2.1
          _ = (C_γ / c_γ) *
                (|1 / 2 * t| ^ ((1 + δ + (κ : ℝ)) / 2 - 1 / 2) /
                  |1 / 2 * t| ^ ((-δ + (κ : ℝ)) / 2 - 1 / 2)) := by
                have hexp_ne : Real.exp (-(Real.pi / 2) * |1 / 2 * t|) ≠ 0 := Real.exp_ne_zero _
                field_simp [hexp_ne, hc_pos.ne']
          _ = (C_γ / c_γ) * |1 / 2 * t| ^ (1 / 2 + δ) := by rw [hexp_diff]
      have hcmp : |1 / 2 * t| ^ (1 / 2 + δ) ≤ (|t| + 2) ^ (1 / 2 + δ) := by
        refine Real.rpow_le_rpow (abs_nonneg _) ?_ (by linarith)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith [abs_nonneg t]
      calc
        ‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
            ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖
            ≤ (C_γ / c_γ) * |1 / 2 * t| ^ (1 / 2 + δ) := hgam_div
        _ ≤ M_Γ * (|t| + 2) ^ (1 / 2 + δ) :=
            mul_le_mul (le_max_right _ _) hcmp (by positivity) (by positivity)
  calc
    (Real.pi ^ (-(1 + δ + (κ : ℝ)) / 2) / Real.pi ^ (-(-δ + (κ : ℝ)) / 2)) *
        (‖Complex.Gamma (((1 + δ + (κ : ℝ)) / 2 : ℝ) + ((-1 / 2 * t : ℝ) : ℂ) * I)‖ /
          ‖Complex.Gamma (((-δ + (κ : ℝ)) / 2 : ℝ) + ((1 / 2 * t : ℝ) : ℂ) * I)‖)
        ≤ 1 * (M_Γ * (|t| + 2) ^ (1 / 2 + δ)) :=
          mul_le_mul hpi_ratio hgam_le (by positivity) zero_le_one
    _ = M_Γ * (|t| + 2) ^ (1 / 2 + δ) := one_mul _

/-- **Convexity strip bound for primitive Dirichlet L-functions**:
for any `0 < δ ≤ 1/4`, there exists `C > 0` depending only on `δ` such that for every
`q ≥ 2`, every primitive character `χ` modulo `q`, every `σ ∈ [-δ, 1 + δ]`, and every `t : ℝ`,
`‖LFunction χ (σ + t * I)‖ ≤ C * (q * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2)`. -/
theorem norm_LFunction_primitive_convexity_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {χ : DirichletCharacter ℂ q}, χ.IsPrimitive →
        ∀ {σ t : ℝ}, σ ∈ Set.Icc (-δ) (1 + δ) →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
            C * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2) := by
  obtain ⟨m₁, M₁, hm₁_pos, hrad⟩ := norm_rademacherWeight_strip_bounds hδ0 hδ1
  obtain ⟨M_Γ, hM_Γ_pos, hgam_rat⟩ := gammaFactor_funcEq_ratio_bound hδ0 hδ1
  have hM₁_pos : 0 < M₁ := by
    have h := (hrad (σ := 0) (t := 0) ⟨by linarith, by linarith⟩)
    have h0 : 0 < m₁ * (|(0 : ℝ)| + 2) ^ ((0 - 1 - δ) / 2) := by positivity
    exact pos_of_mul_pos_left (h0.trans_le (h.1.trans h.2)) (by positivity)
  let C_H : ℝ := max ((1 + 1 / δ) * M₁) (M_Γ * (1 + 1 / δ) * M₁)
  have hC_H_pos : 0 < C_H := by positivity
  refine ⟨C_H / m₁, by positivity, ?_⟩
  intro q _ hq χ hprim σ t hσ
  have hχ_ne1 : χ ≠ 1 := by
    intro h1
    have hc : χ.conductor = 1 := h1 ▸ DirichletCharacter.conductor_one
    rw [DirichletCharacter.IsPrimitive, hc] at hprim
    omega
  let H : ℂ → ℂ := fun s ↦
    DirichletCharacter.LFunction χ s * (q : ℂ) ^ ((s - (1 + (δ : ℂ))) / 2) * rademacherWeight δ s
  have hH_diff_open : DifferentiableOn ℂ H {s : ℂ | -1 < s.re ∧ s.re < 2} := by
    have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | -1 < s.re ∧ s.re < 2} :=
      (differentiable_LFunction_of_ne_one hχ_ne1).differentiableOn
    have hq_diff : DifferentiableOn ℂ (fun s : ℂ ↦ (q : ℂ) ^ ((s - (1 + (δ : ℂ))) / 2))
        {s : ℂ | -1 < s.re ∧ s.re < 2} := by
      have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      exact (Differentiable.const_cpow (by fun_prop) (Or.inl hq_ne)).differentiableOn
    exact (hL.mul hq_diff).mul (rademacherWeight_differentiableOn hδ0 hδ1)
  have hsub_open : verticalStripOpen (-δ) (1 + δ) ⊆ {s : ℂ | -1 < s.re ∧ s.re < 2} := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  have hsub_closed : verticalStripClosed (-δ) (1 + δ) ⊆ {s : ℂ | -1 < s.re ∧ s.re < 2} := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  have hclosed : IsClosed (verticalStripClosed (-δ) (1 + δ)) :=
    isClosed_Icc.preimage Complex.continuous_re
  have hclos_sub : closure (verticalStripOpen (-δ) (1 + δ)) ⊆ {s : ℂ | -1 < s.re ∧ s.re < 2} :=
    (hclosed.closure_subset_iff.mpr fun _ hz ↦ Set.Ioo_subset_Icc_self hz).trans hsub_closed
  have hH_diffCont : DiffContOnCl ℂ H (verticalStripOpen (-δ) (1 + δ)) :=
    ⟨hH_diff_open.mono hsub_open, hH_diff_open.continuousOn.mono hclos_sub⟩
  have hA : 0 ≤ (q + 48 * (q : ℝ) ^ 2) * M₁ := by positivity
  have hbound : ∀ z ∈ verticalStripOpen (-δ) (1 + δ),
      ‖H z‖ ≤ (q + 48 * (q : ℝ) ^ 2) * M₁ * Real.exp (2 * (|z.im| + 2) ^ (1 : ℝ)) := by
    intro z hz
    have hL_poly := norm_LFunction_strip_poly_le hχ_ne1
      (by linarith [hz.1] : -(1 / 2 : ℝ) ≤ z.re) (by linarith [hz.2] : z.re ≤ 2)
    have hq_posR : (0 : ℝ) < q := by positivity
    have hq_norm : ‖(q : ℂ) ^ ((z - (1 + (δ : ℂ))) / 2)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq_posR]
      have hre : ((z - (1 + (δ : ℂ))) / 2).re = (z.re - 1 - δ) / 2 := by simp; ring
      rw [hre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ q))
        (by linarith [hz.2])
    have hz_mem : z.re ∈ Set.Icc (-δ) (1 + δ) := ⟨hz.1.le, hz.2.le⟩
    have hrad_hi : ‖rademacherWeight δ z‖ ≤ M₁ := by
      have hz_split : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
      rw [hz_split]
      have h := (hrad (σ := z.re) (t := z.im) hz_mem).2
      have hrpow1 : (|z.im| + 2) ^ ((z.re - 1 - δ) / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z.im]) (by linarith [hz.2])
      calc
        ‖rademacherWeight δ ((z.re : ℂ) + (z.im : ℂ) * I)‖
            ≤ M₁ * (|z.im| + 2) ^ ((z.re - 1 - δ) / 2) := h
        _ ≤ M₁ * 1 := mul_le_mul_of_nonneg_left hrpow1 hM₁_pos.le
        _ = M₁ := mul_one _
    have hexp2 : (|z.im| + 2) ^ (2 : ℕ) ≤ Real.exp (2 * (|z.im| + 2) ^ (1 : ℝ)) := by
      simpa using rpow_le_exp_of_nonneg (x := |z.im| + 2) (B := 2)
        (by linarith [abs_nonneg z.im]) (by norm_num)
    calc
      ‖H z‖ = ‖DirichletCharacter.LFunction χ z‖ *
          ‖(q : ℂ) ^ ((z - (1 + (δ : ℂ))) / 2)‖ * ‖rademacherWeight δ z‖ := by
            simp only [H, norm_mul]
      _ ≤ ((q + 48 * (q : ℝ) ^ 2) * (|z.im| + 2) ^ 2) * 1 * M₁ := by
            refine mul_le_mul (mul_le_mul hL_poly hq_norm (norm_nonneg _) (by positivity))
              hrad_hi (norm_nonneg _) (by positivity)
      _ ≤ (q + 48 * (q : ℝ) ^ 2) * M₁ * Real.exp (2 * (|z.im| + 2) ^ (1 : ℝ)) := by
            nlinarith [hexp2, show 0 ≤ (q + 48 * (q : ℝ) ^ 2) * M₁ by positivity]
  have hle_right : ∀ u : ℝ, ‖H (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ C_H := by
    intro u
    have hre_gt : 1 < (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I).re := by simp; linarith
    have hL_le := norm_LSeries_le_one_add_inv χ hre_gt
    have hre_eq : (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I).re - 1 = δ := by simp
    rw [hre_eq] at hL_le
    have hq_norm : ‖(q : ℂ) ^ (((((1 + δ : ℝ) : ℂ) + (u : ℂ) * I) - (1 + (δ : ℂ))) / 2)‖ = 1 := by
      have hq_posR : (0 : ℝ) < q := by positivity
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq_posR]
      have h0 : (((((1 + δ : ℝ) : ℂ) + (u : ℂ) * I) - (1 + (δ : ℂ))) / 2).re = 0 := by simp
      rw [h0, Real.rpow_zero]
    have hrad_le : ‖rademacherWeight δ (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ M₁ := by
      have h := (hrad (σ := 1 + δ) (t := u) ⟨by linarith, le_rfl⟩).2
      simpa using h
    calc
      ‖H (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I)‖
          = ‖DirichletCharacter.LFunction χ (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I)‖ *
              ‖(q : ℂ) ^ (((((1 + δ : ℝ) : ℂ) + (u : ℂ) * I) - (1 + (δ : ℂ))) / 2)‖ *
              ‖rademacherWeight δ (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
            simp only [H, norm_mul]
      _ ≤ (1 + 1 / δ) * 1 * M₁ :=
            mul_le_mul (mul_le_mul hL_le hq_norm.le (norm_nonneg _) (by positivity))
              hrad_le (norm_nonneg _) (by positivity)
      _ = (1 + 1 / δ) * M₁ := by ring
      _ ≤ C_H := le_max_left _ _
  have hle_left : ∀ u : ℝ, ‖H (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ C_H := by
    intro u
    let w : ℂ := ((1 + δ : ℝ) : ℂ) - (u : ℂ) * I
    have h1w : 1 - w = ((-δ : ℝ) : ℂ) + (u : ℂ) * I := by
      dsimp only [w]; push_cast; ring
    have hw_re : w.re = 1 + δ := by simp [w]
    have h1w_re : (1 - w).re = -δ := by rw [h1w]; simp
    have hgam2_ne : DirichletCharacter.gammaFactor (star χ) w ≠ 0 := by
      rw [gammaFactor_eq_Gammaℝ]
      refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
      rw [add_re, hw_re, natCast_re]
      positivity
    have hfe := LFunction_one_sub_primitive hprim (Or.inr (by omega)) (Or.inr (by omega)) hgam2_ne
    rw [h1w] at hfe
    have hgam_ratio :
        ‖DirichletCharacter.gammaFactor (star χ) w‖ /
          ‖DirichletCharacter.gammaFactor χ (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
          M_Γ * (|u| + 2) ^ (1 / 2 + δ) := by
      rw [gammaFactor_eq_Gammaℝ, gammaFactor_eq_Gammaℝ, parityExp_star]
      have hpar_le : parityExp χ ≤ 1 := by
        rcases χ.even_or_odd with hev | hodd
        · rw [parityExp_of_even hev]; omega
        · rw [parityExp_of_odd hodd]
      have heq1 : w + (parityExp χ : ℂ) =
          1 + (δ : ℂ) - (u : ℂ) * I + ((parityExp χ : ℕ) : ℂ) := by
        dsimp only [w]; push_cast; ring
      have heq2 : ((-δ : ℝ) : ℂ) + (u : ℂ) * I + (parityExp χ : ℂ) =
          -(δ : ℂ) + (u : ℂ) * I + ((parityExp χ : ℕ) : ℂ) := by
        push_cast; ring
      rw [heq1, heq2]
      exact hgam_rat (parityExp χ) hpar_le u
    have hL_w : ‖DirichletCharacter.LFunction (star χ) w‖ ≤ 1 + 1 / δ := by
      have h := norm_LSeries_le_one_add_inv (star χ) (by rw [hw_re]; linarith)
      rwa [hw_re, add_sub_cancel_left] at h
    have hq_posR : (0 : ℝ) < q := by positivity
    have hq_fe : ‖(q : ℂ) ^ (w - 1 / 2)‖ = (q : ℝ) ^ (1 / 2 + δ) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq_posR]
      have hre : (w - 1 / 2).re = 1 / 2 + δ := by rw [sub_re, hw_re]; norm_num; ring
      rw [hre]
    have hL_left :
        ‖DirichletCharacter.LFunction χ (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
          M_Γ * (1 + 1 / δ) * (q : ℝ) ^ (1 / 2 + δ) * (|u| + 2) ^ (1 / 2 + δ) := by
      rw [hfe, norm_mul, norm_mul, norm_mul, norm_div, hq_fe, norm_rootNumber_primitive hprim, mul_one]
      calc
        (q : ℝ) ^ (1 / 2 + δ) *
            (‖DirichletCharacter.gammaFactor (star χ) w‖ /
              ‖DirichletCharacter.gammaFactor χ (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖) *
            ‖DirichletCharacter.LFunction (star χ) w‖
            ≤ (q : ℝ) ^ (1 / 2 + δ) * (M_Γ * (|u| + 2) ^ (1 / 2 + δ)) * (1 + 1 / δ) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hgam_ratio (by positivity))
                hL_w (norm_nonneg _) (by positivity)
        _ = M_Γ * (1 + 1 / δ) * (q : ℝ) ^ (1 / 2 + δ) * (|u| + 2) ^ (1 / 2 + δ) := by ring
    have hq_weight :
        ‖(q : ℂ) ^ (((((-δ : ℝ) : ℂ) + (u : ℂ) * I) - (1 + (δ : ℂ))) / 2)‖ =
          (q : ℝ) ^ (-(1 / 2 + δ)) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq_posR]
      congr 1; simp; ring
    have hrad_left :
        ‖rademacherWeight δ (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
          M₁ * (|u| + 2) ^ (-(1 / 2 + δ)) := by
      have h := (hrad (σ := -δ) (t := u) ⟨le_rfl, by linarith⟩).2
      convert h using 2
      ring
    have hq_cancel : (q : ℝ) ^ (1 / 2 + δ) * (q : ℝ) ^ (-(1 / 2 + δ)) = 1 := by
      rw [← Real.rpow_add hq_posR, add_neg_cancel, Real.rpow_zero]
    have hu_cancel : (|u| + 2) ^ (1 / 2 + δ) * (|u| + 2) ^ (-(1 / 2 + δ)) = 1 := by
      rw [← Real.rpow_add (by positivity : 0 < |u| + 2), add_neg_cancel, Real.rpow_zero]
    calc
      ‖H (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖
          = ‖DirichletCharacter.LFunction χ (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖ *
              ‖(q : ℂ) ^ (((((-δ : ℝ) : ℂ) + (u : ℂ) * I) - (1 + (δ : ℂ))) / 2)‖ *
              ‖rademacherWeight δ (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
            simp only [H, norm_mul]
      _ ≤ (M_Γ * (1 + 1 / δ) * (q : ℝ) ^ (1 / 2 + δ) * (|u| + 2) ^ (1 / 2 + δ)) *
              (q : ℝ) ^ (-(1 / 2 + δ)) * (M₁ * (|u| + 2) ^ (-(1 / 2 + δ))) := by
            rw [hq_weight]
            refine mul_le_mul (mul_le_mul_of_nonneg_right hL_left (by positivity))
              hrad_left (norm_nonneg _) (by positivity)
      _ = M_Γ * (1 + 1 / δ) * M₁ *
            ((q : ℝ) ^ (1 / 2 + δ) * (q : ℝ) ^ (-(1 / 2 + δ))) *
            ((|u| + 2) ^ (1 / 2 + δ) * (|u| + 2) ^ (-(1 / 2 + δ))) := by ring
      _ = M_Γ * (1 + 1 / δ) * M₁ := by rw [hq_cancel, hu_cancel]; ring
      _ ≤ C_H := le_max_right _ _
  have hPL := phragmen_lindelof_vertical_strip_of_exp_rpow_le (σ₁ := -δ) (σ₂ := 1 + δ)
    (by linarith) hH_diffCont hA hbound hle_left hle_right
    (z := (σ : ℂ) + (t : ℂ) * I) ⟨by simpa using hσ.1, by simpa using hσ.2⟩
  have hq_posR : (0 : ℝ) < q := by positivity
  have hq_mid :
      ‖(q : ℂ) ^ ((((σ : ℂ) + (t : ℂ) * I) - (1 + (δ : ℂ))) / 2)‖ =
        (q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq_posR]
    congr 1; simp; ring
  have hrad_mid := (hrad (σ := σ) (t := t) hσ).1
  have hexp_eq : -((1 - σ) / 2 + δ / 2) = (σ - 1 - δ) / 2 := by ring
  rw [← hexp_eq] at hrad_mid
  have hwt_pos : 0 < m₁ * (q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) *
      (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)) := by positivity
  have hL_mul :
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ *
          (m₁ * (q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2))) ≤
        C_H := by
    calc
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ *
          (m₁ * (q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)))
          = ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ *
              ((q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) *
                (m₁ * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)))) := by ring
      _ ≤ ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ *
            ((q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) *
              ‖rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrad_mid (by positivity))
            (norm_nonneg _)
      _ = ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ *
            ‖(q : ℂ) ^ ((((σ : ℂ) + (t : ℂ) * I) - (1 + (δ : ℂ))) / 2)‖ *
            ‖rademacherWeight δ ((σ : ℂ) + (t : ℂ) * I)‖ := by rw [hq_mid]; ring
      _ = ‖H ((σ : ℂ) + (t : ℂ) * I)‖ := by simp only [H, norm_mul]
      _ ≤ C_H := hPL
  have hinv_eq :
      (m₁ * (q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)))⁻¹ =
        (1 / m₁) * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2) := by
    rw [Real.mul_rpow hq_posR.le (by positivity), Real.rpow_neg hq_posR.le,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ |t| + 2)]
    field_simp [hm₁_pos.ne']
  calc
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C_H / (m₁ * (q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2))) :=
          (le_div_iff₀ hwt_pos).mpr hL_mul
    _ = C_H * (m₁ * (q : ℝ) ^ (-((1 - σ) / 2 + δ / 2)) * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)))⁻¹ :=
          div_eq_mul_inv _ _
    _ = (C_H / m₁) * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2) := by
          rw [hinv_eq]; ring

/-- **Uniform convexity strip bound for arbitrary non-principal Dirichlet L-functions**:
for any `ε > 0`, there exists `C > 0` depending only on `ε` such that for every `q ≥ 2`,
every non-principal character `χ ≠ 1` modulo `q`, every `σ ∈ [0, 1]`, and every `t : ℝ`,
`‖LFunction χ (σ + t * I)‖ ≤ C * (q * (|t| + 2)) ^ ((1 - σ) / 2 + ε)`. -/
theorem norm_LFunction_ne_one_convexity_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
        ∀ {σ t : ℝ}, σ ∈ Set.Icc (0 : ℝ) 1 →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
            C * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + ε) := by
  let δ := min (ε / 2) (1 / 4)
  have hδ0 : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδ_le_ε : δ ≤ ε / 2 := min_le_left _ _
  let η := δ / 2
  have hη : 0 < η := half_pos hδ0
  obtain ⟨C₀, hC₀_pos, hprim⟩ := norm_LFunction_primitive_convexity_bound hδ0 hδ1
  let K : ℝ := (2 : ℝ) ^ (Nat.ceil ((2 : ℝ) ^ (1 / η)))
  refine ⟨C₀ * K, by positivity, ?_⟩
  intro q _ hq χ hχ σ t hσ
  let d := χ.conductor
  have hd_pos : 0 < d := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have : NeZero d := ⟨hd_pos.ne'⟩
  have hd_dvd : d ∣ q := χ.conductor_dvd_level
  have hd_le_q : d ≤ q := Nat.le_of_dvd (by omega) hd_dvd
  have hd2 : 2 ≤ d := by
    by_contra hlt
    have hd1 : d = 1 := by omega
    exact hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd1)
  let χs := χ.primitiveCharacter
  have hχs_prim : χs.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hχs_ne1 : χs ≠ 1 := by
    intro h1
    have hc : χs.conductor = 1 := h1 ▸ DirichletCharacter.conductor_one
    have hp : χs.conductor = d := hχs_prim
    omega
  have hchg := DirichletCharacter.LFunction_changeLevel hd_dvd χs
    (s := (σ : ℂ) + (t : ℂ) * I) (Or.inl hχs_ne1)
  rw [χ.changeLevel_primitiveCharacter] at hchg
  have hprod_le : ‖∏ p ∈ q.primeFactors, (1 - χs p * (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))‖ ≤
      (2 : ℝ) ^ q.primeFactors.card :=
    prod_euler_factor_norm_le q (fun p ↦ χs p) (fun p ↦ χs.norm_le_one _) hσ.1
  have htwo_le := prod_two_le_rpow hη q (by omega)
  have hprim_bd := hprim hd2 hχs_prim (σ := σ) (t := t) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hd_rpow : ((d : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2) ≤
      ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2) :=
    Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd_le_q) (by positivity))
      (by linarith [hσ.2])
  have hq_η : (q : ℝ) ^ η ≤ ((q : ℝ) * (|t| + 2)) ^ η :=
    Real.rpow_le_rpow (by positivity)
      (le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg t])) hη.le
  have hexp_sum : ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2) * ((q : ℝ) * (|t| + 2)) ^ η =
      ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1; dsimp only [η]; ring
  have hexp_le : ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ) ≤
      ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + ε) := by
    refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [abs_nonneg t]
  rw [hchg, norm_mul]
  calc
    ‖DirichletCharacter.LFunction χs ((σ : ℂ) + (t : ℂ) * I)‖ *
        ‖∏ p ∈ q.primeFactors, (1 - χs p * (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))‖
        ≤ (C₀ * ((d : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2)) * (K * (q : ℝ) ^ η) :=
          mul_le_mul hprim_bd (hprod_le.trans htwo_le) (norm_nonneg _) (by positivity)
    _ ≤ (C₀ * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2)) * (K * ((q : ℝ) * (|t| + 2)) ^ η) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hd_rpow hC₀_pos.le)
            (mul_le_mul_of_nonneg_left hq_η (by positivity)) (by positivity) (by positivity)
    _ = C₀ * K * (((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ / 2) * ((q : ℝ) * (|t| + 2)) ^ η) := by
          ring
    _ = C₀ * K * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + δ) := by rw [hexp_sum]
    _ ≤ C₀ * K * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + ε) :=
          mul_le_mul_of_nonneg_left hexp_le (by positivity)

/-- **Convexity strip bound for the Riemann zeta function**:
for any `ε > 0`, there exists `C > 0` depending only on `ε` such that for all `σ ∈ [0, 1]` and
all `t : ℝ` with `1 ≤ |t|`, `‖riemannZeta (σ + t * I)‖ ≤ C * (|t| + 2) ^ ((1 - σ) / 2 + ε)`. -/
theorem norm_riemannZeta_convexity_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {σ t : ℝ}, σ ∈ Set.Icc (0 : ℝ) 1 → 1 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ ((1 - σ) / 2 + ε) := by
  let δ := min ε (1 / 4)
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδ_le : δ ≤ ε := min_le_left _ _
  obtain ⟨m₁, M₁, hm₁_pos, hrad⟩ := norm_rademacherWeight_strip_bounds hδ0 hδ1
  obtain ⟨M_Γ, hM_Γ_pos, hgam_rat⟩ := gammaFactor_funcEq_ratio_bound hδ0 hδ1
  have hM₁_pos : 0 < M₁ := by
    have h := hrad (σ := 0) (t := 0) ⟨by linarith, by linarith⟩
    have h0 : 0 < m₁ * (|(0 : ℝ)| + 2) ^ ((0 - 1 - δ) / 2) := by positivity
    exact pos_of_mul_pos_left (h0.trans_le (h.1.trans h.2)) (by positivity)
  let H : ℂ → ℂ := fun s ↦ (riemannZeta₁ s / (s + 3)) * rademacherWeight δ s
  have hH_diff_open : DifferentiableOn ℂ H {s : ℂ | -1 < s.re ∧ s.re < 2} := by
    have hz1 : DifferentiableOn ℂ riemannZeta₁ {s : ℂ | -1 < s.re ∧ s.re < 2} :=
      differentiable_riemannZeta₁.differentiableOn
    have hden : ∀ s ∈ ({s : ℂ | -1 < s.re ∧ s.re < 2} : Set ℂ), s + 3 ≠ 0 := by
      intro s hs h0
      have := congrArg Complex.re h0
      simp at this
      linarith [hs.1]
    have hdiv : DifferentiableOn ℂ (fun s ↦ riemannZeta₁ s / (s + 3))
        {s : ℂ | -1 < s.re ∧ s.re < 2} :=
      hz1.div (differentiable_id.add_const 3).differentiableOn hden
    exact hdiv.mul (rademacherWeight_differentiableOn hδ0 hδ1)
  have hsub_open : verticalStripOpen (-δ) (1 + δ) ⊆ {s : ℂ | -1 < s.re ∧ s.re < 2} := by
    intro z hz; constructor <;> linarith [hz.1, hz.2]
  have hsub_closed : verticalStripClosed (-δ) (1 + δ) ⊆ {s : ℂ | -1 < s.re ∧ s.re < 2} := by
    intro z hz; constructor <;> linarith [hz.1, hz.2]
  have hclosed : IsClosed (verticalStripClosed (-δ) (1 + δ)) :=
    isClosed_Icc.preimage Complex.continuous_re
  have hclos_sub : closure (verticalStripOpen (-δ) (1 + δ)) ⊆ {s : ℂ | -1 < s.re ∧ s.re < 2} :=
    (hclosed.closure_subset_iff.mpr fun _ hz ↦ Set.Ioo_subset_Icc_self hz).trans hsub_closed
  have hH_diffCont : DiffContOnCl ℂ H (verticalStripOpen (-δ) (1 + δ)) :=
    ⟨hH_diff_open.mono hsub_open, hH_diff_open.continuousOn.mono hclos_sub⟩
  have hbound : ∀ z ∈ verticalStripOpen (-δ) (1 + δ),
      ‖H z‖ ≤ (10 * M₁) * Real.exp (3 * (|z.im| + 2) ^ (1 : ℝ)) := by
    intro z hz
    have hpoly := norm_riemannZeta₁_strip_poly_le
      (by linarith [hz.1] : -(1 / 2 : ℝ) ≤ z.re) (by linarith [hz.2] : z.re ≤ 2)
    have hz3_ge1 : 1 ≤ ‖z + 3‖ := by
      have hre : 1 ≤ (z + 3).re := by simp; linarith [hz.1]
      exact hre.trans (Complex.re_le_norm _)
    have hdiv_le : ‖riemannZeta₁ z / (z + 3)‖ ≤ ‖riemannZeta₁ z‖ := by
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hz3_ge1
    have hz_mem : z.re ∈ Set.Icc (-δ) (1 + δ) := ⟨hz.1.le, hz.2.le⟩
    have hrad_hi : ‖rademacherWeight δ z‖ ≤ M₁ := by
      have hz_split : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
      rw [hz_split]
      have h := (hrad (σ := z.re) (t := z.im) hz_mem).2
      have hrpow1 : (|z.im| + 2) ^ ((z.re - 1 - δ) / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z.im]) (by linarith [hz.2])
      calc
        ‖rademacherWeight δ ((z.re : ℂ) + (z.im : ℂ) * I)‖
            ≤ M₁ * (|z.im| + 2) ^ ((z.re - 1 - δ) / 2) := h
        _ ≤ M₁ * 1 := mul_le_mul_of_nonneg_left hrpow1 hM₁_pos.le
        _ = M₁ := mul_one _
    have hexp3 : (|z.im| + 2) ^ (3 : ℕ) ≤ Real.exp (3 * (|z.im| + 2) ^ (1 : ℝ)) := by
      simpa using rpow_le_exp_of_nonneg (x := |z.im| + 2) (B := 3)
        (by linarith [abs_nonneg z.im]) (by norm_num)
    calc
      ‖H z‖ = ‖riemannZeta₁ z / (z + 3)‖ * ‖rademacherWeight δ z‖ := by simp only [H, norm_mul]
      _ ≤ (10 * (|z.im| + 2) ^ 3) * M₁ := mul_le_mul (hdiv_le.trans hpoly) hrad_hi (norm_nonneg _) (by positivity)
      _ ≤ (10 * M₁) * Real.exp (3 * (|z.im| + 2) ^ (1 : ℝ)) := by
          nlinarith [hexp3, show 0 ≤ 10 * M₁ by positivity]
  let C_H : ℝ := max ((1 + 1 / δ) * M₁) (M_Γ * (1 + 1 / δ) * M₁)
  have hC_H_pos : 0 < C_H := by positivity
  have hratio_edge : ∀ {s : ℂ}, -δ ≤ s.re → s.re ≤ 1 + δ → ‖(s - 1) / (s + 3)‖ ≤ 1 := by
    intro s hs_lo hs_hi
    rw [norm_div, div_le_one (norm_pos_iff.mpr (by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith))]
    have hsq : ‖s - 1‖ ^ 2 ≤ ‖s + 3‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, Complex.normSq_apply]
      have hre1 : (s - 1).re = s.re - 1 := by simp
      have him1 : (s - 1).im = s.im := by simp
      have hre2 : (s + 3).re = s.re + 3 := by simp
      have him2 : (s + 3).im = s.im := by simp
      rw [hre1, him1, hre2, him2]
      nlinarith
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have hle_right : ∀ u : ℝ, ‖H (((1 + δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ C_H := by
    intro u
    let s : ℂ := ((1 + δ : ℝ) : ℂ) + (u : ℂ) * I
    have hs_ne1 : s ≠ 1 := by
      intro h0; have := congrArg Complex.re h0; simp [s] at this; linarith
    have hs_eq : riemannZeta₁ s / (s + 3) = ((s - 1) / (s + 3)) * riemannZeta s := by
      rw [riemannZeta_eq_inv_sub_mul hs_ne1]
      field_simp [sub_ne_zero.mpr hs_ne1]
    have hZ_le := norm_riemannZeta_le_one_add_inv (s := s) (by simp [s]; linarith)
    have hre_eq : s.re - 1 = δ := by simp [s]
    rw [hre_eq] at hZ_le
    have hrad_le : ‖rademacherWeight δ s‖ ≤ M₁ := by
      have h := (hrad (σ := 1 + δ) (t := u) ⟨by linarith, le_rfl⟩).2
      simpa [s] using h
    calc
      ‖H s‖ = ‖(s - 1) / (s + 3)‖ * ‖riemannZeta s‖ * ‖rademacherWeight δ s‖ := by
            simp only [H, hs_eq, norm_mul]
      _ ≤ 1 * (1 + 1 / δ) * M₁ :=
            mul_le_mul (mul_le_mul (hratio_edge (by simp [s]; linarith) (by simp [s]))
              hZ_le (norm_nonneg _) zero_le_one) hrad_le (norm_nonneg _) (by positivity)
      _ = (1 + 1 / δ) * M₁ := by ring
      _ ≤ C_H := le_max_left _ _
  have hle_left : ∀ u : ℝ, ‖H (((-δ : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ C_H := by
    intro u
    let s : ℂ := ((-δ : ℝ) : ℂ) + (u : ℂ) * I
    have hs_ne1 : s ≠ 1 := by
      intro h0; have := congrArg Complex.re h0; simp [s] at this; linarith
    have hs_ne0 : s ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp [s] at this; linarith
    have h1s_ne0 : 1 - s ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp [s] at this; linarith
    have hs_eq : riemannZeta₁ s / (s + 3) = ((s - 1) / (s + 3)) * riemannZeta s := by
      rw [riemannZeta_eq_inv_sub_mul hs_ne1]
      field_simp [sub_ne_zero.mpr hs_ne1]
    have hgam_ne : Complex.Gammaℝ s ≠ 0 := by
      intro h0
      rw [Complex.Gammaℝ_eq_zero_iff] at h0
      rcases h0 with ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp [s] at hre
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · simp at hre; linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
        linarith
    have hfe_zeta : riemannZeta s =
        (Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) * riemannZeta (1 - s) := by
      have h1 : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
        have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
          (1 : DirichletCharacter ℂ 1) s (Or.inl hs_ne0)
        rw [DirichletCharacter.LFunction_modOne_eq, DirichletCharacter.completedLFunction_modOne_eq,
          DirichletCharacter.even_one.gammaFactor_def] at h
        rw [h, div_mul_cancel₀ _ hgam_ne]
      have h2 : completedRiemannZeta (1 - s) = riemannZeta (1 - s) * Complex.Gammaℝ (1 - s) := by
        have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
          (1 : DirichletCharacter ℂ 1) (1 - s) (Or.inl h1s_ne0)
        rw [DirichletCharacter.LFunction_modOne_eq, DirichletCharacter.completedLFunction_modOne_eq,
          DirichletCharacter.even_one.gammaFactor_def] at h
        have hg1s : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s]; linarith)
        rw [h, div_mul_cancel₀ _ hg1s]
      have hcomp : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
        (completedRiemannZeta_one_sub s).symm
      rw [h1, h2] at hcomp
      rw [div_mul_eq_mul_div, eq_div_iff hgam_ne]
      exact hcomp.trans (mul_comm _ _)
    have hgam_ratio : ‖Complex.Gammaℝ (1 - s)‖ / ‖Complex.Gammaℝ s‖ ≤
        M_Γ * (|u| + 2) ^ (1 / 2 + δ) := by
      have heq1 : 1 - s = 1 + (δ : ℂ) - (u : ℂ) * I + ((0 : ℕ) : ℂ) := by
        dsimp only [s]; push_cast; ring
      have heq2 : s = -(δ : ℂ) + (u : ℂ) * I + ((0 : ℕ) : ℂ) := by
        dsimp only [s]; push_cast; ring
      rw [heq1, heq2]
      exact hgam_rat 0 (by omega) u
    have hZ_1s : ‖riemannZeta (1 - s)‖ ≤ 1 + 1 / δ := by
      have h := norm_riemannZeta_le_one_add_inv (s := 1 - s) (by simp [s]; linarith)
      have hre_eq : (1 - s).re - 1 = δ := by simp [s]
      rwa [hre_eq] at h
    have hrad_le : ‖rademacherWeight δ s‖ ≤ M₁ * (|u| + 2) ^ (-(1 / 2 + δ)) := by
      have h := (hrad (σ := -δ) (t := u) ⟨le_rfl, by linarith⟩).2
      convert h using 2
      ring
    have hu_cancel : (|u| + 2) ^ (1 / 2 + δ) * (|u| + 2) ^ (-(1 / 2 + δ)) = 1 := by
      rw [← Real.rpow_add (by positivity : 0 < |u| + 2), add_neg_cancel, Real.rpow_zero]
    calc
      ‖H s‖ = ‖(s - 1) / (s + 3)‖ * (‖Complex.Gammaℝ (1 - s)‖ / ‖Complex.Gammaℝ s‖ *
            ‖riemannZeta (1 - s)‖) * ‖rademacherWeight δ s‖ := by
            simp only [H, hs_eq, hfe_zeta, norm_mul, norm_div]
      _ ≤ 1 * (M_Γ * (|u| + 2) ^ (1 / 2 + δ) * (1 + 1 / δ)) *
            (M₁ * (|u| + 2) ^ (-(1 / 2 + δ))) :=
          mul_le_mul (mul_le_mul (hratio_edge (by simp [s]) (by simp [s]; linarith))
            (mul_le_mul hgam_ratio hZ_1s (norm_nonneg _) (by positivity))
            (by positivity) zero_le_one) hrad_le (norm_nonneg _) (by positivity)
      _ = M_Γ * (1 + 1 / δ) * M₁ * ((|u| + 2) ^ (1 / 2 + δ) * (|u| + 2) ^ (-(1 / 2 + δ))) := by
          ring
      _ = M_Γ * (1 + 1 / δ) * M₁ := by rw [hu_cancel, mul_one]
      _ ≤ C_H := le_max_right _ _
  refine ⟨5 * C_H / m₁, by positivity, ?_⟩
  intro σ t hσ ht
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hPL := phragmen_lindelof_vertical_strip_of_exp_rpow_le (σ₁ := -δ) (σ₂ := 1 + δ)
    (by linarith) hH_diffCont (by positivity) hbound hle_left hle_right
    (z := s) ⟨by simpa [s] using by linarith [hσ.1], by simpa [s] using by linarith [hσ.2]⟩
  have hs_ne1 : s ≠ 1 := by
    intro h0
    have him := congrArg Complex.im h0
    simp [s] at him
    norm_num [him] at ht
  have hs3_ne0 : s + 3 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [s] at this; linarith [hσ.1]
  have hs_inv : ‖(s + 3) / (s - 1)‖ ≤ 5 := by
    have hsm1_ge : 1 ≤ ‖s - 1‖ := by
      have him : |(s - 1).im| = |t| := by simp [s]
      exact ht.trans (him ▸ Complex.abs_im_le_norm (s - 1))
    have hdiv_eq : (s + 3) / (s - 1) = 1 + 4 / (s - 1) := by
      have hne := sub_ne_zero.mpr hs_ne1
      field_simp [hne]
      ring
    rw [hdiv_eq]
    calc
      ‖1 + 4 / (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖(4 : ℂ) / (s - 1)‖ := norm_add_le _ _
      _ = 1 + 4 / ‖s - 1‖ := by rw [norm_one, norm_div, Complex.norm_ofNat]
      _ ≤ 1 + 4 / 1 := add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) zero_lt_one hsm1_ge)
      _ = 5 := by norm_num
  have hzeta_eq : riemannZeta s = ((s + 3) / (s - 1)) * (riemannZeta₁ s / (s + 3)) := by
    rw [riemannZeta_eq_inv_sub_mul hs_ne1]
    field_simp [sub_ne_zero.mpr hs_ne1, hs3_ne0]
  have hrad_mid := (hrad (σ := σ) (t := t) ⟨by linarith [hσ.1, hδ0], by linarith [hσ.2, hδ0]⟩).1
  have hexp_eq : -((1 - σ) / 2 + δ / 2) = (σ - 1 - δ) / 2 := by ring
  rw [← hexp_eq] at hrad_mid
  have hdiv_mid : ‖riemannZeta₁ s / (s + 3)‖ ≤ (C_H / m₁) * (|t| + 2) ^ ((1 - σ) / 2 + δ / 2) := by
    have hden_pos : 0 < m₁ * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)) := by positivity
    have hprod : ‖riemannZeta₁ s / (s + 3)‖ * (m₁ * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2))) ≤ C_H := by
      calc
        ‖riemannZeta₁ s / (s + 3)‖ * (m₁ * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)))
            ≤ ‖riemannZeta₁ s / (s + 3)‖ * ‖rademacherWeight δ s‖ :=
              mul_le_mul_of_nonneg_left hrad_mid (norm_nonneg _)
        _ = ‖H s‖ := (norm_mul _ _).symm
        _ ≤ C_H := hPL
    have hdiv := (le_div_iff₀ hden_pos).mpr hprod
    have hinv_eq : (m₁ * (|t| + 2) ^ (-((1 - σ) / 2 + δ / 2)))⁻¹ =
        (1 / m₁) * (|t| + 2) ^ ((1 - σ) / 2 + δ / 2) := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ |t| + 2)]
      field_simp [hm₁_pos.ne']
    rw [div_eq_mul_inv C_H, hinv_eq] at hdiv
    exact hdiv.trans_eq (by ring)
  have hexp_le : (|t| + 2) ^ ((1 - σ) / 2 + δ / 2) ≤ (|t| + 2) ^ ((1 - σ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
  calc
    ‖riemannZeta s‖ = ‖(s + 3) / (s - 1)‖ * ‖riemannZeta₁ s / (s + 3)‖ := by
          rw [hzeta_eq, norm_mul]
    _ ≤ 5 * ((C_H / m₁) * (|t| + 2) ^ ((1 - σ) / 2 + δ / 2)) :=
          mul_le_mul hs_inv hdiv_mid (norm_nonneg _) (by positivity)
    _ ≤ (5 * C_H / m₁) * (|t| + 2) ^ ((1 - σ) / 2 + ε) := by
          have := mul_le_mul_of_nonneg_left hexp_le (by positivity : 0 ≤ 5 * C_H / m₁)
          linarith [show 5 * ((C_H / m₁) * (|t| + 2) ^ ((1 - σ) / 2 + δ / 2)) =
            (5 * C_H / m₁) * (|t| + 2) ^ ((1 - σ) / 2 + δ / 2) by ring]

/-- **Unified convexity strip bound for all Dirichlet L-functions**:
for any `ε > 0`, there exists `C > 0` depending only on `ε` such that for all `q ≥ 1`,
all characters `χ` modulo `q`, all `σ ∈ [0, 1]`, and all `t : ℝ` satisfying `χ ≠ 1 ∨ 1 ≤ |t|`,
`‖LFunction χ (σ + t * I)‖ ≤ C * (q * (|t| + 2)) ^ ((1 - σ) / 2 + ε)`. -/
theorem norm_LFunction_convexity_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {σ t : ℝ},
        σ ∈ Set.Icc (0 : ℝ) 1 → (χ ≠ 1 ∨ 1 ≤ |t|) →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
            C * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + ε) := by
  obtain ⟨C₁, hC₁_pos, hne1⟩ := norm_LFunction_ne_one_convexity_bound hε
  obtain ⟨C₂, hC₂_pos, hzeta⟩ := norm_riemannZeta_convexity_bound (half_pos hε)
  let K : ℝ := (2 : ℝ) ^ (Nat.ceil ((2 : ℝ) ^ (1 / (ε / 2))))
  refine ⟨max C₁ (C₂ * K), by positivity, ?_⟩
  intro q _ χ σ t hσ hχt
  by_cases hχ : χ = 1
  · subst hχ
    have ht : 1 ≤ |t| := hχt.resolve_left (not_not.mpr rfl)
    have hs_ne1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h0
      have him := congrArg Complex.im h0
      simp at him
      norm_num [him] at ht
    rw [LFunction_one_eq_mul_riemannZeta hs_ne1, norm_mul]
    have hprod_le :
        ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))‖ ≤
          (2 : ℝ) ^ q.primeFactors.card := by
      simpa using prod_euler_factor_norm_le q (fun _ ↦ (1 : ℂ)) (fun _ ↦ by rw [norm_one]) hσ.1
    have htwo_le := prod_two_le_rpow (half_pos hε) q (NeZero.pos q)
    have hzeta_bd := hzeta hσ ht
    have hq_posR : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hq_rpow : (q : ℝ) ^ (ε / 2) ≤ (q : ℝ) ^ ((1 - σ) / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith [hσ.2])
    have ht_rpow : (|t| + 2) ^ ((1 - σ) / 2 + ε / 2) ≤ (|t| + 2) ^ ((1 - σ) / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
    calc
      ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))‖ *
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
          ≤ (K * (q : ℝ) ^ (ε / 2)) * (C₂ * (|t| + 2) ^ ((1 - σ) / 2 + ε / 2)) :=
            mul_le_mul (hprod_le.trans htwo_le) hzeta_bd (norm_nonneg _) (by positivity)
      _ ≤ (K * (q : ℝ) ^ ((1 - σ) / 2 + ε)) * (C₂ * (|t| + 2) ^ ((1 - σ) / 2 + ε)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hq_rpow (by positivity))
              (mul_le_mul_of_nonneg_left ht_rpow hC₂_pos.le) (by positivity) (by positivity)
      _ = (C₂ * K) * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + ε) := by
            rw [Real.mul_rpow hq_posR.le (by positivity)]
            ring
      _ ≤ max C₁ (C₂ * K) * ((q : ℝ) * (|t| + 2)) ^ ((1 - σ) / 2 + ε) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hq2 : 2 ≤ q := by
      rcases Nat.lt_trichotomy q 2 with hq1 | hq2 | hq2
      · have hq_eq : q = 1 := by have := NeZero.pos q; omega
        subst hq_eq
        exact absurd (DirichletCharacter.level_one χ) hχ
      · omega
      · omega
    exact (hne1 hq2 hχ hσ).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end ConvexityStripBounds

section ValueAtOneBound

/-- **Upper bound on `L(1, χ)`** for non-principal characters `χ ≠ 1` modulo `q`:
`‖LFunction χ 1‖ ≤ log q + 1`. -/
theorem norm_LFunction_one_le_log_add_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ Real.log (q : ℝ) + 1 := by
  have h1 := LFunction_eq_mul_integral_of_zero_lt_re hχ (s := (1 : ℂ)) (by simp)
  rw [h1, one_mul]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq_pos : (0 : ℝ) < q := by positivity
  let g : ℝ → ℂ := fun t ↦ partialCharSum χ ⌊t⌋₊ * (t : ℂ) ^ (-(1 : ℂ) - 1)
  have hg_meas : Measurable g :=
    ((measurable_from_top (f := fun n : ℕ ↦ partialCharSum χ n)).comp Nat.measurable_floor).mul
      (Complex.continuous_ofReal.measurable.pow_const (-(1 : ℂ) - 1))
  have hg_int_Ioi1 : IntegrableOn g (Set.Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) zero_lt_one).const_mul (q : ℝ)
      |>.mono' hg_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    dsimp only [g]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [sub_re, neg_re, one_re]
    have hre : (-(1 : ℝ) - 1) = (-2 : ℝ) := by norm_num
    rw [hre]
    exact mul_le_mul_of_nonneg_right (norm_partialCharSum_le hχ _) (Real.rpow_nonneg ht0.le _)
  have hsplit_set : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) (q : ℝ) ∪ Set.Ioi (q : ℝ) := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t q with htq | hqt
      · exact Or.inl ⟨ht, htq⟩
      · exact Or.inr hqt
    · rintro (⟨ht, _⟩ | hqt)
      · exact ht
      · exact lt_of_le_of_lt hq1 hqt
  have hint_left : IntegrableOn g (Set.Ioc (1 : ℝ) (q : ℝ)) :=
    hg_int_Ioi1.mono_set Set.Ioc_subset_Ioi_self
  have hint_right : IntegrableOn g (Set.Ioi (q : ℝ)) :=
    hg_int_Ioi1.mono_set (Set.Ioi_subset_Ioi hq1)
  have hsplit_int :
      ∫ t in Set.Ioi (1 : ℝ), g t =
        (∫ t in Set.Ioc (1 : ℝ) (q : ℝ), g t) + ∫ t in Set.Ioi (q : ℝ), g t := by
    rw [hsplit_set]
    exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint_left hint_right
  have hnorm_left : ‖∫ t in Set.Ioc (1 : ℝ) (q : ℝ), g t‖ ≤ Real.log (q : ℝ) := by
    have hinv_int : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Set.Ioc (1 : ℝ) (q : ℝ)) := by
      have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc (1 : ℝ) (q : ℝ)) :=
        continuousOn_inv₀.mono fun t ht ↦ (lt_of_lt_of_le zero_lt_one ht.1).ne'
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hq1).mp (hc.intervalIntegrable_of_Icc hq1))
    calc
      ‖∫ t in Set.Ioc (1 : ℝ) (q : ℝ), g t‖
          ≤ ∫ t in Set.Ioc (1 : ℝ) (q : ℝ), ‖g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) (q : ℝ), t⁻¹ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
            hinv_int ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have ht0 : 0 < t := lt_trans zero_lt_one ht.1
          dsimp only [g]
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp only [sub_re, neg_re, one_re]
          have hre : (-(1 : ℝ) - 1) = (-2 : ℝ) := by norm_num
          rw [hre]
          calc
            ‖partialCharSum χ ⌊t⌋₊‖ * t ^ (-2 : ℝ)
                ≤ t * t ^ (-2 : ℝ) :=
                  mul_le_mul_of_nonneg_right (norm_partialCharSum_le_real χ ht0.le)
                    (Real.rpow_nonneg ht0.le _)
            _ = t⁻¹ := by
                  rw [show (-2 : ℝ) = (-1 : ℝ) + (-1 : ℝ) by norm_num, Real.rpow_add ht0,
                    Real.rpow_neg_one]
                  field_simp [ht0.ne']
      _ = ∫ t in (1 : ℝ)..(q : ℝ), t⁻¹ := (intervalIntegral.integral_of_le hq1).symm
      _ = Real.log ((q : ℝ) / 1) := integral_inv_of_pos zero_lt_one hq_pos
      _ = Real.log (q : ℝ) := by simp
  have hnorm_right : ‖∫ t in Set.Ioi (q : ℝ), g t‖ ≤ 1 := by
    have hrpow_int : IntegrableOn (fun t : ℝ ↦ (q : ℝ) * t ^ (-2 : ℝ)) (Set.Ioi (q : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hq_pos).const_mul (q : ℝ)
    calc
      ‖∫ t in Set.Ioi (q : ℝ), g t‖
          ≤ ∫ t in Set.Ioi (q : ℝ), ‖g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi (q : ℝ), (q : ℝ) * t ^ (-2 : ℝ) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
            hrpow_int ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := lt_trans hq_pos ht
          dsimp only [g]
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp only [sub_re, neg_re, one_re]
          have hre : (-(1 : ℝ) - 1) = (-2 : ℝ) := by norm_num
          rw [hre]
          exact mul_le_mul_of_nonneg_right (norm_partialCharSum_le hχ _) (Real.rpow_nonneg ht0.le _)
      _ = (q : ℝ) * ∫ t in Set.Ioi (q : ℝ), t ^ (-2 : ℝ) := integral_const_mul _ _
      _ = (q : ℝ) * (-(q : ℝ) ^ (-2 + 1 : ℝ) / (-2 + 1 : ℝ)) := by
          rw [integral_Ioi_rpow_of_lt (by norm_num) hq_pos]
      _ = 1 := by
          rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
          field_simp [hq_pos.ne']
  rw [hsplit_int]
  exact (norm_add_le _ _).trans (add_le_add hnorm_left hnorm_right)

/-- **Upper bound on `L(1, χ)`** in the form `2 * log (q + 2)` for all non-principal `χ ≠ 1`. -/
theorem norm_LFunction_one_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 * Real.log ((q : ℝ) + 2) := by
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_trichotomy q 2 with hq1 | hq2 | hq2
    · have hq_eq : q = 1 := by have := NeZero.pos q; omega
      subst hq_eq
      exact absurd (DirichletCharacter.level_one χ) hχ
    · omega
    · omega
  have hlog_q : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) + 2) :=
    Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos q)) (by linarith)
  have h1_le_log : 1 ≤ Real.log ((q : ℝ) + 2) := by
    have hexp : Real.exp 1 < (q : ℝ) + 2 := by
      have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      linarith [Real.exp_one_lt_d9]
    have hlog := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at hlog
    exact hlog.le
  linarith [norm_LFunction_one_le_log_add_one hχ]

end ValueAtOneBound

/-- On the closed right half-plane, changing the character level costs at most
a fixed positive power of the quotient of levels, uniformly in height. -/
theorem norm_LFunction_changeLevel_le {d q : ℕ} [NeZero d] [NeZero q] (hdq : d∣q)
    (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : 0≤s.re) (hne : χ≠1 ∨ s≠1)
    {η : ℝ} (hη : 0<η) :
    ‖(χ.changeLevel hdq).LFunction s‖ ≤
      ‖χ.LFunction s‖*((2:ℝ)^⌈(2:ℝ)^(1/η)⌉₊*((q:ℝ)/d)^η) := by
  obtain ⟨k,rfl⟩ := hdq
  have hd := NeZero.ne d
  have hk : k≠0 := (mul_ne_zero_iff.mp (NeZero.ne (d*k))).2
  let F (p : ℕ) := 1-χ p*(p:ℂ)^(-s)
  have hprod : ∏ p∈(d*k).primeFactors,F p = ∏ p∈k.primeFactors,F p := by
    rw [Nat.primeFactors_mul hd hk]
    symm
    apply Finset.prod_subset Finset.subset_union_right
    intro p hp hpk
    have hpd := (Finset.mem_union.mp hp).resolve_right hpk
    have hχ : χ p=0 := by
      rw [MulChar.apply_eq_zero_iff,ZMod.isUnit_iff_coprime]
      exact (Nat.prime_of_mem_primeFactors hpd).coprime_iff_not_dvd.not.mpr (not_not.mpr (Nat.dvd_of_mem_primeFactors hpd))
    simp [F,hχ]
  have hs' : s=(s.re:ℂ)+(s.im:ℂ)*I := s.re_add_im.symm
  have hF := prod_euler_factor_norm_le k (fun p => χ p) (fun p => χ.norm_le_one _) (t:=s.im) hs
  rw [←hs'] at hF
  have hmul : ((d*k:ℕ):ℝ)/d=k := by push_cast;field_simp
  rw [LFunction_changeLevel_eq _ χ hne,norm_mul,hmul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  change ‖∏ p∈(d*k).primeFactors,F p‖≤_
  rw [hprod]
  exact hF.trans (prod_two_le_rpow hη k (Nat.pos_of_ne_zero hk))

/-- Critical-line transfer from the primitive character to its extension to
level `q`, with exponent one quarter and an absolute constant. -/
theorem norm_LFunction_le_conductor_quarter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ‖χ.LFunction ((1/2:ℂ)+(t:ℂ)*I)‖ ≤
      ‖χ.primitiveCharacter.LFunction ((1/2:ℂ)+(t:ℂ)*I)‖*(65536*((q:ℝ)/χ.conductor)^(1/4:ℝ)) := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have H := norm_LFunction_changeLevel_le χ.conductor_dvd_level χ.primitiveCharacter
    (s:=(1/2:ℂ)+(t:ℂ)*I) (by norm_num) (Or.inr (by intro he;have := congrArg Complex.re he;norm_num at this))
    (by norm_num : 0<(1/4:ℝ))
  rw [χ.changeLevel_primitiveCharacter] at H
  norm_num at H
  exact H

end AnalyticNumberTheory.DirichletLFunctions
