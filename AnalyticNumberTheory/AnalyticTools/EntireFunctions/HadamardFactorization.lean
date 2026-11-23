/-
Copyright (c) 2026 AnalyticNumberTheory-Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.Order
import AnalyticNumberTheory.AnalyticTools.Gamma.InfiniteProducts
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Basic.Denumerable

/-!
# Hadamard Factorization Theorem and Logarithmic Derivative Expansions

This file establishes the Hadamard factorization theorem for entire functions of finite order and
the associated canonical product and logarithmic-derivative partial-fraction expansions:

1. Global holomorphic logarithms of nowhere-vanishing entire functions, polynomial
   characterization from vanishing iterated derivatives, and Borel–Carathéodory polynomial-growth
   criteria on expanding circles.
2. Zero-factoring of entire functions, convergence of zero series from Jensen's inequality via
   dyadic shells, and canonical product order and exact-order identities.
3. Minimum-modulus lower bounds on avoiding circles for canonical products via interval pigeonhole.
4. The Hadamard factorization theorem for finite-order entire functions (`hadamard_factorization`),
   specialized to genus `0` and genus `1`, together with the finite-zero and given-enumeration
   variants (`hadamard_factorization_of_finite_zeros`, `hadamard_factorization_of_zeros`).
5. Partial-fraction expansions of `logDeriv f` for genus-`1` entire functions and canonical
   products (`logDeriv_canonicalProduct_eq_tsum`, `hadamard_logDeriv_genus_one`).
-/

open Complex Filter Metric Set Topology
open scoped BigOperators
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.AnalyticTools.EntireFunctions

/-!
### Section 1: Nowhere-Vanishing Entire Functions and Polynomial Growth
-/

/-- Any nowhere-vanishing entire function `f : ℂ → ℂ` admits a global holomorphic logarithm
`g : ℂ → ℂ` such that `∀ z, f z = Complex.exp (g z)`. -/
theorem exists_cexp_eq_of_differentiable_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  have hf_an : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have h_ld_diff : Differentiable ℂ (logDeriv f) := by
    intro z
    have hfz : DifferentiableAt ℂ f z := hf z
    have hdf : DifferentiableAt ℂ (deriv f) z := (hf_an z (mem_univ z)).deriv.differentiableAt
    exact hdf.div hfz (hf_ne z)
  obtain ⟨g, hg₀, hg_deriv⟩ := h_ld_diff.isExactOn_univ.with_val_at 0 (Complex.log (f 0))
  have hg_diff : Differentiable ℂ g := fun z ↦ (hg_deriv z (mem_univ z)).differentiableAt
  let q : ℂ → ℂ := fun z ↦ f z * Complex.exp (-g z)
  have hq_diff : Differentiable ℂ q := hf.mul hg_diff.neg.cexp
  have hq_deriv : ∀ z, deriv q z = 0 := by
    intro z
    have hfz : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have hgz : HasDerivAt g (logDeriv f z) z := hg_deriv z (mem_univ z)
    have hexp : HasDerivAt (fun w ↦ Complex.exp (-g w))
        (Complex.exp (-g z) * (-logDeriv f z)) z := hgz.neg.cexp
    rw [(hfz.fun_mul hexp).deriv, logDeriv_apply]
    have hne := hf_ne z
    field_simp [hne]
    ring
  have hq_const : ∀ z, q z = q 0 := fun z ↦
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ hq_diff.differentiableOn
      (fun w _ ↦ hq_deriv w) (mem_univ z) (mem_univ 0)
  have hq₀ : q 0 = 1 := by
    simp [q, hg₀, Complex.exp_neg, Complex.exp_log (hf_ne 0), mul_inv_cancel₀ (hf_ne 0)]
  refine ⟨g, hg_diff, fun z ↦ ?_⟩
  have hqz := (hq_const z).trans hq₀
  dsimp only [q] at hqz
  calc
    f z = (f z * Complex.exp (-g z)) * Complex.exp (g z) := by
      rw [mul_assoc, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]
    _ = Complex.exp (g z) := by rw [hqz, one_mul]

private lemma polynomial_natDegree_sum_range_le (n : ℕ) (P : ℕ → Polynomial ℂ)
    (hdeg : ∀ i ∈ Finset.range n, (P i).natDegree ≤ n) :
    (∑ i ∈ Finset.range n, P i).natDegree ≤ n := by
  classical
  have aux : ∀ s : Finset ℕ, (∀ i ∈ s, (P i).natDegree ≤ n) →
      (∑ i ∈ s, P i).natDegree ≤ n := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact hs i (Finset.mem_insert_self i s)
      · exact ih fun j hj ↦ hs j (Finset.mem_insert_of_mem hj)
  exact aux (Finset.range n) hdeg

private lemma polynomial_eval_finset_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ) (x : ℂ) :
    (∑ i ∈ s, P i).eval x = ∑ i ∈ s, (P i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private lemma polynomial_differentiable (Q : Polynomial ℂ) : Differentiable ℂ (fun z ↦ Q.eval z) := by
  have heq : (fun z : ℂ ↦ Q.eval z) =
      fun z ↦ ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * z ^ i := by
    ext z; exact Polynomial.eval_eq_sum_range z
  rw [heq]
  exact Differentiable.fun_sum fun i _ ↦ (differentiable_const _).mul (differentiable_id.pow i)

/-- An entire function `g : ℂ → ℂ` satisfying `iteratedDeriv (p + 1) g z = 0` for all `z : ℂ`
is given by a complex polynomial of degree at most `p`. -/
theorem exists_polynomial_of_iteratedDeriv_eq_zero :
    ∀ (p : ℕ) {g : ℂ → ℂ}, Differentiable ℂ g → (∀ z, iteratedDeriv (p + 1) g z = 0) →
      ∃ Q : Polynomial ℂ, Q.natDegree ≤ p ∧ ∀ z, g z = Q.eval z
  | 0, g, hg, hderiv => by
    have hconst : ∀ z, g z = g 0 := fun z ↦
      isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ hg.differentiableOn
        (fun w _ ↦ by simpa [iteratedDeriv_one] using hderiv w) (mem_univ z) (mem_univ 0)
    refine ⟨Polynomial.C (g 0), (Polynomial.natDegree_C _).le, fun z ↦ ?_⟩
    simpa using hconst z
  | p + 1, g, hg, hderiv => by
    have hg_an : AnalyticOnNhd ℂ g univ := hg.differentiableOn.analyticOnNhd isOpen_univ
    have hdg_diff : Differentiable ℂ (deriv g) := fun z ↦
      (hg_an z (mem_univ z)).deriv.differentiableAt
    have hdg_it : ∀ z, iteratedDeriv (p + 1) (deriv g) z = 0 := by
      intro z
      rw [← iteratedDeriv_succ']
      exact hderiv z
    obtain ⟨P, hP_deg, hP_eq⟩ := exists_polynomial_of_iteratedDeriv_eq_zero p hdg_diff hdg_it
    let term : ℕ → Polynomial ℂ := fun i ↦
      Polynomial.C (P.coeff i / ((i : ℂ) + 1)) * Polynomial.X ^ (i + 1)
    let Q₀ : Polynomial ℂ := ∑ i ∈ Finset.range (P.natDegree + 1), term i
    let Q : Polynomial ℂ := Q₀ + Polynomial.C (g 0)
    have hQ₀_deg : Q₀.natDegree ≤ P.natDegree + 1 := by
      refine polynomial_natDegree_sum_range_le (P.natDegree + 1) term fun i hi ↦ ?_
      have hi_lt : i < P.natDegree + 1 := Finset.mem_range.mp hi
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    have hQ_deg : Q.natDegree ≤ p + 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [Polynomial.natDegree_C]
      exact max_le (hQ₀_deg.trans (Nat.add_le_add_right hP_deg 1)) (Nat.zero_le _)
    have hQ_deriv : ∀ z, HasDerivAt (fun w ↦ Q.eval w) (deriv g z) z := by
      intro z
      have hterm_deriv : ∀ i ∈ Finset.range (P.natDegree + 1),
          HasDerivAt (fun w ↦ (term i).eval w) (P.coeff i * z ^ i) z := by
        intro i _
        have hpow : HasDerivAt (fun w : ℂ ↦ w ^ (i + 1)) (((i + 1 : ℕ) : ℂ) * z ^ i) z := by
          simpa using hasDerivAt_pow (i + 1) z
        have hmul := hpow.const_mul (P.coeff i / ((i : ℂ) + 1))
        have hne : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
        have hval : (P.coeff i / ((i : ℂ) + 1)) * (((i + 1 : ℕ) : ℂ) * z ^ i) =
            P.coeff i * z ^ i := by
          push_cast
          field_simp [hne]
        rw [hval] at hmul
        refine hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)
        simp [term]
      have hsum_deriv : HasDerivAt (fun w ↦ Q₀.eval w)
          (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ i) z := by
        have hsum := HasDerivAt.fun_sum hterm_deriv
        refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)
        dsimp only [Q₀]
        exact polynomial_eval_finset_sum (Finset.range (P.natDegree + 1)) term w
      have hP_sum : ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ i = P.eval z := by
        rw [Polynomial.eval_eq_sum_range]
      rw [hP_sum, ← hP_eq z] at hsum_deriv
      have hc : HasDerivAt (fun w ↦ Q.eval w) (deriv g z + 0) z :=
        (hsum_deriv.fun_add (hasDerivAt_const z (g 0))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun w ↦ by simp [Q])
      simpa only [add_zero] using hc
    have hdiff_zero : ∀ z, deriv (fun w ↦ g w - Q.eval w) z = 0 := by
      intro z
      have hd := (hg z).hasDerivAt.fun_sub (hQ_deriv z)
      simpa using hd.deriv
    have hsub_diff : Differentiable ℂ (fun w ↦ g w - Q.eval w) :=
      hg.sub (polynomial_differentiable Q)
    have hsub_const : ∀ z, g z - Q.eval z = g 0 - Q.eval 0 := fun z ↦
      isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ hsub_diff.differentiableOn
        (fun w _ ↦ hdiff_zero w) (mem_univ z) (mem_univ 0)
    have hQ₀_at_0 : Q₀.eval 0 = 0 := by
      dsimp only [Q₀]
      rw [polynomial_eval_finset_sum]
      simp [term]
    have hQ_at_0 : Q.eval 0 = g 0 := by simp [Q, hQ₀_at_0]
    refine ⟨Q, hQ_deg, fun z ↦ ?_⟩
    have hz := hsub_const z
    rw [hQ_at_0, sub_self] at hz
    exact sub_eq_zero.mp hz

/-- **Real-part maximum principle on disks**: if `g : ℂ → ℂ` is entire, `0 < r`, and
`(g w).re ≤ M` on `Metric.sphere 0 r`, then `(g w).re ≤ M` on `Metric.closedBall 0 r`. -/
theorem re_le_on_closedBall_of_sphere {g : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hg : Differentiable ℂ g) (hsph : ∀ w ∈ Metric.sphere (0 : ℂ) r, (g w).re ≤ M) :
    ∀ w ∈ Metric.closedBall (0 : ℂ) r, (g w).re ≤ M := by
  let h : ℂ → ℂ := fun w ↦ Complex.exp (g w)
  have hh_diff : DiffContOnCl ℂ h (Metric.ball 0 r) := hg.cexp.diffContOnCl
  have hh_frontier : ∀ x ∈ frontier (Metric.ball (0 : ℂ) r), ‖h x‖ ≤ Real.exp M := by
    intro x hx
    dsimp only [h]
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hsph x (Metric.frontier_ball_subset_sphere hx))
  intro w hw
  have hw_cl : w ∈ closure (Metric.ball (0 : ℂ) r) := by rwa [closure_ball (0 : ℂ) hr.ne']
  have hle : ‖h w‖ ≤ Real.exp M :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hh_diff hh_frontier hw_cl
  dsimp only [h] at hle
  rw [Complex.norm_exp, Real.exp_le_exp] at hle
  exact hle

/-- **Borel–Carathéodory polynomial criterion**: if an entire function `g : ℂ → ℂ` satisfies
`(g w).re ≤ C * r ^ α` on arbitrarily large circles `Metric.sphere 0 r` with `0 ≤ α < p + 1`,
then `g` is a polynomial of degree at most `p`. -/
theorem exists_polynomial_of_re_le_rpow {g : ℂ → ℂ} {p : ℕ} {α C : ℝ}
    (hg : Differentiable ℂ g) (_hα_nonneg : 0 ≤ α) (hα_lt : α < (p : ℝ) + 1)
    (hsph : ∀ᶠ R : ℝ in atTop, ∃ r : ℝ, R ≤ r ∧ ∀ w ∈ Metric.sphere (0 : ℂ) r, (g w).re ≤ C * r ^ α) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ p ∧ ∀ z, g z = Q.eval z := by
  refine exists_polynomial_of_iteratedDeriv_eq_zero p hg fun z ↦ ?_
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (norm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp hsph
  let A : ℝ := max C 0
  have hA_nonneg : 0 ≤ A := le_max_right C 0
  let B : ℝ := 2 ^ (p + 3) * ((Nat.factorial (p + 1) : ℝ) * 2 ^ (p + 2))
  have hB_nonneg : 0 ≤ B := by positivity
  let K₁ : ℝ := B * A
  let K₂ : ℝ := B * |(g 0).re|
  have hpow1_pos : 0 < ((p : ℝ) + 1 - α) := sub_pos.mpr hα_lt
  have hpow2_pos : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have htend1 : Tendsto (fun r : ℝ ↦ K₁ * r ^ (-((p : ℝ) + 1 - α))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hpow1_pos).const_mul K₁
  have htend2 : Tendsto (fun r : ℝ ↦ K₂ * r ^ (-((p : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hpow2_pos).const_mul K₂
  have htend : Tendsto (fun r : ℝ ↦
      K₁ * r ^ (-((p : ℝ) + 1 - α)) + K₂ * r ^ (-((p : ℝ) + 1))) atTop (𝓝 (0 + 0)) :=
    htend1.add htend2
  rw [add_zero] at htend
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (htend.eventually (Iio_mem_nhds hε))
  let R_big : ℝ := max R₀ (max R₁ (max (2 * ‖z‖ + 2) 1))
  obtain ⟨r, hr_ge, hr_sph⟩ := hR₀ R_big (le_max_left _ _)
  have hr_ge_R₁ : R₁ ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr_ge)
  have hr_ge_2z : 2 * ‖z‖ + 2 ≤ r :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hr_ge))
  have hr_ge_one : 1 ≤ r :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hr_ge))
  have hr_pos : 0 < r := zero_lt_one.trans_le hr_ge_one
  have hz_lt_r : ‖z‖ < r := by linarith [norm_nonneg z]
  have hr_ball : ∀ w ∈ Metric.ball (0 : ℂ) r, (g w).re ≤ max ((g 0).re) (A * r ^ α) := by
    intro w hw
    have hre := re_le_on_closedBall_of_sphere hr_pos hg hr_sph w (Metric.ball_subset_closedBall hw)
    have hCA : C * r ^ α ≤ A * r ^ α :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hr_pos.le α)
    exact (hre.trans hCA).trans (le_max_right _ _)
  have hbc := norm_iteratedDeriv_le_of_re_le (k := p + 1) (z₀ := 0) (z := z) (r := ‖z‖) (R := r)
    (M := max ((g 0).re) (A * r ^ α)) (Nat.le_add_left 1 p) (norm_nonneg z) hz_lt_r
    hg.differentiableOn hr_ball (Metric.mem_closedBall.mpr (by rw [dist_zero_right]))
  have hr_sub : r / 2 ≤ r - ‖z‖ := by linarith
  have h_frac_le : r / (r - ‖z‖) ^ (p + 2) ≤ 2 ^ (p + 2) * r ^ (-((p : ℝ) + 1)) := by
    have hp2 : (r / 2) ^ (p + 2) ≤ (r - ‖z‖) ^ (p + 2) :=
      pow_le_pow_left₀ (by positivity) hr_sub (p + 2)
    have h1 : r / (r - ‖z‖) ^ (p + 2) ≤ r / (r / 2) ^ (p + 2) :=
      div_le_div_of_nonneg_left hr_pos.le (by positivity) hp2
    have h2 : r / (r / 2) ^ (p + 2) = 2 ^ (p + 2) * r ^ (-((p : ℝ) + 1)) := by
      rw [div_pow, div_div_eq_mul_div]
      have hrp : r ^ (p + 2) = r * r ^ (p + 1) := by ring
      rw [hrp, mul_div_mul_left _ _ hr_pos.ne']
      rw [← Real.rpow_natCast r (p + 1), Real.rpow_neg hr_pos.le, div_eq_mul_inv]
      push_cast
      ring
    exact h1.trans_eq h2
  have hM_diff : max ((g 0).re) (A * r ^ α) - (g 0).re ≤ A * r ^ α + |(g 0).re| := by
    rcases le_total ((g 0).re) (A * r ^ α) with hle | hle
    · rw [max_eq_right hle]
      linarith [neg_le_abs ((g 0).re)]
    · rw [max_eq_left hle, sub_self]
      exact add_nonneg (mul_nonneg hA_nonneg (Real.rpow_nonneg hr_pos.le α)) (abs_nonneg _)
  have hpow_mul : r ^ (-((p : ℝ) + 1)) * (A * r ^ α) = A * r ^ (-((p : ℝ) + 1 - α)) := by
    rw [mul_left_comm, ← Real.rpow_add hr_pos]
    congr 2
    ring
  have hcoeff_le : 2 ^ ((p + 1) + 2) * ((Nat.factorial (p + 1) : ℝ) *
      (r / (r - ‖z‖) ^ ((p + 1) + 1))) * (max ((g 0).re) (A * r ^ α) - (g 0).re) ≤
      K₁ * r ^ (-((p : ℝ) + 1 - α)) + K₂ * r ^ (-((p : ℝ) + 1)) := by
    have h1 : 2 ^ ((p + 1) + 2) * ((Nat.factorial (p + 1) : ℝ) *
        (r / (r - ‖z‖) ^ ((p + 1) + 1))) ≤ B * r ^ (-((p : ℝ) + 1)) := by
      have hfac : (Nat.factorial (p + 1) : ℝ) * (r / (r - ‖z‖) ^ (p + 2)) ≤
          (Nat.factorial (p + 1) : ℝ) * (2 ^ (p + 2) * r ^ (-((p : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h_frac_le (Nat.cast_nonneg _)
      have h23 : (2 : ℝ) ^ ((p + 1) + 2) = 2 ^ (p + 3) := by ring_nf
      calc
        2 ^ ((p + 1) + 2) * ((Nat.factorial (p + 1) : ℝ) *
            (r / (r - ‖z‖) ^ ((p + 1) + 1)))
          = 2 ^ (p + 3) * ((Nat.factorial (p + 1) : ℝ) * (r / (r - ‖z‖) ^ (p + 2))) := by
              rw [h23]
        _ ≤ 2 ^ (p + 3) * ((Nat.factorial (p + 1) : ℝ) * (2 ^ (p + 2) * r ^ (-((p : ℝ) + 1)))) :=
              mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = B * r ^ (-((p : ℝ) + 1)) := by simp only [B]; ring
    have hM_nonneg : 0 ≤ max ((g 0).re) (A * r ^ α) - (g 0).re :=
      sub_nonneg.mpr (le_max_left _ _)
    have h2 : 2 ^ ((p + 1) + 2) * ((Nat.factorial (p + 1) : ℝ) *
        (r / (r - ‖z‖) ^ ((p + 1) + 1))) * (max ((g 0).re) (A * r ^ α) - (g 0).re) ≤
        B * r ^ (-((p : ℝ) + 1)) * (A * r ^ α + |(g 0).re|) :=
      mul_le_mul h1 hM_diff hM_nonneg (by positivity)
    refine h2.trans_eq ?_
    rw [mul_add, mul_assoc B (r ^ (-((p : ℝ) + 1))) (A * r ^ α), hpow_mul]
    simp only [K₁, K₂]
    ring
  have hbc' : ‖iteratedDeriv (p + 1) g z‖ ≤
      2 ^ ((p + 1) + 2) * ((Nat.factorial (p + 1) : ℝ) *
        (r / (r - ‖z‖) ^ ((p + 1) + 1))) * (max ((g 0).re) (A * r ^ α) - (g 0).re) := by
    refine hbc.trans_eq ?_
    ring
  exact (hbc'.trans hcoeff_le).trans (hR₁ r hr_ge_R₁).le

/-!
### Section 2: Zero Factoring and Order of Quotients
-/

/-- An entire function that is not identically zero has finite analytic order at every point. -/
theorem analyticOrderAt_ne_top_of_differentiable_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : f ≠ 0) (z₀ : ℂ) :
    analyticOrderAt f z₀ ≠ ⊤ := by
  have h_ex : ∃ w : ℂ, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf_ne (funext h)
  obtain ⟨w, hw⟩ := h_ex
  have hf_an : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  refine hf_an.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ w)
    (mem_univ z₀) ?_
  rw [(hf_an w (mem_univ w)).analyticOrderAt_eq_zero.mpr hw]
  simp

/-- Factoring out the zero of order `analyticOrderNatAt f c` at `c : ℂ` from a nonzero entire
function `f : ℂ → ℂ`: there exists an entire `f₀ : ℂ → ℂ` with `f₀ c ≠ 0`,
`∀ z, f z = (z - c) ^ analyticOrderNatAt f c * f₀ z`, and identical analytic orders away from `c`. -/
theorem exists_div_pow_entire_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : f ≠ 0) (c : ℂ) :
    ∃ f₀ : ℂ → ℂ, Differentiable ℂ f₀ ∧ f₀ c ≠ 0 ∧
      (∀ z : ℂ, f z = (z - c) ^ analyticOrderNatAt f c * f₀ z) ∧
      (∀ z ≠ c, analyticOrderNatAt f₀ z = analyticOrderNatAt f z) := by
  let m : ℕ := analyticOrderNatAt f c
  let φ : ℂ → ℂ := fun w ↦ f w / (w - c) ^ m
  let f₀ : ℂ → ℂ := fun z ↦ Filter.limUnder (𝓝[≠] z) φ
  have hf_an : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hφ_an : ∀ z ≠ c, AnalyticAt ℂ φ z := by
    intro z hzc
    refine (hf_an z (mem_univ z)).div (((analyticAt_id (𝕜 := ℂ) (z := z)).sub analyticAt_const).pow m)
      (pow_ne_zero m (sub_ne_zero.mpr hzc))
  have hf₀_ne_c : ∀ z ≠ c, f₀ z = φ z := by
    intro z hzc
    have hc_cont : ContinuousAt φ z := (hφ_an z hzc).continuousAt
    exact (hc_cont.continuousWithinAt).tendsto.limUnder_eq
  have hf₀_eq_nhds_ne : ∀ z ≠ c, f₀ =ᶠ[𝓝 z] φ := by
    intro z hzc
    filter_upwards [isOpen_ne.mem_nhds hzc] with w hwc
    exact hf₀_ne_c w hwc
  have htop_c : analyticOrderAt f c ≠ ⊤ := analyticOrderAt_ne_top_of_differentiable_ne_zero hf hf_ne c
  obtain ⟨g, hg_an, hgc, hfg⟩ := (hf_an c (mem_univ c)).analyticOrderAt_ne_top.mp htop_c
  have h_eq_nhdsWithin : φ =ᶠ[𝓝[≠] c] g := by
    filter_upwards [nhdsWithin_le_nhds hfg, self_mem_nhdsWithin] with w hwg hwc
    have hsub_ne : (w - c) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hwc)
    simp only [φ, smul_eq_mul] at hwg ⊢
    rw [hwg, mul_div_cancel_left₀ _ hsub_ne]
  have hf₀_c : f₀ c = g c :=
    ((hg_an.continuousAt.continuousWithinAt).tendsto.congr' h_eq_nhdsWithin.symm).limUnder_eq
  have hf₀_at_c : f₀ =ᶠ[𝓝 c] g := by
    filter_upwards [hfg] with w hwg
    rcases eq_or_ne w c with rfl | hwc
    · exact hf₀_c
    · rw [hf₀_ne_c w hwc]
      have hsub_ne : (w - c) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hwc)
      simp only [φ, smul_eq_mul] at hwg ⊢
      rw [hwg, mul_div_cancel_left₀ _ hsub_ne]
  have hf₀_an_all : ∀ z : ℂ, AnalyticAt ℂ f₀ z := by
    intro z
    rcases eq_or_ne z c with rfl | hzc
    · exact hg_an.congr hf₀_at_c.symm
    · exact (hφ_an z hzc).congr (hf₀_eq_nhds_ne z hzc).symm
  have hf₀_diff : Differentiable ℂ f₀ := fun z ↦ (hf₀_an_all z).differentiableAt
  have hf₀_eq : ∀ z : ℂ, f z = (z - c) ^ m * f₀ z := by
    intro z
    by_cases hzc : z = c
    · rw [hzc]
      by_cases hm : m = 0
      · have hfc : f c ≠ 0 := by
          intro hzero
          have : analyticOrderAt f c ≠ 0 := (hf_an c (mem_univ c)).analyticOrderAt_ne_zero.mpr hzero
          have hm_ne : m ≠ 0 := by
            intro hm0
            apply this
            rw [← Nat.cast_analyticOrderNatAt htop_c]
            simp [m, hm0]
          exact hm_ne hm
        have hf_at_c : f c = g c := by simpa [m, hm] using hfg.self_of_nhds
        simp [hm, hf₀_c, hf_at_c]
      · have hfc : f c = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
        simp [hfc, hm]
    · rw [hf₀_ne_c z hzc]
      have hsub_ne : (z - c) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hzc)
      simp only [φ]
      rw [mul_div_cancel₀ _ hsub_ne]
  have hf₀_ord : ∀ z ≠ c, analyticOrderNatAt f₀ z = analyticOrderNatAt f z := by
    intro z hzc
    have hpow_an : AnalyticAt ℂ (fun w ↦ (w - c) ^ m) z :=
      ((analyticAt_id (𝕜 := ℂ) (z := z)).sub analyticAt_const).pow m
    have hpow_ne : (z - c) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hzc)
    have hpow_top : analyticOrderAt (fun w ↦ (w - c) ^ m) z ≠ ⊤ := by
      rw [hpow_an.analyticOrderAt_eq_zero.mpr hpow_ne]
      simp
    have hpow_ord : analyticOrderNatAt (fun w ↦ (w - c) ^ m) z = 0 := by
      have : analyticOrderAt (fun w ↦ (w - c) ^ m) z = 0 :=
        hpow_an.analyticOrderAt_eq_zero.mpr hpow_ne
      simp [analyticOrderNatAt, this]
    have hf₀_ne : f₀ ≠ 0 := fun h0 ↦ hgc (by rw [← hf₀_c, h0]; rfl)
    have hf₀_top : analyticOrderAt f₀ z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_differentiable_ne_zero hf₀_diff hf₀_ne z
    have hfun_eq : f = fun w ↦ (w - c) ^ m * f₀ w := funext hf₀_eq
    have hmul := analyticOrderNatAt_fun_mul hpow_an (hf₀_an_all z) hpow_top hf₀_top
    rw [← hfun_eq, hpow_ord, zero_add] at hmul
    exact hmul.symm
  exact ⟨f₀, hf₀_diff, hf₀_c.symm ▸ hgc, hf₀_eq, hf₀_ord⟩

/-- Dividing out a monomial `z ^ m` from an entire function preserves any order upper bound
`EntireOrderLe f ρ`. -/
theorem entireOrderLe_of_eq_pow_mul {f g : ℂ → ℂ} {m : ℕ} {ρ : ℝ}
    (hg : Differentiable ℂ g) (hf_ord : EntireOrderLe f ρ)
    (heq : ∀ z : ℂ, f z = z ^ m * g z) :
    EntireOrderLe g ρ := by
  refine entireOrderLe_of_eventually_exp hg fun ε hε ↦ ?_
  obtain ⟨C, _, hbound⟩ := hf_ord.norm_le hε
  refine ⟨C, 1, 1, le_rfl, fun z hz ↦ ?_⟩
  have hpow_ge : 1 ≤ ‖z‖ ^ m := one_le_pow₀ hz
  have hfz : ‖f z‖ = ‖z‖ ^ m * ‖g z‖ := by rw [heq z, norm_mul, norm_pow]
  have hgz_le_fz : ‖g z‖ ≤ ‖f z‖ := by
    calc
      ‖g z‖ = 1 * ‖g z‖ := (one_mul _).symm
      _ ≤ ‖z‖ ^ m * ‖g z‖ := mul_le_mul_of_nonneg_right hpow_ge (norm_nonneg _)
      _ = ‖f z‖ := hfz.symm
  simpa using hgz_le_fz.trans (hbound z)

/-- Dividing two entire functions `f` and `Q` that have the same analytic order at every point
yields a nowhere-vanishing entire quotient `h : ℂ → ℂ` with `∀ z, f z = Q z * h z`. -/
theorem quotient_entire_ne_zero_of_eq_analyticOrderNatAt {f Q : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hQ : Differentiable ℂ Q) (hQ_ne : Q ≠ 0)
    (hord : ∀ z : ℂ, analyticOrderNatAt f z = analyticOrderNatAt Q z) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧ (∀ z, f z = Q z * h z) := by
  let φ : ℂ → ℂ := fun w ↦ f w / Q w
  let h : ℂ → ℂ := fun z ↦ Filter.limUnder (𝓝[≠] z) φ
  have hf_an : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hQ_an : AnalyticOnNhd ℂ Q univ := hQ.differentiableOn.analyticOnNhd isOpen_univ
  have hh_loc : ∀ z₀ : ℂ, ∃ f₁ q₁ : ℂ → ℂ, AnalyticAt ℂ f₁ z₀ ∧ AnalyticAt ℂ q₁ z₀ ∧
      f₁ z₀ ≠ 0 ∧ q₁ z₀ ≠ 0 ∧ (h =ᶠ[𝓝 z₀] fun w ↦ f₁ w / q₁ w) ∧
      (∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ analyticOrderNatAt Q z₀ * f₁ w) ∧
      (∀ᶠ w in 𝓝 z₀, Q w = (w - z₀) ^ analyticOrderNatAt Q z₀ * q₁ w) := by
    intro z₀
    have htop_f : analyticOrderAt f z₀ ≠ ⊤ := analyticOrderAt_ne_top_of_differentiable_ne_zero hf hf_ne z₀
    have htop_Q : analyticOrderAt Q z₀ ≠ ⊤ := analyticOrderAt_ne_top_of_differentiable_ne_zero hQ hQ_ne z₀
    obtain ⟨f₁, hf₁_an, hf₁_ne, hf₁_eq⟩ := (hf_an z₀ (mem_univ z₀)).analyticOrderAt_ne_top.mp htop_f
    obtain ⟨q₁, hq₁_an, hq₁_ne, hq₁_eq⟩ := (hQ_an z₀ (mem_univ z₀)).analyticOrderAt_ne_top.mp htop_Q
    rw [hord z₀] at hf₁_eq
    have hq₁_nhds : ∀ᶠ w in 𝓝 z₀, q₁ w ≠ 0 := hq₁_an.continuousAt.eventually_ne hq₁_ne
    have h_ratio_nhds : φ =ᶠ[𝓝[≠] z₀] fun w ↦ f₁ w / q₁ w := by
      filter_upwards [nhdsWithin_le_nhds (hf₁_eq.and (hq₁_eq.and hq₁_nhds)),
        self_mem_nhdsWithin] with w ⟨hwf, hwQ, _⟩ hw_ne
      have hpow_ne : (w - z₀) ^ analyticOrderNatAt Q z₀ ≠ 0 :=
        pow_ne_zero _ (sub_ne_zero.mpr hw_ne)
      simp only [smul_eq_mul] at hwf hwQ
      simp only [φ]
      rw [hwf, hwQ, mul_div_mul_left _ _ hpow_ne]
    have h_at_z₀ : h z₀ = f₁ z₀ / q₁ z₀ := by
      have hcont : ContinuousAt (fun w ↦ f₁ w / q₁ w) z₀ :=
        hf₁_an.continuousAt.div hq₁_an.continuousAt hq₁_ne
      exact ((hcont.continuousWithinAt).tendsto.congr' h_ratio_nhds.symm).limUnder_eq
    have h_eq_nhds : h =ᶠ[𝓝 z₀] fun w ↦ f₁ w / q₁ w := by
      obtain ⟨U, hU_sub, hU_open, hz₀U⟩ := _root_.mem_nhds_iff.mp (hf₁_eq.and (hq₁_eq.and hq₁_nhds))
      refine _root_.mem_nhds_iff.mpr ⟨U, fun w hwU ↦ ?_, hU_open, hz₀U⟩
      rcases eq_or_ne w z₀ with rfl | hw_ne
      · exact h_at_z₀
      · obtain ⟨hwf, hwQ, hqne⟩ := hU_sub hwU
        simp only [smul_eq_mul] at hwf hwQ
        have hQw_ne : Q w ≠ 0 := by
          rw [hwQ]
          exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hw_ne)) hqne
        have hφ_cont : ContinuousAt φ w :=
          (hf w).continuousAt.div (hQ w).continuousAt hQw_ne
        have hhw : h w = φ w := (hφ_cont.continuousWithinAt).tendsto.limUnder_eq
        change h w = f₁ w / q₁ w
        rw [hhw]
        have hpow_ne : (w - z₀) ^ analyticOrderNatAt Q z₀ ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr hw_ne)
        simp only [φ]
        rw [hwf, hwQ, mul_div_mul_left _ _ hpow_ne]
    exact ⟨f₁, q₁, hf₁_an, hq₁_an, hf₁_ne, hq₁_ne, h_eq_nhds, hf₁_eq, hq₁_eq⟩
  have hh_diff : Differentiable ℂ h := by
    intro z₀
    obtain ⟨f₁, q₁, hf₁_an, hq₁_an, _, hq₁_ne, h_eq, _, _⟩ := hh_loc z₀
    exact ((hf₁_an.div hq₁_an hq₁_ne).congr h_eq.symm).differentiableAt
  have hh_ne : ∀ z₀, h z₀ ≠ 0 := by
    intro z₀
    obtain ⟨f₁, q₁, _, _, hf₁_ne, hq₁_ne, h_eq, _, _⟩ := hh_loc z₀
    rw [h_eq.self_of_nhds]
    exact div_ne_zero hf₁_ne hq₁_ne
  have hmul_eq : ∀ z₀, f z₀ = Q z₀ * h z₀ := by
    intro z₀
    obtain ⟨f₁, q₁, _, _, _, hq₁_ne, h_eq, hf₁_eq, hq₁_eq⟩ := hh_loc z₀
    have hfz := hf₁_eq.self_of_nhds
    have hQz := hq₁_eq.self_of_nhds
    have hhz := h_eq.self_of_nhds
    rcases Nat.eq_zero_or_pos (analyticOrderNatAt Q z₀) with hk | hk
    · simp only [hk, pow_zero, one_mul] at hfz hQz
      rw [hfz, hQz, hhz]
      field_simp [hq₁_ne]
    · rw [hfz, hQz, sub_self, zero_pow hk.ne']
      simp only [zero_mul]
  exact ⟨h, hh_diff, hh_ne, hmul_eq⟩

/-!
### Section 3: Zero-Counting Convergence via Dyadic Shells and Canonical Product Order
-/

private lemma card_finset_le_zeroCount_of_enumeration {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0)
    (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z)
    {R : ℝ} (hR : 0 ≤ R) {S : Finset ℕ} (hS : ∀ n ∈ S, ‖a n‖ ≤ R) :
    S.card ≤ zeroCount f 0 R := by
  classical
  have hf_an : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hfin_zero := zeroSet_finite hR hf_an hf0
  rw [zeroCount_eq_sum_analyticOrderNatAt hR hf_an hf0 (Set.Finite.coe_toFinset hfin_zero)]
  have hfiber : S.card = ∑ z ∈ S.image a, (S.filter (fun n ↦ a n = z)).card :=
    Finset.card_eq_sum_card_fiberwise (f := a) (t := S.image a) fun n hn ↦ Finset.mem_image_of_mem a hn
  rw [hfiber]
  have hterm : ∀ z ∈ S.image a, (S.filter (fun n ↦ a n = z)).card ≤ analyticOrderNatAt f z := by
    intro z hz
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
    have hfin_fiber : ({m : ℕ | a m = a n}).Finite :=
      (ha_fin ‖a n‖).subset fun m hm ↦ by simp only [Set.mem_ofPred_eq] at hm ⊢; rw [hm]
    have hsub : (S.filter (fun m ↦ a m = a n) : Set ℕ) ⊆ {m : ℕ | a m = a n} := by
      intro m hm
      exact (Finset.mem_filter.mp hm).2
    have hncard := Set.ncard_le_ncard hsub hfin_fiber
    rw [Set.ncard_coe_finset, ha_card (a n) (ha_ne n)] at hncard
    exact hncard
  have himage_sub : S.image a ⊆ hfin_zero.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset, mem_zeroSet, Metric.mem_closedBall, dist_zero_right]
    obtain ⟨n, hnS, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨hS n hnS, ?_⟩
    have hfin_fiber : ({m : ℕ | a m = a n}).Finite :=
      (ha_fin ‖a n‖).subset fun m hm ↦ by simp only [Set.mem_ofPred_eq] at hm ⊢; rw [hm]
    have hnonempty : ({m : ℕ | a m = a n}).Nonempty := ⟨n, rfl⟩
    have hpos : 0 < ({m : ℕ | a m = a n}).ncard := (Set.ncard_pos hfin_fiber).mpr hnonempty
    rw [ha_card (a n) (ha_ne n)] at hpos
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne'
  calc
    ∑ z ∈ S.image a, (S.filter (fun n ↦ a n = z)).card
      ≤ ∑ z ∈ S.image a, analyticOrderNatAt f z := Finset.sum_le_sum hterm
    _ ≤ ∑ z ∈ hfin_zero.toFinset, analyticOrderNatAt f z :=
        Finset.sum_le_sum_of_subset himage_sub

private lemma zeroCount_le_rpow_of_entireOrderLe {f : ℂ → ℂ} {ρ δ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ) (hf0 : f 0 ≠ 0)
    (hδ : 0 < δ) :
    ∃ C > 0, ∀ r : ℝ, 1 ≤ r → (zeroCount f 0 r : ℝ) ≤ C * r ^ (ρ + δ) := by
  obtain ⟨C₀, _, hbound⟩ := hord.norm_le (half_pos hδ)
  have hf_an : ∀ r : ℝ, AnalyticOnNhd ℂ f (Metric.closedBall 0 (2 * r)) := fun r ↦
    (hf.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  let C₁ : ℝ := max C₀ 1
  have hC₁_pos : 0 < C₁ := zero_lt_one.trans_le (le_max_right C₀ 1)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let K : ℝ := (max (Real.log C₁ - Real.log ‖f 0‖) 0 + (2 : ℝ) ^ (ρ + δ / 2)) / Real.log 2 + 1
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, fun r hr ↦ ?_⟩
  have hr_pos : 0 < r := zero_lt_one.trans_le hr
  have hr2r : r < 2 * r := by linarith
  have hρδ_nonneg : 0 ≤ ρ + δ := by linarith
  have hr_pow_ge : 1 ≤ r ^ (ρ + δ) := Real.one_le_rpow hr hρδ_nonneg
  let M : ℝ := C₁ * Real.exp ((2 * r) ^ (ρ + δ / 2))
  have hM_pos : 0 < M := mul_pos hC₁_pos (Real.exp_pos _)
  have h_sph : ∀ z ∈ Metric.sphere (0 : ℂ) (2 * r), ‖f z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ = 2 * r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have h1 : C₀ * Real.exp (‖z‖ ^ (ρ + δ / 2)) ≤ C₁ * Real.exp (‖z‖ ^ (ρ + δ / 2)) :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (Real.exp_pos _).le
    simpa [M, hzn] using (hbound z).trans h1
  have hj := zeroCount_le_sub_log_div_log hr_pos hr2r hM_pos (hf_an r) hf0 h_sph
  have h2r_div : 2 * r / r = 2 := by field_simp [hr_pos.ne']
  rw [h2r_div] at hj
  have hlogM : Real.log M = Real.log C₁ + (2 * r) ^ (ρ + δ / 2) := by
    rw [Real.log_mul hC₁_pos.ne' (Real.exp_ne_zero _), Real.log_exp]
  rw [hlogM] at hj
  have h_mul2 : (2 * r) ^ (ρ + δ / 2) = (2 : ℝ) ^ (ρ + δ / 2) * r ^ (ρ + δ / 2) :=
    Real.mul_rpow zero_le_two hr_pos.le
  have hr_pow_cmp : r ^ (ρ + δ / 2) ≤ r ^ (ρ + δ) :=
    Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hnum_le : Real.log C₁ + (2 * r) ^ (ρ + δ / 2) - Real.log ‖f 0‖ ≤
      (max (Real.log C₁ - Real.log ‖f 0‖) 0 + (2 : ℝ) ^ (ρ + δ / 2)) * r ^ (ρ + δ) := by
    have hlin : Real.log C₁ - Real.log ‖f 0‖ ≤
        max (Real.log C₁ - Real.log ‖f 0‖) 0 * r ^ (ρ + δ) :=
      (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) hr_pow_ge)
    have hterm2 : (2 * r) ^ (ρ + δ / 2) ≤ (2 : ℝ) ^ (ρ + δ / 2) * r ^ (ρ + δ) := by
      rw [h_mul2]
      exact mul_le_mul_of_nonneg_left hr_pow_cmp (by positivity)
    linarith
  have hj2 : (zeroCount f 0 r : ℝ) ≤
      ((max (Real.log C₁ - Real.log ‖f 0‖) 0 + (2 : ℝ) ^ (ρ + δ / 2)) / Real.log 2) *
        r ^ (ρ + δ) := by
    refine hj.trans ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hnum_le hlog2_pos.le
  refine hj2.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hr_pos.le _))
  dsimp only [K]
  linarith

/-- **Jensen zero-series convergence via dyadic shells**: if `f` is entire of order at most `ρ ≥ 0`
with `f 0 ≠ 0`, and `a : ℕ → ℂ` enumerates the zeros of `f` according to multiplicity with
finite norm-bounded subsets, then `∑' n, ‖a n‖ ^ (-σ)` converges for every `σ > ρ`. -/
theorem summable_norm_rpow_neg_of_enumeration {f : ℂ → ℂ} {ρ σ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ) (hf0 : f 0 ≠ 0) (hσ : ρ < σ)
    {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0) (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) :
    Summable (fun n : ℕ ↦ ‖a n‖ ^ (-σ : ℝ)) := by
  classical
  let δ : ℝ := (σ - ρ) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hσ_pos : 0 < σ := by linarith
  obtain ⟨C, _, hzc⟩ := zeroCount_le_rpow_of_entireOrderLe hf hρ hord hf0 hδ
  let S_small : Finset ℕ := (ha_fin 1).toFinset.filter (fun n ↦ ‖a n‖ < 1)
  let M_small : ℝ := ∑ n ∈ S_small, ‖a n‖ ^ (-σ : ℝ)
  let r_geom : ℝ := (2 : ℝ) ^ (-δ)
  have hr_geom_pos : 0 < r_geom := Real.rpow_pos_of_pos zero_lt_two _
  have hr_geom_lt : r_geom < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  let C_shell : ℝ := C * (2 : ℝ) ^ (ρ + δ)
  have hC_shell_nonneg : 0 ≤ C_shell := by positivity
  refine summable_of_sum_le (c := M_small + C_shell / (1 - r_geom))
    (fun n ↦ Real.rpow_nonneg (norm_nonneg _) _) (fun u ↦ ?_)
  let u_small := u.filter (fun n ↦ ‖a n‖ < 1)
  let u_big := u.filter (fun n ↦ 1 ≤ ‖a n‖)
  have hu_split : ∑ n ∈ u, ‖a n‖ ^ (-σ : ℝ) =
      (∑ n ∈ u_small, ‖a n‖ ^ (-σ : ℝ)) + (∑ n ∈ u_big, ‖a n‖ ^ (-σ : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not u (fun n ↦ ‖a n‖ < 1)]
    congr 1
    refine Finset.sum_congr (by ext n; simp [u_big, not_lt]) fun _ _ ↦ rfl
  have hu_small_le : ∑ n ∈ u_small, ‖a n‖ ^ (-σ : ℝ) ≤ M_small := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hn'.2.le, hn'.2⟩
  have hu_big_le : ∑ n ∈ u_big, ‖a n‖ ^ (-σ : ℝ) ≤ C_shell / (1 - r_geom) := by
    by_cases hne : u_big.Nonempty
    · have hex_K : ∃ K : ℕ, ∀ n ∈ u_big, ‖a n‖ < (2 : ℝ) ^ K := by
        obtain ⟨n₀, hn₀, hmax⟩ := u_big.exists_max_image (fun n ↦ ‖a n‖) hne
        obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ‖a n₀‖ one_lt_two
        exact ⟨K, fun n hn ↦ (hmax n hn).trans_lt hK⟩
      obtain ⟨K, hK⟩ := hex_K
      let shell : ℕ → Finset ℕ := fun k ↦
        u_big.filter (fun n ↦ (2 : ℝ) ^ k ≤ ‖a n‖ ∧ ‖a n‖ < (2 : ℝ) ^ (k + 1))
      have hdisj : (Finset.range K : Set ℕ).PairwiseDisjoint shell := by
        intro j _ k _ hjk
        rw [Function.onFun, Finset.disjoint_left]
        intro n hnj hnk
        have h1 := (Finset.mem_filter.mp hnj).2
        have h2 := (Finset.mem_filter.mp hnk).2
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
            pow_le_pow_right₀ one_le_two (Nat.succ_le_of_lt hlt)
          linarith [h1.2, h2.1]
        · have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
            pow_le_pow_right₀ one_le_two (Nat.succ_le_of_lt hgt)
          linarith [h2.2, h1.1]
      have hsub_u : u_big ⊆ (Finset.range K).biUnion shell := by
        intro n hn
        have hn1 : 1 ≤ ‖a n‖ := (Finset.mem_filter.mp hn).2
        have hnK : ‖a n‖ < (2 : ℝ) ^ K := hK n hn
        have hex_k : ∃ k : ℕ, (2 : ℝ) ^ k ≤ ‖a n‖ ∧ ‖a n‖ < (2 : ℝ) ^ (k + 1) := by
          let S_k := (Finset.range (K + 1)).filter (fun k ↦ (2 : ℝ) ^ k ≤ ‖a n‖)
          have h0 : 0 ∈ S_k := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ K), by simpa⟩
          have hm := Finset.max'_mem S_k ⟨0, h0⟩
          refine ⟨S_k.max' ⟨0, h0⟩, (Finset.mem_filter.mp hm).2, ?_⟩
          by_contra hlt
          push Not at hlt
          have h_succ_lt_K : S_k.max' ⟨0, h0⟩ + 1 ≤ K := by
            by_contra hge
            have hk_ge : K ≤ S_k.max' ⟨0, h0⟩ := by omega
            have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (S_k.max' ⟨0, h0⟩) :=
              pow_le_pow_right₀ one_le_two hk_ge
            linarith [(Finset.mem_filter.mp hm).2]
          have hmem_succ : S_k.max' ⟨0, h0⟩ + 1 ∈ S_k :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlt⟩
          have hle_max := Finset.le_max' S_k _ hmem_succ
          omega
        obtain ⟨k, hk1, hk2⟩ := hex_k
        have hk_lt_K : k < K := by
          by_contra hk_ge
          have hk_ge' : K ≤ k := not_lt.mp hk_ge
          have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ one_le_two hk_ge'
          linarith
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk_lt_K,
          Finset.mem_filter.mpr ⟨hn, hk1, hk2⟩⟩
      have hsum_shells : ∑ n ∈ u_big, ‖a n‖ ^ (-σ : ℝ) ≤
          ∑ k ∈ Finset.range K, ∑ n ∈ shell k, ‖a n‖ ^ (-σ : ℝ) := by
        calc
          ∑ n ∈ u_big, ‖a n‖ ^ (-σ : ℝ)
            ≤ ∑ n ∈ (Finset.range K).biUnion shell, ‖a n‖ ^ (-σ : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_u fun _ _ _ ↦
                Real.rpow_nonneg (norm_nonneg _) _
          _ = ∑ k ∈ Finset.range K, ∑ n ∈ shell k, ‖a n‖ ^ (-σ : ℝ) :=
              Finset.sum_biUnion hdisj
      have hshell_term : ∀ k ∈ Finset.range K,
          ∑ n ∈ shell k, ‖a n‖ ^ (-σ : ℝ) ≤ C_shell * r_geom ^ k := by
        intro k _
        have hcard : (shell k).card ≤ zeroCount f 0 ((2 : ℝ) ^ (k + 1)) := by
          refine card_finset_le_zeroCount_of_enumeration hf hf0 ha_ne ha_fin ha_card
            (by positivity) fun n hn ↦ (Finset.mem_filter.mp hn).2.2.le
        have h2k_ge : 1 ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ one_le_two
        have hcard_r : ((shell k).card : ℝ) ≤ C * ((2 : ℝ) ^ (k + 1)) ^ (ρ + δ) :=
          (Nat.cast_le.mpr hcard).trans (hzc ((2 : ℝ) ^ (k + 1)) h2k_ge)
        have h_pow_split : ((2 : ℝ) ^ (k + 1)) ^ (ρ + δ) =
            (2 : ℝ) ^ (ρ + δ) * ((2 : ℝ) ^ k) ^ (ρ + δ) := by
          rw [pow_succ', Real.mul_rpow (by positivity) (by positivity)]
        have h_term_le : ∀ n ∈ shell k, ‖a n‖ ^ (-σ : ℝ) ≤ ((2 : ℝ) ^ k) ^ (-σ : ℝ) := by
          intro n hn
          have hlo : (2 : ℝ) ^ k ≤ ‖a n‖ := (Finset.mem_filter.mp hn).2.1
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)
        have hsum_le_card : ∑ n ∈ shell k, ‖a n‖ ^ (-σ : ℝ) ≤
            ((shell k).card : ℝ) * ((2 : ℝ) ^ k) ^ (-σ : ℝ) := by
          calc
            ∑ n ∈ shell k, ‖a n‖ ^ (-σ : ℝ)
              ≤ ∑ _n ∈ shell k, ((2 : ℝ) ^ k) ^ (-σ : ℝ) := Finset.sum_le_sum h_term_le
            _ = ((shell k).card : ℝ) * ((2 : ℝ) ^ k) ^ (-σ : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have h_exp_prod : ((2 : ℝ) ^ k) ^ (ρ + δ) * ((2 : ℝ) ^ k) ^ (-σ : ℝ) = r_geom ^ k := by
          have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
          rw [← Real.rpow_add h2k_pos]
          have hexp : (ρ + δ) + (-σ) = -δ := by simp only [δ]; ring
          rw [hexp, ← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul zero_le_two,
            mul_comm (k : ℝ) (-δ), Real.rpow_mul zero_le_two, Real.rpow_natCast]
        calc
          ∑ n ∈ shell k, ‖a n‖ ^ (-σ : ℝ)
            ≤ ((shell k).card : ℝ) * ((2 : ℝ) ^ k) ^ (-σ : ℝ) := hsum_le_card
          _ ≤ (C * ((2 : ℝ) ^ (k + 1)) ^ (ρ + δ)) * ((2 : ℝ) ^ k) ^ (-σ : ℝ) :=
              mul_le_mul_of_nonneg_right hcard_r (Real.rpow_nonneg (by positivity) _)
          _ = C_shell * (((2 : ℝ) ^ k) ^ (ρ + δ) * ((2 : ℝ) ^ k) ^ (-σ : ℝ)) := by
              rw [h_pow_split]; simp only [C_shell]; ring
          _ = C_shell * r_geom ^ k := by rw [h_exp_prod]
      have hgeom : ∑ k ∈ Finset.range K, C_shell * r_geom ^ k ≤ C_shell / (1 - r_geom) := by
        rw [← Finset.mul_sum]
        have hle := (summable_geometric_of_lt_one hr_geom_pos.le hr_geom_lt).sum_le_tsum
          (Finset.range K) (fun k _ ↦ pow_nonneg hr_geom_pos.le k)
        rw [tsum_geometric_of_lt_one hr_geom_pos.le hr_geom_lt] at hle
        exact (mul_le_mul_of_nonneg_left hle hC_shell_nonneg).trans_eq
          (div_eq_mul_inv C_shell (1 - r_geom)).symm
      exact (hsum_shells.trans (Finset.sum_le_sum hshell_term)).trans hgeom
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty]
      exact div_nonneg hC_shell_nonneg (sub_nonneg.mpr hr_geom_lt.le)
  rw [hu_split]
  exact add_le_add hu_small_le hu_big_le

/-- Under the hypotheses of `summable_norm_rpow_neg_of_enumeration`, the exponent of convergence
of the zero sequence is at most the order `ρ` of `f`. -/
theorem convergenceExponent_le_of_enumeration {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ) (hf0 : f 0 ≠ 0)
    {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0) (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) :
    convergenceExponent a ≤ ρ := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-(ρ + ε) : ℝ)) :=
    summable_norm_rpow_neg_of_enumeration hf hρ hord hf0 (by linarith) ha_ne ha_fin ha_card
  have hnonneg : 0 ≤ ρ + ε := by linarith
  exact convergenceExponent_le hnonneg hsum

/-- Analytic order of a convergent canonical product `canonicalProduct a p`: at `0` the order is
`0`, and at any `z ≠ 0` the order equals the multiplicity `{n : ℕ | a n = z}.ncard`. -/
theorem analyticOrderNatAt_canonicalProduct_eq {a : ℕ → ℂ} {p : ℕ}
    (ha_ne : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)))) :
    analyticOrderNatAt (canonicalProduct a p) 0 = 0 ∧
      (∀ z ≠ 0, analyticOrderNatAt (canonicalProduct a p) z = ({n : ℕ | a n = z}).ncard) := by
  have hdiff_all := differentiable_canonicalProduct ha_ne hsum
  have han_all : AnalyticOnNhd ℂ (canonicalProduct a p) univ :=
    hdiff_all.differentiableOn.analyticOnNhd isOpen_univ
  have h0_val : canonicalProduct a p 0 = 1 := by
    simp [canonicalProduct, weierstrassPrimaryFactor_at_zero]
  have h0_ord : analyticOrderNatAt (canonicalProduct a p) 0 = 0 := by
    have : analyticOrderAt (canonicalProduct a p) 0 = 0 :=
      (han_all 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr (by rw [h0_val]; exact one_ne_zero)
    simp [analyticOrderNatAt, this]
  refine ⟨h0_ord, fun z hzc ↦ ?_⟩
  have htend := tendsto_norm_atTop_of_summable ha_ne (Nat.cast_pos.mpr (Nat.succ_pos p)) hsum
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop (2 * (‖z‖ + 1)))
  let a_shift : ℕ → ℂ := fun k ↦ a (k + N)
  let tail : ℂ → ℂ := canonicalProduct a_shift p
  let head : ℂ → ℂ := fun w ↦ ∏ n ∈ Finset.range N, weierstrassPrimaryFactor p (w / a n)
  have ha_shift_ne : ∀ k : ℕ, a_shift k ≠ 0 := fun k ↦ ha_ne (k + N)
  have hsum_shift : Summable (fun k : ℕ ↦ ‖a_shift k‖ ^ (-((p + 1 : ℕ) : ℝ))) :=
    (summable_nat_add_iff N).mpr hsum
  have h_eq : canonicalProduct a p = fun w ↦ head w * tail w := by
    ext w
    have hm_shift : Multipliable (fun k : ℕ ↦ weierstrassPrimaryFactor p (w / a (k + N))) :=
      multipliable_canonicalProduct ha_shift_ne hsum_shift w
    dsimp only [canonicalProduct, head, tail, a_shift]
    exact (Multipliable.prod_mul_tprod_nat_mul'
      (f := fun n ↦ weierstrassPrimaryFactor p (w / a n)) (k := N) hm_shift).symm
  have htail_diff : Differentiable ℂ tail := differentiable_canonicalProduct ha_shift_ne hsum_shift
  have htail_an : AnalyticAt ℂ tail z :=
    (htail_diff.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)
  have htail_ne_z : tail z ≠ 0 := by
    intro hzero
    rw [canonicalProduct_eq_zero_iff ha_shift_ne hsum_shift] at hzero
    obtain ⟨k, hk⟩ := hzero
    change z = a (k + N) at hk
    have hk_ge := hN (k + N) (Nat.le_add_left N k)
    rw [← hk] at hk_ge
    linarith [norm_nonneg z]
  have htail_top : analyticOrderAt tail z ≠ ⊤ := by
    rw [htail_an.analyticOrderAt_eq_zero.mpr htail_ne_z]; simp
  have htail_ord : analyticOrderNatAt tail z = 0 := by
    have : analyticOrderAt tail z = 0 := htail_an.analyticOrderAt_eq_zero.mpr htail_ne_z
    simp [analyticOrderNatAt, this]
  have hfac_diff : ∀ n : ℕ, Differentiable ℂ (fun w ↦ weierstrassPrimaryFactor p (w / a n)) := fun n ↦
    (differentiable_weierstrassPrimaryFactor p).comp (differentiable_id.div_const (a n))
  have hfac_an : ∀ n : ℕ, AnalyticAt ℂ (fun w ↦ weierstrassPrimaryFactor p (w / a n)) z := fun n ↦
    ((hfac_diff n).differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)
  have hfac_top : ∀ n : ℕ, analyticOrderAt (fun w ↦ weierstrassPrimaryFactor p (w / a n)) z ≠ ⊤ := by
    intro n
    refine analyticOrderAt_ne_top_of_differentiable_ne_zero (hfac_diff n) ?_ z
    intro h0
    have := congrFun h0 0
    simp [weierstrassPrimaryFactor_at_zero] at this
  have hfac_ord : ∀ n : ℕ, analyticOrderNatAt (fun w ↦ weierstrassPrimaryFactor p (w / a n)) z =
      if a n = z then 1 else 0 := by
    intro n
    by_cases hanz : a n = z
    · rw [ite_eq_left_iff.mpr fun h ↦ False.elim (h hanz)]
      let g_fac : ℂ → ℂ := fun w ↦
        (-(1 / a n)) * Complex.exp (∑ k ∈ Finset.Icc 1 p, (w / a n) ^ k / (k : ℂ))
      have hg_an : AnalyticAt ℂ g_fac z := by
        have hg_diff : Differentiable ℂ g_fac := by
          refine differentiable_const _ |>.mul (Differentiable.cexp ?_)
          exact Differentiable.fun_sum fun k _ ↦ ((differentiable_id.div_const _).pow k).div_const _
        exact (hg_diff.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)
      have hg_ne : g_fac z ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero (ha_ne n))) (Complex.exp_ne_zero _)
      have hprod_fac : ∀ w : ℂ, weierstrassPrimaryFactor p (w / a n) = (w - z) ^ 1 * g_fac w := by
        intro w
        simp only [weierstrassPrimaryFactor, pow_one, g_fac]
        have h1w : 1 - w / a n = (w - z) * (-(1 / a n)) := by
          rw [hanz]
          field_simp [hzc]
          ring
        rw [h1w, mul_assoc]
      exact ((hfac_an n).analyticOrderNatAt_eq_iff (hfac_top n)).mpr
        ⟨g_fac, hg_an, hg_ne, Filter.Eventually.of_forall fun w ↦ by
          simpa [smul_eq_mul] using hprod_fac w⟩
    · rw [ite_eq_right_iff.mpr fun h ↦ False.elim (hanz h)]
      have hne_z : weierstrassPrimaryFactor p (z / a n) ≠ 0 := by
        rw [ne_eq, weierstrassPrimaryFactor_eq_zero_iff, div_eq_one_iff_eq (ha_ne n)]
        exact Ne.symm hanz
      have : analyticOrderAt (fun w ↦ weierstrassPrimaryFactor p (w / a n)) z = 0 :=
        (hfac_an n).analyticOrderAt_eq_zero.mpr hne_z
      simp [analyticOrderNatAt, this]
  have hhead_ord_sum : ∀ s : Finset ℕ,
      AnalyticAt ℂ (fun w ↦ ∏ n ∈ s, weierstrassPrimaryFactor p (w / a n)) z ∧
      analyticOrderAt (fun w ↦ ∏ n ∈ s, weierstrassPrimaryFactor p (w / a n)) z ≠ ⊤ ∧
      analyticOrderNatAt (fun w ↦ ∏ n ∈ s, weierstrassPrimaryFactor p (w / a n)) z =
        ∑ n ∈ s, (if a n = z then 1 else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨analyticAt_const, ?_, ?_⟩
      · simp
      · simp
    | insert n s hns ih =>
      have hmul_eq : (fun w ↦ ∏ i ∈ insert n s, weierstrassPrimaryFactor p (w / a i)) =
          fun w ↦ weierstrassPrimaryFactor p (w / a n) *
            ∏ i ∈ s, weierstrassPrimaryFactor p (w / a i) := by
        ext w; exact Finset.prod_insert hns
      rw [hmul_eq]
      refine ⟨(hfac_an n).mul ih.1, ?_, ?_⟩
      · rw [analyticOrderAt_fun_mul (hfac_an n) ih.1]
        simp [hfac_top n, ih.2.1]
      · rw [analyticOrderNatAt_fun_mul (hfac_an n) ih.1 (hfac_top n) ih.2.1, ih.2.2, hfac_ord n,
          Finset.sum_insert hns]
  obtain ⟨hhead_an, hhead_top, hhead_ord⟩ := hhead_ord_sum (Finset.range N)
  have hprod_ord : analyticOrderNatAt (canonicalProduct a p) z =
      ∑ n ∈ Finset.range N, (if a n = z then 1 else 0) := by
    rw [h_eq, analyticOrderNatAt_fun_mul hhead_an htail_an hhead_top htail_top, htail_ord, add_zero]
    exact hhead_ord
  have hset_eq : ({n : ℕ | a n = z} : Set ℕ) =
      ((Finset.range N).filter (fun n ↦ a n = z) : Finset ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨fun hanz ↦ ⟨?_, hanz⟩, fun h ↦ h.2⟩
    by_contra hge
    have hn_ge : N ≤ n := not_lt.mp hge
    have hnorm := hN n hn_ge
    rw [hanz] at hnorm
    linarith [norm_nonneg z]
  rw [hprod_ord, hset_eq, Set.ncard_coe_finset, Finset.card_filter]

/-- **Order bound for canonical products of genus `p` when `p ≤ ρ` and `convergenceExponent a ≤ ρ`**
(without requiring `ρ ≤ p + 1`): if `∑ ‖a n‖ ^ (-(p + 1))` converges, then
`EntireOrderLe (canonicalProduct a p) ρ`. -/
theorem entireOrderLe_canonicalProduct_of_convergenceExponent_le {a : ℕ → ℂ} {p : ℕ} {ρ : ℝ}
    (ha : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))))
    (hpρ : (p : ℝ) ≤ ρ) (hconv : convergenceExponent a ≤ ρ) :
    EntireOrderLe (canonicalProduct a p) ρ := by
  let σ : ℝ := min ρ ((p : ℝ) + 1)
  have hconv_p1 : convergenceExponent a ≤ (p : ℝ) + 1 := by
    have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; rfl
    rw [← hcast]
    exact convergenceExponent_le (Nat.cast_nonneg _) hsum
  have h_ord_σ : EntireOrderLe (canonicalProduct a p) σ :=
    entireOrderLe_canonicalProduct ha hsum (le_min hpρ (by linarith)) (min_le_right _ _)
      (le_min hconv hconv_p1)
  exact h_ord_σ.mono (min_le_left _ _)

/-- **Order bound for canonical products at the floor genus `p = ⌊convergenceExponent a⌋₊`**:
if `convergenceExponent a ≤ ρ` and `∑ ‖a n‖ ^ (-(⌊convergenceExponent a⌋₊ + 1))` converges, then
`EntireOrderLe (canonicalProduct a ⌊convergenceExponent a⌋₊) ρ`. -/
theorem entireOrderLe_canonicalProduct_floor {a : ℕ → ℂ} {ρ : ℝ}
    (ha : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n : ℕ ↦
      ‖a n‖ ^ (-((Nat.floor (convergenceExponent a) + 1 : ℕ) : ℝ))))
    (hconv : convergenceExponent a ≤ ρ) :
    EntireOrderLe (canonicalProduct a (Nat.floor (convergenceExponent a))) ρ :=
  entireOrderLe_canonicalProduct_of_convergenceExponent_le ha hsum
    ((Nat.floor_le (convergenceExponent_nonneg a)).trans hconv) hconv

/-- **Exact order of a canonical product equals the exponent of convergence**: when
`∀ n, a n ≠ 0`, norm-bounded subfamilies of `a` are finite, `∑ ‖a n‖ ^ (-(p + 1))` converges,
and `(p : ℝ) ≤ convergenceExponent a`, we have `exactOrder (canonicalProduct a p) = convergenceExponent a`. -/
theorem exactOrder_canonicalProduct_eq_convergenceExponent {a : ℕ → ℂ} {p : ℕ}
    (ha_ne : ∀ n, a n ≠ 0) (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))))
    (hp_le : (p : ℝ) ≤ convergenceExponent a) :
    exactOrder (canonicalProduct a p) = convergenceExponent a := by
  have hdiff := differentiable_canonicalProduct ha_ne hsum
  have hfin_order : HasFiniteOrder (canonicalProduct a p) :=
    ⟨convergenceExponent a, convergenceExponent_nonneg a,
      entireOrderLe_canonicalProduct_convergenceExponent ha_ne hsum hp_le⟩
  have h0_val : canonicalProduct a p 0 ≠ 0 := by
    simp [canonicalProduct, weierstrassPrimaryFactor_at_zero]
  have h_le : exactOrder (canonicalProduct a p) ≤ convergenceExponent a :=
    exactOrder_le (convergenceExponent_nonneg a)
      (entireOrderLe_canonicalProduct_convergenceExponent ha_ne hsum hp_le)
  have h_ge : convergenceExponent a ≤ exactOrder (canonicalProduct a p) := by
    refine convergenceExponent_le_of_enumeration hdiff (exactOrder_nonneg _)
      (entireOrderLe_exactOrder hfin_order) h0_val ha_ne ha_fin ?_
    intro z hzc
    exact ((analyticOrderNatAt_canonicalProduct_eq ha_ne hsum).2 z hzc).symm
  exact le_antisymm h_le h_ge

/-!
### Section 4: Minimum-Modulus Lower Bounds on Avoiding Circles
-/

private lemma real_exp_neg_two_mul_le_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1t_pos : 0 < 1 - t := by linarith
  have h1t_ge : 1 / 2 ≤ 1 - t := by linarith
  have hdiv_le : t / (1 - t) ≤ 2 * t := by
    calc
      t / (1 - t) ≤ t / (1 / 2) := div_le_div_of_nonneg_left ht0 (by norm_num) h1t_ge
      _ = 2 * t := by ring
  have h_exp : 1 + t / (1 - t) ≤ Real.exp (t / (1 - t)) := by
    linarith [Real.add_one_le_exp (t / (1 - t))]
  have h_inv_eq : (1 + t / (1 - t))⁻¹ = 1 - t := by
    have h1p : 1 + t / (1 - t) = 1 / (1 - t) := by
      field_simp [h1t_pos.ne']
      ring
    rw [h1p, one_div, inv_inv]
  have h_inv : (Real.exp (t / (1 - t)))⁻¹ ≤ (1 + t / (1 - t))⁻¹ :=
    inv_anti₀ (by positivity) h_exp
  rw [← Real.exp_neg, h_inv_eq] at h_inv
  exact (Real.exp_le_exp.mpr (by linarith)).trans h_inv

/-- For `‖u‖ ≤ 1 / 4` and any `p : ℕ`, the primary factor satisfies the lower bound
`Real.exp (-4 * ‖u‖ ^ (p + 1)) ≤ ‖weierstrassPrimaryFactor p u‖`. -/
theorem norm_weierstrassPrimaryFactor_ge_exp_of_norm_le_quarter (p : ℕ) {u : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) :
    Real.exp (-4 * ‖u‖ ^ (p + 1)) ≤ ‖weierstrassPrimaryFactor p u‖ := by
  have hu_half : ‖u‖ ≤ 1 / 2 := hu.trans (by norm_num)
  have hdiff := norm_one_sub_weierstrassPrimaryFactor_le p hu_half
  have hpow_le : ‖u‖ ^ (p + 1) ≤ ‖u‖ := by
    calc
      ‖u‖ ^ (p + 1) = ‖u‖ * ‖u‖ ^ p := by rw [pow_succ']
      _ ≤ ‖u‖ * 1 ^ p := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg u) (hu.trans (by norm_num)) p) (norm_nonneg u)
      _ = ‖u‖ := by simp
  let t : ℝ := 2 * ‖u‖ ^ (p + 1)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 2 := by dsimp only [t]; linarith
  have hexp : Real.exp (-4 * ‖u‖ ^ (p + 1)) ≤ 1 - t := by
    convert real_exp_neg_two_mul_le_one_sub ht0 ht1 using 2
    dsimp only [t]; ring
  have hnorm : 1 - ‖1 - weierstrassPrimaryFactor p u‖ ≤ ‖weierstrassPrimaryFactor p u‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (1 - weierstrassPrimaryFactor p u)
    simpa using htri
  exact hexp.trans ((sub_le_sub_left hdiff 1).trans hnorm)

/-- **Interval pigeonhole avoiding finite points**: for any `S : Finset ℕ`, `f : ℕ → ℝ`, and `0 < R`,
there exists `r ∈ Set.Icc R (2 * R)` such that `R / (2 * ((S.card : ℝ) + 1)) ≤ |r - f n|` for all
`n ∈ S`. -/
theorem exists_radius_mem_Icc_avoiding (S : Finset ℕ) (f : ℕ → ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Icc R (2 * R), ∀ n ∈ S, R / (2 * ((S.card : ℝ) + 1)) ≤ |r - f n| := by
  classical
  let N : ℕ := S.card
  let L : ℝ := R / ((N : ℝ) + 1)
  have hL_pos : 0 < L := div_pos hR (by positivity)
  let c : ℕ → ℝ := fun j ↦ R + ((j : ℝ) + 1 / 2) * L
  by_contra hnone
  push Not at hnone
  have hbad : ∀ j ∈ Finset.range (N + 1), ∃ n ∈ S, |c j - f n| < L / 2 := by
    intro j hj
    have hj_le : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hc_mem : c j ∈ Set.Icc R (2 * R) := by
      refine ⟨?_, ?_⟩
      · dsimp only [c]; linarith [mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 / 2 by positivity) hL_pos.le]
      · have hj_real : (j : ℝ) + 1 / 2 ≤ (N : ℝ) + 1 := by
          have : (j : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hj_le
          linarith
        have hmul : ((j : ℝ) + 1 / 2) * L ≤ ((N : ℝ) + 1) * L :=
          mul_le_mul_of_nonneg_right hj_real hL_pos.le
        have hNL : ((N : ℝ) + 1) * L = R := by
          dsimp only [L]
          field_simp [(show (N : ℝ) + 1 ≠ 0 by positivity)]
        dsimp only [c]
        linarith
    obtain ⟨n, hnS, hlt⟩ := hnone (c j) hc_mem
    refine ⟨n, hnS, hlt.trans_eq ?_⟩
    dsimp only [L, N]
    rw [div_div, mul_comm ((S.card : ℝ) + 1) 2]
  let φ : ℕ → ℕ := fun j ↦ if hj : j ∈ Finset.range (N + 1) then (hbad j hj).choose else 0
  have hφ_mem : ∀ j ∈ Finset.range (N + 1), φ j ∈ S := by
    intro j hj
    dsimp only [φ]
    split_ifs
    exact (hbad j hj).choose_spec.1
  have hφ_dist : ∀ j ∈ Finset.range (N + 1), |c j - f (φ j)| < L / 2 := by
    intro j hj
    dsimp only [φ]
    split_ifs
    exact (hbad j hj).choose_spec.2
  have hφ_inj : Set.InjOn φ (Finset.range (N + 1)) := by
    intro j₁ hj₁ j₂ hj₂ heq
    by_contra hne
    have htri : |c j₁ - c j₂| < L := by
      have hsub : c j₁ - c j₂ = (c j₁ - f (φ j₁)) - (c j₂ - f (φ j₂)) := by rw [heq]; ring
      rw [hsub]
      calc
        |(c j₁ - f (φ j₁)) - (c j₂ - f (φ j₂))|
          ≤ |c j₁ - f (φ j₁)| + |c j₂ - f (φ j₂)| := abs_sub _ _
        _ < L / 2 + L / 2 := add_lt_add (hφ_dist j₁ hj₁) (hφ_dist j₂ hj₂)
        _ = L := by ring
    have hdiff : L ≤ |c j₁ - c j₂| := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 : (1 : ℝ) ≤ (j₂ : ℝ) - (j₁ : ℝ) := by
          have : ((j₁ + 1 : ℕ) : ℝ) ≤ (j₂ : ℝ) := Nat.cast_le.mpr hlt
          push_cast at this
          linarith
        have hpos : c j₂ - c j₁ = ((j₂ : ℝ) - (j₁ : ℝ)) * L := by dsimp only [c]; ring
        have hge : L ≤ c j₂ - c j₁ := by
          rw [hpos]
          exact le_mul_of_one_le_left hL_pos.le h1
        rw [abs_sub_comm]
        exact hge.trans (le_abs_self _)
      · have h1 : (1 : ℝ) ≤ (j₁ : ℝ) - (j₂ : ℝ) := by
          have : ((j₂ + 1 : ℕ) : ℝ) ≤ (j₁ : ℝ) := Nat.cast_le.mpr hgt
          push_cast at this
          linarith
        have hpos : c j₁ - c j₂ = ((j₁ : ℝ) - (j₂ : ℝ)) * L := by dsimp only [c]; ring
        have hge : L ≤ c j₁ - c j₂ := by
          rw [hpos]
          exact le_mul_of_one_le_left hL_pos.le h1
        exact hge.trans (le_abs_self _)
    linarith
  have hcard := Finset.card_le_card_of_injOn φ hφ_mem hφ_inj
  rw [Finset.card_range] at hcard
  omega

private lemma real_log_le_rpow_div {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    Real.log x ≤ x ^ η / η := by
  have h1 : Real.log (x ^ η) ≤ x ^ η - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx η)
  rw [Real.log_rpow hx] at h1
  rw [le_div_iff₀ hη]
  linarith

/-- **Canonical product minimum-modulus bound on avoiding circles**: if `f` is entire of order at
most `ρ` with `f 0 ≠ 0`, `a : ℕ → ℂ` enumerates the zeros of `f` with multiplicity, and
`max ρ (p : ℝ) < α < (p : ℝ) + 1`, then there exists `C > 0` such that for arbitrarily large `R`,
some circle `Metric.sphere 0 r` with `r ∈ Set.Icc R (2 * R)` satisfies
`Real.exp (-C * r ^ α) ≤ ‖canonicalProduct a p z‖` for all `z ∈ Metric.sphere 0 r`. -/
theorem exists_circle_canonicalProduct_lower_bound {f : ℂ → ℂ} {p : ℕ} {ρ α : ℝ}
    (hf : Differentiable ℂ f) (hord : EntireOrderLe f ρ) (hf0 : f 0 ≠ 0)
    (hρ_lt : ρ < α) (hp_lt : (p : ℝ) < α) (hα_lt : α < (p : ℝ) + 1)
    {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0) (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) :
    ∃ C > 0, ∀ᶠ R : ℝ in atTop, ∃ r ∈ Set.Icc R (2 * R),
      ∀ z ∈ Metric.sphere (0 : ℂ) r, Real.exp (-C * r ^ α) ≤ ‖canonicalProduct a p z‖ := by
  classical
  let ρ' : ℝ := max ρ (p : ℝ)
  have hord' : EntireOrderLe f ρ' := hord.mono (le_max_left ρ (p : ℝ))
  have hρ'_lt : ρ' < α := max_lt hρ_lt hp_lt
  have hρ'_nonneg : 0 ≤ ρ' := le_max_of_le_right (Nat.cast_nonneg p)
  let s : ℝ := (ρ' + α) / 2
  have hs_gt : ρ' < s := by dsimp only [s]; linarith
  have hs_lt : s < α := by dsimp only [s]; linarith
  have hs_pos : 0 < s := hρ'_nonneg.trans_lt hs_gt
  have hp_le_s : (p : ℝ) ≤ s := (le_max_right ρ (p : ℝ)).trans hs_gt.le
  have hs_le_p1 : s ≤ (p : ℝ) + 1 := hs_lt.le.trans hα_lt.le
  have hsum_s : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-s : ℝ)) :=
    summable_norm_rpow_neg_of_enumeration hf hρ'_nonneg hord' hf0 hs_gt ha_ne ha_fin ha_card
  have hsum_p1 : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))) := by
    have hle : s ≤ ((p + 1 : ℕ) : ℝ) := by exact_mod_cast hs_le_p1
    exact summable_norm_rpow_neg_of_le ha_ne hs_pos hle hsum_s
  let S_sum : ℝ := ∑' n : ℕ, ‖a n‖ ^ (-s : ℝ)
  have hS_sum_nonneg : 0 ≤ S_sum := tsum_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  let δ : ℝ := (α - ρ') / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  let η : ℝ := (α - (ρ' + δ)) / (ρ' + δ)
  have hρδ_pos : 0 < ρ' + δ := by linarith
  have hη_pos : 0 < η := div_pos (by dsimp only [δ]; linarith) hρδ_pos
  obtain ⟨C_J, _, hzc⟩ := zeroCount_le_rpow_of_entireOrderLe hf hρ'_nonneg hord' hf0 hδ
  let C₁ : ℝ := C_J * (8 : ℝ) ^ (ρ' + δ)
  have hC₁_pos : 0 < C₁ := by positivity
  let C₂ : ℝ := (16 * (C₁ + 1)) ^ η / η
  have hC₂_nonneg : 0 ≤ C₂ := by positivity
  let C_poly : ℝ := C₁ * C₂
  let C_tail : ℝ := 4 * S_sum
  let C_exp : ℝ := (p : ℝ) * (8 : ℝ) ^ s * S_sum
  let C_tot : ℝ := C_tail + C_exp + C_poly + 1
  have hC_tot_pos : 0 < C_tot := by positivity
  refine ⟨C_tot, hC_tot_pos, Filter.eventually_atTop.mpr ⟨1, fun R hR ↦ ?_⟩⟩
  have hR_pos : 0 < R := zero_lt_one.trans_le hR
  let S_R : Finset ℕ := (ha_fin (8 * R)).toFinset
  obtain ⟨r, hr_mem, hr_avoid⟩ := exists_radius_mem_Icc_avoiding S_R (fun n ↦ ‖a n‖) hR_pos
  have hr_ge : R ≤ r := hr_mem.1
  have hr_le : r ≤ 2 * R := hr_mem.2
  have hr_ge_one : 1 ≤ r := hR.trans hr_ge
  have hr_pos : 0 < r := zero_lt_one.trans_le hr_ge_one
  refine ⟨r, hr_mem, fun z hz ↦ ?_⟩
  have hz_norm : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
  have hm := multipliable_canonicalProduct ha_ne hsum_p1 z
  rw [canonicalProduct, hm.norm_tprod]
  have htend_norm : Tendsto (fun M : ℕ ↦ ∏ n ∈ Finset.range M, ‖weierstrassPrimaryFactor p (z / a n)‖)
      atTop (𝓝 (∏' n : ℕ, ‖weierstrassPrimaryFactor p (z / a n)‖)) :=
    hm.norm.hasProd.tendsto_prod_nat
  have hex_M₀ : ∃ M₀ : ℕ, S_R ⊆ Finset.range M₀ :=
    ⟨S_R.sup id + 1, fun n hn ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩
  obtain ⟨M₀, hM₀⟩ := hex_M₀
  refine ge_of_tendsto htend_norm (Filter.eventually_atTop.mpr ⟨M₀, fun M hM ↦ ?_⟩)
  have hS_sub_M : S_R ⊆ Finset.range M := hM₀.trans (Finset.range_mono hM)
  rw [← Finset.prod_sdiff hS_sub_M]
  have htail_ge : Real.exp (-C_tail * r ^ α) ≤
      ∏ n ∈ Finset.range M \ S_R, ‖weierstrassPrimaryFactor p (z / a n)‖ := by
    have hfac_ge : ∀ n ∈ Finset.range M \ S_R,
        Real.exp (-4 * r ^ s * ‖a n‖ ^ (-s : ℝ)) ≤ ‖weierstrassPrimaryFactor p (z / a n)‖ := by
      intro n hn
      have hn_not : n ∉ S_R := (Finset.mem_sdiff.mp hn).2
      have han_gt : 8 * R < ‖a n‖ := by
        by_contra hle
        apply hn_not
        dsimp only [S_R]
        rw [Set.Finite.mem_toFinset]
        exact not_lt.mp hle
      have han_pos : 0 < ‖a n‖ := by linarith
      have hu_norm : ‖z / a n‖ ≤ 1 / 4 := by
        rw [norm_div, hz_norm, div_le_iff₀ han_pos]
        linarith
      have hgeo := norm_weierstrassPrimaryFactor_ge_exp_of_norm_le_quarter p hu_norm
      have hpow_le : ‖z / a n‖ ^ (p + 1) ≤ ‖z / a n‖ ^ s := by
        rcases eq_or_lt_of_le (norm_nonneg (z / a n)) with h0 | hpos
        · rw [← h0, zero_pow (Nat.succ_ne_zero p), Real.zero_rpow hs_pos.ne']
        · rw [← Real.rpow_natCast ‖z / a n‖ (p + 1), Nat.cast_add, Nat.cast_one]
          exact Real.rpow_le_rpow_of_exponent_ge hpos (hu_norm.trans (by norm_num)) hs_le_p1
      have hpow_eq : ‖z / a n‖ ^ s = r ^ s * ‖a n‖ ^ (-s : ℝ) := by
        rw [norm_div, hz_norm, Real.div_rpow hr_pos.le han_pos.le, div_eq_mul_inv,
          ← Real.rpow_neg han_pos.le]
      refine (Real.exp_le_exp.mpr ?_).trans hgeo
      rw [mul_assoc (-4), ← hpow_eq]
      nlinarith
    have hsum_tail_le : ∑ n ∈ Finset.range M \ S_R, 4 * r ^ s * ‖a n‖ ^ (-s : ℝ) ≤ C_tail * r ^ α := by
      have h1 : ∑ n ∈ Finset.range M \ S_R, 4 * r ^ s * ‖a n‖ ^ (-s : ℝ) =
          (4 * r ^ s) * ∑ n ∈ Finset.range M \ S_R, ‖a n‖ ^ (-s : ℝ) := by
        rw [Finset.mul_sum]
      have h2 : ∑ n ∈ Finset.range M \ S_R, ‖a n‖ ^ (-s : ℝ) ≤ S_sum :=
        hsum_s.sum_le_tsum (Finset.range M \ S_R) (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      have hr_pow_cmp : r ^ s ≤ r ^ α := Real.rpow_le_rpow_of_exponent_le hr_ge_one hs_lt.le
      rw [h1]
      calc
        (4 * r ^ s) * ∑ n ∈ Finset.range M \ S_R, ‖a n‖ ^ (-s : ℝ)
          ≤ (4 * r ^ s) * S_sum := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (4 * S_sum) * r ^ s := by ring
        _ ≤ C_tail * r ^ α := mul_le_mul_of_nonneg_left hr_pow_cmp (by positivity)
    calc
      Real.exp (-C_tail * r ^ α)
        ≤ Real.exp (-(∑ n ∈ Finset.range M \ S_R, 4 * r ^ s * ‖a n‖ ^ (-s : ℝ))) := by
            refine Real.exp_le_exp.mpr ?_
            linarith
      _ = Real.exp (∑ n ∈ Finset.range M \ S_R, (-4 * r ^ s * ‖a n‖ ^ (-s : ℝ))) := by
            congr 1
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun n _ ↦ by ring
      _ = ∏ n ∈ Finset.range M \ S_R, Real.exp (-4 * r ^ s * ‖a n‖ ^ (-s : ℝ)) := by
            rw [Real.exp_sum]
      _ ≤ ∏ n ∈ Finset.range M \ S_R, ‖weierstrassPrimaryFactor p (z / a n)‖ :=
            Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) hfac_ge
  have hhead_exp_ge : Real.exp (-C_exp * r ^ α) ≤
      ∏ n ∈ S_R, ‖Complex.exp (∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ))‖ := by
    have hfac_ge : ∀ n ∈ S_R,
        Real.exp (-((p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ))) ≤
          ‖Complex.exp (∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ))‖ := by
      intro n hn
      have han_le : ‖a n‖ ≤ 8 * R := (Set.Finite.mem_toFinset _).mp hn
      have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha_ne n)
      have hn_sum_le : ‖∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ)‖ ≤
          (p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ) := by
        have htri := norm_sum_le (Finset.Icc 1 p) (fun k ↦ (z / a n) ^ k / (k : ℂ))
        refine htri.trans ?_
        have hterm : ∀ k ∈ Finset.Icc 1 p,
            ‖(z / a n) ^ k / (k : ℂ)‖ ≤ (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ) := by
          intro k hk
          simp only [Finset.mem_Icc] at hk
          have hk_pos : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          have hk_le_s : (k : ℝ) ≤ s := by
            have hk_le_p : (k : ℝ) ≤ (p : ℝ) := by exact_mod_cast hk.2
            exact hk_le_p.trans hp_le_s
          have hnorm_le : ‖(z / a n) ^ k / (k : ℂ)‖ ≤
              (r ^ (k : ℝ) * ‖a n‖ ^ (s - k)) * ‖a n‖ ^ (-s : ℝ) := by
            rw [norm_div, norm_pow, norm_div, Complex.norm_natCast, hz_norm]
            refine (div_le_self (by positivity) hk_pos).trans_eq ?_
            have hpow_an : (‖a n‖ ^ k)⁻¹ = ‖a n‖ ^ (s - k) * ‖a n‖ ^ (-s : ℝ) := by
              rw [← Real.rpow_natCast ‖a n‖ k, ← Real.rpow_neg han_pos.le,
                ← Real.rpow_add han_pos]
              congr 2
              ring
            rw [div_eq_mul_inv, mul_pow, inv_pow, hpow_an, ← Real.rpow_natCast r k]
            ring
          have hpow1 : r ^ (k : ℝ) ≤ (8 * r) ^ (k : ℝ) :=
            Real.rpow_le_rpow hr_pos.le (by linarith) (Nat.cast_nonneg k)
          have hpow2 : ‖a n‖ ^ (s - k) ≤ (8 * r) ^ (s - k) :=
            Real.rpow_le_rpow han_pos.le (han_le.trans (by linarith)) (sub_nonneg.mpr hk_le_s)
          have hpow_mul : r ^ (k : ℝ) * ‖a n‖ ^ (s - k) ≤ (8 * r) ^ s := by
            refine (mul_le_mul hpow1 hpow2 (Real.rpow_nonneg han_pos.le _) (by positivity)).trans_eq ?_
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < 8 * r)]
            congr 2
            ring
          exact hnorm_le.trans (mul_le_mul_of_nonneg_right hpow_mul (Real.rpow_nonneg han_pos.le _))
        calc
          ∑ k ∈ Finset.Icc 1 p, ‖(z / a n) ^ k / (k : ℂ)‖
            ≤ ∑ _k ∈ Finset.Icc 1 p, (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ) := Finset.sum_le_sum hterm
          _ = (p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ) := by
              rw [Finset.sum_const, Nat.card_Icc]
              simp [nsmul_eq_mul, mul_assoc]
      rw [Complex.norm_exp, Real.exp_le_exp]
      have hre := neg_le_abs (∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ)).re
      have habs := Complex.abs_re_le_norm (∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ))
      linarith
    have hsum_exp_le : ∑ n ∈ S_R, (p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ) ≤ C_exp * r ^ α := by
      have h1 : ∑ n ∈ S_R, (p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ) =
          ((p : ℝ) * (8 * r) ^ s) * ∑ n ∈ S_R, ‖a n‖ ^ (-s : ℝ) := by
        rw [Finset.mul_sum]
      have h2 : ∑ n ∈ S_R, ‖a n‖ ^ (-s : ℝ) ≤ S_sum :=
        hsum_s.sum_le_tsum S_R (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      have hmul8 : (8 * r) ^ s = (8 : ℝ) ^ s * r ^ s := Real.mul_rpow (by positivity) hr_pos.le
      have hr_pow_cmp : r ^ s ≤ r ^ α := Real.rpow_le_rpow_of_exponent_le hr_ge_one hs_lt.le
      rw [h1]
      calc
        ((p : ℝ) * (8 * r) ^ s) * ∑ n ∈ S_R, ‖a n‖ ^ (-s : ℝ)
          ≤ ((p : ℝ) * (8 * r) ^ s) * S_sum := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ((p : ℝ) * (8 : ℝ) ^ s * S_sum) * r ^ s := by rw [hmul8]; ring
        _ ≤ C_exp * r ^ α := mul_le_mul_of_nonneg_left hr_pow_cmp (by positivity)
    calc
      Real.exp (-C_exp * r ^ α)
        ≤ Real.exp (-(∑ n ∈ S_R, (p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ))) := by
            refine Real.exp_le_exp.mpr ?_
            linarith
      _ = Real.exp (∑ n ∈ S_R, -((p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ))) := by
            congr 1
            rw [← Finset.sum_neg_distrib]
      _ = ∏ n ∈ S_R, Real.exp (-((p : ℝ) * (8 * r) ^ s * ‖a n‖ ^ (-s : ℝ))) := by
            rw [Real.exp_sum]
      _ ≤ ∏ n ∈ S_R, ‖Complex.exp (∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ))‖ :=
            Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) hfac_ge
  have hhead_poly_ge : Real.exp (-C_poly * r ^ α) ≤ ∏ n ∈ S_R, ‖1 - z / a n‖ := by
    let x_base : ℝ := 16 * ((S_R.card : ℝ) + 1)
    have hx_pos : 0 < x_base := by positivity
    have hfac_poly : ∀ n ∈ S_R, 1 / x_base ≤ ‖1 - z / a n‖ := by
      intro n hn
      have han_le : ‖a n‖ ≤ 8 * R := (Set.Finite.mem_toFinset _).mp hn
      have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha_ne n)
      have h1sub : 1 - z / a n = (a n - z) / a n := by field_simp [ha_ne n]
      have hnum : R / (2 * ((S_R.card : ℝ) + 1)) ≤ ‖a n - z‖ := by
        have htri : |r - ‖a n‖| ≤ ‖a n - z‖ := by
          rw [← hz_norm, norm_sub_rev (a n) z]
          exact abs_norm_sub_norm_le z (a n)
        exact (hr_avoid n hn).trans htri
      rw [h1sub, norm_div]
      calc
        1 / x_base = (R / (2 * ((S_R.card : ℝ) + 1))) / (8 * R) := by
          dsimp only [x_base]
          field_simp [hR_pos.ne', (show (S_R.card : ℝ) + 1 ≠ 0 by positivity)]
          ring
        _ ≤ ‖a n - z‖ / ‖a n‖ := div_le_div₀ (by positivity) hnum han_pos han_le
    have hprod_ge : (1 / x_base) ^ S_R.card ≤ ∏ n ∈ S_R, ‖1 - z / a n‖ := by
      calc
        (1 / x_base) ^ S_R.card = ∏ _n ∈ S_R, (1 / x_base) := by rw [Finset.prod_const]
        _ ≤ ∏ n ∈ S_R, ‖1 - z / a n‖ :=
            Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) hfac_poly
    have hpow_exp : (1 / x_base) ^ S_R.card = Real.exp (-((S_R.card : ℝ) * Real.log x_base)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx_pos, inv_eq_one_div, one_div_pow]
    have hN_le : (S_R.card : ℝ) ≤ C₁ * R ^ (ρ' + δ) := by
      have hcard : S_R.card ≤ zeroCount f 0 (8 * R) :=
        card_finset_le_zeroCount_of_enumeration hf hf0 ha_ne ha_fin ha_card
          (by positivity) fun n hn ↦ (Set.Finite.mem_toFinset _).mp hn
      have hzc8 := hzc (8 * R) (by linarith)
      have hsplit : (8 * R) ^ (ρ' + δ) = (8 : ℝ) ^ (ρ' + δ) * R ^ (ρ' + δ) :=
        Real.mul_rpow (by positivity) hR_pos.le
      calc
        (S_R.card : ℝ) ≤ zeroCount f 0 (8 * R) := Nat.cast_le.mpr hcard
        _ ≤ C_J * (8 * R) ^ (ρ' + δ) := hzc8
        _ = C₁ * R ^ (ρ' + δ) := by rw [hsplit]; simp only [C₁]; ring
    have hx_le : x_base ≤ (16 * (C₁ + 1)) * R ^ (ρ' + δ) := by
      have hR_pow_ge : 1 ≤ R ^ (ρ' + δ) := Real.one_le_rpow hR hρδ_pos.le
      dsimp only [x_base]
      nlinarith
    have hlog_le : Real.log x_base ≤ C₂ * R ^ ((ρ' + δ) * η) := by
      have h1 := real_log_le_rpow_div hx_pos hη_pos
      have h2 : x_base ^ η ≤ ((16 * (C₁ + 1)) * R ^ (ρ' + δ)) ^ η :=
        Real.rpow_le_rpow hx_pos.le hx_le hη_pos.le
      have h3 : ((16 * (C₁ + 1)) * R ^ (ρ' + δ)) ^ η =
          (16 * (C₁ + 1)) ^ η * R ^ ((ρ' + δ) * η) := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hR_pos.le _),
          ← Real.rpow_mul hR_pos.le]
      calc
        Real.log x_base ≤ x_base ^ η / η := h1
        _ ≤ ((16 * (C₁ + 1)) ^ η * R ^ ((ρ' + δ) * η)) / η :=
            div_le_div_of_nonneg_right (h2.trans_eq h3) hη_pos.le
        _ = C₂ * R ^ ((ρ' + δ) * η) := by simp only [C₂]; ring
    have hexp_mul_le : (S_R.card : ℝ) * Real.log x_base ≤ C_poly * r ^ α := by
      have hmul : (S_R.card : ℝ) * Real.log x_base ≤ (C₁ * R ^ (ρ' + δ)) * (C₂ * R ^ ((ρ' + δ) * η)) :=
        mul_le_mul hN_le hlog_le (Real.log_nonneg (by dsimp only [x_base]; linarith))
          (by positivity)
      have hpow_R : R ^ (ρ' + δ) * R ^ ((ρ' + δ) * η) = R ^ α := by
        rw [← Real.rpow_add hR_pos]
        congr 2
        dsimp only [η]
        field_simp [hρδ_pos.ne']
        ring
      have hR_r : R ^ α ≤ r ^ α := Real.rpow_le_rpow hR_pos.le hr_ge (by linarith [hρ'_nonneg])
      calc
        (S_R.card : ℝ) * Real.log x_base
          ≤ (C₁ * R ^ (ρ' + δ)) * (C₂ * R ^ ((ρ' + δ) * η)) := hmul
        _ = C_poly * R ^ α := by
            have heq : (C₁ * R ^ (ρ' + δ)) * (C₂ * R ^ ((ρ' + δ) * η)) =
                (C₁ * C₂) * (R ^ (ρ' + δ) * R ^ ((ρ' + δ) * η)) := by ring
            rw [heq, hpow_R]
        _ ≤ C_poly * r ^ α := mul_le_mul_of_nonneg_left hR_r (by positivity)
    rw [hpow_exp] at hprod_ge
    exact (Real.exp_le_exp.mpr (by linarith)).trans hprod_ge
  have hhead_ge : Real.exp (-(C_poly + C_exp) * r ^ α) ≤
      ∏ n ∈ S_R, ‖weierstrassPrimaryFactor p (z / a n)‖ := by
    have hprod_split : ∏ n ∈ S_R, ‖weierstrassPrimaryFactor p (z / a n)‖ =
        (∏ n ∈ S_R, ‖1 - z / a n‖) *
          (∏ n ∈ S_R, ‖Complex.exp (∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ))‖) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun n _ ↦ ?_
      rw [weierstrassPrimaryFactor, norm_mul]
    rw [hprod_split]
    calc
      Real.exp (-(C_poly + C_exp) * r ^ α)
        = Real.exp (-C_poly * r ^ α) * Real.exp (-C_exp * r ^ α) := by
            rw [← Real.exp_add]; congr 1; ring
      _ ≤ (∏ n ∈ S_R, ‖1 - z / a n‖) *
            (∏ n ∈ S_R, ‖Complex.exp (∑ k ∈ Finset.Icc 1 p, (z / a n) ^ k / (k : ℂ))‖) :=
            mul_le_mul hhead_poly_ge hhead_exp_ge (Real.exp_pos _).le
              (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  have htot_exp : Real.exp (-C_tot * r ^ α) ≤
      Real.exp (-C_tail * r ^ α) * Real.exp (-(C_poly + C_exp) * r ^ α) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hrα_nonneg : 0 ≤ r ^ α := Real.rpow_nonneg hr_pos.le α
    dsimp only [C_tot]
    nlinarith
  exact htot_exp.trans (mul_le_mul htail_ge hhead_ge (Real.exp_pos _).le (by positivity))

/-!
### Section 5: Hadamard Factorization Theorem
-/

private lemma list_prod_norm_eq {α : Type*} (f : α → ℂ) (l : List α) :
    ‖(l.map f).prod‖ = (l.map (fun x ↦ ‖f x‖)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma list_prod_one_sub_differentiable (zs : List ℂ) :
    Differentiable ℂ (fun z : ℂ ↦ (zs.map (fun a ↦ 1 - z / a)).prod) := by
  induction zs with
  | nil => simp [differentiable_const]
  | cons a zs ih =>
    have hhead : Differentiable ℂ (fun z : ℂ ↦ 1 - z / a) :=
      (differentiable_const 1).fun_sub (differentiable_id.div_const a)
    simpa only [List.map_cons, List.prod_cons] using hhead.fun_mul ih

private lemma list_prod_primary_differentiable (p : ℕ) (zs : List ℂ) :
    Differentiable ℂ (fun z : ℂ ↦ (zs.map (fun a ↦ weierstrassPrimaryFactor p (z / a))).prod) := by
  induction zs with
  | nil => simp [differentiable_const]
  | cons a zs ih =>
    have hhead : Differentiable ℂ (fun z : ℂ ↦ weierstrassPrimaryFactor p (z / a)) :=
      (differentiable_weierstrassPrimaryFactor p).comp (differentiable_id.div_const a)
    simpa only [List.map_cons, List.prod_cons] using hhead.fun_mul ih

private lemma list_prod_one_sub_at_zero (zs : List ℂ) :
    (zs.map (fun a ↦ 1 - (0 : ℂ) / a)).prod = 1 := by
  induction zs with
  | nil => simp
  | cons a zs _ => simp

private lemma list_prod_one_sub_ne_zero (zs : List ℂ) :
    (fun z : ℂ ↦ (zs.map (fun a ↦ 1 - z / a)).prod) ≠ 0 := by
  intro h0
  have := congrFun h0 0
  rw [list_prod_one_sub_at_zero] at this
  exact one_ne_zero this

private lemma analyticOrderNatAt_list_prod_one_sub :
    ∀ (zs : List ℂ), (∀ a ∈ zs, a ≠ 0) →
      analyticOrderNatAt (fun z : ℂ ↦ (zs.map (fun a ↦ 1 - z / a)).prod) 0 = 0 ∧
      (∀ z ≠ 0, analyticOrderNatAt (fun z : ℂ ↦ (zs.map (fun a ↦ 1 - z / a)).prod) z = zs.count z)
  | [], _ => by
    refine ⟨by simp, fun z _ ↦ by simp⟩
  | a :: zs, hzs => by
    have ha_ne : a ≠ 0 := hzs a (by simp)
    have ih := analyticOrderNatAt_list_prod_one_sub zs fun b hb ↦ hzs b (by simp [hb])
    have hhead_diff : Differentiable ℂ (fun z : ℂ ↦ 1 - z / a) :=
      (differentiable_const 1).fun_sub (differentiable_id.div_const a)
    have htail_diff : Differentiable ℂ (fun z : ℂ ↦ (zs.map (fun b ↦ 1 - z / b)).prod) :=
      list_prod_one_sub_differentiable zs
    have hhead_ne0 : (fun z : ℂ ↦ 1 - z / a) ≠ 0 := fun h0 ↦
      (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h0 0)
    have htail_ne0 : (fun z : ℂ ↦ (zs.map (fun b ↦ 1 - z / b)).prod) ≠ 0 :=
      list_prod_one_sub_ne_zero zs
    have hmul_eq : (fun z : ℂ ↦ ((a :: zs).map (fun b ↦ 1 - z / b)).prod) =
        fun z : ℂ ↦ (1 - z / a) * (zs.map (fun b ↦ 1 - z / b)).prod := by
      ext z; simp
    rw [hmul_eq]
    refine ⟨?_, fun z hzc ↦ ?_⟩
    · have htop1 := analyticOrderAt_ne_top_of_differentiable_ne_zero hhead_diff hhead_ne0 0
      have htop2 := analyticOrderAt_ne_top_of_differentiable_ne_zero htail_diff htail_ne0 0
      rw [analyticOrderNatAt_fun_mul (hhead_diff.analyticAt 0) (htail_diff.analyticAt 0) htop1 htop2,
        ih.1, add_zero]
      have : analyticOrderAt (fun z : ℂ ↦ 1 - z / a) 0 = 0 :=
        (hhead_diff.analyticAt 0).analyticOrderAt_eq_zero.mpr (by simp)
      simp [analyticOrderNatAt, this]
    · have htop1 := analyticOrderAt_ne_top_of_differentiable_ne_zero hhead_diff hhead_ne0 z
      have htop2 := analyticOrderAt_ne_top_of_differentiable_ne_zero htail_diff htail_ne0 z
      rw [analyticOrderNatAt_fun_mul (hhead_diff.analyticAt z) (htail_diff.analyticAt z) htop1 htop2,
        ih.2 z hzc]
      by_cases haz : a = z
      · subst haz
        have hprod_fac : (fun w : ℂ ↦ 1 - w / a) = fun w ↦ (w - a) ^ 1 * (-(1 / a)) := by
          ext w
          field_simp [ha_ne]
          ring
        have hord_1 : analyticOrderNatAt (fun w : ℂ ↦ 1 - w / a) a = 1 :=
          ((hhead_diff.analyticAt a).analyticOrderNatAt_eq_iff htop1).mpr
            ⟨fun _ ↦ -(1 / a), analyticAt_const, neg_ne_zero.mpr (one_div_ne_zero ha_ne),
              Filter.Eventually.of_forall fun w ↦ by simpa [smul_eq_mul] using congrFun hprod_fac w⟩
        rw [hord_1, List.count_cons_self, add_comm]
      · have hne : 1 - z / a ≠ 0 := by
          intro h0
          apply haz
          have : z / a = 1 := (sub_eq_zero.mp h0).symm
          exact ((div_eq_one_iff_eq ha_ne).mp this).symm
        have hord_0 : analyticOrderNatAt (fun w : ℂ ↦ 1 - w / a) z = 0 := by
          have : analyticOrderAt (fun w : ℂ ↦ 1 - w / a) z = 0 :=
            (hhead_diff.analyticAt z).analyticOrderAt_eq_zero.mpr hne
          simp [analyticOrderNatAt, this]
        rw [hord_0, zero_add, List.count_cons_of_ne haz]

private lemma list_prod_one_sub_eq_primary_mul_cexp :
    ∀ (p : ℕ) (zs : List ℂ),
      ∃ R : Polynomial ℂ, R.natDegree ≤ p ∧
        ∀ z : ℂ, (zs.map (fun a ↦ 1 - z / a)).prod =
          Complex.exp (R.eval z) * (zs.map (fun a ↦ weierstrassPrimaryFactor p (z / a))).prod
  | p, [] => ⟨0, by simp, fun z ↦ by simp⟩
  | p, a :: zs => by
    obtain ⟨R₀, hR₀_deg, hR₀_eq⟩ := list_prod_one_sub_eq_primary_mul_cexp p zs
    let S₁ : Polynomial ℂ :=
      -∑ k ∈ Finset.Icc 1 p, Polynomial.C (1 / ((k : ℂ) * a ^ k)) * Polynomial.X ^ k
    have hS₁_deg : S₁.natDegree ≤ p := by
      rw [Polynomial.natDegree_neg]
      have aux : ∀ s : Finset ℕ, (∀ k ∈ s, k ≤ p) →
          (∑ k ∈ s, Polynomial.C (1 / ((k : ℂ) * a ^ k)) * Polynomial.X ^ k).natDegree ≤ p := by
        intro s hs
        induction s using Finset.induction_on with
        | empty => simp
        | insert k s hks ih =>
          rw [Finset.sum_insert hks]
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hs k (Finset.mem_insert_self k s))
          · exact ih fun j hj ↦ hs j (Finset.mem_insert_of_mem hj)
      exact aux (Finset.Icc 1 p) fun k hk ↦ (Finset.mem_Icc.mp hk).2
    let R : Polynomial ℂ := S₁ + R₀
    have hR_deg : R.natDegree ≤ p :=
      (Polynomial.natDegree_add_le _ _).trans (max_le hS₁_deg hR₀_deg)
    refine ⟨R, hR_deg, fun z ↦ ?_⟩
    have hS₁_eval : S₁.eval z = -∑ k ∈ Finset.Icc 1 p, (z / a) ^ k / (k : ℂ) := by
      dsimp only [S₁]
      rw [Polynomial.eval_neg, polynomial_eval_finset_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [div_pow]
      ring
    have hhead : 1 - z / a = Complex.exp (S₁.eval z) * weierstrassPrimaryFactor p (z / a) := by
      rw [hS₁_eval, weierstrassPrimaryFactor]
      calc
        1 - z / a = (1 - z / a) * 1 := (mul_one _).symm
        _ = (1 - z / a) * (Complex.exp (∑ k ∈ Finset.Icc 1 p, (z / a) ^ k / (k : ℂ)) *
              Complex.exp (-∑ k ∈ Finset.Icc 1 p, (z / a) ^ k / (k : ℂ))) := by
            rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
        _ = Complex.exp (-∑ k ∈ Finset.Icc 1 p, (z / a) ^ k / (k : ℂ)) *
              ((1 - z / a) * Complex.exp (∑ k ∈ Finset.Icc 1 p, (z / a) ^ k / (k : ℂ))) := by ring
    simp only [List.map_cons, List.prod_cons, R, Polynomial.eval_add, Complex.exp_add]
    rw [hhead, hR₀_eq z]
    ring

/-- **Hadamard factorization for entire functions with finitely many zeros**: if `f : ℂ → ℂ` is
nonzero, satisfies `EntireOrderLe f ρ` with `0 ≤ ρ < (p : ℝ) + 1`, and `zs : List ℂ` lists the
nonzero zeros of `f` with multiplicity (`∀ a ∈ zs, a ≠ 0`, `∀ z ≠ 0, zs.count z = analyticOrderNatAt f z`),
then there exist polynomials `P₀, Q : Polynomial ℂ` of degree at most `p` giving both the product
over `(1 - z / a)` and the canonical genus-`p` product over `weierstrassPrimaryFactor p (z / a)`. -/
theorem hadamard_factorization_of_finite_zeros {f : ℂ → ℂ} {ρ : ℝ} {p : ℕ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ)
    (hp : ρ < (p : ℝ) + 1) {zs : List ℂ} (hzs_ne : ∀ a ∈ zs, a ≠ 0)
    (hzs_count : ∀ z ≠ 0, zs.count z = analyticOrderNatAt f z) :
    (∃ P₀ : Polynomial ℂ, P₀.natDegree ≤ p ∧ ∀ z : ℂ,
      f z = z ^ analyticOrderNatAt f 0 * Complex.exp (P₀.eval z) *
        (zs.map (fun a ↦ 1 - z / a)).prod) ∧
    (∃ Q : Polynomial ℂ, Q.natDegree ≤ p ∧ ∀ z : ℂ,
      f z = z ^ analyticOrderNatAt f 0 * Complex.exp (Q.eval z) *
        (zs.map (fun a ↦ weierstrassPrimaryFactor p (z / a))).prod) := by
  let m : ℕ := analyticOrderNatAt f 0
  obtain ⟨f₀, hf₀_diff, hf₀_at_0, hf₀_eq, hf₀_ord⟩ :=
    exists_div_pow_entire_of_differentiable hf hf_ne 0
  have hf_mul : ∀ z : ℂ, f z = z ^ m * f₀ z := fun z ↦ by simpa [m] using hf₀_eq z
  have hf₀_ne : f₀ ≠ 0 := fun h0 ↦ hf₀_at_0 (by rw [h0]; rfl)
  have hf₀_ord_bound : EntireOrderLe f₀ ρ := entireOrderLe_of_eq_pow_mul hf₀_diff hord hf_mul
  let Q₀ : ℂ → ℂ := fun z ↦ (zs.map (fun a ↦ 1 - z / a)).prod
  have hQ₀_diff : Differentiable ℂ Q₀ := list_prod_one_sub_differentiable zs
  have hQ₀_ne : Q₀ ≠ 0 := list_prod_one_sub_ne_zero zs
  have hQ₀_ord := analyticOrderNatAt_list_prod_one_sub zs hzs_ne
  have hord_eq : ∀ z : ℂ, analyticOrderNatAt f₀ z = analyticOrderNatAt Q₀ z := by
    intro z
    rcases eq_or_ne z 0 with rfl | hzc
    · have : analyticOrderAt f₀ 0 = 0 :=
        ((hf₀_diff.differentiableOn.analyticOnNhd isOpen_univ) 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr hf₀_at_0
      rw [hQ₀_ord.1]
      simp [analyticOrderNatAt, this]
    · rw [hf₀_ord z hzc, ← hzs_count z hzc, hQ₀_ord.2 z hzc]
  obtain ⟨h, hh_diff, hh_ne, hh_mul⟩ :=
    quotient_entire_ne_zero_of_eq_analyticOrderNatAt hf₀_diff hf₀_ne hQ₀_diff hQ₀_ne hord_eq
  obtain ⟨g, hg_diff, hg_exp⟩ := exists_cexp_eq_of_differentiable_ne_zero hh_diff hh_ne
  let α : ℝ := (ρ + ((p : ℝ) + 1)) / 2
  have hα_pos : ρ < α := by dsimp only [α]; linarith
  have hα_nonneg : 0 ≤ α := hρ.trans hα_pos.le
  have hα_lt : α < (p : ℝ) + 1 := by dsimp only [α]; linarith
  have hε_pos : 0 < α - ρ := sub_pos.mpr hα_pos
  obtain ⟨C_f, hC_f_nonneg, hbound_f⟩ := hf₀_ord_bound.norm_le hε_pos
  let R_zs : ℝ := (zs.map norm).sum + 1
  have hR_zs_ge : 1 ≤ R_zs := by
    have : 0 ≤ (zs.map norm).sum := List.sum_nonneg (fun x hx ↦ by
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg a)
    dsimp only [R_zs]; linarith
  let C_g : ℝ := max (Real.log (max C_f 1)) 0 + 1
  have h_sph : ∀ᶠ R : ℝ in atTop, ∃ r : ℝ, R ≤ r ∧
      ∀ w ∈ Metric.sphere (0 : ℂ) r, (g w).re ≤ C_g * r ^ α := by
    refine Filter.eventually_atTop.mpr ⟨max (2 * R_zs) 1, fun R hR ↦ ⟨R, le_rfl, fun w hw ↦ ?_⟩⟩
    have hwn : ‖w‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hw
    have hR_ge_one : 1 ≤ R := (le_max_right _ _).trans hR
    have hR_ge_zs : 2 * R_zs ≤ R := (le_max_left _ _).trans hR
    have hQ₀_ge : 1 ≤ ‖Q₀ w‖ := by
      have aux : ∀ l : List ℂ, (∀ a ∈ l, a ≠ 0 ∧ ‖a‖ ≤ R_zs) →
          1 ≤ (l.map (fun a ↦ ‖1 - w / a‖)).prod := by
        intro l hl
        induction l with
        | nil => simp
        | cons a l ih =>
          simp only [List.map_cons, List.prod_cons]
          obtain ⟨ha_ne, ha_norm⟩ := hl a (by simp)
          have h1 : 1 ≤ ‖1 - w / a‖ := by
            have han_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha_ne
            have hw_a : 2 ≤ ‖w / a‖ := by
              rw [norm_div, hwn, le_div_iff₀ han_pos]
              have hR_pos : 0 < R_zs := zero_lt_one.trans_le hR_zs_ge
              nlinarith
            have htri : ‖w / a‖ - 1 ≤ ‖w / a - 1‖ := by
              simpa [norm_one] using norm_sub_norm_le (w / a) 1
            rw [norm_sub_rev (w / a) 1] at htri
            linarith
          have h2 : 1 ≤ (l.map (fun b ↦ ‖1 - w / b‖)).prod :=
            ih fun b hb ↦ hl b (by simp [hb])
          exact one_le_mul_of_one_le_of_one_le h1 h2
      have hnorm_prod : ‖Q₀ w‖ = (zs.map (fun a ↦ ‖1 - w / a‖)).prod :=
        list_prod_norm_eq (fun a ↦ 1 - w / a) zs
      rw [hnorm_prod]
      refine aux zs fun a ha ↦ ⟨hzs_ne a ha, ?_⟩
      have hmem : ‖a‖ ∈ zs.map norm := List.mem_map_of_mem ha
      have hle_sum : ‖a‖ ≤ (zs.map norm).sum :=
        List.single_le_sum (fun x hx ↦ by
          obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
          exact norm_nonneg b) ‖a‖ hmem
      dsimp only [R_zs]; linarith
    have hhw : ‖h w‖ ≤ ‖f₀ w‖ := by
      have heq : ‖f₀ w‖ = ‖Q₀ w‖ * ‖h w‖ := by rw [hh_mul w, norm_mul]
      calc
        ‖h w‖ = 1 * ‖h w‖ := (one_mul _).symm
        _ ≤ ‖Q₀ w‖ * ‖h w‖ := mul_le_mul_of_nonneg_right hQ₀_ge (norm_nonneg _)
        _ = ‖f₀ w‖ := heq.symm
    have hf₀_w : ‖f₀ w‖ ≤ max C_f 1 * Real.exp (R ^ α) := by
      have hb := hbound_f w
      have hexp_eq : ρ + (α - ρ) = α := by ring
      rw [hwn, hexp_eq] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left C_f 1) (Real.exp_pos _).le)
    have hre_le : (g w).re ≤ Real.log (max C_f 1) + R ^ α := by
      have hC_pos : 0 < max C_f 1 := zero_lt_one.trans_le (le_max_right C_f 1)
      have h_exp : Real.exp (g w).re ≤ Real.exp (Real.log (max C_f 1) + R ^ α) := by
        rw [← Complex.norm_exp, ← hg_exp w, Real.exp_add, Real.exp_log hC_pos]
        exact hhw.trans hf₀_w
      exact Real.exp_le_exp.mp h_exp
    have hR_pow_ge : 1 ≤ R ^ α := Real.one_le_rpow hR_ge_one hα_nonneg
    have hlin : Real.log (max C_f 1) ≤ max (Real.log (max C_f 1)) 0 * R ^ α :=
      (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) hR_pow_ge)
    dsimp only [C_g]
    nlinarith
  obtain ⟨P₀, hP₀_deg, hP₀_eq⟩ := exists_polynomial_of_re_le_rpow hg_diff hα_nonneg hα_lt h_sph
  have hform1 : ∀ z : ℂ, f z = z ^ m * Complex.exp (P₀.eval z) *
      (zs.map (fun a ↦ 1 - z / a)).prod := by
    intro z
    rw [hf_mul z, hh_mul z, hg_exp z, hP₀_eq z]
    dsimp only [Q₀]
    ring
  obtain ⟨R_poly, hR_deg, hR_eq⟩ := list_prod_one_sub_eq_primary_mul_cexp p zs
  let Q : Polynomial ℂ := P₀ + R_poly
  have hQ_deg : Q.natDegree ≤ p :=
    (Polynomial.natDegree_add_le _ _).trans (max_le hP₀_deg hR_deg)
  have hform2 : ∀ z : ℂ, f z = z ^ m * Complex.exp (Q.eval z) *
      (zs.map (fun a ↦ weierstrassPrimaryFactor p (z / a))).prod := by
    intro z
    rw [hform1 z, hR_eq z]
    simp only [Q, Polynomial.eval_add, Complex.exp_add]
    ring
  exact ⟨⟨P₀, hP₀_deg, hform1⟩, ⟨Q, hQ_deg, hform2⟩⟩

/-- **Hadamard factorization theorem for a given infinite zero enumeration**: if `f : ℂ → ℂ`
is nonzero of finite order `ρ` (`0 ≤ ρ < (p : ℝ) + 1`) and `a : ℕ → ℂ` enumerates the nonzero
zeros of `f` with multiplicity (`∀ R, {n | ‖a n‖ ≤ R}.Finite`), then `∑ ‖a n‖ ^ (-(p + 1))`
converges and there exists a polynomial `Q : Polynomial ℂ` of degree at most `p` such that
`f z = z ^ analyticOrderNatAt f 0 * Complex.exp (Q.eval z) * canonicalProduct a p z`
for all `z : ℂ`. -/
theorem hadamard_factorization_of_zeros {f : ℂ → ℂ} {ρ : ℝ} {p : ℕ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ)
    (hp : ρ < (p : ℝ) + 1) {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0)
    (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) :
    Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))) ∧
      ∃ Q : Polynomial ℂ, Q.natDegree ≤ p ∧ ∀ z : ℂ,
        f z = z ^ analyticOrderNatAt f 0 * Complex.exp (Q.eval z) * canonicalProduct a p z := by
  let m : ℕ := analyticOrderNatAt f 0
  obtain ⟨f₀, hf₀_diff, hf₀_at_0, hf₀_eq, hf₀_ord⟩ :=
    exists_div_pow_entire_of_differentiable hf hf_ne 0
  have hf_mul : ∀ z : ℂ, f z = z ^ m * f₀ z := fun z ↦ by simpa [m] using hf₀_eq z
  have hf₀_ne : f₀ ≠ 0 := fun h0 ↦ hf₀_at_0 (by rw [h0]; rfl)
  have hf₀_ord_bound : EntireOrderLe f₀ ρ := entireOrderLe_of_eq_pow_mul hf₀_diff hord hf_mul
  have ha_card₀ : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f₀ z := fun z hz ↦
    (ha_card z hz).trans (hf₀_ord z hz).symm
  have hsum_p1 : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))) := by
    have hlt : ρ < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast hp
    exact summable_norm_rpow_neg_of_enumeration hf₀_diff hρ hf₀_ord_bound hf₀_at_0 hlt
      ha_ne ha_fin ha_card₀
  have hP_diff := differentiable_canonicalProduct ha_ne hsum_p1
  have hP_ne : canonicalProduct a p ≠ 0 := fun h0 ↦
    (by simp [canonicalProduct, weierstrassPrimaryFactor_at_zero] : canonicalProduct a p 0 ≠ 0)
      (by rw [h0]; rfl)
  have hP_ord := analyticOrderNatAt_canonicalProduct_eq ha_ne hsum_p1
  have hord_eq : ∀ z : ℂ, analyticOrderNatAt f₀ z = analyticOrderNatAt (canonicalProduct a p) z := by
    intro z
    rcases eq_or_ne z 0 with rfl | hzc
    · have : analyticOrderAt f₀ 0 = 0 :=
        ((hf₀_diff.differentiableOn.analyticOnNhd isOpen_univ) 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr hf₀_at_0
      rw [hP_ord.1]
      simp [analyticOrderNatAt, this]
    · rw [← ha_card₀ z hzc, hP_ord.2 z hzc]
  obtain ⟨h, hh_diff, hh_ne, hh_mul⟩ :=
    quotient_entire_ne_zero_of_eq_analyticOrderNatAt hf₀_diff hf₀_ne hP_diff hP_ne hord_eq
  obtain ⟨g, hg_diff, hg_exp⟩ := exists_cexp_eq_of_differentiable_ne_zero hh_diff hh_ne
  let α : ℝ := (max ρ (p : ℝ) + ((p : ℝ) + 1)) / 2
  have hmax_lt : max ρ (p : ℝ) < (p : ℝ) + 1 := max_lt hp (by linarith)
  have hρ_lt_α : ρ < α := (le_max_left ρ (p : ℝ)).trans_lt (by dsimp only [α]; linarith)
  have hp_lt_α : (p : ℝ) < α := (le_max_right ρ (p : ℝ)).trans_lt (by dsimp only [α]; linarith)
  have hα_lt : α < (p : ℝ) + 1 := by dsimp only [α]; linarith
  have hα_nonneg : 0 ≤ α := hρ.trans hρ_lt_α.le
  obtain ⟨C_low, _, hlow⟩ := exists_circle_canonicalProduct_lower_bound hf₀_diff hf₀_ord_bound hf₀_at_0
    hρ_lt_α hp_lt_α hα_lt ha_ne ha_fin ha_card₀
  obtain ⟨C_f, _, hbound_f⟩ := hf₀_ord_bound.norm_le (sub_pos.mpr hρ_lt_α)
  let C_g : ℝ := max (Real.log (max C_f 1)) 0 + 1 + C_low
  have h_sph : ∀ᶠ R : ℝ in atTop, ∃ r : ℝ, R ≤ r ∧
      ∀ w ∈ Metric.sphere (0 : ℂ) r, (g w).re ≤ C_g * r ^ α := by
    filter_upwards [hlow, Filter.eventually_ge_atTop (1 : ℝ)] with R hr_ex hR_one
    obtain ⟨r, hr_mem, hr_low⟩ := hr_ex
    refine ⟨r, hr_mem.1, fun w hw ↦ ?_⟩
    have hr_one : 1 ≤ r := hR_one.trans hr_mem.1
    have hwn : ‖w‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hw
    have hP_pos : 0 < ‖canonicalProduct a p w‖ :=
      lt_of_lt_of_le (Real.exp_pos _) (hr_low w hw)
    have h_f_le : ‖f₀ w‖ ≤ max C_f 1 * Real.exp (r ^ α) := by
      have hb := hbound_f w
      have hexp_eq : ρ + (α - ρ) = α := by ring
      rw [hwn, hexp_eq] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left C_f 1) (Real.exp_pos _).le)
    have h_h_le : ‖h w‖ ≤ max C_f 1 * Real.exp ((1 + C_low) * r ^ α) := by
      have heq : ‖h w‖ = ‖f₀ w‖ / ‖canonicalProduct a p w‖ := by
        rw [hh_mul w, norm_mul, mul_div_cancel_left₀ _ hP_pos.ne']
      rw [heq]
      calc
        ‖f₀ w‖ / ‖canonicalProduct a p w‖
          ≤ (max C_f 1 * Real.exp (r ^ α)) / Real.exp (-C_low * r ^ α) :=
              div_le_div₀ (by positivity) h_f_le (Real.exp_pos _) (hr_low w hw)
        _ = max C_f 1 * Real.exp ((1 + C_low) * r ^ α) := by
              rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
              congr 2; ring
    have hre_le : (g w).re ≤ Real.log (max C_f 1) + (1 + C_low) * r ^ α := by
      have hC_pos : 0 < max C_f 1 := zero_lt_one.trans_le (le_max_right C_f 1)
      have h_exp : Real.exp (g w).re ≤ Real.exp (Real.log (max C_f 1) + (1 + C_low) * r ^ α) := by
        rw [← Complex.norm_exp, ← hg_exp w, Real.exp_add, Real.exp_log hC_pos]
        exact h_h_le
      exact Real.exp_le_exp.mp h_exp
    have hr_pow_ge : 1 ≤ r ^ α := Real.one_le_rpow hr_one hα_nonneg
    have hlin : Real.log (max C_f 1) ≤ max (Real.log (max C_f 1)) 0 * r ^ α :=
      (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) hr_pow_ge)
    dsimp only [C_g]
    nlinarith
  obtain ⟨Q, hQ_deg, hQ_eq⟩ := exists_polynomial_of_re_le_rpow hg_diff hα_nonneg hα_lt h_sph
  refine ⟨hsum_p1, Q, hQ_deg, fun z ↦ ?_⟩
  rw [hf_mul z, hh_mul z, hg_exp z, hQ_eq z]
  dsimp only [m]
  ring

private lemma list_count_flatMap_replicate {l : List ℂ} (hl : l.Nodup) (m : ℂ → ℕ) (z : ℂ) :
    (l.flatMap (fun a ↦ List.replicate (m a) a)).count z = if z ∈ l then m z else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.count_append, ih hl.2, List.count_replicate]
    by_cases haz : a = z
    · subst haz
      simp [hl.1]
    · simp [haz, Ne.symm haz]

/-- **General Hadamard Factorization Theorem**: any nonzero entire function `f : ℂ → ℂ` of
finite order `ρ ≥ 0` (`EntireOrderLe f ρ`), with genus `p := Nat.floor ρ` and `m := analyticOrderNatAt f 0`,
admits a factorization `f z = z ^ m * Complex.exp (Q.eval z) * P z` with `Q.natDegree ≤ p`, where
`P` is either a finite primary product over a list `zs` of the nonzero zeros of `f` (with multiplicity)
or a convergent canonical product `canonicalProduct a p` over a zero enumeration `a : ℕ → ℂ`. -/
theorem hadamard_factorization {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ) :
    (∃ (zs : List ℂ) (Q : Polynomial ℂ), Q.natDegree ≤ Nat.floor ρ ∧
      (∀ a ∈ zs, a ≠ 0) ∧ (∀ z ≠ 0, zs.count z = analyticOrderNatAt f z) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (Q.eval z) *
        (zs.map (fun a ↦ weierstrassPrimaryFactor (Nat.floor ρ) (z / a))).prod)) ∨
    (∃ (a : ℕ → ℂ) (Q : Polynomial ℂ), Q.natDegree ≤ Nat.floor ρ ∧
      (∀ n, a n ≠ 0) ∧ (∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite) ∧
      (∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) ∧
      Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((Nat.floor ρ + 1 : ℕ) : ℝ))) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (Q.eval z) *
        canonicalProduct a (Nat.floor ρ) z)) := by
  classical
  let p : ℕ := Nat.floor ρ
  have hp_lt : ρ < (p : ℝ) + 1 := Nat.lt_floor_add_one ρ
  obtain ⟨f₀, hf₀_diff, hf₀_at_0, hf₀_eq, hf₀_ord⟩ :=
    exists_div_pow_entire_of_differentiable hf hf_ne 0
  have hf₀_ne : f₀ ≠ 0 := fun h0 ↦ hf₀_at_0 (by rw [h0]; rfl)
  let Zset : Set ℂ := {z : ℂ | z ≠ 0 ∧ f₀ z = 0}
  have hf₀_zero_iff : ∀ z ≠ 0, f₀ z = 0 ↔ f z = 0 := by
    intro z hzc
    rw [hf₀_eq z, sub_zero]
    exact mul_eq_zero_iff_left (pow_ne_zero _ hzc) |>.symm
  by_cases hfin : Zset.Finite
  · left
    let S : Finset ℂ := hfin.toFinset
    let zs : List ℂ := S.toList.flatMap (fun z ↦ List.replicate (analyticOrderNatAt f z) z)
    have hzs_ne : ∀ a ∈ zs, a ≠ 0 := by
      intro a ha
      rw [List.mem_flatMap] at ha
      obtain ⟨b, hbS, hba⟩ := ha
      rw [List.mem_replicate] at hba
      rw [hba.2]
      have hb_set : b ∈ Zset := hfin.mem_toFinset.mp (Finset.mem_toList.mp hbS)
      exact hb_set.1
    have hzs_count : ∀ z ≠ 0, zs.count z = analyticOrderNatAt f z := by
      intro z hzc
      dsimp only [zs]
      rw [list_count_flatMap_replicate (Finset.nodup_toList S)]
      by_cases hzS : z ∈ S.toList
      · simp [hzS]
      · rw [ite_eq_right_iff.mpr fun h ↦ False.elim (hzS h)]
        have hz_not_mem : z ∉ Zset := by
          intro hmem
          exact hzS (Finset.mem_toList.mpr (hfin.mem_toFinset.mpr hmem))
        have hfz_ne : f₀ z ≠ 0 := fun h0 ↦ hz_not_mem ⟨hzc, h0⟩
        have hfz_orig : f z ≠ 0 := (hf₀_zero_iff z hzc).not.mp hfz_ne
        have : analyticOrderAt f z = 0 :=
          ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).analyticOrderAt_eq_zero.mpr hfz_orig
        simp [analyticOrderNatAt, this]
    obtain ⟨_, Q, hQ_deg, hQ_form⟩ :=
      hadamard_factorization_of_finite_zeros hf hf_ne hρ hord hp_lt hzs_ne hzs_count
    exact ⟨zs, Q, hQ_deg, hzs_ne, hzs_count, hQ_form⟩
  · right
    have hZset_inf : Zset.Infinite := hfin
    have hZset_countable : Zset.Countable := by
      have hsub : Zset ⊆ ⋃ N : ℕ, zeroSet f₀ 0 (N + 1 : ℝ) := by
        intro z hz
        obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
        refine Set.mem_iUnion.mpr ⟨N, ?_⟩
        rw [mem_zeroSet, Metric.mem_closedBall, dist_zero_right]
        exact ⟨by linarith, hz.2⟩
      refine (Set.countable_iUnion fun N : ℕ ↦ ?_).mono hsub
      have hf₀_an : AnalyticOnNhd ℂ f₀ (Metric.closedBall 0 (N + 1 : ℝ)) :=
        (hf₀_diff.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
      exact (zeroSet_finite (by positivity) hf₀_an hf₀_at_0).countable
    let Zsub := {z : ℂ // z ∈ Zset}
    have : Countable Zsub := hZset_countable.to_subtype
    have : Infinite Zsub := hZset_inf.to_subtype
    let Zmult := Σ z : Zsub, Fin (analyticOrderNatAt f z.1)
    have : Countable Zmult := inferInstance
    have h_pos_ord : ∀ z : Zsub, 0 < analyticOrderNatAt f z.1 := by
      intro z
      have hfz : f z.1 = 0 := (hf₀_zero_iff z.1 z.2.1).mp z.2.2
      have hne0 : analyticOrderAt f z.1 ≠ 0 :=
        ((hf.differentiableOn.analyticOnNhd isOpen_univ) z.1 (mem_univ z.1)).analyticOrderAt_ne_zero.mpr hfz
      have htop : analyticOrderAt f z.1 ≠ ⊤ :=
        analyticOrderAt_ne_top_of_differentiable_ne_zero hf hf_ne z.1
      rw [← Nat.cast_analyticOrderNatAt htop] at hne0
      exact Nat.pos_of_ne_zero (by simpa using hne0)
    have : Infinite Zmult := by
      let inj : Zsub → Zmult := fun z ↦ ⟨z, ⟨0, h_pos_ord z⟩⟩
      refine Infinite.of_injective inj fun z₁ z₂ heq ↦ ?_
      exact congrArg Sigma.fst heq
    let e : ℕ ≃ Zmult := Classical.arbitrary (ℕ ≃ Zmult)
    let a : ℕ → ℂ := fun n ↦ (e n).1.1
    have ha_ne : ∀ n, a n ≠ 0 := fun n ↦ (e n).1.2.1
    have ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite := by
      intro R
      have hf_an : AnalyticOnNhd ℂ f₀ (Metric.closedBall 0 (max R 0)) :=
        (hf₀_diff.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
      let Sfin : Finset ℂ := (zeroSet_finite (le_max_right R 0) hf_an hf₀_at_0).toFinset
      let Bfin : Finset (ℂ × ℕ) :=
        Sfin.biUnion fun z ↦ (Finset.range (analyticOrderNatAt f z)).image fun k ↦ (z, k)
      let φ : ℕ → ℂ × ℕ := fun n ↦ ((e n).1.1, (e n).2.1)
      have hZmult_ext : ∀ x y : Zmult, x.1.1 = y.1.1 → x.2.1 = y.2.1 → x = y := by
        rintro ⟨z₁, k₁⟩ ⟨z₂, k₂⟩ h1 h2
        have hz : z₁ = z₂ := Subtype.ext h1
        subst hz
        exact congrArg (Sigma.mk z₁) (Fin.ext h2)
      have hφ_inj : Function.Injective φ := by
        intro n₁ n₂ heq
        simp only [φ, Prod.mk.injEq] at heq
        exact e.injective (hZmult_ext (e n₁) (e n₂) heq.1 heq.2)
      have hsub : {n : ℕ | ‖a n‖ ≤ R} ⊆ φ ⁻¹' (Bfin : Set (ℂ × ℕ)) := by
        intro n hn
        rw [Set.mem_preimage, Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨(e n).1.1, ?_, Finset.mem_image.mpr ⟨(e n).2.1, Finset.mem_range.mpr (e n).2.2, rfl⟩⟩
        rw [Set.Finite.mem_toFinset, mem_zeroSet, Metric.mem_closedBall, dist_zero_right]
        exact ⟨hn.trans (le_max_left R 0), (e n).1.2.2⟩
      exact (Bfin.finite_toSet.preimage hφ_inj.injOn).subset hsub
    have ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z := by
      intro z hzc
      by_cases hz_mem : z ∈ Zset
      · let g_map : Fin (analyticOrderNatAt f z) → ℕ := fun k ↦ e.symm ⟨⟨z, hz_mem⟩, k⟩
        have hg_inj : Function.Injective g_map := by
          intro k₁ k₂ heq
          have he := congrArg e heq
          dsimp only [g_map] at he
          simp only [Equiv.apply_symm_apply] at he
          exact Sigma.ext_iff.mp he |>.2 |> eq_of_heq
        have hrange : {n : ℕ | a n = z} = Set.range g_map := by
          ext n
          simp only [Set.mem_ofPred_eq, Set.mem_range, g_map, a]
          constructor
          · intro hanz
            rcases he : e n with ⟨⟨w, hw⟩, k⟩
            simp only [he] at hanz
            subst hanz
            refine ⟨k, ?_⟩
            apply e.symm_apply_eq.mpr
            exact he.symm
          · rintro ⟨k, rfl⟩
            simp
        rw [hrange, Set.ncard_range_of_injective hg_inj]
        simp
      · have hempty : {n : ℕ | a n = z} = ∅ := by
          ext n
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro hanz
          exact hz_mem (hanz ▸ (e n).1.2)
        have hfz_ne : f z ≠ 0 := by
          intro h0
          exact hz_mem ⟨hzc, (hf₀_zero_iff z hzc).mpr h0⟩
        have hord0 : analyticOrderAt f z = 0 :=
          ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).analyticOrderAt_eq_zero.mpr hfz_ne
        rw [hempty, Set.ncard_empty]
        simp [analyticOrderNatAt, hord0]
    obtain ⟨hsum, Q, hQ_deg, hQ_form⟩ :=
      hadamard_factorization_of_zeros hf hf_ne hρ hord hp_lt ha_ne ha_fin ha_card
    exact ⟨a, Q, hQ_deg, ha_ne, ha_fin, ha_card, hsum, hQ_form⟩

/-- **Genus-0 Hadamard factorization (infinite-zero form)**: if `f : ℂ → ℂ` is nonzero of order
`ρ` with `0 ≤ ρ < 1` and `a : ℕ → ℂ` enumerates the nonzero zeros of `f` with multiplicity, then
`∑ ‖a n‖ ^ (-1)` converges and `f z = z ^ analyticOrderNatAt f 0 * Complex.exp A * canonicalProduct a 0 z`. -/
theorem hadamard_factorization_of_zeros_genus_zero {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ)
    (hρ1 : ρ < 1) {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0)
    (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) :
    Summable (fun n : ℕ ↦ ‖a n‖ ^ (-1 : ℝ)) ∧
      ∃ A : ℂ, ∀ z : ℂ,
        f z = z ^ analyticOrderNatAt f 0 * Complex.exp A * canonicalProduct a 0 z := by
  have hp0 : ρ < ((0 : ℕ) : ℝ) + 1 := by simpa using hρ1
  obtain ⟨hsum, Q, hQ_deg, hform⟩ :=
    hadamard_factorization_of_zeros hf hf_ne hρ hord (p := 0) hp0 ha_ne ha_fin ha_card
  have hQ_eval : ∀ z : ℂ, Q.eval z = Q.coeff 0 := fun z ↦ by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ_deg)]
    simp
  refine ⟨by simpa using hsum, Q.coeff 0, fun z ↦ ?_⟩
  simpa [hQ_eval z] using hform z

/-- **Genus-0 Hadamard factorization (general form)**: any nonzero entire function `f : ℂ → ℂ` of
order `ρ` with `0 ≤ ρ < 1` factors as `z ^ m * exp A * P z` where `P` is either a finite product
`∏ a ∈ zs, (1 - z / a)` or a convergent genus-`0` canonical product `canonicalProduct a 0 z`. -/
theorem hadamard_factorization_genus_zero {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ)
    (hρ1 : ρ < 1) :
    (∃ (zs : List ℂ) (A : ℂ),
      (∀ a ∈ zs, a ≠ 0) ∧ (∀ z ≠ 0, zs.count z = analyticOrderNatAt f z) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp A *
        (zs.map (fun a ↦ 1 - z / a)).prod)) ∨
    (∃ (a : ℕ → ℂ) (A : ℂ),
      (∀ n, a n ≠ 0) ∧ (∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite) ∧
      (∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) ∧
      Summable (fun n : ℕ ↦ ‖a n‖ ^ (-1 : ℝ)) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp A * canonicalProduct a 0 z)) := by
  have hfloor : Nat.floor ρ = 0 := Nat.floor_eq_zero.mpr hρ1
  rcases hadamard_factorization hf hf_ne hρ hord with
    ⟨zs, Q, hQ_deg, hzs_ne, hzs_count, hform⟩ |
    ⟨a, Q, hQ_deg, ha_ne, ha_fin, ha_card, hsum, hform⟩
  · left
    rw [hfloor] at hQ_deg hform
    have hQ_eval : ∀ z : ℂ, Q.eval z = Q.coeff 0 := fun z ↦ by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ_deg)]
      simp
    refine ⟨zs, Q.coeff 0, hzs_ne, hzs_count, fun z ↦ ?_⟩
    simpa [hQ_eval z] using hform z
  · right
    rw [hfloor] at hQ_deg hsum hform
    have hQ_eval : ∀ z : ℂ, Q.eval z = Q.coeff 0 := fun z ↦ by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ_deg)]
      simp
    refine ⟨a, Q.coeff 0, ha_ne, ha_fin, ha_card, by simpa using hsum, fun z ↦ ?_⟩
    simpa [hQ_eval z] using hform z

/-- **Genus-1 Hadamard factorization (given zero enumeration)**: if `f : ℂ → ℂ` is nonzero of
order `ρ` with `0 ≤ ρ < 2` and `a : ℕ → ℂ` enumerates the nonzero zeros of `f` with multiplicity,
then `∑ ‖a n‖ ^ (-2)` converges and there exist `A, B : ℂ` such that
`f z = z ^ analyticOrderNatAt f 0 * Complex.exp (A + B * z) * canonicalProduct a 1 z`. -/
theorem hadamard_factorization_of_zeros_genus_one {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ)
    (hρ2 : ρ < 2) {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0)
    (ha_fin : ∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite)
    (ha_card : ∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) :
    Summable (fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
      ∃ A B : ℂ, ∀ z : ℂ,
        f z = z ^ analyticOrderNatAt f 0 * Complex.exp (A + B * z) * canonicalProduct a 1 z := by
  obtain ⟨hsum, Q, hQ_deg, hform⟩ :=
    hadamard_factorization_of_zeros hf hf_ne hρ hord (p := 1) (by norm_num; linarith)
      ha_ne ha_fin ha_card
  have hQ_eval : ∀ z : ℂ, Q.eval z = Q.coeff 0 + Q.coeff 1 * z := fun z ↦ by
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ]
  refine ⟨by simpa using hsum, Q.coeff 0, Q.coeff 1, fun z ↦ ?_⟩
  simpa [hQ_eval z] using hform z

/-- **Genus-1 Hadamard factorization (general form)**: any nonzero entire function `f : ℂ → ℂ` of
order `ρ` with `0 ≤ ρ < 2` factors as `z ^ m * Complex.exp (A + B * z) * P z`, where `P` is either
a finite genus-`1` primary product over `zs : List ℂ` or a convergent genus-`1` canonical product
`canonicalProduct a 1 z`. -/
theorem hadamard_factorization_genus_one {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ)
    (hρ2 : ρ < 2) :
    (∃ (zs : List ℂ) (A B : ℂ),
      (∀ a ∈ zs, a ≠ 0) ∧ (∀ z ≠ 0, zs.count z = analyticOrderNatAt f z) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (A + B * z) *
        (zs.map (fun a ↦ weierstrassPrimaryFactor 1 (z / a))).prod)) ∨
    (∃ (a : ℕ → ℂ) (A B : ℂ),
      (∀ n, a n ≠ 0) ∧ (∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite) ∧
      (∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) ∧
      Summable (fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (A + B * z) *
        canonicalProduct a 1 z)) := by
  classical
  obtain ⟨f₀, hf₀_diff, hf₀_at_0, hf₀_eq, hf₀_ord⟩ :=
    exists_div_pow_entire_of_differentiable hf hf_ne 0
  have hf₀_zero_iff : ∀ z ≠ 0, f₀ z = 0 ↔ f z = 0 := by
    intro z hzc
    rw [hf₀_eq z, sub_zero]
    exact mul_eq_zero_iff_left (pow_ne_zero _ hzc) |>.symm
  let Zset : Set ℂ := {z : ℂ | z ≠ 0 ∧ f₀ z = 0}
  by_cases hfin : Zset.Finite
  · left
    let S : Finset ℂ := hfin.toFinset
    let zs : List ℂ := S.toList.flatMap (fun z ↦ List.replicate (analyticOrderNatAt f z) z)
    have hzs_ne : ∀ a ∈ zs, a ≠ 0 := by
      intro a ha
      rw [List.mem_flatMap] at ha
      obtain ⟨b, hbS, hba⟩ := ha
      rw [List.mem_replicate] at hba
      rw [hba.2]
      exact (hfin.mem_toFinset.mp (Finset.mem_toList.mp hbS)).1
    have hzs_count : ∀ z ≠ 0, zs.count z = analyticOrderNatAt f z := by
      intro z hzc
      dsimp only [zs]
      rw [list_count_flatMap_replicate (Finset.nodup_toList S)]
      by_cases hzS : z ∈ S.toList
      · simp [hzS]
      · rw [ite_eq_right_iff.mpr fun h ↦ False.elim (hzS h)]
        have hz_not_mem : z ∉ Zset := fun hmem ↦
          hzS (Finset.mem_toList.mpr (hfin.mem_toFinset.mpr hmem))
        have hfz_orig : f z ≠ 0 := (hf₀_zero_iff z hzc).not.mp (fun h0 ↦ hz_not_mem ⟨hzc, h0⟩)
        have : analyticOrderAt f z = 0 :=
          ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).analyticOrderAt_eq_zero.mpr hfz_orig
        simp [analyticOrderNatAt, this]
    obtain ⟨_, Q, hQ_deg, hQ_form⟩ :=
      hadamard_factorization_of_finite_zeros hf hf_ne hρ hord (p := 1) (by norm_num; linarith)
        hzs_ne hzs_count
    have hQ_eval : ∀ z : ℂ, Q.eval z = Q.coeff 0 + Q.coeff 1 * z := fun z ↦ by
      rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
      simp [Finset.sum_range_succ]
    refine ⟨zs, Q.coeff 0, Q.coeff 1, hzs_ne, hzs_count, fun z ↦ ?_⟩
    simpa [hQ_eval z] using hQ_form z
  · right
    rcases hadamard_factorization hf hf_ne hρ hord with
      ⟨zs, _, _, hzs_ne, hzs_count, _⟩ |
      ⟨a, _, _, ha_ne, ha_fin, ha_card, _, _⟩
    · exfalso
      apply hfin
      have hsub : Zset ⊆ zs.toFinset := by
        intro z hz
        have hfz : f z = 0 := (hf₀_zero_iff z hz.1).mp hz.2
        have hne0 : analyticOrderAt f z ≠ 0 :=
          ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).analyticOrderAt_ne_zero.mpr hfz
        have htop : analyticOrderAt f z ≠ ⊤ :=
          analyticOrderAt_ne_top_of_differentiable_ne_zero hf hf_ne z
        have hpos : 0 < zs.count z := by
          rw [hzs_count z hz.1]
          rw [← Nat.cast_analyticOrderNatAt htop] at hne0
          exact Nat.pos_of_ne_zero (by simpa using hne0)
        exact List.mem_toFinset.mpr (List.count_pos_iff.mp hpos)
      exact zs.toFinset.finite_toSet.subset hsub
    · obtain ⟨hsum, A, B, hform⟩ :=
        hadamard_factorization_of_zeros_genus_one hf hf_ne hρ hord hρ2 ha_ne ha_fin ha_card
      exact ⟨a, A, B, ha_ne, ha_fin, ha_card, hsum, hform⟩

/-!
### Section 6: Logarithmic Derivative Partial Fraction Expansions
-/

private lemma logDeriv_fun_mul_aux (f g : ℂ → ℂ) (z : ℂ) (hf_ne : f z ≠ 0) (hg_ne : g z ≠ 0)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    logDeriv (fun w ↦ f w * g w) z = logDeriv f z + logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, logDeriv_apply, (hf.hasDerivAt.fun_mul hg.hasDerivAt).deriv]
  field_simp [hf_ne, hg_ne]

/-- Explicit logarithmic derivative of a shifted Weierstrass primary factor `w ↦ E_p(w / a)` at any
`z ≠ a` (`a ≠ 0`):
`logDeriv (fun w ↦ weierstrassPrimaryFactor p (w / a)) z = 1 / (z - a) + ∑ k ∈ Finset.Icc 1 p, z ^ (k - 1) / a ^ k`. -/
theorem logDeriv_weierstrassPrimaryFactor_div (p : ℕ) {a z : ℂ} (ha : a ≠ 0) (hza : z ≠ a) :
    logDeriv (fun w ↦ weierstrassPrimaryFactor p (w / a)) z =
      1 / (z - a) + ∑ k ∈ Finset.Icc 1 p, z ^ (k - 1) / a ^ k := by
  let S : ℂ → ℂ := fun w ↦ ∑ k ∈ Finset.Icc 1 p, (w / a) ^ k / (k : ℂ)
  let dS : ℂ := ∑ k ∈ Finset.Icc 1 p, z ^ (k - 1) / a ^ k
  have hS_deriv : HasDerivAt S dS z := by
    have hterm : ∀ k ∈ Finset.Icc 1 p,
        HasDerivAt (fun w : ℂ ↦ (w / a) ^ k / (k : ℂ)) (z ^ (k - 1) / a ^ k) z := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have hdiv : HasDerivAt (fun w : ℂ ↦ w / a) (1 / a) z := by
        simpa using (hasDerivAt_id z).div_const a
      have hpow : HasDerivAt (fun w : ℂ ↦ (w / a) ^ k)
          (((k : ℂ) * (z / a) ^ (k - 1)) * (1 / a)) z := by
        simpa using hdiv.fun_pow k
      have hfin := hpow.div_const (k : ℂ)
      have hval : (((k : ℂ) * (z / a) ^ (k - 1)) * (1 / a)) / (k : ℂ) = z ^ (k - 1) / a ^ k := by
        have ha_pow : a ^ k = a ^ (k - 1) * a := by
          rw [← pow_succ, Nat.sub_add_cancel hk1]
        rw [div_pow, ha_pow]
        field_simp [ha, hkc]
      rwa [hval] at hfin
    simpa [S, dS] using HasDerivAt.fun_sum hterm
  have hlin_deriv : HasDerivAt (fun w : ℂ ↦ 1 - w / a) (-(1 / a)) z := by
    simpa using (hasDerivAt_const z (1 : ℂ)).fun_sub ((hasDerivAt_id z).div_const a)
  have hfull_deriv : HasDerivAt (fun w ↦ weierstrassPrimaryFactor p (w / a))
      ((-(1 / a)) * Complex.exp (S z) + (1 - z / a) * (Complex.exp (S z) * dS)) z :=
    hlin_deriv.fun_mul hS_deriv.cexp
  have h1sub_ne : 1 - z / a ≠ 0 := by
    intro h0
    apply hza
    exact (div_eq_one_iff_eq ha).mp (sub_eq_zero.mp h0).symm
  rw [logDeriv_apply, hfull_deriv.deriv]
  simp only [weierstrassPrimaryFactor]
  change ((-(1 / a)) * Complex.exp (S z) + (1 - z / a) * (Complex.exp (S z) * dS)) /
      ((1 - z / a) * Complex.exp (S z)) = 1 / (z - a) + dS
  have hexp_ne : Complex.exp (S z) ≠ 0 := Complex.exp_ne_zero _
  have hz_sub_ne : z - a ≠ 0 := sub_ne_zero.mpr hza
  field_simp [ha, h1sub_ne, hexp_ne, hz_sub_ne]
  ring

/-- **Logarithmic derivative of a canonical product**: when `∀ n, a n ≠ 0` and
`∑ ‖a n‖ ^ (-(p + 1))` converges, at every `z` avoiding `{a n}` we have
`logDeriv (canonicalProduct a p) z = ∑' n, (1 / (z - a n) + ∑ k ∈ Finset.Icc 1 p, z ^ (k - 1) / a n ^ k)`. -/
theorem logDeriv_canonicalProduct_eq_tsum {a : ℕ → ℂ} {p : ℕ}
    (ha_ne : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))))
    {z : ℂ} (hz_ne : ∀ n, z ≠ a n) :
    logDeriv (canonicalProduct a p) z =
      ∑' n : ℕ, (1 / (z - a n) + ∑ k ∈ Finset.Icc 1 p, z ^ (k - 1) / a n ^ k) := by
  let term : ℕ → ℂ → ℂ := fun n w ↦ weierstrassPrimaryFactor p (w / a n) - 1
  have hterm_diff : ∀ n, DifferentiableOn ℂ (term n) univ := fun n ↦
    (((differentiable_weierstrassPrimaryFactor p).comp
      (differentiable_id.div_const (a n))).sub_const 1).differentiableOn
  have htend_norm := tendsto_norm_atTop_of_summable ha_ne (Nat.cast_pos.mpr (Nat.succ_pos p)) hsum
  have hbound : ∀ K ⊆ (univ : Set ℂ), IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ n in atTop, ∀ w ∈ K, ‖term n w‖ ≤ u n := by
    intro K _ hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    let R : ℝ := max R₀ 1
    have hR_ge : 1 ≤ R := le_max_right R₀ 1
    have hR_pos : 0 < R := zero_lt_one.trans_le hR_ge
    refine ⟨fun n ↦ (2 * R ^ (p + 1)) * ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)), hsum.mul_left _, ?_⟩
    filter_upwards [htend_norm.eventually_ge_atTop (2 * R)] with n hn w hwK
    have hw_norm : ‖w‖ ≤ R := by
      have hw_cb := hR₀ hwK
      rw [Metric.mem_closedBall, dist_zero_right] at hw_cb
      exact hw_cb.trans (le_max_left R₀ 1)
    have han_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (ha_ne n)
    have hdiv_half : ‖w / a n‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ han_pos]
      linarith
    refine (norm_weierstrassPrimaryFactor_sub_one_le p hdiv_half).trans ?_
    rw [norm_div, div_pow, div_eq_mul_inv]
    have hpow : ‖w‖ ^ (p + 1) ≤ R ^ (p + 1) := pow_le_pow_left₀ (norm_nonneg w) hw_norm (p + 1)
    have hinv_eq : (‖a n‖ ^ (p + 1))⁻¹ = ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast ‖a n‖ (p + 1), Real.rpow_neg (norm_nonneg _)]
    rw [hinv_eq]
    have hinv_nonneg : 0 ≤ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    calc
      2 * (‖w‖ ^ (p + 1) * ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)))
        = (2 * ‖w‖ ^ (p + 1)) * ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)) := by ring
      _ ≤ (2 * R ^ (p + 1)) * ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow zero_le_two) hinv_nonneg
  have hne_z : ∀ n, 1 + term n z ≠ 0 := by
    intro n
    simp only [term, add_sub_cancel, ne_eq, weierstrassPrimaryFactor_eq_zero_iff,
      div_eq_one_iff_eq (ha_ne n)]
    exact hz_ne n
  have hdiv_eq := deriv_tprod_nat_one_add_div_eq_tsum isOpen_univ hterm_diff hbound (mem_univ z) hne_z
  have hprod_eq : (fun w : ℂ ↦ ∏' n : ℕ, (1 + term n w)) = canonicalProduct a p := by
    ext w
    simp [term, canonicalProduct]
  have hprod_z : ∏' n : ℕ, (1 + term n z) = canonicalProduct a p z := congrFun hprod_eq z
  rw [hprod_eq, hprod_z, ← logDeriv_apply] at hdiv_eq
  rw [hdiv_eq]
  refine tsum_congr fun n ↦ ?_
  have hdiff_fac : DifferentiableAt ℂ (fun w ↦ weierstrassPrimaryFactor p (w / a n)) z :=
    ((differentiable_weierstrassPrimaryFactor p).comp (differentiable_id.div_const (a n))) z
  have hd_sub : deriv (term n) z = deriv (fun w ↦ weierstrassPrimaryFactor p (w / a n)) z :=
    (hdiff_fac.hasDerivAt.sub_const 1).deriv
  have h1add : 1 + term n z = weierstrassPrimaryFactor p (z / a n) := by simp [term]
  rw [hd_sub, h1add, ← logDeriv_apply]
  exact logDeriv_weierstrassPrimaryFactor_div p (ha_ne n) (hz_ne n)

/-- Quotient-form logarithmic derivative formula `deriv (canonicalProduct a p) z / canonicalProduct a p z`
away from the zeros `{a n}`. -/
theorem deriv_canonicalProduct_div_eq_tsum {a : ℕ → ℂ} {p : ℕ}
    (ha_ne : ∀ n, a n ≠ 0)
    (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((p + 1 : ℕ) : ℝ))))
    {z : ℂ} (hz_ne : ∀ n, z ≠ a n) :
    deriv (canonicalProduct a p) z / canonicalProduct a p z =
      ∑' n : ℕ, (1 / (z - a n) + ∑ k ∈ Finset.Icc 1 p, z ^ (k - 1) / a n ^ k) := by
  simpa [logDeriv_apply] using logDeriv_canonicalProduct_eq_tsum ha_ne hsum hz_ne

private lemma logDeriv_list_prod_primary (p : ℕ) (zs : List ℂ) {z : ℂ}
    (h : ∀ a ∈ zs, a ≠ 0 ∧ z ≠ a) :
    logDeriv (fun w ↦ (zs.map (fun a ↦ weierstrassPrimaryFactor p (w / a))).prod) z =
      (zs.map (fun a ↦ 1 / (z - a) + ∑ k ∈ Finset.Icc 1 p, z ^ (k - 1) / a ^ k)).sum := by
  induction zs with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    rw [logDeriv_apply, deriv_const, zero_div]
  | cons a zs ih =>
    have ha_ne : a ≠ 0 := (h a (by simp)).1
    have hza : z ≠ a := (h a (by simp)).2
    have ih' := ih fun b hb ↦ h b (by simp [hb])
    have hmul : (fun w ↦ ((a :: zs).map (fun b ↦ weierstrassPrimaryFactor p (w / b))).prod) =
        fun w ↦ weierstrassPrimaryFactor p (w / a) *
          (zs.map (fun b ↦ weierstrassPrimaryFactor p (w / b))).prod := by
      ext w; simp only [List.map_cons, List.prod_cons]
    have hhead_diff : DifferentiableAt ℂ (fun w ↦ weierstrassPrimaryFactor p (w / a)) z :=
      ((differentiable_weierstrassPrimaryFactor p).comp (differentiable_id.div_const a)) z
    have htail_diff : DifferentiableAt ℂ
        (fun w ↦ (zs.map (fun b ↦ weierstrassPrimaryFactor p (w / b))).prod) z :=
      list_prod_primary_differentiable p zs z
    have hhead_ne : weierstrassPrimaryFactor p (z / a) ≠ 0 := by
      rw [ne_eq, weierstrassPrimaryFactor_eq_zero_iff, div_eq_one_iff_eq ha_ne]
      exact hza
    have htail_ne : (zs.map (fun b ↦ weierstrassPrimaryFactor p (z / b))).prod ≠ 0 := by
      intro h0
      rw [List.prod_eq_zero_iff] at h0
      obtain ⟨b, hb_zs, hbu⟩ := List.mem_map.mp h0
      have hb := h b (by simp [hb_zs])
      rw [weierstrassPrimaryFactor_eq_zero_iff, div_eq_one_iff_eq hb.1] at hbu
      exact hb.2 hbu
    rw [hmul,
      logDeriv_fun_mul_aux (fun w ↦ weierstrassPrimaryFactor p (w / a))
        (fun w ↦ (zs.map (fun b ↦ weierstrassPrimaryFactor p (w / b))).prod) z
        hhead_ne htail_ne hhead_diff htail_diff,
      logDeriv_weierstrassPrimaryFactor_div p ha_ne hza, ih']
    simp only [List.map_cons, List.sum_cons]

/-- **Logarithmic derivative partial fraction expansion for a genus-1 Hadamard product**:
if `f z = z ^ m * Complex.exp (A + B * z) * canonicalProduct a 1 z` with `∀ n, a n ≠ 0` and
`∑ ‖a n‖ ^ (-2)` convergent, then at any `z ≠ 0` avoiding `{a n}` we have
`logDeriv f z = (m : ℂ) / z + B + ∑' n, (1 / (z - a n) + 1 / a n)`. -/
theorem logDeriv_eq_partial_fractions_of_genus_one_product {f : ℂ → ℂ} {m : ℕ} {A B : ℂ}
    {a : ℕ → ℂ} (ha_ne : ∀ n, a n ≠ 0) (hsum : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)))
    (hform : ∀ z : ℂ, f z = z ^ m * Complex.exp (A + B * z) * canonicalProduct a 1 z)
    {z : ℂ} (hz0 : z ≠ 0) (hz_ne : ∀ n, z ≠ a n) :
    logDeriv f z = (m : ℂ) / z + B + ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
  have hfun : f = fun w ↦ (w ^ m * Complex.exp (A + B * w)) * canonicalProduct a 1 w := by
    ext w; exact hform w
  have hsum1 : Summable (fun n : ℕ ↦ ‖a n‖ ^ (-((1 + 1 : ℕ) : ℝ))) := by simpa using hsum
  have hP_diff : DifferentiableAt ℂ (canonicalProduct a 1) z :=
    differentiable_canonicalProduct ha_ne hsum1 z
  have hP_ne : canonicalProduct a 1 z ≠ 0 := by
    rw [ne_eq, canonicalProduct_eq_zero_iff ha_ne hsum1]
    rintro ⟨n, rfl⟩
    exact hz_ne n rfl
  have hexp_diff : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.exp (A + B * w)) z :=
    (differentiable_const A |>.add (differentiable_const B |>.mul differentiable_id)).cexp z
  have hpow_diff : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ m) z := (differentiable_id.pow m) z
  have hpow_ne : z ^ m ≠ 0 := pow_ne_zero m hz0
  have hexp_ne : Complex.exp (A + B * z) ≠ 0 := Complex.exp_ne_zero _
  have hm_diff : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ m * Complex.exp (A + B * w)) z :=
    hpow_diff.fun_mul hexp_diff
  have hm_ne : z ^ m * Complex.exp (A + B * z) ≠ 0 := mul_ne_zero hpow_ne hexp_ne
  rw [hfun,
    logDeriv_fun_mul_aux (fun w : ℂ ↦ w ^ m * Complex.exp (A + B * w)) (canonicalProduct a 1) z
      hm_ne hP_ne hm_diff hP_diff,
    logDeriv_fun_mul_aux (fun w : ℂ ↦ w ^ m) (fun w : ℂ ↦ Complex.exp (A + B * w)) z
      hpow_ne hexp_ne hpow_diff hexp_diff]
  have hld_pow : logDeriv (fun w : ℂ ↦ w ^ m) z = (m : ℂ) / z := by
    rw [logDeriv_apply, (hasDerivAt_pow m z).deriv]
    rcases m with _ | m'
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      field_simp [hz0]
  have hld_exp : logDeriv (fun w : ℂ ↦ Complex.exp (A + B * w)) z = B := by
    have hd : HasDerivAt (fun w : ℂ ↦ Complex.exp (A + B * w))
        (Complex.exp (A + B * z) * B) z := by
      have hlin : HasDerivAt (fun w : ℂ ↦ A + B * w) B z := by
        simpa using (hasDerivAt_const z A).fun_add ((hasDerivAt_id z).const_mul B)
      exact hlin.cexp
    rw [logDeriv_apply, hd.deriv]
    field_simp [hexp_ne]
  have hld_P : logDeriv (canonicalProduct a 1) z = ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
    simpa [Finset.Icc_self] using logDeriv_canonicalProduct_eq_tsum ha_ne hsum1 hz_ne
  rw [hld_pow, hld_exp, hld_P]

/-- **Logarithmic derivative partial fraction expansion for a finite genus-1 Hadamard product**. -/
theorem logDeriv_eq_partial_fractions_of_finite_genus_one_product {f : ℂ → ℂ} {m : ℕ} {A B : ℂ}
    {zs : List ℂ} (hzs_ne : ∀ a ∈ zs, a ≠ 0)
    (hform : ∀ z : ℂ, f z = z ^ m * Complex.exp (A + B * z) *
      (zs.map (fun a ↦ weierstrassPrimaryFactor 1 (z / a))).prod)
    {z : ℂ} (hz0 : z ≠ 0) (hz_ne : ∀ a ∈ zs, z ≠ a) :
    logDeriv f z = (m : ℂ) / z + B + (zs.map (fun a ↦ 1 / (z - a) + 1 / a)).sum := by
  let P : ℂ → ℂ := fun w ↦ (zs.map (fun a ↦ weierstrassPrimaryFactor 1 (w / a))).prod
  have hfun : f = fun w ↦ (w ^ m * Complex.exp (A + B * w)) * P w := by
    ext w; exact hform w
  have hP_diff : DifferentiableAt ℂ P z := list_prod_primary_differentiable 1 zs z
  have hP_ne : P z ≠ 0 := by
    dsimp only [P]
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    obtain ⟨a, ha_zs, hau⟩ := List.mem_map.mp h0
    rw [weierstrassPrimaryFactor_eq_zero_iff, div_eq_one_iff_eq (hzs_ne a ha_zs)] at hau
    exact hz_ne a ha_zs hau
  have hexp_diff : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.exp (A + B * w)) z :=
    (differentiable_const A |>.add (differentiable_const B |>.mul differentiable_id)).cexp z
  have hpow_diff : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ m) z := (differentiable_id.pow m) z
  have hpow_ne : z ^ m ≠ 0 := pow_ne_zero m hz0
  have hexp_ne : Complex.exp (A + B * z) ≠ 0 := Complex.exp_ne_zero _
  have hm_diff : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ m * Complex.exp (A + B * w)) z :=
    hpow_diff.fun_mul hexp_diff
  have hm_ne : z ^ m * Complex.exp (A + B * z) ≠ 0 := mul_ne_zero hpow_ne hexp_ne
  rw [hfun,
    logDeriv_fun_mul_aux (fun w : ℂ ↦ w ^ m * Complex.exp (A + B * w)) P z
      hm_ne hP_ne hm_diff hP_diff,
    logDeriv_fun_mul_aux (fun w : ℂ ↦ w ^ m) (fun w : ℂ ↦ Complex.exp (A + B * w)) z
      hpow_ne hexp_ne hpow_diff hexp_diff]
  have hld_pow : logDeriv (fun w : ℂ ↦ w ^ m) z = (m : ℂ) / z := by
    rw [logDeriv_apply, (hasDerivAt_pow m z).deriv]
    rcases m with _ | m'
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      field_simp [hz0]
  have hld_exp : logDeriv (fun w : ℂ ↦ Complex.exp (A + B * w)) z = B := by
    have hd : HasDerivAt (fun w : ℂ ↦ Complex.exp (A + B * w))
        (Complex.exp (A + B * z) * B) z := by
      have hlin : HasDerivAt (fun w : ℂ ↦ A + B * w) B z := by
        simpa using (hasDerivAt_const z A).fun_add ((hasDerivAt_id z).const_mul B)
      exact hlin.cexp
    rw [logDeriv_apply, hd.deriv]
    field_simp [hexp_ne]
  have hld_P : logDeriv P z = (zs.map (fun a ↦ 1 / (z - a) + 1 / a)).sum := by
    simpa [Finset.Icc_self] using logDeriv_list_prod_primary 1 zs fun a ha ↦ ⟨hzs_ne a ha, hz_ne a ha⟩
  rw [hld_pow, hld_exp, hld_P]

/-- **Partial fraction expansion of the logarithmic derivative for any entire function of order `< 2`**:
if `f : ℂ → ℂ` is nonzero and satisfies `EntireOrderLe f ρ` with `0 ≤ ρ < 2`, then either `f` has
finitely many nonzero zeros `zs : List ℂ` or an infinite zero enumeration `a : ℕ → ℂ` with
`∑ ‖a n‖ ^ (-2) < ∞`, and away from `0` and the zeros of `f`, `deriv f z / f z` equals
`m / z + B + ∑ (1 / (z - ρ_n) + 1 / ρ_n)`. -/
theorem hadamard_logDeriv_genus_one {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (hρ : 0 ≤ ρ) (hord : EntireOrderLe f ρ)
    (hρ2 : ρ < 2) :
    (∃ (zs : List ℂ) (A B : ℂ),
      (∀ a ∈ zs, a ≠ 0) ∧ (∀ z ≠ 0, zs.count z = analyticOrderNatAt f z) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (A + B * z) *
        (zs.map (fun a ↦ weierstrassPrimaryFactor 1 (z / a))).prod) ∧
      (∀ z : ℂ, z ≠ 0 → f z ≠ 0 →
        deriv f z / f z = (analyticOrderNatAt f 0 : ℂ) / z + B +
          (zs.map (fun a ↦ 1 / (z - a) + 1 / a)).sum)) ∨
    (∃ (a : ℕ → ℂ) (A B : ℂ),
      (∀ n, a n ≠ 0) ∧ (∀ R : ℝ, ({n : ℕ | ‖a n‖ ≤ R}).Finite) ∧
      (∀ z ≠ 0, ({n : ℕ | a n = z}).ncard = analyticOrderNatAt f z) ∧
      Summable (fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
      (∀ z : ℂ, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (A + B * z) *
        canonicalProduct a 1 z) ∧
      (∀ z : ℂ, z ≠ 0 → f z ≠ 0 →
        deriv f z / f z = (analyticOrderNatAt f 0 : ℂ) / z + B +
          ∑' n : ℕ, (1 / (z - a n) + 1 / a n))) := by
  rcases hadamard_factorization_genus_one hf hf_ne hρ hord hρ2 with
    ⟨zs, A, B, hzs_ne, hzs_count, hform⟩ |
    ⟨a, A, B, ha_ne, ha_fin, ha_card, hsum, hform⟩
  · left
    refine ⟨zs, A, B, hzs_ne, hzs_count, hform, fun z hz0 hfz ↦ ?_⟩
    have hz_not : ∀ a ∈ zs, z ≠ a := by
      intro a ha hza
      subst hza
      have hpos : 0 < zs.count z := List.count_pos_iff.mpr ha
      rw [hzs_count z hz0] at hpos
      exact hfz (apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne')
    simpa [logDeriv_apply] using
      logDeriv_eq_partial_fractions_of_finite_genus_one_product hzs_ne hform hz0 hz_not
  · right
    refine ⟨a, A, B, ha_ne, ha_fin, ha_card, hsum, hform, fun z hz0 hfz ↦ ?_⟩
    have hz_not : ∀ n, z ≠ a n := by
      intro n hza
      have hfin_fiber : ({k : ℕ | a k = z}).Finite :=
        (ha_fin ‖z‖).subset fun k hk ↦ by simp only [Set.mem_ofPred_eq] at hk ⊢; rw [hk]
      have hpos : 0 < ({k : ℕ | a k = z}).ncard := (Set.ncard_pos hfin_fiber).mpr ⟨n, hza.symm⟩
      rw [ha_card z hz0] at hpos
      exact hfz (apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne')
    simpa [logDeriv_apply] using
      logDeriv_eq_partial_fractions_of_genus_one_product ha_ne hsum hform hz0 hz_not

end AnalyticNumberTheory.AnalyticTools.EntireFunctions



