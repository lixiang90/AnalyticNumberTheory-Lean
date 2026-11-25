import AnalyticNumberTheory.DirichletLFunctions.CriticalPointwiseMeans
import AnalyticNumberTheory.AnalyticTools.CriticalLinePerronWeights

/-! # Integrals of the fixed-modulus critical-line means -/

noncomputable section

open Complex Real Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.DirichletLFunctions

/-- The Euclidean norm of a family on the critical line, with the principal
character removed; the argument `t` is the signed ordinate. -/
def nonprincipalCriticalNorm {q : ℕ} (G : DirichletCharacter ℂ q → ℂ → ℂ) (t : ℝ) : ℝ :=
  Real.sqrt (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖G χ ((1/2 : ℂ)+t*I)‖^2)

theorem continuous_nonprincipalCriticalNorm {q : ℕ} (G : DirichletCharacter ℂ q → ℂ → ℂ)
    (hG : ∀ χ, χ ≠ 1 → Continuous (G χ)) : Continuous (nonprincipalCriticalNorm G) := by
  apply Real.continuous_sqrt.comp
  exact continuous_finsetSum _ fun χ hχ => ((hG χ (mem_filter.mp hχ).2).comp
    (by fun_prop : Continuous fun t : ℝ => (1/2 : ℂ)+t*I)).norm.pow 2

private lemma root_mean_bound {X C Φ U L : ℝ} {k : ℕ} (hC : 0 ≤ C) (hφ : 0 ≤ Φ)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (h : X ≤ C*Φ*U*(L^k)^2) :
    Real.sqrt X ≤ (Real.sqrt C * Real.sqrt Φ) * (Real.sqrt U * L^k) := by
  apply Real.sqrt_le_iff.mpr ⟨by positivity, h.trans_eq ?_⟩
  simp only [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hφ, Real.sq_sqrt hU]
  ring

/-- Integrating the square roots of the nonprincipal character means against
`dt/|s|²` gives `√φ(q) (1+log q)` for `L` and `√φ(q) (1+log q)²` for `L′`.
Both integrands are absolutely integrable on the whole critical line. -/
theorem nonprincipal_critical_perron_means :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], 2 ≤ q →
      let V := nonprincipalCriticalNorm (q := q) (fun χ => χ.LFunction)
      let D := nonprincipalCriticalNorm (q := q) (fun χ => deriv χ.LFunction)
      let W := fun t : ℝ => ‖(1/2 : ℂ)+t*I‖^2
      Integrable (fun t => V t / W t) ∧ Integrable (fun t => D t / W t) ∧
        (∫ t : ℝ, V t / W t) ≤ C * Real.sqrt q.totient * (1+Real.log q) ∧
        (∫ t : ℝ, D t / W t) ≤ C * Real.sqrt q.totient * (1+Real.log q)^2 := by
  obtain ⟨A, hA, means⟩ := nonprincipal_critical_pointwise_means
  obtain ⟨B, hB, integrate⟩ := critical_line_perron_integral_bound
  refine ⟨B*Real.sqrt A, by positivity, ?_⟩
  intro q _ hq V D W
  let K := Real.sqrt A * Real.sqrt q.totient
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hval : Continuous V := continuous_nonprincipalCriticalNorm _ fun _ h => (differentiable_LFunction_of_ne_one h).continuous
  have hder : Continuous D := continuous_nonprincipalCriticalNorm _ fun _ h =>
    continuous_iff_continuousAt.mpr fun z => ((differentiable_LFunction_of_ne_one h).analyticAt z).deriv.continuousAt
  have point (t : ℝ) :
      let s := (1/2 : ℂ)+t*I
      let U := 1+‖s‖
      let L := 1+Real.log ((q : ℝ)*U)
      V t ≤ K*(Real.sqrt U*L^1) ∧ D t ≤ K*(Real.sqrt U*L^2) := by
    intro s U L
    have hh := means hq (s := s) (by simp [s])
    have hU : 1 ≤ U := by dsimp only [U]; linarith [norm_nonneg s]
    have hL : 0 ≤ L := add_nonneg zero_le_one (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq₁ hU))
    constructor
    · apply root_mean_bound hA.le (Nat.cast_nonneg _) (zero_le_one.trans hU) hL
      simpa only [pow_one] using hh.1
    · apply root_mean_bound hA.le (Nat.cast_nonneg _) (zero_le_one.trans hU) hL
      simpa only [← pow_mul, show 2*2 = 4 by decide] using hh.2
  have hv := integrate hq₁ hK (by decide : 1 ≤ 2) V hval (fun _ => Real.sqrt_nonneg _) (fun t => (point t).1)
  have hd := integrate hq₁ hK (by decide : 2 ≤ 2) D hder (fun _ => Real.sqrt_nonneg _) (fun t => (point t).2)
  refine ⟨hv.1, hd.1, hv.2.trans_eq ?_, hd.2.trans_eq ?_⟩
  · dsimp only [K]
    ring
  · dsimp only [K]
    ring

end AnalyticNumberTheory.DirichletLFunctions
