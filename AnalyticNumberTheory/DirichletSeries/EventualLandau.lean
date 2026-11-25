import AnalyticNumberTheory.DirichletSeries.FrequencyLandau
import AnalyticNumberTheory.DirichletSeries.FrequencyTruncation

/-! # Landau's theorem for eventually nonnegative coefficients -/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

/-- Finitely many arbitrary complex coefficients do not affect Landau's
singularity theorem. Holomorphy on the disk forces absolute convergence
throughout the half-plane to the right of its leftmost real boundary point. -/
theorem landau_absoluteAbscissa_le_of_eventually_nonneg {F : DirichletFrequency} {a : ℕ → ℂ}
    {σ r : ℝ} {G : ℂ → ℂ} (ha : ∀ᶠ n in atTop, ∃ y : ℝ, 0 ≤ y ∧ a n = (y : ℂ)) (hr : 0 < r)
    (hσ : F.abscissa a ≤ (σ : EReal)) (hG : DifferentiableOn ℂ G (ball (σ : ℂ) r))
    (heq : ∀ z ∈ ball (σ : ℂ) r, σ < z.re → G z = F.sum a z) :
    F.absoluteAbscissa a ≤ ((σ-r : ℝ) : EReal) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ha
  let b (n : ℕ) : ℝ := if N ≤ n then (a n).re else 0
  have hb (n : ℕ) : 0 ≤ b n := by
    by_cases hn : N ≤ n
    · obtain ⟨y,hy,hn'⟩ := hN n hn
      simpa [b,hn,hn'] using hy
    · simp [b,hn]
  have htail : (fun n => (b n : ℂ)) = (Ici N).indicator a := by
    funext n
    by_cases hn : N ≤ n
    · obtain ⟨y,_,hy⟩ := hN n hn
      simp [b,hn,hy]
    · simp [b,hn]
  have hσ' : F.abscissa (fun n => (b n : ℂ)) ≤ (σ : EReal) := by rwa [htail,F.abscissa_tail]
  have hpoly : Differentiable ℂ (fun z => F.partialSum a z N) := by unfold partialSum; fun_prop
  let G' (z : ℂ) := G z - F.partialSum a z N
  have hG' : DifferentiableOn ℂ G' (ball (σ : ℂ) r) := hG.sub hpoly.differentiableOn
  have heq' (z : ℂ) (hz : z ∈ ball (σ : ℂ) r) (hz' : σ < z.re) :
      G' z = F.sum (fun n => (b n : ℂ)) z := by
    rw [htail,F.sum_tail_eq_sub a (convergesAt_of_abscissa_lt (hσ.trans_lt (EReal.coe_lt_coe_iff.mpr hz')))]
    exact congrArg (fun v => v - F.partialSum a z N) (heq z hz hz')
  have H := landau_absoluteAbscissa_le hb hr hσ' hG' heq'
  rwa [htail,F.absoluteAbscissa_tail] at H

/-- At a finite real abscissa, no holomorphic extension from the right exists
when all but finitely many coefficients are nonnegative real numbers. -/
theorem no_continuation_of_eventually_nonneg {F : DirichletFrequency} {a : ℕ → ℂ}
    {σ r : ℝ} {G : ℂ → ℂ} (ha : ∀ᶠ n in atTop, ∃ y : ℝ, 0 ≤ y ∧ a n = (y : ℂ)) (hr : 0 < r)
    (hσ : F.abscissa a = (σ : EReal)) (hG : DifferentiableOn ℂ G (ball (σ : ℂ) r)) :
    ¬ (∀ z ∈ ball (σ : ℂ) r, σ < z.re → G z = F.sum a z) := by
  intro heq
  have H := (F.abscissa_le_absoluteAbscissa a).trans
    (landau_absoluteAbscissa_le_of_eventually_nonneg ha hr hσ.le hG heq)
  rw [hσ] at H
  have := EReal.coe_le_coe_iff.mp H
  linarith

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
