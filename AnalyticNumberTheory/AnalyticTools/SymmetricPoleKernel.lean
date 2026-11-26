import AnalyticNumberTheory.AnalyticTools.IntegratedPoleTransform

/-! # The symmetric difference kernel for a family of poles -/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- The contribution of one pole to a central difference of logarithmic width `h`. -/
def symmetricPole (ω : ℂ) (u h : ℝ) : ℂ :=
  Complex.exp (ω*u) * Complex.sinh (ω*h) / ((h : ℂ)*ω^2)

/-- The central difference of the integrated kernel in the nonnegative half-line has the
hyperbolic-sine weight. -/
theorem symmetricPole_eq_difference (ω : ℂ) {u h : ℝ} (hp : 0 ≤ u+h) (hm : 0 ≤ u-h) :
    symmetricPole ω u h = (integratedPole ω (u+h) - integratedPole ω (u-h)) / (2*(h : ℂ)) := by
  simp only [symmetricPole, integratedPole, max_eq_left hp, max_eq_left hm, Complex.sinh,
    Complex.ofReal_add, Complex.ofReal_sub, mul_add, mul_sub]
  simp only [sub_eq_add_neg, Complex.exp_add,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- For each fixed positive width smaller than the logarithmic cutoff, the symmetric
kernel retains absolute convergence for every inverse-square-summable family. -/
theorem summable_symmetricPole {a : ℕ → ℂ} {b u h : ℝ} (hb : ∀ n, (a n).re ≤ b)
    (hS : Summable fun n => (‖a n‖^2)⁻¹) (hp : 0 ≤ u+h) (hm : 0 ≤ u-h) :
    Summable fun n => symmetricPole (a n) u h := by
  simp_rw [symmetricPole_eq_difference _ hp hm, div_eq_mul_inv]
  exact ((summable_integratedPole hb hS _).sub (summable_integratedPole hb hS _)).mul_right _

/-- Taking a finite-width difference exchanges with the absolutely convergent pole series. -/
theorem tsum_symmetricPole_eq_difference {a : ℕ → ℂ} {b u h : ℝ} (hb : ∀ n, (a n).re ≤ b)
    (hS : Summable fun n => (‖a n‖^2)⁻¹) (hp : 0 ≤ u+h) (hm : 0 ≤ u-h) :
    (∑' n, symmetricPole (a n) u h) =
      ((∑' n, integratedPole (a n) (u+h)) - ∑' n, integratedPole (a n) (u-h)) / (2*(h : ℂ)) := by
  simp_rw [symmetricPole_eq_difference _ hp hm]
  rw [tsum_div_const, (summable_integratedPole hb hS _).tsum_sub (summable_integratedPole hb hS _)]

end AnalyticNumberTheory.AnalyticTools
