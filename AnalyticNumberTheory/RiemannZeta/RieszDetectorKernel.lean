import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The sixth Riesz kernel for a mollified zeta function

The kernel has seven linear denominator factors. We collect the basic
height estimates for the mollifier, zeta and this denominator.
-/
open Complex Real Finset Filter MeasureTheory
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

/-- The finite Möbius Dirichlet polynomial used in the Riesz detector. -/
noncomputable def rieszMobiusPolynomial (X : ℕ) (s : ℂ) :=
  dirichletPoly (fun d : ℕ => (ArithmeticFunction.moebius d:ℂ)) X s

/-- The pole-cancelled sixth-order Riesz kernel multiplied by the mollified
zeta function at the shifted argument. -/
noncomputable def rieszDetectorIntegrand (X : ℕ) (ρ : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  riemannZeta (ρ+w)*rieszMobiusPolynomial X (ρ+w)*(1+w/(ρ-1))*(Y:ℂ)^w/rieszDenom 6 w

/-- The finite Möbius polynomial is entire. -/
theorem differentiable_rieszMobiusPolynomial (X : ℕ) : Differentiable ℂ (rieszMobiusPolynomial X) := by
  unfold rieszMobiusPolynomial dirichletPoly
  apply Differentiable.fun_sum
  intro n hn
  have hn' : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by have := (mem_Icc.mp hn).1; omega)
  fun_prop (disch := simp [hn'])

/-- Absolute bound on the right half-plane, uniform in height. -/
theorem norm_rieszMobiusPolynomial_le (X : ℕ) {s : ℂ} (hs : 0≤s.re) :
    ‖rieszMobiusPolynomial X s‖ ≤ ∑ n ∈ Icc 1 X,‖(ArithmeticFunction.moebius n:ℂ)‖ := by
  unfold rieszMobiusPolynomial dirichletPoly
  apply (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  have hr : (1:ℝ)≤n := by exact_mod_cast hn1
  rw [norm_mul,Complex.norm_natCast_cpow_of_pos hn1,neg_re]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith))

/-- Linear growth suffices uniformly to the right of the critical line at large heights. -/
theorem riemannZeta_halfplane_linear_bound :
    ∃ C≥0, ∀ {s : ℂ}, 1/2≤s.re → 2≤|s.im| → ‖riemannZeta s‖ ≤ C*(|s.im|+2) := by
  obtain ⟨A,hA,HA⟩ := norm_riemannZeta_critical_strip_le_of_two_le (ε:=1/2) (by norm_num)
  obtain ⟨B,hB,HB⟩ := norm_riemannZeta_re_ge_one_le
  refine ⟨max A B,hA.le.trans (le_max_left ..),?_⟩
  intro s hs ht
  have he := Complex.re_add_im s
  by_cases h : s.re≤1
  · have H := HA ⟨by linarith,h⟩ ht
    rw [he] at H
    apply H.trans
    apply mul_le_mul (le_max_left ..) _ (by positivity) (hA.le.trans (le_max_left ..))
    calc |s.im|^((1-s.re)/2+1/2) ≤ |s.im|^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
         _ ≤ _ := by rw [Real.rpow_one]; linarith
  · have H := HB (not_le.mp h).le ht
    rw [he] at H
    exact H.trans (mul_le_mul (le_max_right ..) ((Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith))
      (Real.log_nonneg (by linarith)) (hB.le.trans (le_max_right ..)))

/-- Each of the seven denominator factors has norm at least the absolute height. -/
theorem rieszDenom_six_norm_ge (w : ℂ) :
    |w.im|^7 ≤ ‖rieszDenom 6 w‖ := by
  rw [rieszDenom,norm_prod]
  calc |w.im|^7 = ∏ _j ∈ range 7,|w.im| := by simp
       _ ≤ _ := prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => by
          simpa using Complex.abs_im_le_norm (w+(j:ℂ)))

end AnalyticNumberTheory.RiemannZeta
