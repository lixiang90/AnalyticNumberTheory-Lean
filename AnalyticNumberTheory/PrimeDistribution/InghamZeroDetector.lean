import AnalyticNumberTheory.PrimeDistribution.InghamDetectorPolynomial
import AnalyticNumberTheory.RiemannZeta.RieszDetectorShift
import AnalyticNumberTheory.RiemannZeta.RieszDetectorBound

/-!
# A Mellin zero detector on the critical line

A zero in the open right half of the critical strip gives either a
large finite polynomial or a large integral on the critical line.
-/
noncomputable section
open Complex Real Filter Finset MeasureTheory
open scoped Topology ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- At a zero of zeta the finite detector equals the shifted critical-line integral. -/
theorem inghamDetectorRight_eq_critical (X : ℕ) {ρ : ℂ} {Y : ℝ} (hY : 1≤Y)
    (hβ : 1/2<ρ.re) (hβ' : ρ.re<1) (hγ : 1≤ρ.im) (hz : riemannZeta ρ=0) :
    inghamDetectorRight X Y ρ =
      (720/(2*π):ℂ)*(∫ v : ℝ,rieszDetectorIntegrand X ρ Y (((1/2-ρ.re:ℝ):ℂ)+v*I)) := by
  rw [←rieszDetector_shift X hY hβ hβ' hγ hz,inghamDetectorRight]
  apply congrArg (fun z : ℂ => (720/(2*π):ℂ)*z)
  apply integral_congr_ae
  filter_upwards with v
  dsimp only [inghamRieszLine,rieszDetectorIntegrand,rieszMobiusPolynomial]
  ring

/-- The shifted dichotomy holds throughout the open strip, including zeros
arbitrarily close to the critical line. -/
theorem ingham_mellin_dichotomy : ∀ᶠ X : ℕ in atTop,
    ∀ (Y : ℝ) (ρ : ℂ), (X:ℝ)≤Y → Y≤(X:ℝ)^(3/2:ℝ) →
      1/2<ρ.re → ρ.re<1 → (X:ℝ)≤ρ.im → riemannZeta ρ=0 →
      1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)‖ ∨
      1/4≤‖(720/(2*π):ℂ)*(∫ v : ℝ,rieszDetectorIntegrand X ρ Y (((1/2-ρ.re:ℝ):ℂ)+v*I))‖ := by
  filter_upwards [ingham_right_dichotomy,eventually_ge_atTop 1] with X he hX Y ρ hXY hY hβ hβ' hγ hz
  have hx : (1:ℝ)≤X := by exact_mod_cast hX
  rw [←inghamDetectorRight_eq_critical X (hx.trans hXY) hβ hβ' (hx.trans hγ) hz]
  exact he Y ρ hXY hY hβ.le hβ'.le hγ

/-- Ingham's two alternatives with the critical-line integral truncated at
four times the height parameter.  The same finite coefficients and the same
positive constant work for all zeros and cutoffs in the band. -/
theorem ingham_zero_detector :
    ∃ C > (0:ℝ), ∀ᶠ X : ℕ in atTop, ∀ (Y : ℝ) (ρ : ℂ),
      (X:ℝ)≤Y → Y≤(X:ℝ)^(3/2:ℝ) → 1/Real.log X≤ρ.re-1/2 → ρ.re<1 →
      (X:ℝ)≤ρ.im → ρ.im≤2*X → riemannZeta ρ=0 →
      1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)‖ ∨
      1/8≤C*(1+Real.log X)*Y^(1/2-ρ.re)*(∫ v in -(4*(X:ℝ))..4*(X:ℝ),
        (1/(1+|v|)^4)*(‖riemannZeta ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖*
        ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖)) := by
  obtain ⟨C,hC,htrunc⟩ := rieszDetector_critical_truncation
  refine ⟨C,hC,?_⟩
  filter_upwards [ingham_mellin_dichotomy,htrunc,eventually_ge_atTop 2] with X he ht hX Y ρ hXY hY hδ hβ hγ hγ' hz
  have hx : (2:ℝ)≤X := by exact_mod_cast hX
  have hlog : 0<Real.log X := Real.log_pos (by linarith)
  have hβ' : 1/2<ρ.re := by linarith [one_div_pos.mpr hlog]
  rcases he Y ρ hXY hY hβ' hβ hγ hz with h | h
  · exact Or.inl h
  right
  have hb := ht (by linarith : 1≤Y) hδ hβ hγ hγ'
  change ‖(720/(2*π):ℂ)*_‖≤_ at hb
  have heq (v : ℝ) : (1/(1+|v|)^4)*‖riemannZeta ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖*
      ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖ =
      (1/(1+|v|)^4)*(‖riemannZeta ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖*
      ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖) := mul_assoc ..
  simp only [←Complex.ofReal_add,heq] at hb
  linarith only [h,hb]

end AnalyticNumberTheory.PrimeDistribution
