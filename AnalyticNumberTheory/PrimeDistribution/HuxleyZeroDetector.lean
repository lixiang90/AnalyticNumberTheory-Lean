import AnalyticNumberTheory.PrimeDistribution.InghamZeroDetector

/-!
# A mollifier independent of the height parameter

The two alternatives for the Riesz zero detector remain valid uniformly
as the length of the Möbius polynomial varies up to the height.
-/
noncomputable section
open Complex Real Filter Finset MeasureTheory
open scoped Topology ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- The Riesz detector on a height band with freely chosen mollifier length.
The cutoff Y can lie below the height T. -/
theorem huxley_zero_detector :
    ∃ C > (0:ℝ), ∀ᶠ T : ℕ in atTop, ∀ (X : ℕ) (Y : ℝ) (ρ : ℂ),
      1≤X → X≤T → (X:ℝ)≤Y → 16≤Y → Y≤(T:ℝ)^(3/2:ℝ) → 1/Real.log T≤ρ.re-1/2 → ρ.re<1 →
      (T:ℝ)≤ρ.im → ρ.im≤2*T → riemannZeta ρ=0 →
      1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)‖ ∨
      1/8≤C*(1+Real.log T)*Y^(1/2-ρ.re)*(∫ v in -(4*(T:ℝ))..4*(T:ℝ),
        (1/(1+|v|)^4)*(‖riemannZeta ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖*
        ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖)) := by
  obtain ⟨C,hC,htrunc⟩ := rieszDetector_critical_truncation_of_length_le
  refine ⟨C,hC,?_⟩
  filter_upwards [ingham_right_dichotomy_uniform,htrunc,eventually_ge_atTop 2] with T he ht hT X Y ρ hX hXT hXY hy hY hδ hβ hγ hγ' hz
  have hx : (2:ℝ)≤T := by exact_mod_cast hT
  have hlog : 0<Real.log T := Real.log_pos (by linarith)
  have hβ' : 1/2<ρ.re := by linarith [one_div_pos.mpr hlog]
  rcases he X Y ρ hX hXY hy hY hβ'.le hβ.le hγ with h | h
  · exact Or.inl h
  right
  rw [inghamDetectorRight_eq_critical X (by linarith) hβ' hβ (by linarith) hz] at h
  have hb := ht hXT (by linarith : 1≤Y) hδ hβ hγ hγ'
  change ‖(720/(2*π):ℂ)*_‖≤_ at hb
  have heq (v : ℝ) : (1/(1+|v|)^4)*‖riemannZeta ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖*
      ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖ =
      (1/(1+|v|)^4)*(‖riemannZeta ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖*
      ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((ρ.im+v:ℝ):ℂ)*I)‖) := mul_assoc ..
  simp only [←Complex.ofReal_add,heq] at hb
  linarith only [h,hb]

end AnalyticNumberTheory.PrimeDistribution
