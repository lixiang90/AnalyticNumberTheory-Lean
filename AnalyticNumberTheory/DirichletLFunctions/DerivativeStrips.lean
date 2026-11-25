import AnalyticNumberTheory.RiemannZeta.HurwitzDerivativeStrips
import AnalyticNumberTheory.DirichletLFunctions.VinogradovStrips

/-!
# Finite derivative strip estimates with uniform conductor dependence

The constants below apply to every derivative order at once. The initial
period is kept explicit, and the rest carries the factor `q^(1-Re s)`.
-/

open Complex Real Finset
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.DirichletLFunctions

/-- A single constant in the estimate for all finite derivative strips,
all periods, and all coefficient functions bounded by one. -/
theorem periodicLFunction_sub_first_period_derivative_strips :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ), (∀ j,‖Φ j‖≤1) →
      ∀ {k : ℕ} {s : ℂ},2≤k → 0<s.re → 1-k/((2:ℝ)^k-2)≤s.re → 2≤|s.im| →
      ‖ZMod.LFunction Φ s-dirichletPoly (fun n : ℕ => Φ n) q s‖≤
        (q:ℝ)^(1-s.re)*(C*|s.im|^(1/((2:ℝ)^k-2))*(1+Real.log |s.im|)) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_derivative_strips
  exact ⟨C,hC,fun Φ hΦ k s hk hσ hline ht =>
    periodicLFunction_sub_first_period_le Φ hΦ s (fun _ ha => H hk ha hσ hline ht)⟩

/-- The finite order strip bound for every Dirichlet character. The implied
constant is independent of the order, the modulus, and the height. -/
theorem LFunction_derivative_strips :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {k : ℕ} {s : ℂ},
      2≤k → 0<s.re → 1-k/((2:ℝ)^k-2)≤s.re → 2≤|s.im| → ‖χ.LFunction s‖≤
        (∑ n∈Icc 1 q,(n:ℝ)^(-s.re))+
        (q:ℝ)^(1-s.re)*(C*|s.im|^(1/((2:ℝ)^k-2))*(1+Real.log |s.im|)) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_derivative_strips
  exact ⟨C,hC,fun χ k s hk hσ hline ht => periodicLFunction_le_of_regular_hurwitz χ
    (norm_char_le_one χ) s (fun _ ha => H hk ha hσ hline ht)⟩

end AnalyticNumberTheory.DirichletLFunctions
