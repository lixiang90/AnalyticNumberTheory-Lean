import AnalyticNumberTheory.RiemannZeta.HurwitzVinogradov
import AnalyticNumberTheory.DirichletLFunctions.WeylBound

/-!
# Vinogradov–Korobov growth with uniform dependence on the period

The decomposition into shifted Hurwitz zeta-functions separates the
first period from the oscillatory tail. The constants below work for
all moduli and all periodic coefficient functions bounded by one.
-/

open Complex Real Finset
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.DirichletLFunctions

/-- The first-period remainder in the Vinogradov–Korobov estimate, with the
absolute factor `q^(1-Re s)` displayed. -/
theorem periodicLFunction_sub_first_period_vinogradov :
    ∃ K : ℝ,0<K ∧ ∃ D : ℝ,0<D ∧ ∀ {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ),
      (∀ j,‖Φ j‖≤1) → ∀ {s : ℂ},0<s.re → 2≤|s.im| →
      ‖ZMod.LFunction Φ s-dirichletPoly (fun n : ℕ => Φ n) q s‖ ≤
        (q:ℝ)^(1-s.re)*(D*(Real.log |s.im|)^(2/3:ℝ)*
          Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*Real.log |s.im|)) := by
  obtain ⟨K,hK,D,hD,H⟩ := hurwitzZeta_sub_initial_vinogradov_bound
  exact ⟨K,hK,D,hD,fun Φ hΦ s hσ ht =>
    periodicLFunction_sub_first_period_le Φ hΦ s (fun _ ha => H ha hσ ht)⟩

/-- Uniform Vinogradov–Korobov growth for arbitrary Dirichlet characters,
including imprimitive characters, with the elementary initial sum explicit. -/
theorem LFunction_vinogradov_bound :
    ∃ K : ℝ,0<K ∧ ∃ D : ℝ,0<D ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {s : ℂ},0<s.re → 2≤|s.im| → ‖χ.LFunction s‖≤
        (∑ n∈Icc 1 q,(n:ℝ)^(-s.re))+
        (q:ℝ)^(1-s.re)*(D*(Real.log |s.im|)^(2/3:ℝ)*
          Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*Real.log |s.im|)) := by
  obtain ⟨K,hK,D,hD,H⟩ := hurwitzZeta_sub_initial_vinogradov_bound
  exact ⟨K,hK,D,hD,fun χ s hσ ht => periodicLFunction_le_of_regular_hurwitz χ
    (norm_char_le_one χ) s (fun _ ha => H ha hσ ht)⟩

end AnalyticNumberTheory.DirichletLFunctions
