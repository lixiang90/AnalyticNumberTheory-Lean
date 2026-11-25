import AnalyticNumberTheory.DirichletSeries.LogPerronPolynomials
import AnalyticNumberTheory.DirichletSeries.VerticalOrder
import AnalyticNumberTheory.DirichletLFunctions.Characters
import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola

/-! # Perron integrals of interval polynomials twisted by a character -/

noncomputable section
open Complex Real Finset MeasureTheory
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

/-- A Dirichlet polynomial supported on the half-open interval M < n ≤ N
and twisted by one fixed Dirichlet character. -/
def intervalCharacterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (M N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc M N, a n*χ n*(n : ℂ)^(-s)

theorem intervalCharacterPolynomial_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) :
    intervalCharacterPolynomial χ a 0 N = dirichletPoly (fun n => a n*χ n) N := by
  funext s
  rw [intervalCharacterPolynomial, ← Icc_add_one_left_eq_Ioc, zero_add]
  rfl

/-- Integral of a twisted interval polynomial with its upper endpoint
clipped exactly to the Perron cutoff. -/
theorem logPerron_intervalCharacterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (M N : ℕ) {σ x : ℝ} (hσ : 0<σ) (hx : 0<x) :
    let P := intervalCharacterPolynomial χ a M N
    Integrable (logPerronTrace P σ x) ∧ logPerronIntegral P σ x =
      ∑ n ∈ Ioc M (min N ⌊x⌋₊), (a n*χ n)*(Real.log (x/n) : ℂ) := by
  have h := logPerronIntegral_finset (fun n => a n*χ n) (S := Ioc M N)
    (fun n hn => (Nat.zero_le M).trans_lt (mem_Ioc.mp hn).1) hx hσ
  exact ⟨h.1, h.2.trans (sum_Ioc_log_posPart _ M N hx)⟩

private theorem twist_dilated_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℂ) (b : ℕ → ℂ)
    (d : ℕ) (T : Finset ℕ) (x : ℝ) :
    (a*χ d)*(∑ k ∈ T, (b k*χ k)*(Real.log ((x/d)/k) : ℂ)) =
      a*∑ k ∈ T, b k*(χ (d*k)*(Real.log (x/(d*k : ℕ)) : ℂ)) := by
  simp only [mul_sum, div_div, Nat.cast_mul, map_mul]
  exact sum_congr rfl fun _ _ => by ring

/-- Inversion of a polynomial times a character-twisted coefficient series.
It produces an exact hyperbola sum with inner cutoff floor(x)/d. -/
theorem logPerron_intervalCharacter_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (a b : ℕ → ℂ)
    (M N : ℕ) (F : ℂ → ℂ) {σ x : ℝ} (hx : 0<x)
    (hi : ∀ y : ℝ, 0<y → Integrable (logPerronTrace F σ y))
    (hinv : ∀ y : ℝ, 0<y → logPerronIntegral F σ y = logWeightedSum (fun n => b n*χ n) y) :
    let P := fun s => intervalCharacterPolynomial χ a M N s*F s
    Integrable (logPerronTrace P σ x) ∧ logPerronIntegral P σ x =
      ∑ d ∈ Ioc M N, a d*∑ k ∈ Icc 1 (⌊x⌋₊/d), b k*(χ (d*k)*(Real.log (x/(d*k : ℕ)) : ℂ)) := by
  intro P
  have hd (d : ℕ) (hd : d ∈ Ioc M N) : 0<d := (Nat.zero_le M).trans_lt (mem_Ioc.mp hd).1
  have hy (d : ℕ) (mem : d ∈ Ioc M N) : 0<x/d := div_pos hx (Nat.cast_pos.mpr (hd d mem))
  have H := logPerronIntegral_finset_mul (fun n => a n*χ n) hd F hx σ (fun d hm => hi _ (hy d hm))
  refine ⟨H.1,H.2.trans (sum_congr rfl fun d hm => ?_)⟩
  rw [hinv _ (hy d hm), logWeightedSum, DivisorProblems.nat_floor_div_nat hx.le (hd d hm)]
  exact twist_dilated_sum χ _ b d _ x

/-- A product of two finite interval polynomials has the same hyperbola
formula on every positive line, with both sets of interval cutoffs retained. -/
theorem logPerron_intervalCharacter_product {q : ℕ} (χ : DirichletCharacter ℂ q) (a b : ℕ → ℂ)
    (M N V W : ℕ) {σ x : ℝ} (hσ : 0<σ) (hx : 0<x) :
    let P := fun s => intervalCharacterPolynomial χ a M N s * intervalCharacterPolynomial χ b V W s
    Integrable (logPerronTrace P σ x) ∧ logPerronIntegral P σ x =
      ∑ d ∈ Ioc M N, a d*∑ k ∈ Ioc V (min W (⌊x⌋₊/d)), b k*(χ (d*k)*(Real.log (x/(d*k : ℕ)) : ℂ)) := by
  intro P
  have hd (d : ℕ) (hd : d ∈ Ioc M N) : 0<d := (Nat.zero_le M).trans_lt (mem_Ioc.mp hd).1
  have H (d : ℕ) (hm : d ∈ Ioc M N) := logPerron_intervalCharacterPolynomial χ b V W hσ
    (div_pos hx (Nat.cast_pos.mpr (hd d hm)))
  have h := logPerronIntegral_finset_mul (fun n => a n*χ n) hd (intervalCharacterPolynomial χ b V W)
    hx σ (fun d hm => (H d hm).1)
  refine ⟨h.1,h.2.trans (sum_congr rfl fun d hm => ?_)⟩
  rw [(H d hm).2, DivisorProblems.nat_floor_div_nat hx.le (hd d hm)]
  exact twist_dilated_sum χ _ b d _ x

end AnalyticNumberTheory.DirichletLFunctions
