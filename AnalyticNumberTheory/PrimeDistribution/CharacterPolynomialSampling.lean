import AnalyticNumberTheory.PrimeDistribution.DirichletPolynomialSampling
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovBilinear

/-!
# Hybrid large sieve at points of varying real parts

Each primitive character has its own set of sampling points. A uniform bound
on the number of points in a unit height interval controls multiplicity.
-/

noncomputable section

open Finset MeasureTheory Complex
open scoped Classical Topology
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.PrimeDistribution

set_option maxHeartbeats 650000 in
/-- Hybrid large sieve at points in a strip. Each primitive character may be
sampled at its own set of points, with a common local ordinate count. -/
theorem dirichletPoly_character_sampling_strip {Q N L : ℕ} (hL₁ : 0 < L) (hN : 1 ≤ N)
    (S : (Σ q : ℕ, DirichletCharacter ℂ q) → Finset ℂ) {K σ : ℝ} (hK : 0 ≤ K)
    (hre : ∀ p ∈ primitiveCharacterFamily Q, ∀ z ∈ S p, z.re ∈ Set.Icc σ (σ+1))
    (hL : ∀ p ∈ primitiveCharacterFamily Q, ∀ z ∈ S p, 0 ≤ z.im ∧ z.im < L)
    (hmult : ∀ p ∈ primitiveCharacterFamily Q, ∀ j < L,
      (((S p).filter (fun z => ⌊z.im⌋₊=j)).card : ℝ) ≤ K) (a : ℕ → ℂ) :
    ∑ p ∈ primitiveCharacterFamily Q, ∑ z ∈ S p, ‖dirichletPoly (fun n => a n * p.2 n) N z‖^2 ≤
      9*K*(Real.pi^3*((N:ℝ)+(Q:ℝ)^2*L)*(1+Real.log N)^4*dirichletPolyEnergy a N σ) := by
  apply dirichletPoly_family_sampling_strip _ _ _ hK hre hL hmult
  intro u hu k hk
  let g (n : ℕ) := a n * (-Complex.log n)^k
  let b (n : ℕ) := g n * (n:ℂ)^(-(u:ℂ))
  let P (p : Σ q : ℕ, DirichletCharacter ℂ q) (t : ℝ) :=
    dirichletPoly (fun n => (a n * p.2 n) * (-Complex.log n)^k) N ((u:ℂ)+(t:ℂ)*I)
  have hpoly (p : Σ q : ℕ, DirichletCharacter ℂ q) (t : ℝ) :
      P p t =
        ∑ n ∈ Icc 1 N, b n * p.2 n * (n:ℂ)^(-(I*(t:ℂ))) := by
    unfold P dirichletPoly
    refine sum_congr rfl fun n hn => ?_
    have hn₀ : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
    dsimp only [b,g]
    rw [show -((u:ℂ)+(t:ℂ)*I) = -(u:ℂ) + -(I*(t:ℂ)) by ring, Complex.cpow_add _ _ hn₀]
    ring
  have hb (n : ℕ) (hn : n ∈ Icc 1 N) : ‖b n‖^2 = ‖g n‖^2*(n:ℝ)^(-2*u) := by
    rw [show ‖b n‖ = ‖g n‖*‖(n:ℂ)^(-(u:ℂ))‖ from norm_mul ..,
      Complex.norm_natCast_cpow_of_pos (mem_Icc.mp hn).1, neg_re, Complex.ofReal_re, mul_pow,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 2; push_cast; ring
  have hs := hybrid_large_sieve_unweighted b N Q (T:=(L:ℝ)) (by exact_mod_cast hL₁)
  have hmain : ∑ p ∈ primitiveCharacterFamily Q, (∫ t in -(L:ℝ)..L, ‖P p t‖^2) ≤
      Real.pi^3*((N:ℝ)+(Q:ℝ)^2*L)*dirichletPolyEnergy g N u := by
    simp only [hpoly,primitiveCharacterFamily,sum_sigma]
    rwa [dirichletPolyEnergy, ← sum_congr rfl hb]
  change (∑ p ∈ primitiveCharacterFamily Q, (∫ t in (0:ℝ)..L, ‖P p t‖^2)) ≤ _
  have hcont (p : Σ q : ℕ, DirichletCharacter ℂ q) : Continuous (P p) := by
    change Continuous (fun t => P p t)
    simp_rw [hpoly]
    apply continuous_finsetSum
    intro n hn
    have hn₀ : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
    simp_rw [Complex.cpow_def_of_ne_zero hn₀]
    fun_prop
  apply (sum_le_sum fun p _ => intervalIntegral.integral_mono_interval (by simp : -(L:ℝ) ≤ 0)
    (Nat.cast_nonneg L) le_rfl (Filter.Eventually.of_forall fun t => sq_nonneg _)
    (((hcont p).norm.pow 2).intervalIntegrable (μ:=volume) (-(L:ℝ)) L)).trans
  apply hmain.trans
  rw [mul_assoc (Real.pi^3*((N:ℝ)+(Q:ℝ)^2*L))]
  exact mul_le_mul_of_nonneg_left (dirichletPoly_logTwist_energy a hN hu.1 hk) (by positivity)

end AnalyticNumberTheory.PrimeDistribution
