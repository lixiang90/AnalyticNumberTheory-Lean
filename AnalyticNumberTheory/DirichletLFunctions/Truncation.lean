import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation
import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-!
# Truncation in the open right half-plane

For nonprincipal characters the Dirichlet partial sum converges conditionally
at one. The Abel integral gives a remainder uniform in the truncation length.
-/

open Finset Complex MeasureTheory Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

/-- A finite partial sum for a nonprincipal character approximates its L-function
throughout `Re s > 0`, with explicit dependence on the modulus and the height. -/
theorem norm_sub_dirichletPoly_le {q N : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s - dirichletPoly (fun n => χ n) N s‖ ≤
      q * (N:ℝ)^(-s.re) * (1 + ‖s‖ / s.re) := by
  let S (n : ℕ) := ∑ k ∈ Icc 1 n, χ k
  let F (t : ℝ) := S ⌊t⌋₊ * (t:ℂ)^(-s-1)
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := by linarith
  have hS (n : ℕ) : ‖S n‖ ≤ q := norm_sum_Icc_char_le_modulus hχ n
  have hf (t : ℝ) (ht : 0 < t) : ‖F t‖ ≤ q * t^(-s.re-1) := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simpa using mul_le_mul_of_nonneg_right (hS ⌊t⌋₊) (Real.rpow_nonneg ht.le (-s.re-1))
  have hmeas : Measurable F := ((measurable_from_top (f:=S)).comp Nat.measurable_floor).mul
    (Complex.continuous_ofReal.measurable.pow_const _)
  have hint : IntegrableOn F (Set.Ioi (1:ℝ)) := by
    apply ((integrableOn_Ioi_rpow_of_lt (a := -s.re-1) (by linarith) zero_lt_one).const_mul (q:ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hf t (lt_trans zero_lt_one ht)
  have hab := abel_summation_Icc_one_hasDerivAt (fun k : ℕ => χ k)
    (f := fun t : ℝ => (t:ℂ)^(-s)) (f' := fun t : ℝ => -s * (t:ℂ)^(-s-1)) hN₁
    (fun t ht => by
      have hp : (t:ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr
        (Or.inl (by simp; linarith [ht.1]))
      simpa [mul_comm] using (HasDerivAt.cpow_const (c := -s) (hasDerivAt_id (t:ℂ)) hp).comp_ofReal)
    (ContinuousOn.mul continuousOn_const
      (Complex.continuous_ofReal.continuousOn.cpow_const fun t ht =>
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [ht.1]))))
  simp only [Nat.floor_natCast,Complex.ofReal_natCast] at hab
  have hfinite : dirichletPoly (fun n => χ n) N s =
      S N * (N:ℂ)^(-s) + s * ∫ t in (1:ℝ)..N, F t := by
    rw [dirichletPoly, hab, sub_eq_add_neg, ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [F,S]
    ring
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Set.Ioi_subset_Ioi hN₁))
  have habs : ‖∫ t in Set.Ioi (N:ℝ), F t‖ ≤ q * (N:ℝ)^(-s.re) / s.re := by
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫ t in Set.Ioi (N:ℝ), (q:ℝ) * t^(-s.re-1) := by
        apply setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi hN₁)).norm
          ((integrableOn_Ioi_rpow_of_lt (by linarith) hN₀).const_mul (q:ℝ)) measurableSet_Ioi
        intro t ht
        exact hf t (hN₀.trans ht)
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN₀]
        ring_nf
  have hboundary : ‖S N * (N:ℂ)^(-s)‖ ≤ q*(N:ℝ)^(-s.re) := by
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos hN,neg_re]
    exact mul_le_mul_of_nonneg_right (hS N) (by positivity)
  have hfull : DirichletCharacter.LFunction χ s = s * ∫ t in Set.Ioi (1:ℝ), F t :=
    LFunction_eq_mul_integral_of_zero_lt_re hχ hs
  rw [hfull, ← hsplit, hfinite,
    show ∀ a b c : ℂ, s*(a+b)-(c+s*a) = s*b-c by intros; ring]
  apply (norm_sub_le ..).trans
  rw [norm_mul]
  calc
    _ ≤ ‖s‖ * (q * (N:ℝ)^(-s.re) / s.re) + q*(N:ℝ)^(-s.re) :=
      add_le_add (mul_le_mul_of_nonneg_left habs (norm_nonneg _)) hboundary
    _ = _ := by ring


/-- The ordinary Dirichlet partial sums of a nonprincipal character at one. -/
theorem tendsto_char_div_nat {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ∑ d ∈ Ioc 0 N, χ d / (d : ℂ)) atTop (𝓝 (χ.LFunction 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (2*(q:ℝ))
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (g:=fun N : ℕ => 2*(q:ℝ)*(N:ℝ)⁻¹) _ (by simpa using h)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have H := norm_sub_dirichletPoly_le hχ hN (s:=1) (by norm_num)
  rw [norm_sub_rev]
  rw [← Icc_add_one_left_eq_Ioc, zero_add]
  norm_num [dirichletPoly, Complex.cpow_neg_one, Real.rpow_neg_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] at H ⊢
  exact H

end AnalyticNumberTheory.DirichletLFunctions
