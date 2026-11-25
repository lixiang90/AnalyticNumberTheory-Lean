import AnalyticNumberTheory.DirichletLFunctions.VinogradovStrips
import AnalyticNumberTheory.DirichletSeries.Ramachandra
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Absolute estimates for truncated character polynomials

The right-half-plane remainder follows from integral comparison and is
uniform in the height and conductor. On the left of one the polynomial
has its usual power growth in its length.
-/

open Real Complex Finset MeasureTheory Filter
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.DirichletLFunctions

theorem differentiable_dirichletPoly (a : ℕ→ℂ) (N : ℕ) :
    Differentiable ℂ (dirichletPoly a N) := by
  apply Differentiable.fun_sum
  intro n hn
  have h : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hn).1)
  simp_rw [Complex.cpow_def_of_ne_zero h]; fun_prop

theorem norm_characterPolynomial_le_power_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (s : ℂ) :
    ‖dirichletPoly (fun n : ℕ => χ n) N s‖≤∑ n∈Icc 1 N,(n:ℝ)^(-s.re) := by
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro n hn
  rw [norm_mul,Complex.norm_natCast_cpow_of_pos (mem_Icc.mp hn).1,Complex.neg_re]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)

/-- Elementary finite polynomial estimate at positive real part below one. -/
theorem norm_characterPolynomial_le {q N : ℕ} (χ : DirichletCharacter ℂ q) (hN : 1≤N)
    {s : ℂ} (hσ : 0≤s.re) (hσ' : s.re<1) :
    ‖dirichletPoly (fun n : ℕ => χ n) N s‖≤(N:ℝ)^(1-s.re)*(1+1/(1-s.re)) :=
  (norm_characterPolynomial_le_power_sum χ N s).trans
    (first_period_power_sum_le hN (sub_pos.mpr hσ') hσ (by linarith))

/-- The absolute truncation error for a Dirichlet character at any point
of its half-plane of absolute convergence. -/
theorem norm_LFunction_sub_polynomial_absolute {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hN : 1≤N) {s : ℂ} (hσ : 1<s.re) :
    ‖χ.LFunction s-dirichletPoly (fun n : ℕ => χ n) N s‖≤(N:ℝ)^(1-s.re)/(s.re-1) := by
  let a (n : ℕ) := (χ n : ℂ)
  have hs : LSeriesSummable a s := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hσ,dirichletPoly_eq_dirichletPartialSum]
  have h := dirichletPartialSum_add_tail (b:=a) N hs.hasSum
  change dirichletPartialSum a s N+dirichletTail a s N=LSeries a s at h
  change ‖LSeries a s-dirichletPartialSum a s N‖≤_
  rw [←h,add_sub_cancel_left]
  let f (u : ℝ) := u^(-s.re)
  have hN₀ : 0<(N:ℝ) := by exact_mod_cast hN
  have hanti : AntitoneOn f (Set.Ici (N:ℝ)) := fun u hu v _ huv =>
    Real.rpow_le_rpow_of_nonpos (hN₀.trans_le hu) huv (by linarith)
  have hi : IntegrableOn f (Set.Ioi (N:ℝ)) := integrableOn_Ioi_rpow_of_lt (by linarith) hN₀
  have hpos (u : ℝ) (hu : u∈Set.Ioi (N:ℝ)) : 0≤f u := Real.rpow_nonneg (hN₀.trans hu).le _
  let b (n : ℕ) := f (n+N+1:ℕ)
  have hsum : Summable b := by
    have hAll : Summable (fun n : ℕ => f (n:ℝ)) := Real.summable_nat_rpow.mpr (by linarith)
    simpa only [b,Nat.add_assoc] using (summable_nat_add_iff (N+1)).mpr hAll
  have hd (n : ℕ) : ‖LSeries.term a s (n+(N+1))‖≤b n := by
    have hn : 0<n+(N+1) := by omega
    rw [LSeries.term_of_ne_zero hn.ne',norm_div,Complex.norm_natCast_cpow_of_pos hn]
    dsimp only [b,f]; rw [Nat.add_assoc,Real.rpow_neg (Nat.cast_nonneg _)]
    exact div_le_iff₀ (by positivity : 0<((n+(N+1):ℕ):ℝ)^s.re) |>.mpr (by
      rw [inv_mul_cancel₀ (by positivity)]; exact χ.norm_le_one _)
  apply (norm_tsum_le_tsum_norm ((summable_nat_add_iff (N+1)).mpr hs).norm).trans
  apply (Summable.tsum_le_tsum hd ((summable_nat_add_iff (N+1)).mpr hs).norm hsum).trans
  apply (hanti.tsum_comp_add_le_integral N hi hpos).trans_eq
  dsimp only [f]; rw [integral_Ioi_rpow_of_lt (by linarith) hN₀,show -s.re+1=1-s.re by ring,show s.re-1=-(1-s.re) by ring,div_neg,neg_div]

end AnalyticNumberTheory.DirichletLFunctions
