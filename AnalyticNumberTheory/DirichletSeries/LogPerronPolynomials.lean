import AnalyticNumberTheory.DirichletSeries.LogPerronContours

/-! # Finite polynomial multipliers in logarithmic Perron inversion

Multiplication by n⁻ˢ rescales the physical cutoff to x/n. The finite
formulas retain the zero weight at the upper integer endpoint.
-/

noncomputable section
open Complex Real Finset MeasureTheory

namespace AnalyticNumberTheory.DirichletSeries

private lemma nat_cpow_mul_logPerronKernel {x : ℝ} (hx : 0<x) {n : ℕ} (hn : 0<n)
    (σ t : ℝ) :
    (n : ℂ)^(-((σ : ℂ)+t*I)) * logPerronKernel σ (Real.log x) t =
      logPerronKernel σ (Real.log (x/n)) t := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [logPerronKernel, logPerronKernel, ← mul_div_assoc, Complex.cpow_def_of_ne_zero hnC,
    ← Complex.exp_add, Real.log_div hx.ne' hnR.ne', Complex.ofReal_sub, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hnR.le]
  congr 2
  ring

/-- A finite Dirichlet multiplier acts on the Perron trace by a finite
linear combination of dilations of the cutoff. -/
theorem logPerronTrace_finset_mul (a : ℕ → ℂ) {S : Finset ℕ} (hS : ∀ n ∈ S, 0<n)
    (F : ℂ → ℂ) {x : ℝ} (hx : 0<x) (σ t : ℝ) :
    logPerronTrace (fun s => (∑ n ∈ S, a n*(n : ℂ)^(-s))*F s) σ x t =
      ∑ n ∈ S, a n*logPerronTrace F σ (x/n) t := by
  simp only [logPerronTrace, sum_mul]
  apply sum_congr rfl
  intro n hn
  have H := nat_cpow_mul_logPerronKernel hx (hS n hn) σ t
  calc
    _ = a n * (F ((σ : ℂ)+t*I) * ((n : ℂ)^(-((σ : ℂ)+t*I)) * logPerronKernel σ (Real.log x) t)) := by ring
    _ = _ := by rw [H]

/-- Products with finite Dirichlet polynomials preserve integrability at
the scaled cutoffs and admit an exact integrated dilation formula. -/
theorem logPerronIntegral_finset_mul (a : ℕ → ℂ) {S : Finset ℕ} (hS : ∀ n ∈ S, 0<n)
    (F : ℂ → ℂ) {x : ℝ} (hx : 0<x) (σ : ℝ) (hi : ∀ n ∈ S, Integrable (logPerronTrace F σ (x/n))) :
    let G := fun s : ℂ => (∑ n ∈ S, a n*(n : ℂ)^(-s))*F s
    Integrable (logPerronTrace G σ x) ∧
      logPerronIntegral G σ x = ∑ n ∈ S, a n*logPerronIntegral F σ (x/n) := by
  intro G
  have he : logPerronTrace G σ x = fun t => ∑ n ∈ S, a n*logPerronTrace F σ (x/n) t :=
    funext (logPerronTrace_finset_mul a hS F hx σ)
  have hi' (n : ℕ) (hn : n ∈ S) : Integrable (fun t => a n*logPerronTrace F σ (x/n) t) :=
    (hi n hn).const_mul _
  constructor
  · rw [he]
    exact integrable_finsetSum _ hi'
  · simp only [logPerronIntegral, he, integral_finsetSum _ hi', integral_const_mul, sum_div, mul_div_assoc]

/-- A finite polynomial in the Perron integral returns the positive part
of the logarithmic weight at each index, for any positive integration line. -/
theorem logPerronIntegral_finset (a : ℕ → ℂ) {S : Finset ℕ} (hS : ∀ n ∈ S, 0<n)
    {x σ : ℝ} (hx : 0<x) (hσ : 0<σ) :
    let P := fun s : ℂ => ∑ n ∈ S, a n*(n : ℂ)^(-s)
    Integrable (logPerronTrace P σ x) ∧
      logPerronIntegral P σ x = ∑ n ∈ S, a n*((max (Real.log (x/n)) 0 : ℝ) : ℂ) := by
  have hone (y : ℝ) : logPerronTrace (fun _ => 1) σ y = logPerronKernel σ (Real.log y) :=
    funext fun t => one_mul _
  have hi := logPerronIntegral_finset_mul a hS (fun _ => 1) hx σ
    (fun n _ => hone (x/n) ▸ integrable_logPerronKernel hσ (Real.log (x/n)))
  have hval (y : ℝ) : logPerronIntegral (fun _ => 1) σ y = ((max (Real.log y) 0 : ℝ) : ℂ) := by
    rw [logPerronIntegral, hone, integral_logPerronKernel hσ]
  simpa only [mul_one, hval] using hi

/-- The positive logarithmic weight cuts an interval off at the integer
floor of x, with zero contribution when x itself is an integer endpoint. -/
theorem sum_Ioc_log_posPart (a : ℕ → ℂ) (M N : ℕ) {x : ℝ} (hx : 0<x) :
    (∑ n ∈ Ioc M N, a n*((max (Real.log (x/n)) 0 : ℝ) : ℂ)) =
      ∑ n ∈ Ioc M (min N ⌊x⌋₊), a n*(Real.log (x/n) : ℂ) := by
  have he : Ioc M (min N ⌊x⌋₊) = (Ioc M N).filter (· ≤ ⌊x⌋₊) := by ext n; simp; omega
  rw [he, sum_filter]
  apply sum_congr rfl
  intro n hn
  have hpos : (0 : ℝ)<n := by exact_mod_cast (Nat.zero_le M).trans_lt (mem_Ioc.mp hn).1
  by_cases h : n≤⌊x⌋₊
  · rw [ite_eq_left h, max_eq_left (Real.log_nonneg ((one_le_div hpos).mpr ((Nat.le_floor_iff hx.le).mp h)))]
  · have hn' : x<(n : ℝ) := by simpa only [Nat.le_floor_iff hx.le, not_le] using h
    rw [ite_eq_right h, max_eq_right (Real.log_nonpos (div_nonneg hx.le hpos.le) ((div_le_one hpos).mpr hn'.le))]
    simp

end AnalyticNumberTheory.DirichletSeries
