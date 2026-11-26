import AnalyticNumberTheory.PrimeDistribution.PerronRectangleDecay
import AnalyticNumberTheory.PrimeDistribution.TrivialZeroTerm
import AnalyticNumberTheory.DirichletSeries.SharpPerron

/-!
# The sharp, symmetrically height-ordered explicit formula for Chebyshev's function

The ordinates are cut off at an arbitrary real height. Passing first through rectangles
whose horizontal sides miss the zeros gives the full residue sum. The unit-band zero
count then removes the choice of heights without any relation between the height and the
physical cutoff. At a prime power the answer carries exactly half the endpoint mass.
-/

noncomputable section

open Complex Filter Finset MeasureTheory
open scoped Topology Classical ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis AnalyticNumberTheory.RiemannZeta
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.PrimeDistribution

/-- The sharp height truncation of the critical-strip zero contribution, with analytic multiplicity. -/
def sharpZetaZeroSum (x T : ℝ) : ℂ :=
  ∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*((x : ℂ)^z/z)

/-- The change of the sharp zero sum when the height increases by at most one is
`O(x log T/T)` for every `x≥1`, including heights much larger than the cutoff. -/
theorem sharpZetaZeroSum_unit_variation :
    ∃ C > 0, ∀ {x T U : ℝ}, 1 ≤ x → 2 ≤ T → T ≤ U → U ≤ T+1 →
      ‖sharpZetaZeroSum x U - sharpZetaZeroSum x T‖ ≤ (C*x)*(Real.log T/T) := by
  obtain ⟨C, hC, H⟩ := sum_zeroMultiplicity_unit_band_le
  refine ⟨C,hC,fun {x T U} hx hT hTU hU => ?_⟩
  have hT₀ : 0<T := by linarith
  have hsub {a b : ℝ} (hab : a≤b) : nontrivialZerosUpTo a ⊆ nontrivialZerosUpTo b := by
    intro z hz
    obtain ⟨h,h₀,h₁,ht⟩ := mem_nontrivialZerosUpTo.mp hz
    exact mem_nontrivialZerosUpTo.mpr ⟨h,h₀,h₁,ht.trans hab⟩
  let D := nontrivialZerosUpTo U \ nontrivialZerosUpTo T
  have hm {z : ℂ} (hz : z ∈ D) : T < |z.im| := by
    obtain ⟨h, hnot⟩ := mem_sdiff.mp hz
    obtain ⟨h₀,h₁,h₂,_⟩ := mem_nontrivialZerosUpTo.mp h
    exact lt_of_not_ge fun he => hnot (mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,he⟩)
  have hd : D ⊆ (nontrivialZerosUpTo (T+1)).filter (fun z => T ≤ |z.im|) :=
    fun z hz => mem_filter.mpr ⟨hsub hU (mem_sdiff.mp hz).1, (hm hz).le⟩
  rw [sharpZetaZeroSum, sharpZetaZeroSum, ← sum_sdiff_eq_sub (hsub hTU)]
  calc
    _ ≤ ∑ z ∈ D, (zeroMultiplicity z : ℝ)*(x/T) := by
      apply (norm_sum_le ..).trans
      refine sum_le_sum fun z hz => ?_
      rw [norm_mul, Complex.norm_natCast, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply div_le_div₀ (zero_le_one.trans hx) _ hT₀ ((hm hz).le.trans (Complex.abs_im_le_norm z))
      simpa using Real.rpow_le_rpow_of_exponent_le hx (mem_nontrivialZerosUpTo.mp (mem_sdiff.mp hz).1).2.2.1.le
    _ = (∑ z ∈ D, (zeroMultiplicity z : ℝ))*(x/T) := (sum_mul ..).symm
    _ ≤ (C*Real.log T)*(x/T) := mul_le_mul_of_nonneg_right
      ((sum_le_sum_of_subset_of_nonneg hd (fun z _ _ => Nat.cast_nonneg _)).trans (H T hT)) (by positivity)
    _ = _ := by ring

private theorem right_integral (x T : ℝ) :
    (∫ t : ℝ in (-T)..T, zetaPerronIntegrand x ((2 : ℂ)+t*I)) =
      (2*Real.pi : ℂ)*dirichletContourIntegral (fun n => (Λ n : ℂ)) x 2 T := by
  rw [dirichletContourIntegral, ←mul_assoc, mul_one_div_cancel (by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)), one_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.ofReal_ofNat]
  rw [zetaPerronIntegrand, LSeries_vonMangoldt_eq (by simp : 1 < ((2 : ℂ)+t*I).re), logDeriv_apply, neg_div]

/-- The full rectangle solved for the nontrivial-zero sum, with the ordinary
Perron integral on the right line and the remaining three oriented edge integrals. -/
theorem sharpZetaZeroSum_eq_contour {x T : ℝ} (hx : 0 < x) (hT : 0 < T) (R : ℝ)
    (hoff : ∀ z ∈ nontrivialZerosUpTo T, |z.im| ≠ T) :
    sharpZetaZeroSum x T = (x : ℂ) - Complex.log (2*(Real.pi : ℂ)) -
      (∑ n ∈ range ⌈R⌉₊, (x : ℂ)^(trivialZetaZero n)/trivialZetaZero n) -
      dirichletContourIntegral (fun n => (Λ n : ℂ)) x 2 T +
      (zetaPerronHorizontal x R T - zetaPerronHorizontal x R (-T) +
        I*zetaPerronLeft x R T)/(2*Real.pi*I) := by
  have h := rectangleBoundary_zetaPerron hx hT ⌈R⌉₊ hoff
  change zetaPerronHorizontal x R (-T) - zetaPerronHorizontal x R T +
    I*(∫ t : ℝ in (-T)..T, zetaPerronIntegrand x ((2 : ℂ)+t*I)) - I*zetaPerronLeft x R T =
      (2*Real.pi*I)*((x : ℂ)-Complex.log (2*(Real.pi : ℂ))-sharpZetaZeroSum x T-_) at h
  rw [right_integral] at h
  have hπ := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ, Complex.I_ne_zero]
  linear_combination h

/-- The finite sums over negative even zeros converge to the elementary trivial-zero term
with the same complex-power convention as the sharp contour. -/
theorem hasSum_cpow_trivialZetaZero_div {x : ℝ} (hx : 1 < x) :
    HasSum (fun n => (x : ℂ)^(trivialZetaZero n)/trivialZetaZero n)
      ((Real.log (1-(x^2)⁻¹) : ℂ)/2) := by
  have hx₀ := zero_lt_one.trans hx
  have H := hasSum_exp_trivialZetaZero_div (Real.log_pos hx)
  rw [show -2*Real.log x= -(Real.log x+Real.log x) by ring, Real.exp_neg, Real.exp_add, Real.exp_log hx₀, ←sq] at H
  apply H.congr_fun
  intro n
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx₀.ne'), ← Complex.ofReal_log hx₀.le, mul_comm]

/-- Von Mangoldt's full explicit formula, with symmetric truncation at every real height.
At jump points the limiting Chebyshev function has the arithmetic mean of the two adjacent values. -/
theorem tendsto_sharpZetaZeroSum_midpointPsi {x : ℝ} (hx : 1<x) :
    Tendsto (sharpZetaZeroSum x) atTop
      (𝓝 ((x : ℂ)-Complex.log (2*(Real.pi : ℂ))-(Real.log (1-(x^2)⁻¹) : ℂ)/2-(midpointPsi x : ℂ))) := by
  obtain ⟨U, hU, hedge⟩ := exists_tendsto_zetaPerron_edges
  obtain ⟨htop,hbot,hleft⟩ := hedge hx
  have hUt : Tendsto U atTop atTop :=
    tendsto_atTop_mono' atTop (hU.mono fun R h => h.1.le) (tendsto_pow_atTop (by decide : 2 ≠ 0))
  let a (n : ℕ) : ℂ := Λ n
  let D := dirichletContourIntegral a x 2
  let J (R : ℝ) := ∑ n ∈ range ⌈R⌉₊, (x : ℂ)^(trivialZetaZero n)/trivialZetaZero n
  let l := (Real.log (1-(x^2)⁻¹) : ℂ)/2
  have hj : Tendsto J atTop (𝓝 l) := (hasSum_cpow_trivialZetaZero_div hx).tendsto_sum_nat.comp tendsto_nat_ceil_atTop
  have hsum : LSeriesSummable a (2 : ℂ) := LSeriesSummable_vonMangoldt_iff.mpr (by norm_num)
  have hd : Tendsto (fun R => D (U R)) atTop (𝓝 (midpointPsi x : ℂ)) := by
    rw [← midpointPartialSum_vonMangoldt]
    exact (tendsto_dirichletContourIntegral_midpointPartialSum (zero_lt_one.trans hx) (by norm_num : (0 : ℝ)<2) hsum).comp hUt
  have hg : Tendsto (fun R => sharpZetaZeroSum x (U R)) atTop
      (𝓝 ((x : ℂ)-Complex.log (2*(Real.pi : ℂ))-l-(midpointPsi x : ℂ))) := by
    have hm := ((tendsto_const_nhds (x := (x : ℂ)-Complex.log (2*(Real.pi : ℂ)))).sub hj).sub hd
    have he := ((htop.sub hbot).add (hleft.const_mul I)).div_const (2*(Real.pi : ℂ)*I)
    apply (by simpa only [sub_zero,add_zero,mul_zero,zero_div] using hm.add he :
      Tendsto _ atTop (𝓝 ((x : ℂ)-Complex.log (2*(Real.pi : ℂ))-l-(midpointPsi x : ℂ)))).congr'
    filter_upwards [hU] with R hh
    exact (sharpZetaZeroSum_eq_contour (zero_lt_one.trans hx) ((sq_nonneg R).trans_lt hh.1) R hh.2.2).symm
  obtain ⟨C,_,hstep⟩ := sharpZetaZeroSum_unit_variation
  have hgap : Tendsto (fun T : ℝ => sharpZetaZeroSum x (U (Real.sqrt T))-sharpZetaZeroSum x T) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hrate : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using hrate.const_mul (C*x))
    filter_upwards [Real.tendsto_sqrt_atTop.eventually hU, eventually_ge_atTop 2] with T hh hT
    rw [Real.sq_sqrt (by linarith)] at hh
    exact hstep hx.le hT hh.1.le hh.2.1.le
  simpa only [Function.comp_apply, Pi.sub_apply, sub_sub_cancel, sub_zero] using
    (hg.comp Real.tendsto_sqrt_atTop).sub hgap

/-- At a cutoff which is not a prime power the half-weight sum equals the inclusive Chebyshev sum. -/
theorem midpointPsi_eq_psi_of_not_primePower {x : ℝ}
    (hx : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ≠ x) : midpointPsi x = Chebyshev.psi x := by
  rw [midpointPsi, psi_eq_sum_Icc]
  apply sum_congr rfl
  intro n _
  by_cases hn : IsPrimePow n
  · simp [endpointWeight, hx n hn]
  · simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]

/-- Symmetric height truncations of the explicit formula recover the midpoint Chebyshev function. -/
theorem tendsto_explicit_formula_midpointPsi {x : ℝ} (hx : 1 < x) :
    Tendsto (fun T => (x : ℂ) - sharpZetaZeroSum x T - Complex.log (2*(Real.pi : ℂ)) -
      (Real.log (1-(x^2)⁻¹) : ℂ)/2) atTop (𝓝 (midpointPsi x : ℂ)) := by
  have H := (((tendsto_const_nhds (x := (x : ℂ))).sub
    (tendsto_sharpZetaZeroSum_midpointPsi hx)).sub_const (Complex.log (2*(Real.pi : ℂ)))).sub_const
      ((Real.log (1-(x^2)⁻¹) : ℂ)/2)
  convert H using 1
  congr 1
  ring

end AnalyticNumberTheory.PrimeDistribution
