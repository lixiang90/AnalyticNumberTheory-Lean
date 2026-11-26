import AnalyticNumberTheory.PrimeDistribution.RightZeroReciprocals
import AnalyticNumberTheory.PrimeDistribution.VonKoch

/-! # Grosswald's endpoint bound for the prime number theorem error -/

noncomputable section

open Complex Finset Filter Set Asymptotics
open scoped Classical
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.PrimeDistribution

/-- If the supremum Θ of the real parts of the nontrivial zeros is greater than
one half, the prime number theorem error is bounded by C x^Θ for every real x ≥ 2. -/
theorem grosswald_abs_psi_sub_id_le (hΘ : 1/2 < zetaSupRe) :
    ∃ C > 0, ∀ {x : ℝ}, 2 ≤ x → |Chebyshev.psi x-x| ≤ C*x^zetaSupRe := by
  let a := (1/2+zetaSupRe)/2
  let δ := zetaSupRe-a
  let E := (2/δ)^2
  have ha : 1/2 < a := by dsimp [a]; linarith
  have hδ : 0 < δ := by dsimp [δ,a]; linarith
  have hE : 0 < E := sq_pos_of_pos (div_pos two_pos hδ)
  obtain ⟨C, hC, HC⟩ := explicit_formula_psi
  obtain ⟨K, hK, HK⟩ := sum_zeroMultiplicity_div_norm_le
  obtain ⟨B, hB, HB⟩ := sum_zeroMultiplicity_div_norm_right_le ha
  let d := -deriv riemannZeta 0/riemannZeta 0
  refine ⟨3*C*E+‖d‖+K*E+B, by positivity, ?_⟩
  intro x hx
  let S := nontrivialZerosUpTo x
  let R := S.filter (fun z => a ≤ z.re)
  let q (z : ℂ) := (zeroMultiplicity z : ℝ)/‖z‖
  let X := x^zetaSupRe
  let P := x^a
  let L := Real.log x
  let Z := ∑ z ∈ S, (zeroMultiplicity z : ℂ)*((x : ℂ)^z/z)
  have hx₁ := one_le_two.trans hx
  have hx₀ := zero_lt_one.trans_le hx₁
  have hX : 1 ≤ X := Real.one_le_rpow hx₁ (by linarith)
  have hP : 1 ≤ P := Real.one_le_rpow hx₁ (by linarith)
  have hq (z : ℂ) : 0 ≤ q z := by dsimp only [q]; positivity
  have hL : 1/2 ≤ L := (by linarith [Real.log_two_gt_d9] : (1/2 : ℝ) ≤ Real.log 2).trans
    (Real.log_le_log two_pos hx)
  have hsmall : P*L^2 ≤ E*X := by
    have hlog := log_pow_le_rpow_mul_const 2 hδ hx₁
    change L^2 ≤ E*x^δ at hlog
    apply (mul_le_mul_of_nonneg_left hlog (zero_le_one.trans hP)).trans_eq
    change x^a*(E*x^δ) = E*x^zetaSupRe
    rw [mul_left_comm, ← Real.rpow_add hx₀, show a+δ = zetaSupRe by dsimp only [δ]; ring]
  have hright : (∑ z ∈ R, q z) ≤ B := HB R (fun z hz => by
    obtain ⟨hmem, hre⟩ := mem_filter.mp hz
    obtain ⟨hzero,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hmem
    exact ⟨mem_criticalStripZeros.mpr ⟨hzero,h₀,h₁⟩, hre⟩)
  have hsplit : ‖Z‖ ≤ P*(∑ z ∈ S, q z)+X*(∑ z ∈ R, q z) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ z ∈ S, (P*q z + if a ≤ z.re then X*q z else 0) := by
        apply sum_le_sum
        intro z hz
        obtain ⟨hzero,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
        rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hx₀,
          show (zeroMultiplicity z : ℝ)*(x^z.re/‖z‖) = x^z.re*q z by dsimp only [q]; ring]
        split_ifs with hre
        · apply (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx₁
            (re_le_zetaSupRe_of_nontrivial_zero hzero h₀ h₁)) (hq z)).trans
          exact le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans hP) (hq z))
        · rw [add_zero]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx₁ (le_of_not_ge hre)) (hq z)
      _ = _ := by dsimp only [R]; rw [sum_add_distrib, mul_sum, mul_sum, sum_filter]
  have hZ : ‖Z‖ ≤ (K*E+B)*X := by
    have h₁ := mul_le_mul_of_nonneg_left (HK x hx) (zero_le_one.trans hP)
    have h₂ := mul_le_mul_of_nonneg_left hright (zero_le_one.trans hX)
    have h₃ := mul_le_mul_of_nonneg_left hsmall hK.le
    change P*(∑ z ∈ S, q z) ≤ P*(K*L^2) at h₁
    linarith only [hsplit, h₁, h₂, h₃]
  have htr := HC x x hx hx le_rfl
  change ‖(Chebyshev.psi x : ℂ)-((x : ℂ)+d-Z)‖ ≤ C*(x*L^2/x+L) at htr
  rw [mul_div_cancel_left₀ _ hx₀.ne'] at htr
  have hL₂ : L^2 ≤ E*X := (le_mul_of_one_le_left (sq_nonneg _) hP).trans hsmall
  have hcost : L^2+L ≤ 3*(E*X) := by nlinarith [mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ 2*L-1)]
  calc
    _ = ‖(Chebyshev.psi x : ℂ)-(x : ℂ)‖ := by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖((Chebyshev.psi x : ℂ)-((x : ℂ)+d-Z))+(d-Z)‖ := by congr 1; ring
    _ ≤ ‖(Chebyshev.psi x : ℂ)-((x : ℂ)+d-Z)‖+‖d-Z‖ := norm_add_le _ _
    _ ≤ C*(L^2+L)+(‖d‖+‖Z‖) := add_le_add htr (norm_sub_le _ _)
    _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hcost hC.le, le_mul_of_one_le_right (norm_nonneg d) hX, hZ]

/-- Grosswald's refinement of the unconditional von Koch bound when Θ > 1/2. -/
theorem psi_error_isBigO_zetaSupRe_of_half_lt (hΘ : 1/2 < zetaSupRe) :
    (fun x : ℝ => Chebyshev.psi x-x) =O[atTop] fun x : ℝ => x^zetaSupRe := by
  obtain ⟨C, _, H⟩ := grosswald_abs_psi_sub_id_le hΘ
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using H hx

/-- Away from Θ = 1/2, the infimum of admissible pure-power error exponents
is attained, so it is also the least exponent. -/
theorem isLeast_psi_error_exponents_of_half_lt (hΘ : 1/2 < zetaSupRe) :
    IsLeast {a : ℝ | (fun x : ℝ => Chebyshev.psi x-x) =O[atTop] fun x : ℝ => x^a} zetaSupRe :=
  ⟨psi_error_isBigO_zetaSupRe_of_half_lt hΘ, fun _ ha => zetaSupRe_le_of_psi_error_isBigO ha⟩

end AnalyticNumberTheory.PrimeDistribution
