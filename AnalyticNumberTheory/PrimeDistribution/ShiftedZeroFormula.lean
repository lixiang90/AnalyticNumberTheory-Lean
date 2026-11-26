import AnalyticNumberTheory.AnalyticTools.ShiftedIntegratedPoles
import AnalyticNumberTheory.PrimeDistribution.IntegratedExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.SharpExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.Oscillation
import AnalyticNumberTheory.RiemannZeta.ZeroEnumeration

/-!
# The shifted explicit formula before the first prime

On the first prime-free interval the logarithmic mean of the von Mangoldt coefficients
vanishes identically. A real exponential shift of its integrated explicit formula
therefore has value zero. Combining that identity with the centered partial fractions
separates the conditionally convergent unshifted sum from an absolutely summable
correction for every positive real shift other than the pole.
-/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.EntireFunctions
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem zero_re_le (Z : ZetaZeroEnumeration) (n : ℕ) : (Z.zero n).re ≤ 1 :=
  (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le

private theorem trivial_re_le (n : ℕ) : (trivialZetaZero n).re ≤ 1 := by
  simp [trivialZetaZero, Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The integrated explicit formula holds with any enumeration respecting the multiplicities. -/
theorem integratedZetaZeroSum_eq_logWeightedSum (Z : ZetaZeroEnumeration) {x : ℝ} (hx : 1 ≤ x) :
    integratedZetaZeroSum Z (Real.log x) = logWeightedSum (fun n => (Λ n : ℂ)) x := by
  obtain ⟨W,H⟩ := exists_logWeightedSum_vonMangoldt_eq_integratedZetaZeroSum
  have he (V : ZetaZeroEnumeration) := (V.hasSum_distinct (f := fun z => integratedPole z (Real.log x))
    (summable_integratedPole (zero_re_le V) V.summable_inv_sq _).hasSum).tsum_eq
  rw [H hx,integratedZetaZeroSum,integratedZetaZeroSum,←he Z,←he W]

/-- The height-ordered sum of x^ρ/ρ with analytic multiplicities. -/
def sharpZetaZeroSumLimit (x : ℝ) : ℂ := limUnder atTop (sharpZetaZeroSum x)

/-- The value of the sharp zero sum, including its half weight at jumps. -/
theorem sharpZetaZeroSumLimit_eq {x : ℝ} (hx : 1 < x) :
    sharpZetaZeroSumLimit x = (x:ℂ)-Complex.log (2*(Real.pi:ℂ))-
      (Real.log (1-(x^2)⁻¹) : ℂ)/2-(midpointPsi x : ℂ) :=
  (tendsto_sharpZetaZeroSum_midpointPsi hx).limUnder_eq

private theorem shifted_integrated_vanishes (Z : ZetaZeroEnumeration) {x : ℝ}
    (hx : 1 < x) (hx₂ : x < 2) (y : ℝ) :
    exponentialShiftOfPrimitive y (Real.log x) (integratedZetaZeroSum Z) = 0 := by
  apply exponentialShiftOfPrimitive_eq_zero (Real.log_pos hx).le
  intro t ht
  have ht₁ := Real.one_le_exp ht.1
  have ht₂ : Real.exp t < 2 := (Real.exp_le_exp.mpr ht.2).trans_lt (by rwa [Real.exp_log (zero_lt_one.trans hx)])
  have hf : ⌊Real.exp t⌋₊ = 1 := (Nat.floor_eq_iff (Real.exp_pos _).le).mpr (by norm_num; exact ⟨ht.1,ht₂⟩)
  have he := integratedZetaZeroSum_eq_logWeightedSum Z ht₁
  simpa [Real.log_exp,logWeightedSum,hf] using he

private theorem zero_ne_shift (Z : ZetaZeroEnumeration) {y : ℝ} (hy : 0 < y) (n : ℕ) : Z.zero n ≠ y := by
  intro he
  exact riemannZeta_ofReal_ne_zero_of_pos hy (he ▸ (mem_criticalStripZeros.mp (Z.mem_strip n)).1)

private theorem trivial_ne_shift {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : trivialZetaZero n ≠ y := by
  intro he
  have h := congrArg Complex.re he
  simp [trivialZetaZero,Complex.mul_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Before the first prime, the shifted polar term minus ζ'/ζ equals the damped
sharp zero sum, an absolutely summable correction at the nontrivial zeros, and
the residues at the trivial zeros. -/
theorem shifted_explicit_formula_of_lt_two (Z : ZetaZeroEnumeration) {x y : ℝ}
    (hx : 1 < x) (hx₂ : x < 2) (hy : 0 < y) (hy₁ : y ≠ 1) :
    shiftedPoleResidue 1 y (Real.log x) - deriv riemannZeta y / riemannZeta y =
      Complex.exp (-(y:ℂ)*(Real.log x : ℂ))*sharpZetaZeroSumLimit x +
        (∑' n, shiftedPoleCorrection (Z.zero n) y (Real.log x)) +
        ∑' n, shiftedPoleResidue (trivialZetaZero n) y (Real.log x) := by
  let u := Real.log x
  let E := Complex.exp (-(y:ℂ)*(u:ℂ))
  let C := Complex.log (2*(Real.pi:ℂ))
  let L := (Real.log (1-(x^2)⁻¹) : ℂ)/2
  have hu := (Real.log_pos hx).le
  have hx₀ := zero_lt_one.trans hx
  have hyc : (y:ℂ) ≠ 1 := by exact_mod_cast hy₁
  have hc (z : ℂ) : Complex.exp (z*(u:ℂ)) = (x:ℂ)^z := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx₀.ne'),←Complex.ofReal_log hx₀.le,mul_comm z]
  have hN := hasSum_shiftedPoleCorrection (a := Z.zero) zero_le_one (zero_re_le Z) Z.summable_inv_sq
    Z.zero_ne_zero (zero_ne_shift Z hy) (Z.summable_centered y) (u := u) hu hy
  have hT := hasSum_shiftedPoleCorrection (a := trivialZetaZero) zero_le_one trivial_re_le summable_trivialZetaZero_inv_sq
    trivialZetaZero_ne_zero (trivial_ne_shift hy.le) (summable_centered_trivialZetaZero y) (u := u) hu hy
  have hR : HasSum (fun n => shiftedPoleResidue (trivialZetaZero n) y u)
      (E*L + ∑' n, shiftedPoleCorrection (trivialZetaZero n) y u) := by
    apply (((hasSum_cpow_trivialZetaZero_div hx).mul_left E).add hT.summable.hasSum).congr_fun
    intro n
    rw [shiftedPoleResidue_eq_damped_add u (trivialZetaZero_ne_zero n) (trivial_ne_shift hy.le n),hc (trivialZetaZero n)]
  have hP : shiftedPoleResidue 1 y u = E*(x:ℂ) + shiftedPoleCorrection 1 y u := by
    rw [shiftedPoleResidue_eq_damped_add u one_ne_zero hyc.symm, hc 1, Complex.cpow_one, div_one]
  have hD := neg_logDeriv_riemannZeta_eq_distinct_centered hyc (riemannZeta_ofReal_ne_zero_of_pos hy)
  rw [(Z.hasSum_distinct (f := fun z => centeredPole z y) (Z.summable_centered y).hasSum).tsum_eq] at hD
  have hA : Continuous (integratedPole 1) := by unfold integratedPole; fun_prop
  have hB : Continuous (fun t : ℝ => C*(t:ℂ)) := continuous_const.mul Complex.continuous_ofReal
  have hF := continuous_tsum_integratedPole zero_le_one (zero_re_le Z) Z.summable_inv_sq
  have hG := continuous_tsum_integratedPole zero_le_one trivial_re_le summable_trivialZetaZero_inv_sq
  have hzero := shifted_integrated_vanishes Z hx hx₂ y
  change exponentialShiftOfPrimitive y u (fun t => integratedPole 1 t-C*(t:ℂ)-
    (∑' n, integratedPole (Z.zero n) t)-∑' n, integratedPole (trivialZetaZero n) t) = 0 at hzero
  have hAB : Continuous (fun t : ℝ => integratedPole 1 t-C*(t:ℂ)) := hA.sub hB
  have hABF : Continuous (fun t : ℝ => integratedPole 1 t-C*(t:ℂ)-∑' n, integratedPole (Z.zero n) t) := hAB.sub hF
  rw [exponentialShiftOfPrimitive_sub y u hABF hG,
    exponentialShiftOfPrimitive_sub y u hAB hF,exponentialShiftOfPrimitive_sub y u hA hB,
    exponentialShiftOfPrimitive_linear hy,exponentialShiftOfPrimitive_integratedPole_eq_centered one_ne_zero hyc.symm hu hy] at hzero
  have hf : ⌊x⌋₊ = 1 := (Nat.floor_eq_iff hx₀.le).mpr (by norm_num; exact ⟨hx.le,hx₂⟩)
  have hψ : midpointPsi x = 0 := by simp [midpointPsi,hf]
  have hL : sharpZetaZeroSumLimit x = (x:ℂ)-C-L := by simp only [sharpZetaZeroSumLimit_eq hx,hψ,Complex.ofReal_zero,sub_zero,C,L]
  change shiftedPoleResidue 1 y u - deriv riemannZeta y / riemannZeta y = E*sharpZetaZeroSumLimit x + _ + _
  rw [show shiftedPoleResidue 1 y u - deriv riemannZeta y / riemannZeta y =
    shiftedPoleResidue 1 y u + (-deriv riemannZeta y / riemannZeta y) by ring, hD,hP,hL,hR.tsum_eq,hN.tsum_eq,hT.tsum_eq]
  change _-C*(1-E)-_-_ = 0 at hzero
  dsimp only [C] at hzero ⊢
  linear_combination hzero

end AnalyticNumberTheory.PrimeDistribution
