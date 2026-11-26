import AnalyticNumberTheory.AnalyticTools.ShiftedIntegratedPoles
import AnalyticNumberTheory.PrimeDistribution.RiemannCountingNormalization
import Mathlib.MeasureTheory.Integral.Prod

/-! # The integral of the shifted trivial zeros in Riemann's formula -/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private def trivialPower (n : ℕ) (y t : ℝ) : ℝ :=
  t^(-2*((n:ℝ)+1)-y-1)

private def trivialKernel (t y : ℝ) : ℝ :=
  Real.exp (-Real.log t*y)/(t*(t^2-1))

private theorem geometric_power {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t^((-2:ℝ)*((n:ℝ)+1)) = ((t^2)⁻¹)^(n+1) := by
  rw [Real.rpow_mul ht.le,←Nat.cast_add_one,Real.rpow_natCast,Real.rpow_neg ht.le,Real.rpow_two]

private theorem trivialPower_hasSum (y : ℝ) {t : ℝ} (ht : 1 < t) :
    HasSum (fun n => trivialPower n y t) (trivialKernel t y) := by
  have ht₀ := zero_lt_one.trans ht
  have ht₂ : 1 < t^2 := by nlinarith
  let q := (t^2)⁻¹
  have hq : q < 1 := (inv_lt_one₀ (sq_pos_of_pos ht₀)).mpr ht₂
  have hg := ((hasSum_geometric_of_lt_one (by dsimp [q]; positivity) hq).mul_right q).mul_left (t^(-y-1))
  have hval : t^(-y-1)*((1-q)⁻¹*q) = trivialKernel t y := by
    rw [Real.rpow_sub_one ht₀.ne',Real.rpow_def_of_pos ht₀]
    unfold trivialKernel q
    rw [show Real.log t*(-y) = -Real.log t*y by ring]
    field_simp [ht₀.ne',(sub_pos.mpr ht₂).ne',(sub_pos.mpr hq).ne']
  rw [hval] at hg
  apply hg.congr_fun
  intro n
  rw [trivialPower,show -2*((n:ℝ)+1)-y-1 = (-y-1)+(-2)*((n:ℝ)+1) by ring,
    Real.rpow_add ht₀,geometric_power ht₀,pow_succ]

private theorem trivialPower_integral {x y : ℝ} (hx : 1 < x) (hy : 0 ≤ y) (n : ℕ) :
    (∫ t in Ioi x, trivialPower n y t) = x^(-2*((n:ℝ)+1)-y)/(2*((n:ℝ)+1)+y) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  unfold trivialPower
  rw [integral_Ioi_rpow_of_lt (by linarith) (zero_lt_one.trans hx),
    sub_add_cancel,show -2*((n:ℝ)+1)-y = -(2*((n:ℝ)+1)+y) by ring,neg_div_neg_eq]

private theorem integrals_of_trivialPowers {x y : ℝ} (hx : 1 < x) (hy : 0 ≤ y) :
    HasSum (fun n => ∫ t in Ioi x, trivialPower n y t) (∫ t in Ioi x, trivialKernel t y) := by
  have hx₀ := zero_lt_one.trans hx
  have hx₂ : 1 < x^2 := by nlinarith
  let q := (x^2)⁻¹
  have hq : q < 1 := (inv_lt_one₀ (sq_pos_of_pos hx₀)).mpr hx₂
  have hgeom : Summable (fun n : ℕ => q^(n+1)) := by
    simpa only [pow_succ] using ((hasSum_geometric_of_lt_one (by dsimp [q]; positivity) hq).summable.mul_right q)
  have hi (n : ℕ) : IntegrableOn (trivialPower n y) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by linarith [Nat.cast_nonneg (α := ℝ) n]) hx₀
  have hn (n : ℕ) : (∫ t in Ioi x, ‖trivialPower n y t‖) = (∫ t in Ioi x, trivialPower n y t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact Real.norm_of_nonneg (Real.rpow_nonneg (hx₀.trans ht).le _)
  have hs : Summable fun n => ∫ t in Ioi x, ‖trivialPower n y t‖ := by
    apply hgeom.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
    intro n
    rw [hn,trivialPower_integral hx hy]
    have hc : 1 ≤ 2*((n:ℝ)+1)+y := by linarith [Nat.cast_nonneg (α := ℝ) n]
    apply (div_le_self (Real.rpow_nonneg hx₀.le _) hc).trans
    rw [← geometric_power hx₀]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have h := hasSum_integral_of_summable_integral_norm hi hs
  convert h using 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  exact (trivialPower_hasSum y (hx.trans ht)).tsum_eq.symm

/-- The shifted contributions at all negative even zeros. -/
def shiftedTrivialZeroContribution (x y : ℝ) : ℂ :=
  ∑' n, shiftedPoleResidue (trivialZetaZero n) y (Real.log x)

/-- The geometric series of trivial-zero powers gives an elementary integral for
the shifted residue sum on every nonnegative shift. -/
theorem shiftedTrivialZeroContribution_eq_integral {x y : ℝ} (hx : 1 < x) (hy : 0 ≤ y) :
    shiftedTrivialZeroContribution x y =
      -((∫ t in Ioi x, Real.exp (-Real.log t*y)/(t*(t^2-1)) : ℝ):ℂ) := by
  have h := Complex.hasSum_ofReal.mpr (integrals_of_trivialPowers hx hy)
  apply HasSum.tsum_eq
  apply h.neg.congr_fun
  intro n
  have hx₀ := zero_lt_one.trans hx
  let a : ℝ := -2*((n:ℝ)+1)-y
  have ha : trivialZetaZero n - (y:ℂ) = (a:ℂ) := by simp [trivialZetaZero,a]
  rw [shiftedPoleResidue,ha,←Complex.ofReal_mul,←Complex.ofReal_exp,←Complex.ofReal_div]
  change (((Real.exp (a*Real.log x)/a : ℝ):ℂ)) = -((∫ t in Ioi x, trivialPower n y t : ℝ):ℂ)
  rw [trivialPower_integral hx hy, ←Complex.ofReal_neg, Complex.ofReal_inj,
    Real.rpow_def_of_pos hx₀, mul_comm a (Real.log x)]
  dsimp only [a]
  rw [show -2*((n:ℝ)+1)-y = -(2*((n:ℝ)+1)+y) by ring,div_neg]

set_option maxHeartbeats 1200000 in
/-- The total shifted trivial residue is integrable and its integral is the negative
of the decaying tail in the single-endpoint Riemann formula. -/
theorem integral_shiftedTrivialZeroContribution {x : ℝ} (hx : 1 < x) :
    IntegrableOn (shiftedTrivialZeroContribution x) (Ioi 0) ∧
    (∫ y in Ioi (0:ℝ), shiftedTrivialZeroContribution x y) = -(riemannTrivialZeroTail x : ℂ) := by
  let μ := volume.restrict (Ioi x)
  let ν := volume.restrict (Ioi (0:ℝ))
  have hi (t : ℝ) (ht : x < t) : Integrable (trivialKernel t) ν :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (Real.log_pos (hx.trans ht))) 0).div_const _
  have hv (t : ℝ) (ht : x < t) : (∫ y, trivialKernel t y ∂ν) = (t*(t^2-1)*Real.log t)⁻¹ := by
    unfold trivialKernel ν
    rw [integral_div,integral_exp_mul_Ioi (neg_lt_zero.mpr (Real.log_pos (hx.trans ht)))]
    simp [div_eq_mul_inv,mul_comm,mul_assoc]
  have hp (t y : ℝ) (ht : x < t) : 0 ≤ trivialKernel t y := by
    have ht₀ := zero_lt_one.trans (hx.trans ht)
    have ht₂ : 0 < t^2-1 := by nlinarith [hx.trans ht]
    unfold trivialKernel
    positivity
  have hprod : Integrable (Function.uncurry trivialKernel) (μ.prod ν) := by
    apply (integrable_prod_iff (show Measurable (Function.uncurry trivialKernel) by
      change Measurable (fun p : ℝ × ℝ => Real.exp (-Real.log p.1*p.2)/(p.1*(p.1^2-1)))
      fun_prop).aestronglyMeasurable).mpr
    constructor
    · exact (ae_restrict_mem measurableSet_Ioi).mono hi
    · apply (integrableOn_riemannTrivialZeroTail hx).congr
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      rw [← hv t ht]
      apply integral_congr_ae
      exact ae_of_all _ fun y => (Real.norm_of_nonneg (hp t y ht)).symm
  have he : shiftedTrivialZeroContribution x =ᵐ[ν] (fun y : ℝ => -((∫ t, trivialKernel t y ∂μ : ℝ):ℂ)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun y hy => shiftedTrivialZeroContribution_eq_integral hx hy.le
  have hswap := integral_integral_swap (f := trivialKernel) hprod
  have htotal : (∫ t, ∫ y, trivialKernel t y ∂ν ∂μ) = riemannTrivialZeroTail x :=
    integral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono hv)
  refine ⟨(hprod.integral_prod_right.ofReal.neg).congr he.symm,?_⟩
  change (∫ y, shiftedTrivialZeroContribution x y ∂ν) = _
  rw [integral_congr_ae he,integral_neg,
    integral_complex_ofReal (μ := ν) (f := fun y => ∫ t, trivialKernel t y ∂μ),←hswap,htotal]

end AnalyticNumberTheory.PrimeDistribution
