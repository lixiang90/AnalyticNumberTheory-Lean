import AnalyticNumberTheory.AnalyticTools.BarnesKernel

/-!
# Barnes double zeta integrals on rotated rays

Tilting the Mellin ray makes the real parts of both complex periods
positive even when their angle exceeds a right angle.
-/

open Complex Real Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

private theorem norm_exp_neg_mul_lt_one {w : ℂ} (hw : 0<w.re) {t : ℝ} (ht : 0<t) :
    ‖Complex.exp (-w*t)‖<1 := by
  rw [Complex.norm_exp,←Real.exp_zero,Real.exp_lt_exp]; simp [Complex.mul_re]; positivity

private theorem rotatedVector_re (a b ω : ℂ) (hω : ω.re=1) (p : ℕ×ℕ) :
    (barnesVector a b p*ω).re=(a*ω).re+(b*ω).re*(p.1:ℝ)+p.2 := by
  rw [show barnesVector a b p*ω=a*ω+(b*ω)*p.1+ω*p.2 by dsimp [barnesVector]; ring]
  simp [Complex.mul_re,hω]

private theorem rotatedKernel_series {a b ω : ℂ} (hb : 0<(b*ω).re) (hω : 0<ω.re) {t : ℝ} (ht : 0<t) :
    (∑' p : ℕ×ℕ,Complex.exp (-(barnesVector a b p*ω)*t))=barnesComplexKernel a b (ω*t) := by
  let q := Complex.exp (-(b*ω)*t)
  let r := Complex.exp (-ω*t)
  have hq : ‖q‖<1 := norm_exp_neg_mul_lt_one hb ht
  have hr : ‖r‖<1 := norm_exp_neg_mul_lt_one hω ht
  have hsum := summable_mul_of_summable_norm (summable_geometric_of_norm_lt_one hq).norm
    (summable_geometric_of_norm_lt_one hr).norm
  have he (p : ℕ×ℕ) : Complex.exp (-(barnesVector a b p*ω)*t)=Complex.exp (-(a*ω)*t)*(q^p.1*r^p.2) := by
    dsimp [q,r]; rw [←Complex.exp_nat_mul,←Complex.exp_nat_mul,←Complex.exp_add,←Complex.exp_add]
    congr 1; dsimp [barnesVector]; ring
  simp_rw [he]; rw [tsum_mul_left,hsum.tsum_prod]
  simp_rw [tsum_mul_left,tsum_geometric_of_norm_lt_one hr]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hq]
  dsimp [barnesComplexKernel,q,r]; rw [div_eq_mul_inv,mul_inv_rev]
  ring_nf

/-- The ray direction has real part one; its imaginary component may
be chosen to put the second period in a half-plane of decay. -/
theorem integral_rotatedBarnesKernel {a b ω s : ℂ} (ha : 0<(a*ω).re) (hb : 0<(b*ω).re)
    (hω : ω.re=1) (hs : 2<s.re) :
    (∫ t : ℝ in Ioi 0,barnesComplexKernel a b (ω*t)*(t:ℂ)^(s-1))=
      Complex.Gamma s*∑' p : ℕ×ℕ,(barnesVector a b p*ω)^(-s) := by
  let f (p : ℕ×ℕ) := gammaLaplaceKernel s (barnesVector a b p*ω)
  have hsp : 0<s.re := by linarith
  have hp (p : ℕ×ℕ) : 0<(barnesVector a b p*ω).re := by rw [rotatedVector_re a b ω hω]; positivity
  have hi (p : ℕ×ℕ) : IntegrableOn (f p) (Ioi 0) := integrable_gammaLaplaceKernel hsp (hp p)
  have hj : Summable fun p : ℕ×ℕ => ∫ t : ℝ in Ioi 0,‖f p t‖ := by
    apply ((summable_barnes_real ha hb hs).mul_right (Real.Gamma s.re)).congr
    intro p
    let w := (barnesVector a b p*ω).re
    have H := Real.integral_rpow_mul_exp_neg_mul_Ioi hsp (hp p)
    have he : ∀ t∈Ioi (0:ℝ), ‖f p t‖=t^(s.re-1)*Real.exp (-w*t) := fun _ ht => norm_gammaLaplaceKernel _ _ ht
    rw [setIntegral_congr_fun measurableSet_Ioi he]
    dsimp only [w]
    rw [←rotatedVector_re a b ω hω]
    simpa only [Real.rpow_neg (hp p).le,one_div,Real.inv_rpow (hp p).le,neg_mul] using H.symm
  have he := integral_tsum_of_summable_integral_norm hi hj
  calc
    _ = ∫ t : ℝ in Ioi 0,∑' p : ℕ×ℕ,f p t := by
      apply setIntegral_congr_fun measurableSet_Ioi; intro t ht
      simp only [f,gammaLaplaceKernel,tsum_mul_right,rotatedKernel_series hb (show 0<ω.re by rw [hω]; norm_num) ht]
    _ = ∑' p : ℕ×ℕ,∫ t : ℝ in Ioi 0,f p t := he.symm
    _ = _ := by
      have h (p : ℕ×ℕ) : (∫ t : ℝ in Ioi 0,f p t)=(barnesVector a b p*ω)^(-s)*Complex.Gamma s :=
        integral_gammaLaplaceKernel_rightHalfPlane hsp (hp p)
      simp_rw [h]; rw [tsum_mul_right,mul_comm]

/-- For a Barnes lattice in the closed upper half-plane and a ray
tilted clockwise, the complex powers acquire one fixed scalar. -/
theorem rotatedBarnes_tsum {a b ω : ℂ} (ha : 0≤a.im) (hb : 0≤b.im) (hω : ω.im<0) (s : ℂ) :
    (∑' p : ℕ×ℕ,(barnesVector a b p*ω)^(-s))=ω^(-s)*barnesDoubleZeta a b s := by
  have ht (p : ℕ×ℕ) : (barnesVector a b p*ω)^(-s)=ω^(-s)*(barnesVector a b p)^(-s) := by
    have him : 0≤(barnesVector a b p).im := by simp [barnesVector,Complex.mul_im]; positivity
    have harg := Complex.arg_nonneg_iff.mpr him
    rw [Complex.mul_cpow ⟨by linarith [Complex.neg_pi_lt_arg ω],
      by linarith [Complex.arg_le_pi (barnesVector a b p),Complex.arg_neg_iff.mpr hω]⟩,mul_comm]
  simp_rw [ht]; rw [tsum_mul_left]; rfl

end AnalyticNumberTheory.AnalyticTools
