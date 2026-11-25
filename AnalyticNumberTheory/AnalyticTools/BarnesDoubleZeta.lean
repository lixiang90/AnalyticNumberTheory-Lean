import AnalyticNumberTheory.AnalyticTools.LipschitzSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Barnes double zeta integral

For periods `1,b` and offset `a` in the open right half-plane, the
double zeta series has an absolutely convergent Mellin integral.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- A Barnes lattice vector with unit second period. -/
noncomputable def barnesVector (a b : ℂ) (p : ℕ×ℕ) : ℂ := a+b*(p.1:ℂ)+p.2

/-- The double zeta series of the two periods `b` and `1`. -/
noncomputable def barnesDoubleZeta (a b s : ℂ) : ℂ := ∑' p : ℕ×ℕ,(barnesVector a b p)^(-s)

theorem barnesVector_re_pos {a b : ℂ} (ha : 0<a.re) (hb : 0<b.re) (p : ℕ×ℕ) :
    0<(barnesVector a b p).re := by simp [barnesVector,Complex.mul_re]; positivity

/-- Convergence of the positive real majorant for a rank-two Barnes lattice. -/
theorem summable_barnes_real {a b u : ℝ} (ha : 0<a) (hb : 0<b) (hu : 2<u) :
    Summable fun p : ℕ×ℕ => (a+b*p.1+p.2)^(-u) := by
  let c := min 1 (min a b)
  have hc : 0<c := lt_min zero_lt_one (lt_min ha hb)
  have hc1 : c≤1 := min_le_left ..
  have hca : c≤a := (min_le_right ..).trans (min_le_left ..)
  have hcb : c≤b := (min_le_right ..).trans (min_le_right ..)
  let f (n : ℕ) := ((n+1:ℕ):ℝ)^(-(u/2))
  have hf : Summable f := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -(u/2)< -1))
  apply Summable.of_nonneg_of_le (fun p => Real.rpow_nonneg (by positivity) _)
    (f:=fun p : ℕ×ℕ => (c^(-(u/2)))^2*(f p.1*f p.2)) _ ((hf.mul_of_nonneg hf
      (fun _ => Real.rpow_nonneg (by positivity) _) (fun _ => Real.rpow_nonneg (by positivity) _)).mul_left _)
  intro p
  let w := a+b*(p.1:ℝ)+p.2
  have hw : 0<w := by dsimp [w]; positivity
  have h₁ : c*((p.1+1:ℕ):ℝ)≤w := by
    dsimp [w]; push_cast; nlinarith only [hca,mul_le_mul_of_nonneg_right hcb (Nat.cast_nonneg p.1),Nat.cast_nonneg (α:=ℝ) p.2]
  have h₂ : c*((p.2+1:ℕ):ℝ)≤w := by
    dsimp [w]; push_cast; nlinarith only [hca,mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg p.2),
      mul_nonneg hb.le (Nat.cast_nonneg p.1)]
  have hpow (n : ℕ) (hn : c*((n+1:ℕ):ℝ)≤w) : w^(-(u/2))≤c^(-(u/2))*f n := by
    rw [←Real.mul_rpow hc.le (Nat.cast_nonneg (n+1))]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hn (by linarith)
  have hp := mul_le_mul (hpow _ h₁) (hpow _ h₂) (Real.rpow_nonneg hw.le _) (by positivity)
  change w^(-u)≤_
  rw [←Real.rpow_add hw,show -(u/2)+ -(u/2)= -u by ring] at hp
  exact hp.trans_eq (by ring)

theorem summable_barnesDoubleZeta {a b s : ℂ} (ha : 0<a.re) (hb : 0<b.re) (hs : 2<s.re) :
    Summable fun p : ℕ×ℕ => (barnesVector a b p)^(-s) := by
  apply Summable.of_norm_bounded ((summable_barnes_real ha hb hs).mul_right (Real.exp (π*|s.im|)))
  intro p
  have h := norm_cpow_le_arg_bound (barnesVector a b p) (-s)
  simp only [Complex.neg_re,Complex.neg_im,abs_neg] at h
  apply h.trans
  have hp := barnesVector_re_pos ha hb p
  have hh := Real.rpow_le_rpow_of_nonpos hp (Complex.re_le_norm _) (by linarith : -s.re≤0)
  simp only [barnesVector,Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero] at hh
  exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

/-- Mellin kernel for a positive-period Barnes double zeta series. -/
noncomputable def barnesKernel (a b : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-a*t)/((1-Complex.exp (-b*t))*(1-Complex.exp (-(t:ℂ))))

private theorem barnes_geometric_series {a b : ℂ} (hb : 0<b.re) {t : ℝ} (ht : 0<t) :
    (∑' p : ℕ×ℕ,Complex.exp (-barnesVector a b p*t))=barnesKernel a b t := by
  let q := Complex.exp (-b*t)
  let r := Complex.exp (-(t:ℂ))
  have hq : ‖q‖<1 := by
    rw [Complex.norm_exp,←Real.exp_zero,Real.exp_lt_exp]; simp [Complex.mul_re]; positivity
  have hr : ‖r‖<1 := by
    rw [Complex.norm_exp,←Real.exp_zero,Real.exp_lt_exp]; simpa using neg_lt_zero.mpr ht
  have hsum := summable_mul_of_summable_norm (summable_geometric_of_norm_lt_one hq).norm
    (summable_geometric_of_norm_lt_one hr).norm
  have he (p : ℕ×ℕ) : Complex.exp (-barnesVector a b p*t)=Complex.exp (-a*t)*(q^p.1*r^p.2) := by
    dsimp [q,r]; rw [←Complex.exp_nat_mul,←Complex.exp_nat_mul,←Complex.exp_add,←Complex.exp_add]
    congr 1; dsimp [barnesVector]; ring
  simp_rw [he]; rw [tsum_mul_left,hsum.tsum_prod]
  simp_rw [tsum_mul_left,tsum_geometric_of_norm_lt_one hr]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hq]
  dsimp [barnesKernel,q,r]; rw [div_eq_mul_inv,mul_inv_rev]; ring

/-- Mellin representation of Barnes' double zeta for complex periods
with positive real parts. -/
theorem integral_barnesKernel {a b s : ℂ} (ha : 0<a.re) (hb : 0<b.re) (hs : 2<s.re) :
    (∫ t : ℝ in Ioi 0,barnesKernel a b t*(t:ℂ)^(s-1))=Complex.Gamma s*barnesDoubleZeta a b s := by
  let f (p : ℕ×ℕ) := gammaLaplaceKernel s (barnesVector a b p)
  have hsp : 0<s.re := by linarith
  have hi (p : ℕ×ℕ) : IntegrableOn (f p) (Ioi 0) := integrable_gammaLaplaceKernel hsp (barnesVector_re_pos ha hb p)
  have hj : Summable fun p : ℕ×ℕ => ∫ t : ℝ in Ioi 0,‖f p t‖ := by
    apply ((summable_barnes_real ha hb hs).mul_right (Real.Gamma s.re)).congr
    intro p
    let w := (barnesVector a b p).re
    have hw : 0<w := barnesVector_re_pos ha hb p
    have H := Real.integral_rpow_mul_exp_neg_mul_Ioi hsp hw
    have he : ∀ t∈Ioi (0:ℝ), ‖f p t‖=t^(s.re-1)*Real.exp (-w*t) :=
      fun _ ht => norm_gammaLaplaceKernel _ _ ht
    rw [setIntegral_congr_fun measurableSet_Ioi he]
    dsimp only [w,barnesVector] at *
    simp only [Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero] at *
    simpa only [Real.rpow_neg hw.le,one_div,Real.inv_rpow hw.le,neg_mul] using H.symm
  have he := integral_tsum_of_summable_integral_norm hi hj
  calc
    _ = ∫ t : ℝ in Ioi 0,∑' p : ℕ×ℕ,f p t := by
      apply setIntegral_congr_fun measurableSet_Ioi; intro t ht
      simp only [f,gammaLaplaceKernel,tsum_mul_right,barnes_geometric_series hb ht]
    _ = ∑' p : ℕ×ℕ,∫ t : ℝ in Ioi 0,f p t := he.symm
    _ = _ := by
      have h (p : ℕ×ℕ) : (∫ t : ℝ in Ioi 0,f p t)=(barnesVector a b p)^(-s)*Complex.Gamma s :=
        integral_gammaLaplaceKernel_rightHalfPlane hsp (barnesVector_re_pos ha hb p)
      simp_rw [h]; rw [tsum_mul_right,mul_comm]; rfl

end AnalyticNumberTheory.AnalyticTools
