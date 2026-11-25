import AnalyticNumberTheory.DirichletSeries.Perron

/-!
# The Riesz kernel on a critical-line shift

The last six factors in the denominator each gain a power of the imaginary
part. The first factor can be estimated either by the horizontal distance
from its pole or by the height on the integration line.
-/

open Real Complex Finset
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.RiemannZeta

/-- The pole-cancelling linear factor and the Riesz denominator on the left line. -/
theorem riesz_six_critical_kernel_le {ρ w : ℂ} (hρ : 1 ≤ ρ.im)
    (hw : -(1/2:ℝ) ≤ w.re) (hw' : w.re ≤ 0) {d : ℝ} (hd : 0 < d) (hdw : d ≤ ‖w‖) :
    ‖1+w/(ρ-1)‖/‖rieszDenom 6 w‖ ≤ 1458/(d*(1+|w.im|)^5) := by
  let q := 1+|w.im|
  have hq : 1 ≤ q := by dsimp [q]; linarith [abs_nonneg w.im]
  have hq0 : 0 < q := by linarith
  have htail : (q/3)^6 ≤ ∏ j ∈ range 6, ‖w+((j+1:ℕ):ℂ)‖ := by
    calc (q/3)^6 = ∏ _j ∈ range 6, q/3 := by simp [div_pow]
         _ ≤ _ := by
           apply prod_le_prod₀ (fun _ _ => by positivity)
           intro j _
           have h₁ := Complex.re_le_norm (w+((j+1:ℕ):ℂ))
           have h₂ := Complex.abs_im_le_norm (w+((j+1:ℕ):ℂ))
           simp only [Nat.cast_add,Nat.cast_one,add_re,natCast_re,one_re,add_im,natCast_im,one_im,add_zero] at h₁ h₂ ⊢
           dsimp [q]
           linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hden : d*(q/3)^6 ≤ ‖rieszDenom 6 w‖ := by
    rw [rieszDenom,norm_prod,prod_range_succ']
    simp only [Nat.cast_zero,add_zero]
    rw [mul_comm]
    exact mul_le_mul htail hdw hd.le (by positivity)
  have hden0 : 0<‖rieszDenom 6 w‖ := (mul_pos hd (by positivity)).trans_le hden
  have hρ' : 1≤‖ρ-1‖ := by
    have hh := Complex.im_le_norm (ρ-1)
    simp only [sub_im,one_im,sub_zero] at hh; linarith
  have hwN : ‖w‖≤q := by
    have hh := norm_add_le (w.re:ℂ) ((w.im:ℂ)*I)
    rw [Complex.re_add_im,norm_mul,norm_I,mul_one,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonpos hw'] at hh
    dsimp [q]; linarith
  have hlin : ‖1+w/(ρ-1)‖≤2*q := by
    apply (norm_add_le ..).trans
    rw [norm_one,norm_div]
    have h := (div_le_self (norm_nonneg _) hρ').trans hwN
    linarith
  change ‖1+w/(ρ-1)‖/‖rieszDenom 6 w‖ ≤ 1458/(d*q^5)
  apply (div_le_div₀ (by positivity) hlin (mul_pos hd (by positivity)) hden).trans_eq
  field_simp [hd.ne',hq0.ne']; ring

end AnalyticNumberTheory.RiemannZeta
