import AnalyticNumberTheory.DirichletSeries.Perron

/-! # Lower bounds for Riesz kernel denominators -/
open Real Complex Finset
namespace AnalyticNumberTheory.DirichletSeries

/-- The imaginary part gives a lower bound for each factor of a Riesz denominator. -/
theorem im_pow_le_rieszDenom_norm (k : ℕ) (w : ℂ) : |w.im|^(k+1)≤‖rieszDenom k w‖ := by
  rw [rieszDenom,norm_prod]
  calc |w.im|^(k+1) = ∏ _j ∈ range (k+1),|w.im| := by simp
       _ ≤ _ := prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => by
          simpa using Complex.abs_im_le_norm (w+(j:ℂ)))

/-- The first factor measures the distance to the pole, while each trailing
factor supplies a full power of vertical decay. -/
theorem rieszDenom_norm_lower (k : ℕ) {w : ℂ} (hw : -(1/2:ℝ)≤w.re)
    {d : ℝ} (hd : 0≤d) (hdw : d≤‖w‖) : d*((1+|w.im|)/3)^k≤‖rieszDenom k w‖ := by
  let q := 1+|w.im|
  have hq0 : 0<q := by dsimp [q];positivity
  have htail : (q/3)^k ≤ ∏ j ∈ range k, ‖w+((j+1:ℕ):ℂ)‖ := by
    calc (q/3)^k = ∏ _j ∈ range k, q/3 := by simp [div_pow]
         _ ≤ _ := by
           apply prod_le_prod₀ (fun _ _ => by positivity)
           intro j _
           have h₁ := Complex.re_le_norm (w+((j+1:ℕ):ℂ))
           have h₂ := Complex.abs_im_le_norm (w+((j+1:ℕ):ℂ))
           simp only [Nat.cast_add,Nat.cast_one,add_re,natCast_re,one_re,add_im,natCast_im,one_im,add_zero] at h₁ h₂ ⊢
           dsimp [q]
           linarith [Nat.cast_nonneg (α:=ℝ) j]
  rw [rieszDenom,norm_prod,prod_range_succ']
  simp only [Nat.cast_zero,add_zero]
  rw [mul_comm]
  exact mul_le_mul htail hdw hd (by positivity)

end AnalyticNumberTheory.DirichletSeries
