import AnalyticNumberTheory.DirichletLFunctions.EffectiveQuadraticValue
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-!
# A numerical separation of real character zeros from one

The lower bound at one and a Cauchy bound with constant 72 give an
absolute zero-free interval, also for the possible exceptional character.
-/

open Real Set
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Every real zero of a nonprincipal real character, primitive or induced,
lies at the stated effective distance below one. -/
theorem real_zero_effective_gap {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hr : IsReal χ) (hχ : χ ≠ 1)
    {β : ℝ} (hzero : χ.LFunction (β : ℂ) = 0) :
    1 / (12960 * sqrt q * (log ((q:ℝ)+2))^3) ≤ 1-β := by
  let L := log ((q:ℝ)+2)
  have hq₁ : 1≤(q:ℝ) := by exact_mod_cast (show 1≤q by omega)
  have hs : 1 ≤ sqrt q := by simpa using sqrt_le_sqrt hq₁
  have hL : 1 ≤ L := (Real.log_exp 1).symm.trans_le (log_le_log (exp_pos _)
    (by linarith [exp_one_lt_d9]))
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hsp : 0 < sqrt q := lt_of_lt_of_le zero_lt_one hs
  have hβ : β < 1 := by
    by_contra! h
    exact LFunction_ne_zero_on_re_one χ (by simpa using h) (.inl hχ) hzero
  change 1/(12960*sqrt q*L^3) ≤ 1-β
  by_cases hnear : 1-1/(4*L) ≤ β
  · let g (t : ℝ) := χ.LFunction (t:ℂ)
    have hg (t : ℝ) : HasDerivAt g (deriv χ.LFunction (t:ℂ)) t :=
      (DirichletCharacter.differentiable_LFunction hχ (t:ℂ)).hasDerivAt.comp_ofReal
    have H := (convex_Icc (1-1/(4*L)) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hg t).differentiableAt)
      (fun t ht => by rw [(hg t).deriv]; exact norm_deriv_LFunction_near_one_explicit hq hχ t ht.1 ht.2)
      (x:=β) (y:=1) ⟨hnear,hβ.le⟩ ⟨sub_le_self _ (by positivity),le_rfl⟩
    simp only [g, Complex.ofReal_one, hzero, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hβ.le)] at H
    have hlow := quadratic_LFunction_one_lower_bound hq ((isReal_iff_sq_eq_one χ).mp hr) hχ
    have H' : 1/(180*sqrt q*L) ≤ 72*L^2*(1-β) :=
      hlow.trans ((Complex.re_le_norm _).trans H)
    rw [div_le_iff₀ (by positivity)] at H' ⊢
    linarith only [show 1 ≤ (1-β)*(12960*sqrt q*L^3) by convert H' using 1 <;> ring]
  · apply le_trans _ (by linarith only [hnear] : 1/(4*L) ≤ 1-β)
    apply one_div_le_one_div_of_le (by positivity)
    have H : (1:ℝ) ≤ sqrt q*L^2 := one_le_mul_of_one_le_of_one_le hs (one_le_pow₀ hL)
    nlinarith only [mul_le_mul_of_nonneg_right H hLp.le, hLp.le]

end AnalyticNumberTheory.DirichletLFunctions
