import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachPageAsymptotic

/-!
# A finite criterion for odd-prime triples

A numerical lower bound for the singular series translates the weighted
Page estimate into a lower bound for the number of ordered triples.
-/

open Real Finset
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- A logarithmic cutoff expressed in terms of the coefficient in the weighted estimate. -/
noncomputable def pageGoldbachRepresentationThreshold (C : ℝ) : ℝ :=
  max pageGoldbachLogThreshold ((16*C)^(5/2:ℝ))

private theorem page_log_threshold_large : (50000:ℝ)≤pageGoldbachLogThreshold := by
  unfold pageGoldbachLogThreshold
  apply le_trans _ ((le_max_left _ _).trans (le_max_right _ _))
  norm_num [Nat.factorial]

/-- A weighted estimate with coefficient `C` implies a numerical lower bound
for the number of ordered odd-prime triples above the associated cutoff. -/
theorem goldbachTernaryOddCount_lower_of_weighted {N : ℕ} (hodd : Odd N) {C : ℝ}
    (hC : 0≤C) (hsize : pageGoldbachRepresentationThreshold C≤log N)
    (herr : |goldbachTernaryWeighted N-goldbachTernarySingularSeries N*((N-1).choose 2:ℕ)| ≤
      C*((N:ℝ)^2/(log N)^(2/5:ℝ))) :
    (N:ℝ)^2/(8*(log N)^3) ≤ goldbachTernaryOddCount N := by
  let L := log (N:ℝ)
  have hL : 50000≤L := page_log_threshold_large.trans ((le_max_left _ _).trans hsize)
  have hN : N≠0 := by
    rintro rfl
    norm_num [L] at hL
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hLN : L≤N := log_le_self hn.le
  have hN' : 2≤N := by exact_mod_cast (show (2:ℝ)≤N by linarith)
  have hl : 0<L := by linarith
  have hcut : (16*C)^(5/2:ℝ)≤L := (le_max_right _ _).trans hsize
  have hcoef := rpow_le_rpow (rpow_nonneg (mul_nonneg (by norm_num) hC) _) hcut (by norm_num : 0≤(2/5:ℝ))
  rw [←rpow_mul (mul_nonneg (by norm_num) hC),show (5/2:ℝ)*(2/5)=1 by norm_num,rpow_one] at hcoef
  have hwe : C*((N:ℝ)^2/L^(2/5:ℝ)) ≤ (N:ℝ)^2/16 := by
    rw [←mul_div_assoc,div_le_iff₀ (rpow_pos_of_pos hl _)]
    nlinarith only [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (N:ℝ))]
  have hsqrt : 5184*L≤sqrt N := by
    have H := Real.pow_div_factorial_le_exp (L/2) (by positivity) 2
    rw [exp_half,show exp L=(N:ℝ) from exp_log hn] at H
    norm_num at H
    nlinarith only [H,mul_nonneg (show 0≤L-41472 by linarith) hl.le]
  have hprime : 324*(N:ℝ)^(3/2:ℝ)*L ≤ (N:ℝ)^2/16 := by
    have he : (N:ℝ)^(3/2:ℝ) = (N:ℝ)*sqrt N := by
      rw [sqrt_eq_rpow]
      rw [show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hn,rpow_one]
    rw [he]
    have H := mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hn.le (sqrt_nonneg (N:ℝ)))
    have he' : sqrt (N:ℝ)*((N:ℝ)*sqrt N)=(N:ℝ)^2 := by
      nlinarith only [congrArg (fun x : ℝ => (N:ℝ)*x) (sq_sqrt hn.le)]
    rw [he'] at H
    linarith only [H]
  have htwo : 3*(N:ℝ)*L^2≤(N:ℝ)^2/16 := by
    have H := pow_le_pow_left₀ (mul_nonneg (by norm_num) hl.le) hsqrt 2
    rw [sq_sqrt hn.le] at H
    have hq : 48*L^2≤N := by nlinarith only [H,sq_nonneg L]
    nlinarith only [mul_le_mul_of_nonneg_left hq hn.le]
  have hchoose : 3*(N:ℝ)^2/8≤((N-1).choose 2:ℕ) := by
    rw [Nat.cast_choose_two,Nat.cast_sub (by omega : 1≤N),Nat.cast_one]
    nlinarith only [mul_nonneg (show 0≤(N:ℝ)-12 by linarith) hn.le]
  have hmain := mul_le_mul_of_nonneg_right (one_le_goldbachTernarySingularSeries_of_odd hodd)
    (Nat.cast_nonneg (α:=ℝ) ((N-1).choose 2))
  have hw := (abs_le.mp (herr.trans hwe)).1
  have hp := (goldbachTernaryWeighted_sub_thetaWeighted_le hN').trans hprime
  have ht := (goldbachTernaryThetaWeighted_sub_odd_le hN').trans htwo
  change (N:ℝ)^2/(8*L^3) ≤ _
  rw [div_le_iff₀ (by positivity)]
  dsimp only [L] at *
  nlinarith only [hchoose,hmain,hw,hp,ht,sq_nonneg (N:ℝ)]

set_option maxRecDepth 4096 in
/-- Above a cutoff given by the Page estimates, every odd integer has at least
`N²/(8 log³ N)` ordered representations by three odd primes. -/
theorem page_goldbachTernaryOddCount_lower :
    ∃ c A b : ℝ, 0<c ∧ c≤1/4 ∧ 0<A ∧ 0<b ∧ ∀ {N : ℕ}, 2≤N → Odd N →
      pageGoldbachRepresentationThreshold (goldbachPageConstant c (pageMajorArcLogConstant A b 12 30))≤log N →
      (N:ℝ)^2/(8*(log N)^3) ≤ goldbachTernaryOddCount N := by
  obtain ⟨c,A,b,hc,hc',hA,hb,H⟩ := page_goldbachTernary_finite
  refine ⟨c,A,b,hc,hc',hA,hb,?_⟩
  intro N hN hodd hsize
  have hcoeff := pageMajorArcLogConstant_pos A b 12 30
  apply goldbachTernaryOddCount_lower_of_weighted hodd _ hsize (H hN ((le_max_left _ _).trans hsize))
  unfold goldbachPageConstant
  positivity

end AnalyticNumberTheory.AdditiveNumberTheory
