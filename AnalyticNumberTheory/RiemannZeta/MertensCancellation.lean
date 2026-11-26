import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion
import AnalyticNumberTheory.PrimeDistribution.TwistedPerron
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis
import AnalyticNumberTheory.RiemannZeta.ZeroFreeRegion

/-!
# Unconditional cancellation in the Möbius summatory function

The classical zero-free region permits a Perron shift for the reciprocal of zeta.
The removable zero at one contributes no residue. Balancing the vertical side with
the truncation error gives an exponential saving in the square root of the logarithm.
-/

noncomputable section

open Complex Filter Set
open scoped Topology ArithmeticFunction.Moebius LSeries.notation ComplexOrder
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.RiemannZeta

/-- The pole-removed quotient represents the reciprocal of zeta also at one. -/
theorem riemannZetaInv_eq_div_zetaOne (s : ℂ) : riemannZetaInv s = (s - 1) / zetaOne s := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [riemannZetaInv]
  rw [riemannZetaInv_eq_inv_of_ne_one hs, zetaOne_eq_sub_one_mul hs, div_eq_mul_inv, mul_inv_rev]
  have h := mul_inv_cancel₀ (sub_ne_zero.mpr hs)
  linear_combination -(riemannZeta s)⁻¹ * h

/-- The extended reciprocal is analytic at every nonzero value of zeta,
including the removable point at one. -/
theorem analyticAt_riemannZetaInv_of_ne_zero {s : ℂ} (hs : riemannZeta s ≠ 0) :
    AnalyticAt ℂ riemannZetaInv s := by
  have hden : zetaOne s ≠ 0 := by
    rcases eq_or_ne s 1 with rfl | h
    · simp
    rw [zetaOne_eq_sub_one_mul h]
    exact mul_ne_zero (sub_ne_zero.mpr h) hs
  have hnum : AnalyticAt ℂ (fun z : ℂ => z-1) s := analyticAt_id.sub analyticAt_const
  exact (hnum.div (differentiable_zetaOne.analyticAt s) hden).congr
    (Filter.Eventually.of_forall fun z => (riemannZetaInv_eq_div_zetaOne z).symm)

/-- At a real cutoff the complex coefficient sum of Möbius is the integer Mertens function. -/
theorem coeffPartialSum_moebius_floor (x : ℝ) :
    coeffPartialSum ↗μ ⌊x⌋₊ = (mertensM x : ℂ) := by
  simp [coeffPartialSum, mertensM, Int.cast_sum]

private lemma norm_moebius_le_one (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

private lemma moebius_absolute_series_le {c : ℝ} (hc : 1 < c) (hc' : c ≤ 2) :
    ∑' n : ℕ, ‖LSeries.term ↗μ (c : ℂ) n‖ ≤ 4 / (c-1)^2 := by
  have h₁ : LSeriesSummable 1 (c : ℂ) := LSeriesSummable_one_iff.mpr hc
  have hμ : LSeriesSummable ↗μ (c : ℂ) := DirichletSeries.LSeriesSummable_moebius_iff.mpr hc
  have heq (n : ℕ) : ‖LSeries.term 1 (c : ℂ) n‖ = (LSeries.term 1 (c : ℂ) n).re :=
    (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg
      (LSeries.term_nonneg (a := 1) (n := n) (by simp) c))).symm
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term 1 (c : ℂ) n‖ := hμ.norm.tsum_le_tsum
      (fun n => LSeries.norm_term_le _ (by simpa using norm_moebius_le_one n)) h₁.norm
    _ = (riemannZeta (c : ℂ)).re := by
      rw [← LSeries_one_eq_riemannZeta hc, LSeries, Complex.re_tsum h₁]
      exact tsum_congr heq
    _ ≤ ‖riemannZeta (c : ℂ)‖ := Complex.re_le_norm _
    _ ≤ c / (c-1) := by simpa using norm_riemannZeta_le_of_one_lt_re hc 0
    _ ≤ 4 / (c-1)^2 := by
      have hc0 : 0 < c-1 := by linarith
      rw [div_le_div_iff₀ hc0 (sq_pos_of_pos hc0)]
      have hprod := mul_le_mul hc' (show c-1 ≤ 1 by linarith) hc0.le (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [mul_le_mul_of_nonneg_right hprod hc0.le]

private theorem mertensM_halfInteger_bound :
    ∃ C > 0, ∃ γ > 0, ∀ N : ℕ, let x : ℝ := N + 1/2
      Real.exp 16 ≤ x → |(mertensM x : ℝ)| ≤ C * x * Real.exp (-γ * Real.sqrt (Real.log x)) := by
  obtain ⟨a,D,ha,_,hD,hregion⟩ := riemannZeta_zero_free_region_with_bounds
  let d := min a (1/8)
  have hd : 0 < d := lt_min ha (by norm_num)
  obtain ⟨C,hC,herr⟩ := PrimeDistribution.perron_rectangle_error_le_exp hd (min_le_right ..) hD
  refine ⟨C,hC,d/16,by positivity,?_⟩
  intro N x hx
  let y := Real.sqrt (Real.log x)
  let T := Real.exp y
  let heightLog := Real.log (T+3)
  let σ := 1-d/heightLog
  let c := 1+1/Real.log x
  let B := D*heightLog^2
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 16)).trans hx
  have hlog : 16 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hy2 : y^2 = Real.log x := Real.sq_sqrt (by linarith)
  have hy : 1 ≤ y := by nlinarith [Real.sqrt_nonneg (Real.log x)]
  have hT : 2 ≤ T := by
    have := Real.exp_le_exp.mpr hy
    dsimp only [T]
    linarith [Real.exp_one_gt_d9]
  have hyL : y ≤ heightLog := by
    calc y = Real.log T := (Real.log_exp y).symm
         _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  have hσ : 0 < σ := by
    have h := (div_le_self hd.le (hy.trans hyL)).trans (min_le_right a (1/8))
    dsimp [σ]; linarith
  have hσ₁ : σ ≤ 1 := sub_le_self _ (div_nonneg hd.le (by linarith))
  have hc : 1 < c := lt_add_of_pos_right _ (one_div_pos.mpr (by linarith))
  have hc' : c ≤ 2 := by
    have := div_le_one_of_le₀ (by linarith : 1 ≤ Real.log x) (by linarith)
    dsimp [c]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlocal (s : ℂ) (hr : σ ≤ s.re) (hi : |s.im| ≤ T) :
      riemannZeta s ≠ 0 ∧ ‖riemannZetaInv s‖ ≤ B := by
    have hl : 0 < Real.log (|s.im|+2) := Real.log_pos (by linarith [abs_nonneg s.im])
    have hlt : Real.log (|s.im|+2) ≤ heightLog := Real.log_le_log (by positivity) (by linarith)
    have hleft : 1 - a/Real.log (|s.im|+2) ≤ s.re :=
      (sub_le_sub_left (div_le_div₀ ha.le (min_le_left ..) hl hlt) 1).trans hr
    obtain ⟨hz,_,_,hbound⟩ := hregion hleft
    rw [Complex.re_add_im] at hz hbound
    refine ⟨hz,?_⟩
    rcases eq_or_ne s 1 with rfl | hne
    · simpa [riemannZetaInv] using hB
    rw [riemannZetaInv_eq_inv_of_ne_one hne]
    exact hbound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hlt 2) hD.le)
  have hedge (u t : ℝ) (hu : σ ≤ u) (ht : |t| ≤ T) :
      ‖riemannZetaInv ((u:ℂ)+(t:ℂ)*I)‖ ≤ B :=
    (hlocal _ (by simpa using hu) (by simpa using ht)).2
  have hcontour := norm_dirichletContourIntegral_le_of_rectangle (a := ↗μ) (F := riemannZetaInv)
    hx1 hσ (hσ₁.trans hc.le) (by linarith : 0 < T) hB hB
    (fun z hz => (analyticAt_riemannZetaInv_of_ne_zero (hlocal z hz.1.1 (abs_le.mpr hz.2)).1).differentiableAt.differentiableWithinAt)
    (fun t => by
      have hr : 1 < ((c:ℂ)+(t:ℂ)*I).re := by simpa using hc
      have hn : (c:ℂ)+(t:ℂ)*I ≠ 1 := by intro e; simp [e] at hr
      rw [riemannZetaInv_eq_inv_of_ne_one hn, LSeries_moebius_eq_inv_riemannZeta hr])
    (fun t ht => hedge σ t le_rfl (abs_le.mpr ht))
    (fun u hu => hedge u T hu.1 (abs_of_nonneg (by linarith)).le)
    (fun u hu => hedge u (-T) hu.1 (by rw [abs_neg,abs_of_nonneg (by linarith)]))
  have hN : 2 ≤ N := by
    by_contra! hn
    have hsmall : (N:ℝ) ≤ 1 := by exact_mod_cast (by omega : N ≤ 1)
    dsimp [x] at hx; linarith [Real.add_one_le_exp (16:ℝ)]
  have hcut := perron_halfInteger_log_error_le hN hc hc' hT
    (a := ↗μ) (DirichletSeries.LSeriesSummable_moebius_iff.mpr hc)
    (moebius_absolute_series_le hc hc') (fun n _ => (norm_moebius_le_one n).trans (by
      apply (Real.le_log_iff_exp_le (by positivity)).mpr
      change Real.exp 1 ≤ 2*x
      have hxlarge := Real.add_one_le_exp (16:ℝ)
      linarith [Real.exp_one_lt_d9]))
  let J := dirichletContourIntegral ↗μ x c T
  have htri := norm_sub_le J (J - coeffPartialSum ↗μ ⌊x⌋₊)
  rw [sub_sub_cancel, coeffPartialSum_moebius_floor, Complex.norm_intCast] at htri
  rw [← coeffPartialSum_moebius_floor x] at htri
  apply htri.trans
  exact (add_le_add hcontour hcut).trans (herr x hx)

/-- The unconditional Mertens bound with an exponential saving in the square root of log x. -/
theorem mertensM_exp_sqrt_log_bound :
    ∃ C > 0, ∃ γ > 0, ∀ᶠ x : ℝ in atTop,
      |(mertensM x : ℝ)| ≤ C*x*Real.exp (-γ * Real.sqrt (Real.log x)) := by
  obtain ⟨C,hC,γ,hγ,H⟩ := mertensM_halfInteger_bound
  refine ⟨2*C,by positivity,γ/2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 16+2)] with x hx
  let N := ⌊x⌋₊
  let y : ℝ := N+1/2
  have hbig := Real.add_one_le_exp (16:ℝ)
  have hx₁ : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hfloor : (N:ℝ) ≤ x := Nat.floor_le hx0.le
  have hceil : x < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hy : Real.exp 16 ≤ y := by dsimp [y]; linarith
  have hxy : x ≤ 2*y := by dsimp [y]; linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hyx : y ≤ 2*x := by dsimp [y]; linarith
  have hylog : 16 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hy
  have hlog : Real.log x ≤ 2*Real.log y := by
    calc _ ≤ Real.log (2*y) := Real.log_le_log hx0 hxy
         _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
         _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hroot : Real.sqrt (Real.log x) ≤ 2*Real.sqrt (Real.log y) := by
    nlinarith [Real.sq_sqrt (Real.log_nonneg hx₁),Real.sq_sqrt (by linarith : 0 ≤ Real.log y),
      Real.sqrt_nonneg (Real.log x),Real.sqrt_nonneg (Real.log y)]
  have hf : ⌊y⌋₊ = N := (Nat.floor_eq_iff hy0.le).mpr (by dsimp [y]; constructor <;> linarith)
  have he : mertensM x = mertensM y := by simp only [mertensM,hf,N]
  rw [he]
  apply (H N hy).trans
  apply mul_le_mul _ (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hroot hγ.le]))
    (Real.exp_pos _).le (by positivity)
  calc C*y ≤ C*(2*x) := by gcongr
       _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
