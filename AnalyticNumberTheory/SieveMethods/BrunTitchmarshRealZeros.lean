import AnalyticNumberTheory.SieveMethods.BrunTitchmarshBias
import AnalyticNumberTheory.DirichletSeries.PositiveDirichletMass
import AnalyticNumberTheory.DirichletLFunctions.EffectiveRealZero

/-!
# An improvement of Brun–Titchmarsh rules out exceptional real zeros

Near one, the positive Mangoldt series gives a lower bound of order
`B log q`. A real zero much closer than `1/(B² log q)` would cancel
the pole of zeta in the combined logarithmic derivative.
-/

open Real Filter Finset
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.SieveMethods

private theorem hasSum_positiveCharacterMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1<σ) :
    HasSum (fun n : ℕ => positiveCharacterMangoldt χ n*(n:ℝ)^(-σ))
      (-(logDeriv riemannZeta (σ:ℂ)).re-(logDeriv χ.LFunction (σ:ℂ)).re) := by
  obtain ⟨hZ,hZeq⟩ := neg_logDeriv_riemannZeta_eq_LSeries (s:=(σ:ℂ)) (by simpa using hσ)
  obtain ⟨hL,hLeq⟩ := neg_logDeriv_LFunction_eq_LSeries χ (s:=(σ:ℂ)) (by simpa using hσ)
  have H := Complex.hasSum_re (hZ.hasSum.add hL.hasSum)
  change HasSum _ ((LSeries (fun n => (Λ n:ℂ)) σ + LSeries (fun n => χ n*(Λ n:ℂ)) σ).re) at H
  rw [←hZeq,←hLeq] at H
  have hh : ((-deriv riemannZeta (σ:ℂ)/riemannZeta σ)+(-deriv χ.LFunction (σ:ℂ)/χ.LFunction σ)).re =
      -(logDeriv riemannZeta (σ:ℂ)).re-(logDeriv χ.LFunction (σ:ℂ)).re := by simp [logDeriv_apply,neg_div,sub_eq_add_neg]
  rw [hh] at H
  apply H.congr_fun
  intro n
  by_cases hn : n=0
  · subst n;simp [positiveCharacterMangoldt]
  have hpow : (n:ℂ)^(-(σ:ℂ)) = (((n:ℝ)^(-σ):ℝ):ℂ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_neg,Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp only [LSeries.term_of_ne_zero hn,Complex.add_re,div_eq_mul_inv,← Complex.cpow_neg,
    hpow,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,positiveCharacterMangoldt]
  ring

private theorem large_modulus_gap {η α : ℝ} (hη : 0<η) (hη' : η<1) (hα : 0<α)
    (H : BrunTitchmarshImprovement η α) :
    ∃ g : ℝ, 0<g ∧ ∀ᶠ q : ℕ in atTop, ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ≠1 →
      ∀ β : ℝ, χ.LFunction (β:ℂ)=0 → g/log q≤1-β := by
  obtain ⟨δ,hδ,hbias⟩ := positiveCharacterMangoldt_of_brunTitchmarsh hη hη' hα H
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.1 hbias
  obtain ⟨C,hC,hz⟩ := neg_logDeriv_riemannZeta_real_le
  let v := η/4
  have hv : 0<v := by dsimp [v]; positivity
  let B := max 1 (max δ⁻¹ (100/(v*exp (-2))))
  have hB : 1≤B := le_max_left ..
  have hB0 := zero_lt_one.trans_le hB
  have hBδ : δ⁻¹≤B := (le_max_left ..).trans (le_max_right ..)
  have hBv : 100≤B*(v*exp (-2)) := (div_le_iff₀ (mul_pos hv (exp_pos _))).mp
    ((le_max_right ..).trans (le_max_right ..) : 100/(v*exp (-2))≤B)
  let g := 1/B^2
  have hg : 0<g := by dsimp [g]; positivity
  have hg1 : g≤1 := by dsimp [g]; exact one_div_le_one_div_of_le zero_lt_one (one_le_pow₀ hB) |>.trans_eq (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨g,hg,?_⟩
  filter_upwards [eventually_ge_atTop 3,hlog.eventually_ge_atTop 8,hlog.eventually_ge_atTop C,
    hlog.eventually_ge_atTop (log (408*B)),hlog.eventually_ge_atTop (log (max 1 x₀))] with q hq hL hLC hLB hLx
  intro _ χ hχ β hzβ
  let L := log (q:ℝ)
  change 8≤L at hL
  change C≤L at hLC
  change log (408*B)≤L at hLB
  change log (max 1 x₀)≤L at hLx
  have hLp : 0<L := by linarith
  let U := B*L
  let u := 1/U
  have hU : L≤U := by dsimp [U];nlinarith only [mul_nonneg (sub_nonneg.mpr hB) hLp.le]
  have hU0 := hLp.trans_le hU
  have hu : 0<u := one_div_pos.mpr hU0
  have hu8 : u≤1/8 := one_div_le_one_div_of_le (by norm_num) (hL.trans hU)
  have hβ : β<1 := by
    by_contra! hh
    exact LFunction_ne_zero_on_re_one χ (by simpa using hh) (.inl hχ) hzβ
  by_contra! hsmall
  change 1-β<g/L at hsmall
  have hsmall8 : 1-β < 1/8 := hsmall.trans_le (div_le_div₀ (by norm_num) hg1 (by norm_num) hL)
  have hσ : 1<1+u := by linarith
  have hpos (t : ℝ) (ht : exp U≤t) : v*t ≤ ∑n∈Icc 1 ⌊t⌋₊,positiveCharacterMangoldt χ n := by
    have hx : x₀≤exp U := (le_max_right 1 x₀).trans
      (by rw [← exp_log (zero_lt_one.trans_le (le_max_left 1 x₀))];exact exp_le_exp.mpr (hLx.trans hU))
    apply hx₀ t (hx.trans ht) q χ hq hχ
    have htL : U≤log t := (le_log_iff_exp_le (lt_of_lt_of_le (exp_pos _) ht)).mpr ht
    calc L ≤ δ*U := by
             have hbδ : 1≤B*δ := (div_le_iff₀ hδ).mp (by simpa [one_div] using hBδ)
             dsimp [U];nlinarith only [mul_le_mul_of_nonneg_right hbδ hLp.le]
         _ ≤ _ := mul_le_mul_of_nonneg_left htL hδ.le
  have hsum := dirichlet_value_ge_of_linear_mass (positiveCharacterMangoldt_nonneg χ)
    (Y:=exp U) (X:=exp (2*U)) (v:=v) (u:=u) (one_le_exp hU0.le)
    (exp_le_exp.mpr (by linarith)) hu.le (hasSum_positiveCharacterMangoldt χ hσ)
    (fun t ht => hpos t ht.1)
  have hxlog : log (exp (2*U)/exp U)=U := by rw [log_div (exp_pos _).ne' (exp_pos _).ne',log_exp,log_exp]; ring
  have hxpow : (exp (2*U))^(-u)=exp (-2) := by
    rw [Real.rpow_def_of_pos (exp_pos _),log_exp];congr 1;dsimp [u];field_simp
  rw [hxlog,hxpow] at hsum
  have hlower : 100*L ≤ -(logDeriv riemannZeta ((1+u:ℝ):ℂ)).re-
      (logDeriv χ.LFunction ((1+u:ℝ):ℂ)).re := by
    apply le_trans _ hsum
    dsimp [U];nlinarith only [mul_le_mul_of_nonneg_right hBv hLp.le]
  have hZ := hz (1+u) ⟨hσ,by linarith⟩
  have hzreal : -(logDeriv riemannZeta ((1+u:ℝ):ℂ)).re ≤ 1/u+C := by
    simpa [logDeriv_apply,neg_div] using hZ
  have hmem : (β:ℂ)∈Metric.closedBall (((1+u:ℝ):ℂ)+(0:ℝ)*Complex.I) (1/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    simp only [Complex.ofReal_zero,zero_mul,add_zero,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_neg (by linarith)];linarith
  have hzchar := landau_LFunction_center_sub_zero_le hχ hu (by linarith) 0 hmem hzβ
  have hre : ((((1+u:ℝ):ℂ)+(0:ℝ)*Complex.I-(β:ℂ))⁻¹).re = 1/(1+u-β) := by
    simp only [Complex.ofReal_zero,zero_mul,add_zero,← Complex.ofReal_sub,← Complex.ofReal_inv,Complex.ofReal_re,one_div]
  rw [hre] at hzchar
  simp only [Complex.ofReal_zero,zero_mul,add_zero,abs_zero,zero_add] at hzchar
  have hlog₁ : log (408/u) ≤ 2*L := by
    rw [show 408/u=408*B*L by dsimp [u,U];field_simp,log_mul (by positivity) hLp.ne']
    linarith [log_le_self hLp.le]
  have hq0 : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have hlog₂ : log ((q:ℝ)*2)≤2*L := by
    rw [log_mul hq0.ne' (by norm_num)]; change L+log 2≤2*L; linarith [Real.log_le_self (by norm_num : (0:ℝ)≤2)]
  have hdiff : 1/u-1/(1+u-β) ≤ L := by
    let h := 1-β
    have hh : 0<h := sub_pos.mpr hβ
    have hprod : h < L*u^2 := by
      have hid : L*u^2=g/L := by dsimp [u,U,g]; field_simp
      exact hid ▸ hsmall
    have hden : 0<u+h := by positivity
    rw [show 1+u-β=u+h by dsimp [h];ring,show 1/u-1/(u+h)=h/(u*(u+h)) by field_simp;ring]
    apply (div_le_iff₀ (mul_pos hu hden)).mpr
    nlinarith only [hprod,mul_nonneg (mul_nonneg hLp.le hu.le) hh.le]
  linarith

/-- A fixed decrease of the coefficient two on any power range rules out exceptional
real zeros uniformly in the modulus. The hypothesis can hold only if every real
zero of every nonprincipal real character satisfies the stated logarithmic gap. -/
theorem real_zero_gap_of_brunTitchmarsh_improvement {η α : ℝ} (hη : 0<η) (hη' : η<1)
    (hα : 0<α) (H : BrunTitchmarshImprovement η α) :
    ∃ c : ℝ, 0<c ∧ ∀ {q : ℕ} [NeZero q], 3≤q → ∀ {χ : DirichletCharacter ℂ q},
      IsReal χ → χ≠1 → ∀ {β : ℝ}, χ.LFunction (β:ℂ)=0 → c/log q≤1-β := by
  obtain ⟨g,hg,hlarge⟩ := large_modulus_gap hη hη' hα H
  obtain ⟨N,hN⟩ := eventually_atTop.1 hlarge
  let D := 12960*sqrt N*(log ((N:ℝ)+2))^3
  let c := min g (log 3/max 1 D)
  have hD : 0<max 1 D := zero_lt_one.trans_le (le_max_left ..)
  have h3 : 0<log 3 := log_pos (by norm_num)
  refine ⟨c,lt_min hg (div_pos h3 hD),?_⟩
  intro q _ hq χ hreal hχ β hz
  have hqR : (3:ℝ)≤q := by exact_mod_cast hq
  have hL : 0<log q := h3.trans_le (log_le_log (by norm_num) hqR)
  by_cases h : N≤q
  · exact (div_le_div_of_nonneg_right (min_le_left ..) hL.le).trans (hN q h χ hχ β hz)
  have hqN : (q:ℝ)≤N := by exact_mod_cast (Nat.le_of_lt (not_le.mp h))
  have hgap := real_zero_effective_gap (by omega : 2≤q) hreal hχ hz
  have hd : 0<12960*sqrt q*(log ((q:ℝ)+2))^3 := by
    have := log_pos (show 1<(q:ℝ)+2 by linarith)
    have := sqrt_pos.2 (show (0:ℝ)<q by linarith)
    positivity
  have hdd : 12960*sqrt q*(log ((q:ℝ)+2))^3 ≤ max 1 D := by
    apply le_trans _ (le_max_right ..)
    have hlogq : 0≤log ((q:ℝ)+2) := log_nonneg (by linarith)
    dsimp [D];gcongr
  apply le_trans _ hgap
  calc c/log q ≤ (log 3/max 1 D)/log q := div_le_div_of_nonneg_right (min_le_right ..) hL.le
       _ ≤ (log q/max 1 D)/log q := by gcongr
       _ = 1/max 1 D := by field_simp
       _ ≤ _ := one_div_le_one_div_of_le hd hdd

end AnalyticNumberTheory.SieveMethods
