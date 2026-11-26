import AnalyticNumberTheory.RiemannZeta.LogarithmicGrowthUnderRH
import AnalyticNumberTheory.RiemannZeta.ZeroFreeRegion

/-!
# Littlewood's bounds on the line Re s = 1 under RH

Three-circles interpolation for the logarithmic derivative controls the variation of
the Euler logarithm across a horizontal interval of length 1/log log |t|.
-/

noncomputable section

open Complex Set Filter
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

private theorem euler_log_deriv_majorant :
    ∃ A : ℝ, 0 < A ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → ∀ {s : ℂ}, 1+δ ≤ s.re →
      ‖logDeriv riemannZeta s‖ ≤ A/δ := by
  obtain ⟨C,hC,H⟩ := neg_logDeriv_riemannZeta_one_add_le
  refine ⟨1+C, by positivity, ?_⟩
  intro δ hδ hδ₁ s hs
  have h₁ : 1 < ((1+δ : ℝ) : ℂ).re := by simpa using hδ
  have hsum := LSeriesSummable_vonMangoldt_iff.mpr h₁
  have h := norm_LSeries_le_re_of_nonnegative (fun n => Complex.zero_le_real.mpr
    (ArithmeticFunction.vonMangoldt_nonneg (n := n))) hsum hs
  rw [LSeries_vonMangoldt_eq (by linarith), LSeries_vonMangoldt_eq h₁, neg_div, norm_neg] at h
  apply (h.trans (H hδ hδ₁)).trans
  rw [le_div_iff₀ hδ, add_mul, div_mul_cancel₀ _ hδ.ne']
  linarith [mul_le_mul_of_nonneg_left hδ₁ hC.le]

private theorem thin_exponent {δ b : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hb : 1-δ ≤ b) (hb' : b ≤ 1+δ) :
    Real.log (b/(1-δ)) / Real.log ((5/4)/(1-δ)) ≤ (4/Real.log (5/4))*δ := by
  have hp : 0 < 1-δ := by linarith
  have hκ : 0 < Real.log (5/4:ℝ) := Real.log_pos (by norm_num)
  have hden : Real.log (5/4:ℝ) ≤ Real.log ((5/4)/(1-δ)) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hp).mpr (by linarith))
  have hnum : Real.log (b/(1-δ)) ≤ 4*δ := calc
    _ ≤ b/(1-δ)-1 := Real.log_le_sub_one_of_pos (div_pos (hp.trans_le hb) hp)
    _ ≤ _ := by rw [sub_le_iff_le_add, div_le_iff₀ hp]; nlinarith [mul_nonneg hδ.le (by linarith : 0 ≤ 1/2-δ)]
  rw [div_le_iff₀ (hκ.trans_le hden)]
  calc
    _ ≤ 4*δ := hnum
    _ = (4/Real.log (5/4)*δ)*Real.log (5/4) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

private theorem outer_derivative_bound (hRH : RiemannHypothesisProp) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t : ℝ), 8 ≤ |t| → ∀ v ∈ Metric.closedBall (⟨2,t⟩ : ℂ) (5/4),
      ‖deriv (slitLogZeta hRH) v‖ ≤ B*Real.log |t| := by
  obtain ⟨A,hA,H⟩ := norm_slitLogZeta_on_closedBall hRH (c := 2) (r := 11/8) (R := 23/16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨16*A, by positivity, ?_⟩
  intro t ht v hv
  let z : ℂ := ⟨2,t⟩
  have hd := differentiableOn_slitLogZeta_ball hRH (z := z) (R := 23/16)
    (by change (1/2 : ℝ) < 2-23/16; norm_num) (by change 23/16 < |t|; linarith)
  have hsub : Metric.closedBall v (1/8) ⊆ Metric.closedBall z (11/8) := by
    apply Metric.closedBall_subset_closedBall'
    change dist v z ≤ 5/4 at hv
    linarith
  have hcl := hd.diffContOnCl_ball (hsub.trans (Metric.closedBall_subset_ball (by norm_num : (11/8:ℝ) < 23/16)))
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/8) hcl
    (fun w hw => H t (by linarith) w (hsub (Metric.sphere_subset_closedBall hw)))
  have hs : |t|+2 ≤ |t|^2 := by nlinarith [sq_nonneg (|t|-2)]
  have hlog : Real.log (|t|+2) ≤ 2*Real.log |t| := by
    simpa [Real.log_pow] using Real.log_le_log (by positivity) hs
  nlinarith [mul_le_mul_of_nonneg_left hlog hA.le]

private theorem eventually_large_loglog :
    ∃ T : ℝ, 8 ≤ T ∧ ∀ u ≥ T, 4 ≤ Real.log (Real.log u) := by
  obtain ⟨U,H⟩ := tendsto_atTop_atTop.mp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop) 4
  exact ⟨max 8 U, le_max_left _ _, fun u hu => H u ((le_max_right _ _).trans hu)⟩

/-- Under RH, ζ'/ζ is O(log log |t|) in the shrinking neighborhood
|Re s − 1| ≤ 1/log log |t|, uniformly for large positive and negative heights. -/
theorem norm_logDeriv_riemannZeta_near_one_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C T : ℝ, 0 < C ∧ 8 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      |s.re-1| ≤ (Real.log (Real.log |s.im|))⁻¹ →
      ‖logDeriv riemannZeta s‖ ≤ C*Real.log (Real.log |s.im|) := by
  obtain ⟨A,hA,HA⟩ := euler_log_deriv_majorant
  obtain ⟨B,hB,HB⟩ := outer_derivative_bound hRH
  obtain ⟨T,hT,HT⟩ := eventually_large_loglog
  let D := max A B
  let κ := 4/Real.log (5/4:ℝ)
  have hD : 0 < D := hA.trans_le (le_max_left _ _)
  refine ⟨D*Real.exp κ,T,mul_pos hD (Real.exp_pos _),hT,?_⟩
  intro s ht hs
  let t := s.im
  let z : ℂ := ⟨2,t⟩
  let L := Real.log |t|
  let m := Real.log L
  let δ := m⁻¹
  have ht8 : 8 ≤ |t| := hT.trans ht
  have hm : 4 ≤ m := HT _ ht
  have hm0 : 0 < m := by linarith
  have hd : 0 < δ := inv_pos.mpr hm0
  have hd' : δ ≤ 1/4 := by simpa only [δ, one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4) hm
  have hL : 1 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by linarith : _ ≤ |t|))
    simpa [L] using h
  change |s.re-1| ≤ δ at hs
  have hre := abs_le.mp hs
  have hnorm : ‖s-z‖ = 2-s.re := by
    have he : s-z = ((s.re-2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [z,t]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hh := differentiableOn_slitLogZeta_ball hRH (z := z) (R := 11/8)
    (by change (1/2 : ℝ) < 2-11/8; norm_num) (by change 11/8 < |t|; linarith)
  have hinner (v : ℂ) (hv : v ∈ Metric.sphere z (1-δ)) : ‖deriv (slitLogZeta hRH) v‖ ≤ D*m := by
    rw [Metric.mem_sphere, dist_eq_norm] at hv
    have hx := Complex.abs_re_le_norm (v-z)
    rw [Complex.sub_re,hv] at hx
    change |v.re-2| ≤ 1-δ at hx
    have hx' : 1+δ ≤ v.re := by linarith [(abs_le.mp hx).1]
    have hvd := hasDerivAt_slitLogZeta hRH (s := v) (by linarith)
      (mem_slitPlane_iff.mpr (.inl (by simp only [Complex.sub_re,Complex.one_re]; linarith)))
    rw [hvd.deriv]
    apply (HA hd (by linarith) hx').trans
    simpa [δ,div_eq_mul_inv] using mul_le_mul_of_nonneg_right (le_max_left A B) hm0.le
  have houter (v : ℂ) (hv : v ∈ Metric.sphere z (5/4)) : ‖deriv (slitLogZeta hRH) v‖ ≤ (D*m)*L := by
    apply (HB t ht8 v (Metric.sphere_subset_closedBall hv)).trans
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hL)
    exact (le_max_right _ _).trans (le_mul_of_one_le_right hD.le (by linarith))
  let θ := Real.log ((2-s.re)/(1-δ)) / Real.log ((5/4)/(1-δ))
  have hθ : θ ≤ κ*δ := thin_exponent hd hd' (by linarith) (by linarith)
  have hpower : L^θ ≤ Real.exp κ := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hL), Real.exp_le_exp]
    change m*θ ≤ κ
    calc
      _ ≤ m*(κ*δ) := mul_le_mul_of_nonneg_left hθ hm0.le
      _ = κ := by dsimp [δ]; field_simp
  have hDm := mul_pos hD hm0
  have hinterp := hadamard_three_circles_annulus (by linarith : 0 < 1-δ) (by linarith : 1-δ < 5/4)
    (by norm_num : (5/4:ℝ) < 11/8) hDm (mul_pos hDm (zero_lt_one.trans_le hL))
    (hh.deriv Metric.isOpen_ball) hinner houter (w := s) (by rw [hnorm]; linarith) (by rw [hnorm]; linarith)
  have hsd := hasDerivAt_slitLogZeta hRH (s := s) (by linarith)
    (mem_slitPlane_iff.mpr (.inr (by simpa using (abs_pos.mp (by linarith : 0 < |t|)))))
  rw [logDeriv_apply, ← hsd.deriv]
  calc
    _ ≤ (D*m)^(1-θ) * ((D*m)*L)^θ := by simpa only [hnorm] using hinterp
    _ = (D*m)*L^θ := by rw [Real.mul_rpow hDm.le (zero_le_one.trans hL), ← mul_assoc,
      ← Real.rpow_add hDm, sub_add_cancel, Real.rpow_one]
    _ ≤ (D*m)*Real.exp κ := mul_le_mul_of_nonneg_left hpower hDm.le
    _ = (D*Real.exp κ)*m := by ring

/-- Under RH, the modulus of the Euler-normalized logarithm on Re s = 1 is at most
log log log |t| plus an absolute constant for all sufficiently large |t|. -/
theorem norm_slitLogZeta_one_le_log_log_log (hRH : RiemannHypothesisProp) :
    ∃ A T : ℝ, 0 < A ∧ 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖slitLogZeta hRH (1+(t : ℂ)*I)‖ ≤ Real.log (Real.log (Real.log |t|))+A := by
  obtain ⟨C,T,hC,hT,H⟩ := norm_logDeriv_riemannZeta_near_one_of_rh hRH
  obtain ⟨U,hU,HU⟩ := eventually_large_loglog
  refine ⟨Real.log 2+C,max T U,add_pos (Real.log_pos (by norm_num)) hC,hT.trans (le_max_left _ _),?_⟩
  intro t ht
  let m := Real.log (Real.log |t|)
  let δ := m⁻¹
  have hm : 4 ≤ m := HU _ ((le_max_right _ _).trans ht)
  have hm0 : 0 < m := by linarith
  have hδ : 0 < δ := inv_pos.mpr hm0
  have hδ₁ : δ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have ht₈ := hT.trans ((le_max_left _ _).trans ht)
  have ht0 := abs_pos.mp (show 0 < |t| by linarith)
  let f (x : ℝ) := slitLogZeta hRH ((x : ℂ)+(t : ℂ)*I)
  let g (x : ℝ) := logDeriv riemannZeta ((x : ℂ)+(t : ℂ)*I)
  have hd (x : ℝ) (hx : x ∈ Icc (1 : ℝ) (1+δ)) : HasDerivAt f (g x) x := by
    have hs : 1/2 < (((x : ℂ)+(t : ℂ)*I)).re := by simp; linarith [hx.1]
    have hcut : ((x : ℂ)+(t : ℂ)*I)-1 ∈ slitPlane := mem_slitPlane_iff.mpr (.inr (by simpa using ht0))
    simpa [f,g,logDeriv_apply,Function.comp_def] using
      ((hasDerivAt_slitLogZeta hRH hs hcut).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ)*I))).comp_ofReal
  have hbd (x : ℝ) (hx : x ∈ Ico (1 : ℝ) (1+δ)) : ‖g x‖ ≤ C*m := by
    have h := H ((x : ℂ)+(t : ℂ)*I) (by simpa using (le_max_left T U).trans ht) (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
        add_zero, Complex.add_im, Complex.mul_I_im, zero_add]
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      change x-1 ≤ δ
      linarith [hx.2])
    simpa [g,m] using h
  have hdist := norm_image_sub_le_of_norm_deriv_le_segment' (fun x hx => (hd x hx).hasDerivWithinAt)
    hbd (1+δ) (right_mem_Icc.mpr (by linarith))
  have hdiff : ‖f (1+δ)-f 1‖ ≤ C := by
    convert hdist using 1
    dsimp only [δ]
    field_simp
    ring
  have ha : 1 < 1+δ := by linarith
  have hz := norm_riemannZeta_le_of_one_lt_re ha 0
  have hz' : ‖riemannZeta ((1+δ : ℝ) : ℂ)‖ ≤ 2/δ := by
    apply (show ‖riemannZeta ((1+δ : ℝ) : ℂ)‖ ≤ (1+δ)/δ by simpa using hz).trans
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hE : ‖f (1+δ)‖ ≤ Real.log m + Real.log 2 := by
    dsimp only [f]
    rw [slitLogZeta_eq_logZeta hRH (by simpa using ha)]
    apply (norm_logZeta_le_log_norm_riemannZeta ha (by simp)).trans
    have hne := riemannZeta_ne_zero_of_one_lt_re (s := ((1+δ:ℝ) : ℂ)) ha
    calc
      _ ≤ Real.log (2/δ) := Real.log_le_log (norm_pos_iff.mpr hne) hz'
      _ = Real.log m + Real.log 2 := by simp only [Real.log_div (by norm_num : (2:ℝ) ≠ 0) hδ.ne', δ,Real.log_inv]; ring
  change ‖f 1‖ ≤ Real.log m + (Real.log 2+C)
  calc
    _ = ‖f (1+δ) - (f (1+δ)-f 1)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖f (1+δ)‖ + ‖f (1+δ)-f 1‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- On Re s = 1, RH gives Littlewood's O(log log |t|) bounds for both ζ and 1/ζ. -/
theorem norm_riemannZeta_one_and_inv_le_log_log (hRH : RiemannHypothesisProp) :
    ∃ C T : ℝ, 0 < C ∧ 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖riemannZeta (1+(t : ℂ)*I)‖ ≤ C*Real.log (Real.log |t|) ∧
      ‖(riemannZeta (1+(t : ℂ)*I))⁻¹‖ ≤ C*Real.log (Real.log |t|) := by
  obtain ⟨A,T,_,hT,H⟩ := norm_slitLogZeta_one_le_log_log_log hRH
  obtain ⟨U,_,HU⟩ := eventually_large_loglog
  refine ⟨Real.exp A,max T U,Real.exp_pos _,hT.trans (le_max_left _ _),?_⟩
  intro t ht
  have ht₈ := hT.trans ((le_max_left _ _).trans ht)
  have hm := HU _ ((le_max_right _ _).trans ht)
  let s := 1+(t : ℂ)*I
  have hs : 1/2 < s.re := by norm_num [s]
  have hs1 : s ≠ 1 := by
    intro he
    have h := congrArg Complex.im he
    simp [s] at h
    norm_num [h] at ht₈
  have hr := (Complex.abs_re_le_norm (slitLogZeta hRH s)).trans (H t ((le_max_left _ _).trans ht))
  change ‖riemannZeta s‖ ≤ _ ∧ ‖(riemannZeta s)⁻¹‖ ≤ _
  rw [← exp_slitLogZeta hRH hs hs1, ← Complex.exp_neg, Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
  have heq : Real.exp (Real.log (Real.log (Real.log |t|))+A) =
      Real.exp A*Real.log (Real.log |t|) := by rw [Real.exp_add, Real.exp_log (by linarith), mul_comm]
  exact ⟨(Real.exp_le_exp.mpr (abs_le.mp hr).2).trans_eq heq,
    (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hr).1])).trans_eq heq⟩

end AnalyticNumberTheory.RiemannZeta
