import AnalyticNumberTheory.DirichletLFunctions.DeuringHeilbronn

/-!
# The two shifted poles for repulsion within the exceptional character

Simultaneously translating the ζ and exceptional-character factors introduces
a second ζ pole. At small heights it is paired with the translated exceptional
zero. At larger heights its powers already decay geometrically.
-/
noncomputable section
open Complex Filter Set Finset Metric
open scoped Topology ArithmeticFunction
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Simultaneous positivity of the ζ and real-character factors at heights zero and t. -/
theorem self_shifted_four_logDeriv_power_nonpos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hr : IsReal χ)
    {σ : ℝ} (hσ : 1<σ) (t : ℝ) (k : ℕ) :
    (signedTaylorCoeff (logDeriv riemannZeta) σ k).re +
      (signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction χ)) σ k).re +
      (signedTaylorCoeff (logDeriv riemannZeta) (σ+t*I) k).re +
      (signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction χ)) (σ+t*I) k).re ≤ 0 := by
  have h₀ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)) (fun h => neg_logDeriv_riemannZeta_eq_LSeries h)
    (by simpa using hσ) k
  have h₁ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)) (fun h => neg_logDeriv_LFunction_eq_LSeries χ h)
    (by simpa using hσ) k
  have h₂ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)+t*I) (fun h => neg_logDeriv_riemannZeta_eq_LSeries h)
    (by simpa using hσ) k
  have h₃ := signedTaylorCoeff_LSeries_logDeriv (s:=(σ:ℂ)+t*I) (fun h => neg_logDeriv_LFunction_eq_LSeries χ h)
    (by simpa using hσ) k
  have h := Complex.reCLM.hasSum (((h₀.add h₁).add h₂).add h₃)
  have hp := h.nonneg (fun n => by
    simp only [Complex.reCLM_apply,Complex.add_re]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    have hfirst (a : ℕ → ℂ) : LSeries.term (LSeries.logMul^[k] a) σ n =
        (((Real.log n)^k*(n:ℝ)^(-σ):ℝ):ℂ)*a n := by simpa using term_iter_factor a hn k σ 0
    rw [hfirst,hfirst,term_iter_factor _ hn,term_iter_factor _ hn]
    let u := (n:ℂ)^(-(t:ℂ)*I)
    have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hv : ‖(n:ℂ)^(-(t:ℂ)*I)‖ = 1 := by
      rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
    have hu : ‖u‖ ≤ 1 := hv.le
    have hu' := (abs_le.mp ((Complex.abs_re_le_norm u).trans hu)).1
    have hχ' := (abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (norm_char_le_one χ _))).1
    have him := hr (n:ZMod q)
    have heq : (χ n : ℂ)*(Λ n:ℂ)*(n:ℂ)^(-(t:ℂ)*I) = (Λ n:ℂ)*(χ n*u) := by
      dsimp [u]; ring
    rw [heq]
    change 0 ≤ _ + _ + (_ * ((Λ n:ℂ)*u)).re + _
    simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      mul_zero,sub_zero,him,zero_mul]
    have hw : 0 ≤ (Real.log n)^k*(n:ℝ)^(-σ)*Λ n :=
      mul_nonneg (mul_nonneg (pow_nonneg (Real.log_nonneg hn') _) (Real.rpow_nonneg (by positivity) _))
        ArithmeticFunction.vonMangoldt_nonneg
    nlinarith only [mul_nonneg hw (mul_nonneg (by linarith : 0≤1+(χ n).re) (by linarith : 0≤1+u.re))])
  simp only [Complex.reCLM_apply,Complex.add_re,neg_mul,Complex.neg_re,
    Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hp
  have hk : 0<(k.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  by_contra! hbad
  nlinarith only [hp,mul_pos hk hbad]

theorem zetaOne_shifted_signed_coeff (t : ℝ) (k : ℕ) :
    signedTaylorCoeff (logDeriv zetaOne) (5/4+t*I) k =
      ((5/4+(t:ℂ)*I)-1)⁻¹^(k+1) + signedTaylorCoeff (logDeriv riemannZeta) (5/4+t*I) k := by
  let c : ℂ := 5/4+t*I
  let lin : ℂ → ℂ := fun w => w-1
  have hc : 1<c.re := by norm_num [c]
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const continuous_re
  have hmem : {w : ℂ | 1<w.re} ∈ 𝓝 c := hopen.mem_nhds hc
  have hn {w : ℂ} (hw : 1<w.re) : w≠1 := fun h => by subst w; simp at hw
  have he : zetaOne =ᶠ[𝓝 c] lin*riemannZeta := by
    filter_upwards [hmem] with w hw; exact zetaOne_eq_sub_one_mul (hn hw)
  have he' : logDeriv zetaOne =ᶠ[𝓝 c] fun w => (w-1)⁻¹+logDeriv riemannZeta w := by
    filter_upwards [hmem,logDeriv_congr_nhds he] with w hw hew
    rw [hew,logDeriv_mul (f:=lin) (g:=riemannZeta) w (sub_ne_zero.mpr (hn hw)) (riemannZeta_ne_zero_of_one_le_re hw.le)
      (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta (hn hw))]
    simp [lin,logDeriv_apply,one_div]
  have hζ : AnalyticAt ℂ riemannZeta c :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) c (hn hc)
  have hp : AnalyticAt ℂ (fun w => (w-1)⁻¹) c := (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hn hc))
  rw [signedTaylorCoeff_congr he',signedTaylorCoeff_add (h:=logDeriv riemannZeta) hp (hζ.deriv.div hζ (riemannZeta_ne_zero_of_one_le_re hc.le)),
    signedTaylorCoeff_inv_sub]
  <;> rfl

private theorem zetaOne_ne_zero_re_ge_one (z : ℂ) (hz : 1≤z.re) : zetaOne z≠0 := by
  by_cases he : z=1
  · simp [he]
  · rw [zetaOne_eq_sub_one_mul he]
    exact mul_ne_zero (sub_ne_zero.mpr he) (riemannZeta_ne_zero_of_one_le_re hz)

/-- The pole-removed ζ function at arbitrary height has local power bounds
linear in log(|t|+2), with an absolute implied constant. -/
theorem exists_shifted_zetaOne_zero_power_bounds :
    ∃ B : ℝ, 0<B ∧ ∀ t : ℝ, ∃ S, ZeroPowerBounds zetaOne (5/4+t*I) (B*Real.log (|t|+2)) S := by
  obtain ⟨A,hA,ha⟩ := norm_zetaOne_re_ge_half_le
  let J := 1+80*A
  have hJ : 1≤J := by dsimp [J]; linarith
  have hJP : 0<J := by linarith
  have hlogJ := Real.log_nonneg hJ
  let B := 88*(2*Real.log J+2)
  refine ⟨B,by dsimp [B]; positivity,fun t => ?_⟩
  let c : ℂ := 5/4+t*I
  let T := |t|+2
  let L := Real.log T
  have hT : 2≤T := by dsimp [T]; linarith [abs_nonneg t]
  have hL : 1/2≤L := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h; exact h.trans (Real.log_le_log (by norm_num) hT)
  have hlog : Real.log (J*T^2) ≤ (2*Real.log J+2)*L := by
    rw [Real.log_mul hJP.ne' (by positivity),Real.log_pow]
    dsimp [L] at *; norm_num only [Nat.cast_ofNat]
    nlinarith [mul_nonneg hlogJ (sub_nonneg.mpr hL)]
  have hc : c.re=5/4 := by simp [c]
  have hci : c.im=t := by simp [c]
  have hc1 : c≠1 := fun he => by rw [he] at hc; norm_num at hc
  have hdi : 1/4≤‖c-1‖ := by have h := Complex.re_le_norm (c-1); rw [Complex.sub_re,hc,Complex.one_re] at h; linarith
  have hsub : ‖(c-1)⁻¹‖ ≤ 4 := by rw [norm_inv,inv_eq_one_div,div_le_iff₀ (by linarith)]; linarith
  have hz : ‖(riemannZeta c)⁻¹‖≤5 := by
    have h := LFunction_one_eq_mul_riemannZeta (q:=1) hc1
    simp only [Nat.primeFactors_one,Finset.prod_empty,one_mul] at h
    rw [←h]; have hh := norm_inv_LFunction_le_one_add_inv (1:DirichletCharacter ℂ 1) (s:=c) (by rw [hc]; norm_num)
    rw [hc] at hh; norm_num at hh; simpa using hh
  apply scaled_zero_power_bounds (M:=J*T^2) (by positivity) hc
    ((differentiable_zetaOne.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)) zetaOne_ne_zero_re_ge_one
  · intro z hz'
    have hd : ‖z-c‖=3/4 := by simpa [mem_sphere,dist_eq_norm] using hz'
    have hre := Complex.abs_re_le_norm (z-c)
    have him := Complex.abs_im_le_norm (z-c)
    rw [Complex.sub_re,hc,hd] at hre
    rw [Complex.sub_im,hci,hd] at him
    have hzi : |z.im|+3 ≤ 2*T := by
      dsimp [T]; linarith [abs_sub_abs_le_abs_sub z.im t,abs_nonneg t]
    have hb := ha z (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2])
    have hbound : ‖zetaOne z‖ ≤ A*(2*T)^2 := hb.trans (by gcongr)
    have hi : ‖(zetaOne c)⁻¹‖ ≤ 20 := by
      rw [zetaOne_eq_sub_one_mul hc1,mul_inv, norm_mul]
      exact (mul_le_mul hsub hz (norm_nonneg _) (by norm_num)).trans (by norm_num)
    rw [div_eq_mul_inv,norm_mul]
    calc
      _ ≤ (A*(2*T)^2)*20 := by gcongr
      _ ≤ _ := by dsimp [J]; nlinarith [sq_nonneg T]
  · have h2 : 1/2≤Real.log 2 := by have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at this; linarith
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    change _ ≤ B*L*Real.log 2
    have hBL : 0≤B*L := by dsimp [B]; positivity
    dsimp [B] at *
    nlinarith [mul_nonneg hBL (sub_nonneg.mpr h2),mul_nonneg hlogJ (by linarith : 0≤L)]
  · change _ ≤ B*L; dsimp [B]; linarith

/-- Powers on the unit disk are n-Lipschitz. -/
private theorem norm_pow_sub_pow_le {a b : ℂ} (ha : ‖a‖≤1) (hb : ‖b‖≤1) (n : ℕ) :
    ‖a^n-b^n‖ ≤ n*‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a^(n+1)-b^(n+1)=a*(a^n-b^n)+(a-b)*b^n by ring]
    calc
      _ ≤ ‖a‖*‖a^n-b^n‖+‖a-b‖*‖b‖^n := by simpa only [norm_mul,norm_pow] using norm_add_le (a*(a^n-b^n)) ((a-b)*b^n)
      _ ≤ 1*(n*‖a-b‖)+‖a-b‖*1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hb
      _ = _ := by push_cast; ring

private theorem norm_shifted_denominator (t x : ℝ) (hx : x≤1) :
    1/4 ≤ ‖(5/4+(t:ℂ)*I)-(x:ℂ)‖ := by
  have h := Complex.re_le_norm ((5/4+(t:ℂ)*I)-(x:ℂ))
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,
    neg_zero,add_zero] at h
  norm_num only [Complex.div_ofNat_re] at h
  norm_num at h
  linarith

theorem shifted_real_zeroPowerPoint_norm_le (t x : ℝ) (hx : x≤1) :
    ‖zeroPowerPoint (5/4+t*I) ⟨x,0⟩‖≤1 := by
  have h := norm_shifted_denominator t x hx
  simp only [zeroPowerPoint,norm_div,norm_inv,Complex.norm_ofNat]
  rw [div_le_one (by norm_num),inv_eq_one_div,div_le_iff₀ (by linarith)]; linarith

/-- Uniform cancellation of the translated ζ pole with a translated real
exceptional zero in every power. -/
theorem shifted_pole_minus_zero_power_le (t α : ℝ) (hα : α≤1) (n : ℕ) :
    (zeroPowerPoint (5/4+t*I) ⟨1,0⟩^n).re -
    (zeroPowerPoint (5/4+t*I) ⟨α,0⟩^n).re ≤ 4*(1-α)*n := by
  let c : ℂ := 5/4+t*I
  have ha := norm_shifted_denominator t α hα
  have hu := norm_shifted_denominator t 1 le_rfl
  simp only [Complex.ofReal_one] at hu
  have han : 0<‖c-(α:ℂ)‖ := by dsimp [c]; linarith
  have hun : 0<‖c-1‖ := by dsimp [c]; linarith
  have he : ‖zeroPowerPoint c ⟨1,0⟩-zeroPowerPoint c ⟨α,0⟩‖ ≤ 4*(1-α) := by
    unfold zeroPowerPoint
    rw [←sub_div,inv_sub_inv (norm_pos_iff.mp hun) (norm_pos_iff.mp han),norm_div,norm_div,norm_mul,Complex.norm_ofNat,
      show c-(α:ℂ)-(c-1) = ((1-α:ℝ):ℂ) by push_cast; ring,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hα)]
    rw [div_le_iff₀ (by norm_num),div_le_iff₀ (mul_pos hun han)]
    have hmul := mul_le_mul hu ha (by norm_num) hun.le
    dsimp [c] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hα) (sub_nonneg.mpr hmul)]
  have hu' : ‖zeroPowerPoint c ⟨1,0⟩‖≤1 := by simpa using shifted_real_zeroPowerPoint_norm_le t 1 le_rfl
  have ha' := shifted_real_zeroPowerPoint_norm_le t α hα
  have h := norm_pow_sub_pow_le hu' ha' n
  have hreal := Complex.re_le_norm (zeroPowerPoint c ⟨1,0⟩^n-zeroPowerPoint c ⟨α,0⟩^n)
  rw [Complex.sub_re] at hreal
  exact (hreal.trans h).trans (by rw [mul_comm (4*(1-α))]; exact mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))

/-- At heights |t|≥3/16 the normalized pole has modulus at most 4/5. -/
theorem shifted_pole_norm_le_of_height {t : ℝ} (ht : 3/16≤|t|) :
    ‖zeroPowerPoint (5/4+t*I) ⟨1,0⟩‖ ≤ 4/5 := by
  let d : ℂ := 5/4+t*I-1
  have hsq : ‖d‖^2 = (1/4:ℝ)^2+t^2 := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]; dsimp [d]; norm_num; ring
  have hd : 5/16≤‖d‖ := by
    have ht' := sq_le_sq' (by linarith [abs_nonneg t] : -|t|≤3/16) ht
    rw [sq_abs] at ht'
    nlinarith [norm_nonneg d]
  change ‖d⁻¹/4‖ ≤ _
  rw [norm_div,norm_inv,Complex.norm_ofNat,div_le_iff₀ (by norm_num),inv_eq_one_div,div_le_iff₀ (by linarith)]
  linarith

theorem exceptional_zero_mem_shifted_ball {α t : ℝ} (hα : 31/32≤α) (hα' : α<1) (ht : |t|≤3/16) :
    (α:ℂ)∈closedBall (5/4+t*I) (3/8) := by
  rw [mem_closedBall,dist_eq_norm]
  let d : ℂ := α-(5/4+t*I)
  have hsq : ‖d‖^2 = (α-5/4)^2+t^2 := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]; dsimp [d]; norm_num; ring
  have ht' := sq_le_sq' (by linarith [abs_nonneg t] : -(3/16:ℝ)≤|t|) ht
  rw [sq_abs] at ht'
  have ha' := sq_le_sq' (by linarith : -(9/32:ℝ)≤α-5/4) (by linarith : α-5/4≤9/32)
  change ‖d‖≤_
  nlinarith [norm_nonneg d]

end AnalyticNumberTheory.DirichletLFunctions
