import AnalyticNumberTheory.PrimeDistribution.LeastPrimeMoments
import AnalyticNumberTheory.DirichletLFunctions.DeuringHeilbronn

/-!
# Expansion of the high moments for the least-prime problem

The center 1+1/1024 and the zero disk have fixed radii independent of the
modulus. Powers of the scaled reciprocal distances describe the moments.
Their analytic remainder decays geometrically in the order.
-/
noncomputable section
open Complex Real Finset Filter Metric Set
open scoped Classical Topology
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.PrimeDistribution

def leastPrimeMomentCenter : ℂ := 1+1/1024

/-- Every distinct zero in the moment disk appears once. Multiplicities enter
the moment expansion separately. -/
def leastPrimeMomentZeros (f : ℂ → ℂ) : Finset ℂ :=
  if h : (zeroSet f leastPrimeMomentCenter (3/8)).Finite then h.toFinset else ∅

def leastPrimeZeroRatio (z : ℂ) : ℂ := (1/1024)/(leastPrimeMomentCenter-z)

theorem mem_leastPrimeMomentZeros {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall leastPrimeMomentCenter (3/4)))
    (hn : f leastPrimeMomentCenter≠0) {z : ℂ} :
    z∈leastPrimeMomentZeros f ↔ z∈closedBall leastPrimeMomentCenter (3/8) ∧ f z=0 := by
  have hf' : AnalyticOnNhd ℂ f (closedBall leastPrimeMomentCenter (3/8)) := hf.mono (closedBall_subset_closedBall (by norm_num))
  simp only [leastPrimeMomentZeros,dif_pos (zeroSet_finite (by norm_num) hf' hn),Set.Finite.mem_toFinset,mem_zeroSet]

private theorem moment_disk_expansion {f : ℂ → ℂ} {M : ℝ} (hM : 1≤M)
    (hf : AnalyticOnNhd ℂ f (closedBall leastPrimeMomentCenter (3/4))) (hn : f leastPrimeMomentCenter≠0)
    (hb : ∀ z ∈ sphere leastPrimeMomentCenter (3/4), ‖f z/f leastPrimeMomentCenter‖≤M) (m : ℕ) :
    ‖(1/1024:ℂ)^(m+1)*signedTaylorCoeff (logDeriv f) leastPrimeMomentCenter m -
      ∑ z ∈ leastPrimeMomentZeros f,(analyticOrderNatAt f z:ℂ)*(leastPrimeZeroRatio z)^(m+1)‖ ≤
      Real.log M*(1/256:ℝ)^m := by
  let c := leastPrimeMomentCenter
  obtain ⟨Z,hZ,_,hp⟩ := local_logDeriv_power_sum (by linarith : 0<M) hf hn hb
  have hz : Z=leastPrimeMomentZeros f := by
    ext z; rw [mem_leastPrimeMomentZeros hf hn]
    change z∈(Z:Set ℂ) ↔ _; rw [hZ]; rfl
  rw [←hz]
  let e := (1/1024:ℂ)^(m+1)
  have he : (∑ z ∈ Z,(analyticOrderNatAt f z:ℂ)*(leastPrimeZeroRatio z)^(m+1)) =
      e*∑ z ∈ Z,(analyticOrderNatAt f z:ℂ)*(c-z)⁻¹^(m+1) := by
    rw [mul_sum]; apply sum_congr rfl; intro z _
    dsimp only [leastPrimeZeroRatio,e,c]; rw [div_eq_mul_inv,mul_pow]; ring
  rw [he,←mul_sub,norm_mul]
  have hnE : ‖e‖=(1/1024:ℝ)^(m+1) := by dsimp only [e]; rw [norm_pow]; norm_num
  change ‖e‖*_ ≤ _
  rw [hnE]
  calc
    _ ≤ (1/1024:ℝ)^(m+1)*(352*Real.log M*(16/5:ℝ)^m) := by gcongr; exact hp m
    _ = (352/1024*Real.log M)*(1/320:ℝ)^m := by
      rw [show (1/320:ℝ)=(1/1024)*(16/5) by norm_num,mul_pow,pow_succ]; ring
    _ ≤ _ := by
      apply mul_le_mul _ (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by positivity) (Real.log_nonneg hM)
      linarith [Real.log_nonneg hM]

/-- Finite local expansion of a nonprincipal character moment. The logarithmic
factor includes the modulus and the implicit constant is independent of m. -/
theorem nonprincipal_moment_zero_expansion {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (m : ℕ) :
    ‖(∑' n, turanMangoldtTerm χ (1/1024) 0 m n) +
      ∑ z ∈ leastPrimeMomentZeros (DirichletCharacter.LFunction χ),
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) z:ℂ)*leastPrimeZeroRatio z^(m+1)‖ ≤
      24*Real.log ((q:ℝ)+2)*(1/256:ℝ)^m := by
  let c := leastPrimeMomentCenter
  have hc : c.re=1+1/1024 := by norm_num [c,leastPrimeMomentCenter]
  have hc' : 1<c.re := by rw [hc]; norm_num
  have hci : c.im=0 := by norm_num [c,leastPrimeMomentCenter]
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c (3/4)) :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hM : 1≤(2:ℝ)^20*(q:ℝ)^2 := by nlinarith [one_le_pow₀ hq (n:=2)]
  have hh := moment_disk_expansion hM hf (LFunction_ne_zero_on_re_one χ hc'.le (.inl hχ)) (fun w hw => by
    have hd : ‖w-c‖=3/4 := by simpa [mem_sphere,dist_eq_norm] using hw
    have hre := Complex.abs_re_le_norm (w-c)
    have him := Complex.abs_im_le_norm (w-c)
    rw [Complex.sub_re,hc,hd] at hre; rw [Complex.sub_im,hci,sub_zero,hd] at him
    have hw' := norm_LFunction_strip_poly_le hχ (by linarith [(abs_le.mp hre).1] : -(1/2:ℝ)≤w.re)
      (by linarith [(abs_le.mp hre).2] : w.re≤2)
    have hp : (q:ℝ)+48*(q:ℝ)^2≤49*(q:ℝ)^2 := by nlinarith [mul_nonneg (by positivity : 0≤(q:ℝ)) (sub_nonneg.mpr hq)]
    have hb : ‖DirichletCharacter.LFunction χ w‖ ≤ 49*(q:ℝ)^2*3^2 := by
      refine hw'.trans ?_; gcongr; linarith
    have hi := norm_inv_LFunction_le_one_add_inv χ hc'
    rw [hc] at hi; norm_num at hi
    rw [div_eq_mul_inv,norm_mul,norm_inv]
    calc
      _ ≤ (49*(q:ℝ)^2*3^2)*1025 := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (q:ℝ)]) m
  have hMlog : Real.log ((2:ℝ)^20*(q:ℝ)^2) ≤ 24*Real.log ((q:ℝ)+2) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]; norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ)≤q+2),Real.log_le_log (by positivity : (0:ℝ)<q) (by linarith : (q:ℝ)≤q+2),Real.log_nonneg (by linarith : (1:ℝ)≤q+2)]
  refine (le_trans ?_ hh).trans (mul_le_mul_of_nonneg_right hMlog (by positivity))
  rw [(hasSum_turanMangoldtTerm χ (by norm_num : (0:ℝ)<1/1024) 0 m).tsum_eq]
  simp only [Complex.ofReal_zero,zero_mul,add_zero,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [neg_mul,neg_add_eq_sub,norm_sub_rev]
  rfl

/-- Horizontal distance to one controls the modulus of a scaled reciprocal
throughout the critical strip; this exponential bound admits direct use of a
zero-density estimate. -/
theorem norm_leastPrimeZeroRatio_le_exp {z : ℂ} (h₀ : 0≤z.re) (h₁ : z.re≤1) :
    ‖leastPrimeZeroRatio z‖ ≤ Real.exp (-(1-z.re)) := by
  let d := 1-z.re
  have hd : 0≤d := sub_nonneg.mpr h₁
  have hd' : d≤1 := by dsimp [d]; linarith
  have he : Real.exp d ≤ 1+2*d := by
    have h : Real.exp ((1-d)*0+d*1) ≤ (1-d)*Real.exp 0+d*Real.exp 1 :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) hd (by ring)
    simp only [mul_zero,zero_add,mul_one,Real.exp_zero] at h
    nlinarith [mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hd]
  have hsep : 1/1024+d ≤ ‖leastPrimeMomentCenter-z‖ := by
    have h := Complex.re_le_norm (leastPrimeMomentCenter-z)
    rw [Complex.sub_re,show leastPrimeMomentCenter.re=1+1/1024 by norm_num [leastPrimeMomentCenter]] at h; dsimp [d]; linarith
  have hp : 0<‖leastPrimeMomentCenter-z‖ := by linarith
  change ‖(1/1024:ℂ)/(leastPrimeMomentCenter-z)‖ ≤ Real.exp (-d)
  rw [norm_div,show ‖(1/1024:ℂ)‖=(1/1024:ℝ) by norm_num,Real.exp_neg,div_le_iff₀ hp,inv_mul_eq_div,le_div_iff₀ (Real.exp_pos _)]
  linarith

private theorem pole_removed_signed_coeff (m : ℕ) :
    signedTaylorCoeff (logDeriv zetaOne) leastPrimeMomentCenter m =
      (1024:ℂ)^(m+1)+signedTaylorCoeff (logDeriv riemannZeta) leastPrimeMomentCenter m := by
  let c := leastPrimeMomentCenter
  let lin : ℂ → ℂ := fun w => w-1
  have hc : 1<c.re := by norm_num [c,leastPrimeMomentCenter]
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const continuous_re
  have hmem : {w : ℂ | 1<w.re}∈𝓝 c := hopen.mem_nhds hc
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
  norm_num [c,leastPrimeMomentCenter]

/-- The unique primitive principal moment is exponentially close to its pole
contribution one. Its other singularities are separated from the fixed center. -/
theorem principal_moment_one_bound :
    ∃ E r : ℝ, 0<E ∧ 0<r ∧ r<1 ∧ ∀ m : ℕ,
      ‖(∑' n, turanMangoldtTerm (1:DirichletCharacter ℂ 1) (1/1024) 0 m n)-1‖ ≤ E*r^m := by
  let c := leastPrimeMomentCenter
  let Z := leastPrimeMomentZeros zetaOne
  have hf : AnalyticOnNhd ℂ zetaOne (closedBall c (3/4)) :=
    (differentiable_zetaOne.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hn {z : ℂ} (hz : 1≤z.re) : zetaOne z≠0 := by
    by_cases he : z=1
    · simp [he]
    · rw [zetaOne_eq_sub_one_mul he]
      exact mul_ne_zero (sub_ne_zero.mpr he) (riemannZeta_ne_zero_of_one_le_re hz)
  have hc : c.re=1+1/1024 := by norm_num [c,leastPrimeMomentCenter]
  have hcn : zetaOne c≠0 := hn (by rw [hc]; norm_num)
  obtain ⟨w,_,hmax⟩ := (isCompact_closedBall c (3/4)).exists_isMaxOn
    ⟨c,mem_closedBall_self (by norm_num)⟩ (differentiable_zetaOne.continuous.div_const (zetaOne c)).norm.continuousOn
  let M := 1+‖zetaOne w/zetaOne c‖
  have hM : 1≤M := by dsimp [M]; linarith [norm_nonneg (zetaOne w/zetaOne c)]
  have hg (z : ℂ) (hz : z∈Z) : ‖leastPrimeZeroRatio z‖<1 := by
    obtain ⟨hb,hz'⟩ := (mem_leastPrimeMomentZeros hf hcn).mp hz
    have hx : z.re<1 := lt_of_not_ge (fun h => hn h hz')
    have hd : ‖z-c‖≤3/8 := by simpa [c,mem_closedBall,dist_eq_norm] using hb
    have hre := (Complex.abs_re_le_norm (z-c)).trans hd
    rw [Complex.sub_re,hc] at hre
    exact (norm_leastPrimeZeroRatio_le_exp (by linarith [(abs_le.mp hre).1]) hx.le).trans_lt (Real.exp_lt_one_iff.mpr (by linarith))
  let S := insert (1/256:ℝ) (Z.image (fun z => ‖leastPrimeZeroRatio z‖))
  have hs : S.Nonempty := ⟨_,mem_insert_self ..⟩
  let r := S.max' hs
  have hr : 1/256≤r := le_max' _ _ (mem_insert_self ..)
  have hr' : r<1 := by
    have h := S.max'_mem hs
    rcases mem_insert.mp h with he | he
    · rw [show r=1/256 from he]; norm_num
    · obtain ⟨z,hz,he⟩ := mem_image.mp he; change r < 1; rw [show r=‖leastPrimeZeroRatio z‖ from he.symm]; exact hg z hz
  have hzle (z : ℂ) (hz : z∈Z) : ‖leastPrimeZeroRatio z‖≤r := le_max' S _ (mem_insert_of_mem (mem_image_of_mem (fun z => ‖leastPrimeZeroRatio z‖) hz))
  let A := ∑ z ∈ Z,(analyticOrderNatAt zetaOne z:ℝ)
  have hA : 0≤A := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨1+Real.log M+A,r,by have := Real.log_nonneg hM; linarith,by linarith,hr',fun m => ?_⟩
  let v := (1/1024:ℂ)^(m+1)
  let F := ∑ z ∈ Z,(analyticOrderNatAt zetaOne z:ℂ)*leastPrimeZeroRatio z^(m+1)
  have hF : ‖F‖≤A*r^m := by
    calc
      _ ≤ ∑ z ∈ Z,‖(analyticOrderNatAt zetaOne z:ℂ)*leastPrimeZeroRatio z^(m+1)‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ Z,(analyticOrderNatAt zetaOne z:ℝ)*r^m := by
        apply sum_le_sum; intro z hz
        rw [norm_mul,Complex.norm_natCast,norm_pow]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg _) (hzle z hz) _).trans (pow_le_pow_of_le_one (by linarith) hr'.le (by omega))
      _ = _ := (sum_mul ..).symm
  have hE := moment_disk_expansion hM hf hcn (fun z hz => (hmax (sphere_subset_closedBall hz)).trans (by dsimp [M]; linarith)) m
  change ‖v*signedTaylorCoeff (logDeriv zetaOne) c m-F‖ ≤ _ at hE
  have ht := (hasSum_turanMangoldtTerm (1:DirichletCharacter ℂ 1) (by norm_num : (0:ℝ)<1/1024) 0 m).tsum_eq
  simp only [DirichletCharacter.LFunction_modOne_eq,Complex.ofReal_zero,zero_mul,add_zero,Complex.ofReal_add,Complex.ofReal_one,
    Complex.ofReal_div,Complex.ofReal_ofNat] at ht
  have hv : v*(1024:ℂ)^(m+1)=1 := by dsimp only [v]; rw [←mul_pow]; norm_num
  have heq : (∑' n,turanMangoldtTerm (1:DirichletCharacter ℂ 1) (1/1024) 0 m n)-1 =
      -(v*signedTaylorCoeff (logDeriv zetaOne) c m) := by
    rw [ht,pole_removed_signed_coeff]
    change -v*signedTaylorCoeff (logDeriv riemannZeta) leastPrimeMomentCenter m-1= -(v*_)
    rw [mul_add,hv]; ring
  rw [heq,norm_neg]
  have htotal := norm_add_le (v*signedTaylorCoeff (logDeriv zetaOne) c m-F) F
  rw [sub_add_cancel] at htotal
  refine htotal.trans ((add_le_add hE hF).trans ?_)
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hr m) (Real.log_nonneg hM)
  nlinarith [pow_nonneg (by linarith : 0≤r) m]

end AnalyticNumberTheory.PrimeDistribution
