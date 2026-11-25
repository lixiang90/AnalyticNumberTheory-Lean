import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Gaussian-damped ratios of real archimedean gamma factors

The constants depend only on the two real parts. The imaginary parts can
be arbitrary, including zero. Moving the real part by `c` costs exactly
`(1+|t|)^(c/2)`.
-/

open Complex Real Set
namespace AnalyticNumberTheory.AnalyticTools

/-- The real archimedean gamma factor is holomorphic in the right half-plane. -/
theorem differentiableAt_GammaReal {z : ℂ} (hz : 0<z.re) : DifferentiableAt ℂ Complex.Gammaℝ z := by
  have h := (Complex.differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz))
  change DifferentiableAt ℂ (fun u => (Complex.Gammaℝ u)⁻¹⁻¹) z at h
  simpa only [inv_inv] using h

private theorem comparable_rpow {p q W : ℝ} (hp : 0<p) (hq : 0<q) (hW : 0<W)
    (h₁ : p≤q*W) (h₂ : q≤p*W) (e : ℝ) : p^e≤q^e*W^|e| := by
  rcases le_total 0 e with he|he
  · rw [abs_of_nonneg he,←Real.mul_rpow hq.le hW.le]
    exact Real.rpow_le_rpow hp.le h₁ he
  · rw [abs_of_nonpos he,Real.rpow_neg hW.le,←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hW _),
      ←Real.mul_rpow hp.le hW.le]
    exact Real.rpow_le_rpow_of_nonpos hq h₂ he

private noncomputable def gammaProfile (σ t : ℝ) :=
  Real.exp (-(π/4)*|t|)*(1+|t|)^(σ/2-1/2)

/-- Two-sided vertical norm estimates for the real gamma factor on a fixed
positive vertical line, including its bounded part. -/
theorem norm_GammaReal_vertical_profile {σ : ℝ} (hσ : 0<σ) :
    ∃ b B : ℝ,0<b ∧ 0<B ∧ ∀ t : ℝ,
      b*(Real.exp (-(π/4)*|t|)*(1+|t|)^(σ/2-1/2))≤‖Complex.Gammaℝ ((σ:ℂ)+t*I)‖ ∧
      ‖Complex.Gammaℝ ((σ:ℂ)+t*I)‖≤B*(Real.exp (-(π/4)*|t|)*(1+|t|)^(σ/2-1/2)) := by
  obtain ⟨c,C,hc,hcC,H⟩ := Gamma.norm_complex_gamma_strip_bounds (σ/2) (σ/2)
  let e := σ/2-1/2
  let P := π^(-σ/2)
  let V := (4:ℝ)^|e|
  have hP : 0<P := Real.rpow_pos_of_pos Real.pi_pos _
  have hV : 0<V := Real.rpow_pos_of_pos (by norm_num) _
  let z (t : ℝ) := (σ:ℂ)+t*I
  have hz (t) : 0<(z t).re := by simpa [z] using hσ
  let f (t : ℝ) := ‖Complex.Gammaℝ (z t)‖/gammaProfile σ t
  have hE (t) : 0<gammaProfile σ t := by dsimp [gammaProfile]; positivity
  have hf (t) : 0<f t := div_pos (norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (hz t))) (hE t)
  have hcZ : Continuous (fun t => Complex.Gammaℝ (z t)) := continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_GammaReal (hz t)).continuousAt.comp (by dsimp [z]; fun_prop)
  have hcE : Continuous (gammaProfile σ) := by
    unfold gammaProfile
    apply Continuous.mul (by fun_prop)
    exact (continuous_const.add continuous_abs).rpow_const (fun t => Or.inl (show (1:ℝ)+|t|≠0 by positivity))
  have hcf : Continuous f := hcZ.norm.div hcE (fun t => (hE t).ne')
  obtain ⟨u,_,hu⟩ := isCompact_Icc.exists_isMinOn (f:=f) (nonempty_Icc.mpr (by norm_num : (-2:ℝ)≤2)) hcf.continuousOn
  obtain ⟨v,_,hv⟩ := isCompact_Icc.exists_isMaxOn (f:=f) (nonempty_Icc.mpr (by norm_num : (-2:ℝ)≤2)) hcf.continuousOn
  refine ⟨min (f u) (P*c/V),max (f v) (P*C*V),lt_min (hf _) (by positivity),lt_of_lt_of_le (hf _) (le_max_left ..),?_⟩
  intro t
  change min _ _*gammaProfile σ t≤_ ∧ _≤max _ _*gammaProfile σ t
  by_cases ht : 2≤|t|
  · have hp : 0 < |t|/2 := by linarith
    have hq : 0<1+|t| := by positivity
    have h₁ : |t|/2≤(1+|t|)*4 := by linarith
    have h₂ : 1+|t|≤(|t|/2)*4 := by linarith
    have hpow := comparable_rpow hp hq (by norm_num : (0:ℝ)<4) h₁ h₂ e
    have hpow' := comparable_rpow hq hp (by norm_num : (0:ℝ)<4) h₂ h₁ e
    have hg := H (t:=t/2) ⟨le_rfl,le_rfl⟩ (by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),show -(π/2)*(|t|/2)=-(π/4)*|t| by ring] at hg
    let G := Complex.Gamma (((σ/2:ℝ):ℂ)+(t/2:ℝ)*I)
    let E := Real.exp (-(π/4)*|t|)
    change c*E*(|t|/2)^e≤‖G‖ ∧ ‖G‖≤C*E*(|t|/2)^e at hg
    have heq : ‖Complex.Gammaℝ (z t)‖=P*‖G‖ := by
      unfold Complex.Gammaℝ
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have h1 : (-z t/2).re = -σ/2 := by simp [z]
      rw [h1,show z t/2=((σ/2:ℝ):ℂ)+(t/2:ℝ)*I by dsimp [z]; push_cast; ring]
    rw [heq]
    change min _ _*(E*(1+|t|)^e)≤_ ∧ _≤max _ _*(E*(1+|t|)^e)
    constructor
    · apply (mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity)).trans
      calc _ = P*(c*E)*((1+|t|)^e/V) := by ring
           _ ≤ P*(c*E)*((|t|/2)^e) := mul_le_mul_of_nonneg_left ((div_le_iff₀ hV).mpr hpow') (by positivity)
           _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg.1 hP.le
    · apply (mul_le_mul_of_nonneg_left hg.2 hP.le).trans
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
      calc _ = P*(C*E)*(|t|/2)^e := by ring
           _ ≤ P*(C*E)*((1+|t|)^e*V) := mul_le_mul_of_nonneg_left hpow (by have := hc.trans_le hcC; positivity)
           _ = _ := by ring
  · have hm : t∈Icc (-2:ℝ) 2 := abs_le.mp (le_of_not_ge ht)
    exact ⟨(le_div_iff₀ (hE _)).mp ((min_le_left ..).trans (hu hm)),
      (div_le_iff₀ (hE _)).mp ((hv hm).trans (le_max_left ..))⟩

/-- The vertical Gaussian kernel obtained by displacing a gamma factor
from `σ` to `σ+c`. The real shift may be negative. -/
theorem norm_GammaReal_gaussian_ratio {σ c : ℝ} (hσ : 0<σ) (hsc : 0<σ+c) (hc : c≠0) :
    ∃ C : ℝ,0<C ∧ ∀ t v : ℝ,
      ‖Complex.Gammaℝ (((σ+c:ℝ):ℂ)+(t+v:ℝ)*I)/Complex.Gammaℝ ((σ:ℂ)+t*I)*
        Complex.exp (((c:ℂ)+v*I)^2)/((c:ℂ)+v*I)‖≤
        C*(1+|t|)^(c/2)*Real.exp (-v^2/2) := by
  obtain ⟨b,_,hb,_,Hd⟩ := norm_GammaReal_vertical_profile hσ
  obtain ⟨_,B,_,hB,Hn⟩ := norm_GammaReal_vertical_profile hsc
  let e := (σ+c)/2-1/2
  let A := |e|+π/4
  have hca := abs_pos.mpr hc
  refine ⟨B/b*Real.exp (c^2+A^2/2)/|c|,by positivity,?_⟩
  intro t v
  let U := 1+|t|
  let V := 1+|v|
  let W := 1+|t+v|
  have hu : 0<U := by dsimp [U]; positivity
  have hv : 0<V := by dsimp [V]; positivity
  have hw : 0<W := by dsimp [W]; positivity
  have pl := comparable_rpow hw hu hv
    (show W≤U*V by dsimp [W,U,V]; nlinarith [abs_add_le t v,mul_nonneg (abs_nonneg t) (abs_nonneg v)])
    (show U≤W*V by have ha := abs_add_le (t+v) (-v); rw [add_neg_cancel_right,abs_neg] at ha; dsimp [W,U,V]; nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v)]) e
  have hlog : Real.log V≤|v| := by simpa [V] using Real.log_le_sub_one_of_pos hv
  have hVexp : V^|e|≤Real.exp (|e| * |v|) := by
    rw [Real.rpow_def_of_pos hv,Real.exp_le_exp,mul_comm]; gcongr
  have hphase : Real.exp (-(π/4)*|t+v|)≤Real.exp (-(π/4)*|t|)*Real.exp (π/4*|v|) := by
    rw [←Real.exp_add,Real.exp_le_exp]
    have ha := abs_add_le (t+v) (-v); rw [add_neg_cancel_right,abs_neg] at ha
    nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ha)]
  let G := ‖Complex.Gammaℝ ((σ:ℂ)+t*I)‖
  have hG : 0<G := norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hσ))
  have hn := (Hn (t+v)).2
  have hd := (Hd t).1
  have hratio : ‖Complex.Gammaℝ (((σ+c:ℝ):ℂ)+(t+v:ℝ)*I)‖/G≤B/b*U^(c/2)*Real.exp (A*|v|) := by
    apply (div_le_iff₀ hG).mpr
    apply hn.trans
    apply le_trans _ (mul_le_mul_of_nonneg_left hd (by positivity : 0≤B/b*U^(c/2)*Real.exp (A*|v|)))
    change B*(Real.exp (-(π/4)*|t+v|)*W^e)≤_
    have pp := pl.trans (mul_le_mul_of_nonneg_left hVexp (by positivity))
    apply (mul_le_mul_of_nonneg_left (mul_le_mul hphase pp (by positivity) (by positivity)) hB.le).trans_eq
    rw [show e=(σ/2-1/2)+c/2 by dsimp [e]; ring,Real.rpow_add hu,
      show A*|v|=|e| * |v|+π/4*|v| by dsimp [A]; ring,Real.exp_add]
    change _=B/b*U^(c/2)*_*(b*(Real.exp (-(π/4)*|t|)*U^(σ/2-1/2)))
    dsimp [e]; field_simp; ring
  let w := (c:ℂ)+v*I
  have hcw : |c|≤‖w‖ := by simpa [w] using Complex.abs_re_le_norm w
  have he : (w^2).re=c^2-v^2 := by simp [w,pow_two]
  rw [norm_div,norm_mul,norm_div,Complex.norm_exp]
  change _/G*Real.exp (w^2).re/‖w‖≤_
  rw [he]
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le) (norm_nonneg _)).trans
  apply (div_le_div_of_nonneg_left (by positivity) hca hcw).trans
  have hexp : Real.exp (A*|v|)*Real.exp (c^2-v^2)≤Real.exp (c^2+A^2/2)*Real.exp (-v^2/2) := by
    rw [←Real.exp_add,←Real.exp_add,Real.exp_le_exp]; nlinarith [sq_nonneg (A-|v|),sq_abs v]
  calc _ = (B/b*U^(c/2)/|c|)*(Real.exp (A*|v|)*Real.exp (c^2-v^2)) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hexp (by positivity : 0≤B/b*U^(c/2)/|c|)).trans_eq (by ring)

end AnalyticNumberTheory.AnalyticTools
