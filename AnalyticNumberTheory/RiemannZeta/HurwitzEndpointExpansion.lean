import AnalyticNumberTheory.RiemannZeta.HurwitzFourierExpansion
import AnalyticNumberTheory.AnalyticTools.Summation.MonotoneIntegralWeights

/-!
# The first endpoint term in a nonstationary Hurwitz Fourier integral

Retaining the endpoint term leaves inverse squares and cubes of the
distance from the stationary frequency. They can be summed without
taking absolute values of the leading reciprocal.
-/
noncomputable section
open Real Complex Filter Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- Endpoint contribution after a single oscillatory integration by parts. -/
def hurwitzEndpoint (s : ℂ) (ω u : ℝ) : ℂ :=
  -I*(u:ℂ)/((ω*u-s.im:ℝ):ℂ)*hurwitzMode s ω u

theorem hurwitzMode_deriv (s : ℂ) (ω : ℝ) {u : ℝ} (hu : 0<u) :
    HasDerivAt (hurwitzMode s ω) ((I*ω-s/(u:ℂ))*hurwitzMode s ω u) u := by
  have hc : HasDerivAt (fun v : ℝ => (v:ℂ)^(-s)) ((-s)*(u:ℂ)^(-s-1)) u := by
    simpa using cpow_shift_hasDerivAt (a:=0) (by simpa using hu) (-s)
  have he : HasDerivAt (fun v : ℝ => Complex.exp ((ω*v:ℝ)*I)) (Complex.exp ((ω*u:ℝ)*I)*((ω:ℂ)*I)) u := by
    simpa using ((((hasDerivAt_id u).const_mul ω).ofReal_comp.mul_const I).cexp)
  convert he.mul hc using 1
  · rfl
  · dsimp only [hurwitzMode];rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hu.ne'),Complex.cpow_one];ring

theorem hurwitzEndpoint_deriv {s : ℂ} {ω u : ℝ} (hu : 0<u) (hD : ω*u-s.im≠0) :
    HasDerivAt (hurwitzEndpoint s ω) (hurwitzMode s ω u+
      I*(((s.re/(ω*u-s.im)+s.im/(ω*u-s.im)^2:ℝ):ℂ)*hurwitzMode s ω u)) u := by
  have hD' : ((ω*u-s.im:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD
  have hz := (((hasDerivAt_id u).const_mul ω).sub_const s.im).ofReal_comp
  have h := ((((hasDerivAt_id u).ofReal_comp.const_mul (-I)).div hz hD').mul (hurwitzMode_deriv s ω hu))
  convert h using 1
  · rfl
  · dsimp only [id_eq,Pi.div_apply];push_cast
    have hd' : (ω:ℂ)*(u:ℂ)-(s.im:ℂ)≠0 := by simpa using hD'
    have huc : (u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hu.ne'
    generalize hurwitzMode s ω u=F
    conv_rhs => rw [show s=(s.re:ℂ)+s.im*I from (Complex.re_add_im s).symm]
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,zero_add,Complex.ofReal_re]
    field_simp [hd',huc]
    ring_nf <;> simp [Complex.I_sq,Complex.I_pow_three] <;> try ring

theorem hurwitzMode_sub_endpoint_eq {s : ℂ} {ω a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hD : ∀ u∈Icc a b,ω*u-s.im≠0) :
    (∫ u in a..b,hurwitzMode s ω u)-(hurwitzEndpoint s ω b-hurwitzEndpoint s ω a) =
      -I*∫ u in a..b,((s.re/(ω*u-s.im)+s.im/(ω*u-s.im)^2:ℝ):ℂ)*hurwitzMode s ω u := by
  have hf : ContinuousOn (hurwitzMode s ω) (Icc a b) := fun u hu =>
    (hurwitzMode_deriv _ _ (ha.trans_le hu.1)).continuousAt.continuousWithinAt
  have hDcont : ContinuousOn (fun u : ℝ => ω*u-s.im) (Icc a b) := by fun_prop
  have hw : ContinuousOn (fun u : ℝ => ((s.re/(ω*u-s.im)+s.im/(ω*u-s.im)^2:ℝ):ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn ((continuousOn_const.div hDcont hD).add
      (continuousOn_const.div (hDcont.pow 2) (fun u hu => pow_ne_zero 2 (hD u hu))))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=hurwitzEndpoint s ω)
    (fun u hu => hurwitzEndpoint_deriv (ha.trans_le ((uIcc_of_le hab) ▸ hu).1) (hD u ((uIcc_of_le hab) ▸ hu)))
    ((hf.add (continuousOn_const.mul (hw.mul hf))).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable_of_Icc hab) (by exact (continuousOn_const.mul (hw.mul hf)).intervalIntegrable_of_Icc hab)] at h
  rw [intervalIntegral.integral_const_mul] at h
  linear_combination h

/-- Endpoint accuracy with simultaneous lower bounds for the phase derivative
and its numerator. -/
theorem hurwitzMode_endpoint_error {s : ℂ} {ω a b d g : ℝ} (ha : 0<a) (hab : a≤b)
    (hσ : 0≤s.re) (ht : 0≤s.im) (hω : 0≤ω) (hd : 0<d) (hg : 0<g)
    (hD : ∀ u∈Icc a b,d≤|ω*u-s.im|) (hG : ∀ u∈Icc a b,g≤|ω-s.im/u|)
    (hsign : (∀ u∈Icc a b,ω*u-s.im≤0) ∨ (∀ u∈Icc a b,0≤ω*u-s.im)) :
    ‖(∫ u in a..b,hurwitzMode s ω u)-(hurwitzEndpoint s ω b-hurwitzEndpoint s ω a)‖ ≤
      3*(s.re/d+s.im/d^2)*(a^(-s.re)*(4/g)) := by
  let D (u : ℝ) := ω*u-s.im
  let F := hurwitzMode s ω
  let H := a^(-s.re)*(4/g)
  have hne (u : ℝ) (hu : u∈Icc a b) : D u≠0 := abs_pos.mp (hd.trans_le (hD u hu))
  have hDc : ContinuousOn D (Icc a b) := by dsimp [D]; fun_prop
  have hdd (u : ℝ) : HasDerivAt D ω u := by simpa [D] using (((hasDerivAt_id u).const_mul ω).sub_const s.im)
  have hfc (u : ℝ) (hu : u∈Icc a b) : ContinuousAt F u := (hurwitzMode_deriv _ _ (ha.trans_le hu.1)).continuousAt
  have hfm : StronglyMeasurable F := by change StronglyMeasurable (fun u : ℝ => Complex.exp ((ω*u:ℝ)*I)*(u:ℂ)^(-s));fun_prop
  have hF (u : ℝ) (hu : u∈Icc a b) : ‖∫ v in a..u,F v‖≤H :=
    hurwitzMode_first ha hu.1 hσ ht hg (fun v hv => hG v ((Icc_subset_Icc_right hu.2) hv))
  have H₁ := norm_integral_monotone_weight hab F (fun u => (D u)⁻¹) (fun u => -ω/(D u)^2)
    hfc hfm (fun u hu => (hdd u).inv (hne u hu))
    (continuousOn_const.div (hDc.pow 2) (fun u hu => pow_ne_zero 2 (hne u hu)))
    (.inl (fun u hu => div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hω) (sq_nonneg _)))
    (A:=1/d) (fun u hu => by rw [abs_inv,one_div];exact inv_anti₀ hd (hD u hu)) hF
  have hd₂ (u : ℝ) (hu : u∈Icc a b) : HasDerivAt (fun v => ((D v)^2)⁻¹)
      (-(2*D u*ω)/((D u)^2)^2) u := by
    convert ((hdd u).pow 2).inv (pow_ne_zero 2 (hne u hu)) using 1 <;> simp <;> ring
  have hs₂ : (∀ u∈Icc a b,-(2*D u*ω)/((D u)^2)^2≤0) ∨ (∀ u∈Icc a b,0≤ -(2*D u*ω)/((D u)^2)^2) := by
    rcases hsign with h|h
    · right;intro u hu
      apply div_nonneg _ (sq_nonneg _)
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (h u hu)) hω)
    · left;intro u hu
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) (h u hu)) hω)
  have H₂ := norm_integral_monotone_weight hab F (fun u => ((D u)^2)⁻¹) (fun u => -(2*D u*ω)/((D u)^2)^2)
    hfc hfm hd₂ (((continuousOn_const.mul hDc).mul continuousOn_const).neg.div ((hDc.pow 2).pow 2)
      (fun u hu => pow_ne_zero 2 (pow_ne_zero 2 (hne u hu)))) hs₂
    (A:=1/d^2) (fun u hu => by rw [abs_inv,abs_pow,one_div]; exact inv_anti₀ (sq_pos_of_pos hd) (pow_le_pow_left₀ hd.le (hD u hu) 2)) hF
  have hi₁ : IntervalIntegrable (fun u => (((D u)⁻¹:ℝ):ℂ)*F u) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn (hDc.inv₀ hne)).mul (fun u hu => (hfc u hu).continuousWithinAt)).intervalIntegrable_of_Icc hab
  have hi₂ : IntervalIntegrable (fun u => ((((D u)^2)⁻¹:ℝ):ℂ)*F u) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn ((hDc.pow 2).inv₀ (fun u hu => pow_ne_zero 2 (hne u hu)))).mul
      (fun u hu => (hfc u hu).continuousWithinAt)).intervalIntegrable_of_Icc hab
  rw [hurwitzMode_sub_endpoint_eq ha hab hne,norm_mul,norm_neg,Complex.norm_I,one_mul]
  change ‖∫ u in a..b,((s.re/D u+s.im/(D u)^2:ℝ):ℂ)*F u‖≤_
  simp_rw [div_eq_mul_inv,Complex.ofReal_add,Complex.ofReal_mul,add_mul,mul_assoc]
  rw [intervalIntegral.integral_add (hi₁.const_mul _) (hi₂.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hσ,abs_of_nonneg ht]
  apply (add_le_add (mul_le_mul_of_nonneg_left H₁ hσ) (mul_le_mul_of_nonneg_left H₂ ht)).trans_eq
  dsimp [H];ring

end AnalyticNumberTheory.RiemannZeta
