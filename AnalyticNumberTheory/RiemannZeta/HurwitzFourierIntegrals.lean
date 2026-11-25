import AnalyticNumberTheory.AnalyticTools.OscillatoryGamma
import AnalyticNumberTheory.AnalyticTools.Summation.WeightedIntegrals
import AnalyticNumberTheory.ExponentialSums.VanDerCorput
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Oscillatory integrals for the sharp Hurwitz functional equation

The phase is linear minus a logarithm. Far from its stationary point the
first derivative test applies; near it the second derivative test controls
the possible mode at the endpoint.
-/
noncomputable section
open Real Complex Filter Set MeasureTheory
open scoped Interval Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

/-- Fourier mode of the Dirichlet monomial on the positive half-line. -/
def hurwitzMode (s : ℂ) (ω u : ℝ) : ℂ := Complex.exp ((ω*u:ℝ)*I)*(u:ℂ)^(-s)

private def angle (t ω u : ℝ) := ω*u-t*Real.log u
private def wave (t ω u : ℝ) := Complex.exp ((angle t ω u:ℂ)*I)

theorem hurwitzMode_eq_gamma (s : ℂ) (ω u : ℝ) :
    hurwitzMode s ω u = gammaLaplaceKernel (1-s) (-(ω:ℂ)*I) u := by
  dsimp [hurwitzMode,gammaLaplaceKernel]; push_cast; congr 1
  · congr 1; ring
  · congr 1; ring

private theorem mode_polar (s : ℂ) (ω : ℝ) {u : ℝ} (hu : 0<u) :
    hurwitzMode s ω u = ((u^(-s.re):ℝ):ℂ)*wave s.im ω u := by
  dsimp [hurwitzMode,wave,angle]
  rw [Real.rpow_def_of_pos hu,Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),←Complex.ofReal_log hu.le,
    ←Complex.exp_add,←Complex.exp_add]
  congr 1; push_cast; nth_rw 1 [←Complex.re_add_im s]; ring

private theorem phase_deriv (t ω : ℝ) {u : ℝ} (hu : 0<u) :
    HasDerivAt (angle t ω) (ω-t/u) u := by
  convert ((hasDerivAt_id u).const_mul ω).sub ((Real.hasDerivAt_log hu.ne').const_mul t) using 1
  · rfl
  · simp [div_eq_mul_inv]

private theorem phase_deriv₂ (t ω : ℝ) {u : ℝ} (hu : 0<u) :
    HasDerivAt (fun v : ℝ => ω-t/v) (t/u^2) u := by
  convert (hasDerivAt_const u ω).sub ((hasDerivAt_const u t).div (hasDerivAt_id u) hu.ne') using 1
  · rfl
  · dsimp; ring

private theorem phase_second_cont (t : ℝ) {a b : ℝ} (ha : 0<a) :
    ContinuousOn (fun u : ℝ => t/u^2) (Icc a b) :=
  continuousOn_const.div (continuousOn_id.pow 2) fun _ hu => (sq_pos_of_pos (ha.trans_le hu.1)).ne'

private theorem wave_first {t ω a b m : ℝ} (ha : 0<a) (hab : a≤b) (ht : 0≤t)
    (hm : 0<m) (hg : ∀ u∈Icc a b,m≤|ω-t/u|) :
    ‖∫ u in a..b,wave t ω u‖ ≤ 4/m :=
  vanDerCorput_integral_first_deriv hab hm
    (fun _ hu => phase_deriv _ _ (ha.trans_le hu.1))
    (fun _ hu => phase_deriv₂ _ _ (ha.trans_le hu.1)) (phase_second_cont t ha)
    (.inl (fun _ _ => div_nonneg ht (sq_nonneg _))) hg

private theorem wave_second {t ω a b : ℝ} (ha : 0<a) (hab : a≤b) (ht : 0<t) :
    ‖∫ u in a..b,wave t ω u‖ ≤ 8*b/Real.sqrt t := by
  have hb := ha.trans_le hab
  apply (vanDerCorput_integral_second_deriv hab (div_pos ht (sq_pos_of_pos hb))
    (fun _ hu => phase_deriv t ω (ha.trans_le hu.1))
    (fun _ hu => phase_deriv₂ t ω (ha.trans_le hu.1)) (phase_second_cont t ha)
    (fun u hu => by rw [abs_of_nonneg (div_nonneg ht.le (sq_nonneg _))]
                    exact div_le_div_of_nonneg_left ht.le (sq_pos_of_pos (ha.trans_le hu.1))
                      ((sq_le_sq₀ (ha.trans_le hu.1).le hb.le).mpr hu.2))).trans_eq
  rw [Real.sqrt_div ht.le,Real.sqrt_sq hb.le,div_div_eq_mul_div]

private theorem weighted_mode {s : ℂ} {ω a b : ℝ} (ha : 0<a) (hab : a≤b) (hσ : 0≤s.re)
    (H : ℝ → ℝ) (hH : ContinuousOn H (Icc a b)) (hf : ∀ u∈Icc a b,‖∫ v in a..u,wave s.im ω v‖≤H u) :
    ‖∫ u in a..b,hurwitzMode s ω u‖ ≤
      b^(-s.re)*H b + ∫ u in a..b,(s.re*u^(-s.re-1))*H u := by
  have hcon : ∀ u∈Icc a b,ContinuousAt (wave s.im ω) u := by
    intro u hu; exact (((Complex.continuous_ofReal.continuousAt.comp (phase_deriv s.im ω (ha.trans_le hu.1)).continuousAt).mul continuousAt_const).cexp)
  have hw (u : ℝ) (hu : u∈Icc a b) : HasDerivAt (fun u : ℝ => u^(-s.re)) ((-s.re)*u^(-s.re-1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl (ha.trans_le hu.1).ne')
  have hw' : ContinuousOn (fun u : ℝ => (-s.re)*u^(-s.re-1)) (Icc a b) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun _ hu => Or.inl (ha.trans_le hu.1).ne')
  rw [intervalIntegral.integral_congr (fun u hu => mode_polar s ω (ha.trans_le ((uIcc_of_le hab) ▸ hu).1))]
  apply (norm_integral_decreasing_weight_variable H hab (wave s.im ω) _ _ hcon
    (by unfold wave angle; fun_prop) hw hw' (fun u hu => mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (ha.trans_le hu.1).le _))
    (Real.rpow_nonneg (ha.trans_le hab).le _) hH hf).trans_eq
  simp

private theorem weighted_mode_const {s : ℂ} {ω a b H : ℝ} (ha : 0<a) (hab : a≤b)
    (hσ : 0≤s.re) (hf : ∀ u∈Icc a b,‖∫ v in a..u,wave s.im ω v‖≤H) :
    ‖∫ u in a..b,hurwitzMode s ω u‖ ≤ a^(-s.re)*H := by
  apply (weighted_mode ha hab hσ (fun _ => H) continuousOn_const hf).trans_eq
  rw [intervalIntegral.integral_mul_const]
  have he : (∫ u in a..b,s.re*u^(-s.re-1))=a^(-s.re)-b^(-s.re) := by
    have hw (u : ℝ) (hu : u ∈ Icc a b) : HasDerivAt (fun v : ℝ => -(v^(-s.re))) (s.re*u^(-s.re-1)) u := by
      convert (Real.hasDerivAt_rpow_const (p:=-s.re) (Or.inl (ha.trans_le hu.1).ne')).neg using 1 <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun v : ℝ => -(v^(-s.re)))
      (fun u hu => hw u ((uIcc_of_le hab) ▸ hu)) ((continuousOn_const.mul
        (continuousOn_id.rpow_const fun u (hu : u∈Icc a b) => Or.inl (ha.trans_le hu.1).ne')).intervalIntegrable_of_Icc hab)]
    ring
  rw [he]; ring

/-- A finite tail interval whose phase derivative has a positive gap. -/
theorem hurwitzMode_first {s : ℂ} {ω a b m : ℝ} (ha : 0<a) (hab : a≤b)
    (hσ : 0≤s.re) (ht : 0≤s.im) (hm : 0<m) (hg : ∀ u∈Icc a b,m≤|ω-s.im/u|) :
    ‖∫ u in a..b,hurwitzMode s ω u‖ ≤ a^(-s.re)*(4/m) :=
  weighted_mode_const ha hab hσ fun u hu =>
    wave_first ha hu.1 ht hm (fun v hv => hg v ((Icc_subset_Icc_right hu.2) hv))

/-- The stationary range is bounded uniformly in the linear frequency. -/
theorem hurwitzMode_second {s : ℂ} {ω a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hσ : 0≤s.re) (ht : 0<s.im) :
    ‖∫ u in a..b,hurwitzMode s ω u‖ ≤ a^(-s.re)*(8*b/Real.sqrt s.im) := by
  apply weighted_mode_const ha hab hσ
  intro u hu
  exact (wave_second ha hu.1 ht).trans (div_le_div_of_nonneg_right (by linarith [hu.2]) (Real.sqrt_nonneg _))

theorem norm_hurwitzMode (s : ℂ) (ω : ℝ) {u : ℝ} (hu : 0<u) :
    ‖hurwitzMode s ω u‖=u^(-s.re) := by
  rw [hurwitzMode,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos hu,Complex.neg_re]

theorem hurwitzMode_integrable_at_zero {s : ℂ} (hσ : s.re<1) (ω : ℝ) {b : ℝ} (hb : 0≤b) :
    IntervalIntegrable (hurwitzMode s ω) volume 0 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
  apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -s.re))).mono'
  · unfold hurwitzMode; fun_prop
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu => (norm_hurwitzMode s ω hu.1).le

/-- Up to the cutoff on the low-frequency side, the derivative gap is measured
in logarithmic coordinates. The inequality is uniform down to zero. -/
theorem hurwitzMode_head_first {s : ℂ} {ω x D : ℝ} (hx : 0<x) (hσ₀ : 0≤s.re)
    (hσ₁ : s.re<1) (ht : 0≤s.im) (hD : 0<D) (hgap : ∀ v : ℝ, 0<v → v≤x → D≤s.im-ω*v) :
    ‖∫ u in 0..x,hurwitzMode s ω u‖ ≤ 4*x^(1-s.re)/(D*(1-s.re)) := by
  have hpart (a : ℝ) (ha : 0<a) (hax : a≤x) :
      ‖∫ u in a..x,hurwitzMode s ω u‖ ≤ 4*x^(1-s.re)/(D*(1-s.re)) := by
    let H (v : ℝ) := 4*v/D
    have hf (u : ℝ) (hu : u∈Icc a x) : ‖∫ v in a..u,wave s.im ω v‖ ≤ H u := by
      have hup := ha.trans_le hu.1
      apply (wave_first ha hu.1 ht (div_pos hD hup) (fun v hv => ?_)).trans_eq
      · dsimp [H]; rw [div_div_eq_mul_div]
      · have hvp := ha.trans_le hv.1
        have h := hgap v hvp (hv.2.trans hu.2)
        have hg : D/v≤s.im/v-ω := (div_le_iff₀ hvp).mpr (by rw [sub_mul,div_mul_cancel₀ _ hvp.ne']; linarith)
        exact ((div_le_div_of_nonneg_left hD.le hvp hv.2).trans hg).trans
          (by rw [←abs_sub_comm]; exact le_abs_self _)
    have h := weighted_mode ha hax hσ₀ H (by dsimp [H]; fun_prop) hf
    have hconst (u : ℝ) (hu : u∈Icc a x) : s.re*u^(-s.re-1)*H u=(4*s.re/D)*u^(-s.re) := by
      have hp := ha.trans_le hu.1
      have hh : u^(-s.re-1)*u=u^(-s.re) := by
        nth_rw 2 [←Real.rpow_one u]; rw [←Real.rpow_add hp]; congr 1; ring
      dsimp [H]; linear_combination (4*s.re/D)*hh
    rw [intervalIntegral.integral_congr (fun u hu => hconst u ((uIcc_of_le hax) ▸ hu)),
      intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith : -1 < -s.re))] at h
    have hnx : x^(-s.re)*x=x^(1-s.re) := by
      nth_rw 2 [←Real.rpow_one x]; rw [←Real.rpow_add hx]; congr 1; ring
    have hpos : 0<1-s.re := by linarith
    have hq : (x^(-s.re+1)-a^(-s.re+1))/(-s.re+1) ≤ x^(1-s.re)/(1-s.re) := by
      rw [show -s.re+1=1-s.re by ring]
      exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg ha.le _)) hpos.le
    apply h.trans
    dsimp only [H]
    apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left hq (by positivity : 0≤4*s.re/D))).trans_eq
    rw [show x^(-s.re)*(4*x/D)=4*(x^(-s.re)*x)/D by ring,hnx]
    field_simp; ring
  have hInt := hurwitzMode_integrable_at_zero hσ₁ ω hx.le
  have hcont := intervalIntegral.continuousOn_primitive_interval_left
    (show IntegrableOn (hurwitzMode s ω) (uIcc 0 x) from by
      rw [uIcc_of_le hx.le,integrableOn_Icc_iff_integrableOn_Ioc]; exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp hInt)
  have hfilt : 𝓝[>] (0:ℝ) ≤ 𝓝[uIcc 0 x] 0 := by
    apply nhdsWithin_le_of_mem
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hx)] with v (hv : 0<v) hvx
    rw [uIcc_of_le hx.le]; exact ⟨hv.le,hvx.le⟩
  apply le_of_tendsto (hcont 0 left_mem_uIcc |>.tendsto.norm.mono_left hfilt)
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hx)] with v (hv : 0<v) hvx
  exact hpart v hv hvx.le

end AnalyticNumberTheory.RiemannZeta
