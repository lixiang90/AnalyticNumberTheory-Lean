import AnalyticNumberTheory.RiemannZeta.Littlewood
import AnalyticNumberTheory.PrimeDistribution.HoheiselZeroSums
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem

/-!
# Improvement of the classical prime number theorem error

A growing lower bound for (1−β) log T over zeros up to height T, together
with log-free density, allows an arbitrary fixed coefficient in the
exponential error exp(−d sqrt(log x)).
-/
noncomputable section
open Finset Real Complex Filter Asymptotics MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.PrimeDistribution

private theorem explicit_formula_global_weight :
    ∃ D : ℝ, 0<D ∧ ∀ {x T : ℝ}, 2≤x → 2≤T → T≤x →
      |Chebyshev.psi x-x| ≤ D*(1+x*(Real.log x)^2/T+Real.log x+
        x*∑ ρ∈nontrivialZerosUpTo T,(zeroMultiplicity ρ:ℝ)*x^(ρ.re-1)) := by
  obtain ⟨C,hC,H⟩ := explicit_formula_psi
  let A := 1+∑ ρ∈nontrivialZerosUpTo 1,‖ρ‖⁻¹
  let c : ℂ := -deriv riemannZeta 0 / riemannZeta 0
  let D := C+A+‖c‖
  have hA : 1≤A := le_add_of_nonneg_right (sum_nonneg (fun z _ => by positivity))
  have hd : 0<D := by dsimp [D]; linarith [norm_nonneg c]
  refine ⟨D,hd,fun {x T} hx hT hTx => ?_⟩
  have hxp : 0<x := by linarith
  have hlog := Real.log_nonneg (show 1≤x by linarith)
  let S := ∑ ρ∈nontrivialZerosUpTo T,(zeroMultiplicity ρ:ℂ)*((x:ℂ)^ρ/ρ)
  let U := ∑ ρ∈nontrivialZerosUpTo T,(zeroMultiplicity ρ:ℝ)*x^(ρ.re-1)
  have hU : 0≤U := sum_nonneg (fun _ _ => by positivity)
  have hs : ‖S‖≤A*(x*U) := by
    dsimp only [S,U]; rw [←mul_assoc,Finset.mul_sum]
    refine (norm_sum_le ..).trans (sum_le_sum fun ρ hρ => ?_)
    obtain ⟨hzero,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hρ
    have hinv : ‖ρ‖⁻¹≤A := by
      by_cases h : 1≤|ρ.im|
      · exact (inv_le_one_of_one_le₀ (h.trans (Complex.abs_im_le_norm _))).trans hA
      · have hm := (mem_nontrivialZerosUpTo (T:=1)).mpr ⟨hzero,h₀,h₁,le_of_not_ge h⟩
        exact (single_le_sum (f:=fun z : ℂ => ‖z‖⁻¹) (fun _ _ => by positivity) hm).trans
          (le_add_of_nonneg_left zero_le_one)
    rw [norm_mul,Complex.norm_natCast,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hxp,div_eq_mul_inv]
    have he : x^ρ.re=x*x^(ρ.re-1) := by nth_rw 2 [←Real.rpow_one x]; rw [←Real.rpow_add hxp]; congr 1; ring
    rw [he]
    calc _ ≤ (zeroMultiplicity ρ:ℝ)*((x*x^(ρ.re-1))*A) := by gcongr
         _ = _ := by ring
  have ht := H x T hx hT hTx
  change ‖(Chebyshev.psi x:ℂ)-((x:ℂ)+c-S)‖≤_ at ht
  have heq : ((Chebyshev.psi x-x:ℝ):ℂ) = ((Chebyshev.psi x:ℂ)-((x:ℂ)+c-S))+(c-S) := by push_cast; ring
  have hmain : |Chebyshev.psi x-x| ≤ C*(x*(Real.log x)^2/T+Real.log x)+‖c‖+A*(x*U) := by
    change ‖(Chebyshev.psi x-x:ℝ)‖≤_
    rw [←Complex.norm_real,heq]
    exact (norm_add_le ..).trans ((add_le_add ht ((norm_sub_le ..).trans (add_le_add le_rfl hs))).trans_eq (by ring))
  change _≤D*(1+x*(Real.log x)^2/T+Real.log x+x*U)
  have hrem : 0≤x*(Real.log x)^2/T+Real.log x := by positivity
  have hD₁ : C≤D := by dsimp [D]; linarith [norm_nonneg c]
  have hD₂ : A≤D := by dsimp [D]; linarith [norm_nonneg c]
  have hD₃ : ‖c‖≤D := by dsimp [D]; linarith
  nlinarith only [hmain,hD₃,mul_le_mul_of_nonneg_right hD₁ hrem,mul_le_mul_of_nonneg_right hD₂ (mul_nonneg hxp.le hU)]

/-- A growing scaled zero-free gap improves the classical error bound
for ψ to every fixed positive coefficient in the exponential. -/
theorem psi_error_arbitrary_exp_of_growing_gap (hz : GrowingZetaScaledGap) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x-x|≤C*x*Real.exp (-d*√(Real.log x)) := by
  obtain ⟨A,hA,K,hK,H⟩ := zeta_zero_sum_of_scaled_gap
  obtain ⟨D,hD,HD⟩ := explicit_formula_global_weight
  let a := d+1
  have ha : 0<a := by dsimp [a]; linarith
  let u (x : ℝ) := √(Real.log x)
  let T (x : ℝ) := Real.exp (a*u x)
  let r := 4*a^2
  have hu : Tendsto u atTop atTop := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hT : Tendsto T atTop atTop := Real.tendsto_exp_atTop.comp (hu.const_mul_atTop ha)
  have hpoly : ∀ᶠ v : ℝ in atTop, v^4≤Real.exp v := by
    filter_upwards [(isLittleO_rpow_exp_atTop (4:ℝ)).bound zero_lt_one,eventually_ge_atTop (0:ℝ)] with v hv hv'
    simpa only [show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hv' 4),
      Real.norm_of_nonneg (Real.exp_pos v).le,one_mul] using hv
  refine ⟨D*(3+K),by positivity,?_⟩
  filter_upwards [hT (hz r),hT.eventually_ge_atTop 2,hu.eventually_ge_atTop 1,hu.eventually_ge_atTop a,
    hu.eventually_ge_atTop (4*a*(A+1)),hu hpoly,eventually_ge_atTop (2:ℝ)] with x hgap ht₂ hu₁ hua huA hup hx
  have hxp : 0<x := by linarith
  have huq : (u x)^2=Real.log x := Real.sq_sqrt (Real.log_nonneg (by linarith))
  have htx : T x≤x := by
    dsimp only [T]; apply (Real.exp_le_exp.mpr _).trans_eq (Real.exp_log hxp)
    nlinarith only [huq,mul_le_mul_of_nonneg_right hua (show 0≤u x by linarith)]
  have hlogT : Real.log (T x+2)≤2*a*u x := by
    have hl := Real.log_le_log (by linarith : 0<T x+2) (show T x+2≤(T x)^2 by nlinarith [sq_nonneg (T x-2)])
    rw [Real.log_pow,show Real.log (T x)=a*u x from Real.log_exp _] at hl
    norm_num at hl; linarith
  let b := u x/(4*a)
  have hb : 0≤b := by dsimp [b]; positivity [show 0≤u x by linarith]
  have hparam : (A+1+b)*Real.log (T x+2)≤Real.log x := by
    apply (mul_le_mul_of_nonneg_left hlogT (show 0≤A+1+b by linarith)).trans
    dsimp [b]; field_simp; nlinarith only [huq,mul_le_mul_of_nonneg_right huA (show 0≤u x by linarith),mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right huA (show 0≤u x by linarith)) ha.le]
  have hsum := H (show 0≤T x by linarith) hxp hb hparam hgap
  have hbr : b*r=a*u x := by dsimp [b,r]; field_simp
  rw [neg_mul, hbr] at hsum
  let E := Real.exp (-d*u x)
  have hE : 0<E := Real.exp_pos _
  have hscale : Real.exp (u x) ≤ x*E := by
    change Real.exp (u x) ≤ x*Real.exp (-d*u x)
    conv_rhs => lhs; rw [←Real.exp_log hxp]
    rw [←Real.exp_add]; apply Real.exp_le_exp.mpr
    dsimp [a] at hua; nlinarith only [huq,mul_le_mul_of_nonneg_right hua (show 0≤u x by linarith)]
  have hconst : 1≤x*E := (Real.one_le_exp (by linarith : 0≤u x)).trans hscale
  have hlogx : Real.log x≤x*E := by
    apply le_trans _ (hup.trans hscale); rw [←huq]; nlinarith [mul_nonneg (show 0≤(u x)^2-1 by nlinarith) (sq_nonneg (u x))]
  have htrunc : x*(Real.log x)^2/T x ≤ x*E := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    have he : E*T x=Real.exp (u x) := by dsimp [E,T,a]; rw [←Real.exp_add]; congr 1; ring
    rw [mul_assoc,he,←huq]; exact mul_le_mul_of_nonneg_left (by simpa [←pow_mul] using hup) hxp.le
  have hdec : Real.exp (-(a*u x))≤E := by apply Real.exp_le_exp.mpr; dsimp [a]; linarith
  have hg := HD hx ht₂ htx
  change |Chebyshev.psi x-x|≤D*(3+K)*x*E
  have htotal := add_le_add (add_le_add (add_le_add hconst htrunc) hlogx)
    (mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hdec hK.le)) hxp.le)
  exact hg.trans ((mul_le_mul_of_nonneg_left htotal hD.le).trans_eq (by ring))

private theorem eventually_sqrt_le_exp_error (d : ℝ) :
    ∀ᶠ x : ℝ in atTop, √x ≤ x*Real.exp (-d*√(Real.log x)) := by
  filter_upwards [(Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (2*d),
    eventually_gt_atTop (1:ℝ)] with x hd hx
  have hp := zero_lt_one.trans hx
  have hs := Real.sq_sqrt (Real.log_nonneg hx.le)
  have he : √x=Real.exp (Real.log x/2) := by rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hp]; congr 1; ring
  rw [he]; conv_rhs => lhs; rw [←Real.exp_log hp]
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  change 2*d≤√(Real.log x) at hd
  nlinarith only [hs,mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg (Real.log x))]

/-- The improved exponential error for θ retains every fixed positive
coefficient from the corresponding estimate for ψ. -/
theorem theta_error_arbitrary_exp_of_growing_gap (hz : GrowingZetaScaledGap) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x-x|≤C*x*Real.exp (-d*√(Real.log x)) := by
  obtain ⟨C,hC,H⟩ := psi_error_arbitrary_exp_of_growing_gap hz hd
  let K := (Real.log 4+4)*3
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K+C,by positivity,?_⟩
  filter_upwards [H,eventually_sqrt_le_exp_error d] with x h hs
  have hθ := abs_psi_sub_theta_le_mul_sqrt x
  rw [abs_sub_comm (Chebyshev.psi x)] at hθ
  have htri := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
  change _≤K*√x at hθ
  nlinarith only [htri,hθ,h,mul_le_mul_of_nonneg_left hs hK.le]

private theorem integrable_theta_error {x : ℝ} (hx : 2≤x) :
    IntervalIntegrable (fun t => (Chebyshev.theta t-t)/(t*(Real.log t)^2)) volume 2 x := by
  have hi : IntervalIntegrable (fun t => Chebyshev.theta t/(t*(Real.log t)^2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hj : ContinuousOn (fun t : ℝ => t/(t*(Real.log t)^2)) (Set.Icc 2 x) := by
    apply continuousOn_of_forall_continuousAt; intro t ht
    have ht' : 1<t := by linarith [ht.1]
    have hn : t≠0 := by linarith
    have hl' := (Real.log_pos ht').ne'
    fun_prop (disch := positivity)
  simpa only [sub_div] using hi.sub (hj.intervalIntegrable_of_Icc hx)

/-- Abel summation transfers the exponential improvement to the difference
between prime counting and the logarithmic integral. -/
theorem primePi_error_arbitrary_exp_of_growing_gap (hz : GrowingZetaScaledGap) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      |primePi x-logIntegral x|≤C*x*Real.exp (-d*√(Real.log x)) := by
  obtain ⟨C,hC,H⟩ := theta_error_arbitrary_exp_of_growing_gap hz (show 0<2*d by positivity)
  obtain ⟨U,hU⟩ := eventually_atTop.mp H
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  let B := (Real.log 4+1)/(Real.log 2)^2
  let D := C/(Real.log 2)^2
  have hB : 0<B := by dsimp [B]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨C/Real.log 2+2/Real.log 2+B+D,by positivity,?_⟩
  filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop U,Real.tendsto_sqrt_atTop.eventually_ge_atTop 2,
    eventually_ge_atTop (4:ℝ),eventually_sqrt_le_exp_error d] with x hUs hxs hx hscale
  let s := √x
  let E := Real.exp (-d*√(Real.log x))
  let f (t : ℝ) := (Chebyshev.theta t-t)/(t*(Real.log t)^2)
  have hx' : 0<x := by linarith
  have hsx : s≤x := Real.sqrt_le_self_iff.mpr (.inr (by linarith))
  have hs' : 0<s := Real.sqrt_pos.mpr hx'
  have hi := integrable_theta_error (show 2≤x by linarith)
  have hm : s∈Set.uIcc 2 x := by rw [Set.uIcc_of_le (by linarith)]; exact ⟨hxs,hsx⟩
  have hi₁ : IntervalIntegrable f volume 2 s := hi.mono_set (Set.uIcc_subset_uIcc_left hm)
  have hi₂ : IntervalIntegrable f volume s x := hi.mono_set (Set.uIcc_subset_uIcc_right hm)
  have hcmp {t : ℝ} (ht : 2≤t) {v : ℝ} (hv : 0≤v) (hb : |Chebyshev.theta t-t|≤v*t) :
      ‖f t‖ ≤ v/(Real.log 2)^2 := by
    have ht' : 0<t := by linarith
    have hlt := Real.log_le_log (show (0:ℝ)<2 by norm_num) ht
    change |(Chebyshev.theta t-t)/(t*(Real.log t)^2)|≤_
    rw [abs_div,abs_of_pos (mul_pos ht' (sq_pos_of_pos (h₂.trans_le hlt)))]
    calc _ ≤ (v*t)/(t*(Real.log 2)^2) := by gcongr
         _ = _ := by field_simp
  have hleft : |∫ t in (2:ℝ)..s,f t| ≤ B*s := by
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a:=2) (b:=s) (f:=f)
      (C:=B) (fun t ht => by
        rw [Set.uIoc_of_le hxs] at ht
        apply hcmp ht.1.le (by positivity : 0≤Real.log 4+1)
        rw [abs_le]
        constructor <;> nlinarith [ht.1,Chebyshev.theta_le_log4_mul_x (by linarith [ht.1] : 0≤t),
          Chebyshev.theta_nonneg t,mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤4)) (show 0≤t by linarith [ht.1])])
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxs)] at hbd
    nlinarith only [hbd,hB]
  have hE : 0<E := Real.exp_pos _
  have hright : |∫ t in s..x,f t| ≤ D*x*E := by
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a:=s) (b:=x) (f:=f)
      (C:=D*E) (fun t ht => by
        rw [Set.uIoc_of_le hsx] at ht
        have hg := Real.log_le_log hs' ht.1.le
        change Real.log (√x)≤Real.log t at hg
        rw [Real.log_sqrt hx'.le] at hg
        have hlx := Real.log_nonneg (show 1≤x by linarith)
        have hlt := Real.log_nonneg (show 1≤t by linarith [ht.1,hxs])
        have hlog : √(Real.log x)≤2*√(Real.log t) := by
          apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
          rw [mul_pow,Real.sq_sqrt hlx,Real.sq_sqrt hlt]; nlinarith
        have he : Real.exp (-(2*d)*√(Real.log t))≤E := Real.exp_le_exp.mpr (by
          nlinarith only [mul_le_mul_of_nonneg_left hlog hd.le])
        have ht' := hU t (hUs.trans ht.1.le)
        have hb : |Chebyshev.theta t-t|≤(C*E)*t := by
          nlinarith only [ht',mul_le_mul_of_nonneg_left he (show 0≤C*t by positivity [show 0<t by linarith [ht.1,hxs]])]
        exact (hcmp (hxs.trans ht.1.le) (mul_nonneg hC.le hE.le) hb).trans_eq (by dsimp [D]; ring))
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hsx)] at hbd
    nlinarith only [hbd,mul_nonneg (mul_nonneg hD.le hE.le) hs'.le]
  have hfx : |∫ t in (2:ℝ)..x,f t|≤ B*s+D*x*E := by
    rw [←intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
    exact (abs_add_le ..).trans (add_le_add hleft hright)
  have hθ := hU x (hUs.trans hsx)
  have hdec : Real.exp (-(2*d)*√(Real.log x))≤E := Real.exp_le_exp.mpr (by
    nlinarith only [mul_nonneg hd.le (Real.sqrt_nonneg (Real.log x))])
  have hxlog := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2≤x)
  have hfirst : |(Chebyshev.theta x-x)/Real.log x|≤(C/Real.log 2)*x*E := by
    rw [abs_div,abs_of_pos (h₂.trans_le hxlog)]
    calc _ ≤ (C*x*E)/Real.log 2 := by gcongr; exact hθ.trans (mul_le_mul_of_nonneg_left hdec (by positivity))
         _ = _ := by ring
  have hsE : s≤x*E := hscale
  have hone : 1≤x*E := (show 1≤s by linarith).trans hsE
  have hconst := mul_le_mul_of_nonneg_left hone (show 0≤2/Real.log 2 by positivity)
  have hid := primePi_sub_li_eq_theta_sub_id_abel (show 2≤x by linarith)
  change primePi x-logIntegral x=(Chebyshev.theta x-x)/Real.log x+2/Real.log 2+∫ t in (2:ℝ)..x,f t at hid
  rw [hid]
  have ht1 := abs_add_le ((Chebyshev.theta x-x)/Real.log x) (2/Real.log 2)
  rw [abs_of_nonneg (by positivity : 0≤2/Real.log 2)] at ht1
  exact (abs_add_le ..).trans ((add_le_add ht1 hfx).trans (by
    nlinarith only [hfirst,hconst,mul_le_mul_of_nonneg_left hsE hB.le]))

/-- For each fixed positive d, the error of the prime number theorem for
ψ is O_d(x exp(−d sqrt(log x))). -/
theorem psi_error_arbitrary_exp {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x-x|≤C*x*Real.exp (-d*√(Real.log x)) :=
  psi_error_arbitrary_exp_of_growing_gap
    (growingZetaScaledGap_of_arbitrary_width (fun _ hB => RiemannZeta.littlewood_zero_free hB)) hd

/-- The prime-weighted Chebyshev function admits the same arbitrary
fixed exponential saving. -/
theorem theta_error_arbitrary_exp {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x-x|≤C*x*Real.exp (-d*√(Real.log x)) :=
  theta_error_arbitrary_exp_of_growing_gap
    (growingZetaScaledGap_of_arbitrary_width (fun _ hB => RiemannZeta.littlewood_zero_free hB)) hd

/-- The error in approximating prime counting by the logarithmic integral
is O_d(x exp(−d sqrt(log x))) for every fixed d>0. -/
theorem primePi_error_arbitrary_exp {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      |primePi x-logIntegral x|≤C*x*Real.exp (-d*√(Real.log x)) :=
  primePi_error_arbitrary_exp_of_growing_gap
    (growingZetaScaledGap_of_arbitrary_width (fun _ hB => RiemannZeta.littlewood_zero_free hB)) hd

private theorem global_exp_error_of_eventual {f : ℝ → ℝ} {d : ℝ} (hd : 0<d)
    (hcoarse : ∃ K : ℝ, 0<K ∧ ∃ k : ℝ, 0<k ∧ ∀ x : ℝ, 2≤x →
      |f x|≤K*x*Real.exp (-k*√(Real.log x)))
    (h : ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, |f x|≤C*x*Real.exp (-d*√(Real.log x))) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 2≤x → |f x|≤C*x*Real.exp (-d*√(Real.log x)) := by
  obtain ⟨K,hK,k,hk,H⟩ := hcoarse
  obtain ⟨C,hC,H'⟩ := h
  obtain ⟨X,hX⟩ := eventually_atTop.mp H'
  let D := K*Real.exp (d*√(Real.log (max 2 X)))
  refine ⟨max C D,hC.trans_le (le_max_left ..),fun x hx => ?_⟩
  have hxp : 0<x := by linarith
  by_cases hxX : X≤x
  · exact (hX x hxX).trans (by gcongr; exact le_max_left ..)
  · have hX' : x≤max 2 X := (le_of_not_ge hxX).trans (le_max_right ..)
    have hle := Real.sqrt_le_sqrt (Real.log_le_log hxp hX')
    have hprod : 1≤Real.exp (d*√(Real.log (max 2 X)))*Real.exp (-d*√(Real.log x)) := by
      rw [←Real.exp_add]; exact Real.one_le_exp (by nlinarith [mul_le_mul_of_nonneg_left hle hd.le])
    have hweak := (H x hx).trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hk.le (Real.sqrt_nonneg (Real.log x))])))
    have hmain : K*x≤D*x*Real.exp (-d*√(Real.log x)) := by
      dsimp [D]; nlinarith only [mul_le_mul_of_nonneg_left hprod (show 0≤K*x by positivity)]
    exact hweak.trans (hmain.trans (by gcongr; exact le_max_right ..))

/-- Uniform form of the improved prime number theorem. For each prescribed
positive d a single constant bounds the three errors, simultaneously at
all real x≥2. -/
theorem prime_number_theorem_arbitrary_exp {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 2≤x →
      |Chebyshev.psi x-x| ≤ C*x*Real.exp (-d*√(Real.log x)) ∧
      |Chebyshev.theta x-x| ≤ C*x*Real.exp (-d*√(Real.log x)) ∧
      |primePi x-logIntegral x| ≤ C*x*Real.exp (-d*√(Real.log x)) := by
  obtain ⟨A,hA,HA⟩ := global_exp_error_of_eventual (f:=fun x => Chebyshev.psi x-x) hd abs_psi_sub_id_le_exp (psi_error_arbitrary_exp hd)
  obtain ⟨B,hB,HB⟩ := global_exp_error_of_eventual (f:=fun x => Chebyshev.theta x-x) hd abs_theta_sub_id_le_exp (theta_error_arbitrary_exp hd)
  obtain ⟨C,hC,HC⟩ := global_exp_error_of_eventual (f:=fun x => primePi x-logIntegral x) hd abs_primePi_sub_logIntegral_le_exp (primePi_error_arbitrary_exp hd)
  refine ⟨A+B+C,by positivity,fun x hx => ?_⟩
  have hxp : 0<x := by linarith
  exact ⟨(HA x hx).trans (by gcongr <;> linarith),
    (HB x hx).trans (by gcongr <;> linarith),(HC x hx).trans (by gcongr <;> linarith)⟩

end AnalyticNumberTheory.PrimeDistribution
