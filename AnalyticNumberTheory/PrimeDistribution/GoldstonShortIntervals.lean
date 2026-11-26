import AnalyticNumberTheory.PrimeDistribution.GoldstonIntervalZeros
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalPrimeCounts

/-! # The prime number theorem in intervals longer than √x log x under RH -/

noncomputable section

open Filter Asymptotics Real Complex
open scoped Topology

namespace AnalyticNumberTheory.PrimeDistribution

open AnalyticNumberTheory.RiemannZeta

/-- A free splitting parameter g gives an error h/g + √x log x (1+log g)
in the short-interval prime number theorem for the von Mangoldt function. -/
theorem psi_interval_goldston_bound_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C > 0, ∀ {x h g : ℝ}, Real.exp 2 ≤ x → 0 ≤ h → h ≤ x → 1 ≤ g →
      2*g ≤ Real.sqrt x/Real.log x →
      |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤
        C*(h/g+Real.sqrt x*Real.log x*(1+Real.log g)) := by
  obtain ⟨A,hA,HE⟩ := goldston_truncated_explicit_formula_of_rh hRH
  obtain ⟨B,hB,HZ⟩ := sharpZetaZeroSum_increment_of_rh hRH
  refine ⟨6*A+B,by positivity,?_⟩
  intro x h g hx hh hhx hg hgT
  let y := x+h
  let r := Real.sqrt x
  let T := r/Real.log x
  let U := T/g
  let M := r*Real.log x
  have hx₀ := (Real.exp_pos _).trans_le hx
  have hx₁ : 1 ≤ x := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2)).trans hx
  have hlog : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx₀).mpr hx
  have hr : 0 < r := Real.sqrt_pos.mpr hx₀
  have hr2 : r^2 = x := Real.sq_sqrt hx₀.le
  have hlog₀ : 0 < Real.log x := by linarith
  have hy : x ≤ y := le_add_of_nonneg_right hh
  have hg₀ := zero_lt_one.trans_le hg
  have hT : 2 ≤ T := by dsimp only [T,r]; linarith
  have hT₀ : 0 < T := by linarith
  have hU : 2 ≤ U := (le_div_iff₀ hg₀).mpr hgT
  have hUT : U ≤ T := div_le_self hT₀.le hg
  have hrx : r ≤ x := (Real.sqrt_le_iff.mpr ⟨hx₀.le,by nlinarith [sq_nonneg (x-1)]⟩)
  have hTx : T ≤ x := (div_le_self hr.le (by linarith)).trans hrx
  have hlogT := Real.log_le_log hT₀ hTx
  have hlogT₀ : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := mul_nonneg hr.le hlog₀.le
  have hq : 0 ≤ Real.log g := Real.log_nonneg hg
  have hroot : Real.sqrt y ≤ 2*r := by
    have hysq := Real.sq_sqrt (hx₀.trans_le hy).le
    dsimp only [y] at hysq ⊢
    nlinarith [Real.sqrt_nonneg (x+h)]
  have hquot : x/T = M := by dsimp only [T,M]; field_simp [hr.ne',hlog₀.ne']; nlinarith [hr2]
  have hquot' : y/T ≤ 2*M := by
    rw [←hquot,←mul_div_assoc]; exact div_le_div_of_nonneg_right (by dsimp only [y]; linarith) hT₀.le
  have hlogy : Real.sqrt y*Real.log T ≤ 2*M := by
    calc _ ≤ (2*r)*Real.log x := mul_le_mul hroot hlogT hlogT₀ (by positivity)
         _ = _ := by dsimp only [M]; ring
  have hlogx : r*Real.log T ≤ M := mul_le_mul_of_nonneg_left hlogT hr.le
  have hlow : (h/r)*U*Real.log T ≤ h/g := by
    calc _ ≤ (h/r)*U*Real.log x := mul_le_mul_of_nonneg_left hlogT (by dsimp only [U]; positivity)
         _ = _ := by dsimp only [U,T]; field_simp [hr.ne',hlog₀.ne',hg₀.ne']
  have hratio : T/U = g := by dsimp only [U]; field_simp [hT₀.ne',hg₀.ne']
  let E (v : ℝ) := (Chebyshev.psi v:ℂ)-(v:ℂ)+sharpZetaZeroSum v T
  have h₁ : ‖E x‖ ≤ A*(M+M) := (HE hx hT).trans (mul_le_mul_of_nonneg_left
    (add_le_add hquot.le hlogx) hA.le)
  have h₂ : ‖E y‖ ≤ A*(2*M+2*M) := (HE (hx.trans hy) hT).trans (mul_le_mul_of_nonneg_left
    (add_le_add hquot' hlogy) hA.le)
  have hz := HZ hx₀ hh hhx hU hUT
  rw [hratio] at hz
  have h₃ := hz.trans (mul_le_mul_of_nonneg_left (add_le_add hlow
    (mul_le_mul_of_nonneg_right hlogx (by linarith : 0 ≤ 1+Real.log g))) hB.le)
  have he : ((Chebyshev.psi y-Chebyshev.psi x-h:ℝ):ℂ) =
      (E y-E x)-(sharpZetaZeroSum y T-sharpZetaZeroSum x T) := by dsimp only [E,y]; push_cast; ring
  change ‖(Chebyshev.psi y-Chebyshev.psi x-h:ℝ)‖ ≤ _
  rw [←Complex.norm_real,he]
  apply (norm_sub_le _ _).trans ((add_le_add (norm_sub_le ..) le_rfl).trans _)
  apply (add_le_add (add_le_add h₂ h₁) h₃).trans
  change _ ≤ (6*A+B)*(h/g+M*(1+Real.log g))
  nlinarith only [mul_nonneg hA.le (div_nonneg hh hg₀.le),mul_nonneg (mul_nonneg hA.le hM) hq]

/-- If h(x) is eventually positive and at most x and h(x)/(√x log x) tends
to infinity, then ψ(x+h(x))−ψ(x) is asymptotic to h(x) under RH. -/
theorem psi_variable_shortInterval_of_rh (hRH : RiemannHypothesisProp) {h : ℝ → ℝ}
    (hh : ∀ᶠ x in atTop, 0 < h x ∧ h x ≤ x)
    (hgrowth : Tendsto (fun x => h x/(Real.sqrt x*Real.log x)) atTop atTop) :
    (fun x => Chebyshev.psi (x+h x)-Chebyshev.psi x) ~[atTop] h := by
  obtain ⟨C,hC,H⟩ := psi_interval_goldston_bound_of_rh hRH
  have hdom : (fun x : ℝ => Real.sqrt x*Real.log x) =o[atTop] h := IsLittleO.of_tendsto_div_atTop hgrowth
  have hlog : Real.log =o[atTop] Real.sqrt := by
    change Real.log =o[atTop] fun x : ℝ => Real.sqrt x
    simpa only [Real.sqrt_eq_rpow] using isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)
  apply IsLittleO.of_bound
  intro ε hε
  let g := max 1 (2*C/ε)
  have hg : 1 ≤ g := le_max_left ..
  have hg₀ := zero_lt_one.trans_le hg
  have hq : 0 < 1+Real.log g := by linarith [Real.log_nonneg hg]
  have hc : C/g ≤ ε/2 := by
    apply (div_le_iff₀ hg₀).mpr
    have := (div_le_iff₀ hε).mp (le_max_right 1 (2*C/ε))
    dsimp only [g]; linarith
  have hd := hdom.bound (show 0 < ε/(2*C*(1+Real.log g)) by positivity)
  have ht := hlog.bound (show 0 < 1/(2*g) by positivity)
  filter_upwards [hh,hd,ht,eventually_ge_atTop (Real.exp 2)] with x hh hd ht hx
  have hx₀ := (Real.exp_pos _).trans_le hx
  have hxlog : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx₀).mpr hx
  have hl : 0 < Real.log x := by linarith
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) hl.le),
    abs_of_pos hh.1] at hd
  simp only [Real.norm_eq_abs,abs_of_pos hl,abs_of_nonneg (Real.sqrt_nonneg x)] at ht
  have hcut : 2*g ≤ Real.sqrt x/Real.log x := by
    apply (le_div_iff₀ hl).mpr
    have h := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*g by positivity)
    field_simp [hg₀.ne'] at h
    linarith
  change |Chebyshev.psi (x+h x)-Chebyshev.psi x-h x| ≤ ε*|h x|
  rw [abs_of_pos hh.1]
  apply (H hx hh.1.le hh.2 hg hcut).trans
  calc
    _ = (C/g)*h x + (C*(1+Real.log g))*(Real.sqrt x*Real.log x) := by ring
    _ ≤ (ε/2)*h x + (C*(1+Real.log g))*((ε/(2*C*(1+Real.log g)))*h x) :=
      add_le_add (mul_le_mul_of_nonneg_right hc hh.1.le) (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = _ := by field_simp [hC.ne',hq.ne']; ring

/-- The θ increment has the same short-interval asymptotic above √x log x under RH. -/
theorem theta_variable_shortInterval_of_rh (hRH : RiemannHypothesisProp) {h : ℝ → ℝ}
    (hh : ∀ᶠ x in atTop, 0 < h x ∧ h x ≤ x)
    (hgrowth : Tendsto (fun x => h x/(Real.sqrt x*Real.log x)) atTop atTop) :
    (fun x => Chebyshev.theta (x+h x)-Chebyshev.theta x) ~[atTop] h := by
  have hdom : (fun x : ℝ => Real.sqrt x*Real.log x) =o[atTop] h := IsLittleO.of_tendsto_div_atTop hgrowth
  have hroot : Real.sqrt =O[atTop] (fun x : ℝ => Real.sqrt x*Real.log x) := by
    apply IsBigO.of_bound 1
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg x),Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (zero_le_one.trans hx)),one_mul]
    exact le_mul_of_one_le_right (Real.sqrt_nonneg x) hx
  have he := (shortInterval_theta_sub_psi_isBigO_sqrt (hh.mono fun _ hx => hx.2)).trans_isLittleO
    (hroot.trans_isLittleO hdom)
  exact ((psi_variable_shortInterval_of_rh hRH hh hgrowth).add_isLittleO he).congr_left
    (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)

/-- Under RH, if h(x)/(√x log x) tends to infinity and 0 < h(x) ≤ x
eventually, the number of primes in (x,x+h(x)] is asymptotic to h(x)/log x. -/
theorem primePi_variable_shortInterval_of_rh (hRH : RiemannHypothesisProp) {h : ℝ → ℝ}
    (hh : ∀ᶠ x in atTop, 0 < h x ∧ h x ≤ x)
    (hgrowth : Tendsto (fun x => h x/(Real.sqrt x*Real.log x)) atTop atTop) :
    (fun x => primePi (x+h x)-primePi x) ~[atTop] fun x => h x/Real.log x :=
  primePi_variableInterval_of_theta_equivalent hh (theta_variable_shortInterval_of_rh hRH hh hgrowth)

end AnalyticNumberTheory.PrimeDistribution
