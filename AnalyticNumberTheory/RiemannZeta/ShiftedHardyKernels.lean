import AnalyticNumberTheory.RiemannZeta.HardyOscillation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Oscillatory kernels for two shifted Hardy polynomials

The quadratic-phase estimate includes a free phase offset, as required
by the additive coefficients of the reciprocal Hurwitz polynomial.
The frequency spacing estimate compares any two shifts in the same
pair of unit cells with their integer logarithmic spacing.
-/
noncomputable section
open Real Complex MeasureTheory Set
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

/-- The doubled elementary phase, for arbitrary positive real frequencies. -/
def shiftedHardyPhase (r s u t : ℝ) :=
  2*hardyPhase t-t*(Real.log r+Real.log s)+u

private def slope (r s t : ℝ) := Real.log t-Real.log (2*Real.pi)-Real.log r-Real.log s

private theorem phase_deriv (r s u : ℝ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (shiftedHardyPhase r s u) (slope r s t) t := by
  have H := ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).sub
    ((hasDerivAt_id t).const_mul (Real.log (2*Real.pi)+1))
  have h := (((((H.div_const 2).sub_const (Real.pi/8)).const_mul 2).sub
    ((hasDerivAt_id t).mul_const (Real.log r+Real.log s))).add_const u)
  convert h using 1
  · rfl
  · dsimp [slope];field_simp;ring

private theorem slope_deriv (r s : ℝ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (slope r s) t⁻¹ t :=
  (((Real.hasDerivAt_log ht.ne').sub_const (Real.log (2*Real.pi))).sub_const (Real.log r)).sub_const (Real.log s)

/-- Second-derivative estimate valid also at a stationary endpoint. -/
theorem norm_integral_shiftedHardyPhase_le_sqrt (r s u : ℝ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ‖∫ t in a..b,Complex.exp ((shiftedHardyPhase r s u t:ℂ)*I)‖≤8*Real.sqrt b := by
  have hb := ha.trans_le hab
  have H := vanDerCorput_integral_second_deriv (F':=slope r s) (F'':=fun t : ℝ => t⁻¹)
    hab (r:=b⁻¹) (by positivity)
    (fun t ht => phase_deriv r s u (ha.trans_le ht.1)) (fun t ht => slope_deriv r s (ha.trans_le ht.1))
    (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne'))
    (fun t ht => by rw [abs_of_nonneg (inv_nonneg.mpr (ha.trans_le ht.1).le)]
                    exact inv_anti₀ (ha.trans_le ht.1) ht.2)
  exact H.trans_eq (by rw [Real.sqrt_inv,div_inv_eq_mul])

private theorem log_neq {r s : ℝ} (hr : 0<r) (hs : 0<s) (hne : r≠s) : Real.log s≠Real.log r :=
  fun h => hne ((Real.log_injOn_pos hs hr h).symm)

/-- First-derivative test after both real-frequency cutoffs have been passed. -/
theorem norm_integral_shiftedHardyPhase_of_ne {r s : ℝ} (hr : 0<r) (hs : 0<s) (hne : r≠s)
    (u : ℝ) {a b : ℝ} (hrA : 2*Real.pi*r^2≤a) (hsA : 2*Real.pi*s^2≤a) (hab : a≤b) :
    ‖∫ t in a..b,Complex.exp ((shiftedHardyPhase r s u t:ℂ)*I)‖≤4/|Real.log s-Real.log r| := by
  have hrc : 0<2*Real.pi*r^2 := by positivity
  have hsc : 0<2*Real.pi*s^2 := by positivity
  have ha := hrc.trans_le hrA
  apply vanDerCorput_integral_first_deriv (F':=slope r s) (F'':=fun t : ℝ => t⁻¹) hab (abs_pos.mpr (sub_ne_zero.mpr (log_neq hr hs hne)))
    (fun t ht => phase_deriv r s u (ha.trans_le ht.1)) (fun t ht => slope_deriv r s (ha.trans_le ht.1))
    (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')) (Or.inl (fun t ht => inv_nonneg.mpr (ha.trans_le ht.1).le))
  intro t ht
  have H := Real.log_le_log hrc (hrA.trans ht.1)
  have K := Real.log_le_log hsc (hsA.trans ht.1)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at H K
  apply le_trans _ (le_abs_self _)
  rw [abs_le];dsimp [slope];norm_num at H K;constructor <;> linarith

/-- Corresponding linear-phase estimate, with an arbitrary constant offset. -/
theorem norm_integral_linear_phase {d : ℝ} (hd : d≠0) (u : ℝ) {a b : ℝ} (hab : a≤b) :
    ‖∫t in a..b,Complex.exp (((t*d+u:ℝ):ℂ)*I)‖≤4/|d| :=
  vanDerCorput_integral_first_deriv (F:=fun t : ℝ => t*d+u) (F':=fun _ => d) (F'':=fun _ => 0) hab
    (abs_pos.mpr hd) (fun t _ => by simpa using ((hasDerivAt_id t).mul_const d).add_const u)
    (fun t _ => hasDerivAt_const _ _) continuousOn_const (Or.inl (fun _ _ => le_rfl)) (fun _ _ => le_rfl)

/-- Moving the nth frequency anywhere between n−1+a and n preserves
at least a times the logarithmic gap between distinct cells. -/
theorem shifted_log_gap_lower {a r s : ℝ} {k l : ℕ} (ha : a∈Ioc (0:ℝ) 1) (hk : 0<k)
    (hkl : k<l) (hr : 0<r) (hrk : r≤k) (hsl : (l:ℝ)-1+a≤s) :
    a*(Real.log l-Real.log k)≤Real.log s-Real.log r := by
  have hkr : 0<(k:ℝ) := Nat.cast_pos.mpr hk
  have hlr : 0<(l:ℝ) := Nat.cast_pos.mpr (hk.trans hkl)
  have hdist : (k:ℝ)+1≤l := by exact_mod_cast hkl
  have hconv : (k:ℝ)+a*((l:ℝ)-k)≤s := by nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (show 0≤(l:ℝ)-k-1 by linarith)]
  have hk' : (1:ℝ)≤(l:ℝ)/k := (one_le_div hkr).mpr (by linarith)
  have hs : 0<s := by linarith [mul_nonneg ha.1.le (show 0≤(l:ℝ)-k by linarith)]
  have hj := rpow_one_add_le_one_add_mul_self (s:=(l:ℝ)/k-1) (by linarith) ha.1.le ha.2
  rw [show 1+((l:ℝ)/k-1)=l/k by ring] at hj
  have hfrac : 1+a*((l:ℝ)/k-1)≤s/k := by
    apply (le_div_iff₀ hkr).mpr
    convert hconv using 1 <;> field_simp <;> ring
  have H := Real.log_le_log (Real.rpow_pos_of_pos (div_pos hlr hkr) a) (hj.trans hfrac)
  rw [Real.log_rpow (div_pos hlr hkr),Real.log_div hlr.ne' hkr.ne',Real.log_div hs.ne' hkr.ne'] at H
  linarith only [H,Real.log_le_log hr hrk]

end AnalyticNumberTheory.RiemannZeta
