import AnalyticNumberTheory.RiemannZeta.HardyOscillation

/-!
# Oscillatory kernels in the Riemann–Siegel second moment

After both sharp cutoffs have been passed, the slope of the sum phase
is at least the logarithmic separation of the indices. On the diagonal
a second derivative estimate controls the endpoint stationary point.
-/
noncomputable section
open Real Complex MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

/-- The elementary Riemann–Siegel phase at integer frequency n. -/
def hardyAngle (n : ℕ) (t : ℝ) := hardyPhase t-t*Real.log n

/-- The height at which the n-th term enters the Riemann–Siegel sum. -/
def hardyCutoff (n : ℕ) : ℝ := 2*Real.pi*(n:ℝ)^2

theorem continuous_hardyAngle (n : ℕ) : Continuous (hardyAngle n) := by
  unfold hardyAngle hardyPhase
  exact (((Real.continuous_mul_log.sub (continuous_const.mul continuous_id)).div_const 2).sub continuous_const).sub
    (continuous_id.mul continuous_const)

private theorem cos_integral_le_exp {F : ℝ→ℝ} (hF : Continuous F) (a b : ℝ) :
    |∫t in a..b,Real.cos (F t)|≤‖∫t in a..b,Complex.exp ((F t:ℂ)*I)‖ := by
  let f := fun t : ℝ => Complex.exp ((F t:ℂ)*I)
  have hf : Continuous f := by dsimp [f];fun_prop
  have H := intervalIntegral.intervalIntegral_re (hf.intervalIntegrable (μ:=volume) a b)
  change (∫t in a..b,(f t).re)=(∫t in a..b,f t).re at H
  simp only [f,Complex.exp_ofReal_mul_I_re] at H
  rw [H];exact Complex.abs_re_le_norm _

private def pairSlope (m n : ℕ) (t : ℝ) := Real.log t-Real.log (2*Real.pi)-Real.log m-Real.log n

private theorem pair_deriv (m n : ℕ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun u => hardyAngle m u+hardyAngle n u) (pairSlope m n t) t := by
  have hh := ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).sub
    ((hasDerivAt_id t).const_mul (Real.log (2*Real.pi)+1))
  have hd (j : ℕ) := ((hh.div_const 2).sub_const (Real.pi/8)).sub ((hasDerivAt_id t).mul_const (Real.log j))
  convert (hd m).add (hd n) using 1
  · rfl
  · dsimp [pairSlope];field_simp;ring

private theorem pairSlope_deriv (m n : ℕ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (pairSlope m n) t⁻¹ t :=
  (((Real.hasDerivAt_log ht.ne').sub_const (Real.log (2*Real.pi))).sub_const (Real.log m)).sub_const (Real.log n)

/-- The stationary endpoint contributes O(sqrt b), uniformly in the index. -/
theorem abs_integral_hardyAngle_add_le_sqrt (m n : ℕ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    |∫t in a..b,Real.cos (hardyAngle m t+hardyAngle n t)|≤8*Real.sqrt b := by
  have hb := ha.trans_le hab
  apply (cos_integral_le_exp ((continuous_hardyAngle m).add (continuous_hardyAngle n)) a b).trans
  have H := vanDerCorput_integral_second_deriv (F':=pairSlope m n) (F'':=fun t : ℝ => t⁻¹)
    hab (r:=b⁻¹) (by positivity)
    (fun t ht => pair_deriv m n (ha.trans_le ht.1)) (fun t ht => pairSlope_deriv m n (ha.trans_le ht.1))
    (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne'))
    (fun t ht => by rw [abs_of_nonneg (inv_nonneg.mpr (ha.trans_le ht.1).le)]
                    exact inv_anti₀ (ha.trans_le ht.1) ht.2)
  exact H.trans_eq (by rw [Real.sqrt_inv,div_inv_eq_mul])

private theorem log_cutoff {n : ℕ} (hn : 0<n) :
    Real.log (hardyCutoff n)=Real.log (2*Real.pi)+2*Real.log n := by
  have hp : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  rw [hardyCutoff,Real.log_mul (by positivity) (by positivity),Real.log_pow];norm_num

private theorem log_ne {m n : ℕ} (hm : 0<m) (hn : 0<n) (hne : m≠n) : Real.log n≠Real.log m := by
  rcases lt_or_gt_of_ne hne with h|h
  · exact (Real.log_lt_log (Nat.cast_pos.mpr hm) (by exact_mod_cast h)).ne'
  · exact (Real.log_lt_log (Nat.cast_pos.mpr hn) (by exact_mod_cast h)).ne

/-- Beyond both entry heights, the unequal-index sum phase has a bound
inversely proportional to the logarithmic separation. -/
theorem abs_integral_hardyAngle_add_of_ne {m n : ℕ} (hm : 0<m) (hn : 0<n) (hne : m≠n)
    {a b : ℝ} (hmA : hardyCutoff m≤a) (hnA : hardyCutoff n≤a) (hab : a≤b) :
    |∫t in a..b,Real.cos (hardyAngle m t+hardyAngle n t)|≤4/|Real.log n-Real.log m| := by
  have hcm : 0<hardyCutoff m := by dsimp [hardyCutoff];positivity
  have hcn : 0<hardyCutoff n := by dsimp [hardyCutoff];positivity
  have ha := hcm.trans_le hmA
  apply (cos_integral_le_exp ((continuous_hardyAngle m).add (continuous_hardyAngle n)) a b).trans
  apply vanDerCorput_integral_first_deriv (F':=pairSlope m n) (F'':=fun t : ℝ => t⁻¹) hab (abs_pos.mpr (sub_ne_zero.mpr (log_ne hm hn hne)))
    (fun t ht => pair_deriv m n (ha.trans_le ht.1)) (fun t ht => pairSlope_deriv m n (ha.trans_le ht.1))
    (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')) (Or.inl (fun t ht => inv_nonneg.mpr (ha.trans_le ht.1).le))
  intro t ht
  have h₁ := Real.log_le_log hcm (hmA.trans ht.1)
  have h₂ := Real.log_le_log hcn (hnA.trans ht.1)
  rw [log_cutoff hm] at h₁
  rw [log_cutoff hn] at h₂
  apply le_trans _ (le_abs_self _)
  rw [abs_le];dsimp [pairSlope];constructor <;> linarith

/-- The phase difference is linear in height; the first derivative test
therefore uses the same logarithmic spacing on every interval. -/
theorem abs_integral_hardyAngle_sub_of_ne {m n : ℕ} (hm : 0<m) (hn : 0<n) (hne : m≠n)
    {a b : ℝ} (hab : a≤b) :
    |∫t in a..b,Real.cos (hardyAngle m t-hardyAngle n t)|≤4/|Real.log n-Real.log m| := by
  let d := Real.log n-Real.log m
  have he (t : ℝ) : hardyAngle m t-hardyAngle n t=t*d := by dsimp [hardyAngle,d];ring
  simp_rw [he]
  apply (cos_integral_le_exp (continuous_id.mul continuous_const) a b).trans
  exact vanDerCorput_integral_first_deriv (F:=fun t : ℝ => t*d) (F':=fun _ => d) (F'':=fun _ => 0) hab
    (abs_pos.mpr (sub_ne_zero.mpr (log_ne hm hn hne)))
    (fun t _ => by simpa using (hasDerivAt_id t).mul_const d) (fun t _ => hasDerivAt_const _ _)
    continuousOn_const (Or.inl (fun _ _ => le_rfl)) (fun _ _ => le_rfl)

end AnalyticNumberTheory.RiemannZeta
