import AnalyticNumberTheory.RiemannZeta.HardyOscillation
import AnalyticNumberTheory.RiemannZeta.CriticalFirstMoment

/-!
# First moment of a Dirichlet polynomial with the Riemann–Siegel phase

The frequencies up to `2√T` cost `O(T^(3/4))` by the second derivative
test. Integrating each higher frequency by the first derivative test costs
`O(√N)` in total for a polynomial of length `N`.
-/

open Complex Real Finset Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

private noncomputable def phaseWeight (t : ℝ) := Complex.exp ((hardyPhase t:ℂ)*I)
private noncomputable def frequency (n : ℕ) (t : ℝ) :=
  Complex.exp (((hardyPhase t - t*Real.log n:ℝ):ℂ)*I)
private noncomputable def coeff (n : ℕ) := (√(n:ℝ))⁻¹

private theorem sum_coeff (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, coeff n ≤ 1+2*√(N:ℝ) := by
  rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons]
  simp only [coeff, Nat.cast_one,Real.sqrt_one,inv_one]
  exact add_le_add le_rfl (sum_inv_sqrt_le N)

private theorem weighted_term (n : ℕ) (hn : 0 < n) (t : ℝ) :
    phaseWeight t * (n:ℂ)^(-(1/2+(t:ℂ)*I)) = (coeff n:ℂ)*frequency n t := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (coeff n:ℂ) = (n:ℂ)^(-(1/2:ℂ)) := by
    dsimp [coeff]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_inv, Complex.ofReal_cpow hnr.le, Complex.cpow_neg]
    push_cast
    rfl
  rw [hc, Complex.cpow_def_of_ne_zero hnc, Complex.cpow_def_of_ne_zero hnc, phaseWeight,frequency,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.ofReal_natCast, ← Complex.ofReal_log hnr.le]
  congr 1
  push_cast
  ring

private theorem frequency_continuousOn (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (frequency n) (Set.Icc T (2*T)) := by
  have hlog : ContinuousOn Real.log (Set.Icc T (2*T)) := fun t ht =>
    (Real.continuousAt_log (hT.trans_le ht.1).ne').continuousWithinAt
  have hc : ContinuousOn hardyPhase (Set.Icc T (2*T)) := by
    unfold hardyPhase
    fun_prop
  unfold frequency
  fun_prop

/-- Elementary pointwise bound for a Dirichlet polynomial on the critical line. -/
theorem norm_criticalDirichletPoly_le (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    ‖dirichletPoly (fun _ => 1) N (1/2+(t:ℂ)*I)‖ ≤ 1+2*√(N:ℝ) := by
  simp only [dirichletPoly,one_mul]
  apply (norm_sum_le _ _).trans
  apply (sum_coeff N hN).trans'
  apply sum_le_sum
  intro n hn
  rw [Complex.norm_natCast_cpow_of_pos (Finset.mem_Icc.mp hn).1,
    show (-(1/2+(t:ℂ)*I)).re=-(1/2:ℝ) by simp,
    Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  rfl

/-- The dyadic first moment of a twisted polynomial, with an explicit stationary range. -/
theorem norm_integral_hardyPhase_mul_dirichletPoly_le (N : ℕ) (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..(2*T), Complex.exp ((hardyPhase t:ℂ)*I) *
      dirichletPoly (fun _ => 1) N (1/2+(t:ℂ)*I)‖ ≤
      16*√T*(1+2*√((⌈2*√T⌉₊:ℕ):ℝ)) + (8/Real.log 2)*(1+2*√(N:ℝ)) := by
  let M := ⌈2*√T⌉₊
  let S := Icc 1 N
  let V := S.filter (fun n => n ≤ M)
  let W := S.filter (fun n => ¬n ≤ M)
  let A (n : ℕ) := (coeff n:ℂ)*(∫ t in T..(2*T), frequency n t)
  have hT0 : 0 < T := by linarith
  have hab : T ≤ 2*T := by linarith
  have hrepr (t : ℝ) : Complex.exp ((hardyPhase t:ℂ)*I) *
      dirichletPoly (fun _ => 1) N (1/2+(t:ℂ)*I) = ∑ n ∈ S, (coeff n:ℂ)*frequency n t := by
    unfold dirichletPoly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simpa only [one_mul,phaseWeight] using weighted_term n (Finset.mem_Icc.mp hn).1 t
  simp_rw [hrepr]
  have hi (n : ℕ) : IntervalIntegrable (fun t : ℝ => (coeff n:ℂ)*frequency n t) volume T (2*T) :=
    (continuousOn_const.mul (frequency_continuousOn n hT0)).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_finsetSum (s := S) (fun n _ => hi n)]
  simp_rw [intervalIntegral.integral_const_mul]
  change ‖∑ n ∈ S, A n‖ ≤ _
  have hM : 1 ≤ M := by
    have h : 1 ≤ √T := by simpa using Real.sqrt_le_sqrt hT
    have hM' : 2*√T ≤ M := Nat.le_ceil _
    exact_mod_cast (show (1:ℝ) ≤ M by linarith)
  have hc (n : ℕ) : 0 ≤ coeff n := by dsimp [coeff]; positivity
  have hnorm (n : ℕ) : ‖A n‖ = coeff n*‖∫ t in T..(2*T), frequency n t‖ := by
    simp only [A,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc n)]
  have hV : ∑ n ∈ V, ‖A n‖ ≤ (16*√T)*(1+2*√(M:ℝ)) := by
    calc _ ≤ ∑ n ∈ V, (16*√T)*coeff n := by
           apply sum_le_sum
           intro n hn
           rw [hnorm,mul_comm]
           exact mul_le_mul_of_nonneg_right (norm_integral_hardyPhase_sub_log_le_sqrt n hT0) (hc n)
         _ ≤ ∑ n ∈ Icc 1 M, (16*√T)*coeff n := by
           apply sum_le_sum_of_subset_of_nonneg _ (fun n hn _ => by positivity [hc n])
           intro n hn
           obtain ⟨hnS,hnM⟩ := mem_filter.mp hn
           exact mem_Icc.mpr ⟨(mem_Icc.mp hnS).1, hnM⟩
         _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_coeff M hM) (by positivity)
  have hW : ∑ n ∈ W, ‖A n‖ ≤ (8/Real.log 2)*(1+2*√(N:ℝ)) := by
    calc _ ≤ ∑ n ∈ W, (8/Real.log 2)*coeff n := by
           apply sum_le_sum
           intro n hn
           have h : M < n := Nat.lt_of_not_ge (mem_filter.mp hn).2
           have h' : 2*√T ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast h.le)
           rw [hnorm,mul_comm]
           exact mul_le_mul_of_nonneg_right (norm_integral_hardyPhase_sub_log_le_const hT0 h') (hc n)
         _ ≤ ∑ n ∈ S, (8/Real.log 2)*coeff n := by
           apply sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun n hn _ => by positivity [hc n])
         _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_coeff N hN) (by positivity)
  have hsum := Finset.sum_filter_add_sum_filter_not S (fun n => n ≤ M) (fun n => ‖A n‖)
  exact (norm_sum_le _ _).trans (hsum.symm.le.trans (add_le_add hV hW))

end AnalyticNumberTheory.RiemannZeta
