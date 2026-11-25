import AnalyticNumberTheory.RiemannZeta.HurwitzBoundedHeight
import AnalyticNumberTheory.RiemannZeta.HurwitzWaveComparison
import AnalyticNumberTheory.AnalyticTools.ShiftedHarmonicRemainder

/-!
# The initial part of the Hurwitz second moment

The norm of the first Dirichlet-series term is a⁻¹ᐟ² on the critical line.
Removing its square before integration preserves the square-root
dependence of the remainder as the shift tends to zero.
-/

noncomputable section
open Real Complex MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.RiemannZeta

/-- Squared modulus of Hurwitz zeta on the critical line. -/
def hurwitzCriticalEnergy (a t : ℝ) :=
  ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2

theorem continuous_hurwitzCriticalEnergy (a : ℝ) : Continuous (hurwitzCriticalEnergy a) :=
  (continuous_hurwitz_critical_line a).norm.pow 2

/-- Uniform approximation to the second moment on any bounded interval
starting at zero, retaining the singular first term T/a exactly. -/
theorem hurwitz_critical_initial_moment (U : ℝ) :
    ∃ K : ℝ,0<K ∧ ∀ {T a : ℝ}, 0≤T → T≤U → a∈Ioc (0:ℝ) 1 →
      |(∫t in (0:ℝ)..T,hurwitzCriticalEnergy a t)-T/a|≤K*T*((√a)⁻¹+1) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_bounded_height U
  refine ⟨2*C+C^2,by positivity,?_⟩
  intro T a hT hU ha
  let r := (√a)⁻¹
  have hr : 0<r := inv_pos.mpr (sqrt_pos.2 ha.1)
  have hpt (t : ℝ) (ht : 0≤t) (ht' : t≤T) : |hurwitzCriticalEnergy a t-1/a|≤(2*C+C^2)*(r+1) := by
    let s := (1/2:ℂ)+t*I
    let z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s
    let w := (a:ℂ)^(-s)
    have hnorm : ‖w‖=r := by
      dsimp [w,r];rw [Complex.norm_cpow_eq_rpow_re_of_pos ha.1,neg_re,show s.re=1/2 by simp [s],
        Real.rpow_neg ha.1.le,←Real.sqrt_eq_rpow]
    have hc : ‖z-w‖≤C := H ha (by rw [abs_of_nonneg ht];exact ht'.trans hU)
    have hd := (abs_norm_sub_norm_le z w).trans hc
    rw [hnorm] at hd
    have hs : r^2=1/a := by rw [one_div,←Real.sq_sqrt ha.1.le];dsimp [r];rw [inv_pow]
    change |‖z‖^2-1/a|≤_
    rw [←hs,sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) hr.le)]
    calc _ ≤ (C+2*r)*C := mul_le_mul (by linarith [(abs_le.mp hd).2]) hd (abs_nonneg _) (by positivity)
         _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg C) hr.le]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=T)
    (f:=fun t => hurwitzCriticalEnergy a t-1/a) (C:=(2*C+C^2)*(r+1)) (by
      intro t ht
      rw [Set.uIoc_of_le hT] at ht
      simpa only [Real.norm_eq_abs] using hpt t ht.1.le ht.2)
  rw [intervalIntegral.integral_sub ((continuous_hurwitzCriticalEnergy a).intervalIntegrable ..) (by simp),
    intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one_div,Real.norm_eq_abs,abs_of_nonneg hT] at hi
  exact hi.trans_eq (by ring)

/-- The singular main term at a bounded height cancels against the
digamma coefficient appearing in the diagonal integral. -/
theorem hurwitz_initial_digamma_error (U : ℝ) :
    ∃ K : ℝ,0<K ∧ ∀ {T a : ℝ}, 0≤T → T≤U → a∈Ioc (0:ℝ) 1 →
      |(∫t in (0:ℝ)..T,hurwitzCriticalEnergy a t)-T*(-realDigamma a-Real.eulerMascheroniConstant)|
        ≤ K*T*((√a)⁻¹+1) := by
  obtain ⟨C,hC,HC⟩ := hurwitz_critical_initial_moment U
  let d := 2+2*|Real.eulerMascheroniConstant|
  have hd : 0<d := by dsimp [d];positivity
  refine ⟨C+d,by positivity,?_⟩
  intro T a hT hU ha
  let M := ∫t in (0:ℝ)..T,hurwitzCriticalEnergy a t
  have hψ := abs_realDigamma_add_inv_le ha
  have hψ' : |realDigamma a+1/a+Real.eulerMascheroniConstant|≤d :=
    (abs_add_le ..).trans (by dsimp [d];linarith only [hψ])
  have he : M-T*(-realDigamma a-Real.eulerMascheroniConstant)=
      (M-T/a)+T*(realDigamma a+1/a+Real.eulerMascheroniConstant) := by ring
  rw [show (∫t in (0:ℝ)..T,hurwitzCriticalEnergy a t)=M by rfl,he]
  refine (abs_add_le ..).trans ?_
  rw [abs_mul,abs_of_nonneg hT]
  have hplus : 0≤d*T*(√a)⁻¹ := by positivity
  have hh : |M-T/a|≤C*T*((√a)⁻¹+1) := HC hT hU ha
  linarith only [hh,mul_le_mul_of_nonneg_left hψ' hT,hplus]

end AnalyticNumberTheory.RiemannZeta
