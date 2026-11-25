import AnalyticNumberTheory.RiemannZeta.HurwitzMomentInitial
import AnalyticNumberTheory.RiemannZeta.HurwitzUniformSecondMoment
import AnalyticNumberTheory.RiemannZeta.CriticalDiagonalIntegral

/-!
# Uniform two-term Hurwitz second moment at all heights

The linear coefficient is γ − ψ(a) − 1. Clipping the logarithm at a
fixed height B gives a formula valid from T = 0 onwards, with an error
linear in T at small heights and of square-root order at large heights.
-/

noncomputable section
open Real Complex Set MeasureTheory
open scoped Interval
open AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.RiemannZeta

private theorem hurwitz_high_moment :
    ∃ C : ℝ,0<C ∧ ∀ {a T : ℝ}, a∈Ioc (0:ℝ) 1 → 8*Real.pi≤T →
      |(∫t in (0:ℝ)..T,hurwitzCriticalEnergy a t)-
        (T*Real.log (T/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T)|
        ≤ C*√T*((√a)⁻¹+Real.log T) := by
  let b := 8*Real.pi
  obtain ⟨A,hA,HA⟩ := hurwitz_initial_digamma_error b
  obtain ⟨B,hB,HB⟩ := hurwitz_critical_diagonal_uniform
  obtain ⟨D,hD,HD⟩ := critical_diagonal_integral_error
  let F := 10*√(2*Real.pi)
  have hb : 3≤b := by dsimp [b];linarith [Real.pi_gt_three]
  have hF : 0<F := by dsimp [F];positivity
  have hb0 : 0<b := by linarith
  refine ⟨A*b+2*B+F+D,by positivity,?_⟩
  intro a T ha hT
  let E := hurwitzCriticalEnergy a
  let r := (√a)⁻¹
  let u := Real.log T
  let V := √T*(r+u)
  let Z := ∫t in b..T,E t
  let I₀ := ∫t in (0:ℝ)..b,E t
  let Da := ∫t in b..T,hurwitzCriticalDiagonal a t
  let D₁ := ∫t in b..T,2*∑n∈Finset.Icc 1 ⌊√(t/(2*Real.pi))⌋₊,(n:ℝ)⁻¹
  let c := -realDigamma a-Real.eulerMascheroniConstant
  let M := T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T
  have hT' : b≤T := hT
  have ht : 3≤T := hb.trans hT'
  have hl : 1≤u := (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans ht)
  have hs : 1≤√T := Real.le_sqrt_of_sq_le (by linarith)
  have hr : 0≤r := inv_nonneg.mpr (sqrt_nonneg _)
  have hsum : 1≤r+u := by linarith
  have hlow := HA (show 0≤b by linarith) le_rfl ha
  change |I₀-b*c|≤A*b*(r+1) at hlow
  have hV : r+1≤V := (by linarith : r+1≤r+u).trans (le_mul_of_one_le_left (by linarith) hs)
  have hV' : √T≤V := le_mul_of_one_le_right (sqrt_nonneg _) hsum
  have h₀ := hlow.trans (mul_le_mul_of_nonneg_left hV (mul_nonneg hA.le hb0.le))
  have h₁ := HB ha hT
  change |∫t in b..T,E t-hurwitzCriticalDiagonal a t|≤B*√T*(r+(1+u)) at h₁
  rw [intervalIntegral.integral_sub ((continuous_hurwitzCriticalEnergy a).intervalIntegrable ..)
    (hurwitzCriticalDiagonal_monotone ha.1).intervalIntegrable] at h₁
  change |Z-Da|≤_ at h₁
  have h₁' : |Z-Da|≤(2*B)*V := by
    calc _ ≤ B*√T*(r+(1+u)) := h₁
         _ ≤ B*√T*(2*(r+u)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
         _ = _ := by dsimp [V];ring
  have h₂ := hurwitz_diagonal_shift_error ha hT
  change |Da-D₁-(T-b)*c|≤F*√T at h₂
  have h₂' := h₂.trans (mul_le_mul_of_nonneg_left hV' hF.le)
  have h₃ := HD T hT
  change |D₁-M|≤D*√T at h₃
  have h₃' := h₃.trans (mul_le_mul_of_nonneg_left hV' hD.le)
  have he : (∫t in (0:ℝ)..T,E t)=I₀+Z :=
    (intervalIntegral.integral_add_adjacent_intervals ((continuous_hurwitzCriticalEnergy a).intervalIntegrable ..)
      ((continuous_hurwitzCriticalEnergy a).intervalIntegrable ..)).symm
  rw [mul_assoc (A*b+2*B+F+D)]
  change |(∫t in (0:ℝ)..T,E t)-_|≤(A*b+2*B+F+D)*V
  rw [he,show T*Real.log (T/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T=M+T*c by dsimp [M,c];ring]
  rw [abs_le] at h₀ h₁' h₂' h₃' ⊢
  constructor <;>linarith only [h₀.1,h₀.2,h₁'.1,h₁'.2,h₂'.1,h₂'.2,h₃'.1,h₃'.2]

/-- Uniform two-term expansion of the Hurwitz critical-line second moment,
for every positive shift up to one and every nonnegative height. The
implied constant depends only on the fixed logarithmic cutoff B ≥ 3. -/
theorem hurwitz_second_moment_uniform {B : ℝ} (hB : 3≤B) :
    ∃ C : ℝ,0<C ∧ ∀ {a T : ℝ}, a∈Ioc (0:ℝ) 1 → 0≤T →
      |(∫t in (0:ℝ)..T,hurwitzCriticalEnergy a t)-
        (T*Real.log (max T B/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T)|
        ≤ C*(√T*min 1 (√T))*((√a)⁻¹+Real.log (max T B)) := by
  let U := max B (8*Real.pi)
  have hU := le_max_left B (8*Real.pi)
  have hu : 3≤U := hB.trans hU
  obtain ⟨A,hA,HA⟩ := hurwitz_high_moment
  obtain ⟨K,hK,HK⟩ := hurwitz_initial_digamma_error U
  let J := Real.log U+|Real.log (2*Real.pi)|+2*|Real.eulerMascheroniConstant|+1
  have hJ : 0<J := by
    have := Real.log_nonneg (show 1≤U by linarith);dsimp [J];positivity
  let D := (K+J)*(√U+1)
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨max A D,hA.trans_le (le_max_left ..),?_⟩
  intro a T ha ht
  let t := max T B
  let l := Real.log t
  let r := (√a)⁻¹
  let w := √T*min 1 (√T)
  have ht3 : 3≤t := hB.trans (le_max_right ..)
  have hl : 1≤l := (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans ht3)
  have hr : 0≤r := inv_nonneg.mpr (sqrt_nonneg _)
  have hw : 0≤w := mul_nonneg (sqrt_nonneg _) (le_min zero_le_one (sqrt_nonneg _))
  have hr' : 1≤r+l := by linarith
  by_cases hlarge : U≤T
  · have hBT : B≤T := hU.trans hlarge
    have hT : 8*Real.pi≤T := (le_max_right ..).trans hlarge
    have hs : 1≤√T := le_sqrt_of_sq_le (by linarith)
    rw [max_eq_left hBT,min_eq_left hs,mul_one]
    have hnn : 0≤(√a)⁻¹+Real.log T := add_nonneg hr (Real.log_nonneg (by linarith [Real.pi_gt_three]))
    exact (HA ha hT).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left A D) (sqrt_nonneg T)) hnn)
  have hTU : T≤U := (not_le.mp hlarge).le
  have htU : t≤U := max_le hTU hU
  have hscale : T≤(√U+1)*w := by
    by_cases hs : √T≤1
    · dsimp [w];rw [min_eq_right hs,Real.mul_self_sqrt ht]
      exact le_mul_of_one_le_left ht (by linarith [sqrt_nonneg U])
    · dsimp [w];rw [min_eq_left (not_le.mp hs).le,mul_one]
      calc T = √T*√T := (Real.mul_self_sqrt ht).symm
           _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [sqrt_le_sqrt hTU]) (sqrt_nonneg _)
  have hlog : |Real.log (t/(2*Real.pi))+2*Real.eulerMascheroniConstant-1|≤J := by
    rw [Real.log_div (by linarith : t≠0) (by positivity : 2*Real.pi≠0)]
    have hlU := Real.log_le_log (by linarith : 0<t) htU
    have hl0 : 0≤Real.log t := by change 0≤l;linarith
    dsimp [J];rw [abs_le]
    constructor <;> linarith [abs_nonneg (Real.log (2*Real.pi)),abs_nonneg Real.eulerMascheroniConstant,
      le_abs_self (Real.log (2*Real.pi)),neg_abs_le (Real.log (2*Real.pi)),le_abs_self Real.eulerMascheroniConstant,
      neg_abs_le Real.eulerMascheroniConstant]
  let I₀ := ∫t in (0:ℝ)..T,hurwitzCriticalEnergy a t
  let c := -realDigamma a-Real.eulerMascheroniConstant
  have hh : |I₀-T*c|≤K*T*(r+1) := HK ht hTU ha
  have he : T*Real.log (t/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T=
      T*c+T*(Real.log (t/(2*Real.pi))+2*Real.eulerMascheroniConstant-1) := by dsimp [c];ring
  change |I₀-_|≤max A D*w*(r+l)
  rw [he,←sub_sub]
  refine (abs_sub ..).trans ?_
  rw [abs_mul,abs_of_nonneg ht]
  calc _ ≤ K*T*(r+1)+T*J := add_le_add hh (mul_le_mul_of_nonneg_left hlog ht)
       _ ≤ K*T*(r+l)+J*T*(r+l) := by
             have hj := le_mul_of_one_le_right (mul_nonneg hJ.le ht) hr'
             nlinarith only [hj,mul_le_mul_of_nonneg_left (show r+1≤r+l by linarith) (mul_nonneg hK.le ht)]
       _ = (K+J)*T*(r+l) := by ring
       _ ≤ (K+J)*((√U+1)*w)*(r+l) := by gcongr
       _ = D*w*(r+l) := by dsimp [D];ring
       _ ≤ _ := by gcongr;exact le_max_right ..

end AnalyticNumberTheory.RiemannZeta
