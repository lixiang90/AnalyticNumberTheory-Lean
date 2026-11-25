import AnalyticNumberTheory.RiemannZeta.RiemannSiegelFirstCorrection
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks

/-!
# The elementary phase in the Riemann–Siegel cosine sum

Replacing the exact gamma phase by its Stirling approximation changes
the entire sharp cosine sum by O(t^(-3/4)). This preserves the precision
of the first corrected formula.
-/
open Real Complex Finset
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

private theorem abs_cosine_shift_error {t : ℝ} (ht : 2≤t) (w : ℝ) :
    |Real.cos ((hardyGammaUnit t).arg-w)-Real.cos (hardyPhase t-w)|≤4/t := by
  let U := hardyGammaUnit t
  have hU : Complex.exp ((U.arg:ℂ)*I)=U := by
    have H := Complex.norm_mul_exp_arg_mul_I U
    rw [norm_hardyGammaUnit] at H;simpa using H
  have hcos (p : ℝ) : Real.cos (p-w)=(Complex.exp ((p:ℂ)*I)*Complex.exp (((-w:ℝ):ℂ)*I)).re := by
    rw [←Complex.exp_add,show (p:ℂ)*I+((-w:ℝ):ℂ)*I=((p-w:ℝ):ℂ)*I by push_cast;ring,Complex.exp_ofReal_mul_I_re]
  change |Real.cos (U.arg-w)-Real.cos (hardyPhase t-w)|≤_
  rw [hcos,hcos,hU,←Complex.sub_re,←sub_mul]
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
  exact norm_hardyGammaUnit_sub_exp_le ht

private theorem sum_succ_to_Icc {R : Type*} [AddCommMonoid R] (f : ℕ→R) (N : ℕ) :
    (∑m∈range N,f (m+1))=∑n∈Icc 1 N,f n := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,sum_Icc_succ_top (by omega),ih]

private theorem phase_sum_error {t : ℝ} (ht : 2≤t) (N : ℕ) :
    |(2*∑m∈range N,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1))-
      (2*∑n∈Icc 1 N,Real.cos (hardyPhase t-t*Real.log n)/Real.sqrt n)|≤16/t*Real.sqrt N := by
  have hsum := sum_succ_to_Icc (fun n : ℕ => Real.cos ((hardyGammaUnit t).arg-t*Real.log n)/Real.sqrt n) N
  simp only [Nat.cast_add,Nat.cast_one] at hsum
  rw [hsum,←mul_sub,←sum_sub_distrib,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have H : (∑n∈Icc 1 N, |Real.cos ((hardyGammaUnit t).arg-t*Real.log n)/Real.sqrt n-
      Real.cos (hardyPhase t-t*Real.log n)/Real.sqrt n|)≤(4/t)*(2*Real.sqrt N) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (sum_Icc_inv_sqrt_le N) (by positivity))
    rw [mul_sum];apply sum_le_sum
    intro n hn
    rw [←sub_div,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (abs_cosine_shift_error ht _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans H) (by norm_num : (0:ℝ)≤2)).trans_eq
  ring

private theorem phase_sum_height {t : ℝ} (ht : 8*Real.pi≤t) :
    let x := Real.sqrt (t/(2*Real.pi))
    16/t*Real.sqrt ⌊x⌋₊≤16*t^(-(3/4:ℝ)) := by
  intro x
  have hp : 0<t := (by positivity : 0<8*Real.pi).trans_le ht
  have hx : 0≤x := Real.sqrt_nonneg _
  have H : Real.sqrt ⌊x⌋₊≤t^(1/4:ℝ) := by
    apply (Real.sqrt_le_sqrt (Nat.floor_le hx)).trans
    dsimp only [x]
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul (by positivity : 0≤t/(2*Real.pi)),
      show (1/2:ℝ)*(1/2)=1/4 by norm_num]
    exact Real.rpow_le_rpow (by positivity) (div_le_self hp.le (by linarith [Real.pi_gt_three])) (by norm_num)
  apply (mul_le_mul_of_nonneg_left H (by positivity : 0≤16/t)).trans_eq
  rw [show -(3/4:ℝ)=1/4-1 by norm_num,Real.rpow_sub_one hp.ne'];ring

/-- The corrected Riemann–Siegel formula in terms of the elementary
Stirling phase and a cosine sum indexed by positive integers. -/
theorem hardyZ_elementary_first_correction : ∃ C : ℝ,0<C ∧ ∀ {t : ℝ},8*Real.pi≤t →
    let x := Real.sqrt (t/(2*Real.pi))
    let N := ⌊x⌋₊
    |hardyZ t-(2*∑n∈Icc 1 N,Real.cos (hardyPhase t-t*Real.log n)/Real.sqrt n)-
      (-1:ℝ)^(N+1)*(Real.sqrt x)⁻¹*riemannSiegelCorrection (2*(x-N))|≤C*t^(-(3/4:ℝ)) := by
  obtain ⟨C,hC,H⟩ := hardyZ_riemannSiegel_first_correction
  refine ⟨C+16,by positivity,?_⟩
  intro t ht x N
  have h := H ht
  have hphase := (phase_sum_error (by linarith [Real.pi_gt_three] : 2≤t) N).trans (phase_sum_height ht)
  let a := 2*∑m∈range N,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1)
  let b := 2*∑n∈Icc 1 N,Real.cos (hardyPhase t-t*Real.log n)/Real.sqrt n
  let R := (-1:ℝ)^(N+1)*(Real.sqrt x)⁻¹*riemannSiegelCorrection (2*(x-N))
  change |hardyZ t-a-R|≤_ at h
  change |a-b|≤_ at hphase
  change |hardyZ t-b-R|≤_
  rw [show hardyZ t-b-R=(hardyZ t-a-R)+(a-b) by ring]
  linarith only [abs_add_le (hardyZ t-a-R) (a-b),h,hphase]

/-- The elementary cosine polynomial approximates Hardy's function with
error O(t^(-1/4)), uniformly for t≥8π. -/
theorem hardyZ_elementary_cosine_error : ∃ C : ℝ,0<C ∧ ∀ {t : ℝ},8*Real.pi≤t →
    |hardyZ t-(2*∑n∈Icc 1 ⌊Real.sqrt (t/(2*Real.pi))⌋₊,Real.cos (hardyPhase t-t*Real.log n)/Real.sqrt n)|≤
      C*t^(-(1/4:ℝ)) := by
  let C := 604*(2*Real.pi)^(1/4:ℝ)
  exact ⟨C+16,by dsimp [C];positivity,by
    intro t ht
    have hp : 1≤t := by linarith [Real.pi_gt_three]
    have H := hardyZ_riemannSiegel_cosine (t:=t) (by rwa [abs_of_pos (by linarith : 0<t)])
    simp only [abs_of_pos (by linarith : 0<t)] at H
    let N := ⌊Real.sqrt (t/(2*Real.pi))⌋₊
    let a := 2*∑m∈range N,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1)
    let b := 2*∑n∈Icc 1 N,Real.cos (hardyPhase t-t*Real.log n)/Real.sqrt n
    change |hardyZ t-a|≤C*t^(-(1/4:ℝ)) at H
    have hphase := (phase_sum_error (by linarith [Real.pi_gt_three] : 2≤t) N).trans (phase_sum_height ht)
    change |a-b|≤_ at hphase
    change |hardyZ t-b|≤_
    linarith only [abs_sub_le (hardyZ t) a b,H,hphase,Real.rpow_le_rpow_of_exponent_le hp (by norm_num : -(3/4:ℝ)≤ -(1/4))]⟩

end AnalyticNumberTheory.RiemannZeta
