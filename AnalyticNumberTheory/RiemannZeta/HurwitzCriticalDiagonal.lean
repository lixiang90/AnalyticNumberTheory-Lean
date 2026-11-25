import AnalyticNumberTheory.AnalyticTools.ShiftedHarmonicRemainder
import AnalyticNumberTheory.RiemannZeta.CriticalDiagonalIntegral

/-!
# The linear term in the shifted critical-line diagonal

The direct polynomial contributes the constant −ψ(a), while the
Fourier polynomial contributes Euler's constant. The error in comparing
with the unshifted diagonal is uniform over 0<a≤1.
-/
noncomputable section
open Real Finset MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.RiemannZeta

def hurwitzCriticalDiagonal (a t : ℝ) :=
  let x := Real.sqrt (t/(2*Real.pi))
  (∑n∈range (⌊x-a⌋₊+1),1/((n:ℝ)+a))+(harmonic ⌊x⌋₊:ℝ)

private theorem harmonic_summation (N : ℕ) : (harmonic N:ℝ)=∑n∈Finset.Icc 1 N,(n:ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc,Rat.cast_sum]
  apply sum_congr rfl;intro i _;simp

theorem hurwitzCriticalDiagonal_monotone {a : ℝ} (ha : 0<a) : Monotone (hurwitzCriticalDiagonal a) := by
  intro t u ht
  let x := Real.sqrt (t/(2*Real.pi))
  let y := Real.sqrt (u/(2*Real.pi))
  have hx : x≤y := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ht (by positivity))
  apply add_le_add
  · apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ (Nat.floor_mono (sub_le_sub_right hx a))))
    intro n _ _;positivity
  · rw [harmonic_summation,harmonic_summation]
    apply sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hx))
    intro n _ _;positivity

/-- The shift-dependent part of the diagonal is linear in T, with an
explicit error independent of the shift. -/
theorem hurwitz_diagonal_shift_error {a T : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hT : 8*Real.pi≤T) :
    |(∫t in (8*Real.pi)..T,hurwitzCriticalDiagonal a t)-
      (∫t in (8*Real.pi)..T,2*∑n∈Finset.Icc 1 ⌊Real.sqrt (t/(2*Real.pi))⌋₊,(n:ℝ)⁻¹)-
      (T-8*Real.pi)*(-realDigamma a-Real.eulerMascheroniConstant)|≤10*Real.sqrt (2*Real.pi)*Real.sqrt T := by
  let b := 8*Real.pi
  let U := fun t : ℝ => 2*(harmonic ⌊Real.sqrt (t/(2*Real.pi))⌋₊:ℝ)
  let g := fun t : ℝ => 5*Real.sqrt (2*Real.pi)/Real.sqrt t
  let c := -realDigamma a-Real.eulerMascheroniConstant
  have hb : 0<b := by dsimp [b];positivity
  have hu : Monotone U := by
    intro s t h;dsimp [U];rw [harmonic_summation,harmonic_summation]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right h (by positivity))))) (fun _ _ _ => by positivity)
  have hpt {t : ℝ} (ht : b≤t) : |hurwitzCriticalDiagonal a t-U t-c|≤g t := by
    let x := Real.sqrt (t/(2*Real.pi))
    have hπ : 0<2*Real.pi := by positivity
    have hx : 2≤x := Real.le_sqrt_of_sq_le ((le_div_iff₀ hπ).mpr (by dsimp [b] at ht;linarith))
    have H := shifted_harmonic_floor_remainder ha hx
    have K := harmonic_floor_remainder (by linarith : 0<x)
    change |((∑n∈range (⌊x-a⌋₊+1),1/((n:ℝ)+a))+(harmonic ⌊x⌋₊:ℝ))-2*(harmonic ⌊x⌋₊:ℝ)-c|≤_
    have hg : g t=5/x := by
      dsimp [g,x];rw [Real.sqrt_div (hb.trans_le ht).le];field_simp
    rw [hg,abs_le]
    rw [abs_le] at H K;dsimp [c];simp only [div_eq_mul_inv,one_mul] at H K ⊢
    constructor <;> linarith only [H.1,H.2,K.1,K.2]
  have hgc : ContinuousOn g (uIcc b T) := by
    intro t ht;rw [uIcc_of_le (show b≤T from hT)] at ht
    dsimp [g];fun_prop (disch := positivity [hb.trans_le ht.1])
  have H := intervalIntegral.norm_integral_le_of_norm_le (f:=fun t => hurwitzCriticalDiagonal a t-U t-c)
    (g:=g) (μ:=volume) (show b≤T from hT) (Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs];exact hpt ht.1.le)) hgc.intervalIntegrable
  have hD : IntervalIntegrable (hurwitzCriticalDiagonal a) volume b T := (hurwitzCriticalDiagonal_monotone ha.1).intervalIntegrable
  have hU : IntervalIntegrable U volume b T := hu.intervalIntegrable
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub (f:=fun t=>hurwitzCriticalDiagonal a t-U t) (g:=fun _=>c)
    (hD.sub hU) (continuous_const.intervalIntegrable ..),intervalIntegral.integral_sub hD hU,
    intervalIntegral.integral_const,smul_eq_mul] at H
  have hg : (∫t in b..T,g t)=10*Real.sqrt (2*Real.pi)*Real.sqrt T-10*Real.sqrt (2*Real.pi)*Real.sqrt b := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t => 10*Real.sqrt (2*Real.pi)*Real.sqrt t) _ hgc.intervalIntegrable
    intro t ht;rw [uIcc_of_le (show b≤T from hT)] at ht
    convert (Real.hasDerivAt_sqrt (hb.trans_le ht.1).ne').const_mul (10*Real.sqrt (2*Real.pi)) using 1;dsimp [g];ring
  rw [hg] at H
  have hU' : U=(fun t : ℝ => 2*∑n∈Finset.Icc 1 ⌊Real.sqrt (t/(2*Real.pi))⌋₊,(n:ℝ)⁻¹) := by
    funext t;dsimp [U];rw [harmonic_summation]
  rw [←hU']
  exact H.trans (sub_le_self _ (by positivity))

/-- The integrated Hurwitz diagonal with its explicit digamma secondary
term for each positive shift up to one. -/
theorem hurwitz_critical_diagonal_expansion {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) :
    ∃ C : ℝ,0<C ∧ ∀{T : ℝ},8*Real.pi≤T →
    |(∫t in (8*Real.pi)..T,hurwitzCriticalDiagonal a t)-
      (T*Real.log (T/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T)|≤C*Real.sqrt T := by
  obtain ⟨D,hD,H⟩ := critical_diagonal_integral_error
  let c := -realDigamma a-Real.eulerMascheroniConstant
  let b := 8*Real.pi
  refine ⟨10*Real.sqrt (2*Real.pi)+D+|b*c|,by positivity,?_⟩
  intro T ht
  let I := ∫t in b..T,hurwitzCriticalDiagonal a t
  let J := ∫t in b..T,2*∑n∈Finset.Icc 1 ⌊Real.sqrt (t/(2*Real.pi))⌋₊,(n:ℝ)⁻¹
  let F := T*Real.log (T/(2*Real.pi))+(2*Real.eulerMascheroniConstant-1)*T
  have h := hurwitz_diagonal_shift_error ha ht
  change |I-J-(T-b)*c|≤_ at h
  have hh : |J-F|≤D*Real.sqrt T := H T ht
  have he : I-(T*Real.log (T/(2*Real.pi))+(Real.eulerMascheroniConstant-realDigamma a-1)*T)=
      (I-J-(T-b)*c)+(J-F)-b*c := by dsimp only [c,F];ring
  change |I-_|≤_
  rw [he]
  have hs := le_mul_of_one_le_right (abs_nonneg (b*c)) (show 1≤Real.sqrt T from Real.le_sqrt_of_sq_le (by linarith [Real.pi_gt_three]))
  linarith only [abs_sub ((I-J-(T-b)*c)+(J-F)) (b*c),abs_add_le (I-J-(T-b)*c) (J-F),h,hh,hs]

end AnalyticNumberTheory.RiemannZeta
