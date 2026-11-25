import AnalyticNumberTheory.RiemannZeta.ShiftedHardyKernels
import AnalyticNumberTheory.RiemannZeta.CriticalCosineOffDiagonal
import AnalyticNumberTheory.AnalyticTools.MovingPolynomialEnergy

/-!
# Weighted direct and reciprocal Hardy waves on a scaled integer grid

Both families may have independent complex coefficients of absolute
value at most one. A common scale leaves the logarithmic frequency
spacing unchanged.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate Interval
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

def scaledHardyAngle (d : ℝ) (n : ℕ) (t : ℝ) := hardyPhase t-t*Real.log (n/d)

def scaledHardyEntry (d : ℝ) (n : ℕ) := 2*Real.pi*((n:ℝ)/d)^2

def weightedHardyWave (d : ℝ) (w : Bool×ℕ→ℂ) (i : Bool×ℕ) (t : ℝ) :=
  (w i*(((Real.sqrt i.2)⁻¹:ℝ):ℂ))*
    Complex.exp (((if i.1 then -scaledHardyAngle d i.2 t else scaledHardyAngle d i.2 t:ℝ):ℂ)*I)

def scaledWaveIndex (N : ℕ) : Finset (Bool×ℕ) := (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 N

theorem continuous_weightedHardyWave (d : ℝ) (w : Bool×ℕ→ℂ) (i : Bool×ℕ) : Continuous (weightedHardyWave d w i) := by
  have h : Continuous hardyPhase := (((Real.continuous_mul_log.sub (continuous_const.mul continuous_id)).div_const 2).sub continuous_const)
  unfold weightedHardyWave scaledHardyAngle;split_ifs <;>fun_prop

theorem norm_weightedHardyWave (d : ℝ) (w : Bool×ℕ→ℂ) (i : Bool×ℕ) (t : ℝ) :
    ‖weightedHardyWave d w i t‖=‖w i‖*(Real.sqrt i.2)⁻¹ := by
  rw [weightedHardyWave,norm_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]

private def ph (d : ℝ) (i : Bool×ℕ) (t : ℝ) := if i.1 then -scaledHardyAngle d i.2 t else scaledHardyAngle d i.2 t

private def oscillation (f : ℝ→ℝ) (u v : ℝ) := ‖∫t in u..v,Complex.exp ((f t:ℂ)*I)‖

private theorem oscillation_neg (f : ℝ→ℝ) (u v : ℝ) :
    oscillation (fun t => -f t) u v=oscillation f u v := by
  have h (t : ℝ) : Complex.exp (((-f t:ℝ):ℂ)*I)=conj (Complex.exp ((f t:ℂ)*I)) := by
    rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I];push_cast;ring_nf
  dsimp only [oscillation];simp_rw [h];rw [intervalIntegral.intervalIntegral_conj,Complex.norm_conj]

private theorem pair_oscillation {d : ℝ} (hd : 0<d) (i j : Bool×ℕ) (hi : 0 < i.2) (hj : 0 < j.2)
    {u v : ℝ} (hu : 0<u) (huv : u≤v) (hij : i≠j) (hiu : scaledHardyEntry d i.2≤u) (hju : scaledHardyEntry d j.2≤u) :
    oscillation (fun t => ph d i t-ph d j t) u v≤
      if i.2=j.2 then 8*Real.sqrt v else 4/|Real.log j.2-Real.log i.2| := by
  let r := (i.2:ℝ)/d
  let s := (j.2:ℝ)/d
  let l := Real.log s-Real.log r
  have hi₀ := Nat.cast_pos (α:=ℝ).mpr hi
  have hj₀ := Nat.cast_pos (α:=ℝ).mpr hj
  have hl : l=Real.log j.2-Real.log i.2 := by dsimp [l,r,s];rw [Real.log_div hi₀.ne' hd.ne',Real.log_div hj₀.ne' hd.ne'];ring
  have hne (h : i.2≠j.2) : r≠s := by dsimp [r,s];intro he;exact h (Nat.cast_inj.mp ((div_left_inj' hd.ne').mp he))
  have hlin (h : i.2≠j.2) : oscillation (fun t => t*l) u v ≤ if i.2=j.2 then 8*Real.sqrt v else 4/|Real.log j.2-Real.log i.2| := by
    rw [if_neg h,←hl]
    have h₀ : l≠0 := sub_ne_zero.mpr (fun H => hne h ((Real.log_injOn_pos (div_pos hj₀ hd) (div_pos hi₀ hd) H).symm))
    simpa only [oscillation,add_zero] using norm_integral_linear_phase h₀ 0 huv
  have hsum : oscillation (shiftedHardyPhase r s 0) u v ≤ if i.2=j.2 then 8*Real.sqrt v else 4/|Real.log j.2-Real.log i.2| := by
    split_ifs with h
    · exact norm_integral_shiftedHardyPhase_le_sqrt r s 0 hu huv
    · rw [←hl];exact norm_integral_shiftedHardyPhase_of_ne (div_pos hi₀ hd) (div_pos hj₀ hd) (hne h) 0 hiu hju huv
  obtain ⟨b,m⟩ := i;obtain ⟨c,n⟩ := j;cases b <;>cases c
  · have he : (fun t => ph d (false,m) t-ph d (false,n) t)=(fun t => t*l) := by
      funext t;dsimp [ph,scaledHardyAngle,l,r,s];ring
    rw [he];exact hlin (fun e=>hij (Prod.ext rfl e))
  · have he : (fun t => ph d (false,m) t-ph d (true,n) t)=shiftedHardyPhase r s 0 := by
      funext t;dsimp [ph,scaledHardyAngle,shiftedHardyPhase,r,s];ring
    rw [he];exact hsum
  · have he : (fun t => ph d (true,m) t-ph d (false,n) t)=(fun t => -shiftedHardyPhase r s 0 t) := by
      funext t;dsimp [ph,scaledHardyAngle,shiftedHardyPhase,r,s];ring
    rw [he,oscillation_neg];exact hsum
  · have he : (fun t => ph d (true,m) t-ph d (true,n) t)=(fun t => -(t*l)) := by
      funext t;dsimp [ph,scaledHardyAngle,l,r,s];ring
    rw [he,oscillation_neg];exact hlin (fun e=>hij (Prod.ext rfl e))

/-- Absolute cost of a weighted pair after both cutoffs enter. -/
theorem weighted_hardy_pair_bound {d : ℝ} (hd : 0<d) (w : Bool×ℕ→ℂ) (hw : ∀i,‖w i‖≤1)
    (i j : Bool×ℕ) (hi : 0 < i.2) (hj : 0 < j.2) (hij : i≠j) {u v : ℝ} (hu : 0<u)
    (huv : u≤v) (hiu : scaledHardyEntry d i.2≤u) (hju : scaledHardyEntry d j.2≤u) :
    ‖∫t in u..v,weightedHardyWave d w i t*conj (weightedHardyWave d w j t)‖≤
      (if i.2=j.2 then 8*Real.sqrt v*(i.2:ℝ)⁻¹ else 0)+2*criticalCosineGap i.2 j.2 := by
  let B := fun k : Bool×ℕ => w k*(((Real.sqrt k.2)⁻¹:ℝ):ℂ)
  have h (t : ℝ) : weightedHardyWave d w i t*conj (weightedHardyWave d w j t)=
      (B i*conj (B j))*Complex.exp (((ph d i t-ph d j t:ℝ):ℂ)*I) := by
    change (B i*Complex.exp ((ph d i t:ℂ)*I))*conj (B j*Complex.exp ((ph d j t:ℂ)*I))=_
    rw [map_mul,←Complex.exp_conj,map_mul (starRingEnd ℂ) (↑(ph d j t)) I,Complex.conj_ofReal,Complex.conj_I]
    push_cast;rw [sub_mul,Complex.exp_sub,div_eq_mul_inv,←Complex.exp_neg,show ∀z:ℂ,z*(-I)= -(z*I) by intro;ring];ring
  have hB (k : Bool×ℕ) : ‖B k‖≤(Real.sqrt k.2)⁻¹ := by
    dsimp only [B];rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw k) (inv_nonneg.mpr (Real.sqrt_nonneg (k.2:ℝ)))
  simp_rw [h];rw [intervalIntegral.integral_const_mul,norm_mul,norm_mul,Complex.norm_conj]
  apply (mul_le_mul (mul_le_mul (hB i) (hB j) (norm_nonneg _) (by positivity))
    (pair_oscillation hd i j hi hj hu huv hij hiu hju) (norm_nonneg _) (by positivity)).trans
  by_cases he : i.2=j.2
  · simp only [he,ite_true,criticalCosineGap,mul_zero,add_zero]
    rw [←mul_inv_rev,←sq,Real.sq_sqrt (Nat.cast_nonneg _)];ring_nf <;>exact le_rfl
  · simp only [he,ite_false,criticalCosineGap,zero_add,Real.rpow_neg (Nat.cast_nonneg _) _,←Real.sqrt_eq_rpow]
    ring_nf <;>exact le_rfl

end AnalyticNumberTheory.RiemannZeta
