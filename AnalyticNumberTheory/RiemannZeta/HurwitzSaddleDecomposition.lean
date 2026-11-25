import AnalyticNumberTheory.RiemannZeta.HurwitzGeometricTails
import AnalyticNumberTheory.RiemannZeta.HurwitzRotatedHeads
import AnalyticNumberTheory.RiemannZeta.HurwitzFrequencyWindow

/-!
# Separating the saddle contour in the sharp Hurwitz formula

Placing the direct cutoff halfway between consecutive lattice points removes
the paired Fourier endpoint terms exactly. Only the positive-frequency heads
remain when the complete gamma modes are subtracted.
-/
noncomputable section
open Real Complex MeasureTheory Filter Finset Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

private theorem paired_modes_half (s : ℂ) (a b : ℝ) (m j : ℕ) (hb : b=a+m+1/2) :
    hurwitzCorrectedMode a b s (hurwitzOmega j)+hurwitzCorrectedMode a b s (-hurwitzOmega j)=
      hurwitzShift a (hurwitzOmega j)*hurwitzTail s (hurwitzOmega j) b+
      hurwitzShift a (-hurwitzOmega j)*hurwitzTail s (-hurwitzOmega j) b := by
  have h (k : ℝ) (hk : k=1 ∨ k= -1) :
      hurwitzShift a (k*hurwitzOmega j)*hurwitzMode s (k*hurwitzOmega j) b =
      (b:ℂ)^(-s)*(-1)^(j+1) := by
    have H := shiftedRayMode_eq_geometric s a b m (j+1) hb hk (0:ℝ)
    rw [show 2*Real.pi*k*(j+1:ℕ)=k*hurwitzOmega j by unfold hurwitzOmega;push_cast;ring] at H
    simpa [hurwitzRay,hurwitzRayRatio,fourierPowerMode_ofReal] using H
  have hp := h 1 (.inl rfl)
  have hn := h (-1) (.inr rfl)
  simp only [one_mul,neg_one_mul] at hp hn
  have hf : hurwitzFrequency (-(hurwitzOmega j))= -hurwitzFrequency (hurwitzOmega j) := by unfold hurwitzFrequency;push_cast;ring
  simp only [hurwitzCorrectedMode,mul_sub,←mul_div_assoc]
  rw [hp,hn,hf,div_neg];ring

/-- Full tail decomposition prior to turning the finitely many low modes. -/
theorem hurwitzZeta_sub_half_cutoff {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) {a b : ℝ}
    (ha : a∈Ioc (0:ℝ) 1) (m q : ℕ) (hb : b=a+m+1/2) :
    HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a b s =
      -(b:ℂ)^(1-s)/(1-s)+hurwitzGeometricTail s b 1 q+hurwitzGeometricTail s b (-1) 0+
        ∑ j∈range q,hurwitzShift a (hurwitzOmega j)*hurwitzTail s (hurwitzOmega j) b := by
  have hab : a≤b := by rw [hb];linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hb' := ha.1.trans_le hab
  have H := (hurwitzZeta_hasSum_correctedModes ha hab hσ hσ').tendsto_sum_nat
  simp_rw [paired_modes_half s a b m _ hb] at H
  have hsaw : sawtooth (b-a)=0 := by
    have hv : b-a=(m:ℝ)+1/2 := by rw [hb];ring
    rw [hv,sawtooth,show (m:ℝ)=((m:ℤ):ℝ) by simp,Int.fract_intCast_add,Int.fract_eq_self.mpr (by norm_num : 1/2∈Ico (0:ℝ) 1)]
    ring
  simp only [hsaw,Complex.ofReal_zero,zero_mul,sub_zero] at H
  let P (j : ℕ) := hurwitzShift a (hurwitzOmega j)*hurwitzTail s (hurwitzOmega j) b
  let N (j : ℕ) := hurwitzShift a (-hurwitzOmega j)*hurwitzTail s (-hurwitzOmega j) b
  have hL := (tendsto_hurwitz_shifted_tails hσ hσ' m q hb hb' (k:=1) (.inl rfl))
  have hR := (tendsto_hurwitz_shifted_tails hσ hσ' m 0 hb hb' (k:= -1) (.inr rfl))
  simp only [one_mul,neg_one_mul,zero_add] at hL hR
  have hi : Tendsto (fun Y : ℕ => q+Y) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat q
  have he := tendsto_nhds_unique (H.comp hi)
    ((((hL.const_add (∑ j∈range q,P j)).add (hR.comp hi))).congr' (Filter.Eventually.of_forall fun Y => by
      change (∑ j∈range q,P j)+(∑ j∈range Y,P (q+j))+(∑ j∈range (q+Y),N j)=∑ j∈range (q+Y), (P j+N j)
      rw [sum_add_distrib,sum_range_add P]))
  linear_combination he

/-- Sum of the negative complete gamma modes at the dual cutoff. -/
def hurwitzNegativeDual (s : ℂ) (a : ℝ) (q : ℕ) :=
  ∑ j∈range q,hurwitzShift a (-hurwitzOmega j)*hurwitzDualMode s (-hurwitzOmega j)

/-- Auxiliary radial heads entering from the origin below the real axis. -/
def hurwitzRadialHeads (s : ℂ) (a b : ℝ) (q : ℕ) :=
  ∑ j∈range q,hurwitzShift a (hurwitzOmega j)*
    ((1-I)*(∫ t in (0:ℝ)..(b/2),fourierPowerMode s (hurwitzOmega j) ((1-I)*t)))

/-- Lower half of the saddle contour traversed from -b/2 to zero. -/
def hurwitzLowerGeometric (s : ℂ) (b : ℝ) (q : ℕ) :=
  (1+I)*∫ v in (-b/2)..0,(hurwitzRay b 1 v)^(-s)*(hurwitzRayRatio 1 v)^(q+1)/(1-hurwitzRayRatio 1 v)

private theorem geom_weight_difference (z r : ℂ) (q : ℕ) (hr : r≠1) :
    ∑ j∈range q,z*r^(j+1)=z*r^1/(1-r)-z*r^(q+1)/(1-r) := by
  have H : (∑ j∈range q,r^(j+1))=(∑ j∈range q,r^j)*r := by
    rw [sum_mul];apply sum_congr rfl;intro j _;rw [pow_succ]
  rw [←mul_sum,H,geom_sum_eq hr,pow_one,pow_succ,show r-1= -(1-r) by ring,div_neg]
  field_simp [sub_ne_zero.mpr hr.symm];ring

set_option maxHeartbeats 600000 in
private theorem sum_diagonal_heads (s : ℂ) (a b : ℝ) (m q : ℕ) (hb : b=a+m+1/2) (hh : 0<b) :
    (∑ j∈range q,hurwitzShift a (hurwitzOmega j)*
      ((1+I)*(∫ v in (-b/2)..0,fourierPowerMode s (hurwitzOmega j) (hurwitzRay b 1 v)))) =
      hurwitzLowerGeometric s b 0-hurwitzLowerGeometric s b q := by
  let z := hurwitzRay b 1
  let r := hurwitzRayRatio 1
  have hpos : 0<b → ∀ v∈uIcc (-b/2) 0,0<(z v).re := by
    intro hh v hv;rw [Set.uIcc_of_le (by linarith)] at hv;dsimp only [z];rw [hurwitzRay_re];linarith [hv.1]
  have weight (v : ℝ) (j : ℕ) : hurwitzShift a (hurwitzOmega j)*fourierPowerMode s (hurwitzOmega j) (z v)=(z v)^(-s)*(r v)^(j+1) := by
    have H := shiftedRayMode_eq_geometric s a b m (j+1) hb (k:=1) (.inl rfl) v
    simpa only [mul_one,hurwitzOmega,Nat.cast_add,Nat.cast_one] using H
  have hcont : ContinuousOn (fun v : ℝ => (z v)^(-s)) (uIcc (-b/2) 0) :=
    ContinuousOn.cpow_const (by unfold z hurwitzRay;fun_prop) (fun v hv => Or.inl (hpos hh v hv))
  have hr : Continuous r := by unfold r hurwitzRayRatio;fun_prop
  have hi (j : ℕ) : IntervalIntegrable (fun v => (z v)^(-s)*(r v)^j) volume (-b/2) 0 := (hcont.mul (hr.pow j).continuousOn).intervalIntegrable (μ:=volume)
  have hi' (j : ℕ) : IntervalIntegrable (fun v => (z v)^(-s)*(r v)^j/(1-r v)) volume (-b/2) 0 := ((hcont.mul (hr.pow j).continuousOn).div
    (continuous_const.sub hr).continuousOn (fun v _ => sub_ne_zero.mpr (hurwitzRayRatio_ne_one 1 v).symm)).intervalIntegrable (μ:=volume)
  let F (j : ℕ) (v : ℝ) := (z v)^(-s)*(r v)^(j+1)
  let G (j : ℕ) (v : ℝ) := (z v)^(-s)*(r v)^j/(1-r v)
  have he (j : ℕ) : hurwitzShift a (hurwitzOmega j)*
      ((1+I)*(∫ v in (-b/2)..0,fourierPowerMode s (hurwitzOmega j) (z v))) =
      (1+I)*(∫ v in (-b/2)..0,F j v) := by
    rw [mul_left_comm,←intervalIntegral.integral_const_mul];apply congrArg
    apply intervalIntegral.integral_congr;intro v _;exact weight v j
  calc
    _ = ∑ j∈range q,(1+I)*(∫ v in (-b/2)..0,F j v) := sum_congr rfl fun j _ => he j
    _ = (1+I)*(∫ v in (-b/2)..0,∑ j∈range q,F j v) := by
      rw [intervalIntegral.integral_finsetSum (s:=range q) (f:=F) (fun j _ => hi (j+1)),mul_sum]
    _ = (1+I)*(∫ v in (-b/2)..0,G 1 v-G (q+1) v) := by
      congr 1;apply intervalIntegral.integral_congr;intro v _
      exact geom_weight_difference _ _ _ (hurwitzRayRatio_ne_one 1 v)
    _ = _ := by
      rw [intervalIntegral.integral_sub (f:=G 1) (g:=G (q+1)) (hi' 1) (hi' (q+1)),mul_sub]
      rfl

/-- Exact decomposition into the saddle contour, its lower endpoint,
the nonstationary negative frequencies, and radial heads at the origin. -/
theorem hurwitzZeta_saddle_decomposition {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1)
    {a b : ℝ} (ha : a∈Ioc (0:ℝ) 1) (m q : ℕ) (hb : b=a+m+1/2) :
    HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a b s-hurwitzDualSum a q s =
      hurwitzGeometricTail s b 1 q+hurwitzLowerGeometric s b q
      -(b:ℂ)^(1-s)/(1-s)+hurwitzGeometricTail s b (-1) 0-hurwitzLowerGeometric s b 0
      -hurwitzRadialHeads s a b q-hurwitzNegativeDual s a q := by
  have hb' : 0<b := by rw [hb];linarith [ha.1,Nat.cast_nonneg (α:=ℝ) m]
  have H := hurwitzZeta_sub_half_cutoff hσ hσ' ha m q hb
  have hj := sum_diagonal_heads s a b m q hb hb'
  rw [H,hurwitzDualSum,Nat.floor_natCast]
  simp only [hurwitzPair,sum_add_distrib,hurwitzTail,mul_sub,sum_sub_distrib]
  have hh (j : ℕ) := hurwitzMode_head_eq_diagonals hσ.le hσ' (hurwitzOmega j) hb'
  simp_rw [hh,mul_add,sum_add_distrib]
  unfold hurwitzRadialHeads hurwitzNegativeDual
  linear_combination -hj

end AnalyticNumberTheory.RiemannZeta
