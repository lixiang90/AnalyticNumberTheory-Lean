import AnalyticNumberTheory.RiemannZeta.HurwitzFrequencyWindow
import AnalyticNumberTheory.RiemannZeta.HurwitzHighFrequencies
import AnalyticNumberTheory.RiemannZeta.HurwitzConjugation

/-!
# Sharp approximate functional equation for Hurwitz zeta

For 0<a≤1 and xy=|Im s|/(2π), the direct polynomial runs over n+a≤x
and the dual polynomial over 1≤n≤y. All constants are uniform in a.
The square-root transition term allows the stationary frequency to coincide
with the endpoint.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

private theorem high_pair {a x y : ℝ} {s : ℂ} (hx : 0<x) (hy : 2≤y) (ht : 1≤s.im)
    (hσ : 0<s.re) (hσ' : s.re<1) (hxy : s.im=2*Real.pi*x*y) {k : ℕ}
    (hk : 2*(⌊y⌋₊+1)≤k) : ‖hurwitzCorrectedMode a x s (hurwitzOmega k)+
      hurwitzCorrectedMode a x s (-hurwitzOmega k)‖ ≤ 100*y*x^(-s.re)/((k:ℝ)+1)^2 := by
  have hπ : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hky : 2*y≤(k:ℝ)+1 := by
    have hc : 2*((⌊y⌋₊:ℝ)+1)≤(k:ℝ) := by exact_mod_cast hk
    linarith [Nat.lt_floor_add_one y]
  have ht' : s.im/x=2*Real.pi*y := by rw [hxy]; field_simp
  have hfreq : 2*(s.im/x)≤hurwitzOmega k := by
    rw [ht',hurwitzOmega]; nlinarith [mul_nonneg (by positivity : 0≤2*Real.pi) (sub_nonneg.mpr hky)]
  have home := hurwitzOmega_pos k
  have H (ω : ℝ) (hw : |ω|=hurwitzOmega k) :
      ‖hurwitzCorrectedMode a x s ω‖ ≤ 50*y*x^(-s.re)/((k:ℝ)+1)^2 := by
    apply (norm_hurwitzCorrectedMode_high hx hσ hσ' ht (hfreq.trans_eq hw.symm)).trans
    rw [hw,ht',hurwitzOmega,mul_pow]
    calc
      _ = (50*y*x^(-s.re)/((k:ℝ)+1)^2)/(2*Real.pi) := by field_simp <;> ring
      _ ≤ _ := div_le_self (by positivity) hπ
  apply (norm_add_le _ _).trans ((add_le_add (H _ (abs_of_pos home)) (H _ (by simp [abs_of_pos home]))).trans_eq ?_)
  ring

private theorem frequency_boundary (a x : ℝ) (hx : 0<x) (s : ℂ) (L : ℕ) :
    ‖∑ m∈range L,hurwitzPair a m (fun ω => hurwitzMode s ω x/hurwitzFrequency ω)‖ ≤
      2*x^(-s.re)*(1+Real.log L) := by
  have H (m : ℕ) (ω : ℝ) (hw : |ω|=hurwitzOmega m) :
      ‖hurwitzShift a ω*(hurwitzMode s ω x/hurwitzFrequency ω)‖≤x^(-s.re)/((m:ℝ)+1) := by
    rw [norm_mul,norm_hurwitzShift,one_mul,norm_div,norm_hurwitzMode s ω hx,hurwitzFrequency,
      norm_mul,norm_neg,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,hw,hurwitzOmega]
    have hπ : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
    gcongr
    nlinarith [mul_nonneg (sub_nonneg.mpr hπ) (show 0≤(m:ℝ)+1 by positivity)]
  have HH : ∑ i∈range L, 1/((i:ℝ)+1) ≤ 1+Real.log L := by
    simpa only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,Nat.cast_add,Nat.cast_one,one_div]
      using harmonic_le_one_add_log L
  apply (norm_sum_le ..).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left HH (by positivity))
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  apply (norm_add_le _ _).trans
  apply (add_le_add (H m _ (abs_of_pos (hurwitzOmega_pos m)))
    (H m _ (by simp [abs_of_pos (hurwitzOmega_pos m)]))).trans_eq
  ring

private theorem dual_sum_in_window (a y : ℝ) (s : ℂ) :
    ∑ m∈range (2*(⌊y⌋₊+1)),(if m<⌊y⌋₊ then hurwitzPair a m (hurwitzDualMode s) else 0) =
      hurwitzDualSum a y s := by
  rw [←sum_filter,hurwitzDualSum]
  congr 1; ext m; simp; omega

/-- Positive-height form with a numerical constant, uniform in the real shift. -/
theorem hurwitzZeta_sharp_afe_pos {a x y : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hx : 2≤x) (hy : 2≤y)
    {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) (hxy : s.im=2*Real.pi*x*y) :
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a y s‖ ≤
      256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt s.im) := by
  let Y := ⌊y⌋₊
  let L := 2*(Y+1)
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s
  let D := hurwitzDirectSum a x s
  let U := hurwitzDualSum a y s
  let P := (x:ℂ)^(1-s)/(1-s)
  let W := (sawtooth (x-a):ℂ)*(x:ℂ)^(-s)
  let F (m : ℕ) := hurwitzCorrectedMode a x s (hurwitzOmega m)+hurwitzCorrectedMode a x s (-hurwitzOmega m)
  let B (m : ℕ) := hurwitzPair a m (fun ω => hurwitzMode s ω x/hurwitzFrequency ω)
  let G (m : ℕ) := hurwitzPair a m (fun ω => if m<Y then hurwitzTail s ω x-hurwitzDualMode s ω else hurwitzTail s ω x)
  have hx' : 0<x := by linarith
  have hy' : 0<y := by linarith
  have hπ : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hxt : x≤s.im := by rw [hxy]; nlinarith [mul_nonneg (sub_nonneg.mpr hπ) (mul_nonneg hx'.le hy'.le),mul_nonneg hx'.le (show 0≤y-1 by linarith)]
  have ht : 1≤s.im := by linarith
  have hs : 0<1-s.re := by linarith
  have hY : 2≤Y := (Nat.le_floor_iff hy'.le).mpr (by exact_mod_cast hy)
  have hYL : y≤(L:ℝ) := by dsimp [L,Y]; push_cast; linarith [Nat.lt_floor_add_one y]
  have hdiag : ∑ m∈range L,F m=(∑ m∈range L,G m)+U-∑ m∈range L,B m := by
    rw [show U=∑ m∈range L,(if m<Y then hurwitzPair a m (hurwitzDualMode s) else 0) from
      (dual_sum_in_window a y s).symm,←sum_add_distrib,←sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    dsimp only [F,G,B,hurwitzPair,hurwitzCorrectedMode]
    split_ifs <;> ring
  have hsum : HasSum F (Z-D+P-W) := hurwitzZeta_hasSum_correctedModes ha (by linarith [ha.2]) hσ hσ'
  have htail := norm_sub_sum_le_of_inverse_square hsum (L:=L) (by dsimp [L];omega)
    (A:=100*y*x^(-s.re)) (by positivity) (fun k hk => high_pair hx' hy ht hσ hσ' hxy hk)
  have htail' : ‖(Z-D+P-W)-(∑ m∈range L,F m)‖≤100*x^(-s.re) := by
    apply htail.trans
    rw [div_le_iff₀ (hy'.trans_le hYL)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hYL) (Real.rpow_nonneg hx'.le (-s.re))]
  have hB := frequency_boundary a x hx' s L
  have hG := hurwitz_frequency_window (a:=a) hx' hy hσ hσ' ht hxy
  have hP : ‖P‖≤x^(-s.re) := by
    dsimp [P]; rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx']
    have hden : x≤‖1-s‖ := hxt.trans (by simpa [abs_of_nonneg (by linarith : 0≤s.im)] using Complex.abs_im_le_norm (1-s))
    rw [div_le_iff₀ (hx'.trans_le hden),sub_re,one_re,show 1-s.re= -s.re+1 by ring,Real.rpow_add hx',Real.rpow_one]
    gcongr
  have hW : ‖W‖≤x^(-s.re) := by
    dsimp [W]; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos hx',neg_re]
    exact (mul_le_mul_of_nonneg_right (show |sawtooth (x-a)|≤1 by linarith [sawtooth_abs_le (x-a)]) (by positivity)).trans_eq (one_mul _)
  have hcomb : ‖Z-D-U‖≤100*x^(-s.re)+x^(-s.re)+x^(-s.re)+
      (16/(1-s.re)*x^(-s.re)*(1+Real.log (Y+1:ℕ))+2*(48+16/(1-s.re))*x^(1-s.re)/Real.sqrt s.im)+
      2*x^(-s.re)*(1+Real.log L) := by
    have he : Z-D-U=((((Z-D+P-W)-(∑ m∈range L,F m))-P)+W+(∑ m∈range L,G m))-(∑ m∈range L,B m) := by rw [hdiag]; abel
    rw [he]
    exact (norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans
      (add_le_add ((norm_sub_le ..).trans (add_le_add htail' hP)) hW)) hG)) hB)
  have hlog : 0≤Real.log (y+2) := Real.log_nonneg (by linarith)
  have hYl : Real.log (Y+1:ℕ) ≤ Real.log (y+2) := by
    apply Real.log_le_log (by positivity); push_cast; linarith [Nat.floor_le hy'.le (a:=y)]
  have hLl : Real.log L ≤ 1+Real.log (y+2) := by
    dsimp [L]; push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    push_cast at hYl; linarith
  apply hcomb.trans
  let A := x^(-s.re)
  let E := x^(1-s.re)/Real.sqrt s.im
  let K := 1/(1-s.re)
  have hA : 0≤A := by dsimp [A]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  change 100*A+A+A+(16/(1-s.re)*A*(1+Real.log (Y+1:ℕ))+2*(48+16/(1-s.re))*x^(1-s.re)/Real.sqrt s.im)+2*A*(1+Real.log L) ≤ _
  apply le_trans _ (show 100*A+A+A+(16*K*A*(1+Real.log (y+2))+2*(48+16*K)*E)+2*A*(1+(1+Real.log (y+2))) ≤
      256*(1+K)*(A*(1+Real.log (y+2))+E) by
    nlinarith [mul_nonneg hA hlog,mul_nonneg hK hA,mul_nonneg (mul_nonneg hK hA) hlog,mul_nonneg hK hE])
  dsimp only [E,K]
  ring_nf at hYl hLl ⊢
  nlinarith [mul_nonneg (mul_nonneg hA (inv_nonneg.mpr hs.le)) (sub_nonneg.mpr hYl),mul_nonneg hA (sub_nonneg.mpr hLl)]


theorem hurwitzDualSum_conj (a y : ℝ) (s : ℂ) :
    hurwitzDualSum a y (conj s)=conj (hurwitzDualSum a y s) := by
  rw [hurwitzDualSum,hurwitzDualSum,map_sum]
  apply sum_congr rfl
  intro m hm
  have hw := (hurwitzOmega_pos m).ne'
  change hurwitzPair a m (hurwitzDualMode (conj s))=conj (hurwitzPair a m (hurwitzDualMode s))
  have hp := hurwitzDualMode_conj s (neg_ne_zero.mpr hw)
  rw [neg_neg] at hp
  have hp' := hurwitzShift_conj a (-hurwitzOmega m)
  rw [neg_neg] at hp'
  simp only [hurwitzPair,map_add,map_mul]
  rw [hurwitzDualMode_conj s hw,hp,←hurwitzShift_conj,←hurwitzShift_conj,neg_neg,add_comm]

/-- The sharp two-sided approximate functional equation for either sign of
the height, at arbitrary direct and reciprocal cutoffs satisfying the
saddle-point relation. -/
theorem hurwitzZeta_sharp_afe {a x y : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hx : 2≤x) (hy : 2≤y)
    {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a y s‖ ≤
      256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt |s.im|) := by
  rcases le_total 0 s.im with ht|ht
  · rw [abs_of_nonneg ht] at hxy ⊢
    exact hurwitzZeta_sharp_afe_pos ha hx hy hσ hσ' hxy
  · rw [abs_of_nonpos ht] at hxy ⊢
    have hs : s≠1 := fun he => by simp [he] at hσ'
    have H := hurwitzZeta_sharp_afe_pos (s:=conj s) ha hx hy hσ hσ' (by simpa using hxy)
    rw [hurwitzZeta_conj_in_strip ha (by linarith) hs,hurwitzDirectSum_conj ha.1,hurwitzDualSum_conj,
      ←map_sub,←map_sub,Complex.norm_conj] at H
    exact H

end AnalyticNumberTheory.RiemannZeta
