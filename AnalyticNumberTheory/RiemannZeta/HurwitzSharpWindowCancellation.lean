import AnalyticNumberTheory.RiemannZeta.HurwitzEndpointPhases
import AnalyticNumberTheory.ExponentialSums.StationaryFrequencyWindow

/-!
# Cancellation of the endpoint reciprocals in the sharp Hurwitz window

The width of the transition band is √t/x. Matching its two sides at
integer distances from floor y removes the absolute harmonic sum from
the error term.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

private def windowTerm (a x : ℝ) (s : ℂ) (Y n : ℕ) (ω : ℝ) :=
  hurwitzShift a ω*(if n≤Y then hurwitzTail s ω x-hurwitzDualMode s ω else hurwitzTail s ω x)

theorem hurwitz_frequency_window_uniform {s : ℂ} {a x y : ℝ} (hx : 2≤x) (hxy' : x≤y)
    (hσ : 0<s.re) (hσ' : s.re<1) (hxy : s.im=2*Real.pi*x*y) :
    let Y := ⌊y⌋₊
    let G (m : ℕ) := hurwitzPair a m (fun ω => if m<Y then hurwitzTail s ω x-hurwitzDualMode s ω else hurwitzTail s ω x)
    ‖∑ m∈range (2*(Y+1)),G m‖≤500*x^(-s.re) := by
  intro Y G
  let A := x^(-s.re)
  let w := Real.sqrt s.im/x
  let R := ⌈w⌉₊
  let δ := y-Y
  let z := hurwitzEndpointPhase (x-a)
  let c := I/(2*Real.pi)*(x:ℂ)^(-s)*z^Y
  let F (n : ℕ) := windowTerm a x s Y n (2*Real.pi*n)
  let B (n : ℕ) := windowTerm a x s Y n (-(2*Real.pi*n))
  have hx' : 0<x := by linarith
  have hy : 2≤y := hx.trans hxy'
  have hy' : 0<y := by linarith
  have ht' : 0<s.im := hxy ▸ by positivity
  have hπ : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hxt : x*y≤s.im := by rw [hxy];nlinarith [mul_nonneg (sub_nonneg.mpr hπ) (mul_nonneg hx'.le hy'.le)]
  have ht : 1≤s.im := by nlinarith [mul_nonneg (show 0≤x-1 by linarith) (show 0≤y-1 by linarith)]
  have hτ : s.im/x=2*Real.pi*y := by rw [hxy];field_simp
  have hsqrt := Real.sq_sqrt ht'.le
  have hw : 1≤w := by
    dsimp [w];rw [le_div_iff₀ hx',one_mul]
    nlinarith [Real.sqrt_nonneg s.im,mul_nonneg hx'.le (sub_nonneg.mpr hxy')]
  have hwp : 0<w := by linarith
  have hYR : w≤(R:ℝ) := Nat.le_ceil _
  have hR : 1≤R := by exact_mod_cast (hw.trans hYR)
  have hR' : (R:ℝ)≤2*w := by dsimp only [R];linarith [Nat.ceil_lt_add_one hwp.le]
  have hY : 2≤Y := (Nat.le_floor_iff hy'.le).mpr (by exact_mod_cast hy)
  have hYy : (Y:ℝ)≤y := Nat.floor_le hy'.le
  have hyY : y<(Y:ℝ)+1 := Nat.lt_floor_add_one _
  have hδ : 0≤δ := sub_nonneg.mpr hYy
  have hδ' : δ≤1 := by dsimp [δ];linarith
  have hA : 0≤A := Real.rpow_nonneg hx'.le _
  have hz : ‖z‖=1 := norm_hurwitzEndpointPhase _
  have hp : x^(1-s.re)=A*x := by rw [show 1-s.re= -s.re+1 by ring,Real.rpow_add hx',Real.rpow_one]
  have hpow (n : ℕ) : x^(1-s.re)/Real.sqrt s.im=A/w := by dsimp [w]; rw [hp];field_simp
  have hc : ‖c‖≤A := by
    dsimp [c]; rw [norm_mul,norm_pow,hz,one_pow,mul_one,norm_mul,norm_div,Complex.norm_I,
      Complex.norm_cpow_eq_rpow_re_of_pos hx',neg_re,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_two]
    change (1/(2*Real.pi))*A≤A
    exact (mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hπ) hA).trans_eq (one_mul _)
  have hmain (n : ℕ) : ‖F n‖≤24*A/w := by
    dsimp only [F,windowTerm];rw [norm_mul,norm_hurwitzShift,one_mul]
    by_cases hn : n≤Y
    · rw [if_pos hn]
      have hn' := (Nat.cast_le (α:=ℝ)).mpr hn
      refine (hurwitz_transition_head hx' hσ.le hσ' ht (by positivity) ?_).trans_eq ?_
      · rw [hxy];nlinarith [mul_nonneg (mul_nonneg (show 0≤2*Real.pi by positivity) hx'.le) (sub_nonneg.mpr (hn'.trans hYy))]
      · linear_combination 24*hpow n
    · rw [if_neg hn]
      have hn' : (Y:ℝ)+1≤n := by exact_mod_cast (by omega : Y+1≤n)
      refine (hurwitzTail_stationary hx' hσ hσ' ht ?_).trans_eq ?_
      · rw [abs_of_nonneg (by positivity),hxy]
        nlinarith [mul_nonneg (mul_nonneg (show 0≤2*Real.pi by positivity) hx'.le) (sub_nonneg.mpr (hyY.le.trans hn'))]
      · linear_combination 24*hpow n
  have hN : ((Y-1:ℕ):ℝ)*(x/s.im)≤1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one,←mul_div_assoc,div_le_one ht']
    nlinarith [mul_nonneg hx'.le (sub_nonneg.mpr hYy)]
  have hE (j : ℕ) : hurwitzFarError s.re s.im x j=
      40*A*(x/s.im+(1/x)/(j:ℝ)^2+w^2/(j:ℝ)^3) := by
    dsimp only [hurwitzFarError,w,A];rw [div_pow,hsqrt];ring
  have hl (j : ℕ) (hj : j∈Ioc R (Y-1)) :
      ‖F (Y-j)+c*(conj z)^j/((j:ℂ)+δ)‖≤40*A*(x/s.im+(1/x)/(j:ℝ)^2+w^2/(j:ℝ)^3) := by
    have hj0 := (mem_Ioc.mp hj).1
    have hj1 := (mem_Ioc.mp hj).2
    have hjY : j≤Y := by omega
    have hjp : 0<(j:ℝ) := by exact_mod_cast (by omega : 0<j)
    have htj : (j:ℝ)≤s.im/x-2*Real.pi*(Y-j:ℕ) := by
      rw [hτ,Nat.cast_sub hjY]
      nlinarith [mul_nonneg (sub_nonneg.mpr hπ) hjp.le,mul_nonneg (show 0≤2*Real.pi by positivity) (sub_nonneg.mpr hYy)]
    have H := hurwitz_low_far (s:=s) hx' hjp hσ.le hσ' ht' (by positivity) htj
    rw [←hE]
    dsimp only [F,windowTerm];rw [if_pos (Nat.sub_le _ _)]
    have hh := hurwitzShift_mul_endpoint (a:=a) hx' hxy (Y-j)
    rw [hurwitzPhase_sub (x-a) hjY,Nat.cast_sub (R:=ℂ) hjY] at hh
    have he : (Y:ℂ)-(j:ℂ)-(y:ℂ)= -((j:ℂ)+δ) := by dsimp [δ];push_cast;ring
    rw [he] at hh
    dsimp only [c,z]
    have hsign : (I/(2*Real.pi)*(x:ℂ)^(-s)*z^Y)*(conj z)^j/((j:ℂ)+δ)=
        hurwitzShift a (2*Real.pi*(Y-j:ℕ))*hurwitzEndpoint s (2*Real.pi*(Y-j:ℕ)) x := by
      rw [hh,div_neg];dsimp only [z];ring
    rw [show I/(2*Real.pi)*(x:ℂ)^(-s)*(hurwitzEndpointPhase (x-a))^Y*(conj (hurwitzEndpointPhase (x-a)))^j/((j:ℂ)+δ)=_ from hsign,
      ←mul_add,norm_mul,norm_hurwitzShift,one_mul]
    exact H
  have hh (j : ℕ) (hj : j∈Ioc R (Y-1)) :
      ‖F (Y+j)-c*z^j/((j:ℂ)-δ)‖≤40*A*(x/s.im+(1/x)/(j:ℝ)^2+w^2/(j:ℝ)^3) := by
    have hj0 := (mem_Ioc.mp hj).1
    have hjp : 2≤(j:ℝ) := by exact_mod_cast (by omega : 2≤j)
    have htj : (j:ℝ)≤2*Real.pi*(Y+j:ℕ)-s.im/x := by
      rw [hτ,Nat.cast_add]
      have hπ' : 2≤2*Real.pi := by linarith [Real.pi_gt_three]
      nlinarith [mul_nonneg (sub_nonneg.mpr hπ') (show 0≤(Y:ℝ)+j-y by linarith)]
    have H := hurwitz_high_far (s:=s) hx' (show 0<(j:ℝ) by linarith) hσ hσ' ht' htj
    rw [←hE]
    dsimp only [F,windowTerm];rw [if_neg (by omega : ¬Y+j≤Y)]
    have hphase := hurwitzShift_mul_endpoint (a:=a) hx' hxy (Y+j)
    rw [pow_add,Nat.cast_add (R:=ℂ)] at hphase
    have he : (Y:ℂ)+(j:ℂ)-(y:ℂ)=(j:ℂ)-δ := by dsimp [δ];push_cast;ring
    rw [he] at hphase
    have hsign : -(c*z^j/((j:ℂ)-δ))=hurwitzShift a (2*Real.pi*(Y+j:ℕ))*hurwitzEndpoint s (2*Real.pi*(Y+j:ℕ)) x := by
      rw [hphase];dsimp only [c,z];ring
    rw [sub_eq_add_neg,hsign,←mul_add,norm_mul,norm_hurwitzShift,one_mul]
    exact H
  have H := norm_stationary_window hR hA (div_nonneg hx'.le ht'.le) hN (show 0≤1/x by positivity)
    ((div_le_one hx').mpr (by linarith)) hw hYR hR' hδ hδ' (fun j => F (Y-j)) (fun j => F (Y+j))
    c z hc hz (fun j _ => ⟨hmain _,hmain _⟩) hl hh
  have Hpos : ‖∑ m∈range (2*(Y+1)),F (m+1)‖≤(435+4*(Real.pi+2))*A := by
    rw [sum_range_centered F (by omega : 1≤Y)]
    have hM (n : ℕ) : ‖F n‖≤24*A := (hmain n).trans (div_le_self (by positivity) hw)
    calc
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add H (hM _)) (hM _)) (hM _)) (hM _)
      _ = _ := by ring
  have hB (n : ℕ) : ‖B n‖≤4*x^(1-s.re)/s.im := by
    dsimp only [B,windowTerm];rw [norm_mul,norm_hurwitzShift,one_mul]
    by_cases hn : n≤Y
    · rw [if_pos hn]
      apply hurwitz_negative_head hx' hσ' ht' (neg_nonpos.mpr (by positivity))
      rw [abs_neg,abs_of_nonneg (by positivity),hxy]
      nlinarith [mul_nonneg (mul_nonneg (show 0≤2*Real.pi by positivity) hx'.le) (sub_nonneg.mpr (((Nat.cast_le (α:=ℝ)).mpr hn).trans hYy))]
    · rw [if_neg hn]
      have hn' : (Y:ℝ)+1≤n := by exact_mod_cast (by omega : Y+1≤n)
      have Hfreq : s.im/x≤2*Real.pi*n := by rw [hτ];gcongr; linarith
      have hwpos := (div_pos ht' hx').trans_le Hfreq
      have H := hurwitzTail_first hσ hσ' ht'.le (neg_ne_zero.mpr hwpos.ne')
        hx' (div_pos ht' hx') (fun u hu => by
          rw [abs_of_nonpos (by linarith only [hwpos,div_nonneg ht'.le (hx'.trans_le hu).le])]
          linarith [div_nonneg ht'.le (hx'.trans_le hu).le])
      apply H.trans_eq
      rw [hp];dsimp only [A];field_simp <;> ring
  have Hneg : ‖∑ m∈range (2*(Y+1)),B (m+1)‖≤16*A := by
    apply (norm_sum_le _ _).trans ((sum_le_sum fun m hm => hB (m+1)).trans ?_)
    rw [sum_const,card_range,nsmul_eq_mul,hp]
    push_cast
    rw [←mul_div_assoc,div_le_iff₀ ht']
    nlinarith [mul_le_mul_of_nonneg_right hxt hA,mul_nonneg (mul_nonneg hA hx'.le) (sub_nonneg.mpr hYy),
      mul_nonneg (mul_nonneg hA hx'.le) (show 0≤y-1 by linarith)]
  have hG (m : ℕ) : G m=F (m+1)+B (m+1) := by
    dsimp [G,F,B,hurwitzPair,windowTerm,hurwitzOmega];push_cast
    simp only [Nat.add_one_le_iff]
  simp_rw [hG,sum_add_distrib]
  apply (norm_add_le _ _).trans ((add_le_add Hpos Hneg).trans ?_)
  change (435+4*(Real.pi+2))*A+16*A≤500*A
  nlinarith [mul_nonneg hA (sub_nonneg.mpr Real.pi_lt_four.le)]

end AnalyticNumberTheory.RiemannZeta
