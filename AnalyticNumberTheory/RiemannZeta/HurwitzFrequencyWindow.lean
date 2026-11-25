import AnalyticNumberTheory.RiemannZeta.HurwitzFourierExpansion
import AnalyticNumberTheory.RiemannZeta.HurwitzStationaryEndpoint
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The Fourier frequencies in the sharp Hurwitz window

The integral from zero controls the frequencies retained in the dual
polynomial. The tail integral controls the omitted frequencies. Summing
the first-derivative estimates costs one harmonic sum on each side.
-/
noncomputable section
open Real Complex Filter Set Finset MeasureTheory
namespace AnalyticNumberTheory.RiemannZeta

/-- Shifted sum of the positive and negative modes at frequency m+1. -/
def hurwitzPair (a : ℝ) (m : ℕ) (f : ℝ → ℂ) : ℂ :=
  hurwitzShift a (hurwitzOmega m)*f (hurwitzOmega m)+
    hurwitzShift a (-hurwitzOmega m)*f (-hurwitzOmega m)

private lemma norm_pair {a E : ℝ} {m : ℕ} {f : ℝ → ℂ}
    (h : ∀ ω : ℝ, |ω|=hurwitzOmega m → ‖f ω‖≤E) : ‖hurwitzPair a m f‖≤2*E := by
  have hp := hurwitzOmega_pos m
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_hurwitzShift,one_mul]
  linarith [h _ (abs_of_pos hp),h _ (abs_neg _ |>.trans (abs_of_pos hp))]

/-- The two finite sums use the Fourier cutoff m+1≤y. -/
def hurwitzDualSum (a y : ℝ) (s : ℂ) : ℂ :=
  ∑ m∈range ⌊y⌋₊,hurwitzPair a m (hurwitzDualMode s)

private lemma lower_gap {s : ℂ} {ω x d : ℝ} (hx : 0<x) (hσ : 0≤s.re) (hσ' : s.re<1)
    (ht : 0≤s.im) (hd : 0<d) (hgap : x*d≤s.im-|ω| * x) :
    ‖hurwitzTail s ω x-hurwitzDualMode s ω‖ ≤ 4/(1-s.re)*x^(-s.re)/d := by
  have H := hurwitzMode_head_first (ω:=ω) hx hσ hσ' ht (mul_pos hx hd)
    (fun u hu hub => by
      have h := (mul_le_mul_of_nonneg_right (le_abs_self ω) hu.le).trans (mul_le_mul_of_nonneg_left hub (abs_nonneg ω))
      linarith)
  rw [hurwitzTail,sub_sub_cancel_left,norm_neg]
  convert H using 1
  rw [show 1-s.re= -s.re+1 by ring,Real.rpow_add hx,Real.rpow_one]
  field_simp <;> ring

private lemma upper_gap {s : ℂ} {ω x d : ℝ} (hx : 0<x) (hσ : 0<s.re) (hσ' : s.re<1)
    (ht : 0≤s.im) (hd : 0<d) (hgap : d≤|ω| - s.im/x) :
    ‖hurwitzTail s ω x‖≤x^(-s.re)*(4/d) := by
  have hw : 0 < |ω| := by linarith [div_nonneg ht hx.le]
  apply hurwitzTail_first hσ hσ' ht (abs_pos.mp hw) hx hd
  intro u hu
  have H := abs_sub_abs_le_abs_sub ω (s.im/u)
  rw [abs_of_nonneg (div_nonneg ht (hx.trans_le hu).le)] at H
  linarith [div_le_div_of_nonneg_left ht hx hu]

private lemma harmonic_range (N : ℕ) : ∑ i∈range N, 1/((i:ℝ)+1) ≤ 1+Real.log N := by
  simpa only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,Nat.cast_add,Nat.cast_one,
    one_div] using harmonic_le_one_add_log N

private lemma split_window {f : ℕ → ℂ} {Y : ℕ} (hY : 1≤Y) {A E : ℝ} (hA : 0≤A)
    (hlo : ∀ m<Y-1, ‖f m‖≤A/((Y-1-m:ℕ):ℝ))
    (hne : ‖f (Y-1)‖≤E) (hne' : ‖f Y‖≤E)
    (hhi : ∀ j<Y+1, ‖f (Y+1+j)‖≤A/((j:ℝ)+1)) :
    ‖∑ m∈range (2*(Y+1)),f m‖ ≤ 2*A*(1+Real.log (Y+1:ℕ))+2*E := by
  let N := Y-1
  have hN : N+1=Y := by dsimp [N]; omega
  have H (J : ℕ) : ∑ i∈range J, A/((i:ℝ)+1) ≤ A*(1+Real.log J) := by
    simpa only [mul_sum,div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left (harmonic_range J) hA
  have H₀ : ∑ m∈range N, ‖f m‖≤A*(1+Real.log (Y+1:ℕ)) := by
    rw [←sum_range_reflect (fun m => ‖f m‖) N]
    refine (sum_le_sum (g:=fun j : ℕ => A/((j:ℝ)+1)) fun j hj => ?_).trans
      ((H N).trans (mul_le_mul_of_nonneg_left ?_ hA))
    · have hj' := mem_range.mp hj
      have h := hlo (N-1-j) (by dsimp [N] at *;omega)
      simpa only [show Y-1-(N-1-j)=j+1 by dsimp [N] at *;omega,Nat.cast_add,Nat.cast_one] using h
    · by_cases hn : N=0
      · simp only [hn,Nat.cast_zero,Real.log_zero,add_zero]; linarith [Real.log_nonneg (show (1:ℝ)≤(Y+1:ℕ) by exact_mod_cast (by omega : 1≤Y+1))]
      · apply add_le_add_right
        exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) (by exact_mod_cast (by omega : N≤Y+1))
  have H₂ := (sum_le_sum fun j (hj : j∈range (Y+1)) => hhi j (mem_range.mp hj)).trans (H (Y+1))
  apply (norm_sum_le _ _).trans
  rw [show 2*(Y+1)=(N+2)+(Y+1) by omega,sum_range_add,sum_range_succ,sum_range_succ]
  simp only [hN,show N+2=Y+1 by omega]
  dsimp [N] at H₀ ⊢
  linarith

/-- Total contribution of heads and tails in the finite frequency window.
The at most two modes adjacent to the stationary endpoint are bounded
separately by the second derivative test. -/
theorem hurwitz_frequency_window {s : ℂ} {x y a : ℝ} (hx : 0<x) (hy : 2≤y)
    (hσ : 0<s.re) (hσ' : s.re<1) (ht : 1≤s.im) (hxy : s.im=2*Real.pi*x*y) :
    let Y := ⌊y⌋₊
    let f (m : ℕ) := hurwitzPair a m (fun ω => if m<Y then hurwitzTail s ω x-hurwitzDualMode s ω
      else hurwitzTail s ω x)
    ‖∑ m∈range (2*(Y+1)),f m‖ ≤ 16/(1-s.re)*x^(-s.re)*(1+Real.log (Y+1:ℕ))+
       2*(48+16/(1-s.re))*x^(1-s.re)/Real.sqrt s.im := by
  intro Y f
  have hY : 2≤Y := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hy)
  have hY' : (Y:ℝ)≤y := Nat.floor_le (by linarith)
  have hY'' : y<(Y:ℝ)+1 := Nat.lt_floor_add_one _
  have hp : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
  have ht' : 0≤s.im := by linarith
  have hs : 0<1-s.re := by linarith
  have A : 0≤8/(1-s.re)*x^(-s.re) := by positivity
  have he : 1≤1/(1-s.re) := by rw [le_div_iff₀ hs]; linarith
  have H := split_window (f:=f) (Y:=Y) (by omega) A
    (E:=(48+16/(1-s.re))*x^(1-s.re)/Real.sqrt s.im)
  refine (H ?_ ?_ ?_ ?_).trans ?_ <;> clear H
  · intro m hm
    dsimp only [f]; simp only [if_pos (show m<Y by omega)]
    have hd : 0<Y-1-m := by omega
    have hd' : 0<((Y-1-m:ℕ):ℝ) := by exact_mod_cast hd
    have heq : ((Y-1-m:ℕ):ℝ)=(Y:ℝ)-1-m := by
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
    calc
      _ ≤ _ := norm_pair (E:=4/(1-s.re)*x^(-s.re)/((Y-1-m:ℕ):ℝ)) fun ω hw =>
        lower_gap hx hσ.le hσ' ht' hd' (by
          rw [hxy,hw,hurwitzOmega,heq]
          have h := mul_le_mul_of_nonneg_left (show (Y:ℝ)-1-m≤y-((m:ℝ)+1) by linarith) hx.le
          nlinarith [mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg hx.le (show 0≤y-((m:ℝ)+1) by linarith [heq,hd']))])
      _ = _ := by ring
  · dsimp only [f]; simp only [if_pos (show Y-1<Y by omega)]
    refine (norm_pair (E:=(16+8/(1-s.re))*x^(1-s.re)/Real.sqrt s.im) ?_).trans ?_
    · intro ω hw
      rw [hurwitzTail,sub_sub_cancel_left,norm_neg]
      apply hurwitzMode_head_stationary hx hσ.le hσ' ht
      apply (mul_le_mul_of_nonneg_right (le_abs_self ω) hx.le).trans
      rw [hw,hurwitzOmega,Nat.cast_sub (by omega),Nat.cast_one,hxy]
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0≤2*Real.pi) hx.le) (sub_nonneg.mpr hY')]
    · have h := Real.rpow_nonneg hx.le (1-s.re)
      rw [←mul_div_assoc,←mul_assoc,show 2*(16+8/(1-s.re))=32+16/(1-s.re) by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : 32+16/(1-s.re)≤48+16/(1-s.re)) h) (Real.sqrt_nonneg _)
  · dsimp only [f]; simp only [lt_irrefl,if_false]
    refine (norm_pair (E:=24*x^(1-s.re)/Real.sqrt s.im) ?_).trans ?_
    · intro ω hw
      apply hurwitzTail_stationary hx hσ hσ' ht
      rw [hw,hurwitzOmega,hxy]
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0≤2*Real.pi) hx.le) (sub_nonneg.mpr hY''.le)]
    · have h := Real.rpow_nonneg hx.le (1-s.re)
      have h' := Real.sqrt_nonneg s.im
      calc
        _ = 48*x^(1-s.re)/Real.sqrt s.im := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by positivity)) h) h'
  · intro j hj
    dsimp only [f]; simp only [if_neg (show ¬Y+1+j<Y by omega)]
    have hj' : 0<(j:ℝ)+1 := by positivity
    refine (norm_pair (E:=x^(-s.re)*(4/((j:ℝ)+1))) ?_).trans ?_
    · intro ω hw
      apply upper_gap hx hσ hσ' ht' hj'
      rw [hw,hurwitzOmega,hxy,show 2*Real.pi*x*y/x=2*Real.pi*y by field_simp]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hj'.le,
        mul_nonneg (by positivity : 0≤2*Real.pi) (sub_nonneg.mpr hY''.le)]
    · calc
        _ = 8*x^(-s.re)/((j:ℝ)+1) := by ring
        _ ≤ _ := by
          have H := mul_le_mul_of_nonneg_right he (show 0≤8*x^(-s.re)/((j:ℝ)+1) by positivity)
          convert H using 1 <;> ring
  · ring_nf; exact le_rfl

end AnalyticNumberTheory.RiemannZeta
