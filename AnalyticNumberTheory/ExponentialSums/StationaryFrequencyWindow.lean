import AnalyticNumberTheory.ExponentialSums.ShiftedSineHarmonics

/-!
# Summation around a stationary Fourier frequency

Separate the short transition band from the paired frequencies outside
it. After extracting the signed endpoint reciprocal, inverse-square and
inverse-cube errors are summable uniformly in the transition width.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
namespace AnalyticNumberTheory.ExponentialSums

private lemma sum_from_one {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℕ → E) :
    ∑ j∈Ioc 0 N,f j=∑ k∈range N,f (k+1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_Ioc_succ_top (Nat.zero_le n),sum_range_succ,ih]

/-- Pair n=Y−j with n=Y+j in the window 1≤n≤2Y+2. -/
theorem sum_range_centered (f : ℕ → ℂ) {Y : ℕ} (hY : 1≤Y) :
    ∑ m∈range (2*(Y+1)),f (m+1)=
      (∑ j∈Ioc 0 (Y-1),(f (Y-j)+f (Y+j)))+
      f Y+f (2*Y)+f (2*Y+1)+f (2*Y+2) := by
  let N := Y-1
  have hN : N+1=Y := by dsimp [N];omega
  have hlow : (∑ m∈range N,f (m+1))=∑ j∈range N,f (Y-(j+1)) := by
    rw [←sum_range_reflect (fun m => f (m+1)) N]
    exact sum_congr rfl (fun j hj => congrArg f (by have := mem_range.mp hj;omega))
  have hmid : (∑ j∈range N,f (N+1+j+1))=∑ j∈range N,f (Y+(j+1)) := by
    exact sum_congr rfl (fun j hj => congrArg f (by omega))
  have hextra : (∑ i∈range 3,f (N+1+N+i+1))=f (2*Y)+f (2*Y+1)+f (2*Y+2) := by
    simp only [sum_range_succ,sum_range_zero,zero_add]
    rw [show N+1+N+0+1=2*Y by omega,show N+1+N+1+1=2*Y+1 by omega,show 2*Y+1+1=2*Y+2 by omega]
  rw [show 2*(Y+1)=((N+1)+N)+3 by omega,sum_range_add,sum_range_add,sum_range_succ,
    sum_from_one,sum_add_distrib,hlow,hmid,hextra,hN]
  abel

private lemma sum_far_majorant {R N : ℕ} (hR : 1≤R) {A p v w : ℝ}
    (hA : 0≤A) (hp : 0≤p) (hNp : (N:ℝ)*p≤1) (hv : 0≤v) (hv' : v≤1)
    (hw : 0≤w) (hwR : w≤(R:ℝ)) :
    ∑ j∈Ioc R N, 40*A*(p+v/(j:ℝ)^2+w^2/(j:ℝ)^3) ≤ 120*A := by
  have hr : 1≤(R:ℝ) := by exact_mod_cast hR
  have hrp : 0<(R:ℝ) := by linarith
  have hcard : ((Ioc R N).card:ℝ)≤N := by rw [Nat.card_Ioc];exact_mod_cast Nat.sub_le N R
  have hsum : (∑ j∈Ioc R N,(p+v/(j:ℝ)^2+w^2/(j:ℝ)^3)) =
      (Ioc R N).card*p+v*(∑ j∈Ioc R N,1/(j:ℝ)^2)+w^2*(∑ j∈Ioc R N,1/(j:ℝ)^3) := by
    rw [sum_add_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,mul_sum,mul_sum]
    simp_rw [mul_one_div]
  rw [←mul_sum,hsum]
  rw [show 120*A=(40*A)*3 by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have Hp := (mul_le_mul_of_nonneg_right hcard hp).trans hNp
  have Hv := mul_le_mul hv' (sum_Ioc_inverse_square hR N) (sum_nonneg fun _ _ => by positivity) zero_le_one
  have Hw := mul_le_mul (pow_le_pow_left₀ hw hwR 2) (sum_Ioc_inverse_cube hR N)
    (sum_nonneg fun _ _ => by positivity) (sq_nonneg (R:ℝ))
  rw [mul_one_div_cancel (pow_ne_zero 2 hrp.ne')] at Hw
  have HR : 1/(R:ℝ)≤1 := (div_le_one hrp).mpr hr
  linarith

/-- Quantitative summation of the two sides of a stationary frequency.
Within the band of width R, each mode is bounded by 24A/w. Outside the
band the signed reciprocal main terms cancel as a truncated Hilbert sum. -/
theorem norm_stationary_window {R N : ℕ} (hR : 1≤R) {A p v w δ : ℝ}
    (hA : 0≤A) (hp : 0≤p) (hNp : (N:ℝ)*p≤1) (hv : 0≤v) (hv' : v≤1)
    (hw : 1≤w) (hwR : w≤(R:ℝ)) (hRw : (R:ℝ)≤2*w) (hδ : 0≤δ) (hδ' : δ≤1)
    (f g : ℕ → ℂ) (c z : ℂ) (hc : ‖c‖≤A) (hz : ‖z‖=1)
    (hnear : ∀ j∈Ioc 0 (min R N),‖f j‖≤24*A/w ∧ ‖g j‖≤24*A/w)
    (hlo : ∀ j∈Ioc R N,‖f j+c*(conj z)^j/((j:ℂ)+δ)‖≤40*A*(p+v/(j:ℝ)^2+w^2/(j:ℝ)^3))
    (hhi : ∀ j∈Ioc R N,‖g j-c*z^j/((j:ℂ)-δ)‖≤40*A*(p+v/(j:ℝ)^2+w^2/(j:ℝ)^3)) :
    ‖∑ j∈Ioc 0 N,(f j+g j)‖ ≤ (339+4*(Real.pi+2))*A := by
  let M := Ioc 0 (min R N)
  let U := Ioc R N
  let K (j : ℕ) := z^j/((j:ℂ)-δ)-(conj z)^j/((j:ℂ)+δ)
  let E (j : ℕ) := 40*A*(p+v/(j:ℝ)^2+w^2/(j:ℝ)^3)
  have hwp : 0<w := by linarith
  have hne : ‖∑ j∈M,(f j+g j)‖≤96*A := by
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (g:=fun _ => 48*A/w) (fun j hj => (norm_add_le _ _).trans
      ((add_le_add (hnear j hj).1 (hnear j hj).2).trans_eq (by ring)))).trans
    rw [sum_const,nsmul_eq_mul]
    have hcard : (M.card:ℝ)≤R := by dsimp [M];rw [Nat.card_Ioc,Nat.sub_zero];exact_mod_cast min_le_left R N
    apply (mul_le_mul_of_nonneg_right (hcard.trans hRw) (by positivity)).trans_eq
    field_simp;ring
  have hfar : ‖∑ j∈U,(f j+g j-c*K j)‖ ≤ 240*A := by
    apply (norm_sum_le _ _).trans
    have he (j : ℕ) : f j+g j-c*K j=(f j+c*(conj z)^j/((j:ℂ)+δ))+
      (g j-c*z^j/((j:ℂ)-δ)) := by dsimp [K];ring
    apply (sum_le_sum (g:=fun j => E j+E j) (fun j hj => (he j) ▸
      (norm_add_le _ _).trans (add_le_add (hlo j hj) (hhi j hj)))).trans
    rw [sum_add_distrib]
    have H := sum_far_majorant hR hA hp hNp hv hv' hwp.le hwR
    exact (add_le_add H H).trans_eq (by ring)
  have hk : ‖∑ j∈U,c*K j‖ ≤ A*(4*(Real.pi+2)+3) := by
    rw [←mul_sum,norm_mul]
    exact mul_le_mul hc (norm_shifted_symmetric_harmonic_sum hR N hδ hδ' hz) (norm_nonneg _) hA
  have hU : Ioc 0 N=M∪U := by ext j;simp [M,U,le_min_iff];omega
  have hMU : Disjoint M U := disjoint_left.mpr (fun j hm hu => by
    have := (mem_Ioc.mp hm).2;have := (mem_Ioc.mp hu).1;dsimp [M,U] at *;omega)
  rw [hU,sum_union hMU]
  have hh : (∑ j∈U,(f j+g j))=(∑ j∈U,(f j+g j-c*K j))+(∑ j∈U,c*K j) := by
    rw [sum_sub_distrib];abel
  rw [hh]
  apply (norm_add_le _ _).trans ((add_le_add hne ((norm_add_le _ _).trans (add_le_add hfar hk))).trans_eq ?_)
  ring

end AnalyticNumberTheory.ExponentialSums
