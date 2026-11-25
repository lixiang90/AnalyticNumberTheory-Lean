import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans

/-!
# Euler–Maclaurin's formula at a real Hurwitz cutoff

The cutoff is independent of the shift of the progression. The boundary
terms carry the first and second periodic Bernoulli functions.
-/
noncomputable section
open Real Complex Filter Finset MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- Direct Hurwitz polynomial up to the real cutoff x, for 0<a≤x. -/
def hurwitzDirectSum (a x : ℝ) (s : ℂ) :=
  ∑ n∈Icc 0 ⌊x-a⌋₊,((n:ℂ)+a)^(-s)

private theorem cell_correction (a : ℝ) (s : ℂ) (hs : s≠1) {N : ℕ} {r : ℝ}
    (ha : 0<a) (hr : (N:ℝ)≤r) (hr' : r<(N:ℝ)+1) :
    let f (u : ℝ) (k : ℂ) := ((u+a:ℝ):ℂ)^k
    let P (u : ℝ) := f u (1-s)/(1-s) - (sawtooth u:ℂ)*f u (-s) -
      (bernoulliKernel 2 u:ℂ)*s*f u (-s-1)
    P r-P N = s*(s+1)*∫ u in (N:ℝ)..r,(bernoulliKernel 2 u:ℂ)*f u (-s-2) := by
  intro f P
  let v (u : ℝ) : ℂ := (u:ℂ)-N
  let W (u : ℝ) := v u-1/2
  let B (u : ℝ) := ((v u)^2-v u+1/6)/2
  let Q (u : ℝ) := f u (1-s)/(1-s)-W u*f u (-s)-B u*s*f u (-s-1)
  have he (u : ℝ) (hu : u∈Set.Icc (N:ℝ) r) : W u=(sawtooth u:ℂ) ∧ B u=(bernoulliKernel 2 u:ℝ) := by
    have hfl : ⌊u⌋=(N:ℤ) := Int.floor_eq_iff.mpr ⟨by simpa using hu.1,by simpa using hu.2.trans_lt hr'⟩
    dsimp [v,W,B,sawtooth]; rw [bernoulliKernel_two]; simp only [Int.fract,hfl,Int.cast_natCast]
    push_cast; constructor <;> ring
  have heQ (u : ℝ) (hu : u∈Set.Icc (N:ℝ) r) : Q u=P u := by dsimp [Q,P]; rw [(he u hu).1,(he u hu).2]
  have hd (u : ℝ) (hu : u∈Set.Icc (N:ℝ) r) : HasDerivAt Q
      (s*(s+1)*((bernoulliKernel 2 u:ℂ)*f u (-s-2))) u := by
    have hp : 0<u+a := by linarith [hu.1,Nat.cast_nonneg (α:=ℝ) N]
    have hF (k : ℂ) := cpow_shift_hasDerivAt hp k
    have hv : HasDerivAt v 1 u := by simpa [v] using ((hasDerivAt_id u).ofReal_comp.sub_const (N:ℂ))
    have hW := hv.sub_const (1/2)
    have hB := (((hv.pow 2).sub hv).add_const (1/6)).div_const (2:ℂ)
    have h := ((((hF (1-s)).div_const (1-s)).sub (hW.mul (hF (-s)))).sub
      ((hB.mul_const s).mul (hF (-s-1))))
    change HasDerivAt Q _ u at h
    convert h using 1
    rw [←(he u hu).2]
    dsimp only [f,B,W,Pi.sub_apply,Pi.pow_apply]
    rw [show 1-s-1= -s by ring,show -s-1-1= -s-2 by ring]
    field_simp [sub_ne_zero.mpr (Ne.symm hs)]; ring
  have hi : ContinuousOn (fun u => s*(s+1)*((bernoulliKernel 2 u:ℂ)*f u (-s-2))) (Set.Icc (N:ℝ) r) := by
    apply continuousOn_const.mul
    apply (Complex.continuous_ofReal.comp (continuous_bernoulliKernel (by norm_num))).continuousOn.mul
    intro u hu
    exact (cpow_shift_hasDerivAt (by linarith [hu.1,Nat.cast_nonneg (α:=ℝ) N] : 0<u+a) _).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hd u ((Set.uIcc_of_le hr) ▸ hu)) (hi.intervalIntegrable_of_Icc hr)
  rw [intervalIntegral.integral_const_mul,heQ r (Set.right_mem_Icc.mpr hr),heQ N (Set.left_mem_Icc.mpr hr)] at h
  exact h.symm

/-- Second-order Hurwitz Euler–Maclaurin formula for an arbitrary real
cutoff x≥a, including the boundary at an integer translate of the shift. -/
theorem hurwitzZeta_eq_real_cutoff {a x : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) (hx : a≤x) {s : ℂ}
    (hs : -1<s.re) (hs' : s≠1) :
    HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s = hurwitzDirectSum a x s-
      (x:ℂ)^(1-s)/(1-s)+(sawtooth (x-a):ℂ)*(x:ℂ)^(-s)+
      (bernoulliKernel 2 (x-a):ℂ)*s*(x:ℂ)^(-s-1)-
      s*(s+1)*∫ u in Set.Ioi (x-a),(bernoulliKernel 2 u:ℂ)*((u+a:ℝ):ℂ)^(-s-2) := by
  let r := x-a
  let N := ⌊r⌋₊
  have hr₀ : 0≤r := sub_nonneg.mpr hx
  have hr : (N:ℝ)≤r := Nat.floor_le hr₀
  have hr' : r<(N:ℝ)+1 := Nat.lt_floor_add_one _
  have he := cell_correction a s hs' ha.1 hr hr'
  dsimp only at he
  rw [sawtooth_natCast,bernoulliKernel_two_natCast,show r+a=x by dsimp [r]; ring] at he
  push_cast at he
  have hi := integrableOn_bernoulliKernel_two_shift_cpow_Ioi (Nat.cast_nonneg N) ha.1 hs
  have hsplit := intervalIntegral.integral_interval_add_Ioi (b:=r) hi (hi.mono_set (Set.Ioi_subset_Ioi hr))
  have H := hurwitzZeta_eq_eulerMaclaurin_second_order_of_re_gt_neg_one ha N hs hs'
  dsimp only [hurwitzDirectSum,N,r] at H he hsplit ⊢
  push_cast at H he hsplit ⊢
  linear_combination H+he+s*(s+1)*hsplit

end AnalyticNumberTheory.RiemannZeta
