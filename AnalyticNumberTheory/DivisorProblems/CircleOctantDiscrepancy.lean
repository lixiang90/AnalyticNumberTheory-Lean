import AnalyticNumberTheory.DivisorProblems.CircleArc
import AnalyticNumberTheory.DivisorProblems.CircleOctants
import AnalyticNumberTheory.DivisorProblems.SawtoothErrors

/-!
# The octant sawtooth formula in Gauss's circle problem

Euler–Maclaurin summation up to the real diagonal cutoff retains its boundary
term. The remaining integral has bounded size because the first octant has
bounded slope and the second derivative has bounded integral.
-/

noncomputable section
open Finset Real MeasureTheory
open scoped Classical Topology
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.DivisorProblems

/-- Integrating the first periodic Bernoulli correction along the octant
costs at most an absolute constant, independently of the radius. -/
theorem circleArc_first_order_remainder {x : ℝ} (hx : 0<x) :
    |∫ t in (0:ℝ)..Real.sqrt (x/2), sawtooth t*(-t/circleArc x t)| ≤ 1/4 := by
  let u := Real.sqrt (x/2)
  let f := circleArc x
  let g (t : ℝ) := -t/f t
  let d (t : ℝ) := -x/(f t)^3
  have hu : 0<u := Real.sqrt_pos.mpr (by linarith)
  have hu2 : u^2=x/2 := Real.sq_sqrt (by linarith)
  have hu' : f u=u := by dsimp only [f,circleArc]; rw [hu2,show x-x/2=x/2 by ring]
  have hs (t : ℝ) (ht : t∈Set.Icc 0 u) : t^2≤x/2 := by
    rw [←hu2]; exact pow_le_pow_left₀ ht.1 ht.2 _
  have hf (t : ℝ) (ht : t∈Set.Icc 0 u) : u≤f t := Real.sqrt_le_sqrt (by linarith [hs t ht])
  have hg (t : ℝ) (ht : t∈Set.Icc 0 u) : HasDerivAt g (d t) t :=
    circleArc_deriv_hasDerivAt (by linarith [hs t ht])
  have hd : ContinuousOn d (Set.Icc 0 u) :=
    continuousOn_const.div ((continuous_circleArc x).continuousOn.pow 3) (fun t ht => pow_ne_zero 3 (hu.trans_le (hf t ht)).ne')
  have he := integral_bernoulliKernel_mul_eq_sub (j:=1) le_rfl hu.le hg hd
  simp only [bernoulliKernel_one,show 1+1=2 by rfl] at he
  change |∫ t in (0:ℝ)..u,sawtooth t*g t| ≤ _
  rw [he,show g 0=0 by simp [g],mul_zero,sub_zero,show g u = -1 by dsimp only [g]; rw [hu']; field_simp]
  have hi : |∫ t in (0:ℝ)..u, bernoulliKernel 2 t*d t| ≤ 1/6 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=u) (C:=(1/12)*(2/u))
      (f:=fun t => bernoulliKernel 2 t*d t) (fun t ht => by
        rw [Set.uIoc_of_le hu.le] at ht
        have hft := hf t ⟨ht.1.le,ht.2⟩
        have hftp := hu.trans_le hft
        rw [Real.norm_eq_abs,abs_mul]
        apply mul_le_mul (bernoulliKernel_two_abs_le _) _ (abs_nonneg _) (by norm_num)
        rw [show |d t| = x/(f t)^3 by dsimp only [d]; rw [abs_div,abs_neg,abs_of_pos hx,abs_of_pos (pow_pos hftp 3)]]
        apply (div_le_div_iff₀ (pow_pos hftp _) hu).mpr
        have hh := pow_le_pow_left₀ hu.le hft 3
        nlinarith only [congrArg (fun y : ℝ => y*u) hu2,hh])
    rw [Real.norm_eq_abs,sub_zero,abs_of_pos hu] at hb
    apply hb.trans_eq; field_simp; ring
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_neg,abs_one,mul_one]
  linarith only [hi,bernoulliKernel_two_abs_le u]

/-- The Gauss circle error differs by a bounded amount from minus eight
times the sawtooth sum along the octant. The bound includes diagonal and
axis lattice points, also when a cutoff is integral. -/
theorem abs_gaussCircleError_add_octant_sawtooth_le {x : ℝ} (hx : 0<x) :
    |gaussCircleError x +
      8*∑ n ∈ Icc 1 ⌊Real.sqrt (x/2)⌋₊, sawtooth (circleArc x n)| ≤ 8 := by
  let u := Real.sqrt (x/2)
  let M := ⌊u⌋₊
  let R := Real.sqrt x
  let f := circleArc x
  let g (t : ℝ) := -t/f t
  let J := ∫ t in (0:ℝ)..u,sawtooth t*g t
  have hu : 0<u := Real.sqrt_pos.mpr (by linarith)
  have hu2 : u^2=x/2 := Real.sq_sqrt (by linarith)
  have hfu : f u=u := by dsimp only [f,circleArc]; rw [hu2,show x-x/2=x/2 by ring]
  have hf0 : f 0=R := by simp [f,circleArc,R]
  have hs (t : ℝ) (ht : t∈Set.Icc 0 u) : t^2<x := by
    have hh := pow_le_pow_left₀ ht.1 ht.2 2; linarith only [hh,hu2,hx]
  have hg : ContinuousOn g (Set.Icc 0 u) := fun t ht => (circleArc_deriv_hasDerivAt (hs t ht)).continuousAt.continuousWithinAt
  have he := euler_maclaurin_first_order_Ioc_nat (a:=0) (b:=u) (f:=f) (f':=g) le_rfl hu.le
    (fun t ht => circleArc_hasDerivAt (hs t ht)) hg
  have hI : Ioc 0 M=Icc 1 M := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  change ∑ n ∈ Ioc ⌊(0:ℝ)⌋₊ M,f n = (∫ t in (0:ℝ)..u,f t)+J-(sawtooth u*f u-sawtooth 0*f 0) at he
  rw [Nat.floor_zero,hI,integral_circleArc_to_diagonal hx.le,hfu,hf0,show sawtooth 0= -1/2 by norm_num [sawtooth]] at he
  have hfl (t : ℝ) : (⌊f t⌋₊:ℝ)=f t-1/2-sawtooth (f t) := nat_floor_eq_sub_half_sub_sawtooth (Real.sqrt_nonneg _)
  have hct := gaussCircleCount_eq_octant_slices hx.le
  change gaussCircleCount x = 4*(⌊R⌋₊:ℝ)+1+8*(∑ n ∈ Icc 1 M,(⌊f n⌋₊:ℝ))-4*(M:ℝ)^2 at hct
  simp_rw [hfl] at hct
  simp only [sum_sub_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hct
  have hMu : (M:ℝ)≤u := Nat.floor_le hu.le
  have huM : u<(M:ℝ)+1 := Nat.lt_floor_add_one u
  have hR₀ : 0≤R := Real.sqrt_nonneg _
  have hR₁ := Nat.floor_le hR₀
  have hR₂ := Nat.lt_floor_add_one R
  have huψ := nat_floor_eq_sub_half_sub_sawtooth hu.le
  change (M:ℝ)=u-1/2-sawtooth u at huψ
  have hJ : |J|≤1/4 := circleArc_first_order_remainder hx
  have hprod₀ := mul_nonneg (sub_nonneg.mpr hMu) (by linarith : 0≤1-(u-(M:ℝ)))
  have hprod₁ : (u-(M:ℝ))*(1-(u-(M:ℝ)))≤1 := by nlinarith only [sq_nonneg (u-(M:ℝ)-1/2)]
  have hform : gaussCircleError x + 8*∑ n ∈ Icc 1 M,sawtooth (f n) =
      4*((⌊R⌋₊:ℝ)-R)+1+4*((u-(M:ℝ))*(1-(u-(M:ℝ))))+8*J := by
    unfold gaussCircleError
    nlinarith only [hct,he,hu2,congrArg (fun y : ℝ => y*u) huψ]
  rw [hform]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hJ).1],by linarith [(abs_le.mp hJ).2]⟩

end AnalyticNumberTheory.DivisorProblems
