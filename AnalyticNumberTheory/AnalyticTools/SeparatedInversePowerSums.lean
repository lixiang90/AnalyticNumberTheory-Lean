import AnalyticNumberTheory.AnalyticTools.SeparatedLaplaceSums
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues

/-!
# Inverse powers at points with individual spacings

Integration of the one-sided exponential estimate gives the lattice constant for
inverse powers. A reflected copy gives the two-sided bounds for the quadratic
and quartic kernels in the weighted Hilbert inequality.
-/

open Finset Real MeasureTheory Set
namespace AnalyticNumberTheory.AnalyticTools

private noncomputable def momentKernel (k : ℕ) (b t : ℝ) := t^((k:ℝ)-1)*exp (-(b*t))

private theorem momentKernel_integrable {k : ℕ} {b : ℝ} (hk : 0<k) (hb : 0<b) :
    IntegrableOn (momentKernel k b) (Ioi 0) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  unfold momentKernel
  simpa [neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s:=(k:ℝ)-1) (by linarith) (p:=1) one_pos hb)

private theorem integral_momentKernel {k : ℕ} {b : ℝ} (hk : 0<k) (hb : 0<b) :
    ∫t in Ioi 0,momentKernel k b t=(1/b)^k*Gamma k := by
  simpa [momentKernel] using integral_rpow_mul_exp_neg_mul_Ioi (a:=(k:ℝ)) (by exact_mod_cast hk) hb

private theorem geometric_moment_sum {t a : ℝ} (ht : 0<t) (ha : 0<a) (k : ℕ) :
    ∑'n : ℕ,a*momentKernel k (((n:ℝ)+1)*a) t=t^((k:ℝ)-1)*latticeExponentialTail t a := by
  let r := exp (-(t*a))
  have hr : r<1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos ht ha))
  have H := ((hasSum_geometric_of_lt_one (exp_pos _).le hr).mul_right r).mul_left (a*t^((k:ℝ)-1))
  have he (n : ℕ) : r^n*r=exp (-((((n:ℝ)+1)*a)*t)) := by
    dsimp [r]; rw [← Real.exp_nat_mul,←Real.exp_add]; congr 1; ring
  have he' : (1-r)⁻¹*r=1/(exp (t*a)-1) := by
    dsimp [r]; rw [Real.exp_neg]
    have hpos : 0<exp (t*a)-1 := sub_pos.mpr (one_lt_exp_iff.mpr (mul_pos ht ha))
    field_simp [hpos.ne']
  rw [←show a*t^((k:ℝ)-1)*((1-r)⁻¹*r)=t^((k:ℝ)-1)*latticeExponentialTail t a by
    rw [he',latticeExponentialTail]; ring,←H.tsum_eq]
  exact tsum_congr fun n => by rw [he]; dsimp [momentKernel]; ring

/-- On one side of a point, the sharp inverse-power bound has the same constant as an
equally spaced lattice. The series is indexed starting at one. -/
theorem sum_separated_inverse_power_right {ι : Type*} (S : Finset ι) (x δ : ι→ℝ)
    {k : ℕ} {L a w : ℝ} (hk : 0<k) (hL : 0<L)
    (hseries : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^k) L)
    (ha : 0<a) (hδ : ∀i∈S, 0<δ i) (hleft : ∀i∈S, max a (δ i)≤x i-w)
    (hsep : ∀i∈S, ∀j∈S, i≠j → δ i≤|x i-x j|) :
    (∑i∈S,δ i/(x i-w)^k)≤a/a^k*L := by
  let F (n : ℕ) (t : ℝ) := a*momentKernel k (((n:ℝ)+1)*a) t
  have hr (n : ℕ) : 0<((n:ℝ)+1)*a := by positivity
  have hI (n : ℕ) : IntegrableOn (F n) (Ioi 0) := (momentKernel_integrable hk (hr n)).const_mul a
  let c := a/a^k*Gamma k
  have hc : 0<c := by dsimp [c]; positivity
  have hFn (n : ℕ) : ∫t in Ioi 0,F n t=c*(1/((n:ℝ)+1)^k) := by
    dsimp only [F]
    rw [integral_const_mul,integral_momentKernel hk (hr n)]
    dsimp [c]; rw [div_pow,mul_pow]; ring
  have hn (n : ℕ) : ∫t in Ioi 0,‖F n t‖=∫t in Ioi 0,F n t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => Real.norm_of_nonneg ?_
    dsimp [F,momentKernel]; exact mul_nonneg ha.le (mul_nonneg (Real.rpow_nonneg ht.le _) (exp_pos _).le)
  have hFs : HasSum (fun n : ℕ => ∫t in Ioi 0,F n t) (c*L) :=
    (hseries.mul_left c).congr_fun fun n => hFn n
  have hFnorm : Summable (fun n : ℕ => ∫t in Ioi 0,‖F n t‖) := hFs.summable.congr fun n => (hn n).symm
  have hval := hFs.unique (hasSum_integral_of_summable_integral_norm hI hFnorm)
  have hsumI : IntegrableOn (fun t => ∑'n,F n t) (Ioi 0) := by
    by_contra h
    have hz := integral_undef h
    exact (mul_pos hc hL).ne' (hval.trans hz)
  have hx i (hi : i∈S) : 0<x i-w := ha.trans_le ((le_max_left _ _).trans (hleft i hi))
  have hiI i (hi : i∈S) : IntegrableOn (fun t => δ i*momentKernel k (x i-w) t) (Ioi 0) :=
    (momentKernel_integrable hk (hx i hi)).const_mul _
  have hcomp := setIntegral_mono_on (s:=Ioi 0) (integrable_finsetSum S hiI) hsumI measurableSet_Ioi
    (fun t ht => show (∑i∈S,δ i*momentKernel k (x i-w) t)≤∑'n,F n t from by
      rw [show (∑'n,F n t)=_ from geometric_moment_sum ht ha k]
      have H := mul_le_mul_of_nonneg_left (sum_separated_exponential_right S x δ ht ha hδ hleft hsep)
        (Real.rpow_nonneg ht.le ((k:ℝ)-1))
      rw [mul_sum] at H
      convert H using 1; refine sum_congr rfl fun i _ => ?_; dsimp [momentKernel]; rw [mul_comm t (x i-w)]; ring)
  rw [←hval,integral_finsetSum S hiI] at hcomp
  have hh : (∑i∈S,∫t in Ioi 0,δ i*momentKernel k (x i-w) t)=(∑i∈S,δ i/(x i-w)^k)*Gamma k := by
    rw [sum_mul]; refine sum_congr rfl fun i hi => ?_
    rw [integral_const_mul,integral_momentKernel hk (hx i hi),div_pow,one_pow]; ring
  rw [hh] at hcomp
  apply (mul_le_mul_iff_left₀ (Gamma_pos_of_pos (show 0<(k:ℝ) by exact_mod_cast hk))).mp
  dsimp [c] at hcomp
  simpa only [mul_right_comm (a/a^k) _ L] using hcomp

/-- Both sides of an external point contribute at most one copy of the zeta sum. -/
theorem sum_separated_inverse_power {ι : Type*} (S : Finset ι) (x δ : ι→ℝ)
    {k : ℕ} {L a w : ℝ} (hk : 0<k) (hL : 0<L)
    (hseries : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^k) L)
    (ha : 0<a) (hδ : ∀i∈S, 0<δ i) (hdist : ∀i∈S, max a (δ i)≤|x i-w|)
    (hsep : ∀i∈S, ∀j∈S, i≠j → δ i≤|x i-x j|) :
    (∑i∈S,δ i/|x i-w|^k)≤2*(a/a^k*L) := by
  classical
  let P := S.filter (fun i => w≤x i)
  let N := S.filter (fun i => ¬w≤x i)
  have hP i (hi : i∈P) : |x i-w|=x i-w := abs_of_nonneg (sub_nonneg.mpr (mem_filter.mp hi).2)
  have hN i (hi : i∈N) : |x i-w|= -x i- -w := by
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge (mem_filter.mp hi).2))]; ring
  have hp := sum_separated_inverse_power_right P x δ hk hL hseries ha
    (fun i hi => hδ i (mem_filter.mp hi).1)
    (fun i hi => (hdist i (mem_filter.mp hi).1).trans_eq (hP i hi))
    (fun i hi j hj => hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1)
  have hn := sum_separated_inverse_power_right N (fun i => -x i) δ hk hL hseries ha
    (fun i hi => hδ i (mem_filter.mp hi).1)
    (fun i hi => (hdist i (mem_filter.mp hi).1).trans_eq (hN i hi))
    (fun i hi j hj hij => by
      rw [neg_sub_neg,abs_sub_comm (x j) (x i)]
      exact hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij)
  rw [←sum_filter_add_sum_filter_not S (fun i => w≤x i)]
  change (∑i∈P,δ i/|x i-w|^k)+(∑i∈N,δ i/|x i-w|^k)≤_
  rw [sum_congr rfl (fun i hi => by rw [hP i hi]),sum_congr (s₁:=N) rfl (fun i hi => by rw [hN i hi])]
  linarith

/-- The sharp quadratic spacing estimate with the local gaps as weights. -/
theorem sum_separated_inverse_square {ι : Type*} (S : Finset ι) (x δ : ι→ℝ)
    {a w : ℝ} (ha : 0<a) (hδ : ∀i∈S, 0<δ i) (hdist : ∀i∈S, max a (δ i)≤|x i-w|)
    (hsep : ∀i∈S, ∀j∈S, i≠j → δ i≤|x i-x j|) :
    (∑i∈S,δ i/(x i-w)^2)≤π^2/(3*a) := by
  have H := sum_separated_inverse_power S x δ (k:=2) (L:=π^2/6) (by decide) (by positivity)
    (by simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two) ha hδ hdist hsep
  simpa only [sq_abs,show 2*(a/a^2*(π^2/6))=π^2/(3*a) by field_simp; ring] using H

/-- The sharp quartic spacing estimate with the local gaps as weights. -/
theorem sum_separated_inverse_fourth {ι : Type*} (S : Finset ι) (x δ : ι→ℝ)
    {a w : ℝ} (ha : 0<a) (hδ : ∀i∈S, 0<δ i) (hdist : ∀i∈S, max a (δ i)≤|x i-w|)
    (hsep : ∀i∈S, ∀j∈S, i≠j → δ i≤|x i-x j|) :
    (∑i∈S,δ i/(x i-w)^4)≤π^4/(45*a^3) := by
  have H := sum_separated_inverse_power S x δ (k:=4) (L:=π^4/90) (by decide) (by positivity)
    (by simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four) ha hδ hdist hsep
  have hfour (v : ℝ) : |v|^4=v^4 := by rw [show 4=2*2 by decide,pow_mul,pow_mul,sq_abs]
  simpa only [hfour,show 2*(a/a^4*(π^4/90))=π^4/(45*a^3) by field_simp; ring] using H

end AnalyticNumberTheory.AnalyticTools
