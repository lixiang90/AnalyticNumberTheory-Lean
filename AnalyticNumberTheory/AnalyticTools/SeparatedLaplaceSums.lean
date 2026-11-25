import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exponential sums at points with individual spacings

The sum over a separated set on one side of an external point is dominated by
the corresponding equally spaced exponential sum. Each sample carries its own
local separation. The potential a/(exp(ta)−1) telescopes after removal of the
nearest sample and yields the sharp lattice constant for inverse-power kernels.
-/

open Finset Real
namespace AnalyticNumberTheory.AnalyticTools

/-- Tail mass for an equally spaced exponential sum, excluding its origin. -/
noncomputable def latticeExponentialTail (t a : ℝ) := a/(exp (t*a)-1)

private theorem tail_den_pos {t a : ℝ} (ht : 0<t) (ha : 0<a) : 0<exp (t*a)-1 :=
  sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ht ha))

theorem latticeExponentialTail_antitone {t a b : ℝ} (ht : 0<t) (ha : 0<a) (hab : a≤b) :
    latticeExponentialTail t b≤latticeExponentialTail t a := by
  rcases hab.eq_or_lt with rfl|hab
  · rfl
  have h := convexOn_exp.secant_mono_aux1 (x:=0) (y:=t*a) (z:=t*b) (Set.mem_univ _) (Set.mem_univ _)
    (mul_pos ht ha) (mul_lt_mul_of_pos_left hab ht)
  rw [Real.exp_zero] at h
  rw [latticeExponentialTail,latticeExponentialTail,div_le_div_iff₀ (tail_den_pos ht (ha.trans hab)) (tail_den_pos ht ha)]
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith

private theorem add_latticeExponentialTail {t a : ℝ} (ht : 0<t) (ha : 0<a) :
    a+latticeExponentialTail t a=a/(1-exp (-(t*a))) := by
  have hE := tail_den_pos ht ha
  rw [latticeExponentialTail,Real.exp_neg]
  have hden : (1-(exp (t*a))⁻¹)=(exp (t*a)-1)/exp (t*a) := by
    field_simp
  rw [hden, div_div_eq_mul_div]
  rw [eq_div_iff hE.ne',add_mul,div_mul_cancel₀ _ hE.ne']
  ring

theorem add_latticeExponentialTail_mono {t a b : ℝ} (ht : 0<t) (ha : 0<a) (hab : a≤b) :
    a+latticeExponentialTail t a≤b+latticeExponentialTail t b := by
  rcases hab.eq_or_lt with rfl|hab
  · rfl
  have h := convexOn_exp.secant_mono_aux1 (x:= -(t*b)) (y:= -(t*a)) (z:=0)
    (Set.mem_univ _) (Set.mem_univ _) (neg_lt_neg (mul_lt_mul_of_pos_left hab ht)) (neg_lt_zero.mpr (mul_pos ht ha))
  rw [Real.exp_zero] at h
  have hx (v : ℝ) (hv : 0<v) : 0<1-exp (-(t*v)) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  rw [add_latticeExponentialTail ht ha,add_latticeExponentialTail ht (ha.trans hab),
    div_le_div_iff₀ (hx a ha) (hx b (ha.trans hab))]
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith

private theorem exp_mul_add_tail {t a : ℝ} (ht : 0<t) (ha : 0<a) :
    exp (-(t*a))*(a+latticeExponentialTail t a)=latticeExponentialTail t a := by
  have h := tail_den_pos ht ha
  rw [latticeExponentialTail,Real.exp_neg]
  field_simp; ring

/-- A one-sided Laplace bound for a finite separated set with varying local spacings. -/
theorem sum_separated_exponential_right {ι : Type*} (S : Finset ι) (x δ : ι→ℝ)
    {t a w : ℝ} (ht : 0<t) (ha : 0<a)
    (hδ : ∀i∈S, 0<δ i) (hleft : ∀i∈S, max a (δ i)≤x i-w)
    (hsep : ∀ i∈S, ∀j∈S, i≠j → δ i≤|x i-x j|) :
    (∑i∈S,δ i*exp (-(t*(x i-w))))≤latticeExponentialTail t a := by
  classical
  induction S using Finset.strongInductionOn generalizing w a with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl|hne
    · simp only [sum_empty]; exact div_nonneg ha.le (tail_den_pos ht ha).le
    obtain ⟨m,hm,hmin⟩ := exists_min_image S x hne
    let T := S.erase m
    have hT : T ⊆ S := erase_subset ..
    have hmin' (i : ι) (hi : i∈T) : max (δ m) (δ i)≤x i-x m := by
      have hne := (mem_erase.mp hi).1
      have hx := hmin i (hT hi)
      have hi' := hsep i (hT hi) m hm hne
      have hm' := hsep m hm i (hT hi) hne.symm
      rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hi'
      rw [abs_of_nonpos (sub_nonpos.mpr hx)] at hm'
      exact max_le (by linarith) hi'
    have H := ih T (erase_ssubset hm) (w:=x m) (a:=δ m) (hδ m hm)
      (fun i hi => hδ i (hT hi)) hmin' (fun i hi j hj h => hsep i (hT hi) j (hT hj) h)
    let b := x m-w
    obtain ⟨hab,hdb⟩ := max_le_iff.mp (hleft m hm)
    have hb : 0<b := ha.trans_le hab
    have eqs : ∑i∈T,δ i*exp (-(t*(x i-w)))=exp (-(t*b))*∑i∈T,δ i*exp (-(t*(x i-x m))) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [show -(t*(x i-w))= -(t*b)+ -(t*(x i-x m)) by dsimp [b]; ring,Real.exp_add]; ring
    rw [←sum_erase_add S _ hm]
    change (∑i∈T,δ i*exp (-(t*(x i-w))))+δ m*exp (-(t*b))≤_
    rw [eqs]
    calc
      _ ≤ exp (-(t*b))*(δ m+latticeExponentialTail t (δ m)) := by nlinarith [mul_le_mul_of_nonneg_left H (exp_pos (-(t*b))).le]
      _ ≤ exp (-(t*b))*(b+latticeExponentialTail t b) :=
        mul_le_mul_of_nonneg_left (add_latticeExponentialTail_mono ht (hδ m hm) hdb) (exp_pos _).le
      _ = latticeExponentialTail t b := exp_mul_add_tail ht hb
      _ ≤ _ := latticeExponentialTail_antitone ht ha hab

end AnalyticNumberTheory.AnalyticTools
