import AnalyticNumberTheory.AnalyticTools.SeparatedInversePowerSums

/-!
# Row estimates for locally separated Hilbert kernels

Quadratic and quartic kernels are summable with explicit constants. The
mixed estimate controls two different poles by the single-pole estimates.
-/

open Finset Real
namespace AnalyticNumberTheory.AnalyticTools

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem univ_gap_max (x δ : ι→ℝ) (hsep : ∀i j, i≠j → δ i≤|x i-x j|)
    {s i : ι} (hi : i∈univ.erase s) : max (δ s) (δ i)≤|x i-x s| := by
  have h := (mem_erase.mp hi).1
  exact max_le ((hsep s i h.symm).trans_eq (abs_sub_comm ..)) (hsep i s h)

/-- The quadratic kernel row sum is at most π²/(3δₛ). The reciprocal is total at the diagonal. -/
theorem hilbert_quadratic_row (x δ : ι→ℝ) (hδ : ∀i, 0<δ i)
    (hsep : ∀i j, i≠j → δ i≤|x i-x j|) (s : ι) :
    (∑r,δ r/(x r-x s)^2)≤π^2/(3*δ s) := by
  rw [←sum_erase_add univ _ (mem_univ s)]
  simpa only [sub_self,zero_pow (by decide : 2≠0),div_zero,add_zero] using
    sum_separated_inverse_square (univ.erase s) x δ (hδ s) (fun i _ => hδ i)
      (fun _ hi => univ_gap_max x δ hsep hi) (fun i _ j _ => hsep i j)

/-- The quartic kernel row sum is at most π⁴/(45δₛ³). -/
theorem hilbert_quartic_row (x δ : ι→ℝ) (hδ : ∀i, 0<δ i)
    (hsep : ∀i j, i≠j → δ i≤|x i-x j|) (s : ι) :
    (∑r,δ r/(x r-x s)^4)≤π^4/(45*δ s^3) := by
  rw [←sum_erase_add univ _ (mem_univ s)]
  simpa only [sub_self,zero_pow (by decide : 4≠0),div_zero,add_zero] using
    sum_separated_inverse_fourth (univ.erase s) x δ (hδ s) (fun i _ => hδ i)
      (fun _ hi => univ_gap_max x δ hsep hi) (fun i _ j _ => hsep i j)

private theorem mixedPole_le {x a b : ℝ} (hab : a≠b) :
    1/((x-a)^2*(x-b)^2) ≤ 2*((1/(x-a)^2+1/(x-b)^2)/(a-b)^2) := by
  rcases eq_or_ne x a with rfl|hxa
  · simp only [sub_self,zero_pow (by decide : 2≠0),zero_mul,div_zero,zero_add]
    positivity
  rcases eq_or_ne x b with rfl|hxb
  · simp only [sub_self,zero_pow (by decide : 2≠0),mul_zero,div_zero,add_zero]
    positivity
  have ha := sq_pos_of_ne_zero (sub_ne_zero.mpr hxa)
  have hb := sq_pos_of_ne_zero (sub_ne_zero.mpr hxb)
  have hd := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  rw [←mul_div_assoc,le_div_iff₀ hd,div_mul_eq_mul_div,one_mul,div_le_iff₀ (mul_pos ha hb)]
  field_simp [ha.ne',hb.ne']
  nlinarith [sq_nonneg (x-a+(x-b))]

/-- Bound for the product of two quadratic kernels at distinct poles. -/
theorem hilbert_mixed_quadratic_row (x δ : ι→ℝ) (hδ : ∀i, 0<δ i)
    (hsep : ∀i j, i≠j → δ i≤|x i-x j|) {s t : ι} (hst : s≠t) :
    (∑r,δ r/((x r-x s)^2*(x r-x t)^2))≤
      (2*π^2/3)*(1/δ s+1/δ t)/(x s-x t)^2 := by
  have hx : x s≠x t := by
    intro he
    simpa [he,not_le_of_gt (hδ s)] using hsep s t hst
  calc
    _ ≤ ∑r,2*((δ r/(x r-x s)^2+δ r/(x r-x t)^2)/(x s-x t)^2) := by
      refine sum_le_sum fun r _ => ?_
      have h := mul_le_mul_of_nonneg_left (mixedPole_le (x:=x r) hx) (hδ r).le
      convert h using 1 <;> ring
    _ = 2*(((∑r,δ r/(x r-x s)^2)+(∑r,δ r/(x r-x t)^2))/(x s-x t)^2) := by
      rw [←mul_sum,←sum_div,sum_add_distrib]
    _ ≤ 2*((π^2/(3*δ s)+π^2/(3*δ t))/(x s-x t)^2) := by
      gcongr
      · exact hilbert_quadratic_row x δ hδ hsep s
      · exact hilbert_quadratic_row x δ hδ hsep t
    _ = _ := by ring

end AnalyticNumberTheory.AnalyticTools
