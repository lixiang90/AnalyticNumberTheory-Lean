import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Reassembling mean squares over short blocks

A separate positive large-sieve constant is assigned to every block.
Weighted Cauchy–Schwarz adds these constants while the disjoint block
energies add to the energy of the full polynomial.
-/
open Real Complex Finset
namespace AnalyticNumberTheory.SieveMethods

/-- Reassembly of finite mean squares with a distinct sampling constant on each block. -/
theorem sampling_sum_of_blocks {ι κ : Type*} (S : Finset ι) (J : Finset κ)
    (f : κ→ι→ℂ) (B E : κ→ℝ) (hB : ∀j∈J,0<B j)
    (h : ∀ j∈J,(∑i∈S,‖f j i‖^2)≤B j*E j) :
    (∑i∈S,‖∑j∈J,f j i‖^2)≤(∑j∈J,B j)*(∑j∈J,E j) := by
  rcases J.eq_empty_or_nonempty with rfl|hJ
  · simp
  have hb := sum_pos hB hJ
  have hh (i) : ‖∑j∈J,f j i‖^2 ≤ (∑j∈J,B j)*(∑j∈J,‖f j i‖^2/B j) := by
    have cs := sq_sum_div_le_sum_sq_div J (fun j => ‖f j i‖) hB
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2).trans
      (((div_le_iff₀ hb).mp cs).trans_eq (mul_comm ..))
  apply (sum_le_sum (fun i _ => hh i)).trans
  rw [←mul_sum,sum_comm (s:=S)]
  apply mul_le_mul_of_nonneg_left _ hb.le
  apply sum_le_sum;intro j hj
  rw [←Finset.sum_div,div_le_iff₀ (hB j hj)]
  exact (h j hj).trans_eq (mul_comm ..)

/-- Summing the small length saving over dyadic scales costs one logarithm
in the conductor-height parameter, independently of the number of scales. -/
theorem dyadic_kernel_decay_sum {H : ℝ} (hH : 1≤H) (J : Finset ℕ) :
    (∑j∈J,((2:ℝ)^j)^(-(1/(4+Real.log H))))≤10*(1+Real.log H) := by
  let δ := 1/(4+Real.log H)
  have hl := Real.log_nonneg hH
  have hδ : 0<δ := by dsimp [δ];positivity
  let x := δ*Real.log 2
  have hl₂ : 1/2≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : 0<x := mul_pos hδ (by linarith)
  have hq : Real.exp (-x)<1 := by simpa using Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  have hpow (j:ℕ) : ((2:ℝ)^j)^(-δ)=Real.exp (-x)^j := by
    rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,←Real.exp_nat_mul];congr 1;dsimp [x];ring
  simp_rw [show -(1/(4+Real.log H))= -δ by rfl,hpow]
  have hu := (summable_geometric_of_lt_one (Real.exp_pos (-x)).le hq).sum_le_tsum J (fun j _ => pow_nonneg (Real.exp_pos _).le j)
  rw [tsum_geometric_of_lt_one (Real.exp_pos (-x)).le hq] at hu
  have hh : (1-Real.exp (-x))⁻¹≤1+1/x := by
    have he := Real.add_one_le_exp x
    rw [inv_le_iff_one_le_mul₀ (sub_pos.mpr hq)]
    rw [Real.exp_neg]
    have he' : (Real.exp x)⁻¹≤(1+x)⁻¹ := inv_anti₀ (by linarith) (by linarith only [he])
    have hc := mul_le_mul_of_nonneg_right (sub_le_sub_left he' 1) (show 0≤1+1/x by positivity)
    rw [mul_comm (1+1/x)]
    apply le_trans _ hc
    field_simp <;> ring_nf <;> rfl
  have hxlarge : 1/x≤2*(4+Real.log H) := by
    dsimp [x,δ];rw [one_div_mul_eq_div,one_div_div]
    apply (div_le_iff₀ (by linarith : 0<Real.log 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hl₂ (show 0≤2*(4+Real.log H) by positivity)]
  exact hu.trans (hh.trans (by linarith))
end AnalyticNumberTheory.SieveMethods
