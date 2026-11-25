import AnalyticNumberTheory.SieveMethods.LargeSieve
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Sampling Dirichlet polynomials with an infinite Gram kernel

Finite-dimensional duality allows an infinite, smoothly weighted family
of frequencies to majorize any finite subset. Only the row and column
sums of the absolute correlations enter.
-/
open Finset Complex
open scoped ComplexConjugate
namespace AnalyticNumberTheory.SieveMethods

/-- A Gram-matrix row bound for an arbitrary finite selection of frequencies
from a square-summable sequence, with an infinite sum defining each correlation. -/
theorem sample_of_infinite_gram {ι : Type*} (S : Finset ι) (F : Finset ℕ)
    (g : ι→ℕ→ℂ) (G : ι→ι→ℂ) {D : ℝ} (hD : 0≤D)
    (hG : ∀i∈S,∀j∈S,HasSum (fun n => g i n*conj (g j n)) (G i j))
    (hr : ∀i∈S,∑j∈S,‖G i j‖≤D) (hc : ∀j∈S,∑i∈S,‖G i j‖≤D)
    (a : ℕ→ℂ) :
    ∑i∈S,‖∑n∈F,a n*g i n‖^2 ≤ D*∑n∈F,‖a n‖^2 := by
  classical
  apply (duality_iff F S g hD).mpr _ a
  intro b
  let u (n:ℕ) := ∑i∈S,b i*g i n
  let Z := ∑i∈S,∑j∈S,(b i*conj (b j))*G i j
  have hsum : HasSum (fun n => u n*conj (u n)) Z := by
    have hh := hasSum_sum (s:=S) (fun i hi => hasSum_sum (s:=S) (fun j hj =>
      (hG i hi j hj).mul_left (b i*conj (b j))))
    apply hh.congr_fun
    intro n
    dsimp only [u]
    rw [map_sum,Finset.sum_mul]
    apply sum_congr rfl;intro i hi
    rw [Finset.mul_sum]
    apply sum_congr rfl;intro j hj
    rw [map_mul];ring
  have hsq : HasSum (fun n => ‖u n‖^2) Z.re := by
    simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_re]
      using Complex.hasSum_re hsum
  have hle := sum_le_hasSum F (fun n _ => sq_nonneg (‖u n‖)) hsq
  have hpoint (i j : ι) : ‖(b i*conj (b j))*G i j‖≤
      ((‖b i‖^2+‖b j‖^2)/2)*‖G i j‖ := by
    rw [norm_mul,norm_mul,Complex.norm_conj]
    gcongr
    nlinarith [sq_nonneg (‖b i‖-‖b j‖)]
  have hn : ‖Z‖≤∑i∈S,∑j∈S,((‖b i‖^2+‖b j‖^2)/2)*‖G i j‖ :=
    (norm_sum_le ..).trans (sum_le_sum fun i _ =>
      (norm_sum_le ..).trans (sum_le_sum fun j _ => hpoint i j))
  have hrow := sum_le_sum (s:=S) (fun i hi => mul_le_mul_of_nonneg_left (hr i hi) (sq_nonneg ‖b i‖))
  have hcol := sum_le_sum (s:=S) (fun j hj => mul_le_mul_of_nonneg_left (hc j hj) (sq_nonneg ‖b j‖))
  simp_rw [mul_sum] at hrow hcol
  rw [sum_comm] at hcol
  have he : ∑i∈S,∑j∈S,((‖b i‖^2+‖b j‖^2)/2)*‖G i j‖ =
      ((∑i∈S,∑j∈S,‖b i‖^2*‖G i j‖)+(∑i∈S,∑j∈S,‖b j‖^2*‖G i j‖))/2 := by
    simp_rw [add_div,add_mul,div_mul_eq_mul_div,Finset.sum_add_distrib,←Finset.sum_div]
  rw [he] at hn
  simp only [←Finset.sum_mul] at hrow hcol
  exact hle.trans ((Complex.re_le_norm Z).trans (hn.trans (by nlinarith only [hrow,hcol])))

end AnalyticNumberTheory.SieveMethods
