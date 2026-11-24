import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# A Fejér inequality for finite power sums

The lower bound for the real part of a triangularly weighted power sum holds
on the closed unit disk. A second nonnegative weight detects a distinguished
point on the unit circle while all other points have bounded negative part.
-/

noncomputable section
open Finset Complex
open scoped ComplexConjugate
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- The nonconstant part of the unnormalized analytic Fejér kernel, evaluated
at z. The mode j+1 has coefficient K-j. -/
def fejerPowerSum (K : ℕ) (z : ℂ) : ℝ :=
  ∑ j ∈ range K, ((K:ℝ)-j) * (z^(j+1)).re

private theorem fejerPowerSum_succ (K : ℕ) (z : ℂ) :
    fejerPowerSum (K+1) z = fejerPowerSum K z + (z*∑ j ∈ range (K+1),z^j).re := by
  unfold fejerPowerSum
  rw [mul_sum,Complex.re_sum]
  simp_rw [← pow_succ']
  rw [sum_range_succ, sum_range_succ (f := fun i => (z^(i+1)).re)]
  push_cast
  have hw (i : ℕ) : ((K:ℝ)+1-i)*(z^(i+1)).re = ((K:ℝ)-i)*(z^(i+1)).re + (z^(i+1)).re := by ring
  simp_rw [hw]
  rw [sum_add_distrib]
  ring

/-- Positivity of the Fejér kernel on the entire closed complex unit disk. -/
theorem fejerPowerSum_lower_bound (K : ℕ) {z : ℂ} (hz : ‖z‖≤1) :
    -((K:ℝ)+1)/2 ≤ fejerPowerSum K z := by
  let P := fun n : ℕ => ∑ i ∈ range n,z^i
  have hp (n : ℕ) : P (n+1) = 1+z*P n := by
    dsimp [P]
    rw [sum_range_succ',mul_sum]
    simp [pow_succ',add_comm]
  have hsq (w : ℂ) : normSq (1+w) = 1+2*w.re+normSq w := by
    rw [Complex.normSq_add]
    simp
    ring
  have hident (n : ℕ) : ((n:ℝ)+1)+2*fejerPowerSum n z =
      normSq (P (n+1)) + (1-normSq z)*∑ j ∈ range n,normSq (P (j+1)) := by
    induction n with
    | zero => simp [P,fejerPowerSum]
    | succ n ih =>
      rw [fejerPowerSum_succ, sum_range_succ (f := fun j => normSq (P (j+1))), hp (n+1),hsq,Complex.normSq_mul]
      change _+2*(fejerPowerSum n z + (z*P (n+1)).re) = _
      push_cast
      linarith
  have hnon : 0 ≤ (1-normSq z)*∑ j ∈ range K,normSq (P (j+1)) := by
    apply mul_nonneg _ (sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  linarith [hident K,Complex.normSq_nonneg (P (K+1))]

private theorem fejerPowerSum_one (K : ℕ) : fejerPowerSum K 1 = K*((K:ℝ)+1)/2 := by
  induction K with
  | zero => simp [fejerPowerSum]
  | succ K ih =>
    rw [fejerPowerSum_succ,ih]
    simp
    ring

/-- A nonnegative coefficient used to detect the phase of a chosen power. -/
def fejerPhaseWeight (K j : ℕ) (v : ℂ) : ℝ :=
  ((K:ℝ)-j)*(1+(v^(j+1)).re)

theorem fejerPhaseWeight_nonneg {j K : ℕ} (hj : j∈range K) {v : ℂ} (hv : ‖v‖=1) :
    0 ≤ fejerPhaseWeight K j v := by
  have h := Complex.abs_re_le_norm (v^(j+1))
  rw [norm_pow,hv,one_pow] at h
  dsimp [fejerPhaseWeight]
  exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast (mem_range.mp hj).le)) (by linarith [(abs_le.mp h).1])

theorem fejerPhaseWeight_le {j K : ℕ} (hj : j∈range K) {v : ℂ} (hv : ‖v‖=1) :
    fejerPhaseWeight K j v ≤ 2*K := by
  have h := Complex.re_le_norm (v^(j+1))
  rw [norm_pow,hv,one_pow] at h
  have hj' : (j:ℝ)≤K := by exact_mod_cast (mem_range.mp hj).le
  change ((K:ℝ)-j)*(1+_) ≤ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hj') (sub_nonneg.mpr h),Nat.cast_nonneg (α:=ℝ) j]

private theorem sum_phaseWeight_eq (K : ℕ) (v z : ℂ) :
    ∑ j ∈ range K, fejerPhaseWeight K j v*(z^(j+1)).re =
      fejerPowerSum K z + (fejerPowerSum K (v*z)+fejerPowerSum K (conj v*z))/2 := by
  unfold fejerPhaseWeight fejerPowerSum
  simp only [mul_pow,← map_pow,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  rw [add_div]
  simp_rw [sum_div]
  rw [← sum_add_distrib,← sum_add_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

/-- Each point of the disk has a lower bound independent of its phase. -/
theorem sum_phaseWeight_lower {v z : ℂ} (hv : ‖v‖=1) (hz : ‖z‖≤1) (K : ℕ) :
    -((K:ℝ)+1) ≤ ∑ j ∈ range K, fejerPhaseWeight K j v*(z^(j+1)).re := by
  rw [sum_phaseWeight_eq]
  have h1 := fejerPowerSum_lower_bound K hz
  have h2 := fejerPowerSum_lower_bound K (z:=v*z) (by simpa [norm_mul,hv])
  have h3 := fejerPowerSum_lower_bound K (z:=conj v*z) (by simpa [norm_mul,hv])
  linarith

/-- The distinguished unit phase contributes quadratically in K. -/
theorem sum_phaseWeight_self_lower {v : ℂ} (hv : ‖v‖=1) (K : ℕ) :
    ((K:ℝ)+1)*(K-3:ℝ)/4 ≤ ∑ j ∈ range K, fejerPhaseWeight K j v*(v^(j+1)).re := by
  have hc : conj v*v=1 := by rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,hv]; norm_num
  rw [sum_phaseWeight_eq,hc,fejerPowerSum_one]
  have h1 := fejerPowerSum_lower_bound K hv.le
  have h2 := fejerPowerSum_lower_bound K (z:=v*v) (by simp [norm_mul,hv])
  linarith

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
