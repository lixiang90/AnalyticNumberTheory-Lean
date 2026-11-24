import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Summing dyadic interval estimates

A positive power controls the geometric sum of the contributions from
all preceding intervals.
-/

open Real Filter MeasureTheory
open scoped Asymptotics Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- A power bound on the integrals of a continuous nonnegative function
over all dyadic intervals gives the same power bound from one. -/
theorem integral_from_one_of_dyadic {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (h : ∀ T : ℝ, 2 ≤ T → (∫ t in T..2*T, f t) ≤ C*T^q) :
    ∃ K > 0, ∀ T : ℝ, 1 ≤ T → (∫ t in (1:ℝ)..T, f t) ≤ K*T^q := by
  let b := (2:ℝ)^q
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hq
  let m := ∫ t in (1:ℝ)..2, f t
  have hm : 0 ≤ m := intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hf0 t)
  let A := 1+m+C/(b-1)
  have hA : 0<A := by dsimp [A]; positivity
  have hrec : A+C ≤ A*b := by
    have hdiv : C/(b-1) ≤ A := by dsimp [A]; linarith
    have := (div_le_iff₀ (by linarith : 0 < b-1)).mp hdiv
    linarith
  have hsum (n : ℕ) : (∫ t in (1:ℝ)..(2:ℝ)^(n+1), f t) ≤ A*((2:ℝ)^(n+1))^q := by
    induction n with
    | zero =>
      simp only [zero_add,pow_one]
      change m ≤ A*b
      have ha : m ≤ A := by
        dsimp [A]
        have : 0 ≤ C/(b-1) := by positivity
        linarith
      nlinarith only [ha,mul_nonneg hA.le (sub_nonneg.mpr hb.le)]
    | succ n ih =>
      let x := (2:ℝ)^(n+1)
      have hx : 2 ≤ x := by dsimp [x]; rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=n)]
      have hxx : (2:ℝ)^(n+1+1) = 2*x := by dsimp [x]; rw [pow_succ,mul_comm]
      rw [hxx,← intervalIntegral.integral_add_adjacent_intervals (a:=(1:ℝ)) (b:=x) (c:=2*x)
        (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)]
      calc _ ≤ A*x^q+C*x^q := add_le_add ih (h x hx)
           _ ≤ _ := by
             rw [← add_mul,Real.mul_rpow (by norm_num) (by linarith : 0 ≤ x)]
             exact (mul_le_mul_of_nonneg_right hrec (Real.rpow_nonneg (by linarith) _)).trans_eq (by dsimp [b]; ring)
  refine ⟨A*b,mul_pos hA (by linarith),?_⟩
  intro T hT
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near hT (by norm_num : (1:ℝ)<2)
  have hmono := intervalIntegral.integral_mono_interval (μ:=volume) (a:=(1:ℝ)) le_rfl hT hn'.le
    (Eventually.of_forall hf0) (hf.intervalIntegrable ..)
  have hpow : (2:ℝ)^(n+1) ≤ 2*T := by rw [pow_succ]; linarith
  apply (hmono.trans (hsum n)).trans
  apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hpow hq.le) hA.le).trans_eq
  rw [Real.mul_rpow (by norm_num) (by linarith)]
  dsimp [b]; ring

end AnalyticNumberTheory.AnalyticTools
