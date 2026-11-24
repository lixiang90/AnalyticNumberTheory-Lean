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

/-- A positive nondecreasing weight can be carried through dyadic summation. This
includes bounds of the form `T^q (1+log T)^k` with a fixed nonnegative integer `k`. -/
theorem integral_from_one_of_weighted_dyadic {f g : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (hg : Continuous g) (hg0 : ∀ t, 0 < g t)
    (hmono : MonotoneOn g (Set.Ici 1)) {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (h : ∀ T : ℝ, 2 ≤ T → (∫ t in T..2*T, f t) ≤ C*T^q*g T) :
    ∃ K > 0, ∀ T : ℝ, 1 ≤ T → (∫ t in (1:ℝ)..T, f t) ≤ K*T^q*g T := by
  let F (t : ℝ) := f t/g t
  have hF : Continuous F := hf.div hg (fun t => (hg0 t).ne')
  have hF0 (t : ℝ) : 0 ≤ F t := div_nonneg (hf0 t) (hg0 t).le
  have hh (T : ℝ) (hT : 2 ≤ T) : (∫ t in T..2*T, F t) ≤ C*T^q := by
    have hab : T ≤ 2*T := by linarith
    have hg' := (hf.div continuous_const (fun _ => (hg0 T).ne')).intervalIntegrable (μ := volume) T (2*T)
    have hp (t : ℝ) (ht : t ∈ Set.Icc T (2*T)) : F t ≤ f t/g T :=
      div_le_div_of_nonneg_left (hf0 t) (hg0 T) (hmono (by change 1 ≤ T; linarith)
        (by change 1 ≤ t; linarith [ht.1]) ht.1)
    have H := intervalIntegral.integral_mono_on hab (hF.intervalIntegrable ..) hg' hp
    change (∫ u in T..2*T, F u) ≤ ∫ u in T..2*T, f u/g T at H
    rw [intervalIntegral.integral_div] at H
    exact H.trans ((div_le_iff₀ (hg0 T)).mpr (h T hT))
  obtain ⟨K,hK,hk⟩ := integral_from_one_of_dyadic hF hF0 hq hC hh
  refine ⟨K,hK,?_⟩
  intro T hT
  have hp (t : ℝ) (ht : t ∈ Set.Icc 1 T) : f t ≤ F t*g T := by
    calc f t = F t*g t := (div_mul_cancel₀ (f t) (hg0 t).ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (hmono ht.1 hT ht.2) (hF0 t)
  have H := intervalIntegral.integral_mono_on (μ := volume) hT (hf.intervalIntegrable ..)
    ((hF.mul continuous_const).intervalIntegrable ..) hp
  change (∫ u in (1:ℝ)..T, f u) ≤ ∫ u in (1:ℝ)..T, F u*g T at H
  rw [intervalIntegral.integral_mul_const] at H
  exact H.trans (mul_le_mul_of_nonneg_right (hk T hT) (hg0 T).le)

end AnalyticNumberTheory.AnalyticTools
