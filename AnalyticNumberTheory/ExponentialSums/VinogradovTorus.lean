import AnalyticNumberTheory.ExponentialSums.VinogradovShiftedCounts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integration and orthogonality on Vinogradov's torus

The iterated integral preserves inequalities between continuous functions.
Orthogonality expresses the number of matching frequency vectors in two
arbitrary finite families as an integral of their character sums.
-/

open Finset Real Complex MeasureTheory
namespace AnalyticNumberTheory.ExponentialSums

private theorem continuous_finCons {X : Type*} [TopologicalSpace X] {k : ℕ}
    {f : X → ℝ} {g : X → Fin k → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (Fin.cons (f x) (g x) : Fin (k+1) → ℝ)) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using hf
  · simpa only [Fin.cons_succ,Function.comp_def] using (continuous_apply i).comp hg

/-- The torus integral depends continuously on parameters in a continuous family. -/
theorem continuous_torusIntegral_parameter (k : ℕ) {X : Type*} [TopologicalSpace X]
    (f : X → (Fin k → ℝ) → ℝ) (hf : Continuous f.uncurry) :
    Continuous (fun x => torusIntegral k (f x)) := by
  induction k generalizing X with
  | zero => exact hf.comp (continuous_id.prodMk continuous_const)
  | succ k ih =>
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    apply ih (X:=X×ℝ) (fun p α => f p.1 (Fin.cons p.2 α))
    exact hf.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_finCons (continuous_snd.comp continuous_fst) continuous_snd))

private theorem continuous_torus_slices {k : ℕ} {f : (Fin (k+1) → ℝ) → ℝ} (hf : Continuous f) :
    Continuous (fun t : ℝ => torusIntegral k (fun α => f (Fin.cons t α))) :=
  continuous_torusIntegral_parameter k _ (hf.comp (continuous_finCons continuous_fst continuous_snd))

/-- Monotonicity of the torus integral on continuous real functions. -/
theorem torusIntegral_mono (k : ℕ) {f g : (Fin k → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ α, f α ≤ g α) : torusIntegral k f ≤ torusIntegral k g := by
  induction k with
  | zero => exact h _
  | succ k ih =>
    apply intervalIntegral.integral_mono_on zero_le_one ((continuous_torus_slices hf).intervalIntegrable ..)
      ((continuous_torus_slices hg).intervalIntegrable ..)
    intro t _
    exact ih (hf.comp (continuous_finCons continuous_const continuous_id)) (hg.comp
      (continuous_finCons continuous_const continuous_id)) (fun α => h _)

/-- A constant multiplier commutes with torus integration. -/
theorem torusIntegral_const_mul (k : ℕ) (a : ℝ) (f : (Fin k → ℝ) → ℝ) :
    torusIntegral k (fun α => a*f α) = a*torusIntegral k f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [torusIntegral,ih,intervalIntegral.integral_const_mul]

/-- Finite sums of continuous functions commute with torus integration. -/
theorem torusIntegral_finsetSum (k : ℕ) {ι : Type*} (S : Finset ι) (f : ι → (Fin k → ℝ) → ℝ)
    (hf : ∀ i ∈ S, Continuous (f i)) :
    torusIntegral k (fun α => ∑ i ∈ S, f i α) = ∑ i ∈ S, torusIntegral k (f i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [torusIntegral]
    have hs (t : ℝ) := ih (fun i α => f i (Fin.cons t α)) (fun i hi =>
      (hf i hi).comp (continuous_finCons continuous_const continuous_id))
    simp_rw [hs]
    exact intervalIntegral.integral_finsetSum fun i hi => (continuous_torus_slices (hf i hi)).intervalIntegrable ..

/-- Exponential sum of a finite family of integral frequency vectors. -/
noncomputable def torusCharSum {k : ℕ} {ι : Type*} (P : Finset ι) (f : ι → Fin k → ℤ)
    (α : Fin k → ℝ) : ℂ := ∑ x ∈ P, torusChar k (f x) α

theorem continuous_torusCharSum {k : ℕ} {ι : Type*} (P : Finset ι) (f : ι → Fin k → ℤ) :
    Continuous (torusCharSum P f) := continuous_finsetSum P fun i _ => continuous_torusChar (f i)

/-- Orthogonality counts pairs with equal moment vectors, including families with repeated frequencies. -/
theorem matching_card_eq_torusIntegral {k : ℕ} {ι κ : Type*} (P : Finset ι) (Q : Finset κ)
    (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) :
    (((P ×ˢ Q).filter (fun z => f z.1=g z.2)).card : ℝ) =
      torusIntegral k (fun α => (torusCharSum P f α * star (torusCharSum Q g α)).re) := by
  classical
  let m (z : ι×κ) := f z.1-g z.2
  have he (α) : torusCharSum P f α * star (torusCharSum Q g α) =
      ∑ z ∈ P ×ˢ Q, (1:ℂ)*torusChar k (m z) α := by
    simp only [torusCharSum,star_sum,Finset.sum_mul_sum,Finset.sum_product,one_mul,m,sub_eq_add_neg,
      torusChar_add,torusChar_neg]
  simp_rw [he]
  rw [torusIntegral_re_char_sum,torusIntegralC_char_sum_eq]
  simp only [one_mul,Complex.re_sum,card_filter,Nat.cast_sum]
  apply sum_congr rfl
  intro z _
  have hiff : (∀ j, m z j=0) ↔ f z.1=g z.2 := by
    simp only [m,Pi.sub_apply,sub_eq_zero,funext_iff]
  by_cases h : f z.1=g z.2 <;> simp [h,hiff]

end AnalyticNumberTheory.ExponentialSums
