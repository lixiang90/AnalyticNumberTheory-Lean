import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Exponential moments of finite zero-counting measures

A uniform exponential bound on the cumulative count controls weighted
power sums. A common lower bound on the zero gap can be retained as an
additional exponential factor without changing the counting constant.
-/

noncomputable section
open Finset
namespace AnalyticNumberTheory.PrimeDistribution

/-- Exponential summation of a finite weighted counting function. Here the
cumulative estimate involves x≤t, and r is a lower bound on every x.
The constant is independent of the size of S. -/
theorem finite_density_exponential_moment {ι : Type*} (S : Finset ι) (w x : ι → ℝ)
    {A C b r : ℝ} (hA : 0≤A) (hC : 0≤C) (hb : 0≤b)
    (hw : ∀ i∈S, 0≤w i) (hx : ∀ i∈S, 0≤x i) (hr : ∀ i∈S,r≤x i)
    (hcnt : ∀ t : ℝ, 0≤t → (∑ i ∈ S with x i≤t,w i) ≤ C*Real.exp (A*t)) :
    ∑ i ∈ S,w i*Real.exp (-(A+1+b)*x i) ≤
      (C*Real.exp A/(1-Real.exp (-1)))*Real.exp (-b*r) := by
  classical
  let f := fun i => ⌊x i⌋₊
  let U := S.image f
  let G := fun i => w i*Real.exp (-(A+1)*x i)
  have hsep (i : ι) (hi : i∈S) : w i*Real.exp (-(A+1+b)*x i) ≤ G i*Real.exp (-b*r) := by
    rw [show -(A+1+b)*x i=(-(A+1)*x i)+(-b*x i) by ring,Real.exp_add,←mul_assoc]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg (hw _ hi) (Real.exp_pos _).le)
    exact mul_le_mul_of_nonpos_left (hr _ hi) (neg_nonpos.mpr hb)
  have hblock (n : ℕ) : (∑ i ∈ S with f i=n,G i) ≤ C*Real.exp A*(Real.exp (-1))^n := by
    let V := S.filter (fun i => f i=n)
    have hmem {i} (hi : i∈V) : i∈S ∧ (n:ℝ)≤x i ∧ x i < (n:ℝ)+1 := by
      obtain ⟨hi,he⟩ := mem_filter.mp hi
      rw [←he]; exact ⟨hi,Nat.floor_le (hx _ hi),Nat.lt_floor_add_one _⟩
    have hsub : V⊆S.filter (fun i => x i≤(n:ℝ)+1) := fun i hi => mem_filter.mpr ⟨(hmem hi).1,(hmem hi).2.2.le⟩
    have hw' := (sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hw _ (mem_filter.mp hi).1)).trans
      (hcnt (n+1) (by positivity))
    calc
      _ ≤ ∑ i ∈ V,w i*Real.exp (-(A+1)*n) := by
        apply sum_le_sum; intro i hi
        dsimp only [G]
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hw _ (hmem hi).1)
        exact mul_le_mul_of_nonpos_left (hmem hi).2.1 (by linarith)
      _ ≤ (C*Real.exp (A*(n+1)))*Real.exp (-(A+1)*n) := by
        rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hw' (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,←Real.exp_add,←Real.exp_nat_mul,mul_assoc,←Real.exp_add]; congr 2; ring
  have hgeom := (summable_geometric_of_lt_one (Real.exp_pos (-1)).le
    (Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ)<0))).sum_le_tsum U (fun i _ => by positivity)
  rw [tsum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ)<0))] at hgeom
  have hbase : (∑ i ∈ S,G i) ≤ C*Real.exp A/(1-Real.exp (-1)) := by
    rw [←sum_fiberwise_of_maps_to (s:=S) (t:=U) (g:=f) (fun i hi => mem_image_of_mem f hi) G]
    refine (sum_le_sum (fun n _ => hblock n)).trans ?_
    rw [←mul_sum,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  calc
    _ ≤ ∑ i ∈ S,G i*Real.exp (-b*r) := sum_le_sum hsep
    _ ≤ _ := by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le

end AnalyticNumberTheory.PrimeDistribution
