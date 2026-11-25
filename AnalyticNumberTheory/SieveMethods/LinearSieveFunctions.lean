import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The upper and lower functions of the linear sieve

The method of steps constructs the two functions simultaneously. On each
unit interval the weighted derivative of one function equals the other
function evaluated one unit earlier.
-/
noncomputable section
open Filter Set Real
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

private def seed (upper : Bool) : ℝ := if upper then 2*exp eulerMascheroniConstant else 0

private def stage : ℕ → Bool → ℝ → ℝ
  | 0,b,_ => seed b
  | n+1,b,u => seed b+∫ v in (2:ℝ)..max 2 u, stage n (!b) (v-1)/max 1 (v-1)

private theorem stage_continuous (n : ℕ) (b : Bool) : Continuous (stage n b) := by
  induction n generalizing b with
  | zero => exact continuous_const
  | succ n ih =>
    have hf : Continuous (fun v : ℝ => stage n (!b) (v-1)/max 1 (v-1)) :=
      ((ih _).comp (continuous_id.sub continuous_const)).div (continuous_const.max (continuous_id.sub continuous_const))
        (fun v => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left ..)))
    have hp : Continuous (fun x => ∫ v in (2:ℝ)..x,stage n (!b) (v-1)/max 1 (v-1)) :=
      continuous_iff_continuousAt.mpr fun x => (hf.integral_hasStrictDerivAt 2 x).hasDerivAt.continuousAt
    exact continuous_const.add (hp.comp (continuous_const.max continuous_id))

private theorem stage_stable (n : ℕ) (b : Bool) {u : ℝ} (hu : u≤n+2) :
    stage (n+1) b u=stage n b u := by
  induction n generalizing b u with
  | zero => simp only [Nat.cast_zero,zero_add] at hu; simp [stage,max_eq_left hu]
  | succ n ih =>
    simp only [stage]
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (le_max_left ..)] at hv
    have hv' : v-1≤(n:ℝ)+2 := by
      have := hv.2
      rw [le_max_iff] at this
      push_cast at hu
      rcases this with h | h <;> linarith [Nat.cast_nonneg (α:=ℝ) n]
    exact congrArg (fun z : ℝ => z/max 1 (v-1)) (ih (!b) hv')

private theorem stages_agree {n m : ℕ} (hnm : n≤m) (b : Bool) {u : ℝ} (hu : u≤n+2) :
    stage m b u=stage n b u := by
  induction m,hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have h : (n:ℝ)≤m := by exact_mod_cast hnm
    exact (stage_stable m b (by linarith)).trans ih

private def weighted (b : Bool) (u : ℝ) := stage ⌈u⌉₊ b u

private theorem weighted_eq_stage (n : ℕ) (b : Bool) {u : ℝ} (hu : u≤n+2) :
    weighted b u=stage n b u := by
  rcases le_total n ⌈u⌉₊ with h | h
  · exact stages_agree h b hu
  · exact (stages_agree h b (by linarith [Nat.le_ceil u])).symm

private theorem weighted_continuous (b : Bool) : Continuous (weighted b) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have he : weighted b =ᶠ[𝓝 u] stage ⌈u⌉₊ b := by
    filter_upwards [eventually_lt_nhds (show u<(⌈u⌉₊:ℝ)+2 by linarith [Nat.le_ceil u])] with v hv
    exact weighted_eq_stage _ b hv.le
  exact (stage_continuous _ b).continuousAt.congr_of_eventuallyEq he

private theorem weighted_initial (b : Bool) {u : ℝ} (hu : u≤2) : weighted b u=seed b := by
  exact weighted_eq_stage 0 b (by simpa using hu)

private theorem weighted_integral (b : Bool) {u : ℝ} (hu : 2≤u) :
    weighted b u=seed b+∫ v in (2:ℝ)..u,weighted (!b) (v-1)/(v-1) := by
  let n := ⌈u⌉₊
  have hle : u≤(n:ℝ) := Nat.le_ceil u
  rw [weighted_eq_stage (n+1) b (by push_cast; linarith),stage,max_eq_right hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hu] at hv
  dsimp only
  rw [max_eq_right (show 1≤v-1 by linarith [hv.1]),weighted_eq_stage n (!b) (by linarith [hv.2])]

/-- The linear sieve function, indexed by true for the upper bound and false
for the lower bound. Its analytic domain is u≥1. -/
def linearSieveFunction (upper : Bool) (u : ℝ) : ℝ := weighted upper u/u

/-- The upper function F of the one-dimensional sieve. -/
def linearSieveUpper (u : ℝ) : ℝ := linearSieveFunction true u

/-- The lower function f of the one-dimensional sieve. -/
def linearSieveLower (u : ℝ) : ℝ := linearSieveFunction false u

theorem continuousOn_linearSieveFunction (b : Bool) :
    ContinuousOn (linearSieveFunction b) (Ici 1) := by
  exact (weighted_continuous b).continuousOn.div continuous_id.continuousOn
    fun _ h => ne_of_gt (zero_lt_one.trans_le h)

theorem linearSieve_initial {u : ℝ} (hu : u∈Icc 1 2) :
    linearSieveUpper u=2*exp eulerMascheroniConstant/u ∧ linearSieveLower u=0 := by
  simp [linearSieveUpper,linearSieveLower,linearSieveFunction,weighted_initial _ hu.2,seed]

theorem linearSieve_integral (b : Bool) {u : ℝ} (hu : 2≤u) :
    u*linearSieveFunction b u=(if b then 2*exp eulerMascheroniConstant else 0)+
      ∫ v in (2:ℝ)..u,linearSieveFunction (!b) (v-1) := by
  change u*(weighted b u/u)=seed b+_
  rw [show u*(weighted b u/u)=weighted b u by field_simp [show u≠0 by linarith]]
  exact weighted_integral b hu



private theorem stage_nonneg (n : ℕ) (b : Bool) (u : ℝ) : 0≤stage n b u := by
  induction n generalizing b u with
  | zero => cases b <;> simp [stage,seed] <;> positivity
  | succ n ih =>
    apply add_nonneg
    · cases b <;> simp [seed] <;> positivity
    · exact intervalIntegral.integral_nonneg (le_max_left ..) (fun v _ =>
        div_nonneg (ih _ _) (zero_le_one.trans (le_max_left ..)))

theorem linearSieveFunction_nonneg (b : Bool) {u : ℝ} (hu : 0≤u) :
    0≤linearSieveFunction b u := div_nonneg (stage_nonneg _ _ _) hu

/-- The delay differential equation satisfied by the weighted functions. -/
theorem hasDerivAt_mul_linearSieveFunction (b : Bool) {u : ℝ} (hu : 2<u) :
    HasDerivAt (fun x => x*linearSieveFunction b x) (linearSieveFunction (!b) (u-1)) u := by
  let H (v : ℝ) := weighted (!b) (v-1)/max 1 (v-1)
  have hc : Continuous H := ((weighted_continuous _).comp (continuous_id.sub continuous_const)).div
    (continuous_const.max (continuous_id.sub continuous_const))
    (fun v => ne_of_gt (zero_lt_one.trans_le (le_max_left ..)))
  have he : (fun x => x*linearSieveFunction b x) =ᶠ[𝓝 u] fun x => seed b+∫ v in (2:ℝ)..x,H v := by
    filter_upwards [eventually_gt_nhds hu] with x hx
    rw [linearSieve_integral b hx.le]
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_le hx.le] at hv
    change weighted (!b) (v-1)/(v-1)=weighted (!b) (v-1)/max 1 (v-1)
    rw [max_eq_right (by linarith [hv.1] : 1≤v-1)]
  have hd := (hc.integral_hasStrictDerivAt 2 u).hasDerivAt.const_add (seed b)
  have : H u=linearSieveFunction (!b) (u-1) := by
    simp [H,linearSieveFunction,max_eq_right (show 1≤u-1 by linarith)]
  rw [←this]
  exact hd.congr_of_eventuallyEq he

/-- The initial values and the integrated delay equations uniquely determine
the functions on the entire half-line. -/
theorem linearSieveFunction_unique (G : Bool → ℝ → ℝ)
    (hi : ∀ b (u : ℝ), u∈Icc 1 2 →
       u*G b u=if b then 2*exp eulerMascheroniConstant else 0)
    (hr : ∀ b (u : ℝ), 2≤u → u*G b u=(if b then 2*exp eulerMascheroniConstant else 0)+
      ∫ v in (2:ℝ)..u, G (!b) (v-1)) :
    ∀ b (u : ℝ), 1≤u → G b u=linearSieveFunction b u := by
  have hbase (b : Bool) {u : ℝ} (h₁ : 1≤u) (h₂ : u≤2) : G b u=linearSieveFunction b u := by
    apply (mul_left_cancel₀ (by linarith : u≠0))
    rw [hi b u ⟨h₁,h₂⟩,linearSieveFunction,weighted_initial b h₂]
    change seed b=u*(seed b/u); field_simp [show u≠0 by linarith]
  have hs (n : ℕ) : ∀ b (u : ℝ), 1≤u → u≤n+2 → G b u=linearSieveFunction b u := by
    induction n with
    | zero => intro b u h₁ h₂; exact hbase b h₁ (by simpa using h₂)
    | succ n ih =>
      intro b u h₁ h₂
      by_cases hh : u≤2
      · exact hbase b h₁ hh
      have hu := (not_le.mp hh).le
      apply (mul_left_cancel₀ (by linarith : u≠0))
      rw [hr b u hu,linearSieve_integral b hu]
      congr 1
      apply intervalIntegral.integral_congr
      intro v hv; rw [uIcc_of_le hu] at hv
      apply ih (!b) (v-1) (by linarith [hv.1])
      push_cast at h₂; linarith [hv.2]
  intro b u h₁
  exact hs ⌈u⌉₊ b u h₁ (by linarith [Nat.le_ceil u])

/-- The upper linear sieve function on the first three units. -/
theorem linearSieveUpper_eq_of_le_three {u : ℝ} (hu : u∈Icc 1 3) :
    linearSieveUpper u=2*exp eulerMascheroniConstant/u := by
  by_cases h : u≤2
  · exact (linearSieve_initial ⟨hu.1,h⟩).1
  have h₂ := (not_le.mp h).le
  apply (eq_div_iff (by linarith [hu.1] : u≠0)).mpr
  rw [mul_comm]; change u*linearSieveFunction true u=_
  rw [linearSieve_integral true h₂]; simp only [Bool.not_true,Bool.true_eq,ite_true]
  have hz : (∫ v in (2:ℝ)..u,linearSieveFunction false (v-1))=0 := by
    rw [←intervalIntegral.integral_zero (a:=2) (b:=u) (μ:=MeasureTheory.volume) (E:=ℝ)]
    apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_le h₂] at hv
    exact (linearSieve_initial (show v-1∈Icc 1 2 from ⟨by linarith [hv.1],by linarith [hv.2,hu.2]⟩)).2
  rw [hz,add_zero]

/-- The first positive branch of the lower linear sieve function. -/
theorem linearSieveLower_eq_of_le_four {u : ℝ} (hu : u∈Icc 2 4) :
    linearSieveLower u=2*exp eulerMascheroniConstant*log (u-1)/u := by
  apply (eq_div_iff (by linarith [hu.1] : u≠0)).mpr
  rw [mul_comm]; change u*linearSieveFunction false u=_
  rw [linearSieve_integral false hu.1]; simp only [Bool.not_false,Bool.false_eq_true,ite_false,zero_add]
  calc _ = ∫ v in (2:ℝ)..u,(2*exp eulerMascheroniConstant)*(v-1)⁻¹ := by
             apply intervalIntegral.integral_congr
             intro v hv; rw [uIcc_of_le hu.1] at hv
             exact (linearSieveUpper_eq_of_le_three (show v-1∈Icc 1 3 from
               ⟨by linarith [hv.1],by linarith [hv.2,hu.2]⟩)).trans (div_eq_mul_inv ..)
       _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right (fun x : ℝ => x⁻¹) 1,
                      integral_inv_of_pos (by norm_num) (by linarith [hu.1])]; norm_num

end AnalyticNumberTheory.SieveMethods
