import AnalyticNumberTheory.SieveMethods.LinearSieveFunctions
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The Dickman function and the width of the linear sieve

The weighted difference of the upper and lower linear sieve functions,
shifted by one unit, is the Dickman function. Its moving-average identity
proves positivity and yields a factorial bound.
-/
noncomputable section
open Filter Set MeasureTheory Real
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

private def c : ℝ := 2*exp eulerMascheroniConstant
private theorem c_pos : 0<c := by unfold c; positivity

/-- The Dickman function on the half-line, extended constantly to negative
arguments. It is one on [0,1] and satisfies xρ'(x)=−ρ(x−1) for x>1. -/
def dickman (x : ℝ) : ℝ :=
  let u := max 0 x+1
  (u*linearSieveUpper u-u*linearSieveLower u)/c

theorem continuous_dickman : Continuous dickman := by
  let h := fun x : ℝ => max 0 x+1
  have hh : Continuous h := by dsimp [h]; fun_prop
  have hm : ∀x,h x∈Ici 1 := fun x => by change 1≤max 0 x+1; linarith [le_max_left 0 x]
  have H (b : Bool) : Continuous (fun x => linearSieveFunction b (h x)) :=
    (continuousOn_linearSieveFunction b).comp_continuous hh hm
  exact ((hh.mul (H true)).sub (hh.mul (H false))).div_const c

theorem dickman_eq_one {x : ℝ} (hx : x≤1) : dickman x=1 := by
  let u := max 0 x+1
  have h₁ : 1≤u := by dsimp [u]; linarith [le_max_left 0 x]
  have h₂ : u≤2 := by dsimp [u]; linarith [max_le (by norm_num : (0:ℝ)≤1) hx]
  obtain ⟨hF,hf⟩ := linearSieve_initial ⟨h₁,h₂⟩
  change (u*linearSieveUpper u-u*linearSieveLower u)/c=1
  rw [hF,hf]; unfold c; field_simp [show u≠0 by linarith] <;> ring

/-- Exact relation between the Dickman function and the sieve functions. -/
theorem linearSieve_gap_eq_dickman {u : ℝ} (hu : 1≤u) :
    linearSieveUpper u-linearSieveLower u=2*exp eulerMascheroniConstant*dickman (u-1)/u := by
  rw [dickman,max_eq_right (by linarith : 0≤u-1),sub_add_cancel]
  dsimp only [c]
  field_simp [show u≠0 by linarith] <;> ring

/-- The Dickman delay differential equation. -/
theorem hasDerivAt_dickman {x : ℝ} (hx : 1<x) : HasDerivAt dickman (-dickman (x-1)/x) x := by
  let f := fun y : ℝ => ((y+1)*linearSieveUpper (y+1)-(y+1)*linearSieveLower (y+1))/c
  have he : dickman =ᶠ[𝓝 x] f := by
    filter_upwards [eventually_gt_nhds (by linarith : 0<x)] with y hy
    simp [dickman,f,max_eq_right hy.le]
  have H (b : Bool) := (hasDerivAt_mul_linearSieveFunction b (by linarith : 2<x+1)).comp x ((hasDerivAt_id x).add_const 1)
  have hd := ((H true).sub (H false)).div_const c
  have hh := linearSieve_gap_eq_dickman hx.le
  have hneg : (linearSieveLower x-linearSieveUpper x)/c= -dickman (x-1)/x := by
    change linearSieveUpper x-linearSieveLower x=c*dickman (x-1)/x at hh
    field_simp [c_pos.ne',show x≠0 by linarith] at hh ⊢; linarith
  rw [←hneg]
  apply HasDerivAt.congr_of_eventuallyEq (f:=f) _ he
  simpa only [f,linearSieveUpper,linearSieveLower,Bool.not_true,Bool.not_false,add_sub_cancel_right,
    mul_one,Function.comp_def,id_eq,Pi.sub_apply] using! hd

/-- The integral of ρ over its last unit interval is xρ(x). -/
theorem integral_dickman_last_unit {x : ℝ} (hx : 1≤x) :
    (∫ t in x-1..x,dickman t)=x*dickman x := by
  let f := fun t : ℝ => t*dickman t
  have hcont : Continuous f := continuous_id.mul continuous_dickman
  have hsub : Continuous (fun t : ℝ => dickman t-dickman (t-1)) :=
    continuous_dickman.sub (continuous_dickman.comp (continuous_id.sub continuous_const))
  have hd (t : ℝ) (ht : t∈Ioo 1 x) : HasDerivAt f (dickman t-dickman (t-1)) t := by
    have hd := (hasDerivAt_id t).mul (hasDerivAt_dickman ht.1)
    have he : 1*dickman t+id t*(-dickman (t-1)/t)=dickman t-dickman (t-1) := by
      dsimp only [id_eq]; field_simp [show t≠0 by linarith [ht.1]] <;> ring
    rw [he] at hd
    exact hd
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hcont.continuousOn hd
    (hsub.intervalIntegrable 1 x)
  have hs : Continuous (fun t : ℝ => dickman (t-1)) := continuous_dickman.comp (continuous_id.sub continuous_const)
  rw [intervalIntegral.integral_sub (continuous_dickman.intervalIntegrable ..) (hs.intervalIntegrable ..),
    intervalIntegral.integral_comp_sub_right dickman 1] at hh
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (continuous_dickman.intervalIntegrable 0 (x-1)) (continuous_dickman.intervalIntegrable (x-1) x)
  have hsum' := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (continuous_dickman.intervalIntegrable 0 1) (continuous_dickman.intervalIntegrable 1 x)
  have hseed : (∫ t in (0:ℝ)..1,dickman t)=1 := by
    calc _ = ∫ _ in (0:ℝ)..1,(1:ℝ) := intervalIntegral.integral_congr (fun t ht => dickman_eq_one (by simpa using ht.2))
         _ = _ := by simp
  simp only [sub_self,f,dickman_eq_one le_rfl,one_mul] at hh
  linarith only [hh,hsum,hsum',hseed]

/-- The Dickman function is nonnegative on the whole half-line. -/
theorem dickman_nonneg (x : ℝ) : 0≤dickman x := by
  by_cases hx : x≤1
  · rw [dickman_eq_one hx]; norm_num
  have h1 := (not_le.mp hx).le
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (show 0≤x by linarith)) continuous_dickman.continuousOn
  have hmx := hmin (show x∈Icc (0:ℝ) x from ⟨by linarith,le_rfl⟩)
  by_contra! hn
  have hmneg := hmx.trans_lt hn
  have hm1 : 1<m := by by_contra! h; rw [dickman_eq_one h] at hmneg; linarith
  have hc := intervalIntegral.integral_mono_on (show m-1≤m by linarith) (intervalIntegrable_const (μ:=volume) (c:=dickman m))
    (continuous_dickman.intervalIntegrable (m-1) m) (fun t ht => hmin (show t∈Icc (0:ℝ) x from ⟨by linarith [ht.1],ht.2.trans hm.2⟩))
  rw [integral_dickman_last_unit hm1.le,intervalIntegral.integral_const] at hc
  simp only [sub_sub_cancel,one_smul] at hc
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hm1) hmneg]


/-- The Dickman function is strictly positive even though its decay is
faster than every geometric progression. -/
theorem dickman_pos (x : ℝ) : 0<dickman x := by
  have hs (n : ℕ) : ∀ x : ℝ, x≤n+1 → 0<dickman x := by
    induction n with
    | zero => intro x hx; rw [dickman_eq_one (by simpa using hx)]; exact zero_lt_one
    | succ n ih =>
      intro x hx; push_cast at hx
      by_cases h : x≤1
      · rw [dickman_eq_one h]; exact zero_lt_one
      have h1 := not_le.mp h
      have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (a:=x-1) (b:=x) (f:=fun _ => 0) (g:=dickman) (by linarith) continuousOn_const
        continuous_dickman.continuousOn (fun t _ => dickman_nonneg t)
        ⟨x-1,⟨le_rfl,by linarith⟩,ih (x-1) (by linarith)⟩
      rw [intervalIntegral.integral_zero,integral_dickman_last_unit h1.le] at hpos
      exact (mul_pos_iff_of_pos_left (by linarith : 0<x)).mp hpos
  exact hs ⌈x⌉₊ x (by linarith [Nat.le_ceil x])

theorem antitone_dickman : Antitone dickman := by
  have ha : AntitoneOn dickman (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) continuous_dickman.continuousOn
    · rw [interior_Ici]; exact fun x hx => (hasDerivAt_dickman hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro x hx; rw [(hasDerivAt_dickman hx).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (dickman_nonneg _)) (zero_le_one.trans hx.le)
  intro x y hxy
  by_cases hx : 1≤x
  · exact ha hx (hx.trans hxy) hxy
  by_cases hy : 1≤y
  · rw [dickman_eq_one (not_le.mp hx).le,←dickman_eq_one (x:=1) le_rfl]
    exact ha (Set.mem_Ici.mpr le_rfl) hy hy
  rw [dickman_eq_one (not_le.mp hy).le,dickman_eq_one (not_le.mp hx).le]

/-- For x≥n the Dickman function is bounded by 1/n!. -/
theorem dickman_le_inv_factorial (n : ℕ) {x : ℝ} (hx : n≤x) :
    dickman x≤(n.factorial:ℝ)⁻¹ := by
  have hs : ∀n : ℕ, dickman n≤(n.factorial:ℝ)⁻¹ := by
    intro m; induction m with
    | zero => norm_num [dickman_eq_one]
    | succ m ih =>
      have hm : (1:ℝ)≤m+1 := by linarith [Nat.cast_nonneg (α:=ℝ) m]
      have hh := intervalIntegral.integral_mono_on (show (m:ℝ)≤m+1 by linarith)
        (continuous_dickman.intervalIntegrable _ _) (intervalIntegrable_const (μ:=volume) (c:=dickman m))
        (fun t ht => antitone_dickman ht.1)
      rw [show (∫t in (m:ℝ)..m+1,dickman t)=(m+1)*dickman (m+1) by
        simpa only [add_sub_cancel_right] using integral_dickman_last_unit hm,intervalIntegral.integral_const] at hh
      simp only [add_sub_cancel_left,one_smul] at hh
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one,mul_inv_rev,←div_eq_mul_inv,le_div_iff₀ (by positivity : (0:ℝ)<m+1)]
      exact (mul_comm ..).le.trans (hh.trans ih)
  exact (antitone_dickman hx).trans (hs n)

/-- Strict order and quantitative width of the linear sieve for u≥n+1. -/
theorem linearSieve_gap_le_factorial (n : ℕ) {u : ℝ} (hu : n+1≤u) :
    0<linearSieveUpper u-linearSieveLower u ∧
    linearSieveUpper u-linearSieveLower u ≤
      2*exp eulerMascheroniConstant / ((n.factorial:ℝ)*u) := by
  have h1 : 1≤u := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  rw [linearSieve_gap_eq_dickman h1]
  constructor
  · exact div_pos (mul_pos c_pos (dickman_pos _)) (by linarith)
  · rw [div_mul_eq_div_div,div_le_div_iff_of_pos_right (by linarith : 0<u),div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (dickman_le_inv_factorial n (by linarith)) c_pos.le

end AnalyticNumberTheory.SieveMethods
