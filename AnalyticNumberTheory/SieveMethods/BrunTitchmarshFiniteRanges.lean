import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Numerical intervals for the finite Brun–Titchmarsh sieve

On u ≥ B/d the expression (d u + B) log u − 2u is convex. Thus a
wheel bound on a long closed interval only requires endpoint estimates.
The remaining small intervals use monotonicity of the logarithm.
-/
open Real Set
namespace AnalyticNumberTheory.SieveMethods

private theorem bt_convex_range {a b u d B : ℝ} (ha : 0<a) (hB : B≤d*a)
    (hd : 0≤d) (hu : u∈Icc a b)
    (h₁ : (d*a+B)*log a≤2*a) (h₂ : (d*b+B)*log b≤2*b) :
    (d*u+B)*log u≤2*u := by
  let F := fun x => (d*x+B)*log x-2*x
  let G := fun x => d*log x+d+B/x-2
  have dF (x : ℝ) (hx : 0<x) : HasDerivAt F (G x) x := by
    have H := ((((hasDerivAt_id' x).const_mul d).add_const B).mul (Real.hasDerivAt_log hx.ne')).sub
      ((hasDerivAt_id' x).const_mul 2)
    convert H using 1
    dsimp [G]; field_simp [hx.ne']; ring
  have dG (x : ℝ) (hx : 0<x) : HasDerivAt G ((d*x-B)/x^2) x := by
    have H := ((((Real.hasDerivAt_log hx.ne').const_mul d).add_const d).add
      ((hasDerivAt_const x B).div (hasDerivAt_id' x) hx.ne')).sub_const 2
    convert H using 1
    field_simp [hx.ne'] <;> ring
  have hF : ConvexOn ℝ (Icc a b) F := convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc ..)
    (fun x hx => (dF x (ha.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => (dF x (ha.trans_le (interior_subset hx).1)).hasDerivWithinAt)
    (fun x hx => (dG x (ha.trans_le (interior_subset hx).1)).hasDerivWithinAt)
    (fun x hx => div_nonneg (sub_nonneg.mpr (hB.trans (mul_le_mul_of_nonneg_left
      (interior_subset hx).1 hd))) (sq_nonneg _))
  have h := (hF.le_max_of_mem_Icc (left_mem_Icc.mpr (hu.1.trans hu.2))
    (right_mem_Icc.mpr (hu.1.trans hu.2)) hu).trans
    (max_le (sub_nonpos.mpr h₁) (sub_nonpos.mpr h₂))
  exact sub_nonpos.mp h

private theorem bt_log_taylor {x h : ℝ} (hx : 0<x) (hh : 0≤h) (n : ℕ)
    (H : x ≤ ∑ i∈Finset.range n,h^i/(i.factorial:ℝ)) : log x≤h :=
  (Real.log_le_iff_le_exp hx).2 (H.trans (Real.sum_le_exp_of_nonneg hh n))

private theorem bt_small_range {a b u d B h : ℝ} (ha : 0<a) (hd : 0≤d) (hB : 0≤B)
    (hu : u∈Icc a b) (hl : log b≤h) (hh : 0≤h) (hcoef : h*(d+B/a)≤2) :
    (d*u+B)*log u≤2*u := by
  have hp := ha.trans_le hu.1
  have hlog := (Real.log_le_log hp hu.2).trans hl
  have H := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hB ha hu.1) hh
  have H' : h*(d+B/u)≤2 := by linarith
  have J := mul_le_mul_of_nonneg_right H' hp.le
  have E := mul_le_mul_of_nonneg_left hlog (add_nonneg (mul_nonneg hd hp.le) hB)
  apply E.trans
  convert J using 1
  field_simp [hp.ne'] <;> ring

/-- At least one wheel, with cutoff 1, 2, 3, 7, or 13, gives the required
majorant over the entire interval 1 < u ≤ 20000. -/
theorem bt_finite_wheel_ranges {u : ℝ} (hu : 1<u) (hU : u≤20000) :
    ((1*u+1)*log u≤2*u) ∨ ((1/2*u+3)*log u≤2*u) ∨
    ((1/3*u+6)*log u≤2*u) ∨ ((8/35*u+20)*log u≤2*u) ∨
    ((192/1001*u+70)*log u≤2*u) := by
  have h1 : log (5/2)≤1 := bt_log_taylor (by norm_num) (by norm_num) 5 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h2 : log 4≤7/5 := bt_log_taylor (by norm_num) (by norm_num) 7 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h3 : log (24/5)≤8/5 := bt_log_taylor (by norm_num) (by norm_num) 7 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h4 : log (29/5)≤44/25 := bt_log_taylor (by norm_num) (by norm_num) 9 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h5 : log 6≤9/5 := bt_log_taylor (by norm_num) (by norm_num) 9 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h6 : log 20≤3 := bt_log_taylor (by norm_num) (by norm_num) 12 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h7 : log 200≤11/2 := bt_log_taylor (by norm_num) (by norm_num) 13 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h8 : log 2000≤8 := bt_log_taylor (by norm_num) (by norm_num) 15 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  have h9 : log 20000≤10 := bt_log_taylor (by norm_num) (by norm_num) 18 (by norm_num [Finset.sum_range_succ,Nat.factorial])
  by_cases H₁ : u≤5/2
  · exact .inl (bt_small_range (a:=1) (by norm_num) (by norm_num) (by norm_num) ⟨hu.le,H₁⟩ h1 (by norm_num) (by norm_num))
  by_cases H₂ : u≤4
  · exact .inl (bt_small_range (a:=5/2) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,H₂⟩ h2 (by norm_num) (by norm_num))
  by_cases H₃ : u≤24/5
  · exact .inl (bt_small_range (a:=4) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,H₃⟩ h3 (by norm_num) (by norm_num))
  right
  by_cases H₄ : u≤29/5
  · exact .inl (bt_small_range (a:=24/5) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,H₄⟩ h4 (by norm_num) (by norm_num))
  by_cases H₅ : u≤6
  · exact .inl (bt_small_range (a:=29/5) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,H₅⟩ h5 (by norm_num) (by norm_num))
  by_cases H₆ : u≤20
  · exact .inl (bt_convex_range (a:=6) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,H₆⟩ (by linarith only [h5]) (by linarith only [h6]))
  right
  by_cases H₇ : u≤200
  · exact .inl (bt_convex_range (a:=20) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,H₇⟩ (by linarith only [h6]) (by linarith only [h7]))
  right
  by_cases H₈ : u≤2000
  · exact .inl (bt_convex_range (a:=200) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,H₈⟩ (by linarith only [h7]) (by linarith only [h8]))
  exact .inr (bt_convex_range (a:=2000) (by norm_num) (by norm_num) (by norm_num) ⟨by linarith,hU⟩ (by linarith only [h8]) (by linarith only [h9]))

end AnalyticNumberTheory.SieveMethods
