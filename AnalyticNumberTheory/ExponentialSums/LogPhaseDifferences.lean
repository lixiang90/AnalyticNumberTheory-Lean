import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.ExponentialSums.LogarithmicPhases
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Higher differences of logarithmic phases

The mean-value formula for a finite difference with unequal positive steps
evaluates a higher derivative at a point between the first and last nodes.
It gives uniform two-sided estimates for differenced logarithmic phases.
-/

open Real Finset Set

namespace AnalyticNumberTheory.ExponentialSums

/-- Positive forward translations commute with differentiation on the positive half-line. -/
theorem iterForwardDiff_hasDerivAt {k : ℕ} (h : Fin k → ℝ) (hh : ∀ i, 0 ≤ h i)
    {f g : ℝ → ℝ} (hf : ∀ x, 0 < x → HasDerivAt f (g x) x) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iterForwardDiff h f) (iterForwardDiff h g x) x := by
  induction k generalizing x with
  | zero => exact hf x hx
  | succ k ih =>
    let t (i : Fin k) := h i.succ
    have ht (i : Fin k) : 0 ≤ t i := hh i.succ
    have hd := (ih t ht (x := x+h 0) (by linarith [hh 0])).comp x
      ((hasDerivAt_id x).add_const (h 0))
    change HasDerivAt (fun u => iterForwardDiff t f (u+h 0)-iterForwardDiff t f u)
      (iterForwardDiff t g (x+h 0)-iterForwardDiff t g x) x
    simpa only [Function.comp_def,id_eq,mul_one,Pi.sub_def] using
      hd.sub (ih t ht hx)

/-- A mixed forward difference equals the product of its steps times a derivative
somewhere in the interval covered by all of the steps. -/
theorem iterForwardDiff_mean_value {k : ℕ} (h : Fin k → ℝ) (hh : ∀ i, 0 < h i)
    (f : ℕ → ℝ → ℝ) (hf : ∀ j x, 0 < x → HasDerivAt (f j) (f (j+1) x) x)
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ∃ y ∈ Icc x (x+∑ i, h i),
      iterForwardDiff h (f j) x = (∏ i, h i) * f (j+k) y := by
  induction k generalizing j x with
  | zero => exact ⟨x,by simp,by simp [iterForwardDiff]⟩
  | succ k ih =>
    let t (i : Fin k) := h i.succ
    have ht (i : Fin k) : 0 < t i := hh i.succ
    let F := iterForwardDiff t (f j)
    let G := iterForwardDiff t (f (j+1))
    have hd (u : ℝ) (hu : 0<u) : HasDerivAt F (G u) u :=
      iterForwardDiff_hasDerivAt t (fun i => (ht i).le) (hf j) hu
    obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope F G (show x<x+h 0 by linarith [hh 0])
      (fun u hu => (hd u (hx.trans_le hu.1)).continuousAt.continuousWithinAt)
      (fun u hu => hd u (hx.trans hu.1))
    obtain ⟨y,hy,he'⟩ := ih t ht (j+1) (hx.trans hu.1)
    refine ⟨y, ⟨hu.1.le.trans hy.1, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_succ]
      change y ≤ x+(h 0+∑ i, t i)
      linarith [hy.2,hu.2]
    · have he₁ : F (x+h 0)-F x = G u*h 0 := by
        rw [show x+h 0-x=h 0 by ring,eq_div_iff (hh 0).ne'] at he
        exact he.symm
      rw [Fin.prod_univ_succ]
      change F (x+h 0)-F x = h 0*(∏ i,t i)*f (j+(k+1)) y
      rw [he₁,show G u = _ from he',show j+1+k=j+(k+1) by omega]
      ring

/-- The derivative of order `k+2` of the shifted logarithmic phase. -/
noncomputable def logSecondDerivative (τ a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (-1:ℝ)^(k+1)*τ*((k+1).factorial:ℝ)/(x+a)^(k+2)

/-- Successive derivatives of a shifted logarithm on its positive ray. -/
theorem logSecondDerivative_hasDerivAt {τ a x : ℝ} (hx : 0<x+a) (k : ℕ) :
    HasDerivAt (logSecondDerivative τ a k) (logSecondDerivative τ a (k+1) x) x := by
  let c := (-1:ℝ)^(k+1)*τ*((k+1).factorial:ℝ)
  have hd := (hasDerivAt_const x c).div (((hasDerivAt_id x).add_const a).pow (k+2))
    (pow_ne_zero _ hx.ne')
  change HasDerivAt (fun u => c/(u+a)^(k+2)) _ x
  convert hd using 1
  · rfl
  · simp only [logSecondDerivative,c,Nat.factorial_succ (k+1),Nat.cast_mul,
      pow_succ (-1:ℝ) (k+1),id_eq,Pi.pow_apply,zero_mul,zero_sub,mul_one,show k+2-1=k+1 by omega]
    simp only [pow_succ (x+a), Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- Exact size of any positive-step forward difference of the curvature of a
logarithmic phase, at an intermediate point. -/
theorem iterForwardDiff_log_curvature {k : ℕ} (h : Fin k → ℝ) (hh : ∀ i, 0<h i)
    {τ a x : ℝ} (ha : 0≤a) (hx : 0<x) :
    ∃ y ∈ Icc x (x+∑ i,h i),
      |iterForwardDiff h (fun u => -τ/(u+a)^2) x| =
        (∏ i,h i) * |τ| * ((k+1).factorial:ℝ)/(y+a)^(k+2) := by
  obtain ⟨y,hy,he⟩ := iterForwardDiff_mean_value h hh (logSecondDerivative τ a)
    (fun j x hx => logSecondDerivative_hasDerivAt (by linarith) j) 0 hx
  have h0 : logSecondDerivative τ a 0 = fun u => -τ/(u+a)^2 := by
    funext u
    simp [logSecondDerivative]
  rw [h0,Nat.zero_add] at he
  refine ⟨y,hy,?_⟩
  rw [he,logSecondDerivative,abs_mul,abs_div,abs_mul,abs_mul,abs_pow,
    abs_of_nonneg (Finset.prod_nonneg fun i _ => (hh i).le),abs_neg,abs_one,one_pow,
    abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (k+1).factorial),abs_of_pos (pow_pos (show 0<y+a by linarith [hy.1]) _)]
  ring

/-- A second derivative estimate after any fixed number of positive differences.
The endpoints of the incomplete block and the offset in the logarithm may vary. -/
theorem iterForwardDiff_logPhase_bound {M b k : ℕ} (hM : 1≤M) (hb : M<b) (hb' : b≤2*M)
    (h : Fin k → ℝ) (hh : ∀ i, 0<h i) (hhM : ∀ i, h i≤M)
    {a τ : ℝ} (ha : a∈Set.Icc (0:ℝ) 1) (hτ : 0 < |τ|) :
    let K := (k:ℝ)+3
    let lam₀ := (∏ i,h i) * |τ| * ((k+1).factorial:ℝ)/(K*M)^(k+2)
    ‖∑ n ∈ Finset.Ioc M b,e (iterForwardDiff h (logPhase τ a) n)‖ ≤
      (20*K^(k+2)+20)*(((b:ℝ)-M)*√lam₀+(√lam₀)⁻¹) := by
  let K := (k:ℝ)+3
  let P := (∏ i,h i) * |τ| * ((k+1).factorial:ℝ)
  let lam := P/(K*M)^(k+2)
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hm0 : 0<(M:ℝ) := by linarith
  have hK : 1≤K := by dsimp [K]; linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hK0 : 0<K := by linarith
  have hprod : 0<∏ i,h i := Finset.prod_pos fun i _ => hh i
  have hP : 0<P := by dsimp [P]; positivity
  have hL : 0<lam := by dsimp [lam]; positivity
  let g := fun x : ℝ => τ/(x+a)
  let u := fun x : ℝ => -τ/(x+a)^2
  have du (x : ℝ) (hx : 0<x) : HasDerivAt u (logSecondDerivative τ a 1 x) x := by
    have hu : u = logSecondDerivative τ a 0 := by
      funext v
      simp [u,logSecondDerivative]
    rw [hu]
    exact logSecondDerivative_hasDerivAt (by linarith [ha.1]) 0
  have H := vanDerCorput_second_deriv (f:=iterForwardDiff h (logPhase τ a))
    (f':=iterForwardDiff h g) (f'':=iterForwardDiff h u)
    hb hL (c:=K^(k+2)) (one_le_pow₀ hK)
    (fun x hx => iterForwardDiff_hasDerivAt h (fun i => (hh i).le)
      (fun t ht => logPhase_deriv τ a (by linarith [ha.1])) (hm0.trans_le hx.1))
    (fun x hx => iterForwardDiff_hasDerivAt h (fun i => (hh i).le)
      (fun t ht => logPhase_second τ a (by linarith [ha.1])) (hm0.trans_le hx.1))
    (fun x hx => (iterForwardDiff_hasDerivAt h (fun i => (hh i).le) du
      (hm0.trans_le hx.1)).continuousAt.continuousWithinAt) (by
      intro x hx
      obtain ⟨y,hy,hy'⟩ := iterForwardDiff_log_curvature (τ:=τ) h hh ha.1 (hm0.trans_le hx.1)
      change |iterForwardDiff h u x| = P/(y+a)^(k+2) at hy'
      rw [hy']
      have hsum : ∑ i,h i ≤ k*(M:ℝ) := by simpa using Finset.sum_le_sum (s:=univ) (fun i _ => hhM i)
      have hbm : (b:ℝ)≤2*M := by exact_mod_cast hb'
      have hylo : (M:ℝ)≤y+a := by linarith [hy.1,hx.1,ha.1]
      have hyhi : y+a≤K*M := by dsimp [K]; nlinarith only [hy.2,hx.2,hbm,ha.2,hm,hsum]
      constructor
      · exact div_le_div_of_nonneg_left hP.le (pow_pos (hm0.trans_le hylo) _)
          (pow_le_pow_left₀ (hm0.trans_le hylo).le hyhi _)
      · calc P/(y+a)^(k+2) ≤ P/(M:ℝ)^(k+2) := div_le_div_of_nonneg_left hP.le
                (pow_pos hm0 _) (pow_le_pow_left₀ hm0.le hylo _)
             _ = K^(k+2)*lam := by dsimp [lam]; rw [mul_pow]; field_simp)
  simpa only [e,← Real.sqrt_eq_rpow,Real.rpow_neg hL.le,K,P,lam] using H

end AnalyticNumberTheory.ExponentialSums
