import AnalyticNumberTheory.SieveMethods.LinearSieveMonotonicity

/-! # A rational bound for the two-step linear sieve contraction

On the transition interval from two to four, elementary rational majorants
for the exponential and logarithm give a contraction coefficient of 73/100.
-/
noncomputable section
open Real Set
namespace AnalyticNumberTheory.SieveMethods

private theorem sieveRate_mono {a b : ℝ} (hab : a≤b) {f f' : ℝ→ℝ}
    (hd : ∀v∈Icc a b, HasDerivAt f (f' v) v) (hn : ∀v∈Icc a b, 0≤f' v) :
    f a ≤ f b := by
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (HasDerivAt.continuousOn hd)
    (fun v hv => (hd v (interior_subset hv)).hasDerivWithinAt)
    (fun v hv => hn v (interior_subset hv)) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

private theorem sieveRate_exp {u : ℝ} (h₁ : 2≤u) (h₂ : u≤4) :
    exp (u-2)≤((u+6)/(10-u))^4 := by
  let F := fun t : ℝ => 4*(log (t+6)-log (10-t))-(t-2)
  have hd (v : ℝ) (hv : v∈Icc 2 u) : HasDerivAt F ((v-2)^2/((v+6)*(10-v))) v := by
    have hv₁ : 0<v+6 := by linarith [hv.1]
    have hv₂ : 0<10-v := by linarith [hv.2]
    have H := (((((hasDerivAt_id' v).add_const 6).log hv₁.ne').sub
      (((hasDerivAt_id' v).const_sub 10).log hv₂.ne')).const_mul 4).sub
      ((hasDerivAt_id' v).sub_const 2)
    convert H using 1
    field_simp [hv₁.ne',hv₂.ne']
    ring
  have H := sieveRate_mono h₁ hd (fun v hv => div_nonneg (sq_nonneg _) (mul_nonneg
    (by linarith [hv.1]) (by linarith [hv.2])))
  have hl : u-2≤4*log ((u+6)/(10-u)) := by
    rw [Real.log_div (by linarith) (by linarith)]
    norm_num [F] at H
    linarith
  have hp : 0<(u+6)/(10-u) := div_pos (by linarith) (by linarith)
  calc exp (u-2) ≤ exp (4*log ((u+6)/(10-u))) := Real.exp_le_exp.mpr hl
       _ = _ := by rw [show (4:ℝ)=(4:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hp]

private def sieveRate_logMajorant (x : ℝ) := 2*(x-1)/(x+1)+(x-1)^3/(6*x*(x+1))

private theorem sieveRate_log {x : ℝ} (hx : 1≤x) : log x≤sieveRate_logMajorant x := by
  let F := fun t : ℝ => sieveRate_logMajorant t - log t
  have hd (v : ℝ) (hv : v∈Icc 1 x) :
      HasDerivAt F ((v-1)^4/(6*v^2*(v+1)^2)) v := by
    have hv₁ : v≠0 := by linarith [hv.1]
    have hv₂ : v+1≠0 := by linarith [hv.1]
    have A := (hasDerivAt_id' v).sub_const 1
    have B := (hasDerivAt_id' v).add_const 1
    have C := ((hasDerivAt_id' v).const_mul 6).mul B
    have H := (((A.const_mul 2).div B hv₂).add ((A.pow 3).div C
      (show 6*v*(v+1)≠0 by positivity [zero_lt_one.trans_le hv.1]))).sub (Real.hasDerivAt_log hv₁)
    convert H using 1
    · rfl
    · dsimp
      field_simp [hv₁,hv₂]
      ring
  have H := sieveRate_mono hx hd (fun v _ => by positivity)
  simp [F,sieveRate_logMajorant] at H ⊢
  linarith

/-- Numerical estimate on the transition segment of the continuum kernel. -/
theorem linearSieve_transition_rate {u : ℝ} (h₁ : 2≤u) (h₂ : u≤4) :
    exp (u-2)/u*(log (3/(u-1))+1/3)≤73/100 := by
  have hu : 0<u := by linarith
  have hp : 0<u-1 := by linarith
  have hq : 0<u+2 := by linarith
  have hr : 0<10-u := by linarith
  have hx : 1≤3/(u-1) := (one_le_div hp).mpr (by linarith)
  have H := mul_le_mul (div_le_div_of_nonneg_right (sieveRate_exp h₁ h₂) hu.le)
    (add_le_add_left (sieveRate_log hx) (1/3)) (by linarith [Real.log_nonneg hx])
    (div_nonneg (by positivity) hu.le)
  apply H.trans
  have hM : sieveRate_logMajorant (3/(u-1)) = (4-u)*(u^2+28*u-20)/(18*(u-1)*(u+2)) := by
    unfold sieveRate_logMajorant
    have hp' : 3/(u-1)+1≠0 := by linarith
    field_simp [hp.ne',hq.ne',hp']
    ring
  rw [hM]
  have hnum : 0 ≤ 229376*(4-u)^7+12009472*(u-2)*(4-u)^6+64868352*(u-2)^2*(4-u)^5+
      136990720*(u-2)^3*(4-u)^4+141088640*(u-2)^4*(4-u)^3+80094912*(u-2)^5*(4-u)^2+
      30124224*(u-2)^6*(4-u)+7305984*(u-2)^7 := by positivity [sub_nonneg.mpr h₁,sub_nonneg.mpr h₂]
  field_simp [hu,hp,hq,hr]
  nlinarith only [hnum]

end AnalyticNumberTheory.SieveMethods
