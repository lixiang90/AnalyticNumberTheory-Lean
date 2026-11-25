import AnalyticNumberTheory.SieveMethods.BrunTitchmarshFull

/-! # The strict Brun–Titchmarsh inequality

For y/q > e, moving the left endpoint slightly to the right preserves
the prime count and strictly decreases the upper bound. For the remaining
ratios the unsieved count already gives a strict inequality.
-/
open Real Set Finset
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

private theorem bt_div_log_strict : StrictMonoOn (fun v : ℝ => v/log v) (Set.Ioi (exp 1)) := by
  have hd (v : ℝ) (hv : v∈Set.Ioi (exp 1)) :
      HasDerivAt (fun t : ℝ => t/log t) ((log v-1)/(log v)^2) v := by
    have h₁ : 1<log v := (Real.lt_log_iff_exp_lt ((exp_pos 1).trans hv)).2 hv
    convert (hasDerivAt_id' v).div (Real.hasDerivAt_log ((exp_pos 1).trans hv).ne') (by linarith : log v≠0) using 1
    field_simp [((exp_pos 1).trans hv).ne']
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi _) (HasDerivAt.continuousOn hd)
    (fun v hv => (hd v (interior_subset hv)).hasDerivWithinAt)
  intro v hv
  have he := interior_subset hv
  have h₁ : 1<log v := (Real.lt_log_iff_exp_lt ((exp_pos 1).trans he)).2 he
  exact div_pos (sub_pos.mpr h₁) (sq_pos_of_pos (by linarith))

/-- Strict form of the Brun–Titchmarsh theorem throughout y > q. -/
theorem brun_titchmarsh_strict {x y : ℝ} {q a : ℕ} (hx : 0≤x) (hq : 1≤q) (hy : (q:ℝ)<y) :
    piAP (x+y) q a-piAP x q a < 2*y/(q.totient*log (y/(q:ℝ))) := by
  let u := y/(q:ℝ)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hu : 1<u := (one_lt_div hq').2 hy
  have hlu := Real.log_pos hu
  have he : (q:ℝ)*u=y := by dsimp [u]; field_simp
  by_cases hsmall : u≤exp 1
  · have hlog : log u≤1 := (Real.log_le_iff_le_exp (by linarith : 0<u)).2 hsmall
    have P₀ : primeFinset 1=∅ := by unfold primeFinset; rw [Nat.floor_one]; decide
    have H := brun_titchmarsh_wheel (a:=a) hx (hq'.trans hy) hq 1
    simp only [P₀,Finset.prod_empty,mul_one,Finset.card_empty,pow_zero,Nat.cast_zero,add_zero] at H
    apply (lt_div_iff₀ (mul_pos hφ hlu)).2
    rw [←mul_assoc]
    apply (mul_le_mul_of_nonneg_right H hlu.le).trans_lt
    change (q:ℝ)*(u+1)*log u<_
    have hh := mul_le_mul_of_nonneg_left hlog (mul_nonneg hq'.le (by linarith : 0≤u+1))
    nlinarith only [hh,he,mul_pos hq' (sub_pos.mpr hu)]
  let h := min ((y-(q:ℝ)*exp 1)/2) (((⌊x⌋₊:ℕ):ℝ)+1-x)/2
  have hbig := (not_le.mp hsmall)
  have hgap : 0<y-(q:ℝ)*exp 1 := by linarith [(lt_div_iff₀ hq').mp hbig]
  have hfloor := Nat.lt_floor_add_one x
  have hpos : 0<h := by
    dsimp only [h]
    apply div_pos (lt_min (by positivity) (by linarith)) (by norm_num)
  have hfirst : h < y-(q:ℝ)*exp 1 := by
    have h₁ := min_le_left ((y-(q:ℝ)*exp 1)/2) (((⌊x⌋₊:ℕ):ℝ)+1-x)
    dsimp only [h]
    linarith only [h₁,hgap]
  have hsecond : x+h< (⌊x⌋₊:ℝ)+1 := by
    have h₂ := min_le_right ((y-(q:ℝ)*exp 1)/2) (((⌊x⌋₊:ℕ):ℝ)+1-x)
    dsimp only [h]
    linarith only [h₂,hfloor]
  have hx' : 0≤x+h := by linarith
  have hfl : ⌊x+h⌋₊=⌊x⌋₊ := by
    apply Nat.le_antisymm _ (Nat.floor_mono (by linarith))
    apply Nat.lt_succ_iff.mp
    exact (Nat.floor_lt hx').2 (by simpa only [Nat.cast_succ] using hsecond)
  have hpi : piAP (x+h) q a=piAP x q a := by simp [piAP,primeCountingAP,hfl]
  have he' : exp 1 < (y-h)/q := (lt_div_iff₀ hq').2 (by linarith)
  have hy' : (q:ℝ)<y-h := (one_lt_div hq').1 ((Real.one_lt_exp_iff.2 zero_lt_one).trans he')
  have H := brun_titchmarsh_two (a:=a) hx' hq hy'
  rw [show x+h+(y-h)=x+y by ring,hpi] at H
  apply H.trans_lt
  have H' := bt_div_log_strict he' hbig (div_lt_div_of_pos_right (by linarith : y-h<y) hq')
  have heq (v : ℝ) : 2*v/(q.totient*log (v/q))=
      (2*(q:ℝ)/q.totient)*((v/q)/log (v/q)) := by field_simp [hq'.ne'] <;> ring
  rw [heq,heq]
  exact mul_lt_mul_of_pos_left H' (by positivity)

end AnalyticNumberTheory.SieveMethods
