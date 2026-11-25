import AnalyticNumberTheory.ExponentialSums.ReciprocalTransform
import AnalyticNumberTheory.ExponentialSums.ShiftedHarmonicSums

/-!
# The reciprocal-phase B-process on a dyadic interval

The dual sum is taken over the integers between the two endpoint slopes.
Its terms have square-root phase. All constants and endpoint conventions
are explicit.
-/

open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.ExponentialSums

private theorem reciprocal_dual_frequency_sum {u V Z : ℝ} (hu : 0<u) (hZ : V≤Z)
    (F : ℤ→ℂ) :
    (∑ n ∈ Finset.Icc (⌊-Z⌋-1) 1, if u≤-(n:ℝ) ∧ -(n:ℝ)≤V then F (-n) else 0) =
      ∑ m ∈ Finset.Icc ⌈u⌉ ⌊V⌋, F m := by
  classical
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun n _ => -n)
  · intro n hn
    have h := (Finset.mem_filter.mp hn).2
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by simpa using h.1),Int.le_floor.mpr (by simpa using h.2)⟩
  · intro n hn m hm he; omega
  · intro m hm
    have ⟨hl,hr⟩ := Finset.mem_Icc.mp hm
    have hl' : u≤(m:ℝ) := Int.ceil_le.mp hl
    have hr' : (m:ℝ)≤V := Int.le_floor.mp hr
    refine ⟨-m,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,by simpa using And.intro hl' hr'⟩,by simp⟩
    · have h : (⌊-Z⌋:ℝ)≤(-m:ℤ) := by push_cast; linarith [Int.floor_le (-Z)]
      have h' : ⌊-Z⌋≤-m := by exact_mod_cast h
      omega
    · have h : 0≤m := by exact_mod_cast (hu.le.trans hl')
      omega
  · intro _ _; rfl

private theorem dual_integral_error {a b A : ℝ} (ha : 0<a) (hab : a≤b)
    (hba : b≤2*a) (hA : 0<A) (n : ℤ) :
    ‖(∫ t in a..b,e (A/t-(n:ℝ)*t)) -
      (if A/b^2≤-(n:ℝ) ∧ -(n:ℝ)≤A/a^2 then reciprocalSaddleTerm A (-n) else 0)‖ ≤
      19*(1+Real.sqrt (b^3/A))*
        (1/(1+|(n:ℝ)-(-(A/a^2))|)+1/(1+|(n:ℝ)-(-(A/b^2))|)) := by
  have hb := ha.trans_le hab
  have H := reciprocal_transform_integral ha hab hba hA (-(n:ℝ))
  simp only [neg_mul,←sub_eq_add_neg] at H
  have habs (x : ℝ) : |-(n:ℝ)-x|=|(n:ℝ)-(-x)| := by
    rw [←abs_neg (-(n:ℝ)-x)]; congr 1; ring
  rw [habs,habs] at H
  apply H.trans
  let u := A/b^2
  let V := A/a^2
  let G := Real.sqrt (b^3/A)
  let U := 1/(1+|(n:ℝ)-(-u)|)
  let W := 1/(1+|(n:ℝ)-(-V)|)
  have hG : 0≤G := Real.sqrt_nonneg _
  have hU : 0≤U := by dsimp [U]; positivity
  have hW : 0≤W := by dsimp [W]; positivity
  change (if u≤-(n:ℝ) ∧ -(n:ℝ)≤V then 1/(Real.pi * -(n:ℝ)) else 0) + 18*(1+G)*(W+U) ≤ 19*(1+G)*(W+U)
  have hsmall : (if u≤-(n:ℝ) ∧ -(n:ℝ)≤V then 1/(Real.pi * -(n:ℝ)) else 0)≤U := by
    split_ifs with h
    · have hu : 0<u := by dsimp [u]; positivity
      have hz : n<0 := by exact_mod_cast (show (n:ℝ)<0 by linarith [h.1])
      have h1 : (1:ℝ)≤-(n:ℝ) := by exact_mod_cast (show (1:ℤ)≤-n by omega)
      dsimp only [U]
      rw [abs_of_nonpos (by linarith [h.1] : (n:ℝ)-(-u)≤0)]
      apply div_le_div_of_nonneg_left zero_le_one (by linarith [h.1]) _
      nlinarith only [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (show 0≤-(n:ℝ) by linarith), h1,hu]
    · exact hU
  nlinarith only [hsmall,hW,mul_nonneg hG (add_nonneg hW hU)]

/-- All stationary and nonstationary integral errors summed over the Poisson
frequency window. The upper cutoff may exceed the maximal endpoint slope. -/
theorem reciprocal_dual_integral_sum_error {a b A Z : ℝ} (ha : 0<a) (hab : a≤b)
    (hba : b≤2*a) (hA : 0<A) (hZ : A/a^2≤Z) :
    ‖(∑ n∈Finset.Icc (⌊-Z⌋-1) (1:ℤ),∫ t in a..b,e (A/t-(n:ℝ)*t)) -
      ∑ m∈Finset.Icc ⌈A/b^2⌉ ⌊A/a^2⌋,reciprocalSaddleTerm A m‖ ≤
      152*(1+Real.sqrt (b^3/A))*(1+Real.log (6+Z)) := by
  let u := A/b^2
  let V := A/a^2
  let S := Finset.Icc (⌊-Z⌋-1) (1:ℤ)
  let K : ℕ := ⌈Z⌉₊+2
  let G := Real.sqrt (b^3/A)
  have hb := ha.trans_le hab
  have hu : 0<u := by dsimp [u]; positivity
  have hV : 0<V := by dsimp [V]; positivity
  have huV : u≤V := by dsimp [u,V]; gcongr
  have hZp := hV.trans_le hZ
  have hG : 0≤G := Real.sqrt_nonneg _
  let Q (n : ℤ) := ∫ t in a..b, e (A/t-(n:ℝ)*t)
  let F (n : ℤ) := if u≤-(n:ℝ) ∧ -(n:ℝ)≤V then reciprocalSaddleTerm A (-(n:ℝ)) else 0
  have hQ : ‖(∑ n ∈ S,Q n) - ∑ n ∈ S,F n‖ ≤
      19*(1+G)*(4*(1+Real.log (K+2:ℝ))+4*(1+Real.log (K+2:ℝ))) := by
    rw [←Finset.sum_sub_distrib]
    have hsum (x : ℝ) (hx : 0≤x) (hx' : x≤Z) :=
      sum_shifted_inv_one_add_abs_le S (y:=-x) (K:=K) (fun n hn => by
        have hh := Finset.mem_Icc.mp hn
        have hnl : (⌊-Z⌋:ℝ)-1≤n := by exact_mod_cast hh.1
        have hnu : (n:ℝ)≤1 := by exact_mod_cast hh.2
        have hK : Z+2≤(K:ℝ) := by dsimp [K]; push_cast; linarith [Nat.le_ceil Z]
        apply abs_le.mpr
        constructor <;> linarith [Int.sub_one_lt_floor (-Z)])
    calc
      ‖∑ n∈S,(Q n-F n)‖ ≤ ∑ n∈S,‖Q n-F n‖ := norm_sum_le _ _
      _ ≤ ∑ n∈S,19*(1+G)*(1/(1+|(n:ℝ)-(-V)|)+1/(1+|(n:ℝ)-(-u)|)) :=
        Finset.sum_le_sum (fun n _ => dual_integral_error ha hab hba hA n)
      _ ≤ 19*(1+G)*(4*(1+Real.log (K+2:ℝ))+4*(1+Real.log (K+2:ℝ))) := by
        rw [←Finset.mul_sum,Finset.sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (add_le_add (hsum _ hV.le hZ) (hsum _ hu.le (huV.trans hZ))) (by positivity)
  have hcollapse := reciprocal_dual_frequency_sum (V:=V) (Z:=Z) hu hZ (fun m : ℤ => reciprocalSaddleTerm A m)
  have hf : (∑ n∈S,F n)= ∑ m∈Finset.Icc ⌈u⌉ ⌊V⌋,reciprocalSaddleTerm A m := by
    simpa only [S,F,Int.cast_neg] using hcollapse
  rw [←hf]
  apply hQ.trans
  have hK : (K:ℝ)+2≤6+Z := by dsimp [K]; push_cast; linarith [Nat.ceil_lt_add_one hZp.le]
  have hlogK := Real.log_le_log (by positivity : 0<(K:ℝ)+2) hK
  nlinarith only [hlogK,mul_le_mul_of_nonneg_left hlogK hG]

/-- The unconditional van der Corput transform of a reciprocal exponential
sum. The error grows at most logarithmically in the spectral length,
with the square-root reciprocal curvature cost at the endpoints. -/
theorem reciprocal_vanDerCorput_transform {a b : ℤ} (ha : 0<a) (hab : a<b)
    (hba : b≤2*a) {A : ℝ} (hA : 0<A) :
    ‖(∑ n ∈ Finset.Ioc a b,e (A/(n:ℝ))) -
      ∑ m ∈ Finset.Icc ⌈A/(b:ℝ)^2⌉ ⌊A/(a:ℝ)^2⌋, reciprocalSaddleTerm A m‖ ≤
      216*(1+Real.sqrt ((b:ℝ)^3/A))*(1+Real.log (6+A/(a:ℝ)^2)) := by
  classical
  let V := A/(a:ℝ)^2
  let u := A/(b:ℝ)^2
  let G := Real.sqrt ((b:ℝ)^3/A)
  let S := Finset.Icc (⌊-V⌋-1) (1:ℤ)
  let K : ℕ := ⌈V⌉₊+2
  have ha' : 0<(a:ℝ) := by exact_mod_cast ha
  have hab' : (a:ℝ)≤b := by exact_mod_cast hab.le
  have hb' := ha'.trans_le hab'
  have hba' : (b:ℝ)≤2*(a:ℝ) := by exact_mod_cast hba
  have hu : 0<u := by dsimp [u]; positivity
  have hV : 0<V := by dsimp [V]; positivity
  have huV : u≤V := by dsimp [u,V]; gcongr
  have hG : 0≤G := Real.sqrt_nonneg _
  let U := (a:ℝ)+1/4
  let W := (b:ℝ)+3/4
  have hp {t : ℝ} (ht : t∈Icc U W) : 0<t := by dsimp [U] at ht; linarith [ht.1]
  have hC : ContinuousOn (fun t : ℝ => A/t) (Icc (a:ℝ) W) := continuousOn_const.div continuousOn_id (fun _ ht => (ha'.trans_le ht.1).ne')
  have hD (t : ℝ) (ht : t∈Icc U W) : HasDerivAt (fun t : ℝ => A/t) (-A/t^2) t := by
    simpa only [id_eq,zero_mul,mul_one,zero_sub] using (hasDerivAt_const t A).fun_div (hasDerivAt_id t) (hp ht).ne'
  have hD' (t : ℝ) (ht : t∈Icc U W) : HasDerivAt (fun t : ℝ => -A/t^2) (2*A/t^3) t := by
    apply ((hasDerivAt_const t (-A)).fun_div (hasDerivAt_pow 2 t) (pow_ne_zero _ (hp ht).ne')).congr_deriv
    field_simp [(hp ht).ne']; ring
  have hP := vanDerCorput_poisson_sharp (α:=-V) (β:=0) hab (by linarith) hC hD hD'
    (ContinuousOn.div (f:=fun _ : ℝ => 2*A) (g:=fun t : ℝ => t^3) continuousOn_const (continuousOn_id.pow 3) (fun _ ht => pow_ne_zero 3 (hp ht).ne'))
    (Or.inl (fun t ht => by have := hp ht; positivity)) (fun t ht => by
      have ht' : (a:ℝ)≤t := by linarith [ht.1]
      have H : A/t^2≤V := by dsimp [V]; gcongr
      constructor
      · rw [neg_div]; linarith
      · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  simp only [Int.ceil_zero,zero_add,zero_sub,neg_neg] at hP
  have hQ := reciprocal_dual_integral_sum_error ha' hab' hba' hA (le_refl V)
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hP hQ).trans ?_)
  have hlog := Real.log_le_log (by positivity : 0<2+V) (by linarith : 2+V≤6+V)
  have hlogn := Real.log_nonneg (by linarith : 1≤6+V)
  change 64*(1+Real.log (2+V))+152*(1+G)*(1+Real.log (6+V))≤216*(1+G)*(1+Real.log (6+V))
  nlinarith only [hlog,hG,mul_nonneg hG hlogn]

end AnalyticNumberTheory.ExponentialSums
