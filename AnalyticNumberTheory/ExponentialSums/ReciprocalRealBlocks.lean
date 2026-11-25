import AnalyticNumberTheory.ExponentialSums.ReciprocalBProcess
import AnalyticNumberTheory.ExponentialSums.RealPoissonIntervals

/-!
# Reciprocal exponential sums with real endpoints
-/

open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.ExponentialSums

/-- The reciprocal B-process with exact real endpoints in both variables. -/
theorem reciprocal_vanDerCorput_real {a b A : ℝ} (ha : 1≤a) (hab : a≤b)
    (hba : b≤2*a) (hA : 0<A) :
    ‖(∑ n∈Finset.Ioc ⌊a⌋ ⌊b⌋,e (A/(n:ℝ))) -
      ∑ m∈Finset.Icc ⌈A/b^2⌉ ⌊A/a^2⌋,reciprocalSaddleTerm A m‖ ≤
      248*(1+Real.sqrt (b^3/A))*(1+Real.log (6+4*A/a^2)) := by
  let l : ℝ := ⌊a⌋
  let Z := A/l^2
  let G := Real.sqrt (b^3/A)
  have hl₁ : 1≤⌊a⌋ := Int.le_floor.mpr (by simpa using ha)
  have hl : 1≤l := by dsimp [l]; exact_mod_cast hl₁
  have hl' : 0<l := by linarith
  have hLa : l≤a := Int.floor_le a
  have ha' : 0<a := by linarith
  have hlower : a≤2*l := by linarith [show a<l+1 from Int.lt_floor_add_one _]
  have hZ : A/a^2≤Z := by dsimp [Z]; gcongr
  have hZp : 0<Z := by dsimp [Z]; positivity
  have hZu : Z≤4*A/a^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hl') (sq_pos_of_pos ha')).mpr
    calc A*a^2 ≤ A*(2*l)^2 := by gcongr
         _ = _ := by ring
  have hp {t : ℝ} (ht : t∈Icc l (b+1)) := hl'.trans_le ht.1
  have hD (t : ℝ) (ht : t∈Icc l (b+1)) : HasDerivAt (fun t : ℝ => A/t) (-A/t^2) t := by
    simpa only [id_eq,zero_mul,mul_one,zero_sub] using (hasDerivAt_const t A).fun_div (hasDerivAt_id t) (hp ht).ne'
  have hD' (t : ℝ) (ht : t∈Icc l (b+1)) : HasDerivAt (fun t : ℝ => -A/t^2) (2*A/t^3) t := by
    apply ((hasDerivAt_const t (-A)).fun_div (hasDerivAt_pow 2 t) (pow_ne_zero _ (hp ht).ne')).congr_deriv
    field_simp [(hp ht).ne']; ring
  have HP := vanDerCorput_poisson_real (α:=-Z) (β:=0) hab (by linarith) hD hD'
    (ContinuousOn.div (f:=fun _ : ℝ => 2*A) (g:=fun t : ℝ => t^3) continuousOn_const (continuousOn_id.pow 3) (fun _ ht => pow_ne_zero 3 (hp ht).ne'))
    (Or.inl (fun t ht => by have := hp ht; positivity)) (fun t ht => by
      have H : A/t^2≤Z := by dsimp [Z]; gcongr; exact ht.1
      exact ⟨by rw [neg_div]; linarith,div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)⟩)
  simp only [Int.ceil_zero,zero_add,zero_sub,neg_neg] at HP
  have HQ := reciprocal_dual_integral_sum_error ha' hab hba hA hZ
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add HP HQ).trans ?_)
  have h₁ := Real.log_le_log (by positivity : 0<2+Z) (by linarith : 2+Z≤6+4*A/a^2)
  have h₂ := Real.log_le_log (by positivity : 0<6+Z) (by linarith : 6+Z≤6+4*A/a^2)
  have hC := Real.log_nonneg (by linarith : 1≤6+4*A/a^2)
  have hG : 0≤G := Real.sqrt_nonneg _
  change 96*(1+Real.log (2+Z))+152*(1+G)*(1+Real.log (6+Z))≤248*(1+G)*(1+Real.log (6+4*A/a^2))
  nlinarith only [h₁,h₂,hG,mul_nonneg hG hC,mul_le_mul_of_nonneg_left h₂ hG]

private theorem closed_sub_open_frequency {u V : ℝ} (huV : u≤V) (f : ℤ→ℂ)
    {K : ℝ} (hK : 0≤K) (h : ∀ m:ℤ, (m:ℝ)=u → ‖f m‖≤K) :
    ‖(∑ m∈Finset.Icc ⌈u⌉ ⌊V⌋,f m)-(∑ m∈Finset.Ioc ⌊u⌋ ⌊V⌋,f m)‖≤K := by
  have h₁ : ⌊u⌋≤⌈u⌉ := Int.floor_le_ceil _
  have h₂ : ⌈u⌉≤⌊u⌋+1 := Int.ceil_le.mpr (by push_cast; exact (Int.lt_floor_add_one u).le)
  by_cases he : ⌈u⌉=⌊u⌋
  · have hu : (⌊u⌋:ℝ)=u := le_antisymm (Int.floor_le _) (by rw [←he]; exact Int.le_ceil u)
    have hf : ⌊u⌋≤⌊V⌋ := Int.floor_le_floor huV
    have hs : Finset.Icc ⌈u⌉ ⌊V⌋=insert ⌊u⌋ (Finset.Ioc ⌊u⌋ ⌊V⌋) := by
      ext n; simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ioc]; omega
    rw [hs,Finset.sum_insert (by simp),add_sub_cancel_right]
    exact h _ hu
  · have hs : Finset.Icc ⌈u⌉ ⌊V⌋=Finset.Ioc ⌊u⌋ ⌊V⌋ := by
      ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc]; omega
    simpa only [hs,sub_self,norm_zero] using hK

/-- A half-open spectral window makes the transform additive when adjacent
physical intervals are joined. -/
theorem reciprocal_vanDerCorput_real_Ioc {a b A : ℝ} (ha : 1≤a) (hab : a≤b)
    (hba : b≤2*a) (hA : 0<A) :
    ‖(∑ n∈Finset.Ioc ⌊a⌋ ⌊b⌋,e (A/(n:ℝ))) -
      ∑ m∈Finset.Ioc ⌊A/b^2⌋ ⌊A/a^2⌋,reciprocalSaddleTerm A m‖ ≤
      249*(1+Real.sqrt (b^3/A))*(1+Real.log (6+4*A/a^2)) := by
  have ha' : 0<a := by linarith
  have hb := ha'.trans_le hab
  have h₁ := reciprocal_vanDerCorput_real ha hab hba hA
  have h₂ := closed_sub_open_frequency (show A/b^2≤A/a^2 by gcongr) (fun m : ℤ => reciprocalSaddleTerm A m)
    (Real.sqrt_nonneg (b^3/A)) (fun m hm => by rw [hm]; exact norm_reciprocalSaddleTerm_at_slope_le hA hb)
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add h₁ h₂).trans ?_)
  have hG := Real.sqrt_nonneg (b^3/A)
  have hL := Real.log_nonneg (by linarith [show 0≤4*A/a^2 by positivity] : 1≤6+4*A/a^2)
  nlinarith only [hL,hG,mul_nonneg hG hL]

private theorem intSumIoc_split (f : ℤ→ℂ) {a b c : ℤ} (hab : a≤b) (hbc : b≤c) :
    ∑ n∈Finset.Ioc a c,f n = ∑ n∈Finset.Ioc a b,f n + ∑ n∈Finset.Ioc b c,f n := by
  rw [←Finset.Ioc_union_Ioc_eq_Ioc hab hbc,Finset.sum_union]
  exact Finset.disjoint_left.mpr (fun n h h' => ((Finset.mem_Ioc.mp h').1).not_ge (Finset.mem_Ioc.mp h).2)

/-- The half-open reciprocal transform for an arbitrary positive interval.
The length parameter counts the number of dyadic pieces required. -/
theorem reciprocal_vanDerCorput_interval {A a b : ℝ} (ha : 1≤a) (hab : a≤b) (hA : 0<A)
    (J : ℕ) (hJ : b≤(2:ℝ)^J*a) :
    ‖(∑ n∈Finset.Ioc ⌊a⌋ ⌊b⌋,e (A/(n:ℝ))) -
      ∑ m∈Finset.Ioc ⌊A/b^2⌋ ⌊A/a^2⌋,reciprocalSaddleTerm A m‖ ≤
      (J:ℝ)*249*(1+Real.sqrt (b^3/A))*(1+Real.log (6+4*A/a^2)) := by
  let F (x y : ℝ) := ∑ n∈Finset.Ioc ⌊x⌋ ⌊y⌋,e (A/(n:ℝ))
  let G (x y : ℝ) := ∑ m∈Finset.Ioc ⌊A/y^2⌋ ⌊A/x^2⌋,reciprocalSaddleTerm A m
  let E (x y : ℝ) := 249*(1+Real.sqrt (y^3/A))*(1+Real.log (6+4*A/x^2))
  have hE {x y : ℝ} (hx : 0<x) : 0≤E x y := by
    have := Real.log_nonneg (by linarith [show 0≤4*A/x^2 by positivity] : 1≤6+4*A/x^2)
    dsimp [E]; positivity
  have ha' : 0<a := by linarith
  have hgen (j : ℕ) {y : ℝ} (hay : a≤y) (hy : y≤(2:ℝ)^j*a) :
      ‖F a y-G a y‖≤(j:ℝ)*E a y := by
    induction j generalizing y with
    | zero =>
      have he : y=a := le_antisymm (by simpa using hy) hay
      simp [he,F,G]
    | succ j ih =>
      let c := (2:ℝ)^j*a
      have hac : a≤c := by
        exact le_mul_of_one_le_left ha'.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
      by_cases h : y≤c
      · exact (ih hay h).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) (hE ha'))
      have hcy := (not_le.mp h).le
      have hc' := ha'.trans_le hac
      have hyc : y≤2*c := by dsimp [c]; rw [pow_succ] at hy; linarith only [hy]
      have hleft := ih hac (le_refl c)
      have hright := reciprocal_vanDerCorput_real_Ioc (ha.trans hac) hcy hyc hA
      have hlog := Real.log_nonneg (by linarith [show 0≤4*A/a^2 by positivity] : 1≤6+4*A/a^2)
      have hE₁ : E a c≤E a y := by
        dsimp [E]; gcongr
      have hE₂ : E c y≤E a y := by
        dsimp [E]; gcongr
      have hF : F a y=F a c+F c y := intSumIoc_split _ (Int.floor_le_floor hac) (Int.floor_le_floor hcy)
      have hG : G a y=G c y+G a c := intSumIoc_split _
        (Int.floor_le_floor (show A/y^2≤A/c^2 by gcongr))
        (Int.floor_le_floor (show A/c^2≤A/a^2 by gcongr))
      rw [hF,hG,show F a c+F c y-(G c y+G a c)=(F a c-G a c)+(F c y-G c y) by abel]
      have hex : ‖F c y-G c y‖≤E c y := hright
      apply (norm_add_le _ _).trans
      apply (add_le_add (hleft.trans (mul_le_mul_of_nonneg_left hE₁ (by positivity))) (hex.trans hE₂)).trans_eq
      push_cast; ring
  exact (hgen J hab hJ).trans_eq (by dsimp [E]; ring)

end AnalyticNumberTheory.ExponentialSums
