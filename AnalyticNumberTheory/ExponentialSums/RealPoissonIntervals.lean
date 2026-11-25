import AnalyticNumberTheory.ExponentialSums.SharpPoissonSummation

/-!
# Truncated Poisson summation with real endpoints

The exponential sum uses the integers in `(a,b]`. Its dual integrals
extend exactly between `a` and `b`, even when an endpoint lies strictly
between integers.
-/

open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.ExponentialSums

private theorem kernel_neg (A B : ℤ) (t : ℝ) :
    intervalDirichletKernel A B (-t)=star (intervalDirichletKernel A B t) := by
  dsimp only [intervalDirichletKernel]; rw [star_sum]
  apply Finset.sum_congr rfl; intro n _; rw [star_e]; congr 1; ring

/-- Any part of a unit interval with integer endpoints costs only a
logarithmic factor in the number of consecutive frequencies. -/
theorem norm_integral_mul_kernel_unit_le {A B i : ℤ} (hAB : A<B)
    {l u : ℝ} (hl : (i:ℝ)≤l) (hlu : l≤u) (hu : u≤(i:ℝ)+1)
    {F : ℝ→ℂ} (hc : ContinuousOn F (Icc l u)) (hF : ∀ t∈Icc l u,‖F t‖≤1) :
    ‖∫ t in l..u,F t*intervalDirichletKernel A B t‖≤8*Real.log (1+((B:ℝ)-A)) := by
  let K := intervalDirichletKernel A B
  let v := max l (min u ((i:ℝ)+1/2))
  let L := 4*Real.log (1+((B:ℝ)-A))
  have hlv : l≤v := le_max_left _ _
  have hvu : v≤u := max_le hlu (min_le_left _ _)
  have hkc := continuous_intervalDirichletKernel A B
  have hL : 0≤L := by
    have hN : 0<(B:ℝ)-A := sub_pos.mpr (by exact_mod_cast hAB)
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hleft : ‖∫ t in l..v,F t*K t‖≤L := by
    by_cases hv : v≤(i:ℝ)+3/4
    · exact norm_integral_mul_intervalDirichletKernel_le hAB hl hlv hv
        (hc.mono (Icc_subset_Icc_right hvu)) (fun t ht => hF t ⟨ht.1,ht.2.trans hvu⟩)
    · have H : v=l := max_eq_left (by
        by_contra! hh
        rw [show v=min u ((i:ℝ)+1/2) from max_eq_right hh.le] at hv
        linarith [min_le_right u ((i:ℝ)+1/2)])
      simpa only [H,intervalIntegral.integral_same,norm_zero] using hL
  have hright : ‖∫ t in v..u,F t*K t‖≤L := by
    by_cases hv : (i:ℝ)+1/4≤v
    · let j : ℤ := -(i+1)
      have hl' : (j:ℝ)≤-u := by dsimp [j]; push_cast; linarith
      have hu' : -v≤(j:ℝ)+3/4 := by dsimp [j]; push_cast; linarith
      let f (t : ℝ) := star (F (-t))
      have hm {t : ℝ} (ht : t∈Icc (-u) (-v)) : -t∈Icc l u := by constructor <;> linarith [ht.1,ht.2]
      have hf : ContinuousOn f (Icc (-u) (-v)) :=
        continuous_star.comp_continuousOn (hc.comp (continuous_id.neg.continuousOn) (fun _ ht => hm ht))
      have H := norm_integral_mul_intervalDirichletKernel_le hAB hl' (neg_le_neg hvu) hu' hf
        (fun t ht => by dsimp only [f]; rw [norm_star]; exact hF _ (hm ht))
      have hflip := intervalIntegral.integral_comp_neg (fun t => F t*K t) (a:=-u) (b:=-v)
      simp only [neg_neg] at hflip
      rw [←hflip]
      have he : (∫ t in (-u)..(-v),F (-t)*K (-t)) = star (∫ t in (-u)..(-v),f t*K t) := by
        change _=starRingEnd ℂ _
        rw [←intervalIntegral.intervalIntegral_conj]
        apply intervalIntegral.integral_congr; intro t _
        change F (-t)*K (-t)=star (star (F (-t))*K t)
        rw [star_mul,star_star,mul_comm,show K (-t)=star (K t) from kernel_neg A B t]
      rw [he,norm_star]
      exact H
    · have H : v=u := le_antisymm hvu (by
        by_contra! hh
        have hx := le_max_right l (min u ((i:ℝ)+1/2))
        change min u ((i:ℝ)+1/2)≤v at hx
        rcases le_total u ((i:ℝ)+1/2) with ho|ho
        · rw [min_eq_left ho] at hx; linarith
        · rw [min_eq_right ho] at hx; linarith)
      simpa only [H,intervalIntegral.integral_same,norm_zero] using hL
  have hfc : ContinuousOn (fun t => F t*K t) (Icc l u) := hc.mul hkc.continuousOn
  rw [←intervalIntegral.integral_add_adjacent_intervals ((hfc.mono (Icc_subset_Icc_right hvu)).intervalIntegrable_of_Icc hlv)
    ((hfc.mono (Icc_subset_Icc_left hlv)).intervalIntegrable_of_Icc hvu)]
  exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by dsimp [L]; ring))

/-- Truncated Poisson summation on `(a,b]` with the original real endpoints.
The derivative hypotheses are imposed on the interval enlarged by less
than one at each end. -/
theorem vanDerCorput_poisson_real {a b : ℝ} (hab : a≤b) {f f' f'' : ℝ→ℝ}
    {α β : ℝ} (hαβ : α≤β)
    (hf : ∀ t∈Icc (⌊a⌋:ℝ) (b+1),HasDerivAt f (f' t) t)
    (hf' : ∀ t∈Icc (⌊a⌋:ℝ) (b+1),HasDerivAt f' (f'' t) t)
    (hc : ContinuousOn f'' (Icc (⌊a⌋:ℝ) (b+1)))
    (hm : (∀ t∈Icc (⌊a⌋:ℝ) (b+1),0≤f'' t) ∨ (∀ t∈Icc (⌊a⌋:ℝ) (b+1),f'' t≤0))
    (hbound : ∀ t∈Icc (⌊a⌋:ℝ) (b+1),α≤f' t ∧ f' t≤β) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,e (f n)) -
      ∑ n ∈ Finset.Icc (⌊α⌋-1) (⌈β⌉+1),∫ t in a..b,e (f t-(n:ℝ)*t)‖ ≤
      96*(1+Real.log (2+(β-α))) := by
  let l := ⌊a⌋
  let u := ⌊b⌋
  let A := ⌊α⌋-2
  let B := ⌈β⌉+1
  let g (t : ℝ) := e (f t)
  let F (t : ℝ) := g t*intervalDirichletKernel A B t
  have hlu : l≤u := Int.floor_le_floor hab
  have hlu' : (l:ℝ)≤u := by exact_mod_cast hlu
  have hla : (l:ℝ)≤a := Int.floor_le _
  have hub : (u:ℝ)≤b := Int.floor_le _
  have H : (Finset.Icc (⌊α⌋-1) (⌈β⌉+1))=Finset.Ioc A B := by
    ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc,A,B]; omega
  have hAB : A<B := by
    have hh : (⌊α⌋:ℝ)≤(⌈β⌉:ℤ) := (Int.floor_le α).trans (hαβ.trans (Int.le_ceil β))
    have : ⌊α⌋≤⌈β⌉ := by exact_mod_cast hh
    dsimp [A,B]; omega
  have hfC : ContinuousOn f (Icc (l:ℝ) (b+1)) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hg : ContinuousOn g (Icc (l:ℝ) (b+1)) := (show Continuous e by unfold e; fun_prop).comp_continuousOn hfC
  have hF : ContinuousOn F (Icc (l:ℝ) (b+1)) := hg.mul (continuous_intervalDirichletKernel A B).continuousOn
  have hInt {x y : ℝ} (hx : (l:ℝ)≤x) (hxy : x≤y) (hy : y≤b+1) : IntervalIntegrable F volume x y :=
    (hF.mono (Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  have hconvert {x y : ℝ} (hx : (l:ℝ)≤x) (hxy : x≤y) (hy : y≤b+1) :
      (∑ n∈Finset.Icc (⌊α⌋-1) (⌈β⌉+1),∫ t in x..y,e (f t-(n:ℝ)*t))=∫ t in x..y,F t := by
    rw [H]
    simpa only [one_mul] using sum_integral_phase_eq (A:=A) (B:=B) (χ:=fun _ => (1:ℂ)) hxy
      (hfC.mono (Icc_subset_Icc hx hy)) continuousOn_const
  have hlog : 0≤Real.log (2+(β-α)) := Real.log_nonneg (by linarith)
  have hp : ‖(∑ n∈Finset.Ioc l u,e (f n)) - ∫ t in (l:ℝ)..(u:ℝ),F t‖ ≤64*(1+Real.log (2+(β-α))) := by
    rcases eq_or_lt_of_le hlu with he|hlt
    · rw [he]; simp; positivity
    · have hs : Icc ((l:ℝ)+1/4) ((u:ℝ)+3/4) ⊆ Icc (l:ℝ) (b+1) :=
        Icc_subset_Icc (by linarith) (by linarith)
      have hv := vanDerCorput_poisson_sharp hlt hαβ
        (hfC.mono (Icc_subset_Icc le_rfl (by linarith : (u:ℝ)+3/4≤b+1)))
        (fun t ht => hf t (hs ht)) (fun t ht => hf' t (hs ht)) (hc.mono hs)
        (hm.imp (fun h t ht => h t (hs ht)) (fun h t ht => h t (hs ht)))
        (fun t ht => hbound t (hs ht))
      rw [←hconvert le_rfl hlu' (by linarith)]
      exact hv
  let L := 8*Real.log (1+((B:ℝ)-A))
  have he (i : ℤ) (x : ℝ) (hi : l ≤ i) (hix : (i:ℝ)≤x) (hi' : x≤(i:ℝ)+1) (hx : x≤b) :
      ‖∫ t in (i:ℝ)..x,F t‖≤L :=
    norm_integral_mul_kernel_unit_le hAB le_rfl hix hi'
      (hg.mono (Icc_subset_Icc (Int.cast_le.mpr hi) (by linarith))) (fun t _ => (norm_e _).le)
  have h₁ := he l a le_rfl hla (Int.lt_floor_add_one a).le hab
  have h₂ := he u b hlu hub (Int.lt_floor_add_one b).le le_rfl
  have hid := (intervalIntegral.integral_add_adjacent_intervals (hInt le_rfl hlu' (by linarith))
    (hInt hlu' hub (by linarith))).trans (intervalIntegral.integral_add_adjacent_intervals
      (hInt le_rfl hla (by linarith)) (hInt hla hab (by linarith))).symm
  have hd : (∫ t in (l:ℝ)..(u:ℝ),F t)-(∫ t in a..b,F t) =
      (∫ t in (l:ℝ)..a,F t)-(∫ t in (u:ℝ)..b,F t) := by linear_combination hid
  rw [hconvert hla hab (by linarith)]
  apply (norm_sub_le_norm_sub_add_norm_sub _ (∫ t in (l:ℝ)..(u:ℝ),F t) _).trans
  rw [hd]
  apply (add_le_add hp ((norm_sub_le _ _).trans (add_le_add h₁ h₂))).trans
  have hcard : 1+((B:ℝ)-A)≤3*(2+(β-α)) := by
    dsimp [A,B]; push_cast; linarith [Int.sub_one_lt_floor α,Int.ceil_lt_add_one β]
  have hN : 0<(B:ℝ)-A := sub_pos.mpr (by exact_mod_cast hAB)
  have hl := Real.log_le_log (by positivity : 0<1+((B:ℝ)-A)) hcard
  rw [Real.log_mul (by norm_num) (by linarith)] at hl
  dsimp only [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))]

end AnalyticNumberTheory.ExponentialSums
