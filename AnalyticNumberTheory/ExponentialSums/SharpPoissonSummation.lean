import AnalyticNumberTheory.ExponentialSums.VanDerCorput
import AnalyticNumberTheory.ExponentialSums.DirichletKernelIntegrals

/-!
# Truncated Poisson summation on a sharp interval

The transition regions of the Poisson cutoff can be removed after summing
over the dual frequencies. The error is controlled by the integral norm
of a single Dirichlet kernel.
-/

open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.ExponentialSums

private theorem kernel_remove_cutoff {A B a b : ℤ} (hAB : A<B) (hab : a<b)
    {g : ℝ→ℂ} (hg : ContinuousOn g (Icc (a:ℝ) ((b:ℝ)+3/4)))
    (hgn : ∀ t∈Icc (a:ℝ) ((b:ℝ)+3/4), ‖g t‖≤1) :
    ‖(∫ t in ((a:ℝ)+1/4)..((b:ℝ)+3/4),
        ((vdcBump a b t:ℂ)*g t)*intervalDirichletKernel A B t) -
      (∫ t in (a:ℝ)..(b:ℝ),g t*intervalDirichletKernel A B t)‖ ≤
      12*Real.log (1+((B:ℝ)-A)) := by
  let U : ℝ := (a:ℝ)+1/4
  let V : ℝ := (a:ℝ)+3/4
  let W : ℝ := (b:ℝ)+3/4
  let χ (t : ℝ) : ℂ := vdcBump a b t
  let F (t : ℝ) := g t*intervalDirichletKernel A B t
  let G (t : ℝ) := (χ t*g t)*intervalDirichletKernel A B t
  let L := 4*Real.log (1+((B:ℝ)-A))
  have hstep : (a:ℝ)+1≤(b:ℝ) := by exact_mod_cast hab
  have haU : (a:ℝ)≤U := by dsimp [U]; linarith
  have hUV : U≤V := by dsimp [U,V]; linarith
  have hVb : V≤(b:ℝ) := by dsimp [V]; linarith
  have hbW : (b:ℝ)≤W := by dsimp [W]; linarith
  have hχ : Continuous χ := Complex.continuous_ofReal.comp (continuous_vdcBump a b)
  have hG₀ : ContinuousOn (fun t => χ t*g t) (Icc (a:ℝ) W) := hχ.continuousOn.mul hg
  have hG₁ (t : ℝ) (ht : t∈Icc (a:ℝ) W) : ‖χ t*g t‖≤1 := by
    have H := vdcBump_mem_unitInterval hab t
    rw [norm_mul,show ‖χ t‖=vdcBump a b t by dsimp [χ]; rw [Complex.norm_real,Real.norm_of_nonneg H.1]]
    exact (mul_le_of_le_one_left (norm_nonneg _) H.2).trans (hgn t ht)
  have hfc : ContinuousOn F (Icc (a:ℝ) W) := hg.mul (continuous_intervalDirichletKernel A B).continuousOn
  have hgc : ContinuousOn G (Icc (a:ℝ) W) := hG₀.mul (continuous_intervalDirichletKernel A B).continuousOn
  have hi {l u : ℝ} (hl : (a:ℝ)≤l) (hlu : l≤u) (hu : u≤W) :
      IntervalIntegrable F volume l u ∧ IntervalIntegrable G volume l u :=
    ⟨(hfc.mono (Icc_subset_Icc hl hu)).intervalIntegrable_of_Icc hlu,
     (hgc.mono (Icc_subset_Icc hl hu)).intervalIntegrable_of_Icc hlu⟩
  have hmid : (∫ t in V..(b:ℝ),G t) = ∫ t in V..(b:ℝ),F t := by
    apply intervalIntegral.integral_congr; intro t ht
    rw [uIcc_of_le hVb] at ht
    have hz := vdcBump_eq_one hab (t:=t) ⟨ht.1,by linarith [ht.2]⟩
    simp only [G,F,χ,hz,Complex.ofReal_one,one_mul]
  have hb₁ : ‖∫ t in U..V,G t‖≤L :=
    norm_integral_mul_intervalDirichletKernel_le hAB haU hUV le_rfl
      (hG₀.mono (Icc_subset_Icc haU (hVb.trans hbW))) (fun t ht => hG₁ t ⟨haU.trans ht.1,ht.2.trans (hVb.trans hbW)⟩)
  have hb₂ : ‖∫ t in (b:ℝ)..W,G t‖≤L :=
    norm_integral_mul_intervalDirichletKernel_le hAB le_rfl hbW le_rfl
      (hG₀.mono (Icc_subset_Icc (haU.trans (hUV.trans hVb)) le_rfl)) (fun t ht => hG₁ t ⟨(haU.trans (hUV.trans hVb)).trans ht.1,ht.2⟩)
  have hb₃ : ‖∫ t in (a:ℝ)..V,F t‖≤L :=
    norm_integral_mul_intervalDirichletKernel_le hAB le_rfl (haU.trans hUV) le_rfl
      (hg.mono (Icc_subset_Icc le_rfl (hVb.trans hbW))) (fun t ht => hgn t ⟨ht.1,ht.2.trans (hVb.trans hbW)⟩)
  change ‖(∫ t in U..W,G t)-(∫ t in (a:ℝ)..(b:ℝ),F t)‖≤_
  rw [←intervalIntegral.integral_add_adjacent_intervals (hi haU (hUV.trans hVb) hbW).2 (hi (haU.trans (hUV.trans hVb)) hbW le_rfl).2,
    ←intervalIntegral.integral_add_adjacent_intervals (hi haU hUV (hVb.trans hbW)).2 (hi (haU.trans hUV) hVb hbW).2,hmid,
    ←intervalIntegral.integral_add_adjacent_intervals (hi le_rfl (haU.trans hUV) (hVb.trans hbW)).1 (hi (haU.trans hUV) hVb hbW).1]
  have hcancel (x y z w : ℂ) : x+y+z-(w+y)=x+z-w := by ring
  rw [hcancel]
  exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    ((add_le_add (add_le_add hb₁ hb₂) hb₃).trans_eq (by dsimp [L]; ring)))

private theorem sum_integral_phase_eq {a b : ℝ} (hab : a≤b) {A B : ℤ} {f : ℝ→ℝ}
    (hf : ContinuousOn f (Icc a b)) {χ : ℝ→ℂ} (hc : ContinuousOn χ (Icc a b)) :
    (∑ n ∈ Finset.Ioc A B, ∫ t in a..b,χ t*e (f t-(n:ℝ)*t)) =
      ∫ t in a..b,(χ t*e (f t))*intervalDirichletKernel A B t := by
  have hE : Continuous e := by unfold e; fun_prop
  have hi (n : ℤ) : ContinuousOn (fun t => χ t*e (f t-(n:ℝ)*t)) (Icc a b) :=
    hc.mul (hE.comp_continuousOn (hf.sub (continuousOn_const.mul continuousOn_id)))
  rw [←intervalIntegral.integral_finsetSum (fun n _ => (hi n).intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr; intro t _
  dsimp only [intervalDirichletKernel]; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  rw [show f t-(n:ℝ)*t = f t+(-t)*(n:ℝ) by ring,e_add,mul_assoc]

/-- Sharp-interval form of the truncated Poisson formula. The outer sum
uses exactly the frequencies from the smoothed formula and the integral
has no weight or transition regions. -/
theorem vanDerCorput_poisson_sharp {a b : ℤ} (hab : a<b) {f f' f'' : ℝ→ℝ}
    {α β : ℝ} (hαβ : α≤β)
    (hc : ContinuousOn f (Icc (a:ℝ) ((b:ℝ)+3/4)))
    (hf : ∀ t∈Icc ((a:ℝ)+1/4) ((b:ℝ)+3/4),HasDerivAt f (f' t) t)
    (hf' : ∀ t∈Icc ((a:ℝ)+1/4) ((b:ℝ)+3/4),HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Icc ((a:ℝ)+1/4) ((b:ℝ)+3/4)))
    (hm : (∀ t∈Icc ((a:ℝ)+1/4) ((b:ℝ)+3/4),0≤f'' t) ∨ (∀ t∈Icc ((a:ℝ)+1/4) ((b:ℝ)+3/4),f'' t≤0))
    (hbound : ∀ t∈Icc ((a:ℝ)+1/4) ((b:ℝ)+3/4),α≤f' t ∧ f' t≤β) :
    ‖(∑ n ∈ Finset.Ioc a b,e (f n)) -
      ∑ n ∈ Finset.Icc (⌊α⌋-1) (⌈β⌉+1),∫ t in (a:ℝ)..(b:ℝ),e (f t-(n:ℝ)*t)‖ ≤
      64*(1+Real.log (2+(β-α))) := by
  let A := ⌊α⌋-2
  let B := ⌈β⌉+1
  have hfl := Int.floor_le α
  have hcl := Int.le_ceil β
  have hAB : A<B := by
    have hh : (⌊α⌋:ℝ)≤(⌈β⌉:ℤ) := hfl.trans (hαβ.trans hcl)
    have : ⌊α⌋≤⌈β⌉ := by exact_mod_cast hh
    dsimp [A,B]; omega
  have hs : Finset.Icc (⌊α⌋-1) (⌈β⌉+1) = Finset.Ioc A B := by
    ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc,A,B]; omega
  have hg : Continuous e := by unfold e; fun_prop
  have habR : (a:ℝ)+1≤(b:ℝ) := by exact_mod_cast hab
  have hU : (a:ℝ)≤(a:ℝ)+1/4 := by linarith
  have hV : (b:ℝ)≤(b:ℝ)+3/4 := by linarith
  let χ (t : ℝ) : ℂ := vdcBump a b t
  have hχ : Continuous χ := Complex.continuous_ofReal.comp (continuous_vdcBump a b)
  have HP := vanDerCorput_B_poisson_reduction hab hαβ hf hf' hf'' hm hbound
  change ‖(∑ n ∈ Finset.Ioc a b,e (f n)) - ∑ n ∈ Finset.Icc (⌊α⌋-1) (⌈β⌉+1),
    ∫ t in ((a:ℝ)+1/4)..((b:ℝ)+3/4),χ t*e (f t-(n:ℝ)*t)‖ ≤ _ at HP
  rw [hs,sum_integral_phase_eq (by linarith) (hc.mono (Icc_subset_Icc hU le_rfl)) hχ.continuousOn] at HP
  have HQ := kernel_remove_cutoff hAB hab (hg.comp_continuousOn hc) (fun t _ => (norm_e _).le)
  have Hsum := sum_integral_phase_eq (A:=A) (B:=B) (χ:=fun _ => (1:ℂ))
    (by linarith : (a:ℝ)≤b) (hc.mono (Icc_subset_Icc le_rfl hV)) continuousOn_const
  simp only [one_mul] at Hsum
  rw [hs,Hsum]
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
  apply (add_le_add HP HQ).trans
  have hcard : 1+((B:ℝ)-A)≤3*(2+(β-α)) := by
    dsimp [A,B]; push_cast
    linarith [Int.sub_one_lt_floor α, Int.ceil_lt_add_one β]
  have hN : 0<(B:ℝ)-A := sub_pos.mpr (by exact_mod_cast hAB)
  have Hlog := Real.log_le_log (by positivity : 0<1+((B:ℝ)-A)) hcard
  rw [Real.log_mul (by norm_num) (by linarith)] at Hlog
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hL := Real.log_nonneg (by linarith : 1≤2+(β-α))
  linarith

end AnalyticNumberTheory.ExponentialSums
