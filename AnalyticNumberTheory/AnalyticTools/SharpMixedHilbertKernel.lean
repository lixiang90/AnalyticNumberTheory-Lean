import AnalyticNumberTheory.AnalyticTools.HilbertKernelEstimates
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The mixed Hilbert kernel at two separated poles

The mixed quadratic row estimate uses disjoint intervals centered at the points.
A symmetric interval average dominates the value of the kernel at its midpoint.
An antiderivative controls the total contribution outside the two omitted cells.
-/

noncomputable section

open Real Set MeasureTheory Filter Finset
open scoped Topology Interval

namespace AnalyticNumberTheory.AnalyticTools

private def mixedKernel (a b x : ℝ) := 1 / ((x-a)^2 * (x-b)^2)

private def mixedPrimitive (a b x : ℝ) :=
  -1/(x-a) - 1/(x-b) - 2/(b-a) * (Real.log (x-b) - Real.log (x-a))

private theorem mixedPrimitive_deriv {a b x : ℝ} (hab : a < b) (ha : x ≠ a) (hb : x ≠ b) :
    HasDerivAt (mixedPrimitive a b) ((b-a)^2 * mixedKernel a b x) x := by
  have A := (hasDerivAt_id x).sub_const a
  have B := (hasDerivAt_id x).sub_const b
  change HasDerivAt (fun y : ℝ => y-a) 1 x at A
  change HasDerivAt (fun y : ℝ => y-b) 1 x at B
  have na := sub_ne_zero.mpr ha
  have nb := sub_ne_zero.mpr hb
  have h := (((A.inv na).neg.sub (B.inv nb)).sub
    (((B.log nb).sub (A.log na)).const_mul (2/(b-a))))
  convert h using 1
  · ext y
    simp [mixedPrimitive, one_div, neg_div]
  · dsimp [mixedKernel]
    field_simp [na, nb, sub_ne_zero.mpr hab.ne']
    <;> ring

private theorem mixed_midpoint {A B v : ℝ} (hv : 0 ≤ v) (ha : v < |A|) (hb : v < |B|) :
    2 / (A^2 * B^2) ≤ 1 / ((A-v)^2*(B-v)^2) + 1 / ((A+v)^2*(B+v)^2) := by
  have qa : 0 < A^2-v^2 := by nlinarith [sq_abs A, mul_pos (sub_pos.mpr ha) (by linarith : 0 < |A|+v)]
  have qb : 0 < B^2-v^2 := by nlinarith [sq_abs B, mul_pos (sub_pos.mpr hb) (by linarith : 0 < |B|+v)]
  let u := (|A-v| * |B-v|)⁻¹
  let w := (|A+v| * |B+v|)⁻¹
  have hw : (A^2*B^2)⁻¹ ≤ u*w := by
    dsimp [u,w]
    rw [← mul_inv, show |A-v| * |B-v| * (|A+v| * |B+v|) =
      (A^2-v^2)*(B^2-v^2) by
        rw [mul_mul_mul_comm, ← abs_mul, ← abs_mul, show (A-v)*(A+v)=A^2-v^2 by ring, show (B-v)*(B+v)=B^2-v^2 by ring,
          abs_of_pos qa, abs_of_pos qb] ]
    exact inv_anti₀ (mul_pos qa qb) (mul_le_mul (by linarith [sq_nonneg v])
      (by linarith [sq_nonneg v]) qb.le (sq_nonneg A))
  have hu : u^2 = 1/((A-v)^2*(B-v)^2) := by simp [u, one_div, mul_pow]
  have hw' : w^2 = 1/((A+v)^2*(B+v)^2) := by simp [w, one_div, mul_pow]
  rw [← hu, ← hw', div_eq_mul_inv]
  nlinarith only [sq_nonneg (u-w), hw]

private theorem mixed_mono {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hd : ∀ y ∈ D, HasDerivAt f (f' y) y) (hn : ∀ y ∈ D, 0 ≤ f' y) : MonotoneOn f D :=
  monotoneOn_of_hasDerivWithinAt_nonneg hD (HasDerivAt.continuousOn hd)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hn y (interior_subset hy))

private theorem mixed_cell {a b x h : ℝ} (hab : a < b) (hh : 0 < h)
    (ha : 2*h ≤ |x-a|) (hb : 2*h ≤ |x-b|) :
    2*h * ((b-a)^2*mixedKernel a b x) ≤ mixedPrimitive a b (x+h)-mixedPrimitive a b (x-h) := by
  let f := fun v => mixedPrimitive a b (x+v) - mixedPrimitive a b (x-v)
    - (2*((b-a)^2*mixedKernel a b x))*v
  let f' := fun v => (b-a)^2*mixedKernel a b (x+v) + (b-a)^2*mixedKernel a b (x-v)
    - 2*((b-a)^2*mixedKernel a b x)
  have off (c : ℝ) (hc : 2*h ≤ |x-c|) {v : ℝ} (hv : v ∈ Icc 0 h) :
      x+v ≠ c ∧ x-v ≠ c := by
    have hav : v < |x-c| := by linarith [hv.2]
    constructor
    · intro he
      rw [show x-c = -v by linarith, abs_neg, abs_of_nonneg hv.1] at hav
      exact lt_irrefl _ hav
    · intro he
      rw [show x-c = v by linarith, abs_of_nonneg hv.1] at hav
      exact lt_irrefl _ hav
  have hd (v : ℝ) (hv : v ∈ Icc 0 h) : HasDerivAt f (f' v) v := by
    have A := (mixedPrimitive_deriv hab (off a ha hv).1 (off b hb hv).1).comp v
      ((hasDerivAt_id v).const_add x)
    have B := (mixedPrimitive_deriv hab (off a ha hv).2 (off b hb hv).2).comp v
      ((hasDerivAt_id v).const_sub x)
    have E := (A.sub B).sub ((hasDerivAt_id v).const_mul (2*((b-a)^2*mixedKernel a b x)))
    convert E using 1
    · rfl
    · dsimp [f']; ring
  have H := mixed_mono (convex_Icc 0 h) hd (fun v hv => by
    have hs := mixed_midpoint hv.1 (show v < |x-a| by linarith [hv.2])
      (show v < |x-b| by linarith [hv.2])
    have H : 2*mixedKernel a b x ≤ mixedKernel a b (x-v)+mixedKernel a b (x+v) := by
      simpa only [mixedKernel, show x-v-a=x-a-v by ring, show x-v-b=x-b-v by ring,
        show x+v-a=x-a+v by ring, show x+v-b=x-b+v by ring, mul_one_div] using hs
    dsimp [f']
    nlinarith only [mul_nonneg (sq_nonneg (b-a)) (sub_nonneg.mpr H)])
  have H' := H (left_mem_Icc.mpr hh.le) (right_mem_Icc.mpr hh.le) hh.le
  dsimp [f] at H'
  simp only [add_zero, sub_zero, sub_self, mul_zero] at H'
  linarith
private theorem mixed_limit {l : Filter ℝ} (a b : ℝ)
    (hi : ∀ c : ℝ, Tendsto (fun x : ℝ => (x-c)⁻¹) l (𝓝 0))
    (he : ∀ c : ℝ, ∀ᶠ x in l, x ≠ c) : Tendsto (mixedPrimitive a b) l (𝓝 0) := by
  have hr : Tendsto (fun x : ℝ => 1+(a-b)*(x-a)⁻¹) l (𝓝 1) := by
    simpa using ((hi a).const_mul (a-b)).const_add 1
  have hl : Tendsto (fun x : ℝ => Real.log (x-b)-Real.log (x-a)) l (𝓝 0) := by
    have hk := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hr
    apply (show Tendsto (fun x : ℝ => Real.log (1+(a-b)*(x-a)⁻¹)) l (𝓝 0) by simpa [Function.comp_def] using hk).congr'
    filter_upwards [he a, he b] with x hxa hxb
    rw [← Real.log_div (sub_ne_zero.mpr hxb) (sub_ne_zero.mpr hxa)]
    congr 1
    field_simp [sub_ne_zero.mpr hxa]
    ring
  change Tendsto (fun x => -1/(x-a)-1/(x-b)-2/(b-a)*(Real.log (x-b)-Real.log (x-a))) l (𝓝 0)
  simpa [div_eq_mul_inv] using
    (((hi a).neg.sub (hi b)).sub (hl.const_mul (2/(b-a))))

private theorem mixed_pole_mono {a b : ℝ} (hab : a < b) {D : Set ℝ} (hD : Convex ℝ D)
    (hn : ∀ y ∈ D, y ≠ a ∧ y ≠ b) : MonotoneOn (mixedPrimitive a b) D :=
  mixed_mono hD (fun y hy => mixedPrimitive_deriv hab (hn y hy).1 (hn y hy).2)
    (fun y _ => by unfold mixedKernel; positivity)

private theorem mixed_outer_sign {a b x : ℝ} (hab : a < b) :
    (x<a → 0≤mixedPrimitive a b x) ∧ (b<x → mixedPrimitive a b x≤0) := by
  constructor
  · intro hx
    have hm := mixed_pole_mono hab (convex_Iic x) (fun y hy => by
      change y ≤ x at hy
      exact ⟨by linarith, by linarith⟩)
    have ht := mixed_limit (l:=atBot) a b (fun c =>
      tendsto_inv_atBot_zero.comp (tendsto_atBot_add_const_right _ (-c) tendsto_id))
      (fun c => (eventually_lt_atBot c).mono fun _ h => h.ne)
    exact le_of_tendsto ht ((eventually_le_atBot x).mono fun y hy => hm hy Set.self_mem_Iic hy)
  · intro hx
    have hm := mixed_pole_mono hab (convex_Ici x) (fun y hy => by
      change x ≤ y at hy
      exact ⟨by linarith, by linarith⟩)
    have ht := mixed_limit (l:=atTop) a b (fun c =>
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-c) tendsto_id))
      (fun c => (eventually_gt_atTop c).mono fun _ h => h.ne')
    exact ge_of_tendsto ht ((eventually_ge_atTop x).mono fun y hy => hm Set.self_mem_Ici hy hy)

private theorem mixed_packing {ι : Type*} (S : Finset ι) (l r : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hl : ∀ i ∈ S, 0 ≤ l i) (hr : ∀ i ∈ S, r i ≤ M) (hlr : ∀ i ∈ S, l i ≤ r i)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r i ≤ l j ∨ r j ≤ l i) :
    ∑ i ∈ S, (r i-l i) ≤ M := by
  let U := fun i => Ioc (l i) (r i)
  have hdis : PairwiseDisjoint (↑S) U := by
    intro i hi j hj hij
    rcases hd i hi j hj hij with hij|hji
    · exact Set.disjoint_left.mpr fun y hyi hyj => (not_lt_of_ge (hyi.2.trans hij)) hyj.1
    · exact Set.disjoint_left.mpr fun y hyi hyj => (not_lt_of_ge (hyj.2.trans hji)) hyi.1
  have hsub : (⋃ i ∈ S, U i) ⊆ Ioc 0 M := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨i, hi, hy⟩ := hy
    exact ⟨(hl i hi).trans_lt hy.1, hy.2.trans (hr i hi)⟩
  have H := measureReal_mono (μ:=volume) hsub (by simp [Real.volume_Ioc])
  rw [measureReal_biUnion_finset hdis (fun _ _ => measurableSet_Ioc) (by intros; simp [U, Real.volume_Ioc]),
    Real.volume_real_Ioc_of_le hM, sub_zero] at H
  exact (Finset.sum_congr rfl fun i hi => (Real.volume_real_Ioc_of_le (hlr i hi)).symm).le.trans H
private theorem mixed_jump {a b h k : ℝ} (hh : 0<h) (hk : 0<k)
    (ha : 2*h ≤ b-a) (hb : 2*k ≤ b-a) :
    mixedPrimitive a b (a-h) - mixedPrimitive a b (a+h) ≤ 2/h ∧
    mixedPrimitive a b (b-k) - mixedPrimitive a b (b+k) ≤ 2/k := by
  have hd : 0 < b-a := by linarith
  have hc : 0 ≤ 2/(b-a) := by positivity
  constructor
  · have hm : 1/(b-a+h) ≤ 1/(b-a-h) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hlog : Real.log (b-a-h) ≤ Real.log (b-a+h) :=
      Real.log_le_log (by linarith) (by linarith)
    simp only [mixedPrimitive, show a-h-a = -h by ring, show a+h-a=h by ring,
      show a-h-b = -(b-a+h) by ring, show a+h-b = -(b-a-h) by ring,
      Real.log_neg_eq_log, div_neg]
    have hmul := mul_le_mul_of_nonneg_left hlog hc
    simp only [div_eq_mul_inv, one_mul, neg_mul, neg_one_mul] at hm hmul ⊢
    nlinarith only [hm, hmul]
  · have hm : 1/(b-a+k) ≤ 1/(b-a-k) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hlog : Real.log (b-a-k) ≤ Real.log (b-a+k) :=
      Real.log_le_log (by linarith) (by linarith)
    simp only [mixedPrimitive, show b-k-b = -k by ring, show b+k-b=k by ring,
      show b-k-a = b-a-k by ring, show b+k-a = b-a+k by ring,
      Real.log_neg_eq_log, div_neg]
    have hmul := mul_le_mul_of_nonneg_left hlog hc
    simp only [div_eq_mul_inv, one_mul, neg_mul, neg_one_mul] at hm hmul ⊢
    nlinarith only [hm, hmul]

/-- Cumulative primitive after deleting the two cells around the poles. -/
private def mixedCumulative (a b h k x : ℝ) :=
  mixedPrimitive a b (min x (a-h)) +
    (mixedPrimitive a b (max (a+h) (min x (b-k))) - mixedPrimitive a b (a+h)) +
    (mixedPrimitive a b (max x (b+k)) - mixedPrimitive a b (b+k))

private theorem mixed_cumulative_mono {a b h k : ℝ} (hh : 0<h) (hk : 0<k)
    (hm : a+h ≤ b-k) : Monotone (mixedCumulative a b h k) := by
  have hab : a<b := by linarith
  have h₁ := mixed_pole_mono hab (convex_Iic (a-h)) (fun y hy => by
    change y ≤ a-h at hy
    exact ⟨by linarith, by linarith⟩)
  have h₂ := mixed_pole_mono hab (convex_Icc (a+h) (b-k)) (fun y hy =>
    ⟨ne_of_gt (by linarith [hy.1]), ne_of_lt (by linarith [hy.2])⟩)
  have h₃ := mixed_pole_mono hab (convex_Ici (b+k)) (fun y hy => by
    change b+k ≤ y at hy
    exact ⟨by linarith, by linarith⟩)
  intro x y hxy
  apply add_le_add
  · apply add_le_add
    · exact h₁ (show min x (a-h) ≤ a-h from min_le_right ..) (show min y (a-h) ≤ a-h from min_le_right ..) (min_le_min_right _ hxy)
    · apply sub_le_sub_right
      apply h₂
      · exact ⟨le_max_left .., max_le hm (min_le_right ..)⟩
      · exact ⟨le_max_left .., max_le hm (min_le_right ..)⟩
      · exact max_le_max_left _ (min_le_min_right _ hxy)
  · apply sub_le_sub_right
    exact h₃ (show b+k ≤ max x (b+k) from le_max_right ..) (show b+k ≤ max y (b+k) from le_max_right ..) (max_le_max_right _ hxy)

private theorem mixed_cumulative_bounds {a b h k : ℝ} (hh : 0<h) (hk : 0<k)
    (ha : 2*h ≤ b-a) (hb : 2*k ≤ b-a) (x : ℝ) :
    0 ≤ mixedCumulative a b h k x ∧ mixedCumulative a b h k x ≤ 2/h+2/k := by
  have hm : a+h ≤ b-k := by linarith
  have hab : a<b := by linarith
  have mon := mixed_cumulative_mono hh hk hm
  let l := min x (a-h)
  let r := max x (b+k)
  have hl : l ≤ a-h := min_le_right ..
  have hr : b+k ≤ r := le_max_right ..
  have hlow : mixedCumulative a b h k l = mixedPrimitive a b l := by
    simp [mixedCumulative, min_eq_left hl,
      min_eq_left (show l ≤ b-k by linarith), max_eq_left (show l ≤ a+h by linarith),
      max_eq_right (show l ≤ b+k by linarith)]
  have hhigh : mixedCumulative a b h k r = mixedPrimitive a b (a-h) +
      (mixedPrimitive a b (b-k)-mixedPrimitive a b (a+h)) +
      (mixedPrimitive a b r - mixedPrimitive a b (b+k)) := by
    rw [mixedCumulative, min_eq_right (show a-h≤r by linarith),
      min_eq_right (show b-k≤r by linarith), max_eq_right hm, max_eq_left hr]
  constructor
  · have H := mon (show l≤x from min_le_left ..)
    rw [hlow] at H
    exact ((mixed_outer_sign hab).1 (show l<a by linarith)).trans H
  · have H := mon (show x≤r from le_max_left ..)
    rw [hhigh] at H
    obtain ⟨H₁,H₂⟩ := mixed_jump hh hk ha hb
    have H₃ := (mixed_outer_sign hab).2 (show b<r by linarith)
    linarith
private theorem mixed_cumulative_diff {a b h k l r : ℝ} (hh : 0<h) (hk : 0<k)
    (hm : a+h ≤ b-k) (hlr : l≤r)
    (H : r≤a-h ∨ (a+h≤l ∧ r≤b-k) ∨ b+k≤l) :
    mixedCumulative a b h k r - mixedCumulative a b h k l =
      mixedPrimitive a b r - mixedPrimitive a b l := by
  rcases H with H|⟨H,J⟩|H
  · have E (x : ℝ) (hx : x≤r) : mixedCumulative a b h k x = mixedPrimitive a b x := by
      simp only [mixedCumulative, min_eq_left (hx.trans H), min_eq_left (show x≤b-k by linarith),
        max_eq_left (show x≤a+h by linarith), max_eq_right (show x≤b+k by linarith),
        sub_self, add_zero]
    rw [E r le_rfl,E l hlr]
  · have E (x : ℝ) (hx : x ∈ Icc l r) : mixedCumulative a b h k x =
        mixedPrimitive a b (a-h) + (mixedPrimitive a b x - mixedPrimitive a b (a+h)) := by
      simp only [mixedCumulative, min_eq_right (show a-h≤x by linarith [hx.1]),
        min_eq_left (hx.2.trans J), max_eq_right (H.trans hx.1),
        max_eq_right (show x≤b+k by linarith [hx.2]), sub_self, add_zero]
    rw [E r (right_mem_Icc.mpr hlr), E l (left_mem_Icc.mpr hlr)]
    ring
  · have E (x : ℝ) (hx : l≤x) : mixedCumulative a b h k x =
        mixedPrimitive a b (a-h) + (mixedPrimitive a b (b-k)-mixedPrimitive a b (a+h))
          + (mixedPrimitive a b x-mixedPrimitive a b (b+k)) := by
      simp only [mixedCumulative, min_eq_right (show a-h≤x by linarith),
        min_eq_right (show b-k≤x by linarith), max_eq_right hm, max_eq_left (H.trans hx)]
    rw [E r hlr, E l le_rfl]
    ring

private theorem mixed_ordered_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i≠j → δ i ≤ |x i-x j|) {s t : ι} (hst : x s < x t) :
    (∑ i, δ i/((x i-x s)^2*(x i-x t)^2)) ≤
      4*(1/δ s+1/δ t)/(x s-x t)^2 := by
  let L := fun i => x i - δ i/2
  let R := fun i => x i + δ i/2
  have h₀ (i : ι) : L i ≤ R i := by dsimp [L,R]; linarith [hδ i]
  have sep {i j : ι} (hij : x i < x j) : R i ≤ L j := by
    have hn : i ≠ j := fun e => hij.ne (congrArg x e)
    have A := hsep i j hn
    have B := hsep j i hn.symm
    rw [abs_of_neg (sub_neg.mpr hij)] at A
    rw [abs_of_pos (sub_pos.mpr hij)] at B
    dsimp [L,R]
    linarith
  have inj {i j : ι} (hij : i ≠ j) : x i ≠ x j := by
    intro e
    have h := hsep i j hij
    rw [e, sub_self, abs_zero] at h
    exact (not_lt_of_ge h) (hδ i)
  have hn : s ≠ t := fun e => hst.ne (congrArg x e)
  have ha := hsep s t hn
  have hb := hsep t s hn.symm
  rw [abs_of_neg (sub_neg.mpr hst)] at ha
  rw [abs_of_pos (sub_pos.mpr hst)] at hb
  let F := mixedCumulative (x s) (x t) (δ s/2) (δ t/2)
  have hs : 0 < δ s/2 := half_pos (hδ s)
  have ht : 0 < δ t/2 := half_pos (hδ t)
  have hst' : x s+δ s/2 ≤ x t-δ t/2 := sep hst
  have hmono : Monotone F := mixed_cumulative_mono hs ht hst'
  have HB (y : ℝ) : 0 ≤ F y ∧ F y ≤ 2/(δ s/2)+2/(δ t/2) :=
    mixed_cumulative_bounds hs ht (by linarith) (by linarith) y
  have pack := mixed_packing (Finset.univ : Finset ι) (fun i => F (L i)) (fun i => F (R i))
    (show 0≤2/(δ s/2)+2/(δ t/2) by positivity) (fun i _ => (HB _).1)
    (fun i _ => (HB _).2) (fun i _ => hmono (h₀ i)) (fun i _ j _ hij => by
      rcases lt_or_gt_of_ne (inj hij) with h|h
      · exact .inl (hmono (sep h))
      · exact .inr (hmono (sep h)))
  have H (i : ι) : (x t-x s)^2 * (δ i/((x i-x s)^2*(x i-x t)^2)) ≤ F (R i)-F (L i) := by
    by_cases his : i = s
    · subst i
      simpa using sub_nonneg.mpr (hmono (h₀ s))
    by_cases hit : i = t
    · subst i
      simpa using sub_nonneg.mpr (hmono (h₀ t))
    have hc := mixed_cell (x:=x i) hst (half_pos (hδ i))
      (by linarith [hsep i s his]) (by linarith [hsep i t hit])
    have he : F (R i)-F (L i) = mixedPrimitive (x s) (x t) (R i) -
        mixedPrimitive (x s) (x t) (L i) := by
      apply mixed_cumulative_diff hs ht hst' (h₀ i)
      rcases lt_or_gt_of_ne (inj his) with hi|hi
      · exact .inl (sep hi)
      rcases lt_or_gt_of_ne (inj hit) with hj|hj
      · exact .inr (.inl ⟨sep hi, sep hj⟩)
      · exact .inr (.inr (sep hj))
    rw [he]
    convert hc using 1 <;> dsimp [mixedKernel,L,R] <;> ring
  have H' := (Finset.sum_le_sum (s:=Finset.univ) fun i _ => H i).trans pack
  rw [← Finset.mul_sum] at H'
  apply (le_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hst.ne))).2
  convert H' using 1 <;> ring

/-- The mixed Hilbert kernel row estimate with coefficient four for nonuniform gaps. -/
theorem hilbert_mixed_quadratic_row_sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i≠j → δ i ≤ |x i-x j|) {s t : ι} (hst : s≠t) :
    (∑ i, δ i/((x i-x s)^2*(x i-x t)^2)) ≤
      4*(1/δ s+1/δ t)/(x s-x t)^2 := by
  rcases lt_trichotomy (x s) (x t) with h|h|h
  · exact mixed_ordered_row x δ hδ hsep h
  · have H := hsep s t hst
    rw [h, sub_self, abs_zero] at H
    exact False.elim ((not_lt_of_ge H) (hδ s))
  · calc
      _ = ∑ i, δ i/((x i-x t)^2*(x i-x s)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_comm]
      _ ≤ _ := mixed_ordered_row x δ hδ hsep h
      _ = _ := by rw [add_comm (1/δ t), show (x t-x s)^2=(x s-x t)^2 by ring]
end AnalyticNumberTheory.AnalyticTools
