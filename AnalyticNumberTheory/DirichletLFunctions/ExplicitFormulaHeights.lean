import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaDisks

/-!
# Horizontal contours avoiding Dirichlet zeros

One ordinate in every unit interval avoids the absolute ordinates of all
critical-strip zeros. Both horizontal sides of a symmetric Perron contour
therefore satisfy the same logarithmic derivative estimate.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.DirichletLFunctions

private theorem exists_interval_gap {ι : Type*} (S : Finset ι) (f : ι → ℝ) {a b : ℝ} (hab : a<b) :
    ∃ t ∈ Set.Icc a b, ∀ z∈S, (b-a)/(2*((S.card:ℝ)+1))≤|t-f z| := by
  classical
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let g (n : ℕ) : ℝ := if h : n<S.card then f (e.symm ⟨n,h⟩)-a+(b-a) else 0
  obtain ⟨r,hr,H⟩ := exists_radius_mem_Icc_avoiding (range S.card) g (sub_pos.mpr hab)
  refine ⟨r+a-(b-a),⟨by linarith [hr.1],by linarith [hr.2]⟩,?_⟩
  intro z hz
  let j := e ⟨z,hz⟩
  have h := H j.val (mem_range.mpr j.isLt)
  have hj : g j.val=f z-a+(b-a) := by simp [g,j.isLt,j]
  rw [card_range,hj] at h
  simpa only [show r+a-(b-a)-f z=r-(f z-a+(b-a)) by ring] using h

/-- One height in the middle half of every unit interval avoids the ordinates
of zeros on both sides of the real axis, uniformly in the character. -/
theorem exists_LFunction_good_height {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {A : ℝ} (hA : 0≤A) :
    let L := 1+Real.log ((q:ℝ)*(A+3))
    let δ := 1/(4*(2*jensenUnitZeroDensityConst+1)*L)
    ∃ T ∈ Set.Icc (A+1/4) (A+3/4), ∀ z : ℂ, 0<z.re → z.re<1 → χ.LFunction z=0 →
      δ ≤ abs (T - |z.im|) := by
  classical
  let L := 1+Real.log ((q:ℝ)*(A+3))
  let Zp := criticalStripZeroFinset χ A (A+1)
  let Zm := criticalStripZeroFinset χ (-(A+1)) (-A)
  let Z := Zp ∪ Zm
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hq0 : 0<(q:ℝ) := by linarith
  have hL : 1≤L := by
    apply le_add_of_nonneg_right
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le hq (by linarith)
  have hJ := jensenUnitZeroDensityConst_pos
  have hP : (Zp.card:ℝ)≤jensenUnitZeroDensityConst*L := by
    apply (finset_card_zeros_unit_interval_le hχ A (fun z hz => (mem_criticalStripZeroFinset χ).mp hz)).trans
    rw [abs_of_nonneg hA]
    have hlog := Real.log_le_log (show 0<(q:ℝ)*(A+2) by positivity)
      (mul_le_mul_of_nonneg_left (by linarith : A+2≤A+3) hq0.le)
    apply mul_le_mul_of_nonneg_left _ hJ.le; dsimp [L]; linarith
  have hM : (Zm.card:ℝ)≤jensenUnitZeroDensityConst*L := by
    apply (finset_card_zeros_unit_interval_le hχ (-(A+1)) (S:=Zm) (fun z hz => by
      obtain ⟨hr,hr',hi,hi',hf⟩ := (mem_criticalStripZeroFinset χ).mp hz
      exact ⟨hr,hr',hi,by linarith,hf⟩)).trans
    rw [abs_neg,abs_of_nonneg (by linarith : 0≤A+1),show A+1+2=A+3 by ring]
    apply mul_le_mul_of_nonneg_left _ hJ.le
    dsimp [L]; linarith
  have hcard : (Z.card:ℝ)≤2*jensenUnitZeroDensityConst*L := by
    have hu : (Z.card:ℝ)≤(Zp.card:ℝ)+(Zm.card:ℝ) := by exact_mod_cast card_union_le Zp Zm
    linarith
  have hLp : 0<L := by linarith
  have hD : 0<2*jensenUnitZeroDensityConst+1 := by linarith
  have hgap : 1/(4*(2*jensenUnitZeroDensityConst+1)*L)≤
      (A+3/4-(A+1/4))/(2*((Z.card:ℝ)+1)) := by
    rw [show A+3/4-(A+1/4)=(1/2:ℝ) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  obtain ⟨T,hT,H⟩ := exists_interval_gap Z (fun z : ℂ => |z.im|) (a:=A+1/4) (b:=A+3/4) (by linarith)
  refine ⟨T,hT,?_⟩
  intro z hr hr' hf
  by_cases hz : z∈Z
  · exact hgap.trans (H z hz)
  have ho : abs z.im < A ∨ A+1 < abs z.im := by
    by_contra! hb
    apply hz
    apply mem_union.mpr
    rcases le_or_gt 0 z.im with hp|hm
    · rw [abs_of_nonneg hp] at hb
      exact .inl ((mem_criticalStripZeroFinset χ).mpr ⟨hr,hr',hb.1,hb.2,hf⟩)
    · rw [abs_of_neg hm] at hb
      exact .inr ((mem_criticalStripZeroFinset χ).mpr ⟨hr,hr',by linarith [hb.2],by linarith [hb.1],hf⟩)
  have hδ : 1/(4*(2*jensenUnitZeroDensityConst+1)*L)≤1/4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h := le_mul_of_one_le_right hD.le hL
    linarith
  apply hδ.trans
  rcases ho with hl|hu
  · linarith [hT.1,le_abs_self (T-|z.im|)]
  · linarith [hT.2,neg_abs_le (T-|z.im|)]

/-- A gap of size `δ` from the zero ordinates gives a quadratic-log bound
for the ordinary logarithmic derivative on the entire horizontal segment. -/
theorem norm_logDeriv_on_separated_horizontal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t σ δ : ℝ} (hδ : 0<δ) (hσ : 3/8≤σ) (hσ' : σ≤3/2)
    (hgap : ∀ z : ℂ, 0<z.re → z.re<1 → χ.LFunction z=0 → δ≤|t-z.im|) :
    χ.LFunction ((σ:ℂ)+(t:ℂ)*I)≠0 ∧
    ‖logDeriv χ.LFunction ((σ:ℂ)+(t:ℂ)*I)‖ ≤
      (10304+14/(Real.log 2*δ))*Real.log ((q:ℝ)*(|t|+2)) := by
  have hsR : ((σ:ℂ)+(t:ℂ)*I).re=σ := by simp
  have hsI : ((σ:ℂ)+(t:ℂ)*I).im=t := by simp
  have hn : χ.LFunction ((σ:ℂ)+(t:ℂ)*I)≠0 := by
    intro hz
    by_cases h : 1≤σ
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by rw [hsR]; exact h) hz
    · have hg := hgap _ (by rw [hsR]; linarith) (by rw [hsR]; linarith) hz
      rw [hsI,sub_self,abs_zero] at hg
      linarith
  refine ⟨hn,?_⟩
  obtain ⟨Z,_,hsub,hcount,HE⟩ := explicitFormula_local_logDeriv hχ t
  let s := (σ:ℂ)+(t:ℂ)*I
  let L := Real.log ((q:ℝ)*(|t|+2))
  let P := ∑z∈Z,(analyticOrderNatAt χ.LFunction z:ℂ)/(s-z)
  have hp : ‖P‖≤14*L/Real.log 2/δ := by
    calc
      _ ≤ ∑z∈Z,‖(analyticOrderNatAt χ.LFunction z:ℂ)/(s-z)‖ := norm_sum_le _ _
      _ ≤ ∑z∈Z,(analyticOrderNatAt χ.LFunction z:ℝ)/δ := by
        refine sum_le_sum fun z hz => ?_
        obtain ⟨hr,hr',_,_,hf⟩ := (mem_criticalStripZeroFinset χ).mp (hsub hz)
        have hd : δ≤‖s-z‖ := (hgap z hr hr' hf).trans (by simpa [s] using Complex.abs_im_le_norm (s-z))
        rw [norm_div,Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hd
      _ ≤ _ := by rw [←sum_div]; exact div_le_div_of_nonneg_right hcount hδ.le
  have hE : ‖logDeriv χ.LFunction s-P‖≤10304*L := HE σ hσ hσ' hn
  calc
    _ ≤ ‖logDeriv χ.LFunction s-P‖+‖P‖ := norm_le_norm_sub_add _ _
    _ ≤ 10304*L+14*L/Real.log 2/δ := add_le_add hE hp
    _ = _ := by dsimp [L]; ring

end AnalyticNumberTheory.DirichletLFunctions
