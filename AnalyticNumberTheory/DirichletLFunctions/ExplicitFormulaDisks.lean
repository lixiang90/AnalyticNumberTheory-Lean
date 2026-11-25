import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion
import AnalyticNumberTheory.DirichletLFunctions.ZeroExpansion

/-!
# Local partial fractions for a character explicit formula

The disk centered at `17/16+it` reaches strictly to the left of the critical
line while its half-radius disk contains only nontrivial zeros. The growth
estimate, the local zero count and the remainder are uniform in the conductor.
-/

noncomputable section

open Complex Metric Finset MeromorphicOn
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletLFunctions

private theorem explicitFormula_disk_growth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    let c := (17/16:ℂ)+(t:ℂ)*I
    ∀ w ∈ sphere c (3/2),
      ‖χ.LFunction w / χ.LFunction c‖ ≤ 4096*((q:ℝ)*(|t|+2))^2 := by
  let c := (17/16:ℂ)+(t:ℂ)*I
  change ∀ w ∈ sphere c (3/2), _
  have hcr : c.re=17/16 := by norm_num [c]
  have hci : c.im=t := by norm_num [c]
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hQ : 2≤(q:ℝ)*(|t|+2) := by
    nlinarith [abs_nonneg t,mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hinv := norm_inv_LFunction_le_one_add_inv χ (s:=c) (by rw [hcr]; norm_num)
  rw [hcr] at hinv
  norm_num at hinv
  intro w hw
  have hd : ‖w-c‖=3/2 := by simpa only [mem_sphere,dist_eq_norm] using hw
  have hr := Complex.abs_re_le_norm (w-c)
  have hi := Complex.abs_im_le_norm (w-c)
  rw [sub_re,hcr,hd] at hr
  rw [sub_im,hci,hd] at hi
  have hi' : |w.im|+2 ≤ 2*(|t|+2) := by
    linarith [abs_sub_abs_le_abs_sub w.im t,abs_nonneg t]
  have hnum : ‖χ.LFunction w‖ ≤ 196*((q:ℝ)*(|t|+2))^2 := by
    by_cases hw2 : w.re≤2
    · apply (norm_LFunction_strip_poly_le hχ (by linarith [(abs_le.mp hr).1]) hw2).trans
      calc
        _ ≤ (49*(q:ℝ)^2)*(2*(|t|+2))^2 := by gcongr; nlinarith [sq_nonneg ((q:ℝ)-1)]
        _ = _ := by ring
    · have h := norm_LFunction_le_one_add_inv χ (s:=w) (by linarith)
      have hrec : 1/(w.re-1)≤1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
      have hs : 4≤((q:ℝ)*(|t|+2))^2 := by nlinarith [sq_nonneg ((q:ℝ)*(|t|+2)-2)]
      linarith
  change ‖χ.LFunction w/χ.LFunction c‖ ≤ _
  rw [norm_div,div_eq_mul_inv]
  calc
    _ ≤ (196*((q:ℝ)*(|t|+2))^2)*17 := mul_le_mul hnum hinv (by positivity) (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg ((q:ℝ)*(|t|+2))]

/-- Local partial fractions on the horizontal segment from `3/8+it` to
`3/2+it`. The same disk supplies all the zeros and their multiplicities. -/
theorem explicitFormula_local_logDeriv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ∃ Z : Finset ℂ,
      (Z:Set ℂ)=zeroSet χ.LFunction ((17/16:ℂ)+(t:ℂ)*I) (3/4) ∧
      Z ⊆ criticalStripZeroFinset χ (t-1) (t+1) ∧
      (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z:ℝ)) ≤
        14 * Real.log ((q:ℝ)*(|t|+2)) / Real.log 2 ∧
      ∀ σ : ℝ, 3/8≤σ → σ≤3/2 → χ.LFunction ((σ:ℂ)+(t:ℂ)*I)≠0 →
        ‖logDeriv χ.LFunction ((σ:ℂ)+(t:ℂ)*I) -
          ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z:ℂ)/(((σ:ℂ)+(t:ℂ)*I)-z)‖ ≤
          10304 * Real.log ((q:ℝ)*(|t|+2)) := by
  classical
  let c := (17/16:ℂ)+(t:ℂ)*I
  let Q := (q:ℝ)*(|t|+2)
  have hcr : c.re=17/16 := by norm_num [c]
  have hci : c.im=t := by norm_num [c]
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hQ : 2≤Q := by
    dsimp [Q]
    nlinarith [abs_nonneg t,mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hQpos : 0<Q := by linarith
  have hlog : Real.log (4096*Q^2) ≤ 14*Real.log Q := by
    rw [Real.log_mul (by norm_num) (by positivity),show (4096:ℝ)=2^12 by norm_num,
      Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_log (by norm_num) hQ]
  have H := ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ)
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall c (3/2)) := H.mono (Set.subset_univ _)
  have hf' : AnalyticOnNhd ℂ χ.LFunction (closedBall c (3/4)) := H.mono (Set.subset_univ _)
  have hc : χ.LFunction c≠0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ)
    (by rw [hcr]; norm_num)
  let D := MeromorphicOn.divisor χ.LFunction (closedBall c (3/4))
  let Z := (D.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hZ : (Z:Set ℂ)=zeroSet χ.LFunction c (3/4) := by
    simpa only [Z,Set.Finite.coe_toFinset,D] using divisor_support_eq_zeroSet (by norm_num) hf' hc
  have hzmem {u : ℂ} (hu : u∈Z) : u ∈ closedBall c (3/4) ∧ χ.LFunction u=0 := by
    apply mem_zeroSet.mp
    rw [←hZ]
    exact hu
  have hdiv (u : ℂ) (hu : u∈Z) : D u = (analyticOrderNatAt χ.LFunction u:ℤ) := by
    dsimp only [D]
    rw [AnalyticOnNhd.divisor_apply hf' (hzmem hu).1,←Nat.cast_analyticOrderNatAt
      (analyticOrderAt_ne_top_of_closedBall (by norm_num) hf' hc (hzmem hu).1)]
    simp
  have hB := explicitFormula_disk_growth hχ t
  change ∀ w ∈ sphere c (3/2), ‖χ.LFunction w/χ.LFunction c‖ ≤ 4096*Q^2 at hB
  refine ⟨Z,hZ,?_,?_,?_⟩
  · intro z hz
    obtain ⟨hball,hzero⟩ := hzmem hz
    have hd : ‖z-c‖≤3/4 := by simpa only [mem_closedBall,dist_eq_norm] using hball
    have hr := (Complex.abs_re_le_norm (z-c)).trans hd
    have hi := (Complex.abs_im_le_norm (z-c)).trans hd
    rw [sub_re,hcr] at hr
    rw [sub_im,hci] at hi
    exact (mem_criticalStripZeroFinset _).mpr ⟨by linarith [(abs_le.mp hr).1],lt_of_not_ge
      (fun h => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) h hzero),
      by linarith [(abs_le.mp hi).1],by linarith [(abs_le.mp hi).2],hzero⟩
  · have h := zeroCount_half_le (R:=3/2) (by norm_num) (show 0<(4096*Q^2)*‖χ.LFunction c‖ by positivity) hf hc
      (fun z hz => by have h := hB z hz; rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr hc)] at h; exact h)
    norm_num only [show (3/2:ℝ)/2=3/4 by norm_num] at h
    rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hc),add_sub_cancel_right,
      zeroCount_eq_sum_analyticOrderNatAt (by norm_num) hf' hc hZ] at h
    push_cast at h
    exact h.trans (div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num)))
  · intro σ hlo hhi hn
    let s := (σ:ℂ)+(t:ℂ)*I
    have hsc : s-c=((σ-17/16:ℝ):ℂ) := by dsimp [s,c]; push_cast; ring
    have hs : s∈closedBall c (11/16) := by
      rw [mem_closedBall,dist_eq_norm,hsc,Complex.norm_real,Real.norm_eq_abs,abs_le]
      constructor <;> linarith
    have h := landau_logDeriv_le_of_lt (by norm_num : (0:ℝ)≤11/16) (by norm_num) hf hc hB hs hn
    rw [show (3/2:ℝ)/2=3/4 by norm_num,show (2:ℝ)*(3/4+11/16)/(3/4-11/16)^2=736 by norm_num] at h
    change ‖logDeriv χ.LFunction s - ∑ᶠ u,(D u:ℂ)/(s-u)‖ ≤ 736*Real.log (4096*Q^2) at h
    rw [finsum_eq_sum_of_support_subset _ (s:=Z)] at h
    · have hd : ∀ u∈Z, (D u:ℂ)=(analyticOrderNatAt χ.LFunction u:ℂ) := by
        intro u hu; rw [hdiv u hu,Int.cast_natCast]
      simpa only [sum_congr rfl (fun u hu => congrArg (·/(s-u)) (hd u hu))] using
        h.trans (show 736*Real.log (4096*Q^2) ≤ 10304*Real.log Q by linarith)
    · intro u hu
      by_contra hn
      have hd : D u=0 := by
        by_contra hd
        exact hn ((D.finiteSupport (isCompact_closedBall _ _)).mem_toFinset.mpr hd)
      simp [Function.mem_support,hd] at hu

end AnalyticNumberTheory.DirichletLFunctions
