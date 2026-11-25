import AnalyticNumberTheory.AnalyticTools.Gamma.PositiveSmoothingShift
import AnalyticNumberTheory.SieveMethods.CharacterKernelVerticalBound
import AnalyticNumberTheory.DirichletSeries.ExponentialSmoothing
import AnalyticNumberTheory.DirichletLFunctions.PoleClearedCharacter
import AnalyticNumberTheory.DirichletLFunctions.ConductorLeftEdge

/-!
# Exponentially smoothed correlations of character values

The weight has a third-order zero at the origin. A Mellin shift across the
possible pole at one separates the principal character from the other
characters, uniformly in the height difference.
-/
noncomputable section
open scoped Classical
open Complex Real Set Filter MeasureTheory
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- The exponential character kernel, prior to division by the cube of its length. -/
def smoothedCharacterKernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (s-3) n*(Real.exp (-(n:ℝ)/X):ℂ)

/-- The exponentially weighted correlation series is absolutely convergent. -/
theorem smoothedCharacterKernel_hasSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0<X) {s : ℂ} (hs : s.re∈Icc (0:ℝ) 2) :
    HasSum (fun n : ℕ => LSeries.term (fun n : ℕ => χ n) (s-3) n*(Real.exp (-(n:ℝ)/X):ℂ))
      (smoothedCharacterKernel χ X s) := by
  have h := DirichletSeries.hasSum_exponentiallySmoothed (F:=χ.LFunction)
    (a:=fun n : ℕ => χ n) (s-3) (c:=5-s.re) (by linarith [hs.2]) hX (fun t => by
      have hx : 1<(s-3+(((5-s.re:ℝ):ℂ)+t*I)).re := by simp;norm_num
      rw [DirichletCharacter.LFunction_eq_LSeries χ hx]
      exact (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hx).hasSum)
  exact h.summable.hasSum

/-- Shifting the kernel left of the imaginary axis gives the exact possible residue at one. -/
theorem smoothedCharacterKernel_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X δ : ℝ} (hX : 0<X) (hδ : 0<δ) (hδ' : δ≤1/4) {s : ℂ} (hs : s.re∈Icc (0:ℝ) 2) :
    smoothedCharacterKernel χ X s =
      gammaSmoothingIntegral (fun w => χ.LFunction (s-3+w)) X (3-s.re-δ) +
      poleClearedLFunction χ 1*Complex.Gamma (4-s)*(X:ℂ)^(4-s) := by
  let b := s-3
  let l := 3-s.re-δ
  let r := 5-s.re
  let p := 4-s
  have hb : b.re=s.re-3 := by simp [b]
  have hp : p.re=4-s.re := by simp [p]
  have hl : 0<l := by dsimp [l];linarith [hs.2]
  have hr : 0<r := by dsimp [r];linarith [hs.2]
  have ha : l<p.re := by rw [hp];dsimp [l];linarith
  have hd : p.re<r := by rw [hp];dsimp [r];linarith
  have hbp : b+p=1 := by dsimp [b,p];ring
  have hstrip (w : ℂ) (hw : w.re∈Icc l r) : (b+w).re∈Icc (-1/2:ℝ) 2 := by
    rw [add_re,hb]; obtain ⟨h₁,h₂⟩:=hw;dsimp [l,r] at h₁ h₂;constructor <;> linarith
  obtain ⟨B,hB,HB⟩ := poleClearedLFunction_strip_growth χ
  have hh := gammaSmoothingIntegral_positive_residue
    (F:=fun w => χ.LFunction (b+w)) (R:=fun w => poleClearedLFunction χ (b+w))
    hl ha hd hX (fun w _ => (analyticAt_poleClearedLFunction χ (b+w)).comp
      (f:=fun w : ℂ => b+w) (analyticAt_const.add analyticAt_id))
    (fun w _ hn => by
      have he : b+w≠1 := by intro h;apply hn;linear_combination h-hbp
      rw [poleClearedLFunction_eq χ he];congr 1;linear_combination hbp)
    (m:=3) (B:=B*(1+|b.im|)^3) (by positivity) (fun w hw => by
      apply (HB _ (hstrip w hw)).trans
      have hh : 1+|(b+w).im|≤(1+|b.im|)*(1+|w.im|) := by
        rw [add_im];nlinarith [abs_add_le b.im w.im,mul_nonneg (abs_nonneg b.im) (abs_nonneg w.im)]
      calc _ ≤ B*((1+|b.im|)*(1+|w.im|))^3 := by gcongr
           _ = _ := by ring)
  have hright := DirichletSeries.hasSum_exponentiallySmoothed (F:=χ.LFunction)
    (a:=fun n : ℕ => χ n) b hr hX (fun t => by
      have hx : 1<(b+((r:ℂ)+t*I)).re := by simp [hb,r];norm_num
      rw [DirichletCharacter.LFunction_eq_LSeries χ hx]
      exact (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hx).hasSum)
  rw [hbp] at hh
  exact hright.tsum_eq.trans (sub_eq_iff_eq_add'.mp hh)

/-- The kernel at height difference Im s has square-root conductor error. The
rapidly decaying extra term occurs exactly for the principal character. -/
theorem smoothedCharacterKernel_decay :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
      (hs : s.re∈Icc (0:ℝ) 2) {X : ℝ},1≤X →
      let H := (q:ℝ)*(|s.im|+2)
      X^(s.re-3)*‖smoothedCharacterKernel χ X s‖ ≤
        C*(Real.sqrt H*(1+Real.log H)*X^(-(1/(4+Real.log H))) + (if χ=1 then X/(1+|s.im|)^4 else 0)) := by
  obtain ⟨A,hA,HA⟩ := characterKernel_logarithmic_vertical_decay
  obtain ⟨B,hB,HB⟩ := norm_Gamma_positive_strip_weight (a:=(2:ℝ)) (b:=4) (by norm_num) (by norm_num) 4
  refine ⟨A+B,by positivity,?_⟩
  intro q _ χ s hs X hX
  let H := (q:ℝ)*(|s.im|+2)
  let δ := 1/(4+Real.log H)
  have hq : 1≤(q:ℝ) := by exact_mod_cast (NeZero.one_le : 1≤q)
  have hH : 1≤H := by dsimp [H];nlinarith [abs_nonneg s.im,mul_nonneg (by linarith : 0≤(q:ℝ)-1) (by linarith [abs_nonneg s.im] : 0≤|s.im|+2)]
  have hlog := Real.log_nonneg hH
  have hd : 0<δ := by dsimp [δ];positivity
  have hd' : δ≤1/4 := by dsimp [δ];apply one_div_le_one_div_of_le (by norm_num);linarith
  have hX' := zero_lt_one.trans_le hX
  have hi := HA χ hs hX
  have hr : (4-s).re=4-s.re := by norm_num
  have hg := HB (4-s) (hr ▸ (show 4-s.re∈Icc (2:ℝ) 4 from ⟨by linarith [hs.2],by linarith [hs.1]⟩))
  simp only [sub_im,im_ofNat,zero_sub,abs_neg] at hg
  have hΓ : ‖Complex.Gamma (4-s)‖ ≤ B/(1+|s.im|)^4 := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa [mul_comm] using hg
  let r := poleClearedLFunction χ 1*Complex.Gamma (4-s)*(X:ℂ)^(4-s)
  have hres : X^(s.re-3)*‖r‖≤B*(if χ=1 then X/(1+|s.im|)^4 else 0) := by
    have hp := norm_poleClearedLFunction_one χ
    dsimp only [r];rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX',hr]
    by_cases h : χ=1
    · simp only [if_pos h] at hp ⊢
      have hx : X^(s.re-3)*X^(4-s.re)=X := by
        rw [←Real.rpow_add hX'];convert Real.rpow_one X using 2 <;> ring
      calc _ ≤ X^(s.re-3)*(1*(B/(1+|s.im|)^4)*X^(4-s.re)) := by gcongr
           _ = B*(X^(s.re-3)*X^(4-s.re))/(1+|s.im|)^4 := by ring
           _ = _ := by rw [hx];ring
    · simp only [if_neg h] at hp ⊢
      rw [le_antisymm hp (norm_nonneg _)];simp
  rw [smoothedCharacterKernel_eq χ hX' hd hd' hs]
  change _*‖_+r‖ ≤ (A+B)*(Real.sqrt H*(1+Real.log H)*X^(-δ)+_)
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.rpow_nonneg hX'.le _)).trans
  rw [mul_add]
  apply (add_le_add hi hres).trans
  have ha : 0≤Real.sqrt H*(1+Real.log H)*X^(-δ) := by positivity
  have hb : 0≤(if χ=1 then X/(1+|s.im|)^4 else 0) := by split_ifs <;> positivity
  nlinarith only [mul_nonneg hB.le ha,mul_nonneg hA.le hb]

/-- The kernel at height difference Im s has square-root conductor error. The
rapidly decaying extra term occurs exactly for the principal character. -/
theorem smoothedCharacterKernel_bound :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
      (hs : s.re∈Icc (0:ℝ) 2) {X : ℝ},1≤X →
      let H := (q:ℝ)*(|s.im|+2)
      X^(s.re-3)*‖smoothedCharacterKernel χ X s‖ ≤
        C*(Real.sqrt H*(1+Real.log H) + (if χ=1 then X/(1+|s.im|)^4 else 0)) := by

  obtain ⟨C,hC,HC⟩ := smoothedCharacterKernel_decay
  refine ⟨C,hC,?_⟩;intro q _ χ s hs X hX
  let H := (q:ℝ)*(|s.im|+2)
  have hH : 1≤H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast (NeZero.one_le : 1≤q))
    (by linarith [abs_nonneg s.im])
  have hl := Real.log_nonneg hH
  apply (HC χ hs hX).trans
  apply mul_le_mul_of_nonneg_left (add_le_add _ le_rfl) hC.le
  apply mul_le_of_le_one_right (by change 0≤Real.sqrt H*(1+Real.log H);positivity)
  exact (Real.rpow_le_rpow_of_exponent_le hX (show -(1/(4+Real.log H))≤0 from neg_nonpos.mpr (by positivity))).trans_eq (Real.rpow_zero _)

end AnalyticNumberTheory.SieveMethods
