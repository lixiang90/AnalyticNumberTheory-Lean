import AnalyticNumberTheory.DirichletLFunctions.RectangularCount
import AnalyticNumberTheory.DirichletLFunctions.HorizontalArgument
import AnalyticNumberTheory.DirichletLFunctions.ConductorZeros

/-!
# Riemann–von Mangoldt for Dirichlet L-functions

The functional equation reflects the left edges to the right, with the extra
vertical term `2T log q`. The horizontal changes of argument are logarithmic.
For induced characters the open-strip count agrees with the primitive count
and the conductor occurs in the main term.
-/

open Complex Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace AnalyticNumberTheory.DirichletLFunctions

private noncomputable def horiz (f : ℂ → ℂ) (t a b : ℝ) : ℝ :=
  ∫ x in a..b, (logDeriv f ((x:ℂ)+t*I)).im

private noncomputable def vert (f : ℂ → ℂ) (T a : ℝ) : ℝ :=
  ∫ t in (-T)..T, (logDeriv f ((a:ℂ)+t*I)).re

private theorem no_star_ordinate {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {t : ℝ}
    (hn : ∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ t) :
    ∀ ρ ∈ CriticalStripZerosL (star χ), ρ.im ≠ -t := by
  intro ρ hρ he
  have h := (criticalStripZerosL_star_conj_iff χ (conj ρ)).mp (by simpa using hρ)
  apply hn (conj ρ) h
  simp [he]

private theorem continuousOn_logDeriv_edge {F : ℂ → ℂ} (hF : Differentiable ℂ F) {p : ℝ → ℂ}
    (hp : Continuous p) {U : Set ℝ} (hn : ∀ u ∈ U, F (p u) ≠ 0) : ContinuousOn (fun u => logDeriv F (p u)) U :=
  (((hF.contDiff (n := 1)).continuous_deriv le_rfl).comp hp).continuousOn.div (hF.continuous.comp hp).continuousOn hn

private theorem horiz_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) (t : ℝ) (hno : ∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ t) :
    horiz (DirichletCharacter.completedLFunction χ) t (-1) 2 =
      horiz (DirichletCharacter.completedLFunction χ) t (1/2) 2 -
      horiz (DirichletCharacter.completedLFunction (star χ)) (-t) (1/2) 2 := by
  let F := DirichletCharacter.completedLFunction χ
  let G := DirichletCharacter.completedLFunction (star χ)
  have hF := differentiable_completedLFunction_of_ne_one (isPrimitive_ne_one hχ hq)
  have hn (x : ℝ) : F ((x:ℂ)+t*I) ≠ 0 := fun he => hno _ ((completedLFunction_eq_zero_iff_criticalStrip hχ hq _).mp he) (by simp)
  have hG (x : ℝ) : G ((x:ℂ)+(-t:ℝ)*I) ≠ 0 := fun he =>
    no_star_ordinate hno _ ((completedLFunction_eq_zero_iff_criticalStrip (isPrimitive_star hχ) hq _).mp he) (by simp)
  have hi (a b : ℝ) : IntervalIntegrable (fun x : ℝ => (logDeriv F ((x:ℂ)+t*I)).im) volume a b :=
    (Complex.continuous_im.comp_continuousOn (continuousOn_logDeriv_edge hF
      (p := fun x : ℝ => (x:ℂ)+t*I) (Complex.continuous_ofReal.add continuous_const) (fun x _ => hn x))).intervalIntegrable
  have hleft : horiz F t (-1) (1/2) = -horiz G (-t) (1/2) 2 := by
    unfold horiz
    have hcomp := intervalIntegral.integral_comp_sub_left (fun x : ℝ => (logDeriv F ((x:ℂ)+t*I)).im)
      1 (a := (1/2:ℝ)) (b := 2)
    norm_num at hcomp
    rw [← hcomp, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [show 1-(u:ℂ)+(t:ℂ)*I = 1-((u:ℂ)+(-t:ℝ)*I) by push_cast; ring,
      logDeriv_completedLFunction_reflect hχ hq (hG u)]
    simp [G, ← Complex.natCast_log]
  change horiz F t (-1) 2 = horiz F t (1/2) 2 - horiz G (-t) (1/2) 2
  have hadd : horiz F t (-1) (1/2) + horiz F t (1/2) 2 = horiz F t (-1) 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  rw [← hadd, hleft]
  ring

private theorem vert_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) (T : ℝ) :
    vert (DirichletCharacter.completedLFunction χ) T (-1) =
      -(2*T*Real.log (q:ℝ)) - vert (DirichletCharacter.completedLFunction (star χ)) T 2 := by
  let F := DirichletCharacter.completedLFunction χ
  let G := DirichletCharacter.completedLFunction (star χ)
  have hχs := isPrimitive_ne_one (isPrimitive_star hχ) hq
  have hn (u : ℝ) : G ((2:ℂ)+u*I) ≠ 0 :=
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re _ (Or.inl hχs) (by simp)
  have hin : IntervalIntegrable (fun t : ℝ => (logDeriv G ((2:ℂ)+(-t:ℝ)*I)).re) volume (-T) T :=
    (Complex.continuous_re.comp_continuousOn (continuousOn_logDeriv_edge (differentiable_completedLFunction_of_ne_one hχs)
      (p := fun t : ℝ => (2:ℂ)+(-t:ℝ)*I) (by fun_prop) (fun t _ => hn (-t)))).intervalIntegrable
  change (∫ t in (-T)..T, (logDeriv F (((-1:ℝ):ℂ)+t*I)).re) = _
  calc
    _ = ∫ t in (-T)..T, (-Real.log (q:ℝ) - (logDeriv G ((2:ℂ)+(-t:ℝ)*I)).re) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [show ((-1:ℝ):ℂ)+(t:ℂ)*I = 1-((2:ℂ)+(-t:ℝ)*I) by push_cast; ring,
        logDeriv_completedLFunction_reflect hχ hq (hn (-t))]
      simp [G, ← Complex.natCast_log]
    _ = _ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hin, intervalIntegral.integral_const]
      have hc := intervalIntegral.integral_comp_neg (fun t : ℝ => (logDeriv G ((2:ℂ)+t*I)).re) (a := -T) (b := T)
      simp only [neg_neg] at hc
      rw [hc]
      change (T - -T) • (-Real.log (q:ℝ)) - _ = -(2*T*Real.log (q:ℝ)) - _
      rw [smul_eq_mul]
      congr 1
      ring

/-- Unconditional evaluation of the primitive zero-counting rectangle.
The two horizontal edges contribute `O(log(qT))` together. -/
theorem exists_uniform_primitiveRiemannVonMangoldtContour :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive → 2 ≤ q →
      ∃ H : RiemannVonMangoldtContourHypothesis χ, H.horConst = C := by
  obtain ⟨C,hC,hhalf⟩ := integral_im_logDeriv_completedLFunction_horizontal_le
  refine ⟨(4*C)/(2*Real.pi), by positivity, fun {q} _ {χ} hχ hq => ⟨⟨_, by positivity, ?_⟩, rfl⟩⟩
  intro T hT hn
  let F := DirichletCharacter.completedLFunction χ
  let G := DirichletCharacter.completedLFunction (star χ)
  let X := Real.log ((q:ℝ)*T)
  have hT0 : 0 < T := by linarith
  have hh (t : ℝ) (ht : |t| = T) (hno : ∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ t) :
      |horiz F t (-1) 2| ≤ 2*C*X := by
    have h1 := hhalf hχ hq t (ht ▸ hT) hno
    have h2 := hhalf (isPrimitive_star hχ) hq (-t) (by rw [abs_neg,ht]; exact hT) (no_star_ordinate hno)
    change |horiz F t (1/2) 2| ≤ _ at h1
    change |horiz G (-t) (1/2) 2| ≤ _ at h2
    rw [abs_neg,ht] at h2
    rw [ht] at h1
    rw [horiz_reflect hχ hq t hno]
    exact (abs_sub _ _).trans (by dsimp [X]; linarith)
  have hminus := hh (-T) (by simpa using abs_of_pos hT0) (fun ρ hρ => (hn ρ hρ).2)
  have hplus := hh T (abs_of_pos hT0) (fun ρ hρ => (hn ρ hρ).1)
  have hrect := zeroCountL_rectangle hχ hq hT0 hn
  change 2*Real.pi*(zeroCountL χ T : ℝ) = horiz F (-T) (-1) 2 - horiz F T (-1) 2 + vert F T 2 - vert F T (-1) at hrect
  rw [vert_reflect hχ hq T] at hrect
  have hdiff : (zeroCountL χ T:ℝ) - ((1/(2*Real.pi))*vert F T 2 + (1/(2*Real.pi))*vert G T 2 + (T/Real.pi)*Real.log (q:ℝ)) =
      (horiz F (-T) (-1) 2-horiz F T (-1) 2)/(2*Real.pi) := by
    field_simp
    linear_combination hrect
  change |(zeroCountL χ T:ℝ) - ((1/(2*Real.pi))*vert F T 2 + (1/(2*Real.pi))*vert G T 2 + (T/Real.pi)*Real.log (q:ℝ))| ≤ _*X
  rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
  calc
    _ ≤ (4*C*X)/(2*Real.pi) := div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith)) (by positivity)
    _ = _ := by ring

/-- Rectangular contour estimate for an individual primitive character. -/
noncomputable def primitiveRiemannVonMangoldtContour {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) : RiemannVonMangoldtContourHypothesis χ :=
  (exists_uniform_primitiveRiemannVonMangoldtContour.choose_spec.2 hχ hq).choose

/-- Riemann–von Mangoldt for a primitive nonprincipal Dirichlet character. -/
theorem zeroCountL_asymptotic_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCountL χ T:ℝ) - (T/Real.pi)*Real.log ((q:ℝ)*T/(2*Real.pi*Real.exp 1))| ≤ C*Real.log ((q:ℝ)*T) :=
  zeroCountL_asymptotic (isPrimitive_ne_one hχ hq) (primitiveRiemannVonMangoldtContour hχ hq)

/-- For any nonprincipal character, the main term uses its conductor. Missing
Euler factors have no zeros in the open critical strip. -/
theorem zeroCountL_asymptotic_conductor {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCountL χ T:ℝ) - (T/Real.pi)*Real.log ((χ.conductor:ℝ)*T/(2*Real.pi*Real.exp 1))| ≤
        C*Real.log ((χ.conductor:ℝ)*T) := by
  let _ := neZero_conductor χ
  have hh : 2 ≤ χ.conductor := (by decide : 2 ≤ 3).trans (three_le_conductor_of_ne_one hχ)
  simpa only [zeroCountL_eq_primitiveCharacter χ] using zeroCountL_asymptotic_primitive χ.primitiveCharacter_isPrimitive hh

open AnalyticNumberTheory.RiemannZeta in
/-- The symmetric count of a principal character is twice the usual upper-half
count for ζ, at every height and every nonzero modulus. -/
theorem zeroCountL_principal {q : ℕ} [NeZero q] (T : ℝ) :
    zeroCountL (1 : DirichletCharacter ℂ q) T = 2 * zeroCountUpTo T := by
  classical
  have hlevel := zeroCountL_changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1) T
  rw [DirichletCharacter.changeLevel_one] at hlevel
  rw [hlevel]
  rcases lt_or_ge T 0 with hT | hT
  · simp [zeroCountL_of_neg _ hT, zeroCountUpTo_nonpos hT.le]
  have hne {ρ : ℂ} (hρ : ρ ∈ CriticalStripZeros) : ρ.im ≠ 0 := by
    intro he
    have hr : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simp [he])
    apply xi_ne_zero_ofReal ρ.re
    rw [hr]
    exact xi_eq_zero_iff.mpr hρ
  have half : zeroCountHalfL (1 : DirichletCharacter ℂ 1) T = zeroCountUpTo T := by
    rw [zeroCountHalfL, zeroCountUpTo_eq_sum, DirichletCharacter.LFunction_modOne_eq]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ρ
    rw [mem_criticalStripZeroFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
    simp only [DirichletCharacter.LFunction_modOne_eq, Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h0,h1,hi,hT',hz⟩
      have hρ : ρ ∈ CriticalStripZeros := ⟨hz,h0,h1⟩
      exact ⟨⟨hρ,hi,hT'⟩,lt_of_le_of_ne hi (hne hρ).symm⟩
    · rintro ⟨⟨hρ,hi,hT'⟩,_⟩
      exact ⟨hρ.2.1,hρ.2.2,hi,hT',hρ.1⟩
  have realAxis : zeroCountRealStripL (1 : DirichletCharacter ℂ 1) = 0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    obtain ⟨h0,h1,hlo,hhi,hz⟩ := (mem_criticalStripZeroFinset _).mp hρ
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    exact False.elim (hne ⟨hz,h0,h1⟩ (le_antisymm hhi hlo))
  simpa [realAxis,half,two_mul] using zeroCountL_add_real_eq_half_add_half_star (1 : DirichletCharacter ℂ 1) hT

/-- The symmetric Riemann–von Mangoldt formula for every Dirichlet character.
The conductor enters both the main term and the logarithmic error. -/
theorem zeroCountL_riemannVonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCountL χ T:ℝ) - (T/Real.pi)*Real.log ((χ.conductor:ℝ)*T/(2*Real.pi*Real.exp 1))| ≤
        C*Real.log ((χ.conductor:ℝ)*T) := by
  by_cases hχ : χ = 1
  · subst χ
    rw [(conductor_eq_one_iff (1 : DirichletCharacter ℂ q)).mpr rfl]
    simp only [Nat.cast_one,one_mul]
    obtain ⟨C,hC,hζ⟩ := AnalyticNumberTheory.RiemannZeta.riemannVonMangoldt_asymptotic
    have h₂ := Real.log_pos (by norm_num : (1:ℝ) < 2)
    refine ⟨2*C + 2/Real.log 2, by positivity, fun T hT => ?_⟩
    rw [zeroCountL_principal]
    push_cast
    have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hT
    have hscale := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2/Real.log 2)
    rw [div_mul_cancel₀ _ h₂.ne'] at hscale
    obtain ⟨hl,hu⟩ := abs_le.mp (hζ T hT)
    apply abs_le.mpr
    constructor <;> ring_nf at hl hu hscale ⊢ <;> linarith
  · exact zeroCountL_asymptotic_conductor hχ

/-- Immediately to the right of any nonnegative height the count is constant,
and neither horizontal edge contains an open-strip zero. -/
theorem eventually_zeroCountL_eq_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {T : ℝ} (hT : 0 ≤ T) : ∀ᶠ t in 𝓝[>] T, zeroCountL χ t = zeroCountL χ T ∧
      ∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ t ∧ ρ.im ≠ -t := by
  classical
  let Z := criticalStripZeroFinset χ (-(T+1)) (T+1)
  have hev : ∀ᶠ t in 𝓝[>] T, ∀ ρ ∈ Z, T < |ρ.im| → t < |ρ.im| := by
    apply Z.eventually_all.mpr
    intro ρ _
    by_cases h : T < |ρ.im|
    · have hu : ∀ᶠ u in 𝓝[>] T, u < |ρ.im| := mem_nhdsWithin_of_mem_nhds (gt_mem_nhds h)
      exact hu.mono fun _ ht _ => ht
    · exact .of_forall fun _ ht => (h ht).elim
  filter_upwards [hev, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by linarith : T < T+1))] with t hh (ht : T < t) (ht' : t < T+1)
  have hbound {ρ : ℂ} (hρ : ρ ∈ CriticalStripZerosL χ) (hg : |ρ.im| ≤ t) : |ρ.im| ≤ T := by
    by_contra! h
    have hm : ρ ∈ Z := (mem_criticalStripZeroFinset χ).mpr
      ⟨hρ.1,hρ.2.1,(abs_le.mp (hg.trans ht'.le)).1,(abs_le.mp (hg.trans ht'.le)).2,hρ.2.2⟩
    exact (hh ρ hm h).not_ge hg
  constructor
  · unfold zeroCountL
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ρ
    simp only [mem_criticalStripZeroFinset]
    constructor
    · rintro ⟨h0,h1,hi,hi',hz⟩
      obtain ⟨hl,hu⟩ := abs_le.mp (hbound ⟨h0,h1,hz⟩ (abs_le.mpr ⟨hi,hi'⟩))
      exact ⟨h0,h1,hl,hu,hz⟩
    · rintro ⟨h0,h1,hi,hi',hz⟩
      exact ⟨h0,h1,by linarith,by linarith,hz⟩
  · intro ρ hρ
    have ha : |ρ.im| ≠ t := fun he => ht.not_ge (he ▸ hbound hρ he.le)
    constructor <;> intro he <;> apply ha <;> simp [he,abs_of_nonneg (hT.trans ht.le)]

/-- Riemann–von Mangoldt with a single absolute implied constant for all
characters, moduli, conductors, and heights at least two. -/
theorem zeroCountL_riemannVonMangoldt_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ), 2 ≤ T →
      |(zeroCountL χ T:ℝ) - (T/Real.pi)*Real.log ((χ.conductor:ℝ)*T/(2*Real.pi*Real.exp 1))| ≤
        C*Real.log ((χ.conductor:ℝ)*T) := by
  obtain ⟨A,hA,hhor⟩ := exists_uniform_primitiveRiemannVonMangoldtContour
  obtain ⟨B,hB,hvert⟩ := rvm_vertical_edges_main_term_asymptotic
  obtain ⟨E,hE,hprin⟩ := zeroCountL_riemannVonMangoldt (1 : DirichletCharacter ℂ 1)
  refine ⟨max E (A+B),hE.trans (le_max_left _ _),fun {q} _ χ T hT => ?_⟩
  have ht : 0 < T := by linarith
  have hf1 : (1:ℝ) ≤ χ.conductor := by exact_mod_cast conductor_pos χ
  have hlog := Real.log_nonneg ((by linarith : (1:ℝ) ≤ T).trans (le_mul_of_one_le_left ht.le hf1))
  by_cases hχ : χ = 1
  · subst χ
    have h := hprin T hT
    rw [zeroCountL_principal] at h ⊢
    simp only [(conductor_eq_one_iff _).mpr rfl,Nat.cast_one,one_mul] at h ⊢
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith)))
  let _ := neZero_conductor χ
  let ψ := χ.primitiveCharacter
  have hf := three_le_conductor_of_ne_one hχ
  obtain ⟨H,hH⟩ := hhor χ.primitiveCharacter_isPrimitive (by omega : 2 ≤ χ.conductor)
  rw [zeroCountL_eq_primitiveCharacter χ]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)
  let f : ℝ → ℝ := fun t => t / Real.pi * Real.log ((χ.conductor:ℝ)*t/(2*Real.pi*Real.exp 1))
  let g : ℝ → ℝ := fun t => Real.log ((χ.conductor:ℝ)*t)
  have hfc : ContinuousAt f T := by dsimp [f]; fun_prop (disch := positivity)
  have hgc : ContinuousAt g T := by dsimp [g]; fun_prop (disch := positivity)
  apply le_of_tendsto_of_tendsto (b := 𝓝[>] T)
    ((continuousAt_const.sub hfc).abs.tendsto.mono_left nhdsWithin_le_nhds)
    ((continuousAt_const.mul hgc).tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [eventually_zeroCountL_eq_right ψ ht.le,self_mem_nhdsWithin] with t he (ht' : T < t)
  obtain ⟨he,hno⟩ := he
  dsimp only [Pi.sub_apply,Pi.mul_apply,Function.comp_apply,id_eq]
  change |(zeroCountL ψ T:ℝ)-f t| ≤ (A+B)*g t
  rw [← he]
  have h2 := hT.trans ht'.le
  have h1 := H.contour_bound t h2 hno
  have h3 := hvert ψ t h2
  rw [hH] at h1
  have hlg : Real.log (t+2) ≤ g t := by
    apply Real.log_le_log (by linarith)
    nlinarith [show (3:ℝ) ≤ χ.conductor by exact_mod_cast hf]
  obtain ⟨hl,hu⟩ := abs_le.mp h1
  obtain ⟨hl',hu'⟩ := abs_le.mp h3
  have hmul := mul_le_mul_of_nonneg_left hlg hB
  dsimp only [f,g] at *
  rw [add_mul]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end AnalyticNumberTheory.DirichletLFunctions
