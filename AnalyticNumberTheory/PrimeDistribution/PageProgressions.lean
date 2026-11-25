import AnalyticNumberTheory.PrimeDistribution.PageRegion
import AnalyticNumberTheory.PrimeDistribution.SiegelWalfisz

/-!
# Page's estimate for character sums and prime progressions

At a fixed modulus bound `Q`, the same exceptional primitive character is removed
at every cutoff. The constants in the character estimate are given in terms of
the zero-free parameter and the right-half-plane logarithmic derivative bound.
-/

noncomputable section

open Complex Finset AnalyticNumberTheory.DirichletLFunctions
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

/-- Coefficient of the Page character-sum error, expressed in terms of the
width `c` of the zero-free region and the right-half-plane bound `Z`. -/
def pageCharacterConstant (c Z : ℝ) : ℝ :=
  perronRectangleConstant (c/16) (characterRectangleConstant (c/4) 1 Z)

theorem pageCharacterConstant_pos {c Z : ℝ} (hc : 0<c) (hZ : 0<Z) :
    0<pageCharacterConstant c Z :=
  perronRectangleConstant_pos (by positivity)
    ((by positivity : 0<4/(c/4)+Z).trans_le (le_max_left ..))

/-- A pointwise finite-cutoff version for a character with the given logarithmic
zero-free region. All coefficients on the right are specified. -/
theorem norm_psiChar_halfInteger_page {c Z Q : ℝ} (hc : 0<c) (hc4 : c≤1/4)
    (hZ : 0<Z) (hQ : 2≤Q) {q : ℕ} [NeZero q] (hq : (q:ℝ)≤Q)
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1)
    (hright : ∀ s : ℂ,1<s.re → s.re≤2 →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖≤1/(s.re-1)+Z)
    (hregion : ∀ {s : ℂ},1-c/Real.log ((Q+2)*(|s.im|+2))≤s.re →
      DirichletCharacter.LFunction χ s≠0) (N : ℕ) :
    let x : ℝ := N+1/2
    let u := Real.sqrt (Real.log x)
    Real.exp 16≤x → Q+2≤Real.exp u →
    ‖psiChar x χ‖≤pageCharacterConstant c Z*x*Real.exp (-(c/256)*u) := by
  intro x u hx hQu
  have hx0 : 0<x := (Real.exp_pos _).trans_le hx
  have hlog : 16≤Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hu : 1≤u := Real.one_le_sqrt.mpr (by linarith)
  have hu0 : 0<u := by linarith
  have hu2 : u^2=Real.log x := Real.sq_sqrt (by linarith)
  have hD : 0<characterRectangleConstant (c/4) 1 Z :=
    (by positivity : 0<4/(c/4)+Z).trans_le (le_max_left ..)
  have hmin : min ((c/4)/4) (1/8) = c/16 := by rw [min_eq_left (by linarith)]; ring
  have H := norm_psiChar_halfInteger_le_explicit (by positivity : 0<(c/4)/4) hD N q χ hχ hx
  change (∀ s : ℂ, 1-((c/4)/4)/u≤s.re → s.re≤2 → |s.im|≤Real.exp u →
      DirichletCharacter.LFunction χ s ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖≤characterRectangleConstant (c/4) 1 Z*Real.log x) →
      ‖psiChar x χ‖≤_ at H
  rw [hmin,show c/16/16=c/256 by ring] at H
  apply H
  intro s hs hs2 ht
  rw [←hu2]
  apply logDeriv_LFunction_of_zeroFree_rectangle (by positivity) (by linarith) hZ hu _ hχ hright _ hs hs2 ht
  · rw [one_mul]
    exact (Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos q)) (by linarith : (q:ℝ)≤Real.exp u)).trans_eq (Real.log_exp _)
  · intro z hzr hzi
    apply hregion
    have hLp : 0<Real.log ((Q+2)*(|z.im|+2)) := Real.log_pos (by nlinarith [abs_nonneg z.im])
    have he1 : 1≤Real.exp u := Real.one_le_exp hu0.le
    have hL : Real.log ((Q+2)*(|z.im|+2)) ≤ 4*u := by
      rw [Real.log_mul (by linarith : Q+2 ≠ 0) (by positivity)]
      have h₁ := (Real.log_le_log (by linarith : 0<Q+2) hQu).trans_eq (Real.log_exp _)
      have h₂ := Real.log_le_log (by positivity : 0 < |z.im|+2)
        (by linarith : |z.im|+2≤4*Real.exp u)
      rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (Real.exp_pos _).ne',Real.log_exp] at h₂
      have h4 : Real.log 4 ≤ 2 := by
        rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
        norm_num only [Nat.cast_ofNat]
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    have hwidth : (c/4)/u ≤ c/Real.log ((Q+2)*(|z.im|+2)) := by
      rw [div_div]
      exact div_le_div_of_nonneg_left hc.le hLp hL
    exact (sub_le_sub_left hwidth 1).trans hzr

/-- One exceptional primitive pair works simultaneously for every cutoff and
all characters in the range. The zero and right-hand constants are absolute. -/
theorem page_psiChar_halfInteger :
    ∃ c Z : ℝ, 0<c ∧ c≤1/4 ∧ 0<Z ∧ ∀ {Q : ℝ}, 2≤Q →
    ∃ e : Σ m : ℕ,DirichletCharacter ℂ m, (e.1=0 ∨ PageExceptionalCharacter Q c e.2) ∧
      ∀ {q : ℕ} [NeZero q],(q:ℝ)≤Q → ∀ {χ : DirichletCharacter ℂ q},
      (⟨χ.conductor,χ.primitiveCharacter⟩ : Σ m : ℕ,DirichletCharacter ℂ m) ≠ e →
      χ≠1 → ∀ N : ℕ, let x : ℝ := N+1/2
      let u := Real.sqrt (Real.log x)
      Real.exp 16≤x → Q+2≤Real.exp u →
      ‖psiChar x χ‖≤pageCharacterConstant c Z*x*Real.exp (-(c/256)*u) := by
  obtain ⟨c,hc,hc4,H⟩ := page_zeroFree_region_primitiveCharacter
  obtain ⟨Z,hZ,HZ⟩ := norm_logDeriv_LFunction_re_gt_one_le
  refine ⟨c,Z,hc,hc4,hZ,fun {Q} hQ => ?_⟩
  obtain ⟨e,he,hreg⟩ := H hQ
  exact ⟨e,he,fun {q} _ hq {χ} heχ hχ N => norm_psiChar_halfInteger_page hc hc4 hZ hQ hq hχ
    (HZ _) (fun hs => hreg hq heχ hχ hs) N⟩

/-- Uniform error for all partial sums up to `N`, with cutoffs below `Y`
handled by Chebyshev's elementary estimate. -/
def pagePartialError (N : ℕ) (Y c Z : ℝ) : ℝ :=
  max (7*Y) (2*pageCharacterConstant c Z*N*Real.exp (-(c/256)*Real.sqrt (Real.log Y)))

/-- The same exceptional primitive character works for every partial twisted
prime sum required by Abel summation on a major arc. -/
theorem page_psiChar_partial :
    ∃ c Z : ℝ, 0<c ∧ c≤1/4 ∧ 0<Z ∧ ∀ {Q : ℝ}, 2≤Q →
    ∃ e : Σ m : ℕ,DirichletCharacter ℂ m, (e.1=0 ∨ PageExceptionalCharacter Q c e.2) ∧
      ∀ {q : ℕ} [NeZero q], (q:ℝ)≤Q → ∀ {χ : DirichletCharacter ℂ q},
      (⟨χ.conductor,χ.primitiveCharacter⟩ : Σ m : ℕ,DirichletCharacter ℂ m) ≠ e → χ≠1 →
      ∀ {N k : ℕ} {Y : ℝ}, Real.exp 16≤Y → Q+2≤Real.exp (Real.sqrt (Real.log Y)) →
      k∈Icc 1 N → ‖psiChar k χ‖≤pagePartialError N Y c Z := by
  obtain ⟨c,Z,hc,hc4,hZ,H⟩ := page_psiChar_halfInteger
  refine ⟨c,Z,hc,hc4,hZ,fun {Q} hQ => ?_⟩
  obtain ⟨e,he,hh⟩ := H hQ
  refine ⟨e,he,fun {q} _ hq {χ} heχ hχ {N k} {Y} hY hQY hk => ?_⟩
  have hC := pageCharacterConstant_pos hc hZ
  obtain ⟨hk1,hkN⟩ := mem_Icc.mp hk
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk1
  have hkR : (k:ℝ)≤N := by exact_mod_cast hkN
  by_cases hsmall : (k:ℝ)≤Y
  · apply (norm_psiChar_le_const_mul_self (Nat.cast_nonneg k) χ).trans
    apply le_trans _ (le_max_left ..)
    have hl := Real.log_le_sub_one_of_pos (by norm_num : 0<(4:ℝ))
    nlinarith [mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α:=ℝ) k)]
  let x : ℝ := k+1/2
  have hx : Y≤x := by dsimp [x]; linarith
  have hY0 : 0<Y := (Real.exp_pos _).trans_le hY
  have hlog := Real.sqrt_le_sqrt (Real.log_le_log hY0 hx)
  have Hk := hh hq heχ hχ k (hY.trans hx) (hQY.trans (Real.exp_le_exp.mpr hlog))
  have hfloor : ⌊x⌋₊=k := (Nat.floor_eq_iff (by dsimp [x]; positivity)).2
    (by dsimp [x]; constructor <;> linarith)
  have hpsi : psiChar k χ = psiChar x χ := by simp only [psiChar,Nat.floor_natCast,hfloor]
  rw [hpsi]
  apply Hk.trans (le_trans _ (le_max_right ..))
  change pageCharacterConstant c Z*x*Real.exp (-(c/256)*Real.sqrt (Real.log x)) ≤ _
  apply mul_le_mul _ (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (by linarith)))
    (Real.exp_pos _).le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left (show x≤2*(N:ℝ) by dsimp [x]; linarith) hC.le]

/-- A reduced class progression bound with a uniform upper bound for the
nonprincipal character sums and an explicit correction from the principal character. -/
theorem abs_psiAP_sub_main_le_of_uniform_char {x E : ℝ} (hx : 1≤x) (hE : 0≤E)
    {q r : ℕ} (hq : 1≤q) (hr : r.Coprime q)
    (H : ∀ χ : DirichletCharacter ℂ q, χ≠1 → ‖psiChar x χ‖≤E) :
    |psiAP x q r-x/q.totient|≤
      (|Chebyshev.psi x-x|+Real.log q/Real.log 2*Real.log x)/q.totient+E := by
  let : NeZero q := ⟨by omega⟩
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  let F : Finset (DirichletCharacter ℂ q) := {(1 : DirichletCharacter ℂ q)}ᶜ
  have hcard : F.card≤q.totient := by
    simpa only [Fintype.card_eq_nat_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      using card_le_univ F
  have hsum : ∑ χ∈F, ‖psiChar x χ‖≤q.totient*E := calc
    _ ≤ ∑ _χ∈F,E := sum_le_sum fun χ h => H χ (by simpa [F] using h)
    _ = (F.card:ℝ)*E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE
  apply (abs_psiAP_sub_div_totient_le_sum_chars hx hq hr).trans
  calc
    _ ≤ (q.totient:ℝ)⁻¹*(|Chebyshev.psi x-x|+Real.log q/Real.log 2*Real.log x+q.totient*E) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity)
    _ = _ := by field_simp [hφ.ne']

/-- Page's progression estimate, uniformly in `1 ≤ k ≤ N` and in all levels
not divisible by the exceptional conductor. -/
theorem page_psiAP :
    ∃ c Z : ℝ, 0<c ∧ c≤1/4 ∧ 0<Z ∧ ∀ {Q : ℝ}, 2≤Q →
    ∃ d : ℕ, (d=0 ∨ ∃ χ : DirichletCharacter ℂ d,PageExceptionalCharacter Q c χ) ∧
      ∀ {q r N k : ℕ} {Y : ℝ}, 1≤q → (q:ℝ)≤Q → ¬d∣q → r.Coprime q →
      Real.exp 16≤Y → Q+2≤Real.exp (Real.sqrt (Real.log Y)) → k∈Icc 1 N →
      |psiAP k q r-k/q.totient|≤
        (|Chebyshev.psi k-k|+Real.log q/Real.log 2*Real.log k)/q.totient+
          pagePartialError N Y c Z := by
  obtain ⟨c,Z,hc,hc4,hZ,H⟩ := page_psiChar_partial
  refine ⟨c,Z,hc,hc4,hZ,fun {Q} hQ => ?_⟩
  obtain ⟨e,he,hh⟩ := H hQ
  refine ⟨e.1,he.imp_right (fun h => ⟨_,h⟩),fun {q r N k} {Y} hq hqQ hnd hr hY hQY hk => ?_⟩
  let : NeZero q := ⟨by omega⟩
  have hY0 : 0<Y := (Real.exp_pos _).trans_le hY
  apply abs_psiAP_sub_main_le_of_uniform_char (by exact_mod_cast (mem_Icc.mp hk).1)
    (le_trans (by positivity) (le_max_left ..)) hq hr
  intro χ hχ
  exact hh hqQ (fun he => hnd (congrArg Sigma.fst he ▸ χ.conductor_dvd_level)) hχ hY hQY hk

end AnalyticNumberTheory.PrimeDistribution
