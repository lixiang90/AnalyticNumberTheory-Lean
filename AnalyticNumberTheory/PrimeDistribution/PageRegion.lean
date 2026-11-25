import AnalyticNumberTheory.DirichletLFunctions.ConductorZeros
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-!
# Page's zero-free region outside one conductor

A single choice of exceptional conductor works at every height and for imprimitive
characters throughout the prescribed range of levels. The value zero encodes the
absence of an exceptional character.
-/

noncomputable section

open Complex Set AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- A primitive real character of this conductor has a zero in Page's interval. -/
def PageExceptionalCharacter (Q c : ℝ) {d : ℕ} (χ : DirichletCharacter ℂ d) : Prop :=
  ∃ _ : NeZero d, 2 ≤ d ∧ (d : ℝ) ≤ Q ∧
    χ.IsPrimitive ∧ IsReal χ ∧ χ ≠ 1 ∧
    ∃ β ∈ Icc (1 - c / Real.log (Q+2)) 1, DirichletCharacter.LFunction χ (β : ℂ) = 0

/-- Outside the characters induced by one primitive real character, every nonprincipal character is zero-free
in the classical logarithmic region. The exceptional conductor, when nonzero,
has a witnessing primitive character and real zero. -/
theorem page_zeroFree_region_primitiveCharacter :
    ∃ c : ℝ, 0<c ∧ c≤1/4 ∧ ∀ {Q : ℝ}, 2≤Q → ∃ e : Σ m : ℕ,DirichletCharacter ℂ m,
      (e.1=0 ∨ PageExceptionalCharacter Q c e.2) ∧
      ∀ {q : ℕ} [NeZero q], (q:ℝ)≤Q → ∀ {χ : DirichletCharacter ℂ q},
        (⟨χ.conductor,χ.primitiveCharacter⟩ : Σ m : ℕ,DirichletCharacter ℂ m) ≠ e → χ≠1 → ∀ {s : ℂ}, 1-c/Real.log ((Q+2)*(|s.im|+2))≤s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨a,ha,hzfr⟩ := zeroFreeRegion
  obtain ⟨b,_,hb,_,hpage⟩ := page_theorem
  let c := min a (min b (1/4))
  have hc : 0<c := lt_min ha (lt_min hb (by norm_num))
  have hca : c≤a := min_le_left ..
  have hcb : c≤b := (min_le_right ..).trans (min_le_left ..)
  have hc4 : c≤1/4 := (min_le_right ..).trans (min_le_right ..)
  refine ⟨c,hc,hc4,fun {Q} hQ => ?_⟩
  obtain ⟨exc,hexc⟩ := hpage Q hQ
  have hl : 1≤Real.log (Q+2) := (Real.le_log_iff_exp_le (by linarith)).mpr
    (Real.exp_one_lt_d9.le.trans (by linarith))
  have huniq {d : ℕ} {χ : DirichletCharacter ℂ d} (h : PageExceptionalCharacter Q c χ) :
      (⟨d,χ⟩ : Σ m : ℕ,DirichletCharacter ℂ m) = exc := by
    obtain ⟨hnz,hd,hdQ,hp,hr,hχ,β,hβ,hz⟩ := h
    by_contra hne
    exact (hexc hd hdQ hp hr hχ hne).1 β
      ⟨(sub_le_sub_left (div_le_div_of_nonneg_right hcb (by linarith : 0≤Real.log (Q+2))) 1).trans hβ.1,hβ.2⟩ hz
  obtain ⟨e,hd,hall⟩ : ∃ e : Σ m : ℕ,DirichletCharacter ℂ m,
      (e.1=0 ∨ PageExceptionalCharacter Q c e.2) ∧
      ∀ z : Σ m : ℕ,DirichletCharacter ℂ m, PageExceptionalCharacter Q c z.2 → z=e := by
    by_cases Hex : ∃ z : Σ m : ℕ,DirichletCharacter ℂ m, PageExceptionalCharacter Q c z.2
    · obtain ⟨z,hz⟩ := Hex
      exact ⟨z,Or.inr hz,fun z' hz' => (huniq hz').trans (huniq hz).symm⟩
    · exact ⟨⟨0,1⟩,Or.inl rfl,fun z hz => (Hex ⟨z,hz⟩).elim⟩
  refine ⟨e,hd,fun {q} _ hq {χ} hnd hχ {s} hs hz => ?_⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hcond : 3≤χ.conductor := three_le_conductor_of_ne_one hχ
  have hcQ : (χ.conductor:ℝ)≤Q := ((Nat.cast_le (α:=ℝ)).mpr
    (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)).trans hq
  have hp : χ.primitiveCharacter ≠ 1 := by
    intro he
    have he' := χ.changeLevel_primitiveCharacter
    rw [he,DirichletCharacter.changeLevel_one] at he'
    exact hχ he'.symm
  let L := Real.log ((Q+2)*(|s.im|+2))
  have hlL : Real.log (Q+2) ≤ L := Real.log_le_log (by linarith)
    (le_mul_of_one_le_right (by linarith) (by linarith [abs_nonneg s.im]))
  have hL : 1≤L := hl.trans hlL
  have hs0 : 0<s.re := by
    change 1-c/L≤s.re at hs
    linarith [(div_le_self hc.le hL).trans hc4]
  have hs1 : s.re<1 := lt_of_not_ge fun hh =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hh hz
  have htrans := (LFunction_changeLevel_strip_zero_order χ.conductor_dvd_level
    χ.primitiveCharacter hs0 hs1).1
  rw [χ.changeLevel_primitiveCharacter] at htrans
  have hzp := htrans.mp hz
  have hplog : 0<Real.log ((χ.conductor:ℝ)*(|s.im|+2)) := Real.log_pos (by
    have h3 : (3:ℝ)≤χ.conductor := by exact_mod_cast hcond
    nlinarith [abs_nonneg s.im])
  have hple : Real.log ((χ.conductor:ℝ)*(|s.im|+2)) ≤ L :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hwidth : c/L ≤ a/Real.log ((χ.conductor:ℝ)*(|s.im|+2)) :=
    div_le_div₀ ha.le hca hplog hple
  obtain ⟨hr,_,hi,_,_,_⟩ := hzfr χ.primitiveCharacter s (.inl hp)
    ((sub_le_sub_left hwidth 1).trans hs) hzp
  have hreal : (s.re:ℂ)=s := Complex.ext rfl (by simpa using hi.symm)
  have hcβ : 1-c/Real.log (Q+2) ≤ s.re :=
    (sub_le_sub_left (div_le_div_of_nonneg_left hc.le (by linarith) hlL) 1).trans hs
  have he : PageExceptionalCharacter Q c χ.primitiveCharacter :=
    ⟨inferInstance,by omega,hcQ,χ.primitiveCharacter_isPrimitive,hr,hp,s.re,
      ⟨hcβ,hs1.le⟩,by rwa [hreal]⟩
  exact hnd (hall _ he)

/-- In particular, the whole logarithmic region is zero-free at every level
which is not a multiple of the exceptional conductor. -/
theorem page_zeroFree_region :
    ∃ c : ℝ, 0<c ∧ c≤1/4 ∧ ∀ {Q : ℝ}, 2≤Q → ∃ d : ℕ,
      (d=0 ∨ ∃ χ : DirichletCharacter ℂ d, PageExceptionalCharacter Q c χ) ∧
      ∀ {q : ℕ} [NeZero q], (q:ℝ)≤Q → ¬d∣q → ∀ {χ : DirichletCharacter ℂ q},
        χ≠1 → ∀ {s : ℂ}, 1-c/Real.log ((Q+2)*(|s.im|+2))≤s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c,hc,hc4,H⟩ := page_zeroFree_region_primitiveCharacter
  refine ⟨c,hc,hc4,fun {Q} hQ => ?_⟩
  obtain ⟨e,he,hz⟩ := H hQ
  refine ⟨e.1,he.imp_right (fun h => ⟨e.2,h⟩),fun {q} _ hq hnd {χ} hχ {s} hs => ?_⟩
  apply hz hq _ hχ hs
  intro h
  exact hnd (congrArg Sigma.fst h ▸ χ.conductor_dvd_level)

end AnalyticNumberTheory.PrimeDistribution
