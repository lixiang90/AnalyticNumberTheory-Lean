import AnalyticNumberTheory.DirichletLFunctions.ExceptionalCharacterRepulsion
import AnalyticNumberTheory.DirichletLFunctions.ConductorZeros

/-!
# Uniform zero repulsion for an entire family of Dirichlet characters

The exceptional and distinct-character estimates combine into a bound for all
primitive and induced targets in the open critical strip. The analytic scale
may be enlarged to a common upper bound across a family and a height range.
-/

noncomputable section
open Complex
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem repulsion_scale_mono {x y d δ : ℝ} (hx : 0<x) (hxy : x≤y)
    (hd : 0<d) (hδ : 0≤δ) (h : min (1/32) (Real.log (1/(d*x))/x) ≤ δ) :
    min (1/32) (Real.log (1/(d*y))/y) ≤ δ := by
  have hy := hx.trans_le hxy
  by_cases hn : 0≤Real.log (1/(d*y))
  · refine (min_le_min_left _ ?_).trans h
    calc
      _ ≤ Real.log (1/(d*y))/x := div_le_div_of_nonneg_left hn hx hxy
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hx.le
        apply Real.log_le_log (by positivity)
        exact one_div_le_one_div_of_le (mul_pos hd hx) (mul_le_mul_of_nonneg_left hxy hd.le)
  · exact (min_le_right _ _).trans ((div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) hy.le).trans hδ)

private theorem primitive_target_repulsion {d q : ℕ} [NeZero d] [NeZero q]
    {χ : DirichletCharacter ℂ d} {ψ : DirichletCharacter ℂ q}
    (hpχ : χ.IsPrimitive) (hpψ : ψ.IsPrimitive) (hr : IsReal χ) (hχ : χ≠1)
    {α : ℝ} {ρ : ℂ} (hzα : DirichletCharacter.LFunction χ (α:ℂ)=0) (hzρ : DirichletCharacter.LFunction ψ ρ=0)
    (hne : (⟨d,χ⟩ : Σ n : ℕ,DirichletCharacter ℂ n) ≠ ⟨q,ψ⟩ ∨ ρ≠(α:ℂ))
    {C D : ℝ} (hC : 0<C) (hD : 0<D)
    (hself : (riemannZeta ρ=0 ∨ DirichletCharacter.LFunction χ ρ=0 ∧ ρ≠(α:ℂ)) →
      let L := Real.log ((d:ℝ)*(|ρ.im|+2))
      min (1/32) (Real.log (1/(C*(1-α)*L))/(C*L)) ≤ 1-ρ.re)
    (hdist : ψ≠1 → (⟨d,χ⟩ : Σ n : ℕ,DirichletCharacter ℂ n) ≠ ⟨q,ψ⟩ →
      let L := Real.log ((d:ℝ)*q*(|ρ.im|+2))
      min (1/32) (Real.log (1/(D*(1-α)*L))/(D*L)) ≤ 1-ρ.re)
    {L : ℝ} (hL : Real.log ((d:ℝ)*q*(|ρ.im|+2))≤L) (hβ : ρ.re<1) :
    let A := max C D
    min (1/32) (Real.log (1/(A*(1-α)*L))/(A*L)) ≤ 1-ρ.re := by
  let ℓ := Real.log ((d:ℝ)*(|ρ.im|+2))
  let ℓ' := Real.log ((d:ℝ)*q*(|ρ.im|+2))
  have hd : (1:ℝ)≤d := by exact_mod_cast NeZero.pos d
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hl : 0<ℓ := by
    apply Real.log_pos
    nlinarith [abs_nonneg ρ.im,mul_nonneg (sub_nonneg.mpr hd) (abs_nonneg ρ.im)]
  have hll : ℓ≤ℓ' := by
    apply Real.log_le_log (by positivity)
    gcongr
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) hq
  have hkn : 0<1-α := sub_pos.mpr (lt_of_not_ge (fun h => LFunction_ne_zero_on_re_one χ (by simpa using h) (.inl hχ) hzα))
  have hm {X v : ℝ} (hX : 0<X) (hm : X≤max C D) (hv : 0<v) (hv' : v≤L)
      (hh : min (1/32) (Real.log (1/(X*(1-α)*v))/(X*v)) ≤ 1-ρ.re) :
      min (1/32) (Real.log (1/(max C D*(1-α)*L))/(max C D*L)) ≤ 1-ρ.re := by
    rw [show X*(1-α)*v=(1-α)*(X*v) by ring] at hh
    rw [show max C D*(1-α)*L=(1-α)*(max C D*L) by ring]
    exact repulsion_scale_mono (mul_pos hX hv) (mul_le_mul hm hv' hv.le (hX.trans_le hm).le)
      hkn (sub_nonneg.mpr hβ.le) hh
  by_cases hψ : ψ=1
  · have hq1 : q=1 := by rw [←hpψ,hψ,DirichletCharacter.conductor_one]
    subst q
    have hζ : riemannZeta ρ=0 := by simpa only [DirichletCharacter.LFunction_modOne_eq] using hzρ
    exact hm hC (le_max_left _ _) hl (hll.trans hL) (hself (.inl hζ))
  · by_cases he : (⟨d,χ⟩ : Σ n : ℕ,DirichletCharacter ℂ n) = ⟨q,ψ⟩
    · have hne' := hne.resolve_left (not_not_intro he)
      have heq : d=q := congrArg Sigma.fst he
      subst q
      have hχψ : χ=ψ := eq_of_heq (Sigma.mk.inj he).2
      have hfun : DirichletCharacter.LFunction χ=DirichletCharacter.LFunction ψ := congrArg DirichletCharacter.LFunction hχψ
      exact hm hC (le_max_left _ _) hl (hll.trans hL) (hself (.inr ⟨hfun.symm ▸ hzρ,hne'⟩))
    · exact hm hD (le_max_right _ _) (hl.trans_le hll) hL (hdist hψ he)

/-- **Family Deuring–Heilbronn theorem.** An exceptional real zero α of a
nonprincipal real primitive character χ repels every open-strip zero ρ of
every Dirichlet L-function ψ, apart from that same zero of the inducing
character. Only the conductor of ψ enters the lower threshold for the
analytic scale L. The same constant works when L is enlarged uniformly. -/
theorem deuring_heilbronn_family :
    ∃ A : ℝ, 0<A ∧ ∀ {d q : ℕ} [NeZero d] [NeZero q]
      {χ : DirichletCharacter ℂ d} (ψ : DirichletCharacter ℂ q),
      χ.IsPrimitive → IsReal χ → χ≠1 → ∀ {α : ℝ} {ρ : ℂ},
      DirichletCharacter.LFunction χ (α:ℂ)=0 → DirichletCharacter.LFunction ψ ρ=0 →
      0<ρ.re → ρ.re<1 →
      ((⟨d,χ⟩ : Σ n : ℕ,DirichletCharacter ℂ n) ≠ ⟨ψ.conductor,ψ.primitiveCharacter⟩ ∨ ρ≠(α:ℂ)) →
      ∀ {L : ℝ}, Real.log ((d:ℝ)*ψ.conductor*(|ρ.im|+2))≤L →
      min (1/32) (Real.log (1/(A*(1-α)*L))/(A*L)) ≤ 1-ρ.re := by
  obtain ⟨C,hC,hself⟩ := deuring_heilbronn_exceptional_character_and_zeta
  obtain ⟨D,hD,hdist⟩ := deuring_heilbronn_distinct_primitive
  refine ⟨max C D,hC.trans_le (le_max_left _ _),fun {d q} _ _ {χ} ψ hp hr hχ {α ρ} hzα hzρ hρ hρ' hne {L} hL => ?_⟩
  letI : NeZero ψ.conductor := ⟨fun h => NeZero.ne q (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp h)⟩
  have htrans := (LFunction_changeLevel_strip_zero_order ψ.conductor_dvd_level ψ.primitiveCharacter hρ hρ').1
  rw [ψ.changeLevel_primitiveCharacter] at htrans
  have hzp := htrans.mp hzρ
  exact primitive_target_repulsion hp ψ.primitiveCharacter_isPrimitive hr hχ hzα hzp hne hC hD
    (fun hh => hself hr hχ hzα hh) (fun hψ he => hdist hp ψ.primitiveCharacter_isPrimitive hr hχ hψ he hzα hzp) hL hρ'

end AnalyticNumberTheory.DirichletLFunctions
