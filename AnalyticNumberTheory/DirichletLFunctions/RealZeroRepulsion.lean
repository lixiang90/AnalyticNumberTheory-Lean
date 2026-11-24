import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-!
# Quantitative repulsion between real Dirichlet zeros

Estermann's positive four-character product compares the values at one to a
real zero of one factor. Applying the derivative bound at a real zero of each
factor gives a logarithmic repulsion estimate with a fifth power of the
conductor logarithm inside the logarithm. The estimate concerns real zeros
of distinct real primitive characters.
-/

noncomputable section
open Complex Set
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Estermann's Taylor estimate for the product of three nonprincipal L-functions
of real characters. A real zero of the second factor bounds the residue at one
from below. The Taylor truncation length grows logarithmically with the modulus. -/
theorem four_character_estermann_residue :
    ∃ K : ℝ, 0<K ∧ ∀ {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q},
      2 ≤ q → IsReal χ → IsReal ψ → χ ≠ 1 → ψ ≠ 1 → χ*ψ ≠ 1 →
      ∀ {β : ℝ}, 3/4 ≤ β → β < 1 → DirichletCharacter.LFunction ψ (β:ℂ) = 0 →
      1-β ≤ 2*‖DirichletCharacter.LFunction χ 1‖*‖DirichletCharacter.LFunction ψ 1‖*
        ‖DirichletCharacter.LFunction (χ*ψ) 1‖*Real.exp (K*Real.log ((q:ℝ)+2)*(1-β)) := by
  obtain ⟨E,hE,hest⟩ := exists_estermann_order_real_character_product
  let A : ℝ := 12*(E*1000^3+1)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hlog := Real.log_nonneg hA
  have hd := Real.log_pos (by norm_num : (1:ℝ)<6/5)
  let K := (Real.log A+6)/Real.log (6/5)+2
  refine ⟨K,by dsimp [K]; positivity,fun {q} _ {χ ψ} hq hrχ hrψ hχ hψ hprod {β} hβ hβ' hz => ?_⟩
  let F := fun z => DirichletCharacter.LFunction χ z*DirichletCharacter.LFunction ψ z*
    DirichletCharacter.LFunction (χ*ψ) z
  let B := (1000*(q:ℝ)^2)^3
  obtain ⟨N,_,hN,hh⟩ := hest hrχ hrψ hχ hψ hprod hβ hβ' hz
  change (N:ℝ) ≤ Real.log (12*(E*B+1))/Real.log (6/5)+2 at hN
  change (1/2:ℝ) ≤ (F 1).re*((2-β)^N/(1-β)) at hh
  let L := Real.log ((q:ℝ)+2)
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hL1 : 1 ≤ L := (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos _)
    (Real.exp_one_lt_d9.le.trans (by linarith)))
  have hq6 := one_le_pow₀ (by linarith : (1:ℝ) ≤ q) (n:=6)
  have harg : 12*(E*B+1) ≤ A*(q:ℝ)^6 := by dsimp [B,A]; nlinarith only [hq6]
  have hlogarg := Real.log_le_log (by dsimp [B]; positivity : 0<12*(E*B+1)) harg
  rw [Real.log_mul (x := A) (by positivity) (by positivity),Real.log_pow] at hlogarg
  have hN' : (N:ℝ) ≤ K*L := by
    have hqL : Real.log (q:ℝ) ≤ L := Real.log_le_log (by positivity) (by linarith)
    have h' := mul_le_mul_of_nonneg_left hL1 hlog
    dsimp only [K]
    apply hN.trans
    rw [add_mul,div_mul_eq_mul_div]
    calc
      _ ≤ ((Real.log A+6)*L)/Real.log (6/5)+2 := by
        gcongr
        norm_num at hlogarg
        nlinarith only [hlogarg,h',hqL]
      _ ≤ _ := by linarith
  have hpow : (2-β)^N ≤ Real.exp (K*L*(1-β)) := by
    calc
      _ ≤ (Real.exp (1-β))^N := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (1-β)]) _
      _ = Real.exp ((N:ℝ)*(1-β)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hN' (by linarith))
  have hh' : (1/2:ℝ)*(1-β) ≤ (F 1).re*(2-β)^N := by
    rw [← mul_div_assoc,le_div_iff₀ (by linarith)] at hh; exact hh
  have hnorm := Complex.re_le_norm (F 1)
  dsimp [F] at hnorm
  rw [norm_mul,norm_mul] at hnorm
  have hfinal := mul_le_mul hnorm hpow (pow_nonneg (by linarith) _) (by positivity)
  dsimp only [F] at hh'
  linarith

/-- A real zero bounds the value at one by its gap times the square of the
modulus logarithm. This estimate also covers real zeros of complex characters. -/
theorem norm_LFunction_one_le_real_zero_gap :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      2 ≤ q → χ ≠ 1 → ∀ {β : ℝ}, DirichletCharacter.LFunction χ (β:ℂ) = 0 →
        ‖DirichletCharacter.LFunction χ 1‖ ≤ C*(Real.log ((q:ℝ)+2))^2*(1-β) := by
  obtain ⟨D,hD,hd⟩ := norm_deriv_LFunction_near_one_le
  refine ⟨max D 8,lt_of_lt_of_le hD (le_max_left _ _),fun {q} _ {χ} hq hχ {β} hz => ?_⟩
  let L := Real.log ((q:ℝ)+2)
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hL : 0<L := Real.log_pos (by linarith)
  have hβ : β<1 := by
    by_contra! h
    exact LFunction_ne_zero_on_re_one χ (by simpa using h) (Or.inl hχ) hz
  by_cases hnear : 1-1/(4*L) ≤ β
  · let g := fun t : ℝ => DirichletCharacter.LFunction χ (t:ℂ)
    have hg (t : ℝ) : HasDerivAt g (deriv (DirichletCharacter.LFunction χ) (t:ℂ)) t :=
      (DirichletCharacter.differentiable_LFunction hχ _).hasDerivAt.comp_ofReal
    have hm := (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hg t).differentiableAt)
      (fun t ht => by rw [(hg t).deriv]; exact hd hq hχ t ht.1 ht.2)
      ⟨hnear,hβ.le⟩ ⟨by linarith [show 0<1/(4*L) by positivity],le_rfl⟩
    simp only [g,hz,sub_zero,Complex.ofReal_one,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hβ)] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) (by linarith))
  · have hh : 1/(4*L) ≤ 1-β := by linarith
    have h0 := norm_LFunction_one_le hχ
    change ‖DirichletCharacter.LFunction χ 1‖ ≤ 2*L at h0
    change _ ≤ max D 8*L^2*(1-β)
    calc
      _ ≤ 2*L := h0
      _ = 8*L^2*(1/(4*L)) := by field_simp; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg L)) hh
        (by positivity) (by have := le_max_right D (8:ℝ); positivity)

private theorem real_zero_repulsion_same_level :
    ∃ C K : ℝ, 0<C ∧ 0<K ∧ ∀ {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q},
      2 ≤ q → IsReal χ → IsReal ψ → χ ≠ 1 → ψ ≠ 1 → χ*ψ ≠ 1 →
      ∀ {α β : ℝ}, 3/4 ≤ β → DirichletCharacter.LFunction χ (α:ℂ)=0 →
        DirichletCharacter.LFunction ψ (β:ℂ)=0 →
        1 ≤ C*(1-α)*(Real.log ((q:ℝ)+2))^5*Real.exp (K*Real.log ((q:ℝ)+2)*(1-β)) := by
  obtain ⟨D,hD,hd⟩ := norm_LFunction_one_le_real_zero_gap
  obtain ⟨K,hK,hest⟩ := four_character_estermann_residue
  refine ⟨4*D^2,K,by positivity,hK,fun {q} _ {χ ψ} hq hrχ hrψ hχ hψ hp {α β} hlo hz1 hz2 => ?_⟩
  let L := Real.log ((q:ℝ)+2)
  have hgap {ξ : DirichletCharacter ℂ q} (hξ : ξ≠1) {u : ℝ}
      (hzu : DirichletCharacter.LFunction ξ (u:ℂ)=0) : u<1 := by
    by_contra! h
    exact LFunction_ne_zero_on_re_one ξ (by simpa using h) (Or.inl hξ) hzu
  have hα := hgap hχ hz1
  have hβ := hgap hψ hz2
  have h1 := hd hq hχ hz1
  have h2 := hd hq hψ hz2
  have h3 := norm_LFunction_one_le hp
  have h0 := hest hq hrχ hrψ hχ hψ hp hlo hβ hz2
  have hL : 0<L := Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) q])
  change 1 ≤ (4*D^2)*(1-α)*L^5*Real.exp (K*L*(1-β))
  apply le_of_mul_le_mul_right (a := 1-β) _ (sub_pos.mpr hβ)
  rw [one_mul]
  refine h0.trans ?_
  calc
    _ ≤ 2*(D*L^2*(1-α))*(D*L^2*(1-β))*(2*L)*Real.exp (K*L*(1-β)) := by gcongr
    _ = _ := by ring

/-- Quantitative real-zero Deuring–Heilbronn estimate, with a logarithmic
loss. For L = log(q₁q₂+2), the gap of a second real zero is at least
log(1/(C(1−α)L⁵))/(KL). Constants are absolute. -/
theorem real_zero_repulsion_logarithmic :
    ∃ C K : ℝ, 0<C ∧ 0<K ∧ ∀ {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
      {χ : DirichletCharacter ℂ q₁} {ψ : DirichletCharacter ℂ q₂},
      χ.IsPrimitive → ψ.IsPrimitive → IsReal χ → IsReal ψ → χ ≠ 1 → ψ ≠ 1 →
      (⟨q₁, χ⟩ : Σ q : ℕ, DirichletCharacter ℂ q) ≠ ⟨q₂, ψ⟩ →
      ∀ {α β : ℝ}, 3/4 ≤ β → DirichletCharacter.LFunction χ (α:ℂ)=0 →
      DirichletCharacter.LFunction ψ (β:ℂ)=0 →
      let L := Real.log ((q₁:ℝ)*q₂+2)
      Real.log (1/(C*(1-α)*L^5))/(K*L) ≤ 1-β := by
  obtain ⟨C,K,hC,hK,hrep⟩ := real_zero_repulsion_same_level
  refine ⟨C,K,hC,hK,fun {q₁ q₂} _ _ {χ ψ} hpχ hpψ hrχ hrψ hχ hψ hne {α β} hlo hz1 hz2 => ?_⟩
  let χ' := χ.changeLevel (dvd_mul_right q₁ q₂)
  let ψ' := ψ.changeLevel (dvd_mul_left q₂ q₁)
  obtain ⟨hχ',hψ',hp⟩ := changeLevel_ne_one_of_distinct_primitive hpχ hpψ hrχ hχ hψ hne
  have hz1' : DirichletCharacter.LFunction χ' (α:ℂ)=0 := by
    rw [LFunction_changeLevel_eq _ χ (Or.inl hχ),hz1,zero_mul]
  have hz2' : DirichletCharacter.LFunction ψ' (β:ℂ)=0 := by
    rw [LFunction_changeLevel_eq _ ψ (Or.inl hψ),hz2,zero_mul]
  have hq₁ : 2 ≤ q₁ := by
    by_contra! h
    have hh : q₁=1 := by have := NeZero.pos q₁; omega
    subst q₁
    exact hχ (Subsingleton.elim _ _)
  have hq : 2 ≤ q₁*q₂ := hq₁.trans (Nat.le_mul_of_pos_right _ (NeZero.pos q₂))
  have h := hrep hq (changeLevel_isReal _ hrχ) (changeLevel_isReal _ hrψ) hχ' hψ' hp hlo hz1' hz2'
  let L := Real.log ((q₁:ℝ)*q₂+2)
  have hL : 0<L := Real.log_pos (by linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) q₁) (Nat.cast_nonneg (α:=ℝ) q₂)])
  have hα : α<1 := by
    by_contra! h
    exact LFunction_ne_zero_on_re_one χ (by simpa using h) (Or.inl hχ) hz1
  push_cast at h
  change 1 ≤ C*(1-α)*L^5*Real.exp (K*L*(1-β)) at h
  have h0 : 0<C*(1-α)*L^5 := by positivity
  change Real.log (1/(C*(1-α)*L^5))/(K*L) ≤ 1-β
  rw [div_le_iff₀ (mul_pos hK hL),mul_comm (1-β)]
  exact (Real.log_le_iff_le_exp (by positivity)).mpr ((div_le_iff₀ h0).mpr (by linarith only [h,mul_comm (C*(1-α)*L^5) (Real.exp (K*L*(1-β)))]))

end AnalyticNumberTheory.DirichletLFunctions
