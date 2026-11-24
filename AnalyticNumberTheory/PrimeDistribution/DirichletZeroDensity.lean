import AnalyticNumberTheory.PrimeDistribution.DirichletZeroDetector
import AnalyticNumberTheory.PrimeDistribution.CharacterPolynomialSampling
import AnalyticNumberTheory.PrimeDistribution.ZeroDetectorBlocks
import AnalyticNumberTheory.DirichletLFunctions.ZeroExpansion

/-!
# Zero density in families of primitive Dirichlet characters

The hybrid large sieve and a finite Möbius detector give a power-saving bound
for the sum of zero counts over all nonprincipal primitive characters up to
modulus `Q`. Each character may contribute any finite set of distinct zeros.
-/

noncomputable section

open Finset Complex
open scoped Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

open ZeroDetector

private abbrev CharIndex := (q : ℕ) × DirichletCharacter ℂ q

private lemma modulus_mem {p : CharIndex} {Q : ℕ} (hp : p ∈ primitiveCharacterFamily Q) :
    1 ≤ p.1 ∧ p.1 ≤ Q := mem_Icc.mp (mem_sigma.mp hp).1

private theorem family_zeroDensity_at_cutoff {Q T X : ℕ} (hQ : 1 ≤ Q) (hT : 1 ≤ T)
    (hX : (16*Q*(T+1))^4 ≤ X)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (3/4:ℝ) 1) (S : CharIndex → Finset ℂ)
    (hS : ∀ (p : CharIndex) [NeZero p.1], p ∈ primitiveCharacterFamily Q → ∀ z ∈ S p,
      p.2 ≠ 1 ∧ DirichletCharacter.LFunction p.2 z = 0 ∧
      σ ≤ z.re ∧ z.re < 1 ∧ 0 ≤ z.im ∧ z.im < T) :
    ∑ p ∈ primitiveCharacterFamily Q, ((S p).card : ℝ) ≤
      (100*(18*(4*Real.pi^3)*3^7*jensenUnitZeroDensityConst)) *
      (1+Real.log X)^10 * (X:ℝ)^(4*(1-σ)) := by
  let F := primitiveCharacterFamily Q
  let J := blocks X
  let ℓ := 1+Real.log X
  let K := jensenUnitZeroDensityConst
  let D := 18*(4*Real.pi^3)*3^7*K
  let V := (X:ℝ)^(4*(1-σ))
  let P (i : ℕ) (p : CharIndex) (z : ℂ) := dirichletPoly (fun n => blockCoeff X i n*p.2 n) (2*2^i) z
  have hA : 1 ≤ 16*Q*(T+1) := Nat.mul_pos (Nat.mul_pos (by decide) hQ) (Nat.succ_pos _)
  have hX1 : 1 ≤ X := (Nat.one_le_pow _ _ hA).trans hX
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX1
  have hℓ : 1 ≤ ℓ := by dsimp only [ℓ]; linarith [Real.log_nonneg hXr]
  have hK : 0 ≤ K := jensenUnitZeroDensityConst_pos.le
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hQT : Q*(T+1) ≤ X := by
    have hpow := Nat.le_self_pow (by decide : 4 ≠ 0) (16*Q*(T+1))
    exact (Nat.mul_le_mul_right _ (by omega : Q ≤ 16*Q)).trans (hpow.trans hX)
  have hcond : (Q:ℝ)^2*T ≤ X := by
    have ha : (1:ℝ) ≤ Q := by exact_mod_cast hQ
    have hb : (1:ℝ) ≤ T := by exact_mod_cast hT
    have hx : (16*(Q:ℝ)*(T+1))^4 ≤ X := by exact_mod_cast hX
    apply le_trans _ hx
    calc
      (Q:ℝ)^2*T ≤ (16*(Q:ℝ)*(T+1))^2 := by nlinarith [sq_nonneg (Q*(T:ℝ))]
      _ ≤ _ := pow_le_pow_right₀ (by nlinarith) (by decide)
  have hcut : 16*(Q:ℝ)*(T+1) ≤ (X:ℝ)^(1/4:ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (16*(Q:ℝ)*(T+1))^4)
      (by exact_mod_cast hX : (16*(Q:ℝ)*(T+1))^4 ≤ X) (by norm_num : (0:ℝ) ≤ 1/4)
    simpa only [←Real.rpow_natCast (16*(Q:ℝ)*(T+1)) 4, ←Real.rpow_mul (by positivity : 0 ≤ 16*(Q:ℝ)*(T+1)),
      Nat.cast_ofNat, show (4:ℝ)*(1/4) = 1 by norm_num, Real.rpow_one] using hh
  have hre (p : CharIndex) (hp : p ∈ F) (z : ℂ) (hz : z ∈ S p) : z.re ∈ Set.Icc σ (σ+1) := by
    let : NeZero p.1 := ⟨Nat.ne_of_gt (modulus_mem hp).1⟩
    obtain ⟨_,_,hzσ,hz₁,_⟩ := hS p hp z hz
    exact ⟨hzσ,by linarith [hσ.1]⟩
  have him (p : CharIndex) (hp : p ∈ F) (z : ℂ) (hz : z ∈ S p) : 0 ≤ z.im ∧ z.im < T := by
    let : NeZero p.1 := ⟨Nat.ne_of_gt (modulus_mem hp).1⟩
    exact (hS p hp z hz).2.2.2.2
  have hcount (p : CharIndex) (hp : p ∈ F) (j : ℕ) (hj : j < T) :
      (((S p).filter (fun z => ⌊z.im⌋₊=j)).card : ℝ) ≤ K*ℓ := by
    let : NeZero p.1 := ⟨Nat.ne_of_gt (modulus_mem hp).1⟩
    by_cases hχ : p.2 = 1
    · have he : S p = ∅ := eq_empty_iff_forall_notMem.mpr fun z hz => (hS p hp z hz).1 hχ
      simp [he]; positivity
    have hb := finset_card_zeros_unit_interval_le hχ (j:ℝ)
      (S:=(S p).filter (fun z => ⌊z.im⌋₊=j)) (by
        intro z hz
        obtain ⟨hzz,hjz⟩ := mem_filter.mp hz
        obtain ⟨_, hz0, hr, hr1, ht, _⟩ := hS p hp z hzz
        have hlow := Nat.floor_le ht
        have hhigh := Nat.lt_floor_add_one z.im
        rw [hjz] at hlow hhigh
        exact ⟨by linarith [hσ.1],hr1,hlow,hhigh.le,hz0⟩)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hK
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have harg : (p.1:ℝ)*(j+2) ≤ X := by
      exact_mod_cast (Nat.mul_le_mul (modulus_mem hp).2 (by omega : j+2 ≤ T+1)).trans hQT
    have hpq : 0 < (p.1:ℝ) := by exact_mod_cast (modulus_mem hp).1
    exact (Real.log_le_log (by positivity) harg).trans (by dsimp only [ℓ]; linarith)
  have heach (p : CharIndex) (hp : p ∈ F) (z : ℂ) (hz : z ∈ S p) :
      (1:ℝ)/4 ≤ (J.card:ℝ)*∑ i ∈ J, ‖P i p z‖^2 := by
    let : NeZero p.1 := ⟨Nat.ne_of_gt (modulus_mem hp).1⟩
    obtain ⟨hχ,hz₀,hzσ,hr,ht,ht₁⟩ := hS p hp z hz
    have hsr := hσ.1.trans hzσ
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg (by linarith : 0 ≤ z.re), abs_of_nonneg ht] at hnorm
    have hsdiv : ‖z‖/z.re ≤ 2*(T+1) := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsr (by positivity : 0≤2*((T:ℝ)+1))]
    have hq : (p.1:ℝ) ≤ Q := by exact_mod_cast (modulus_mem hp).2
    have hd := dirichletDetector_large_at_zero hχ hX1 hsr hz₀ (by
      apply le_trans _ hcut
      calc
        4*(p.1:ℝ)*(1+‖z‖/z.re) ≤ 4*(Q:ℝ)*(1+2*((T:ℝ)+1)) := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) Q) (Nat.cast_nonneg (α:=ℝ) T)])
    rw [tail_twist_by_blocks (fun n : ℕ => p.2 n)] at hd
    have hn : 1/2 ≤ ∑ i ∈ J, ‖P i p z‖ := hd.trans (norm_sum_le ..)
    have hcs := sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun i => ‖P i p z‖)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
    exact (by nlinarith [pow_le_pow_left₀ (by norm_num : 0≤(1/2:ℝ)) hn 2] :
      1/4 ≤ (∑ i ∈ J, ‖P i p z‖)^2).trans hcs
  have hblock (i : ℕ) (hi : i ∈ J) : ∑ p ∈ F, ∑ z ∈ S p, ‖P i p z‖^2 ≤ D*ℓ^8*V := by
    let M := 2^i
    have hm : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
    have hs := dirichletPoly_character_sampling_strip (Q:=Q) (N:=2*M) (L:=T)
      hT (by omega) S (K:=K*ℓ) (by positivity) hre him hcount (blockCoeff X i)
    apply hs.trans
    have hxm : (X:ℝ) ≤ 2*M := by exact_mod_cast (mem_filter.mp hi).2.1.le
    have hlen : Real.pi^3 * ((2*M:ℕ)+(Q:ℝ)^2*T) ≤ (4*Real.pi^3)*(M:ℝ) := by
      push_cast
      calc
        _ ≤ Real.pi^3*(2*M+2*M) := mul_le_mul_of_nonneg_left (add_le_add_right (hcond.trans hxm) _) (by positivity)
        _ = _ := by ring
    have h := block_bound hX1 hi hσ hK (show 0 ≤ 4*Real.pi^3 by positivity) (by positivity) hlen
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
  have hsums := sum_le_sum fun p hp => sum_le_sum (heach p hp)
  simp only [sum_const,nsmul_eq_mul,←mul_sum,←sum_mul] at hsums
  have hswap : (∑ p ∈ F, ∑ z ∈ S p, ∑ i ∈ J, ‖P i p z‖^2) =
      ∑ i ∈ J, ∑ p ∈ F, ∑ z ∈ S p, ‖P i p z‖^2 := by
    rw [sum_comm (s:=J) (t:=F)]
    exact sum_congr rfl fun _ _ => sum_comm
  rw [hswap] at hsums
  have hb := hsums.trans (mul_le_mul_of_nonneg_left (sum_le_sum hblock) (Nat.cast_nonneg _))
  simp only [sum_const,nsmul_eq_mul] at hb
  have hJ : (J.card:ℝ) ≤ 5*ℓ := block_count_le hX1
  have hbound : (J.card:ℝ)*((J.card:ℝ)*(D*ℓ^8*V)) ≤ (5*ℓ)*((5*ℓ)*(D*ℓ^8*V)) := by gcongr
  change (∑ p ∈ F, ((S p).card:ℝ)) ≤ 100*D*ℓ^10*V
  nlinarith only [hb.trans hbound]

/-- Upper-half-plane zero-density bound for nonprincipal primitive characters of
modulus at most `Q`, uniform in any finite sets of distinct zeros. -/
theorem dirichlet_family_zeroDensity_upper :
    ∃ C > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ : ℝ}, 0 ≤ T → σ ∈ Set.Icc (3/4:ℝ) 1 →
    ∀ S : ((q : ℕ) × DirichletCharacter ℂ q) → Finset ℂ,
      (∀ (p : (q : ℕ) × DirichletCharacter ℂ q) [NeZero p.1], p ∈ primitiveCharacterFamily Q →
        ∀ z ∈ S p, p.2 ≠ 1 ∧ DirichletCharacter.LFunction p.2 z = 0 ∧
          σ ≤ z.re ∧ z.re < 1 ∧ 0 ≤ z.im ∧ z.im ≤ T) →
      ∑ p ∈ primitiveCharacterFamily Q, ((S p).card:ℝ) ≤
        C*(1+Real.log ((Q:ℝ)*(T+2)))^10*((Q:ℝ)*(T+2))^(16*(1-σ)) := by
  let D := 100*(18*(4*Real.pi^3)*3^7*jensenUnitZeroDensityConst)
  have hD : 0 < D := by have := jensenUnitZeroDensityConst_pos; dsimp only [D]; positivity
  refine ⟨D*65^10*16^4, by positivity, ?_⟩
  intro Q hQ T σ hT hσ S hS
  let U := ⌊T⌋₊+1
  let X := (16*Q*(U+1))^4
  let Y := (Q:ℝ)*(T+2)
  have hU : 1 ≤ U := Nat.succ_pos _
  have hQ' : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hY : 1 ≤ Y := by dsimp [Y]; nlinarith
  have hY₀ : 0 < Y := by linarith
  have hLY := Real.log_nonneg hY
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (Nat.mul_pos (Nat.mul_pos (by decide) hQ) (Nat.succ_pos _))
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX1
  have hYcmp : (16*(Q:ℝ)*(U+1)) ≤ 16*Y := by
    change _ ≤ 16*((Q:ℝ)*(T+2))
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp only [U]; push_cast; linarith [Nat.floor_le hT]
  have hXcmp : (X:ℝ) ≤ (16*Y)^4 := by
    dsimp only [X]; push_cast; gcongr
  have hlogcmp : 1+Real.log X ≤ 65*(1+Real.log Y) := by
    have h := Real.log_le_log (by linarith : 0<(X:ℝ)) hXcmp
    rw [Real.log_pow,Real.log_mul (by norm_num) hY₀.ne'] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<16)]
  have he : 0 ≤ 4*(1-σ) := by linarith [hσ.2]
  have hpowcmp : (X:ℝ)^(4*(1-σ)) ≤ 16^4*Y^(16*(1-σ)) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hXcmp he).trans
    rw [←Real.rpow_natCast (16*Y) 4, ←Real.rpow_mul (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [show 4*(4*(1-σ)) = 16*(1-σ) by ring, Real.mul_rpow (by norm_num) hY₀.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY₀.le _)
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 16)
      (by linarith [hσ.1] : 16*(1-σ) ≤ 4)).trans_eq (by norm_num)
  have hz := family_zeroDensity_at_cutoff (X:=X) hQ hU le_rfl hσ S (by
    intro p _ hp z hz
    obtain ⟨hχ,hr,hσz,hzr,hi,hti⟩ := hS p hp z hz
    exact ⟨hχ,hr,hσz,hzr,hi,hti.trans_lt (by simpa [U] using Nat.lt_floor_add_one T)⟩)
  apply hz.trans
  change D*(1+Real.log X)^10*(X:ℝ)^(4*(1-σ)) ≤ D*65^10*16^4*(1+Real.log Y)^10*Y^(16*(1-σ))
  calc
    _ ≤ D*(65*(1+Real.log Y))^10*(16^4*Y^(16*(1-σ))) := by
      apply mul_le_mul _ hpowcmp (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hXr]) hlogcmp _
    _ = _ := by ring

private def starIndex (p : CharIndex) : CharIndex := ⟨p.1,star p.2⟩

private lemma starIndex_involutive (p : CharIndex) : starIndex (starIndex p) = p := by
  rcases p with ⟨q,χ⟩
  apply congrArg (Sigma.mk q)
  exact (star_char_eq_inv (star χ)).trans ((congrArg Inv.inv (star_char_eq_inv χ)).trans (inv_inv χ))

private lemma starIndex_mem {Q : ℕ} {p : CharIndex} (hp : p ∈ primitiveCharacterFamily Q) :
    starIndex p ∈ primitiveCharacterFamily Q := by
  let : NeZero p.1 := ⟨Nat.ne_of_gt (modulus_mem hp).1⟩
  obtain ⟨hq,hχ⟩ := mem_sigma.mp hp
  have hprim : (star p.2).IsPrimitive := isPrimitive_star (mem_filter.mp hχ).2
  exact mem_sigma.mpr ⟨hq, mem_filter.mpr ⟨mem_univ _,hprim⟩⟩

private lemma sum_starIndex {Q : ℕ} (f : CharIndex → ℝ) :
    ∑ p ∈ primitiveCharacterFamily Q, f (starIndex p) = ∑ p ∈ primitiveCharacterFamily Q, f p := by
  refine sum_bij (fun p _ => starIndex p) (fun _ => starIndex_mem) ?_ ?_ (fun _ _ => rfl)
  · intro p _ r _ h; simpa only [starIndex_involutive] using congrArg starIndex h
  · intro p hp; exact ⟨starIndex p,starIndex_mem hp,starIndex_involutive p⟩

/-- A power-saving zero-density theorem for the family of all primitive
nonprincipal characters up to modulus `Q`, with both signs of the ordinate. -/
theorem dirichlet_family_zeroDensity :
    ∃ C > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ : ℝ}, 0 ≤ T → σ ∈ Set.Icc (3/4:ℝ) 1 →
    ∀ S : ((q : ℕ) × DirichletCharacter ℂ q) → Finset ℂ,
      (∀ (p : (q : ℕ) × DirichletCharacter ℂ q) [NeZero p.1], p ∈ primitiveCharacterFamily Q →
        ∀ z ∈ S p, p.2 ≠ 1 ∧ DirichletCharacter.LFunction p.2 z = 0 ∧
          σ ≤ z.re ∧ z.re < 1 ∧ |z.im| ≤ T) →
      ∑ p ∈ primitiveCharacterFamily Q, ((S p).card:ℝ) ≤
        C*(1+Real.log ((Q:ℝ)*(T+2)))^10*((Q:ℝ)*(T+2))^(16*(1-σ)) := by
  obtain ⟨C,hC,H⟩ := dirichlet_family_zeroDensity_upper
  refine ⟨2*C,by positivity,?_⟩
  intro Q hQ T σ hT hσ S hS
  let U (p : CharIndex) := (S p).filter fun z => 0 ≤ z.im
  let L (p : CharIndex) := (S p).filter fun z => ¬ 0 ≤ z.im
  let V (p : CharIndex) := (L (starIndex p)).image (starRingEnd ℂ)
  have hU := H hQ hT hσ U (by
    intro p _ hp z hz
    obtain ⟨hs,ht⟩ := mem_filter.mp hz
    obtain ⟨hχ,hzero,hr,hr',hi⟩ := hS p hp z hs
    exact ⟨hχ,hzero,hr,hr',ht,(abs_le.mp hi).2⟩)
  have hV := H hQ hT hσ V (by
    intro p _ hp z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    obtain ⟨hw',hn⟩ := mem_filter.mp hw
    let : NeZero (starIndex p).1 := ‹NeZero p.1›
    obtain ⟨hχ,hzero,hr,hr',hi⟩ := hS (starIndex p) (starIndex_mem hp) w hw'
    change star p.2 ≠ 1 at hχ
    have hχ' : p.2 ≠ 1 := fun e => hχ (by simp [e])
    have hc := LFunction_star_conj hχ w
    simp only [star_star] at hc
    change DirichletCharacter.LFunction (star p.2) w = 0 at hzero
    rw [hzero,map_zero] at hc
    exact ⟨hχ',hc,by simpa using hr,by simpa using hr',by simp; linarith,
      by simp; linarith [(abs_le.mp hi).1]⟩)
  have hvcard (p : CharIndex) : (V p).card = (L (starIndex p)).card :=
    card_image_of_injective _ (starRingEnd ℂ).injective
  simp only [hvcard] at hV
  rw [sum_starIndex (fun p => ((L p).card:ℝ))] at hV
  have hsplit (p : CharIndex) : ((S p).card:ℝ) = (U p).card + (L p).card := by
    exact_mod_cast (card_filter_add_card_filter_not (s:=S p) (fun z => 0 ≤ z.im)).symm
  simp_rw [hsplit]
  rw [sum_add_distrib]
  linarith only [add_le_add hU hV]

end AnalyticNumberTheory.PrimeDistribution
