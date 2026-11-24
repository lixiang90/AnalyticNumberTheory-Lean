import AnalyticNumberTheory.PrimeDistribution.LeastPrimeMomentZeros
import AnalyticNumberTheory.PrimeDistribution.DirichletZeroCountDensity

/-!
# The primitive-family moment inequality in Linnik's theorem

The primitive principal character supplies the main term. Orthogonality and
uniqueness of the inducing primitive character bound the total contribution
of the other moments by the weighted family of zeros up to height one.
-/
noncomputable section
open Finset Complex Real Metric Set
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

abbrev LinnikCharacterIndex := (q : ℕ) × DirichletCharacter ℂ q
abbrev LinnikZeroIndex := LinnikCharacterIndex × ℂ

/-- Primitive nonprincipal characters of modulus at most Q, paired with a
distinct strip zero of height at most one and real part at least σ. -/
def linnikZeroFamily (Q : ℕ) (σ : ℝ) : Finset LinnikZeroIndex :=
  (primitiveCharacterFamily Q).biUnion (fun p => ({p}:Finset LinnikCharacterIndex) ×ˢ nonprincipalDensityFinset p.2 σ 1)

@[simp] theorem mem_linnikZeroFamily {Q : ℕ} {σ : ℝ} {p : LinnikCharacterIndex} {z : ℂ} :
    (p,z)∈linnikZeroFamily Q σ ↔ p∈primitiveCharacterFamily Q ∧ z∈nonprincipalDensityFinset p.2 σ 1 := by
  simp [linnikZeroFamily]

theorem sum_linnikZeroFamily (Q : ℕ) (σ : ℝ) (f : LinnikZeroIndex → ℝ) :
    ∑ j ∈ linnikZeroFamily Q σ,f j =
      ∑ p ∈ primitiveCharacterFamily Q, ∑ z ∈ nonprincipalDensityFinset p.2 σ 1,f (p,z) := by
  rw [linnikZeroFamily,sum_biUnion]
  · apply sum_congr rfl; intro p hp; simp [sum_product]
  · intro a ha b hb h
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact h (((mem_singleton.mp (mem_product.mp hi).1).symm).trans (mem_singleton.mp (mem_product.mp hj).1))

/-- The finite weighted count is exactly the zero-density counting function. -/
theorem sum_linnikZeroMultiplicity (Q : ℕ) (σ : ℝ) :
    ∑ j ∈ linnikZeroFamily Q σ,(characterZeroMultiplicity j.1.2 j.2:ℝ) =
      primitiveFamilyZeroCount Q σ 1 := by
  rw [sum_linnikZeroFamily,primitiveFamilyZeroCount]; push_cast; rfl

private def inducingIndex {q : ℕ} (χ : DirichletCharacter ℂ q) : LinnikCharacterIndex :=
  ⟨χ.conductor,χ.primitiveCharacter⟩

private theorem inducingIndex_injective (q : ℕ) : Function.Injective (inducingIndex (q:=q)) := by
  intro χ ψ h
  let recover (p : LinnikCharacterIndex) : DirichletCharacter ℂ q :=
    if hp : p.1 ∣ q then p.2.changeLevel hp else 1
  have hrec (ξ : DirichletCharacter ℂ q) : recover (inducingIndex ξ) = ξ := by
    dsimp only [recover,inducingIndex]
    rw [dif_pos ξ.conductor_dvd_level]
    exact ξ.changeLevel_primitiveCharacter
  exact (hrec χ).symm.trans ((congrArg recover h).trans (hrec ψ))

private theorem inducingIndex_mem {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    inducingIndex χ ∈ primitiveCharacterFamily q := by
  refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero χ.conductor_ne_zero,Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level⟩,
    mem_filter.mpr ⟨mem_univ _,χ.primitiveCharacter_isPrimitive⟩⟩

theorem primitive_character_pair {q : ℕ} {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) :
    (⟨χ.conductor,χ.primitiveCharacter⟩ : LinnikCharacterIndex) = ⟨q,χ⟩ := by
  have transport {d n : ℕ} (hd : d=n) (ψ : DirichletCharacter ℂ d) :
      (⟨d,ψ⟩:LinnikCharacterIndex)=⟨n,ψ.changeLevel (dvd_of_eq hd)⟩ := by subst n; simp [DirichletCharacter.changeLevel_self]
  exact (transport hp χ.primitiveCharacter).trans (congrArg (Sigma.mk q) χ.changeLevel_primitiveCharacter)

private theorem principal_inducingIndex (q : ℕ) [NeZero q] :
    inducingIndex (1:DirichletCharacter ℂ q)=⟨1,1⟩ := by
  have hq := @DirichletCharacter.conductor_one ℂ _ q _
  have transport {d : ℕ} (hd : d=1) (χ : DirichletCharacter ℂ d) :
      (⟨d,χ⟩:LinnikCharacterIndex)=⟨1,1⟩ := by subst d; congr 1; exact Subsingleton.elim _ _
  exact transport hq _

private theorem moment_local_subset {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hχ : χ≠1) :
    leastPrimeMomentZeros (DirichletCharacter.LFunction χ) ⊆ nonprincipalDensityFinset χ 0 1 := by
  intro z hz
  let c := leastPrimeMomentCenter
  have hc : c.re=1+1/1024 := by norm_num [c,leastPrimeMomentCenter]
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c (3/4)) :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  obtain ⟨hb,hz'⟩ := (mem_leastPrimeMomentZeros hf (LFunction_ne_zero_on_re_one χ (by rw [hc]; norm_num) (.inl hχ))).mp hz
  have hd : ‖z-c‖≤3/8 := by simpa [c,mem_closedBall,dist_eq_norm] using hb
  have hre := (Complex.abs_re_le_norm (z-c)).trans hd; rw [Complex.sub_re,hc] at hre
  have him := (Complex.abs_im_le_norm (z-c)).trans hd
  rw [Complex.sub_im,show c.im=0 by norm_num [c,leastPrimeMomentCenter],sub_zero] at him
  have hzr : 0<z.re := by linarith [(abs_le.mp hre).1]
  exact (mem_nonprincipalDensityFinset χ).mpr ⟨hχ,hz',hzr,hzr.le,lt_of_not_ge (fun h => LFunction_ne_zero_on_re_one χ h (.inl hχ) hz'),by linarith⟩

/-- Global high-moment inequality for a reduced residue class. The zero sum
is over the full primitive family and counts zeros with their multiplicities. -/
theorem primitivePrimeMoment_family_lower :
    ∃ E r : ℝ, 0<E ∧ 0<r ∧ r<1 ∧ ∀ {q a : ℕ} [NeZero q] (ha : a.Coprime q) (m : ℕ),
      1 ≤ ‖∑ χ : DirichletCharacter ℂ q,star (χ a)*primitivePrimeMoment χ m‖ +
        E*r^m + (q:ℝ)*24*Real.log ((q:ℝ)+2)*(1/256:ℝ)^m +
        ∑ j ∈ linnikZeroFamily q 0,(characterZeroMultiplicity j.1.2 j.2:ℝ)*‖leastPrimeZeroRatio j.2‖^(m+1) := by
  obtain ⟨E,r,hE,hr,hr',hpr⟩ := principal_moment_one_bound
  refine ⟨E,r,hE,hr,hr',fun {q a} _ ha m => ?_⟩
  let P := (univ:Finset (DirichletCharacter ℂ q)).erase 1
  let K := 24*Real.log ((q:ℝ)+2)*(1/256:ℝ)^m
  let V := fun p : LinnikCharacterIndex => ∑ z ∈ nonprincipalDensityFinset p.2 0 1,
      (characterZeroMultiplicity p.2 z:ℝ)*‖leastPrimeZeroRatio z‖^(m+1)
  let H := fun χ : DirichletCharacter ℂ q => star (χ a)*primitivePrimeMoment χ m
  have hV (p : LinnikCharacterIndex) : 0≤V p := sum_nonneg (fun _ _ => by positivity)
  have hK : 0≤K := by dsimp [K]; have hl := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) q] : 1≤(q:ℝ)+2); positivity
  have hpr' : ‖H 1-1‖≤E*r^m := by
    have he := congrArg (fun p : LinnikCharacterIndex => ∑' n,turanMangoldtTerm p.2 (1/1024) 0 m n) (principal_inducingIndex q)
    change primitivePrimeMoment (1:DirichletCharacter ℂ q) m=_ at he
    dsimp only [H]; rw [show (1:DirichletCharacter ℂ q) a = 1 from MulChar.one_apply (ZMod.isUnit_iff_coprime _ _ |>.mpr ha),star_one,one_mul,he]
    exact hpr m
  have hlocal (χ : DirichletCharacter ℂ q) (hχ : χ∈P) : ‖H χ‖≤K+V (inducingIndex χ) := by
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hn : χ.primitiveCharacter≠1 := by
      intro he; have h := χ.changeLevel_primitiveCharacter
      rw [he,map_one] at h; exact (ne_of_mem_erase hχ) h.symm
    have h := nonprincipal_moment_zero_expansion hn m
    let Z := leastPrimeMomentZeros (DirichletCharacter.LFunction χ.primitiveCharacter)
    let F := ∑ z ∈ Z,(analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) z:ℂ)*leastPrimeZeroRatio z^(m+1)
    have hb : ‖F‖≤V (inducingIndex χ) := by
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_mul,Complex.norm_natCast,norm_pow]
      dsimp only [V,inducingIndex]
      simp only [characterZeroMultiplicity,dif_pos χ.conductor_ne_zero]
      exact sum_le_sum_of_subset_of_nonneg (moment_local_subset hn) (fun z _ _ => by positivity)
    have hd : 24*Real.log ((χ.conductor:ℝ)+2)*(1/256:ℝ)^m ≤ K := by
      dsimp [K]; gcongr; exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    change ‖primitivePrimeMoment χ m+F‖ ≤ _ at h
    have htri := norm_sub_le (primitivePrimeMoment χ m+F) F
    rw [add_sub_cancel_right] at htri
    dsimp only [H]; rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_char_le_one χ _)).trans (by linarith)
  have hsum : (∑ χ ∈ P,V (inducingIndex χ)) ≤ ∑ p ∈ primitiveCharacterFamily q,V p := by
    rw [←sum_image (inducingIndex_injective q).injOn]
    exact sum_le_sum_of_subset_of_nonneg (by intro p hp; obtain ⟨χ,_,rfl⟩ := mem_image.mp hp; exact inducingIndex_mem χ) (fun p _ _ => hV p)
  have hc : (P.card:ℝ)≤q := by
    have hcount : P.card ≤ Fintype.card (DirichletCharacter ℂ q) := P.card_le_univ
    rw [card_dirichletCharacter_eq_totient] at hcount; exact_mod_cast hcount.trans (Nat.totient_le q)
  have hP := (norm_sum_le P H).trans (sum_le_sum hlocal)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul] at hP
  have hmain : (1:ℝ) ≤ ‖∑ χ : DirichletCharacter ℂ q,H χ‖+‖∑ χ∈P,H χ‖+‖H 1-1‖ := by
    have h1 := norm_sub_le (H 1) (H 1-1)
    rw [sub_sub_cancel,norm_one] at h1
    have h2 := norm_sub_le (∑ χ : DirichletCharacter ℂ q,H χ) (∑ χ∈P,H χ)
    have he : (∑ χ : DirichletCharacter ℂ q,H χ)-(∑ χ∈P,H χ) = H 1 := by
      have := sum_erase_add univ H (mem_univ (1:DirichletCharacter ℂ q)); change (∑ χ∈P,H χ)+H 1=_ at this; rw [←this]; abel
    rw [he] at h2; linarith
  rw [sum_linnikZeroFamily]
  change 1≤ ‖∑ χ : DirichletCharacter ℂ q,H χ‖+ E*r^m + _ + ∑ p ∈ primitiveCharacterFamily q,V p
  have hcoef := mul_le_mul_of_nonneg_right hc hK
  dsimp only [K] at hP hcoef
  nlinarith only [hmain,hpr',hP,hsum,hcoef]

end AnalyticNumberTheory.PrimeDistribution
