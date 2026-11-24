import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovBilinear

/-!
# The character large sieve on prime-supported coefficients

A primitive character of modulus q occurs at every enlarged modulus qd
with d squarefree and coprime to q. On integers coprime to qd induction
preserves its values. Character orthogonality at the enlarged modulus and
the exact imprimitive Gauss sum give the weight q/φ(qd), whose sum over d
gains a logarithm.
-/

noncomputable section
open Finset Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

private theorem norm_sq_cast (z : ℂ) : (‖z‖^2:ℝ) = (z * star z:ℂ) := by
  rw [RCLike.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow]

private theorem character_transform_parseval {q : ℕ} [NeZero q] (T : ℕ → ℂ) :
    let U := (range q).filter (fun c => c.Coprime q)
    (∑ χ : DirichletCharacter ℂ q, ‖∑ c ∈ U, star (χ c)*T c‖^2) =
      (q.totient:ℝ)*∑ c ∈ U,‖T c‖^2 := by
  intro U
  apply Complex.ofReal_injective
  push_cast only [Complex.ofReal_sum,Complex.ofReal_mul]
  simp_rw [norm_sq_cast,star_sum]
  simp_rw [sum_mul,mul_sum,star_mul,star_star]
  have h := fun (a b : ℂ) (u v : ℂ) => show star u*a*(star b*v)=(a*star b)*(v*star u) by ring
  simp_rw [h]
  rw [sum_comm]
  apply Eq.trans _ (by simp only [Complex.ofReal_natCast] : (∑ c ∈ U,(q.totient:ℂ)*(T c*star (T c))) = _)
  apply sum_congr rfl
  intro c hc
  rw [sum_comm]
  simp_rw [←mul_sum]
  simp_rw [sum_chars_nat_mul_conj_eq _ (mem_filter.mp hc).2]
  rw [sum_eq_single c]
  · simp [Nat.ModEq.refl,mul_comm]
  · intro d hd hn
    have hneq : ¬d≡c [MOD q] := fun he => hn (he.eq_of_lt_of_lt (mem_range.mp (mem_filter.mp hd).1) (mem_range.mp (mem_filter.mp hc).1))
    simp [hneq]
  · simp [hc]

private theorem amplified_gauss_transform {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (a : ℕ → ℂ) (M N : ℕ) (h : ∀ n ∈ Ioc M (M+N), a n≠0 → n.Coprime r) :
    (∑ n ∈ Ioc M (M+N), a n*χ n)*DirichletLFunctions.gaussSum (star χ) 1 =
      ∑ c ∈ (range r).filter (fun c => c.Coprime r), star (χ c)*trigPoly a M N ((c:ℝ)/r) := by
  rw [sum_mul]
  have he : ∀ n ∈ Ioc M (M+N), a n*χ n*DirichletLFunctions.gaussSum (star χ) 1 =
      ∑ c ∈ (range r).filter (fun c => c.Coprime r), star (χ c)*(a n*e ((c:ℝ)/r*n)) := by
    intro n hn
    by_cases hz : a n=0
    · simp [hz]
    have hg := gaussSum_eq_star_mul_of_coprime (star χ) (h n hn hz)
    simp only [MulChar.star_apply,star_star] at hg
    rw [mul_assoc,←hg,gaussSum_nat_eq_sum_range,mul_sum,sum_filter]
    apply sum_congr rfl
    intro c hc
    by_cases hcr : c.Coprime r
    · simp only [if_pos hcr,MulChar.star_apply,e]
      push_cast
      rw [show 2*(Real.pi:ℂ)*I*n*c/r=2*(Real.pi:ℂ)*((c:ℂ)/r*n)*I by ring]
      ring
    · have hχc := (char_nat_eq_zero_iff_not_coprime χ c).mpr hcr
      simp [hcr,hχc,MulChar.star_apply]
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl; intro c hc
  rw [trigPoly,mul_sum]

/-- The quadratic Gauss-sum weight at an enlarged modulus, divided by φ(r). -/
def inducedCharacterWeight (r : ℕ) (χ : DirichletCharacter ℂ r) : ℝ :=
  if Squarefree (r/χ.conductor) ∧ (r/χ.conductor).Coprime χ.conductor
    then (χ.conductor:ℝ)/r.totient else 0

theorem inducedCharacterWeight_nonneg {r : ℕ} (χ : DirichletCharacter ℂ r) :
    0 ≤ inducedCharacterWeight r χ := by unfold inducedCharacterWeight; split <;> positivity

private theorem gauss_weighted_character_identity (r : ℕ) (hr : 1≤r) (a : ℕ → ℂ) (M N : ℕ)
    (h : ∀ n ∈ Ioc M (M+N), a n≠0 → n.Coprime r) :
    (∑ χ : DirichletCharacter ℂ r, inducedCharacterWeight r χ*(‖∑ n ∈ Ioc M (M+N),a n*χ n‖^2)) =
      ∑ c ∈ (range r).filter (fun c => c.Coprime r), ‖trigPoly a M N ((c:ℝ)/r)‖^2 := by
  letI : NeZero r := ⟨by omega⟩
  have hp : (r.totient:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (by omega)).ne'
  apply (mul_left_cancel₀ hp)
  rw [← character_transform_parseval]
  rw [mul_sum]
  apply sum_congr rfl
  intro χ _
  rw [← amplified_gauss_transform χ a M N h,norm_mul,mul_pow,norm_gaussSum_one_eq,star_char_eq_inv,DirichletCharacter.conductor_inv]
  unfold inducedCharacterWeight
  split <;> simp [*,Real.sq_sqrt (Nat.cast_nonneg _),hp] <;> field_simp <;> ring

private abbrev CharacterIndex := (q : ℕ) × DirichletCharacter ℂ q

private def extendedIndex (p : CharacterIndex) (d : ℕ) : CharacterIndex :=
  ⟨p.1*d,p.2.changeLevel (dvd_mul_right p.1 d)⟩

private def extensions (Q Z : ℕ) : Finset ((p : CharacterIndex) × ℕ) :=
  (primitiveCharacterFamily Q).sigma (fun p => (Icc 1 Z).filter (fun d => Squarefree d ∧ d.Coprime p.1))

private theorem extendedIndex_injOn (Q Z : ℕ) :
    Set.InjOn (fun i : (p : CharacterIndex) × ℕ => extendedIndex i.1 i.2) (extensions Q Z) := by
  rintro ⟨⟨q,χ⟩,d⟩ hi ⟨⟨r,ψ⟩,e⟩ hj he
  obtain ⟨hp,hd⟩ := mem_sigma.mp hi
  obtain ⟨hp',he'⟩ := mem_sigma.mp hj
  obtain ⟨hq,hχ⟩ := mem_sigma.mp hp
  obtain ⟨hr,hψ⟩ := mem_sigma.mp hp'
  have hqp : 0<q := (mem_Icc.mp hq).1
  have hrp : 0<r := (mem_Icc.mp hr).1
  have hdp : 0<d := (mem_Icc.mp (mem_filter.mp hd).1).1
  have hep : 0<e := (mem_Icc.mp (mem_filter.mp he').1).1
  letI : NeZero (q*d) := ⟨Nat.mul_ne_zero hqp.ne' hdp.ne'⟩
  letI : NeZero (r*e) := ⟨Nat.mul_ne_zero hrp.ne' hep.ne'⟩
  have hqr := congrArg (fun p : CharacterIndex => p.2.conductor) he
  change (χ.changeLevel (dvd_mul_right q d)).conductor = (ψ.changeLevel (dvd_mul_right r e)).conductor at hqr
  rw [DirichletCharacter.conductor_changeLevel χ (dvd_mul_right q d),DirichletCharacter.conductor_changeLevel ψ (dvd_mul_right r e),
    (mem_filter.mp hχ).2,(mem_filter.mp hψ).2] at hqr
  change q=r at hqr
  subst r
  have hde : d=e := Nat.eq_of_mul_eq_mul_left hqp (congrArg Sigma.fst he : q*d=q*e)
  subst e
  have heq : χ.changeLevel (dvd_mul_right q d)=ψ.changeLevel (dvd_mul_right q d) := eq_of_heq (Sigma.mk.inj he).2
  have hχψ := DirichletCharacter.changeLevel_injective (dvd_mul_right q d) heq
  subst ψ; rfl

/-- Static prime-supported character large sieve. The loss in the Farey
cutoff is a factor Z, while the saving on the left is log Z. The support
condition also permits arbitrary integers coprime to every modulus ≤ QZ. -/
theorem sifted_character_large_sieve (a : ℕ → ℂ) (M : ℕ) {N Q Z : ℕ}
    (hN : 1≤N) (hQ : 1≤Q) (hZ : 1≤Z)
    (ha : ∀ n ∈ Ioc M (M+N), a n≠0 → ∀ r ∈ Icc 1 (Q*Z), n.Coprime r) :
    Real.log Z * (∑ p ∈ primitiveCharacterFamily Q, ‖∑ n ∈ Ioc M (M+N), a n*p.2 n‖^2) ≤
      ((N:ℝ)-1+((Q:ℝ)*Z)^2)*∑ n ∈ Ioc M (M+N),‖a n‖^2 := by
  let F := primitiveCharacterFamily Q
  let U := (Icc 1 (Q*Z)).sigma (fun r => (univ : Finset (DirichletCharacter ℂ r)))
  let A := fun p : CharacterIndex => ‖∑ n ∈ Ioc M (M+N),a n*p.2 n‖^2
  let V := fun p : CharacterIndex => inducedCharacterWeight p.1 p.2 * A p
  let E := extensions Q Z
  let g := fun i : (p : CharacterIndex) × ℕ => extendedIndex i.1 i.2
  have hZQ : 1≤Q*Z := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmem (i) (hi : i∈E) : g i ∈ U := by
    obtain ⟨hp,hd⟩ := mem_sigma.mp hi
    have hq := mem_Icc.mp (mem_sigma.mp hp).1
    have hs := mem_Icc.mp (mem_filter.mp hd).1
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq.1 hs.1,Nat.mul_le_mul hq.2 hs.2⟩,mem_univ _⟩
  have hval (p : CharacterIndex) (hp : p∈F) (d : ℕ) (hd : d∈(Icc 1 Z).filter (fun d => Squarefree d ∧ d.Coprime p.1)) :
      V (extendedIndex p d) = ((p.1:ℝ)/p.1.totient)*(d.totient:ℝ)⁻¹*A p := by
    obtain ⟨hq,hχ⟩ := mem_sigma.mp hp
    have hq' : 0<p.1 := (mem_Icc.mp hq).1
    have hd' : 0<d := (mem_Icc.mp (mem_filter.mp hd).1).1
    obtain ⟨hs,hcop⟩ := (mem_filter.mp hd).2
    letI : NeZero (p.1*d) := ⟨Nat.mul_ne_zero hq'.ne' hd'.ne'⟩
    have hc := DirichletCharacter.conductor_changeLevel p.2 (dvd_mul_right p.1 d)
    rw [(mem_filter.mp hχ).2] at hc
    have hv : A (extendedIndex p d)=A p := by
      dsimp only [A,extendedIndex]
      congr 2
      apply sum_congr rfl; intro n hn
      by_cases hzero : a n=0
      · simp [hzero]
      · have hh := ha n hn hzero (p.1*d) ((mem_sigma.mp (hmem ⟨p,d⟩ (mem_sigma.mpr ⟨hp,hd⟩))).1)
        congr 1
        simpa only [Int.cast_natCast] using DirichletCharacter.changeLevel_eq_cast_of_dvd' p.2 (dvd_mul_right _ d) (Nat.isCoprime_iff_coprime.mpr hh)
    dsimp only [V]; rw [hv]
    dsimp only [inducedCharacterWeight,extendedIndex]
    rw [hc,Nat.mul_div_cancel_left _ hq',if_pos ⟨hs,hcop⟩,Nat.totient_mul hcop.symm,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv]; ring
  have hamp : Real.log Z * (∑ p ∈ F,A p) ≤ ∑ i ∈ E,V (g i) := by
    rw [mul_sum]
    dsimp only [E,extensions]
    rw [sum_sigma]
    apply sum_le_sum
    intro p hp
    have hx : Real.log Z ≤ (p.1:ℝ)/p.1.totient * ∑ d ∈ (Icc 1 Z).filter (fun d => Squarefree d ∧ d.Coprime p.1), (d.totient:ℝ)⁻¹ := by
      have hfirst := sum_squarefree_inv_totient_ge_log (z:=(Z:ℝ)) (by exact_mod_cast hZ)
      simpa only [Nat.floor_natCast] using hfirst.trans (by simpa only [Nat.floor_natCast] using sum_squarefree_coprime_inv_totient_ge p.1 Z (mem_Icc.mp (mem_sigma.mp hp).1).1)
    calc
      _ ≤ ((p.1:ℝ)/p.1.totient * ∑ d ∈ (Icc 1 Z).filter (fun d => Squarefree d ∧ d.Coprime p.1), (d.totient:ℝ)⁻¹)*A p :=
        mul_le_mul_of_nonneg_right hx (sq_nonneg _)
      _ = _ := by rw [mul_sum,sum_mul]; apply sum_congr rfl; intro d hd; exact (hval p hp d hd).symm
  have hsub : E.image g ⊆ U := by intro i hi; obtain ⟨j,hj,rfl⟩ := mem_image.mp hi; exact hmem j hj
  have hg := Finset.sum_le_sum_of_subset_of_nonneg (f:=V) hsub (fun p _ _ => mul_nonneg (inducedCharacterWeight_nonneg _) (sq_nonneg _))
  rw [sum_image (extendedIndex_injOn Q Z)] at hg
  have hbound := hamp.trans hg
  dsimp only [U] at hbound
  rw [sum_sigma] at hbound
  refine hbound.trans ?_
  calc
    _ = ∑ r ∈ Icc 1 (Q*Z), ∑ c ∈ (range r).filter (fun c => c.Coprime r), ‖trigPoly a M N ((c:ℝ)/r)‖^2 := by
      apply sum_congr rfl
      intro r hr
      exact gauss_weighted_character_identity r (mem_Icc.mp hr).1 a M N (fun n hn h => ha n hn h r hr)
    _ ≤ _ := by simpa only [Nat.cast_mul] using farey_large_sieve a M hN hZQ

end AnalyticNumberTheory.SieveMethods
