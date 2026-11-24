import AnalyticNumberTheory.PrimeDistribution.DirichletZeroDensity

/-!
# Counting zeros of primitive Dirichlet characters with multiplicity

The count includes both signs of the ordinate and excludes the principal
character. A local Jensen bound supplies one additional logarithm for multiplicity.
-/

noncomputable section

open Finset Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

/-- Critical-strip zeros of a nonprincipal character with `σ ≤ Re ρ` and
`|Im ρ| ≤ T`. The modulus-zero and principal-character cases contribute the empty set. -/
def nonprincipalDensityFinset {q : ℕ} (χ : DirichletCharacter ℂ q) (σ T : ℝ) : Finset ℂ :=
  if h : q ≠ 0 then
    let : NeZero q := ⟨h⟩
    if χ = 1 then ∅ else (criticalStripZeroFinset χ (-T) T).filter (fun z => σ ≤ z.re)
  else ∅

/-- Membership in the family count for positive modulus. -/
@[simp] lemma mem_nonprincipalDensityFinset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ T : ℝ} {z : ℂ} : z ∈ nonprincipalDensityFinset χ σ T ↔
      χ ≠ 1 ∧ DirichletCharacter.LFunction χ z = 0 ∧ 0 < z.re ∧ σ ≤ z.re ∧ z.re < 1 ∧ |z.im| ≤ T := by
  by_cases hχ : χ = 1
  · simp [nonprincipalDensityFinset,NeZero.ne q,hχ]
  · simp [nonprincipalDensityFinset,NeZero.ne q,hχ,abs_le]
    tauto

/-- Multiplicity of a zero of a Dirichlet L-function. The modulus-zero convention
lets one sum directly over a finite family indexed by arbitrary natural moduli. -/
def characterZeroMultiplicity {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℂ) : ℕ :=
  if h : q ≠ 0 then
    let : NeZero q := ⟨h⟩
    analyticOrderNatAt (DirichletCharacter.LFunction χ) z
  else 0

/-- The total number of zeros with multiplicity in the symmetric strip for
nonprincipal primitive characters of all moduli up to `Q`. -/
def primitiveFamilyZeroCount (Q : ℕ) (σ T : ℝ) : ℕ :=
  ∑ p ∈ primitiveCharacterFamily Q, ∑ z ∈ nonprincipalDensityFinset p.2 σ T, characterZeroMultiplicity p.2 z

/-- A single zero has multiplicity at most a constant times the logarithm of
the analytic conductor of its character. -/
theorem characterZeroMultiplicity_le_log {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {z : ℂ} (hz : DirichletCharacter.LFunction χ z = 0)
    (h₀ : 0 < z.re) (h₁ : z.re < 1) :
    (characterZeroMultiplicity χ z:ℝ) ≤ jensenUnitZeroDensityConst * Real.log ((q:ℝ)*(|z.im|+3)) := by
  let t := z.im-1/2
  let c : ℂ := (2:ℂ)+(t+1/2:ℝ)*I
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall c (9/4)) :=
    ((differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hc : DirichletCharacter.LFunction χ c ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp [c])
  have hfin := zeroSet_finite (by norm_num : (0:ℝ) ≤ 9/4) ha hc
  let Z := hfin.toFinset
  have hZ : (Z:Set ℂ) = zeroSet (DirichletCharacter.LFunction χ) c (9/4) := by simp [Z]
  have hzmem : z ∈ Z := by
    rw [← mem_coe,hZ]
    refine ⟨?_,hz⟩
    rw [Metric.mem_closedBall,Complex.dist_eq]
    have he : z-c = ((z.re-2:ℝ):ℂ) := by apply Complex.ext <;> simp [c,t]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]; linarith
  have ho := single_le_sum (f:=fun u => analyticOrderNatAt (DirichletCharacter.LFunction χ) u)
    (fun _ _ => Nat.zero_le _) hzmem
  rw [← zeroCount_eq_sum_analyticOrderNatAt (by norm_num : (0:ℝ) ≤ 9/4) ha hc hZ] at ho
  simp only [characterZeroMultiplicity,dite_eq_left (NeZero.ne q)]
  apply (show (analyticOrderNatAt (DirichletCharacter.LFunction χ) z:ℝ) ≤ _ by exact_mod_cast ho).trans
    ((zeroCount_LFunction_unit_interval_le hχ t).trans _)
  apply mul_le_mul_of_nonneg_left _ jensenUnitZeroDensityConst_pos.le
  have hq : 0 < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply Real.log_le_log (mul_pos hq (by positivity))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hab := abs_sub (z.im) (1/2:ℝ)
  dsimp only [t]; norm_num at hab; linarith

/-- The primitive-character family zero-density theorem counting analytic multiplicities. -/
private theorem primitiveFamilyZeroCount_near_one :
    ∃ C > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ : ℝ}, 0 ≤ T → σ ∈ Set.Icc (3/4:ℝ) 1 →
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤
        C*(1+Real.log ((Q:ℝ)*(T+2)))^11*((Q:ℝ)*(T+2))^(16*(1-σ)) := by
  obtain ⟨C,hC,H⟩ := dirichlet_family_zeroDensity
  let K := jensenUnitZeroDensityConst
  have hK : 0 < K := jensenUnitZeroDensityConst_pos
  refine ⟨K*C,by positivity,?_⟩
  intro Q hQ T σ hT hσ
  let Y := (Q:ℝ)*(T+2)
  let S (p : (q : ℕ) × DirichletCharacter ℂ q) := nonprincipalDensityFinset p.2 σ T
  have hQ' : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hY : 1 ≤ Y := by dsimp only [Y]; nlinarith
  have hD := H hQ hT hσ S (by
    intro p _ hp z hz
    obtain ⟨hχ,hz0,_,hr,hr1,ht⟩ := (mem_nonprincipalDensityFinset p.2).mp hz
    exact ⟨hχ,hz0,hr,hr1,ht⟩)
  have hloc (p : (q : ℕ) × DirichletCharacter ℂ q) (hp : p ∈ primitiveCharacterFamily Q)
      (z : ℂ) (hz : z ∈ S p) : (characterZeroMultiplicity p.2 z:ℝ) ≤ K*(1+Real.log Y) := by
    obtain ⟨hq₀,hqQ⟩ := mem_Icc.mp (mem_sigma.mp hp).1
    let : NeZero p.1 := ⟨Nat.ne_of_gt hq₀⟩
    obtain ⟨hχ,hz0,hr₀,_,hr1,ht⟩ := (mem_nonprincipalDensityFinset p.2).mp hz
    apply (characterZeroMultiplicity_le_log hχ hz0 hr₀ hr1).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    have hq : 0<(p.1:ℝ) := by exact_mod_cast hq₀
    have harg : (p.1:ℝ)*(|z.im|+3) ≤ 2*Y := by
      calc
        _ ≤ (Q:ℝ)*(T+3) := by gcongr
        _ ≤ _ := by dsimp only [Y]; nlinarith
    have hl := Real.log_le_log (by positivity) harg
    rw [Real.log_mul (by norm_num) (by linarith : Y ≠ 0)] at hl
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hsum := sum_le_sum fun p hp => sum_le_sum (hloc p hp)
  simp only [sum_const,nsmul_eq_mul,← sum_mul] at hsum
  unfold primitiveFamilyZeroCount
  push_cast
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_right hD (mul_nonneg hK.le (by linarith [Real.log_nonneg hY]))).trans_eq
  dsimp only [Y]; ring

private lemma card_primitiveFamily_le (Q : ℕ) : (primitiveCharacterFamily Q).card ≤ Q^2 := by
  rw [primitiveCharacterFamily,card_sigma]
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, Q := by
      apply sum_le_sum
      intro q hq
      let : NeZero q := ⟨Nat.ne_of_gt (mem_Icc.mp hq).1⟩
      calc
        _ ≤ (univ : Finset (DirichletCharacter ℂ q)).card := card_le_card (filter_subset ..)
        _ = q.totient := by rw [card_univ,card_dirichletCharacter_eq_totient]
        _ ≤ Q := (Nat.totient_le q).trans (mem_Icc.mp hq).2
    _ = _ := by simp [Nat.card_Icc,pow_two]

/-- The symmetric density bound for all `0 ≤ σ ≤ 1`, counting zeros with their
analytic multiplicities over all nonprincipal primitive characters. -/
theorem primitiveFamilyZeroCount_le :
    ∃ C > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ : ℝ}, 0 ≤ T → σ ∈ Set.Icc (0:ℝ) 1 →
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤
        C*(1+Real.log ((Q:ℝ)*(T+2)))^11*((Q:ℝ)*(T+2))^(16*(1-σ)) := by
  obtain ⟨C,hC,H⟩ := primitiveFamilyZeroCount_near_one
  let K := jensenUnitZeroDensityConst
  have hK : 0 < K := jensenUnitZeroDensityConst_pos
  refine ⟨max C (3*K),hC.trans_le (le_max_left ..),?_⟩
  intro Q hQ T σ hT hσ
  let Y := (Q:ℝ)*(T+2)
  let W := 1+Real.log Y
  have hQ' : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hY : 1 ≤ Y := by dsimp only [Y]; nlinarith
  have hW : 1 ≤ W := by dsimp only [W]; linarith [Real.log_nonneg hY]
  change _ ≤ max C (3*K)*W^11*Y^(16*(1-σ))
  by_cases hnear : 3/4 ≤ σ
  · apply (H hQ hT ⟨hnear,hσ.2⟩).trans
    change C*W^11*Y^(16*(1-σ)) ≤ _
    gcongr; exact le_max_left ..
  let F := primitiveCharacterFamily Q
  have hc (p : (q : ℕ) × DirichletCharacter ℂ q) (hp : p ∈ F) :
      (∑ z ∈ nonprincipalDensityFinset p.2 σ T, (characterZeroMultiplicity p.2 z:ℝ)) ≤ 3*K*(T+2)*W := by
    obtain ⟨hq₀,hqQ⟩ := mem_Icc.mp (mem_sigma.mp hp).1
    let : NeZero p.1 := ⟨Nat.ne_of_gt hq₀⟩
    by_cases hχ : p.2 = 1
    · simp [nonprincipalDensityFinset,hχ,NeZero.ne p.1]; positivity
    have hsub : nonprincipalDensityFinset p.2 σ T ⊆ criticalStripZeroFinset p.2 (-T) T := by
      simp [nonprincipalDensityFinset,NeZero.ne p.1,hχ]
    have hsum := sum_le_sum_of_subset (f:=fun z => analyticOrderNatAt (DirichletCharacter.LFunction p.2) z) hsub
    have hb := zeroCountL_le_mul_log hχ hT
    have hout : ∑ z ∈ nonprincipalDensityFinset p.2 σ T, (characterZeroMultiplicity p.2 z:ℝ) ≤ zeroCountL p.2 T := by
      simp only [characterZeroMultiplicity,dite_eq_left (NeZero.ne p.1)]
      exact_mod_cast hsum
    apply (hout.trans hb).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hq : 0 < (p.1:ℝ) := by exact_mod_cast hq₀
    have hxy : (p.1:ℝ)*(T+3) ≤ 2*Y := by
      calc
        _ ≤ (Q:ℝ)*(T+3) := by gcongr
        _ ≤ _ := by dsimp only [Y]; nlinarith
    have hlog := Real.log_le_log (by positivity) hxy
    rw [Real.log_mul (by norm_num) (by linarith : Y ≠ 0)] at hlog
    dsimp [W]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have htotal := sum_le_sum hc
  simp only [sum_const,nsmul_eq_mul] at htotal
  have hcard : (F.card:ℝ) ≤ (Q:ℝ)^2 := by exact_mod_cast card_primitiveFamily_le Q
  have hpow : (Q:ℝ)^2*(T+2) ≤ Y^(16*(1-σ)) := by
    have hT' : 1 ≤ T+2 := by linarith
    have hh : (Q:ℝ)^2*(T+2) ≤ Y^2 := by dsimp only [Y]; rw [mul_pow]; gcongr; nlinarith
    apply hh.trans
    rw [←Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  unfold primitiveFamilyZeroCount
  push_cast
  apply htotal.trans
  calc
    _ ≤ (Q:ℝ)^2*(3*K*(T+2)*W) := by gcongr
    _ = 3*K*W*((Q:ℝ)^2*(T+2)) := by ring
    _ ≤ max C (3*K)*W^11*Y^(16*(1-σ)) := by
      gcongr
      · exact le_max_right ..
      · simpa only [pow_one] using pow_le_pow_right₀ hW (show 1 ≤ 11 by decide)

/-- Beyond the strip of width `log(1+log Y)/log Y`, with `Y=Q(T+2)`, the
logarithmic factors are absorbed into a fixed power of `Y^(1−σ)`. -/
theorem primitiveFamilyZeroCount_le_of_log_gap :
    ∃ C > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ : ℝ}, 0 ≤ T → σ ∈ Set.Icc (0:ℝ) 1 →
      Real.log (1+Real.log ((Q:ℝ)*(T+2))) ≤ (1-σ)*Real.log ((Q:ℝ)*(T+2)) →
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤ C*((Q:ℝ)*(T+2))^(27*(1-σ)) := by
  obtain ⟨C,hC,H⟩ := primitiveFamilyZeroCount_le
  refine ⟨C,hC,?_⟩
  intro Q hQ T σ hT hσ hgap
  let Y := (Q:ℝ)*(T+2)
  have hQ' : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hY : 1 ≤ Y := by dsimp only [Y]; nlinarith
  have hY' : 0 < Y := by linarith
  have hW : 0 < 1+Real.log Y := by linarith [Real.log_nonneg hY]
  have hpow : 1+Real.log Y ≤ Y^(1-σ) := by
    rw [Real.rpow_def_of_pos hY',←Real.exp_log hW, Real.exp_le_exp]
    simpa only [Y,mul_comm (Real.log _)] using hgap
  have h := H hQ hT hσ
  apply h.trans
  change C*(1+Real.log Y)^11*Y^(16*(1-σ)) ≤ C*Y^(27*(1-σ))
  calc
    _ ≤ C*(Y^(1-σ))^11*Y^(16*(1-σ)) := by gcongr
    _ = _ := by
      rw [mul_assoc,←Real.rpow_mul_natCast hY'.le,←Real.rpow_add hY']
      congr 2; push_cast; ring

end AnalyticNumberTheory.PrimeDistribution
