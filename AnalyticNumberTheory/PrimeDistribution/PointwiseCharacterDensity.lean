import AnalyticNumberTheory.PrimeDistribution.PointwiseDensityBalance
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamSymmetric
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveMomentComparison

/-!
# Pointwise critical-line bounds and zero density for nonprincipal families

A uniform growth estimate H^a(log H)^b leads to conductor exponent
(1+4a)(1−σ)/(2σ−1). The symmetric count includes possible real zeros
and the analytic multiplicity of every critical-strip zero.
-/
noncomputable section
open Real Complex Finset Filter
open scoped ArithmeticFunction.Moebius ComplexConjugate Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

/-- Uniform hybrid critical-line growth for all positive levels, including the principal character. -/
def CriticalCharacterGrowth (a b : ℝ) : Prop :=
  ∃B : ℝ,0<B ∧ ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
    ‖χ.LFunction ((1/2:ℂ)+t*I)‖≤B*((q:ℝ)*(|t|+2))^a*(1+Real.log ((q:ℝ)*(|t|+2)))^b

private theorem nonprincipal_pointwise_detector :
    ∃W : ℝ,0<W ∧ ∀{q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {X : ℕ} {Y σ : ℝ} {z : ℂ},
      χ≠1 → 1≤X → 16≤Y → 3/4≤σ → σ≤z.re → z.re<1 → χ.LFunction z=0 →
      PointwiseZeroDetector χ X Y σ W (fun t => ‖χ.LFunction ((1/2:ℂ)+t*I)‖) z := by
  let E := 729*‖(720/(2*π):ℂ)‖/(1/4)
  refine ⟨8*(1+E),by dsimp [E];positivity,?_⟩
  intro q _ χ X Y σ z hχ hX hY hs hz hz' hzero
  rcases character_detector_window hχ hX hY (by norm_num : (0:ℝ)<1/4) (by linarith : 1/4≤z.re-1/2) hz' hzero with h|h
  · exact Or.inl ((by norm_num : (1/8:ℝ)≤1/4).trans h)
  right
  filter_upwards [h,eventually_ge_atTop (0:ℝ)] with U hU hu
  let J := ∫ t in -U..U,1/(1+|t-z.im|)^6*‖χ.LFunction ((1/2:ℂ)+t*I)‖*
    ‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X ((1/2:ℂ)+t*I)‖
  have hJ : 0≤J := intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hE : 0≤E := by dsimp [E];positivity
  have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Y) (by linarith : 1/2-z.re≤1/2-σ)
  change 1/8≤E*Y^(1/2-z.re)*J at hU
  change 1/(8*(1+E)*Y^(1/2-σ))≤J
  rw [div_le_iff₀ (by positivity [show 0<Y by linarith])]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hE) hJ
  nlinarith only [hU,hh,mul_nonneg (Real.rpow_nonneg (by linarith : 0≤Y) (1/2-σ)) hJ]

/-- Conditional pointwise density for every conjugation-stable nonprincipal
family, uniformly over all admissible conductor-height scales. -/
theorem nonprincipal_pointwise_density {a b C : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b)
    (hC : 0<C) (hg : CriticalCharacterGrowth a b) :
    ∃D : ℝ,0<D ∧ ∀{ι : Type*} (F : Finset ι) (q : ι→ℕ) [∀i,NeZero (q i)]
      (χ : (i:ι)→DirichletCharacter ℂ (q i)) (c : ι→ι) {H L : ℕ} {T σ : ℝ},
    Function.Involutive c → (∀i∈F,c i∈F) →
    (∀i∈F,χ (c i)≠1 → χ i≠1 ∧ ∀z,(χ (c i)).LFunction z=0 → (χ i).LFunction (conj z)=0) →
    1≤H → 3≤L → T<L → σ∈Set.Icc (3/4:ℝ) 1 → F.card*L≤H → (∀i∈F,q i*(L+2)≤H) →
    SparseCharacterBound F (fun i n => χ i n) L H C →
    (∑i∈F,∑z∈nonprincipalDensityFinset (χ i) σ T,(characterZeroMultiplicity (χ i) z:ℝ))
      ≤D*(1+Real.log H)^(10+2*b)*(H:ℝ)^(pointwiseDensityExponent a σ) := by
  obtain ⟨B,hB,HB⟩ := hg
  obtain ⟨W,hW,HW⟩ := nonprincipal_pointwise_detector
  let K := jensenUnitZeroDensityConst
  have hK : 0<K := jensenUnitZeroDensityConst_pos
  obtain ⟨A,hA,D,hD,HD⟩ := pointwise_density_balanced ha hb hB hC hK.le hW
  refine ⟨2*D*K,by positivity,?_⟩
  intro ι F q _ χ c H L T σ hinv hc hstar hH hL hT hs hcard hq hm
  let P (i:ι) (z:ℂ) := χ i≠1 ∧ (χ i).LFunction z=0 ∧ σ≤z.re ∧ z.re<1
  let ℓ := 1+Real.log H
  let Z := (H:ℝ)^(pointwiseDensityExponent a σ)
  have hrH : (1:ℝ)≤H := by exact_mod_cast hH
  have hℓ : 0<ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hrH]
  have hY := (pointwise_density_cutoff_estimates hA.le ha hb).choose_spec.2 hrH hs |>.1
  have hup (S : ι→Finset ℂ) (hS : ∀i∈F,∀z∈S i,P i z ∧ 0≤z.im ∧ z.im<L) :
      (∑i∈F,((S i).card:ℝ))≤D*ℓ^(9+2*b)*Z := by
    have hu (i) (hi:i∈F) := nonprincipal_density_unit_count (X:=H) (L:=L)
      ((Nat.mul_le_mul_left (q i) (by omega : L≤L+2)).trans (hq i hi)) (by omega : 1≤L)
      (show 1/2≤σ by linarith [hs.1]) (S i) (fun z hz => by
        obtain ⟨⟨h₁,h₂,h₃,h₄⟩,h₅,h₆⟩ := hS i hi z hz;exact ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩)
    apply HD q χ S (by omega : 1≤L) hrH hs (by exact_mod_cast hcard) (fun i hi => by exact_mod_cast hq i hi) hm
      (fun i hi z hz => ⟨(hS i hi z hz).1.2.2.1,(hS i hi z hz).1.2.2.2.le,(hS i hi z hz).2⟩)
      hu (fun i t => ‖(χ i).LFunction ((1/2:ℂ)+t*I)‖) (fun i _ => (continuous_character_critical_line (χ i)).norm)
      (fun _ _ _ => norm_nonneg _) (fun i _ => HB (χ i))
    intro hX i hi z hz
    obtain ⟨⟨h₁,h₂,h₃,h₄⟩,_⟩ := hS i hi z hz
    exact HW h₁ hX hY hs.1 h₃ h₄ h₂
  let S (i:ι) := nonprincipalDensityFinset (χ i) σ T
  have hcount := symmetric_family_count_of_upper F c hinv hc (P:=P) (by
    intro i hi z hz
    obtain ⟨hn,he,hr,hr'⟩ := hz
    obtain ⟨hn',hc'⟩ := hstar i hi hn
    exact ⟨hn',hc' z he,by simpa using hr,by simpa using hr'⟩) hup S (by
      intro i hi z hz
      obtain ⟨hn,he,_,hr,hr',ht⟩ := (mem_nonprincipalDensityFinset _).mp hz
      exact ⟨⟨hn,he,hr,hr'⟩,ht.trans_lt hT⟩)
  have hL' : (3:ℝ)≤L := by exact_mod_cast hL
  have hh := nonprincipal_family_multiplicity_le F q χ (σ:=σ) (T:=T) (zero_lt_one.trans_le hrH) (by
    intro i hi
    have hmul := mul_le_mul_of_nonneg_left (show T+3≤2*((L:ℝ)+2) by linarith) (Nat.cast_nonneg (α:=ℝ) (q i))
    have hq' : (q i:ℝ)*((L:ℝ)+2)≤H := by exact_mod_cast hq i hi
    nlinarith only [hmul,hq'])
  apply (hh.trans (mul_le_mul_of_nonneg_right hcount (mul_nonneg hK.le hℓ.le))).trans_eq
  change 2*(D*ℓ^(9+2*b)*Z)*(K*ℓ)=2*D*K*ℓ^(10+2*b)*Z
  rw [show 10+2*b=(9+2*b)+1 by ring,Real.rpow_add hℓ (9+2*b) 1,Real.rpow_one];ring

end AnalyticNumberTheory.PrimeDistribution
