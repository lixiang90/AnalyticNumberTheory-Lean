import AnalyticNumberTheory.PrimeDistribution.PointwiseDensityParameters
import AnalyticNumberTheory.PrimeDistribution.PointwiseCharacterTypeII
import AnalyticNumberTheory.PrimeDistribution.SparseMontgomeryTypeI
import AnalyticNumberTheory.PrimeDistribution.CharacterDetectorWindow

/-!
# Combining the two alternatives of the pointwise zero detector

The sample and its two detector subfamilies share the same adaptive
mollifier length. The first alternative uses the sparse hybrid mean
square. In the second, a pointwise critical-line estimate absorbs the
detected samples once Y is chosen.
-/
noncomputable section
open Real Complex Finset Set Filter MeasureTheory
open scoped ArithmeticFunction.Moebius Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- A common detector for a finite family. The threshold allows the principal
character and nonprincipal characters to use different contour arguments. -/
def PointwiseZeroDetector {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) (Y σ W : ℝ)
    (f : ℝ→ℝ) (z : ℂ) : Prop :=
  1/8≤‖∑n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*χ n*(n:ℂ)^(-z)‖ ∨
    ∀ᶠ U : ℝ in atTop,1/(W*Y^(1/2-σ)) ≤
      ∫t in -U..U,1/(1+|t-z.im|)^6*f t*‖dirichletPoly (fun n => (μ n:ℂ)*χ n) X ((1/2:ℂ)+t*I)‖

set_option maxHeartbeats 700000 in
/-- The unbalanced inequality at any admissible cutoff. The coefficient of the
total sample count tends to zero as the smoothing length grows. -/
theorem pointwise_density_unbalanced {a b B C K J W : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b)
    (hB : 0<B) (hC : 0<C) (hK : 0≤K) (hJ : 0<J) (hW : 0<W) :
    ∃ A : ℝ,0<A ∧ ∀{ι : Type*} {F : Finset ι} (q : ι→ℕ) [∀i,NeZero (q i)]
      (χ : (i:ι)→DirichletCharacter ℂ (q i)) (S : ι→Finset ℂ) {L X : ℕ} {H Y σ : ℝ},
      1≤L → 1≤X → 1≤H → 16≤Y → σ∈Set.Icc (3/4:ℝ) 1 →
      (∀i∈F,(q i:ℝ)*((L:ℝ)+2)≤H) → SparseCharacterBound F (fun i n => χ i n) L H C →
      (∀i∈F,∀z∈S i,σ≤z.re ∧ z.re≤1 ∧ 0≤z.im ∧ z.im<L) →
      (∀i∈F,∀j<L,(((S i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K*(1+Real.log H)) →
      ∀f : ι→ℝ→ℝ,(∀i∈F,Continuous (f i)) → (∀i∈F,∀t,0≤f i t) →
      (∀i∈F,∀t,f i t≤B*((q i:ℝ)*(|t|+2))^a*(1+Real.log ((q i:ℝ)*(|t|+2)))^b) →
      (∀i∈F,∀z∈S i,PointwiseZeroDetector (χ i) X Y σ W (f i) z) →
      let ℓ := 1+Real.log H
      let R := ∑i∈F,((S i).card:ℝ)
      R*Real.sqrt H≤X → (X:ℝ)≤2*R*Real.sqrt H → 1+Real.log X≤J*ℓ →
      R≤A*ℓ*(1+Real.log Y)^5*Y^(2*(1-σ)) +
        A*ℓ^(3+2*b)*H^(1/2+2*a)*Y^(1-2*σ)*R := by
  obtain ⟨D,hD,HD⟩ := pointwise_character_typeII_count ha hb hB hC
  let A₁ := 8192*C*(K+1)
  let A₂ := D*(2*K+1)*J^2*W^2
  have hA₁ : 0<A₁ := by dsimp [A₁];positivity
  have hA₂ : 0<A₂ := by dsimp [A₂];positivity
  refine ⟨A₁+A₂,by positivity,?_⟩
  intro ι F q _ χ S L X H Y σ hL hX hH hY hs hq hm hS hcount f hf hf₀ hpoint hdet
  let ℓ := 1+Real.log H
  let R := ∑i∈F,((S i).card:ℝ)
  let P (i:ι) (z:ℂ) := 1/8≤‖∑n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*χ i n*(n:ℂ)^(-z)‖
  let S₁ (i:ι) := (S i).filter (P i)
  let S₂ (i:ι) := (S i).filter (fun z => ¬P i z)
  let R₁ := ∑i∈F,((S₁ i).card:ℝ)
  let R₂ := ∑i∈F,((S₂ i).card:ℝ)
  have hℓ : 0<ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hH]
  have hy : 0<Y := by linarith
  have hYℓ : 0≤1+Real.log Y := by linarith [Real.log_nonneg (by linarith : 1≤Y)]
  have hR : 0≤R := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hR₁ : 0≤R₁ := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hR₂ : 0≤R₂ := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hRsum : R=R₁+R₂ := by
    dsimp only [R,R₁,R₂,S₁,S₂];rw [←sum_add_distrib]
    apply sum_congr rfl;intro i _;exact_mod_cast (card_filter_add_card_filter_not (s:=S i) (P i)).symm
  have hR₁R : R₁≤R := by linarith
  have hR₂R : R₂≤R := by linarith
  dsimp only
  intro hRX hXR hLog
  have hc (A : ι→Finset ℂ) (hsub : ∀i,A i⊆S i) (i) (hi:i∈F) (j) (hj:j<L) :
      (((A i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K*ℓ := by
    apply le_trans _ (hcount i hi j hj)
    exact_mod_cast Finset.card_le_card (filter_subset_filter _ (hsub i))
  have hP := sparse_montgomery_typeI_count hC hm hH (show 1≤⌊Y⌋₊ from (Nat.one_le_floor_iff _).mpr (by linarith))
    (mul_nonneg hK hℓ.le) (by norm_num : (0:ℝ)≤1/8) ⟨by linarith [hs.1],hs.2⟩ S₁
    (fun i hi z hz => ⟨(hS i hi z (mem_filter.mp hz).1).1,(hS i hi z (mem_filter.mp hz).1).2.1⟩)
    (fun i hi z hz => (hS i hi z (mem_filter.mp hz).1).2.2) (hc _ fun _ => filter_subset ..)
    ((mul_le_mul_of_nonneg_right hR₁R (Real.sqrt_nonneg H)).trans hRX)
    (norm_inghamRieszCoeff hy X) (fun _ _ _ hz => (mem_filter.mp hz).2)
  have hxpos : (0:ℝ)<⌊Y⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff Y).mpr (show 1≤Y by linarith)
  have hlogflo := Real.log_le_log hxpos (Nat.floor_le hy.le)
  have hh : K*ℓ+1+Real.log H=(K+1)*ℓ := by dsimp [ℓ];ring
  have hI : R₁≤A₁*ℓ*(1+Real.log Y)^5*Y^(2*(1-σ)) := by
    change R₁*(1/8:ℝ)^2≤_ at hP
    rw [hh] at hP
    have hp : 128*C*((K+1)*ℓ)*(1+Real.log (⌊Y⌋₊:ℝ))^5*(⌊Y⌋₊:ℝ)^(2*(1-σ))≤
      128*C*((K+1)*ℓ)*(1+Real.log Y)^5*Y^(2*(1-σ)) := by
      gcongr <;>first | exact Nat.floor_le hy.le | linarith [hs.2,Real.log_nonneg (by linarith : 1≤Y)]
    dsimp only [A₁];nlinarith only [hP.trans hp]
  let V := 1/(W*Y^(1/2-σ))
  have hV : 0≤V := by dsimp [V];positivity
  have hII := HD q χ S₂ hL hX hH (mul_nonneg hK hℓ.le) hV hq hm
    (fun i hi z hz => (hS i hi z (mem_filter.mp hz).1).2.2)
    (hc _ fun _ => filter_subset ..) f hf hf₀ hpoint
    (fun i hi z hz => (hdet i hi z (mem_filter.mp hz).1).resolve_left (mem_filter.mp hz).2)
  have hxlog : 0≤1+Real.log X := by linarith [Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)]
  have hII' := pointwise_typeII_damping (a:=a) (b:=b) (σ:=σ) hR₂ hR hK hD.le hJ.le hW
    (zero_lt_one.trans_le hH) hy hℓ hR₂R hXR hxlog hLog hII
  change R₂≤A₂*ℓ^(3+2*b)*H^(1/2+2*a)*Y^(1-2*σ)*R at hII'
  apply le_trans (hRsum.le.trans (add_le_add hI hII')) (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA₂.le) hℓ.le) (pow_nonneg hYℓ 5)) (Real.rpow_nonneg hy.le _)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA₁.le) (Real.rpow_nonneg hℓ.le _)) (Real.rpow_nonneg (zero_le_one.trans hH) _)) (Real.rpow_nonneg hy.le _)) hR

end AnalyticNumberTheory.PrimeDistribution
