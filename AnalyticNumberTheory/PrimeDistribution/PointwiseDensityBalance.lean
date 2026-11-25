import AnalyticNumberTheory.PrimeDistribution.PointwiseDensityDetection
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityBalance
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamCounts

/-!
# Balanced sparse detection under a hybrid critical-line growth bound

The smoothing length depends only on the conductor-height scale. The
Möbius length may also depend on the number of detected points. This
separation permits the same estimate for zeta after removing its low
zeros and for pole-free character L-functions.
-/
noncomputable section
open Real Complex Finset Set Filter
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

theorem pointwiseDensityExponent_nonneg {a σ : ℝ} (ha : 0≤a) (hs : σ∈Set.Icc (3/4:ℝ) 1) :
    0≤pointwiseDensityExponent a σ := by
  unfold pointwiseDensityExponent
  exact div_nonneg (mul_nonneg (by linarith) (by linarith [hs.2])) (by linarith [hs.1])

/-- Any finite family of zeros satisfying the two alternatives at the stated
cutoff has the pointwise density bound, uniformly in σ. -/
theorem pointwise_density_balanced {a b B C K W : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b)
    (hB : 0<B) (hC : 0<C) (hK : 0≤K) (hW : 0<W) :
    ∃A : ℝ,0<A ∧ ∃D : ℝ,0<D ∧ ∀{ι : Type*} {F : Finset ι} (q : ι→ℕ) [∀i,NeZero (q i)]
      (χ : (i:ι)→DirichletCharacter ℂ (q i)) (S : ι→Finset ℂ) {L : ℕ} {H σ : ℝ},
      1≤L → 1≤H → σ∈Set.Icc (3/4:ℝ) 1 → (F.card:ℝ)*L≤H →
      (∀i∈F,(q i:ℝ)*((L:ℝ)+2)≤H) → SparseCharacterBound F (fun i n => χ i n) L H C →
      (∀i∈F,∀z∈S i,σ≤z.re ∧ z.re≤1 ∧ 0≤z.im ∧ z.im<L) →
      (∀i∈F,∀j<L,(((S i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K*(1+Real.log H)) →
      ∀f : ι→ℝ→ℝ,(∀i∈F,Continuous (f i)) → (∀i∈F,∀t,0≤f i t) →
      (∀i∈F,∀t,f i t≤B*((q i:ℝ)*(|t|+2))^a*(1+Real.log ((q i:ℝ)*(|t|+2)))^b) →
      let R := ∑i∈F,((S i).card:ℝ)
      let Y := pointwiseDensityCutoff A b a H σ
      let X := montgomeryMollifierLength R H
      (1≤X → ∀i∈F,∀z∈S i,PointwiseZeroDetector (χ i) X Y σ W (f i) z) →
      R≤D*(1+Real.log H)^(9+2*b)*H^(pointwiseDensityExponent a σ) := by
  let E := max 1 K
  have hE : 1≤E := le_max_left ..
  let J := 4+Real.log (2*E)
  have hJ : 0<J := by dsimp [J];have := Real.log_nonneg (by linarith : 1≤2*E);linarith
  obtain ⟨A,hA,HU⟩ := pointwise_density_unbalanced ha hb hB hC hK hJ hW
  obtain ⟨D,hD,HD⟩ := pointwise_balance_of_unbalanced hA ha hb
  refine ⟨A,hA,1+D,by positivity,?_⟩
  intro ι F q _ χ S L H σ hL hH hs hcard hq hm hS hc f hf hf₀ hp
  dsimp only
  let ℓ := 1+Real.log H
  let R := ∑i∈F,((S i).card:ℝ)
  let X := montgomeryMollifierLength R H
  let Y := pointwiseDensityCutoff A b a H σ
  intro hdet
  have hℓ : 1≤ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hH]
  have hR₀ : 0≤R := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have he := pointwiseDensityExponent_nonneg ha.1 hs
  have hz : 1≤ℓ^(9+2*b)*H^(pointwiseDensityExponent a σ) := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hℓ (by linarith)) (Real.one_le_rpow hH he)
  change R≤(1+D)*ℓ^(9+2*b)*H^(pointwiseDensityExponent a σ)
  rw [mul_assoc]
  by_cases hR : 1≤R
  · have ht (i) (hi:i∈F) := count_from_cells (S i) (fun z hz => (hS i hi z hz).2.2) (hc i hi)
    have he₀ := sum_le_sum ht
    simp only [sum_const,nsmul_eq_mul] at he₀
    have hcrude : R≤E*H*ℓ := by
      apply he₀.trans
      change (F.card:ℝ)*(L*(K*ℓ))≤_
      calc _=((F.card:ℝ)*L)*(K*ℓ) := by ring
           _≤H*(E*ℓ) := mul_le_mul hcard (mul_le_mul_of_nonneg_right (le_max_right 1 K) (zero_le_one.trans hℓ))
             (mul_nonneg hK (zero_le_one.trans hℓ)) (zero_le_one.trans hH)
           _=_ := by ring
    obtain ⟨hRX,hXR⟩ := montgomeryMollifierLength_bounds hR hH
    have hX : 1≤X := by
      have hh : 1≤(X:ℝ) := (one_le_mul_of_one_le_of_one_le hR (by simpa using Real.sqrt_le_sqrt hH)).trans hRX
      exact_mod_cast hh
    have hln := montgomeryMollifierLength_log hE hR hH hcrude
    have hY := (pointwise_density_cutoff_estimates hA.le ha hb).choose_spec.2 hH hs |>.1
    have hu := HU q χ S hL hX hH hY hs hq hm hS hc f hf hf₀ hp (hdet hX) hRX hXR hln
    have hd := HD hR₀ hH hs hu
    change R≤D*ℓ^(9+2*b)*H^(pointwiseDensityExponent a σ) at hd
    rw [mul_assoc] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hz))
  · exact (le_of_not_ge hR).trans (hz.trans (le_mul_of_one_le_left (zero_le_one.trans hz) (by linarith)))

end AnalyticNumberTheory.PrimeDistribution
