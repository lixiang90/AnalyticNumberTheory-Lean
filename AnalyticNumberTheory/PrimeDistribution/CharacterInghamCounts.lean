import AnalyticNumberTheory.PrimeDistribution.CharacterInghamBalance
import AnalyticNumberTheory.PrimeDistribution.DirichletZeroCountDensity

/-! # Upper-half-plane Ingham counts, uniformly up to the critical line -/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

private theorem unit_count {q L X : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : q*L≤X) (hL : 1≤L) {σ : ℝ} (hσ : 1/2≤σ) (S : Finset ℂ)
    (hS : ∀ z∈S,χ≠1 ∧ χ.LFunction z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0≤z.im ∧ z.im<L)
    (j : ℕ) (hj : j<L) :
    ((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ jensenUnitZeroDensityConst*(1+Real.log X) := by
  have hx : 1≤X := lt_of_lt_of_le (Nat.mul_pos (NeZero.pos q) hL) hq
  have hx₁ : (1:ℝ)≤X := by exact_mod_cast hx
  by_cases hχ : χ=1
  · have he := eq_empty_iff_forall_notMem.mpr (fun z hz => (hS z hz).1 hχ)
    rw [he];simp only [filter_empty,card_empty,Nat.cast_zero]
    exact mul_nonneg jensenUnitZeroDensityConst_pos.le (by linarith [Real.log_nonneg hx₁])
  have hh := finset_card_zeros_unit_interval_le hχ (j:ℝ) (S:=S.filter (fun z => ⌊z.im⌋₊=j)) (by
    intro z hz
    obtain ⟨hz,hjz⟩ := mem_filter.mp hz
    obtain ⟨_,hz₀,hr,hr',hi,_⟩ := hS z hz
    have hlo := Nat.floor_le hi
    have hhi := Nat.lt_floor_add_one z.im
    rw [hjz] at hlo hhi
    exact ⟨by linarith,hr',hlo,hhi.le,hz₀⟩)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ jensenUnitZeroDensityConst_pos.le
  rw [abs_of_nonneg (Nat.cast_nonneg j)]
  have hn : q*(j+2) ≤ 2*X := calc
    _ ≤ q*(2*L) := Nat.mul_le_mul_left _ (by omega)
    _ = 2*(q*L) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hq
  have hr : (q:ℝ)*(j+2)≤2*(X:ℝ) := by exact_mod_cast hn
  have h := Real.log_le_log (mul_pos (Nat.cast_pos.mpr (NeZero.pos q)) (by positivity)) hr
  rw [Real.log_mul (by norm_num) (by positivity : (X:ℝ)≠0)] at h
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

private theorem count_from_cells {L : ℕ} (S : Finset ℂ) {K : ℝ}
    (him : ∀ z∈S,0≤z.im ∧ z.im<L)
    (hc : ∀ j<L,((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K) :
    (S.card:ℝ)≤L*K := by
  have hmap (z : ℂ) (hz : z∈S) : ⌊z.im⌋₊∈range L :=
    mem_range.mpr ((Nat.floor_lt (him z hz).1).mpr (him z hz).2)
  rw [card_eq_sum_card_fiberwise hmap,Nat.cast_sum]
  exact (sum_le_sum (fun j hj => hc j (mem_range.mp hj))).trans_eq (by simp)

private theorem dyadic_logarithm_bound {X : ℝ} (hX : 1≤X) (j : ℕ) :
    1+Real.log ((2:ℝ)^j*X) ≤ (1+Real.log X)*((j:ℝ)+1) := by
  rw [Real.log_mul (by positivity) (by linarith : X≠0),Real.log_pow]
  nlinarith only [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2))
    (Nat.cast_nonneg (α:=ℝ) j),mul_nonneg (Real.log_nonneg hX) (Nat.cast_nonneg (α:=ℝ) j)]

/-- A symmetric fourth moment on all dyadic windows and the hybrid large sieve
give Ingham's uniform upper-half count, including zeros on the real axis. -/
theorem character_ingham_upper_count {B : ℝ} (hB : 0<B) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} (F : Finset ι) (q : ι→ℕ) [∀ i,NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (S : ι → Finset ℂ) {X L : ℕ} {σ : ℝ},
    16≤X → 1≤L → σ∈Set.Icc (1/2:ℝ) 1 → F.card*L≤X → (∀ i∈F,q i*L≤X) →
    (∀ m : ℕ,1≤m → CharacterHybridMean F (fun i n => χ i n) (m*L) ((m:ℝ)*X)) →
    (∀ j : ℕ, (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,‖(χ i).LFunction ((1/2:ℂ)+t*I)‖^4)
      ≤ B*(2^j*(X:ℝ))*(1+Real.log (2^j*(X:ℝ)))^4) →
    (∀ i∈F,∀ z∈S i,χ i≠1 ∧ (χ i).LFunction z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0≤z.im ∧ z.im<L) →
    (∑ i∈F,((S i).card:ℝ))≤C*(1+Real.log X)^6*(X:ℝ)^(inghamExponent σ) := by
  let K := jensenUnitZeroDensityConst
  have hK : 0<K := jensenUnitZeroDensityConst_pos
  obtain ⟨D,hD,H⟩ := character_ingham_balanced hB hK
  refine ⟨D+K*Real.exp 2,by positivity,?_⟩
  intro ι F q _ χ S X L σ hX hL hσ hcard hq hm h₄ hS
  let ℓ := 1+Real.log X
  let Z := (X:ℝ)^(inghamExponent σ)
  have hx : (1:ℝ)<X := by exact_mod_cast (by omega : 1<X)
  have hl : 1≤ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hx.le]
  have hZ : 0≤Z := Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hc (i) (hi : i∈F) := unit_count (hq i hi) hL hσ.1 (S i) (hS i hi)
  change _ ≤ (D+K*Real.exp 2)*ℓ^6*Z
  by_cases hgap : 1/ℓ≤σ-1/2
  · have h4' (j : ℕ) := (h₄ j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (show 0≤1+Real.log (2^j*(X:ℝ)) by
          have h' : 1≤(2:ℝ)^j*X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hx.le
          linarith [Real.log_nonneg h']) (dyadic_logarithm_bound hx.le j) 4) (by positivity : 0≤B*(2^j*(X:ℝ))))
    apply (H F q χ S hX hL hσ hgap hm (fun j => (h4' j).trans_eq (by ring)) hS hc).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hK.le (Real.exp_pos _).le) : D≤D+K*Real.exp 2) (by positivity)) hZ
  · have hn : σ-1/2≤(Real.log (X:ℝ))⁻¹ := (not_le.mp hgap).le.trans (by
      rw [one_div];exact inv_anti₀ (Real.log_pos hx) (by dsimp [ℓ];linarith))
    have hz := ingham_near_half hx hσ hn
    have hs := sum_le_sum (s:=F) (fun i hi => count_from_cells (S i)
      (fun z hz => (hS i hi z hz).2.2.2.2) (hc i hi))
    have h' : (F.card:ℝ)*L ≤ X := by exact_mod_cast hcard
    have hℓ := pow_le_pow_right₀ hl (by decide : 1≤6)
    rw [pow_one] at hℓ
    calc _ ≤ (F.card:ℝ)*(L*(K*ℓ)) := by simpa only [sum_const,nsmul_eq_mul] using hs
         _ = ((F.card:ℝ)*L)*(K*ℓ) := by ring
         _ ≤ (Real.exp 2*Z)*(K*ℓ) := mul_le_mul_of_nonneg_right (h'.trans hz) (by positivity)
         _ ≤ (D+K*Real.exp 2)*ℓ^6*Z := by
               apply le_trans (b:=(K*Real.exp 2)*ℓ^6*Z) _ (by gcongr;linarith)
               exact (show Real.exp 2*Z*(K*ℓ)=(K*Real.exp 2)*ℓ*Z by ring).le.trans (by gcongr)

end AnalyticNumberTheory.PrimeDistribution
