import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaLowZeros
import AnalyticNumberTheory.RiemannZeta.FourthMomentNarrowStrip
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamCounts

/-! # Local counts and dyadic fourth means for the zeta detector -/

open Real Complex Finset Set MeasureTheory
open scoped Classical
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

private theorem card_le_sum_zeroMultiplicity (S : Finset ℂ)
    (hS : ∀ z∈S,riemannZeta z=0 ∧ 0<z.re ∧ z.re<1) :
    (S.card:ℝ)≤∑z∈S,(zeroMultiplicity z:ℝ) := by
  calc (S.card:ℝ)=∑_z∈S,(1:ℝ) := by simp
       _ ≤ _ := Finset.sum_le_sum (fun z hz => by
         obtain ⟨h₁,h₂,h₃⟩ := hS z hz
         exact_mod_cast (zeroMultiplicity_pos_iff h₂ h₃).mpr h₁)

/-- Unit-interval occupancy and total cardinality for arbitrary subsets
of zeta zeros, with a common absolute constant. -/
theorem zeta_density_sample_count_inputs :
    ∃ K : ℝ,1≤K ∧ ∀(L : ℕ) (S : Finset ℂ),
      (∀ z∈S,riemannZeta z=0 ∧ 0<z.re ∧ z.re<1 ∧ 0<z.im ∧ z.im<L) →
      (∀ j<L,((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K*(1+Real.log ((L:ℝ)+2))) ∧
      (S.card:ℝ)≤K*((L:ℝ)+2)*(1+Real.log ((L:ℝ)+2)) := by
  obtain ⟨A,hA,HA⟩ := sum_zeroMultiplicity_strip_le
  obtain ⟨B,hB,HB⟩ := zeroCountUpTo_le_mul_log
  let K := 1+A+B
  have hAK : A≤K := by dsimp [K];linarith
  have hBK : B≤K := by dsimp [K];linarith
  refine ⟨K,by dsimp [K];linarith,?_⟩
  intro L S hS
  have hH : 2≤(L:ℝ)+2 := by linarith [Nat.cast_nonneg (α:=ℝ) L]
  have hlog := Real.log_nonneg (by linarith : 1≤(L:ℝ)+2)
  constructor
  · intro j hj
    let V := S.filter (fun z => ⌊z.im⌋₊=j)
    have h := HA j V (fun z hz => by
      obtain ⟨hz,hfloor⟩ := Finset.mem_filter.mp hz
      obtain ⟨h₁,h₂,h₃,ht,_⟩ := hS z hz
      have hlow := Nat.floor_le ht.le
      have hhigh := Nat.lt_floor_add_one z.im
      rw [hfloor] at hlow hhigh
      exact ⟨h₁,h₂,h₃,abs_le.mpr ⟨by linarith,by linarith⟩⟩)
    have hc := card_le_sum_zeroMultiplicity V (fun z hz => by
      obtain ⟨h₁,h₂,h₃,_,_⟩ := hS z (Finset.mem_filter.mp hz).1
      exact ⟨h₁,h₂,h₃⟩)
    rw [abs_of_nonneg (Nat.cast_nonneg j)] at h
    have hle := Real.log_le_log (by positivity : (0:ℝ)<j+2) (by exact_mod_cast Nat.add_le_add_right hj.le 2 : (j:ℝ)+2≤L+2)
    exact (hc.trans h).trans (mul_le_mul hAK (by linarith) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) j] : 1≤(j:ℝ)+2)) (hA.le.trans hAK))
  · have h := sum_zeroMultiplicity_le_zeroCountUpTo (T:=(L:ℝ)+2) S (fun z hz => by
      obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hS z hz;exact ⟨h₁,h₂,h₃,h₄,by linarith⟩)
    have hc : (∑z∈S,(zeroMultiplicity z:ℝ))≤zeroCountUpTo ((L:ℝ)+2) := by exact_mod_cast h
    have hn := card_le_sum_zeroMultiplicity S (fun z hz => by
      obtain ⟨h₁,h₂,h₃,_,_⟩ := hS z hz;exact ⟨h₁,h₂,h₃⟩)
    exact ((hn.trans hc).trans (HB _ hH)).trans (mul_le_mul (mul_le_mul_of_nonneg_right hBK (by positivity)) (by linarith) hlog (by dsimp [K];positivity))

/-- Dyadic fourth moments on every positive and negative height range used
by a zeta detector of height `L`. -/
theorem zeta_density_dyadic_fourth_input :
    ∃ B : ℝ,0<B ∧ ∀ {L : ℕ},1≤L → ∀ j : ℕ,
      (∫ t in -(2^j*(L:ℝ))..2^j*L,‖riemannZeta ((1/2:ℂ)+t*I)‖^4)≤
        (B*((L:ℝ)+2)*(1+Real.log ((L:ℝ)+2))^4)*2^j*((j:ℝ)+1)^4 := by
  obtain ⟨B,hB,H⟩ := fourthMoment_riemannZeta_symmetric_log_le
  refine ⟨B,hB,?_⟩
  intro L hL j
  have hl : (1:ℝ)≤L := by exact_mod_cast hL
  have h₁ : (1:ℝ)≤2^j*L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hl
  have h₀ := Real.log_le_log (zero_lt_one.trans_le hl) (by linarith : (L:ℝ)≤L+2)
  have hlog := (dyadic_logarithm_bound hl j).trans (mul_le_mul_of_nonneg_right (by linarith : 1+Real.log L≤1+Real.log ((L:ℝ)+2)) (by positivity))
  have hpow := pow_le_pow_left₀ (by linarith [Real.log_nonneg h₁] : 0≤1+Real.log ((2:ℝ)^j*L)) hlog 4
  have hlen : (2:ℝ)^j*L≤2^j*((L:ℝ)+2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact (H h₁).trans ((mul_le_mul (mul_le_mul_of_nonneg_left hlen hB.le) hpow (pow_nonneg (by linarith [Real.log_nonneg h₁]) _) (by positivity)).trans_eq (by ring))

end AnalyticNumberTheory.PrimeDistribution
