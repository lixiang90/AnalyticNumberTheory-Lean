import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PowerSums
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Detecting large moduli from real power sums

A Fejér weight aligned with a point of maximal modulus turns pointwise
upper bounds on all the real power sums into a bound on that modulus.
The rapidly decaying error is summed as a geometric series.
-/
noncomputable section
open Finset Complex
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

private theorem summed_phase_lower {ι : Type*} (S : Finset ι) (u : ι → ℂ)
    (hu : ∀ i ∈ S, ‖u i‖≤1) {a : ι} (ha : a∈S) (ha' : ‖u a‖=1) (K : ℕ) :
    ((K:ℝ)+1)*((K:ℝ)/4-S.card) ≤
       ∑ j ∈ range K, fejerPhaseWeight K j (u a)*(∑ i ∈ S,(u i^(j+1)).re) := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  let F := fun i => ∑ j ∈ range K,fejerPhaseWeight K j (u a)*(u i^(j+1)).re
  change _ ≤ ∑ i ∈ S,F i
  rw [←sum_erase_add _ _ ha]
  have hlow : ∑ i ∈ S.erase a, -((K:ℝ)+1) ≤ ∑ i ∈ S.erase a,F i :=
    sum_le_sum (fun i hi => sum_phaseWeight_lower ha' (hu i (mem_of_mem_erase hi)) K)
  have hself : ((K:ℝ)+1)*(K-3:ℝ)/4 ≤ F a := sum_phaseWeight_self_lower ha' K
  simp only [sum_const,nsmul_eq_mul] at hlow
  have hc := S.card_erase_add_one ha
  have hcn : ((S.erase a).card:ℝ)+1=S.card := by exact_mod_cast hc
  nlinarith [Nat.cast_nonneg (α:=ℝ) K]

/-- A large point forces a large pole term. The cardinality counts every point
with its multiplicity by using one index for each occurrence. -/
theorem power_sum_detection {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖≤1) {w : ι} (hw : w∈S) (hw' : 8/9 ≤ ‖z w‖)
    {H D : ℝ} (hH : 0≤H) (hD : 0≤D) {K : ℕ}
    (hK : 512*(H+S.card+1) ≤ K)
    (hpow : ∀ j ∈ range K, (∑ i ∈ S,(z i^(j+1)).re) ≤ D*(j+1)+H*(4/5:ℝ)^j) :
    1 ≤ 16*D*K*(‖z w‖⁻¹)^K := by
  classical
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image S (fun i => ‖z i‖) ⟨w,hw⟩
  let r := ‖z a‖
  have hrw : ‖z w‖≤r := hmax w hw
  have hr : 8/9≤r := hw'.trans hrw
  have hrp : 0<r := by linarith
  have hr1 : r≤1 := hz a ha
  have hri : 1≤r⁻¹ := (one_le_inv₀ hrp).mpr hr1
  have hwinv : r⁻¹≤‖z w‖⁻¹ := inv_anti₀ (by linarith) hrw
  let u := fun i => z i/(r:ℂ)
  have hu (i : ι) (hi : i∈S) : ‖u i‖≤1 := by
    rw [show ‖u i‖=‖z i‖/r by simp [u,norm_div,abs_of_pos hrp],div_le_one hrp]; exact hmax i hi
  have hau : ‖u a‖=1 := by simp [u,r,norm_div,div_self (ne_of_gt hrp : r≠0)]
  let W := fun j => fejerPhaseWeight K j (u a)
  have hW (j : ℕ) (hj : j∈range K) := fejerPhaseWeight_nonneg hj hau
  have hW' (j : ℕ) (hj : j∈range K) := fejerPhaseWeight_le hj hau
  have htwo : ∀ j ∈ range K, W j*(∑ i ∈ S,(u i^(j+1)).re) ≤
       2*K*(D*K*(r⁻¹)^K+2*H*(9/10:ℝ)^j) := by
    intro j hj
    have hjK : j+1≤K := mem_range.mp hj
    have hjR : ((j:ℝ)+1)≤K := by exact_mod_cast hjK
    have hunit : ∑ i ∈ S,(u i^(j+1)).re = (r⁻¹)^(j+1)*(∑ i ∈ S,(z i^(j+1)).re) := by
      rw [mul_sum]; apply sum_congr rfl; intro i _
      simp [u,div_eq_mul_inv,mul_pow,←Complex.ofReal_inv,←Complex.ofReal_pow,Complex.mul_re,mul_comm]
    have hrt : (r⁻¹)^(j+1) ≤ (r⁻¹)^K := pow_le_pow_right₀ hri hjK
    have hratio : r⁻¹*(4/5:ℝ)≤9/10 := by rw [inv_mul_eq_div,div_le_iff₀ hrp]; linarith
    have herr : (r⁻¹)^(j+1)*(4/5:ℝ)^j ≤ 2*(9/10:ℝ)^j := by
      rw [pow_succ',mul_assoc,←mul_pow]
      apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) hratio j) (by positivity) (by norm_num)
      rw [inv_eq_one_div,div_le_iff₀ hrp]; linarith
    have hup : (∑ i ∈ S,(u i^(j+1)).re) ≤ D*K*(r⁻¹)^K+2*H*(9/10:ℝ)^j := by
      rw [hunit]
      calc
        _ ≤ (r⁻¹)^(j+1)*(D*(j+1)+H*(4/5:ℝ)^j) := by gcongr; exact hpow j hj
        _ = D*((j:ℝ)+1)*(r⁻¹)^(j+1)+H*((r⁻¹)^(j+1)*(4/5:ℝ)^j) := by ring
        _ ≤ D*K*(r⁻¹)^K+H*(2*(9/10:ℝ)^j) := by gcongr
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left hup (hW j hj)).trans
      (mul_le_mul_of_nonneg_right (hW' j hj) (by positivity))
  have hl := summed_phase_lower S u hu ha hau K
  have hsum := hl.trans (sum_le_sum htwo)
  simp_rw [mul_add,sum_add_distrib] at hsum
  rw [sum_const,nsmul_eq_mul,card_range] at hsum
  have hgeom : (∑ j ∈ range K,(9/10:ℝ)^j) ≤ 10 := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤9/10) (by norm_num : (9/10:ℝ)<1)).sum_le_tsum
      (range K) (fun i _ => by positivity)
    norm_num [tsum_geometric_of_lt_one] at h
    exact h
  simp_rw [←mul_assoc (2*(K:ℝ)) (2*H)] at hsum
  rw [←mul_sum] at hsum
  have hbound := mul_le_mul_of_nonneg_left hgeom (by positivity : 0≤2*(K:ℝ)*(2*H))
  have hKp : (0:ℝ)<K := by linarith [Nat.cast_nonneg (α:=ℝ) S.card]
  have hsmall : (S.card:ℝ)+40*H ≤ (K:ℝ)/8 := by linarith [Nat.cast_nonneg (α:=ℝ) S.card]
  have hsmall' := mul_le_mul_of_nonneg_left hsmall hKp.le
  have hc : (S.card:ℝ) ≤ (K:ℝ)/4 := by linarith [Nat.cast_nonneg (α:=ℝ) S.card]
  have hdetect : 1≤16*D*K*(r⁻¹)^K := by
    by_contra! hb
    have := mul_lt_mul_of_pos_left hb (mul_pos hKp hKp)
    nlinarith only [hsum,hbound,hsmall',hc,this]
  exact hdetect.trans (by gcongr)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
