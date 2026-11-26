import AnalyticNumberTheory.AnalyticTools.SecondPoleDifference
import AnalyticNumberTheory.PrimeDistribution.ZeroReciprocalTail
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis
import AnalyticNumberTheory.RiemannZeta.ZeroEnumeration

/-!
# The nontrivial zeros in a triangularly weighted explicit formula

A split at height 1/h balances the quadratic small-step bound against the
reciprocal-square tail. Under RH the result is uniform in the height cutoff.
-/

noncomputable section

open Complex Filter Finset
open scoped Topology Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Under RH every finite set of distinct critical-strip zeros contributes at most
C exp(u/2) h log(1/h) in absolute value after two logarithmic differences.
Each term is counted with its analytic multiplicity. -/
theorem sum_norm_secondPoleDifference_le_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ) {h : ℝ}, 0 < h → h ≤ 1/2 → ∀ S : Finset ℂ,
      (∀ z ∈ S, z ∈ CriticalStripZeros) →
      (∑ z ∈ S, (zeroMultiplicity z : ℝ)*‖secondPoleDifference z u h‖) ≤
        C*Real.exp (u/2)*h*Real.log (1/h) := by
  obtain ⟨C,hC,HC⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  obtain ⟨K,hK,HK⟩ := sum_zeroMultiplicity_div_im_sq_tail_le
  let B := (Real.exp 1+1)^2
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B*(C+K),by positivity,?_⟩
  intro u h hh hhalf S hS
  let T := 1/h
  have hT : 2 ≤ T := (le_div_iff₀ hh).mpr (by linarith)
  let A := Real.exp (u/2)*B
  have hA : 0 < A := mul_pos (Real.exp_pos _) hB
  let w (z : ℂ) := (zeroMultiplicity z : ℝ)*‖secondPoleDifference z u h‖
  have hsmall : (Real.exp (h/2)+1)^2 ≤ B := by
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add (Real.exp_le_exp.mpr (by linarith : h/2 ≤ 1)) le_rfl
  have hr (z : ℂ) (hz : z ∈ S) : z.re = 1/2 := by
    obtain ⟨h₀,h₁,h₂⟩ := mem_criticalStripZeros.mp (hS z hz)
    exact hRH z h₀ h₁ h₂
  have hnear : (∑ z ∈ S with |z.im| < T, w z) ≤ A*h^2*(C*T*Real.log T) := by
    let N := S.filter (fun z => |z.im| < T)
    have hsub : N ⊆ nontrivialZerosUpTo T := by
      intro z hz
      obtain ⟨hzS,hzT⟩ := mem_filter.mp hz
      obtain ⟨h₀,h₁,h₂⟩ := mem_criticalStripZeros.mp (hS z hzS)
      exact mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,hzT.le⟩
    have hcnt : (∑ z ∈ N, (zeroMultiplicity z : ℝ)) ≤ C*T*Real.log T :=
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans (HC T hT)
    calc
      _ ≤ ∑ z ∈ N, (A*h^2)*(zeroMultiplicity z : ℝ) := by
        apply sum_le_sum
        intro z hz
        have hzS := (mem_filter.mp hz).1
        have hz₀ : z ≠ 0 := by
          intro he
          have H := hr z hzS
          simp [he] at H
        have H := norm_secondPoleDifference_le_step hz₀ u hh.le
        rw [hr z hzS,one_div_mul_eq_div,one_div_mul_eq_div,mul_pow] at H
        have H' : ‖secondPoleDifference z u h‖ ≤ A*h^2 := H.trans <| calc
          _ ≤ Real.exp (u/2)*(h^2*B) := by gcongr
          _ = _ := by dsimp only [A]; ring
        exact (mul_le_mul_of_nonneg_left H' (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)
      _ = A*h^2*∑ z ∈ N, (zeroMultiplicity z : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hcnt (by positivity)
  have hfar : (∑ z ∈ S with ¬ |z.im| < T, w z) ≤ A*(K*(Real.log T/T)) := by
    let F := S.filter (fun z => ¬ |z.im| < T)
    have hzF (z) (hz : z ∈ F) : riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ T ≤ |z.im| := by
      obtain ⟨hzS,hzT⟩ := mem_filter.mp hz
      obtain ⟨h₀,h₁,h₂⟩ := mem_criticalStripZeros.mp (hS z hzS)
      exact ⟨h₀,h₁,h₂,le_of_not_gt hzT⟩
    calc
      _ ≤ ∑ z ∈ F, A*((zeroMultiplicity z : ℝ)/z.im^2) := by
        apply sum_le_sum
        intro z hz
        have him := (hzF z hz).2.2.2
        have him₀ : z.im ≠ 0 := abs_pos.mp (by linarith : 0 < |z.im|)
        have H := norm_secondPoleDifference_le_height him₀ u h
        rw [hr z (mem_filter.mp hz).1,one_div_mul_eq_div,one_div_mul_eq_div] at H
        have H' : ‖secondPoleDifference z u h‖ ≤ A/z.im^2 := H.trans (by dsimp only [A]; gcongr)
        exact (mul_le_mul_of_nonneg_left H' (Nat.cast_nonneg _)).trans_eq (by ring)
      _ = A*∑ z ∈ F, (zeroMultiplicity z : ℝ)/z.im^2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (HK hT F hzF) hA.le
  change (∑ z ∈ S,w z) ≤ _
  rw [←sum_filter_add_sum_filter_not S (fun z => |z.im| < T) w]
  apply (add_le_add hnear hfar).trans_eq
  dsimp only [T,A]
  field_simp [hh.ne']

/-- The complete, absolutely convergent nontrivial-zero sum obeys the same RH
bound for every positive logarithmic step at most one half. -/
theorem norm_tsum_secondPoleDifference_le_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ZetaZeroEnumeration) {u h : ℝ}, 0 ≤ u → 0 < h → h ≤ 1/2 →
      ‖∑' n, secondPoleDifference (Z.zero n) u h‖ ≤ C*Real.exp (u/2)*h*Real.log (1/h) := by
  obtain ⟨C,hC,H⟩ := sum_norm_secondPoleDifference_le_of_rh hRH
  refine ⟨C,hC,?_⟩
  intro Z u h hu hh hhalf
  have hs := hasSum_secondPoleDifference (fun n => (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le)
    Z.summable_inv_sq hu hh.le
  let f (z : ℂ) := (zeroMultiplicity z : ℂ)*secondPoleDifference z u h
  have hd : HasSum (fun z : CriticalStripZeros => f z) (∑' n, secondPoleDifference (Z.zero n) u h) :=
    Z.hasSum_distinct (f := fun z => secondPoleDifference z u h) hs.summable.hasSum
  rw [←hd.tsum_eq]
  apply le_of_tendsto (tendsto_sum_nontrivialZerosUpTo_of_summable hd.summable).norm
  apply Filter.Eventually.of_forall
  intro T
  apply (norm_sum_le _ _).trans
  simp only [f,norm_mul,Complex.norm_natCast]
  apply H u hh hhalf
  intro z hz
  obtain ⟨h₀,h₁,h₂,_⟩ := mem_nontrivialZerosUpTo.mp hz
  exact mem_criticalStripZeros.mpr ⟨h₀,h₁,h₂⟩

end AnalyticNumberTheory.PrimeDistribution
