import AnalyticNumberTheory.AnalyticTools.LogarithmicPoleSlope
import AnalyticNumberTheory.PrimeDistribution.SharpExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.SmoothedZeroSums

/-!
# Comparing a smoothed zero series with a sharp height truncation

On RH, a logarithmic slope of width 1/(2T) differs from the height-T sharp
zero sum by O(exp(u/2) log T). Positive and negative steps use the same constant.
-/

noncomputable section

open Complex Filter Finset
open scoped Topology Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Increasing the height includes all previously counted nontrivial zeros. -/
theorem nontrivialZerosUpTo_mono : Monotone nontrivialZerosUpTo := by
  intro T U h z hz
  obtain ⟨h₀,h₁,h₂,h₃⟩ := mem_nontrivialZerosUpTo.mp hz
  exact mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,h₃.trans h⟩

/-- The complete series of logarithmic slopes approximates the sharp zero sum
at height T ≥ 2 with error O(exp(u/2) log T) under RH. The estimate holds on
either side of the physical cutoff, at logarithmic distance 1/(2T). -/
theorem norm_tsum_logarithmicPoleSlope_sub_sharp_le_of_rh (hRH : RiemannHypothesisProp) :
    ∃ M : ℝ, 0 < M ∧ ∀ (Z : ZetaZeroEnumeration) {u h T : ℝ}, 0 ≤ u → 0 ≤ u+h →
      2 ≤ T → |h| = 1/(2*T) →
      ‖(∑' n, logarithmicPoleSlope (Z.zero n) u h) - sharpZetaZeroSum (Real.exp u) T‖ ≤
        M*Real.exp (u/2)*Real.log T := by
  obtain ⟨C,hC,HC⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  obtain ⟨K,hK,HK⟩ := sum_zeroMultiplicity_div_im_sq_tail_le
  let B := Real.exp 1+1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨C/2+2*B*K,by positivity,?_⟩
  intro Z u h T hu huv hT hstep
  let E := Real.exp (u/2)
  let S := nontrivialZerosUpTo T
  let f (z : ℂ) := logarithmicPoleSlope z u h
  let g (z : ℂ) := Complex.exp (z*u)/z
  let m (z : ℂ) : ℂ := zeroMultiplicity z
  have hE : 0 < E := Real.exp_pos _
  have hT₀ : 0 < T := by linarith
  have hh : h ≠ 0 := abs_pos.mp (hstep ▸ (by positivity : 0 < 1/(2*T)))
  have hhab : |h| ≤ 1 := by rw [hstep,div_le_iff₀ (by positivity : 0 < 2*T)]; linarith
  have hr {z : ℂ} {U : ℝ} (hz : z ∈ nontrivialZerosUpTo U) : z.re = 1/2 := by
    obtain ⟨h₀,h₁,h₂,_⟩ := mem_nontrivialZerosUpTo.mp hz
    exact hRH z h₀ h₁ h₂
  have hsharp : sharpZetaZeroSum (Real.exp u) T = ∑ z ∈ S, m z*g z := by
    apply sum_congr rfl
    intro z _
    dsimp only [g,m]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)),
      ←Complex.ofReal_log (Real.exp_pos u).le,Real.log_exp,mul_comm (u:ℂ)]
  have hlo : ‖∑ z ∈ S,m z*(f z-g z)‖ ≤ (C/2)*E*Real.log T := by
    calc
      _ ≤ ∑ z ∈ S, (zeroMultiplicity z : ℝ)*(E*|h|) := by
        apply (norm_sum_le ..).trans
        apply sum_le_sum
        intro z hz
        have hre := hr hz
        have hz₀ : z ≠ 0 := by intro he; simp [he] at hre
        have hnorm : ‖z‖ ≤ 2*T := calc
          _ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
          _ ≤ 2*T := by rw [hre,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; linarith [(mem_nontrivialZerosUpTo.mp hz).2.2.2]
        have hprod : ‖z*(h:ℂ)‖ ≤ 1 := by
          rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hstep,←div_eq_mul_one_div,
            div_le_iff₀ (by positivity : 0 < 2*T),one_mul]
          exact hnorm
        have H := norm_logarithmicPoleSlope_sub_residue_le hz₀ u hh hprod
        rw [hre,one_div_mul_eq_div] at H
        rw [norm_mul,show ‖m z‖ = (zeroMultiplicity z:ℝ) from Complex.norm_natCast _]
        exact mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _)
      _ = (∑ z ∈ S,(zeroMultiplicity z : ℝ))*(E*|h|) := (Finset.sum_mul _ _ _).symm
      _ ≤ (C*T*Real.log T)*(E*|h|) := mul_le_mul_of_nonneg_right (HC T hT) (by positivity)
      _ = _ := by rw [hstep]; field_simp
  have hhi (U : ℝ) : ‖∑ z ∈ nontrivialZerosUpTo U \ S, m z*f z‖ ≤ 2*B*K*E*Real.log T := by
    let F := nontrivialZerosUpTo U \ S
    have hzF (z : ℂ) (hz : z ∈ F) : riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ T ≤ |z.im| := by
      obtain ⟨ha,hb⟩ := mem_sdiff.mp hz
      obtain ⟨h₀,h₁,h₂,_⟩ := mem_nontrivialZerosUpTo.mp ha
      exact ⟨h₀,h₁,h₂,le_of_not_ge (fun ht => hb (mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,ht⟩))⟩
    calc
      _ ≤ ∑ z ∈ F, (E*B/|h|)*((zeroMultiplicity z : ℝ)/z.im^2) := by
        apply (norm_sum_le ..).trans
        apply sum_le_sum
        intro z hz
        have him := abs_pos.mp (hT₀.trans_le (hzF z hz).2.2.2)
        have H := norm_logarithmicPoleSlope_le_height him u hh
        rw [hr (mem_sdiff.mp hz).1,one_div_mul_eq_div,one_div_mul_eq_div] at H
        have hb : Real.exp (h/2)+1 ≤ B := add_le_add
          (Real.exp_le_exp.mpr (by linarith [le_abs_self h] : h/2 ≤ 1)) le_rfl
        have H' : ‖f z‖ ≤ E*B/(|h| * z.im^2) := H.trans (by dsimp only [E]; gcongr)
        rw [norm_mul,show ‖m z‖ = (zeroMultiplicity z:ℝ) from Complex.norm_natCast _]
        exact (mul_le_mul_of_nonneg_left H' (Nat.cast_nonneg _)).trans_eq (by ring)
      _ = (E*B/|h|)*(∑ z ∈ F, (zeroMultiplicity z : ℝ)/z.im^2) := (Finset.mul_sum _ _ _).symm
      _ ≤ (E*B/|h|)*(K*(Real.log T/T)) :=
        mul_le_mul_of_nonneg_left (HK hT F hzF) (by positivity)
      _ = _ := by rw [hstep]; field_simp
  have hs := hasSum_logarithmicPoleSlope (fun n => (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le)
    Z.summable_inv_sq hu huv
  have hd : HasSum (fun z : CriticalStripZeros => m z*f z) (∑' n, f (Z.zero n)) :=
    Z.hasSum_distinct (f := f) hs.summable.hasSum
  have hlim := tendsto_sum_nontrivialZerosUpTo_of_summable (f := fun z => m z*f z) hd.summable
  rw [hd.tsum_eq] at hlim
  apply le_of_tendsto ((hlim.sub_const (sharpZetaZeroSum (Real.exp u) T)).norm)
  filter_upwards [eventually_ge_atTop T] with U hU
  have hsub : S ⊆ nontrivialZerosUpTo U := nontrivialZerosUpTo_mono hU
  have heq : (∑ z ∈ nontrivialZerosUpTo U,m z*f z)-sharpZetaZeroSum (Real.exp u) T =
      (∑ z ∈ S, m z*(f z-g z)) + ∑ z ∈ nontrivialZerosUpTo U \ S,m z*f z := by
    rw [hsharp,←sum_sdiff hsub,show (∑ z ∈ S,m z*(f z-g z)) =
      (∑ z ∈ S,m z*f z)-(∑ z ∈ S,m z*g z) by simp only [mul_sub,sum_sub_distrib]]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hlo (hhi U)).trans_eq (by ring))

end AnalyticNumberTheory.PrimeDistribution
