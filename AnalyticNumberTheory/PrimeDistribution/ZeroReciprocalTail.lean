import AnalyticNumberTheory.PrimeDistribution.DensityPowerSums
import AnalyticNumberTheory.PrimeDistribution.ZeroSumHeightLimit

/-!
# The reciprocal-square tail of nontrivial zeros

The bound N(U) ≪ U log U gives a tail ≪ log T / T. It holds for every finite
subfamily above height T and for the full sum with analytic multiplicities.
-/

noncomputable section

open Filter Finset Complex
open scoped Topology Classical
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- For every finite set of distinct nontrivial zeros with absolute ordinate at least
T ≥ 2, the sum of multiplicity divided by ordinate squared is O(log T / T). -/
theorem sum_zeroMultiplicity_div_im_sq_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ {T : ℝ}, 2 ≤ T → ∀ (S : Finset ℂ),
      (∀ z ∈ S, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ T ≤ |z.im|) →
      (∑ z ∈ S, (zeroMultiplicity z : ℝ)/z.im^2) ≤ K*(Real.log T/T) := by
  obtain ⟨C,hC,HC⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  let K := 5*C*Real.exp 3/(1-Real.exp (-1))
  have hd : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  refine ⟨K,div_pos (by positivity) hd,?_⟩
  intro T hT S hS
  let w (z : ℂ) : ℝ := zeroMultiplicity z
  let y (z : ℂ) := Real.log (|z.im|/T)/2
  let A := 5*C*T*Real.log T
  have hT₀ : 0 < T := by linarith
  have hlog : 1/2 ≤ Real.log T := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hT)
  have hy (z : ℂ) (hz : z ∈ S) : 0 ≤ y z := by
    exact div_nonneg (Real.log_nonneg ((one_le_div hT₀).mpr (hS z hz).2.2.2)) zero_le_two
  have hcnt (u : ℝ) (hu : 0 ≤ u) : (∑ z ∈ S with y z ≤ u,w z) ≤ A*Real.exp (3*u) := by
    let U := T*Real.exp (2*u)
    have he : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
    have hU : 2 ≤ U := hT.trans (le_mul_of_one_le_right hT₀.le (Real.one_le_exp_iff.mpr (by linarith)))
    have hsub : S.filter (fun z => y z ≤ u) ⊆ nontrivialZerosUpTo U := by
      intro z hz
      obtain ⟨hzS,hzu⟩ := mem_filter.mp hz
      obtain ⟨h₀,h₁,h₂,h₃⟩ := hS z hzS
      refine mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,?_⟩
      have hL : Real.log (|z.im|/T) ≤ 2*u := by dsimp only [y] at hzu; linarith
      have hq := (Real.log_le_iff_le_exp (div_pos (hT₀.trans_le h₃) hT₀)).mp hL
      exact ((div_le_iff₀ hT₀).mp hq).trans_eq (mul_comm _ _)
    have hlogU : Real.log U = Real.log T+2*u := by rw [show U = T*Real.exp (2*u) from rfl,
      Real.log_mul hT₀.ne' (Real.exp_ne_zero _),Real.log_exp]
    have hmaj : Real.log T+2*u ≤ 5*Real.log T*Real.exp u := by
      nlinarith only [Real.add_one_le_exp u, he,
        mul_le_mul_of_nonneg_left he (show 0 ≤ Real.log T by linarith),
        mul_le_mul_of_nonneg_right hlog (Real.exp_pos u).le]
    calc
      _ ≤ ∑ z ∈ nontrivialZerosUpTo U,w z := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ C*U*Real.log U := HC U hU
      _ ≤ C*U*(5*Real.log T*Real.exp u) := by rw [hlogU]; exact mul_le_mul_of_nonneg_left hmaj (by positivity [show 0 ≤ U by linarith])
      _ = _ := by
        dsimp only [U,A]
        rw [show 3*u = 2*u+u by ring,Real.exp_add]
        ring
  have H := finite_density_exponential_moment S w y (A := 3) (C := A) (b := 0) (r := 0)
    (by norm_num) (by dsimp [A]; positivity [show 0 ≤ Real.log T by linarith]) le_rfl
    (fun _ _ => Nat.cast_nonneg _) hy hy hcnt
  have heq (z : ℂ) (hz : z ∈ S) : Real.exp (-(3+1+0)*y z) = T^2/z.im^2 := by
    have him := hT₀.trans_le (hS z hz).2.2.2
    rw [show -(3+1+0)*y z = -(2*Real.log (|z.im|/T)) by dsimp only [y]; ring,
      Real.exp_neg, two_mul, Real.exp_add, Real.exp_log (div_pos him hT₀)]
    rw [←sq,div_pow,sq_abs,inv_div]
  have hscaled : (∑ z ∈ S, w z/z.im^2)*T^2 ≤ A*Real.exp 3/(1-Real.exp (-1)) := by
    calc
      _ = ∑ z ∈ S, w z*Real.exp (-(3+1+0)*y z) := by
        rw [Finset.sum_mul]; apply sum_congr rfl; intro z hz; rw [heq z hz]; ring
      _ ≤ _ := by simpa using H
  apply (le_div_iff₀ (sq_pos_of_pos hT₀)).mpr hscaled |>.trans_eq
  dsimp only [K,A]
  field_simp [hT₀.ne',hd.ne']

/-- The complete reciprocal-square tail over distinct nontrivial zeros, counted with
analytic multiplicity, has the same O(log T / T) estimate at every T ≥ 2. -/
theorem tsum_zeroMultiplicity_div_im_sq_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ {T : ℝ}, 2 ≤ T →
      (∑' z : CriticalStripZeros, if T ≤ |(z:ℂ).im| then (zeroMultiplicity z : ℝ)/(z:ℂ).im^2 else 0)
        ≤ K*(Real.log T/T) := by
  obtain ⟨K,hK,H⟩ := sum_zeroMultiplicity_div_im_sq_tail_le
  refine ⟨K,hK,?_⟩
  intro T hT
  let f (z : ℂ) := if T ≤ |z.im| then (zeroMultiplicity z : ℝ)/z.im^2 else 0
  have hf : Summable fun z : CriticalStripZeros => f z := by
    have hs : Summable (fun z : CriticalStripZeros => (zeroMultiplicity z : ℝ)/(1+(z:ℂ).im^2)) := by
      simpa only [zero_sub,even_two.neg_pow,zeroMultiplicity] using summable_criticalStripZeros_inv_one_add_sq 0
    apply (hs.mul_left 2).of_norm_bounded
    intro z
    dsimp only [f]
    split_ifs with hz
    · have hsq : 1 ≤ (z:ℂ).im^2 := by
        simpa only [one_pow,sq_abs] using pow_le_pow_left₀ zero_le_one (by linarith : 1 ≤ |(z:ℂ).im|) 2
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)),mul_div_assoc',
        div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) (zeroMultiplicity z))]
    · simp only [norm_zero]; positivity
  have hlim := tendsto_sum_nontrivialZerosUpTo_of_summable hf
  apply le_of_tendsto hlim (Filter.Eventually.of_forall (fun U => ?_))
  rw [show (∑ z ∈ nontrivialZerosUpTo U,f z) =
      ∑ z ∈ (nontrivialZerosUpTo U).filter (fun z => T ≤ |z.im|), (zeroMultiplicity z : ℝ)/z.im^2
      by simp [f,Finset.sum_filter]]
  apply H hT
  intro z hz
  obtain ⟨h₁,h₂⟩ := mem_filter.mp hz
  obtain ⟨h₃,h₄,h₅,_⟩ := mem_nontrivialZerosUpTo.mp h₁
  exact ⟨h₃,h₄,h₅,h₂⟩

end AnalyticNumberTheory.PrimeDistribution
