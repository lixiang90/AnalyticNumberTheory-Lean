import AnalyticNumberTheory.AnalyticTools.EntireFunctions.CenteredPoles
import AnalyticNumberTheory.RiemannZeta.HadamardProduct

/-!
# The centered partial fractions of the zeta logarithmic derivative

Expanding the digamma factor separates every trivial zero from the nontrivial zeros of the
Hadamard product. Subtraction at zero fixes the additive constant directly from ζ at zero.
-/

noncomputable section

open Filter Finset
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.EntireFunctions AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.RiemannZeta

/-- The negative even integers, beginning with `-2`. -/
def trivialZetaZero (n : ℕ) : ℂ := -2 * ((n : ℂ) + 1)

/-- Each negative even integer is a zero of zeta. -/
theorem riemannZeta_trivialZetaZero (n : ℕ) : riemannZeta (trivialZetaZero n) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

private theorem norm_trivialZetaZero (n : ℕ) : ‖trivialZetaZero n‖ = 2*((n : ℝ)+1) := by
  rw [trivialZetaZero, norm_mul, ← Nat.cast_add_one, Complex.norm_natCast]
  norm_num

/-- No negative even zero coincides with the normalization point. -/
theorem trivialZetaZero_ne_zero (n : ℕ) : trivialZetaZero n ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_trivialZetaZero]
  positivity

private theorem finite_trivialZetaZero_norm_le (R : ℝ) : {n | ‖trivialZetaZero n‖ ≤ R}.Finite := by
  apply (Set.finite_Iic ⌈R⌉₊).subset
  intro n hn
  change ‖trivialZetaZero n‖ ≤ R at hn
  rw [norm_trivialZetaZero] at hn
  change n ≤ ⌈R⌉₊
  exact_mod_cast (show (n : ℝ) ≤ ⌈R⌉₊ by linarith [Nat.le_ceil R, Nat.cast_nonneg (α := ℝ) n])

/-- The inverse squared norms of the trivial zeros are summable. -/
theorem summable_trivialZetaZero_inv_sq : Summable fun n => (‖trivialZetaZero n‖^2)⁻¹ := by
  have H := ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left (1/4 : ℝ)
  apply H.congr
  intro n
  rw [norm_trivialZetaZero]
  push_cast
  rw [mul_pow, mul_inv_rev]
  ring

private theorem half_digamma_eq_trivial_sum {s : ℂ} (h : ∀ n, s ≠ trivialZetaZero n) :
    (1/2 : ℂ)*digamma (s/2+1) = -(Real.eulerMascheroniConstant : ℂ)/2 -
      ∑' n, centeredPole (trivialZetaZero n) s := by
  have hΓ (n : ℕ) : s/2+1 ≠ -(n : ℂ) := by
    intro he
    apply h n
    dsimp [trivialZetaZero]
    linear_combination 2*he
  rw [digamma_eq_neg_eulerMascheroni_add_tsum hΓ, mul_add, ← tsum_mul_left,
    sub_eq_add_neg, ← tsum_neg]
  congr 1
  · ring
  · apply tsum_congr
    intro n
    rw [centeredPole_eq (trivialZetaZero_ne_zero n) (h n)]
    have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hs : (n : ℂ)+(s/2+1) ≠ 0 := by
      intro he
      apply h n
      dsimp [trivialZetaZero]
      linear_combination 2*he
    have hsn := sub_ne_zero.mpr (h n)
    dsimp [trivialZetaZero] at hsn ⊢
    field_simp [hn, hs, hsn]
    ring

/-- An enumeration of the nontrivial zeta zeros with their analytic multiplicities and
summable inverse squared radii. -/
structure ZetaZeroEnumeration where
  zero : ℕ → ℂ
  mem_strip : ∀ n, zero n ∈ CriticalStripZeros
  finite_norm_le : ∀ R : ℝ, {n | ‖zero n‖ ≤ R}.Finite
  count_fiber : ∀ ρ ∈ CriticalStripZeros, {n | zero n = ρ}.ncard = analyticOrderNatAt riemannZeta ρ
  summable_inv_sq : Summable fun n => (‖zero n‖^2)⁻¹

/-- Every member of a critical-strip zero enumeration is nonzero. -/
theorem ZetaZeroEnumeration.zero_ne_zero (Z : ZetaZeroEnumeration) (n : ℕ) : Z.zero n ≠ 0 := by
  intro he
  have h := (mem_criticalStripZeros.mp (Z.mem_strip n)).2.1
  simp [he] at h

/-- The centered partial fractions from all nontrivial zeros form an absolutely convergent series. -/
theorem ZetaZeroEnumeration.summable_centered (Z : ZetaZeroEnumeration) (s : ℂ) :
    Summable fun n => centeredPole (Z.zero n) s :=
  summable_centeredPole Z.zero_ne_zero Z.finite_norm_le Z.summable_inv_sq s

/-- The analogous series over all negative even integers also converges absolutely. -/
theorem summable_centered_trivialZetaZero (s : ℂ) :
    Summable fun n => centeredPole (trivialZetaZero n) s :=
  summable_centeredPole trivialZetaZero_ne_zero finite_trivialZetaZero_norm_le
    summable_trivialZetaZero_inv_sq s

/-- The value of the negative logarithmic derivative at the centering point is `-log(2π)`. -/
theorem neg_logDeriv_riemannZeta_zero :
    -deriv riemannZeta 0 / riemannZeta 0 = -Complex.log (2 * (Real.pi : ℂ)) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  ring

/-- The logarithmic derivative of zeta, with all simple-pole terms centered at zero.
The pole at one enters positively in `-ζ'/ζ`, and both zero families enter negatively.
The two series converge absolutely, including at the normalization point. -/
theorem exists_centered_logDeriv_riemannZeta :
    ∃ Z : ZetaZeroEnumeration, ∀ {s : ℂ}, s ≠ 1 → riemannZeta s ≠ 0 →
      -deriv riemannZeta s / riemannZeta s =
        -Complex.log (2 * (Real.pi : ℂ)) + centeredPole 1 s -
          (∑' n, centeredPole (Z.zero n) s) - ∑' n, centeredPole (trivialZetaZero n) s := by
  obtain ⟨a, B, ha, hf, hm, hs, H⟩ := exists_logDeriv_riemannZeta_partial_fractions
  have ha₀ (n : ℕ) : a n ≠ 0 := fun he => by
    have hp := (mem_criticalStripZeros.mp (ha n)).2.1
    simp [he] at hp
  have hS : Summable fun n => (‖a n‖^2)⁻¹ := by
    convert hs using 1
    ext n
    rw [Real.rpow_neg (norm_nonneg _)]; norm_num
  refine ⟨⟨a, ha, hf, hm, hS⟩, ?_⟩
  let D (s : ℂ) := -deriv riemannZeta s / riemannZeta s
  let C : ℂ := -B - (Real.log Real.pi : ℂ)/2 - (Real.eulerMascheroniConstant : ℂ)/2 - 1
  let Q (s : ℂ) := centeredPole 1 s - (∑' n, centeredPole (a n) s) -
    ∑' n, centeredPole (trivialZetaZero n) s
  have hrep (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) : D s = C+Q s := by
    have ht (n : ℕ) : s ≠ trivialZetaZero n := fun he => hz (he ▸ riemannZeta_trivialZetaZero n)
    have hprod (m : ℕ) : s ≠ -2*(m : ℂ) := by
      cases m with
      | zero => simpa using hs0
      | succ n => simpa [trivialZetaZero] using ht n
    have hza (n : ℕ) : s ≠ a n := fun he => hz (he ▸ (mem_criticalStripZeros.mp (ha n)).1)
    have hsum : (∑' n, (1/(s-a n)+1/a n)) = ∑' n, centeredPole (a n) s :=
      tsum_congr fun n => (centeredPole_eq (ha₀ n) (hza n)).symm
    dsimp only [D, C, Q]
    rw [neg_div, H s hprod hs1 hz, half_digamma_eq_trivial_sum ht, hsum,
      centeredPole_eq one_ne_zero hs1, div_one]
    ring
  have hz0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have han : AnalyticAt ℂ riemannZeta 0 :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) 0 zero_ne_one
  have hD : ContinuousAt D 0 := han.deriv.continuousAt.neg.div han.continuousAt hz0
  have hP : Tendsto (centeredPole 1) (𝓝 0) (𝓝 0) := by
    exact tendsto_centeredPole_zero one_ne_zero
  have hQ : Tendsto Q (𝓝 0) (𝓝 0) := by
    simpa [Q] using (hP.sub (tendsto_tsum_centeredPole_zero ha₀ hf hS)).sub
      (tendsto_tsum_centeredPole_zero trivialZetaZero_ne_zero finite_trivialZetaZero_norm_le
        summable_trivialZetaZero_inv_sq)
  have hEv : D =ᶠ[𝓝[≠] 0] (fun s => C + Q s) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_ne_nhds (zero_ne_one : (0 : ℂ) ≠ 1)).filter_mono nhdsWithin_le_nhds,
      (han.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds] with s hs0 hs1 hz
    exact hrep s hs0 hs1 hz
  have hC : D 0 = C := tendsto_nhds_unique ((hD.tendsto.mono_left nhdsWithin_le_nhds).congr' hEv)
    (by simpa only [add_zero] using (tendsto_const_nhds (x := C)).add (hQ.mono_left nhdsWithin_le_nhds))
  intro s hs1 hz
  rw [← neg_logDeriv_riemannZeta_zero]
  by_cases hs0 : s = 0
  · subst s; simp [centeredPole]
  · change D s = D 0 + centeredPole 1 s - (∑' n, centeredPole (a n) s) -
      ∑' n, centeredPole (trivialZetaZero n) s
    rw [hrep s hs0 hs1 hz, hC]
    dsimp only [Q]
    ring

end AnalyticNumberTheory.RiemannZeta
