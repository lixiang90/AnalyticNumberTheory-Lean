import AnalyticNumberTheory.PrimeDistribution.DyadicCharacterSampling
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovBilinear
import AnalyticNumberTheory.SieveMethods.FixedModulusHybridMean

/-!
# Hybrid mean-square inputs for character zero detectors

For a family of primitive characters the conductor-height cost is Q²L.
For the full family at a fixed modulus q it is qL.
-/
noncomputable section
open Real Complex Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- The one-sided hybrid large sieve for all primitive characters with modulus ≤ Q. -/
theorem primitive_family_hybrid_mean (Q : ℕ) {L : ℕ} (hL : 0<L) :
    CharacterHybridMean (primitiveCharacterFamily Q) (fun p n => p.2 n) L ((Q:ℝ)^2*L) := by
  intro N _ a
  let F := primitiveCharacterFamily Q
  let P (p : Σq : ℕ,DirichletCharacter ℂ q) (t : ℝ) :=
    ∑n∈Icc 1 N,a n*p.2 n*(n:ℂ)^(-(I*(t:ℂ)))
  have hc (p) : Continuous (P p) := by
    apply continuous_finsetSum;intro n hn
    have hn₀ : (n:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt (mem_Icc.mp hn).1
    simp_rw [Complex.cpow_def_of_ne_zero hn₀];fun_prop
  change (∑p∈F,∫t in (0:ℝ)..L,‖P p t‖^2)≤_
  apply (sum_le_sum fun p _ => intervalIntegral.integral_mono_interval
    (by simp : -(L:ℝ)≤0) (Nat.cast_nonneg L) le_rfl
    (Filter.Eventually.of_forall fun t => sq_nonneg ‖P p t‖)
    (((hc p).norm.pow 2).intervalIntegrable (μ:=volume) (-(L:ℝ)) L)).trans
  simpa only [F,P,primitiveCharacterFamily,sum_sigma] using
    hybrid_large_sieve_unweighted a N Q (T:=(L:ℝ)) (by exact_mod_cast hL)

/-- The full character group at a single modulus has conductor-height cost qL. -/
theorem fixed_modulus_family_hybrid_mean (q L : ℕ) [NeZero q] :
    CharacterHybridMean (univ : Finset (DirichletCharacter ℂ q)) (fun χ n => χ n) L ((q:ℝ)*L) := by
  intro N hN a
  apply (fixed_modulus_hybrid_mean_square (q:=q) hN a (A:=0) (B:=(L:ℝ)) (Nat.cast_nonneg _)).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hφ : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  rw [sub_zero]
  calc _ ≤ (q:ℝ)*((L:ℝ)+2*π*N/q) := mul_le_mul_of_nonneg_right hφ (by positivity)
       _ = (q:ℝ)*L+2*π*N := by field_simp
       _ ≤ _ := by
         have hsq : 2 ≤ π^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (π-3)]
         have hπ : 2*π≤π^3 := by nlinarith only [mul_le_mul_of_nonneg_right hsq Real.pi_pos.le]
         have hone : 1≤π^3 := by linarith [Real.pi_gt_three]
         have hn := mul_le_mul_of_nonneg_right hπ (Nat.cast_nonneg (α:=ℝ) N)
         have ht := mul_le_mul_of_nonneg_right hone (mul_nonneg hq.le (Nat.cast_nonneg (α:=ℝ) L))
         nlinarith only [hn,ht]
end AnalyticNumberTheory.PrimeDistribution
