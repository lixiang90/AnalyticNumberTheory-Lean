import AnalyticNumberTheory.ExponentialSums.VinogradovTorus
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Mixed Vinogradov moments

The arithmetic–geometric mean inequality bounds a mixed moment by the largest
pure moment. Convexity also bounds powers of sums while retaining an arbitrary
nonnegative weight, as required for separating the nonsingular variables.
-/

open Finset Real Complex
namespace AnalyticNumberTheory.ExponentialSums

/-- The integral moment curve on `ℤ`. -/
def vinogradovCurve (k : ℕ) (n : ℤ) (j : Fin k) : ℤ := n^(j.val+1)

/-- The exponential sum on the moment curve with a finite integer support. -/
noncomputable def vinogradovTorusSum (k : ℕ) (S : Finset ℤ) :=
  torusCharSum S (vinogradovCurve k)

theorem torusChar_sum {k : ℕ} {ι : Type*} (S : Finset ι) (u : ι → Fin k → ℤ) (α : Fin k → ℝ) :
    torusChar k (∑ i ∈ S, u i) α = ∏ i ∈ S, torusChar k (u i) α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [sum_insert hi,prod_insert hi,torusChar_add,ih]

/-- The character sum of a rectangular family of tuples factors by coordinate. -/
theorem torusCharSum_moments_pi {s k : ℕ} (S : Fin s → Finset ℤ) (α : Fin k → ℝ) :
    torusCharSum (Fintype.piFinset S) (vinogradovMoments k) α =
      ∏ i, vinogradovTorusSum k (S i) α := by
  classical
  simp only [vinogradovTorusSum,torusCharSum]
  rw [prod_univ_sum]
  apply sum_congr rfl
  intro x _
  have he : vinogradovMoments k x = ∑ i, vinogradovCurve k (x i) := by
    funext j; simp [vinogradovMoments,vinogradovCurve]
  rw [he,torusChar_sum]

/-- On equal supports the matching-pair count equals the ordinary even moment. -/
theorem vinogradov_box_moment_eq {s k : ℕ} (B : Finset ℤ) :
    torusIntegral k (fun α => ‖vinogradovTorusSum k B α‖^(2*s)) =
      ((vinogradovShiftedPairs (Fintype.piFinset (fun _ : Fin s => B)) (0:Fin k → ℤ)).card:ℝ) := by
  let P := Fintype.piFinset (fun _ : Fin s => B)
  have H := matching_card_eq_torusIntegral P P (vinogradovMoments k) (vinogradovMoments k)
  simp only [vinogradovShiftedPairs,add_zero]
  rw [H]
  congr 1; funext α
  simp only [P,torusCharSum_moments_pi,prod_const,card_univ,Fintype.card_fin]
  rw [Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq,norm_pow]
  ring

/-- A product of absolute values is bounded in mean by the common upper bound on the pure moments. -/
theorem torusIntegral_prod_norm_le {k : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → (Fin k → ℝ) → ℂ) (hf : ∀ i, Continuous (f i)) {H : ℝ}
    (hH : ∀ i, torusIntegral k (fun α => ‖f i α‖^(Fintype.card ι)) ≤ H) :
    torusIntegral k (fun α => ∏ i, ‖f i α‖) ≤ H := by
  let d := Fintype.card ι
  have hd : 0 < (d:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hw : (∑ _i : ι, (d:ℝ)⁻¹) = 1 := by simp [d,hd.ne']
  have hm (α : Fin k → ℝ) : ∏ i, ‖f i α‖ ≤ (d:ℝ)⁻¹ * ∑ i, ‖f i α‖^d := by
    have h := Real.geom_mean_le_arith_mean_weighted univ (fun _ : ι => (d:ℝ)⁻¹)
      (fun i => ‖f i α‖^d) (fun _ _ => inv_nonneg.mpr hd.le) hw (fun _ _ => by positivity)
    rw [←mul_sum] at h
    apply le_trans _ h
    exact le_of_eq (prod_congr rfl fun i _ => by
      rw [←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _),mul_inv_cancel₀ hd.ne',Real.rpow_one])
  apply (torusIntegral_mono k (continuous_finsetProd _ (fun i _ => (hf i).norm))
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => (hf i).norm.pow d))) hm).trans
  change torusIntegral k (fun α => (d:ℝ)⁻¹*∑ i, ‖f i α‖^d) ≤ H
  rw [torusIntegral_const_mul,torusIntegral_finsetSum k univ (fun i α => ‖f i α‖^d) (fun i _ => (hf i).norm.pow d)]
  apply (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hH i)) (inv_nonneg.mpr hd.le)).trans_eq
  simp only [sum_const,card_univ,nsmul_eq_mul]
  change (d:ℝ)⁻¹*((d:ℝ)*H)=H
  field_simp

/-- Convexity splits a power of a sum, retaining a nonnegative common weight. -/
theorem torusIntegral_weight_norm_sum_pow_le {k d : ℕ} (hd : 0<d) {ι : Type*} (S : Finset ι)
    (hS : S.Nonempty) (f : ι → (Fin k → ℝ) → ℂ) (hf : ∀ i∈S, Continuous (f i))
    (w : (Fin k → ℝ) → ℝ) (hw : Continuous w) (hw0 : ∀ α, 0≤w α) :
    torusIntegral k (fun α => w α*‖∑ i ∈ S, f i α‖^d) ≤
      (S.card:ℝ)^(d-1)*∑ i ∈ S, torusIntegral k (fun α => w α*‖f i α‖^d) := by
  let n := (S.card:ℝ)
  have hn : 0<n := Nat.cast_pos.mpr hS.card_pos
  have hc : n^d = n*n^(d-1) := by rw [← pow_succ',Nat.sub_add_cancel hd]
  have hpoint (α) : ‖∑ i ∈ S,f i α‖^d ≤ n^(d-1)*∑ i∈S,‖f i α‖^d := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) d).trans ?_
    have h := Real.pow_arith_mean_le_arith_mean_pow S (fun _ => n⁻¹) (fun i => ‖f i α‖)
      (fun _ _ => inv_nonneg.mpr hn.le) (by simp [n, hS.card_ne_zero]) (fun _ _ => norm_nonneg _) d
    simp only [←mul_sum,mul_pow,inv_pow] at h
    have H := mul_le_mul_of_nonneg_left h (pow_nonneg hn.le d)
    rwa [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hn.ne'),one_mul,←mul_assoc,hc,mul_right_comm n,mul_inv_cancel₀ hn.ne',one_mul] at H
  calc _ ≤ torusIntegral k (fun α => n^(d-1)*∑ i∈S, w α*‖f i α‖^d) := by
            apply torusIntegral_mono k (hw.mul ((continuous_finsetSum _ hf).norm.pow d))
              (continuous_const.mul (continuous_finsetSum _ (fun i hi => hw.mul ((hf i hi).norm.pow d))))
            intro α
            change w α*‖∑ i∈S, f i α‖^d ≤ n^(d-1)*∑ i∈S, w α*‖f i α‖^d
            rw [←mul_sum,mul_left_comm (n^(d-1))]
            exact mul_le_mul_of_nonneg_left (hpoint α) (hw0 α)
       _ = _ := by
            rw [torusIntegral_const_mul,torusIntegral_finsetSum k S (fun i α => w α*‖f i α‖^d) (fun i hi => hw.mul ((hf i hi).norm.pow d))]

/-- A product support adds its two frequency vectors and multiplies its two Fourier sums. -/
theorem torusCharSum_product {k : ℕ} {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (α : Fin k → ℝ) :
    torusCharSum (A ×ˢ B) (fun p => f p.1+g p.2) α = torusCharSum A f α*torusCharSum B g α := by
  simp only [torusCharSum,sum_product,sum_mul_sum,torusChar_add]

/-- The squared modulus of an arbitrary front family is retained when taking
the even moment of the unrestricted tail variables. -/
theorem matching_product_power_eq {k s : ℕ} {ι : Type*} (A : Finset ι) (f : ι → Fin k → ℤ)
    (B : Finset ℤ) :
    let P := A ×ˢ Fintype.piFinset (fun _ : Fin s => B)
    let g := fun z : ι × (Fin s → ℤ) => f z.1+vinogradovMoments k z.2
    (((P ×ˢ P).filter (fun z => g z.1=g z.2)).card : ℝ) =
      torusIntegral k (fun α => ‖torusCharSum A f α‖^2*‖vinogradovTorusSum k B α‖^(2*s)) := by
  intro P g
  rw [matching_card_eq_torusIntegral P P g g]
  dsimp only [P,g]
  congr 1; funext α
  simp only [torusCharSum_product,torusCharSum_moments_pi,prod_const,card_univ,Fintype.card_fin,
    Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq,norm_mul,norm_pow]
  ring

end AnalyticNumberTheory.ExponentialSums
