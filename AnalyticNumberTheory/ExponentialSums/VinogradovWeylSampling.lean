import AnalyticNumberTheory.ExponentialSums.VinogradovBilinearSums

/-!
# Sampling polynomial Weyl sums at several coefficient vectors

A common bounded amplitude may contain the leading monomial of a polynomial.
It is independent of the sample index and therefore passes unchanged through
the Fourier expansion in the lower-degree moments.
-/

open Finset Complex
namespace AnalyticNumberTheory.ExponentialSums

/-- Weighted polynomial Weyl sum on a finite integer support. -/
noncomputable def weightedVinogradovSum {k : ℕ} (B : Finset ℤ) (w : ℤ → ℂ) (α : Fin k → ℝ) : ℂ :=
  ∑ x∈B, w x*torusChar k (vinogradovCurve k x) α

private def tupleWeight {s : ℕ} (w : ℤ → ℂ) (x : Fin s → ℤ) : ℂ := ∏ i,w (x i)

private theorem weighted_power {s k : ℕ} (B : Finset ℤ) (w : ℤ → ℂ) (α : Fin k → ℝ) :
    (weightedVinogradovSum B w α)^s =
      ∑ x∈vinogradovTuples s B, tupleWeight w x * torusChar k (vinogradovMoments k x) α := by
  calc _ = ∏ _i : Fin s, (∑ x∈B,w x*torusChar k (vinogradovCurve k x) α) := by simp [weightedVinogradovSum]
       _ = _ := by
             rw [prod_univ_sum]
             apply sum_congr rfl; intro x _
             have he : vinogradovMoments k x = ∑ i,vinogradovCurve k (x i) := by
               funext j; simp [vinogradovMoments,vinogradovCurve]
             rw [he,torusChar_sum,prod_mul_distrib]; rfl

private theorem weighted_evenMoment_expansion {s k : ℕ} (B : Finset ℤ) (w : ℤ → ℂ) (α : Fin k → ℝ) :
    ((‖weightedVinogradovSum B w α‖^(2*s):ℝ):ℂ) =
      ∑ p∈vinogradovTuples s B ×ˢ vinogradovTuples s B,
        (tupleWeight w p.1 * star (tupleWeight w p.2)) * torusChar k (vinogradovDifference k p) α := by
  let d := weightedVinogradovSum B w α
  calc _ = d^s * star (d^s) := by
             rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_pow]; dsimp only [d]; congr 1; ring
       _ = _ := by
             dsimp only [d]; rw [weighted_power,star_sum,sum_mul_sum,sum_product]
             apply sum_congr rfl; intro x _
             apply sum_congr rfl; intro y _
             rw [vinogradovDifference,sub_eq_add_neg,torusChar_add,torusChar_neg,star_mul]; ring

private theorem tupleWeight_norm_le {s : ℕ} {B : Finset ℤ} {w : ℤ → ℂ}
    (hw : ∀ x∈B, ‖w x‖≤1) {x : Fin s → ℤ} (hx : x∈vinogradovTuples s B) :
    ‖tupleWeight w x‖≤1 := by
  rw [tupleWeight,norm_prod]
  simpa using prod_le_prod₀ (s:=univ) (fun i _ => norm_nonneg (w (x i))) (fun i _ => hw _ (Fintype.mem_piFinset.mp hx i))

/-- The sample Fourier transform at moment differences controls the sum of
the even moments, for any common amplitude bounded by one. -/
theorem sum_weightedVinogradov_evenMoment_le {ι : Type*} (s k : ℕ) (B : Finset ℤ)
    (w : ℤ → ℂ) (hw : ∀ x∈B, ‖w x‖≤1) (Y : Finset ι) (α : ι → Fin k → ℝ) :
    ∑ u∈Y,‖weightedVinogradovSum B w (α u)‖^(2*s) ≤
      ∑ p∈vinogradovTuples s B ×ˢ vinogradovTuples s B,‖∑ u∈Y,torusChar k (vinogradovDifference k p) (α u)‖ := by
  have hpos : 0≤∑ u∈Y, ‖weightedVinogradovSum B w (α u)‖^(2*s) := by positivity
  calc _ = ‖∑ u∈Y,((‖weightedVinogradovSum B w (α u)‖^(2*s):ℝ):ℂ)‖ := by
             rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_of_nonneg hpos]
       _ = _ := by simp_rw [weighted_evenMoment_expansion]; rw [sum_comm]
       _ ≤ _ := by
             apply (norm_sum_le ..).trans (sum_le_sum _)
             intro p hp
             rw [←mul_sum,norm_mul,norm_mul,norm_star]
             apply mul_le_of_le_one_left (norm_nonneg _)
             simpa using mul_le_mul (tupleWeight_norm_le hw (mem_product.mp hp).1)
               (tupleWeight_norm_le hw (mem_product.mp hp).2) (norm_nonneg _) zero_le_one

/-- Sampling inequality for polynomial Weyl sums with a common amplitude.
Cauchy–Schwarz introduces the homogeneous mean-value count only once. -/
theorem weightedVinogradov_sampling_inequality {ι : Type*} (s k : ℕ) (B : Finset ℤ)
    (w : ℤ → ℂ) (hw : ∀ x∈B, ‖w x‖≤1) (Y : Finset ι) (α : ι → Fin k → ℝ)
    (H : Finset (Fin k → ℤ)) (hbox : ∀ p∈vinogradovTuples s B ×ˢ vinogradovTuples s B,vinogradovDifference k p∈H) :
    (∑ u∈Y,‖weightedVinogradovSum B w (α u)‖^(2*s))^2 ≤
      (B.card:ℝ)^(2*s) * (vinogradovCountOn s k B:ℝ) * ∑ g∈H, ‖∑ u∈Y,torusChar k g (α u)‖^2 := by
  let P := vinogradovTuples s B ×ˢ vinogradovTuples s B
  have hc : (P.card:ℝ)=(B.card:ℝ)^(2*s) := by
    simp [P,vinogradovTuples,Fintype.card_piFinset,pow_mul,sq,mul_pow]
  let G (h : Fin k → ℤ) := ‖∑ u∈Y,torusChar k h (α u)‖
  apply (pow_le_pow_left₀ (by positivity) (sum_weightedVinogradov_evenMoment_le s k B w hw Y α) 2).trans
  apply (sq_sum_le_card_mul_sum_sq (s:=P) (f:=fun p => G (vinogradovDifference k p))).trans
  rw [hc,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_vinogradovDifference_le B H hbox (fun g => G g^2) (fun _ _ => sq_nonneg _)

private theorem torusChar_sub_sample {k : ℕ} (h : Fin k → ℤ) (α β : Fin k → ℝ) :
    torusChar k h (α-β) = torusChar k h α * star (torusChar k h β) := by
  change (∏ j,e (((α j-β j):ℝ)*h j)) = (∏ j,e (α j*h j))*star (∏ j,e (β j*h j))
  rw [star_prod,←prod_mul_distrib]
  apply prod_congr rfl; intro j _
  rw [star_e,←e_add]; congr 1; ring

/-- Expanding the squared Fourier transform over a rectangular frequency
box yields a product of one-dimensional geometric sums for each pair of samples. -/
theorem rectangular_sampling_gram_le {ι : Type*} {k : ℕ} (D : Fin k → Finset ℤ)
    (Y : Finset ι) (α : ι → Fin k → ℝ) :
    ∑ h ∈ Fintype.piFinset D, ‖∑ u∈Y,torusChar k h (α u)‖^2 ≤
      ∑ p∈Y ×ˢ Y, ∏ j, ‖∑ v∈D j,e ((α p.1 j-α p.2 j)*v)‖ := by
  let H := Fintype.piFinset D
  have he (h : Fin k → ℤ) : ((‖∑ u∈Y,torusChar k h (α u)‖^2:ℝ):ℂ) =
      ∑ p∈Y ×ˢ Y,torusChar k h (α p.1-α p.2) := by
    calc _ = (∑ u∈Y,torusChar k h (α u)) * star (∑ u∈Y,torusChar k h (α u)) := by
               rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
         _ = _ := by simp only [torusChar_sub_sample,sum_product,star_sum,sum_mul_sum]
  have hbox (p : ι×ι) : (∑ h∈H,torusChar k h (α p.1-α p.2)) =
      ∏ j, ∑ v∈D j,e ((α p.1 j-α p.2 j)*v) := by rw [prod_univ_sum]; rfl
  have hp : 0≤ ∑ h∈H,‖∑ u∈Y,torusChar k h (α u)‖^2 := by positivity
  calc _ = ‖∑ h∈H, ((‖∑ u∈Y,torusChar k h (α u)‖^2:ℝ):ℂ)‖ := by
             rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_of_nonneg hp]
       _ = _ := by simp_rw [he]; rw [sum_comm]
       _ ≤ _ := by apply (norm_sum_le ..).trans_eq; simp only [hbox,norm_prod]

/-- Multidimensional Weyl sampling bound. The mean value is multiplied by the
sum of the geometric kernel products along all pairs of sample points. -/
theorem weightedVinogradov_sampling_box_le {ι : Type*} (s k : ℕ) (B : Finset ℤ)
    (w : ℤ → ℂ) (hw : ∀ x∈B,‖w x‖≤1) (Y : Finset ι) (α : ι → Fin k → ℝ)
    (D : Fin k → Finset ℤ) (hbox : ∀ p∈vinogradovTuples s B ×ˢ vinogradovTuples s B,
      vinogradovDifference k p∈Fintype.piFinset D) :
    (∑ u∈Y,‖weightedVinogradovSum B w (α u)‖^(2*s))^2 ≤
      (B.card:ℝ)^(2*s)*(vinogradovCountOn s k B:ℝ)*
        ∑ p∈Y ×ˢ Y, ∏ j, ‖∑ v∈D j,e ((α p.1 j-α p.2 j)*v)‖ := by
  apply (weightedVinogradov_sampling_inequality s k B w hw Y α _ hbox).trans
  exact mul_le_mul_of_nonneg_left (rectangular_sampling_gram_le D Y α) (by positivity)

end AnalyticNumberTheory.ExponentialSums
