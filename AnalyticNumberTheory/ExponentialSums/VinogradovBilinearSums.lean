import AnalyticNumberTheory.ExponentialSums.VinogradovMixedMoments
import AnalyticNumberTheory.ExponentialSums.VinogradovAffine
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import Mathlib.Algebra.Order.Chebyshev

/-!
# Bilinear exponential sums and Vinogradov's mean value

The even moment of a polynomial exponential sum expands over differences of
vectors of power sums. Summing this identity over several points on the torus
and interchanging the two finite sums retains the cancellation in every
frequency coordinate.
-/

open Finset Complex
namespace AnalyticNumberTheory.ExponentialSums

/-- The difference of the two moment vectors in a pair of tuples. -/
def vinogradovDifference {s : ℕ} (k : ℕ) (p : (Fin s → ℤ) × (Fin s → ℤ)) : Fin k → ℤ :=
  vinogradovMoments k p.1 - vinogradovMoments k p.2

/-- The even moment at one torus point, before integration, is the Fourier
sum over all ordered pairs of tuples. -/
theorem vinogradov_evenMoment_expansion (s k : ℕ) (B : Finset ℤ) (α : Fin k → ℝ) :
    ((‖vinogradovTorusSum k B α‖^(2*s) : ℝ) : ℂ) =
      ∑ p ∈ vinogradovTuples s B ×ˢ vinogradovTuples s B,
        torusChar k (vinogradovDifference k p) α := by
  let U := vinogradovTuples s B
  have hp : torusCharSum U (vinogradovMoments k) α = vinogradovTorusSum k B α ^ s := by
    simpa [U,vinogradovTuples] using torusCharSum_moments_pi (fun _ : Fin s => B) α
  have he : ∀ p : (Fin s → ℤ) × (Fin s → ℤ), torusChar k (vinogradovDifference k p) α =
      torusChar k (vinogradovMoments k p.1) α * star (torusChar k (vinogradovMoments k p.2) α) := by
    intro p; rw [vinogradovDifference,sub_eq_add_neg,torusChar_add,torusChar_neg]
  simp only [he,sum_product,←mul_sum,←sum_mul,←star_sum]
  change _ = torusCharSum U (vinogradovMoments k) α * star (torusCharSum U (vinogradovMoments k) α)
  rw [hp,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_pow]
  congr 1; ring

/-- The sum of the even moments at finitely many sample points is controlled
by the Fourier transform of the sampling measure at the tuple differences. -/
theorem sum_vinogradov_evenMoment_le {ι : Type*} (s k : ℕ) (B : Finset ℤ)
    (S : Finset ι) (α : ι → Fin k → ℝ) :
    ∑ u ∈ S, ‖vinogradovTorusSum k B (α u)‖^(2*s) ≤
      ∑ p ∈ vinogradovTuples s B ×ˢ vinogradovTuples s B,
        ‖∑ u ∈ S, torusChar k (vinogradovDifference k p) (α u)‖ := by
  have hpos : 0 ≤ ∑ u ∈ S, ‖vinogradovTorusSum k B (α u)‖^(2*s) := by positivity
  calc _ = ‖∑ u ∈ S, ((‖vinogradovTorusSum k B (α u)‖^(2*s) : ℝ):ℂ)‖ := by
             rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_of_nonneg hpos]
       _ = _ := by simp_rw [vinogradov_evenMoment_expansion]; rw [sum_comm]
       _ ≤ _ := norm_sum_le ..

/-- A bound on every fiber of the moment-difference map replaces a sum over
tuple pairs by a sum over any enclosing frequency box. -/
theorem sum_vinogradovDifference_le {s k : ℕ} (B : Finset ℤ) (H : Finset (Fin k → ℤ))
    (hbox : ∀ p ∈ vinogradovTuples s B ×ˢ vinogradovTuples s B, vinogradovDifference k p ∈ H)
    (f : (Fin k → ℤ) → ℝ) (hf : ∀ u∈H, 0≤f u) :
    ∑ p ∈ vinogradovTuples s B ×ˢ vinogradovTuples s B, f (vinogradovDifference k p) ≤
      (vinogradovCountOn s k B:ℝ) * ∑ u ∈ H, f u := by
  classical
  let P := vinogradovTuples s B
  let d := @vinogradovDifference s k
  have hmem (u : Fin k → ℤ) : (P ×ˢ P).filter (fun p => d p=u) = vinogradovShiftedPairs P u := by
    ext p
    simp only [P,d,vinogradovDifference,vinogradovShiftedPairs,mem_filter,sub_eq_iff_eq_add]
    rw [add_comm u]
  change ∑ p ∈ P ×ˢ P, f (d p) ≤ _
  rw [←sum_fiberwise_of_maps_to (t:=H) hbox,mul_sum]
  apply sum_le_sum
  intro u hu
  calc _ = ∑ _p ∈ (P ×ˢ P).filter (fun p => d p = u), f u := by
             apply sum_congr rfl; intro p hp; exact congrArg f (mem_filter.mp hp).2
       _ = _ := by simp only [hmem,sum_const,nsmul_eq_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (vinogradovShiftedPairs_card_le P u)) (hf u hu)

/-- The character of a diagonal bilinear form with coefficient vector `α`. -/
noncomputable def diagonalBilinearChar {k : ℕ} (α : Fin k → ℝ) (u v : Fin k → ℤ) : ℂ :=
  torusChar k u (fun j => α j * v j)

theorem diagonalBilinearChar_comm {k : ℕ} (α : Fin k → ℝ) (u v : Fin k → ℤ) :
    diagonalBilinearChar α u v = diagonalBilinearChar α v u := by
  unfold diagonalBilinearChar torusChar
  apply prod_congr rfl; intro j _; congr 1; ring

/-- On a rectangular frequency box the double Fourier kernel separates
exactly into its one-dimensional geometric sums. -/
theorem sum_norm_diagonalBilinearChar_pi {k : ℕ} (α : Fin k → ℝ) (D : Fin k → Finset ℤ) :
    (∑ g ∈ Fintype.piFinset D, ‖∑ h ∈ Fintype.piFinset D, diagonalBilinearChar α g h‖) =
      ∏ j, ∑ u ∈ D j, ‖∑ v ∈ D j, e (α j * v * u)‖ := by
  classical
  have he (g : Fin k → ℤ) : (∑ h ∈ Fintype.piFinset D, diagonalBilinearChar α g h) =
      ∏ j, ∑ v ∈ D j, e (α j * v * g j) := by
    rw [prod_univ_sum]; rfl
  simp_rw [he,norm_prod]
  rw [prod_univ_sum]

/-- The bilinear exponential sum associated to a vector of coefficients.
Its phase is the polynomial in the product of its two summation variables. -/
noncomputable def vinogradovBilinearSum {k : ℕ} (B : Finset ℤ) (α : Fin k → ℝ) : ℂ :=
  ∑ x ∈ B, vinogradovTorusSum k B (fun j => α j * vinogradovCurve k x j)

private theorem pow_sum_nonneg_le {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S, 0≤f i) {d : ℕ} (hd : 0<d) :
    (∑ i∈S,f i)^d ≤ (S.card:ℝ)^(d-1)*∑ i∈S,(f i)^d := by
  simpa only [Nat.sub_add_cancel hd] using pow_sum_le_card_mul_sum_pow hf (d-1)

/-- Vinogradov's bilinear mean-value inequality. Every frequency coordinate
contributes a separate one-dimensional exponential sum. -/
theorem vinogradovBilinearSum_pow_le {s k : ℕ} (hs : 0<s) (B : Finset ℤ)
    (α : Fin k → ℝ) (D : Fin k → Finset ℤ)
    (hbox : ∀ p ∈ vinogradovTuples s B ×ˢ vinogradovTuples s B,
      vinogradovDifference k p ∈ Fintype.piFinset D) :
    ‖vinogradovBilinearSum B α‖^(4*s^2) ≤
      (B.card:ℝ)^(8*s^2-4*s) * (vinogradovCountOn s k B:ℝ)^2 *
        ∏ j, ∑ u ∈ D j, ‖∑ v ∈ D j, e (α j * v * u)‖ := by
  classical
  let d := 2*s
  have hd : 0<d := by dsimp [d]; omega
  let b := (B.card:ℝ)
  let J := (vinogradovCountOn s k B:ℝ)
  let U := vinogradovTuples s B
  let P := U ×ˢ U
  let H := Fintype.piFinset D
  let V (h : Fin k → ℤ) := vinogradovTorusSum k B (fun j => α j * h j)
  let F (g : Fin k → ℤ) := ‖∑ h ∈ H, diagonalBilinearChar α g h‖
  have hkernel (h : Fin k → ℤ) :
      (∑ x ∈ B, torusChar k h (fun j => α j * vinogradovCurve k x j)) = V h := by
    exact sum_congr rfl fun x _ => diagonalBilinearChar_comm α h (vinogradovCurve k x)
  have h1 : ‖vinogradovBilinearSum B α‖^d ≤ b^(d-1)*
      ∑ p∈P, ‖V (vinogradovDifference k p)‖ := by
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) d).trans
    apply (pow_sum_nonneg_le B _ (fun x _ => norm_nonneg _) hd).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [hkernel] using sum_vinogradov_evenMoment_le s k B B
      (fun x j => α j * vinogradovCurve k x j)
  have hcard : (P.card:ℝ) = b^d := by
    simp [P,U,vinogradovTuples,Fintype.card_piFinset,b,d,pow_mul,sq,mul_pow]
  have h2 : (∑ p∈P, ‖V (vinogradovDifference k p)‖)^d ≤
      (b^d)^(d-1)*(J*∑ h∈H, ‖V h‖^d) := by
    apply (pow_sum_nonneg_le P _ (fun p _ => norm_nonneg _) hd).trans
    rw [hcard]
    apply mul_le_mul_of_nonneg_left _ (by dsimp [b]; positivity)
    exact sum_vinogradovDifference_le B H hbox _ (fun h _ => pow_nonneg (norm_nonneg _) d)
  have h3 : (∑ h∈H, ‖V h‖^d) ≤ J*∑ g∈H,F g := by
    exact (sum_vinogradov_evenMoment_le s k B H (fun h j => α j * h j)).trans
      (sum_vinogradovDifference_le B H hbox F (fun g _ => norm_nonneg _))
  have hexp : 4*s^2=d*d := by dsimp [d]; ring
  have hexp' : 8*s^2-4*s=(d-1)*d+d*(d-1) := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
    dsimp [d]
    rw [show 2*(a+1)-1=2*a+1 by omega]
    apply Nat.sub_eq_of_eq_add
    ring
  rw [hexp,pow_mul]
  calc _ ≤ (b^(d-1)*(∑ p∈P, ‖V (vinogradovDifference k p)‖))^d :=
             pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) h1 d
       _ ≤ (b^(d-1))^d*((b^d)^(d-1)*(J*(J*∑ g∈H,F g))) := by
             rw [mul_pow]
             apply mul_le_mul_of_nonneg_left _ (by dsimp [b]; positivity)
             exact h2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by dsimp [J]; positivity)) (by dsimp [b]; positivity))
       _ = _ := by
             rw [←pow_mul,←pow_mul,hexp',pow_add,←sum_norm_diagonalBilinearChar_pi]
             dsimp only [F,H,b,J]; ring

/-- The one-dimensional kernel in a symmetric integral frequency interval. -/
noncomputable def vinogradovLinearKernel (R : ℕ) (θ : ℝ) : ℝ :=
  ∑ u ∈ Icc (-(R:ℤ)) R, ‖∑ v ∈ Icc (-(R:ℤ)) R, e (θ * v * u)‖

/-- Differences of moment vectors from an interval of length `N` lie in the
rectangular frequency box with radii `s N^j`. -/
theorem vinogradovDifference_mem_intervalBox {s k N : ℕ}
    (p : (Fin s → ℤ) × (Fin s → ℤ))
    (hp : p∈vinogradovTuples s (Icc 1 (N:ℤ)) ×ˢ vinogradovTuples s (Icc 1 (N:ℤ))) :
    vinogradovDifference k p∈Fintype.piFinset (fun j : Fin k =>
      Icc (-(s*N^(j.val+1):ℕ):ℤ) (s*N^(j.val+1):ℕ)) := by
  let I := Icc 1 (N:ℤ)
  have hm (x : Fin s → ℤ) (hx : x ∈ vinogradovTuples s I) (j : Fin k) :
      0 ≤ vinogradovMoments k x j ∧ vinogradovMoments k x j ≤ (s*N^(j.val+1):ℕ) := by
    have hv := Fintype.mem_piFinset.mp hx
    have hxi (i : Fin s) := mem_Icc.mp (hv i)
    refine ⟨sum_nonneg (fun i _ => pow_nonneg (by have := (hxi i).1; omega) _),?_⟩
    calc _ ≤ ∑ _i : Fin s, (N:ℤ)^(j.val+1) :=
               sum_le_sum fun i _ => pow_le_pow_left₀ (by have := (hxi i).1; omega) (hxi i).2 _
         _ = _ := by simp
  apply Fintype.mem_piFinset.mpr; intro j
  have h1 := hm p.1 (mem_product.mp hp).1 j
  have h2 := hm p.2 (mem_product.mp hp).2 j
  apply mem_Icc.mpr
  change -(s*N^(j.val+1):ℕ) ≤ vinogradovMoments k p.1 j-vinogradovMoments k p.2 j ∧
    vinogradovMoments k p.1 j-vinogradovMoments k p.2 j ≤ (s*N^(j.val+1):ℕ)
  omega

/-- For the interval of length `N`, the homogeneous solution count in the
bilinear inequality is the analytic mean value `J`, and the frequency radii
are exactly `s N^j` for `1 ≤ j ≤ k`. -/
theorem vinogradovBilinearSum_interval_le {s k : ℕ} (hs : 0<s) (N : ℕ) (α : Fin k → ℝ) :
    ‖vinogradovBilinearSum (Icc 1 (N:ℤ)) α‖^(4*s^2) ≤
      (N:ℝ)^(8*s^2-4*s) * (vinogradovJ s k N)^2 *
        ∏ j, vinogradovLinearKernel (s*N^(j.val+1)) (α j) := by
  let I := Icc 1 (N:ℤ)
  let D (j : Fin k) := Icc (-(s*N^(j.val+1):ℕ):ℤ) (s*N^(j.val+1):ℕ)
  have hbox := @vinogradovDifference_mem_intervalBox s k N
  have H := vinogradovBilinearSum_pow_le hs I α D hbox
  simpa [I,D,vinogradovCountOn_interval,vinogradovJ_eq_card_solutions,Int.card_Icc,
    vinogradovLinearKernel] using H

end AnalyticNumberTheory.ExponentialSums
