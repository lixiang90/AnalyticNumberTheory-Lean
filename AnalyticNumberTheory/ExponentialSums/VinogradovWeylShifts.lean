import AnalyticNumberTheory.ExponentialSums.VinogradovWeylKernels
import AnalyticNumberTheory.ExponentialSums.VinogradovLogShifts

/-!
# The shift inequality for general polynomial Weyl sums

Translating a polynomial phase introduces a common bounded amplitude and
a lower-degree polynomial depending on the shift. Its highest coefficient
runs through an arithmetic progression. Vinogradov's mean value therefore
controls the original sum through the denominator of the leading coefficient.
-/

open Real Finset Polynomial
open scoped Polynomial
namespace AnalyticNumberTheory.ExponentialSums

/-- Weyl sum on the positive integers through `N`. -/
noncomputable def polynomialWeylSum (P : ℝ[X]) (N : ℕ) : ℂ :=
  ∑ x∈Icc 1 (N:ℤ),e (P.eval (x:ℝ))

private noncomputable def differenceFrequencies (P : ℝ[X]) (k : ℕ) (u : ℤ) (j : Fin k) : ℝ :=
  (polyDiff u P).coeff (j.val+1)

private theorem norm_shifted_polynomial_eq (P : ℝ[X]) {k : ℕ} (hP : P.natDegree≤k+1)
    (B : Finset ℤ) (u : ℤ) :
    ‖∑ x∈B,e (P.eval ((x:ℝ)+u))‖ =
      ‖weightedVinogradovSum B (fun x => e (P.eval (x:ℝ))) (differenceFrequencies P k u)‖ := by
  let D := polyDiff u P
  have hd : D.natDegree≤k := (polyDiff_natDegree_and_coeff u P hP).1
  have hD (x : ℤ) : D.eval (x:ℝ) = D.coeff 0 + ∑ j : Fin k,D.coeff (j.val+1)*(x:ℝ)^(j.val+1) := by
    rw [eval_eq_sum_range' (show D.natDegree<k+1 by omega),sum_range_succ',←Fin.sum_univ_eq_sum_range]
    simp; ring
  have hχ (x : ℤ) : torusChar k (vinogradovCurve k x) (differenceFrequencies P k u) =
      e (∑ j : Fin k,D.coeff (j.val+1)*(x:ℝ)^(j.val+1)) := by
    change torusChar k (vinogradovCurve k x) (fun j => (polyDiff u P).coeff (j.val+1)) = _
    have H := diagonalBilinearChar_curve (differenceFrequencies P k u) x 1
    simpa [diagonalBilinearChar,vinogradovCurve,differenceFrequencies,D] using H
  have he (x : ℤ) : e (P.eval ((x:ℝ)+u)) =
      e (D.coeff 0) * (e (P.eval (x:ℝ))*torusChar k (vinogradovCurve k x) (differenceFrequencies P k u)) := by
    rw [hχ,←e_add,←e_add]
    apply congrArg e
    have H : D.eval (x:ℝ) = P.eval ((x:ℝ)+u)-P.eval (x:ℝ) := eval_polyDiff ..
    rw [hD] at H; linarith only [H]
  simp_rw [he]
  rw [←mul_sum,norm_mul,norm_e,one_mul]; rfl

/-- Raw mean-value estimate after integer shifts, with the remaining
one-dimensional rational-approximation kernel displayed explicitly. -/
theorem polynomialWeylSum_shift_bound {d s : ℕ} (P : ℝ[X]) (hP : P.natDegree≤d+2)
    (N Y : ℕ) {A : ℝ} (hA : 0≤A) (hlarge : A+2*Y≤‖polynomialWeylSum P N‖)
    {a : ℤ} {q : ℕ} (hq : 1≤q) (hcop : a.natAbs.Coprime q)
    (hθ : |P.coeff (d+2)-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    let R (j : Fin (d+1)) := s*N^(j.val+1)
    let L := (2*R (Fin.last d)+1:ℝ)
    (Y:ℝ)^2*A^(4*s) ≤
      (N:ℝ)^(2*s)*vinogradovJ s (d+1) N*(∏ j : Fin d, (2*R j.castSucc+1:ℝ))*
        Y*(L+18*((((d+2)*Y:ℕ)+q:ℝ)*Real.log (2*(q:ℝ))+((d+2)*Y:ℕ)*L/q)) := by
  intro R L
  let B := Icc 1 (N:ℤ)
  let Z := Icc 1 (Y:ℤ)
  let D (j : Fin (d+1)) := Icc (-(R j:ℤ)) (R j)
  let α := differenceFrequencies P (d+1)
  let w (x : ℤ) := e (P.eval (x:ℝ))
  have hα (u v : ℤ) : α u (Fin.last d)-α v (Fin.last d)=P.coeff (d+2)*((d+2:ℕ):ℝ)*(u-v) := by
    have H x := (polyDiff_natDegree_and_coeff (x:ℝ) P hP).2
    change (polyDiff (u:ℝ) P).coeff (d+1)-(polyDiff (v:ℝ) P).coeff (d+1) = _
    rw [H u,H v]; ring
  have hrow (u : ℤ) (hu : u∈Z) : A≤‖weightedVinogradovSum B w (α u)‖ := by
    have hu' := mem_Icc.mp hu
    have H := norm_sum_Ioc_shift_sub_le w (fun x => (norm_e _).le) (show (0:ℤ)≤N by omega)
      (show 0≤u by omega)
    have hb : Ioc (0:ℤ) N=B := by ext i; simp [B]; omega
    rw [hb] at H
    have he : ∀ x : ℤ,w (x+u)=e (P.eval ((x:ℝ)+u)) := by intro x; simp [w]
    have htri := norm_add_le ((∑ x∈B,w x)-(∑ x∈B,w (x+u))) (∑ x∈B,w (x+u))
    rw [sub_add_cancel] at htri
    simp_rw [he] at htri H
    rw [norm_shifted_polynomial_eq P hP] at htri
    have hy : (u:ℝ)≤Y := by exact_mod_cast hu'.2
    change A+2*Y≤‖∑ x∈B,w x‖ at hlarge
    change _ ≤ ‖weightedVinogradovSum B w (differenceFrequencies P (d+1) u)‖
    linarith only [hlarge,htri,H,hy]
  have hsum : (Y:ℝ)*A^(2*s) ≤ ∑ u∈Z,‖weightedVinogradovSum B w (α u)‖^(2*s) := by
    simpa [Z,Int.card_Icc] using sum_le_sum (fun u hu => pow_le_pow_left₀ hA (hrow u hu) (2*s))
  have HW := weightedVinogradov_sampling_box_le s (d+1) B w (fun x _ => (norm_e _).le)
    Z α D (@vinogradovDifference_mem_intervalBox s (d+1) N)
  have HK := vinogradov_sampling_top_coefficient R Y α (by positivity : 0<d+2) hα hq hcop hθ
  calc _ = ((Y:ℝ)*A^(2*s))^2 := by rw [mul_pow,←pow_mul]; congr 2; ring
       _ ≤ _ := (pow_le_pow_left₀ (by positivity) hsum 2).trans HW
       _ ≤ _ := by
             rw [show (B.card:ℝ)=N by simp [B,Int.card_Icc],show (vinogradovCountOn s (d+1) B:ℝ)=vinogradovJ s (d+1) N by rw [vinogradovJ_eq_card_solutions,vinogradovCountOn_interval]]
             have h₀ := mul_le_mul_of_nonneg_left HK (mul_nonneg (pow_nonneg (Nat.cast_nonneg (α:=ℝ) N) (2*s)) (vinogradovJ_nonneg s (d+1) N))
             simpa only [mul_assoc] using h₀

end AnalyticNumberTheory.ExponentialSums
