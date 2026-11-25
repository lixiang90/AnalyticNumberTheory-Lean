import AnalyticNumberTheory.AnalyticTools.HilbertKernelEstimates
import Mathlib.Data.Matrix.Mul

/-!
# Quadratic form of the mixed Hilbert kernel

A bound for the Gram matrix controls the nonsymmetric kernel with weights
wᵣ wₛ³. Keeping the two pole estimates as parameters makes the resulting
spectral bound independent of the method used to estimate the mixed sum.
-/

open Finset Matrix Real
namespace AnalyticNumberTheory.AnalyticTools

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonsymmetric square kernel in the weighted Hilbert inequality. -/
noncomputable def hilbertMixedMatrix (x w : ι→ℝ) : Matrix ι ι ℝ :=
  fun r s => w r*w s^3/(x r-x s)^2

/-- The quartic and mixed pole bounds give an entrywise upper bound for the Gram matrix. -/
theorem hilbertMixedMatrix_gram_le (x w : ι→ℝ) (hw : ∀i, 0<w i) {C K : ℝ}
    (hfour : ∀s, (∑r,w r^2/(x r-x s)^4)≤C/(w s)^6)
    (hmix : ∀s t, s≠t → (∑r,w r^2/((x r-x s)^2*(x r-x t)^2))≤
      K*(1/(w s)^2+1/(w t)^2)/(x s-x t)^2) :
    ∀ s t, ((hilbertMixedMatrix x w)ᵀ*hilbertMixedMatrix x w) s t ≤
      (C • (1 : Matrix ι ι ℝ)+K • (hilbertMixedMatrix x w+(hilbertMixedMatrix x w)ᵀ)) s t := by
  intro s t
  rw [Matrix.mul_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.smul_apply,Matrix.add_apply]
  simp only [Matrix.transpose_apply,smul_eq_mul]
  rcases eq_or_ne s t with rfl|hst
  · simp only [hilbertMixedMatrix,Matrix.one_apply_eq,sub_self,zero_pow (by decide : 2≠0),div_zero,
      add_zero,mul_zero,mul_one]
    have h := mul_le_mul_of_nonneg_left (hfour s) (pow_nonneg (hw s).le 6)
    calc
      _ = (w s)^6*∑r,w r^2/(x r-x s)^4 := by
        rw [mul_sum]; refine sum_congr rfl fun r _ => ?_; simp only [div_eq_mul_inv,←_root_.inv_pow]; ring
      _ ≤ _ := by convert h using 1; field_simp [(hw s).ne']
  · simp only [Matrix.one_apply_ne hst,mul_zero,zero_add,hilbertMixedMatrix]
    have h := mul_le_mul_of_nonneg_left (hmix s t hst) (mul_nonneg (pow_nonneg (hw s).le 3) (pow_nonneg (hw t).le 3))
    calc
      _ = ((w s)^3*(w t)^3)*∑r,w r^2/((x r-x s)^2*(x r-x t)^2) := by
        rw [mul_sum]; refine sum_congr rfl fun r _ => ?_
        simp only [div_eq_mul_inv,_root_.mul_inv_rev]; ring
      _ ≤ _ := by
        convert h using 1
        rw [←neg_sub (x s) (x t),neg_sq]
        simp only [div_eq_mul_inv,one_mul,inv_pow]
        field_simp [(hw s).ne',(hw t).ne'] <;> ring

private theorem real_quadratic_mono {A B : Matrix ι ι ℝ} (hAB : ∀ i j, A i j≤B i j) (v : ι→ℝ) (hv : ∀i, 0≤v i) :
    v ⬝ᵥ (A *ᵥ v)≤v ⬝ᵥ (B *ᵥ v) := by
  apply sum_le_sum; intro i _
  apply mul_le_mul_of_nonneg_left _ (hv i)
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hv j)

/-- A quadratic Gram majorant yields an explicit bound on the mixed quadratic form
at every nonnegative unit vector. -/
theorem quadratic_form_le_of_gram_majorant (T : Matrix ι ι ℝ) {C K : ℝ} (hC : 0≤C)
    (hgram : ∀s t,(Tᵀ*T) s t ≤ (C • (1 : Matrix ι ι ℝ)+K • (T+Tᵀ)) s t) (v : ι→ℝ)
    (hv : ∀i,0≤v i) (hn : v ⬝ᵥ v=1) :
    v ⬝ᵥ (T *ᵥ v)≤K+sqrt (K^2+C) := by
  let D := v ⬝ᵥ (T *ᵥ v)
  have hc := sum_mul_sq_le_sq_mul_sq univ v (T *ᵥ v)
  have hn' : (∑i,(v i)^2)=1 := by simpa only [sq,dotProduct] using hn
  rw [hn',one_mul] at hc
  have gram : (∑i,((T *ᵥ v) i)^2) = v ⬝ᵥ ((Tᵀ*T) *ᵥ v) := by
    rw [←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]; simp only [dotProduct,sq]
  have trans : v ⬝ᵥ (Tᵀ *ᵥ v) = D := by
    dsimp [D]; rw [mulVec_transpose,dotProduct_comm v,←dotProduct_mulVec]
  have h := real_quadratic_mono hgram v hv
  rw [add_mulVec,dotProduct_add,smul_mulVec,smul_mulVec,dotProduct_smul,dotProduct_smul,
    one_mulVec,hn,add_mulVec,dotProduct_add,trans] at h
  simp only [smul_eq_mul,mul_one] at h
  change D^2≤_ at hc
  rw [gram] at hc
  have hh : (D-K)^2≤K^2+C := by dsimp [D] at *; nlinarith [hc.trans h]
  have ht : D-K ≤ sqrt (K^2+C) := (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    (by rw [sq_abs,sq_sqrt (by positivity)]; exact hh))
  linarith

end AnalyticNumberTheory.AnalyticTools
