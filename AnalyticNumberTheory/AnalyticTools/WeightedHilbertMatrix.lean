import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The weighted Hilbert matrix

Squaring the Hermitian matrix with entries i wᵣ wₛ/(xᵣ−xₛ) yields an explicit
real symmetric term and a commutator. The commutator has zero quadratic form
on each eigenvector, even when the weights vary.
-/

open Finset Matrix Complex

namespace AnalyticNumberTheory.AnalyticTools

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hermitian form of the finite discrete Hilbert transform with weights on both indices. -/
noncomputable def weightedHilbertMatrix (x w : ι→ℝ) : Matrix ι ι ℂ :=
  fun s t => I*(w s*w t/(x s-x t) : ℝ)

private noncomputable def poleSum (x w : ι→ℝ) (s : ι) : ℝ := ∑r,w r^2/(x r-x s)

private noncomputable def poleDiagonal (x w : ι→ℝ) : Matrix ι ι ℂ :=
  diagonal fun s => (-I)*(poleSum x w s : ℂ)

/-- Real symmetric remainder in the square of the weighted Hilbert matrix. -/
noncomputable def hilbertSquareRemainder (x w : ι→ℝ) : Matrix ι ι ℝ := fun s t =>
  if s=t then ∑r,(w r*w s/(x r-x s))^2
  else w s*w t*(w s^2+w t^2)/(x s-x t)^2

theorem weightedHilbertMatrix_isHermitian (x w : ι→ℝ) : (weightedHilbertMatrix x w).IsHermitian := by
  ext s t
  simp only [conjTranspose_apply,weightedHilbertMatrix,star_mul',Complex.star_def,
    map_mul,conj_I,conj_ofReal]
  rw [←neg_sub (x s) (x t),div_neg,mul_comm (w t) (w s),Complex.ofReal_neg]; ring

private theorem splitDoublePole (x w : ι→ℝ) (hx : Function.Injective x) {s t : ι} (hst : s≠t) (r : ι) :
    w r^2/((x r-x s)*(x r-x t)) =
      (w r^2/(x r-x s)-w r^2/(x r-x t))/(x s-x t)+
      ((if r=s then w s^2 else 0)+(if r=t then w t^2 else 0))/(x s-x t)^2 := by
  have hst' := sub_ne_zero.mpr (hx.ne hst)
  rcases eq_or_ne r s with rfl|hrs
  · simp only [sub_self,zero_mul,div_zero,ite_true,hst,ite_false,add_zero,zero_sub]
    field_simp; ring
  rcases eq_or_ne r t with rfl|hrt
  · simp only [sub_self,mul_zero,div_zero,hrs,ite_false,ite_true,zero_add,sub_zero]
    rw [←neg_sub (x s) (x r)]; field_simp; ring
  · simp only [hrs,hrt,ite_false,add_zero,zero_div]
    field_simp [sub_ne_zero.mpr (hx.ne hrs),sub_ne_zero.mpr (hx.ne hrt),hst']; ring

/-- Partial fractions express the square as a real symmetric remainder plus a commutator. -/
theorem weightedHilbertMatrix_square (x w : ι→ℝ) (hx : Function.Injective x) :
    weightedHilbertMatrix x w * weightedHilbertMatrix x w =
      (hilbertSquareRemainder x w).map (fun t => (t:ℂ))+
      (poleDiagonal x w*weightedHilbertMatrix x w-weightedHilbertMatrix x w*poleDiagonal x w) := by
  ext s t
  simp only [Matrix.add_apply,Matrix.sub_apply,poleDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.map_apply]
  rw [Matrix.mul_apply]
  have hp (r : ι) : weightedHilbertMatrix x w s r*weightedHilbertMatrix x w r t =
      ((w s*w t*(w r^2/((x r-x s)*(x r-x t))) : ℝ):ℂ) := by
    simp only [weightedHilbertMatrix]
    rw [←neg_sub (x r) (x s),div_neg,Complex.ofReal_neg]
    push_cast
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring_nf
    rw [I_sq]; ring
  simp_rw [hp,←Complex.ofReal_sum,←mul_sum]
  rcases eq_or_ne s t with rfl|hst
  · simp only [weightedHilbertMatrix,sub_self,div_zero,Complex.ofReal_zero,mul_zero,zero_mul,
      add_zero,hilbertSquareRemainder,ite_true]
    congr 1
    rw [mul_sum]; refine sum_congr rfl fun r _ => ?_; simp only [div_eq_mul_inv,_root_.mul_inv_rev]; ring
  · simp only [splitDoublePole x w hx hst,sum_add_distrib,←sum_div,sum_sub_distrib,
      ←sum_div,sum_add_distrib,sum_ite_eq',mem_univ,ite_true]
    change (((w s*w t*((poleSum x w s-poleSum x w t)/(x s-x t)+(w s^2+w t^2)/(x s-x t)^2)):ℝ):ℂ) = _
    simp only [hilbertSquareRemainder,hst,ite_false,weightedHilbertMatrix]
    push_cast
    ring_nf
    rw [I_sq]; ring

/-- The quadratic form of a matrix commutator vanishes on an eigenvector of the
Hermitian member. -/
theorem hermitian_commutator_eigenvector {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (P : Matrix ι ι ℂ) {lam : ℝ} {v : ι→ℂ} (hv : A *ᵥ v=(lam:ℂ) • v) :
    star v ⬝ᵥ ((P*A-A*P) *ᵥ v)=0 := by
  have hleft : star v ᵥ* A = (lam:ℂ) • star v := by
    have h := congrArg star hv
    simpa only [star_mulVec,hA.eq,star_smul,Complex.star_def,conj_ofReal] using h
  rw [sub_mulVec,dotProduct_sub,←mulVec_mulVec,←mulVec_mulVec,hv,mulVec_smul,dotProduct_smul,
    dotProduct_mulVec (star v) A,hleft,smul_dotProduct]
  simp only [smul_eq_mul,sub_self]

/-- On a unit eigenvector, the quadratic form of the real remainder equals the square
of the eigenvalue. -/
theorem weightedHilbert_eigen_remainder (x w : ι→ℝ) (hx : Function.Injective x)
    {lam : ℝ} {v : ι→ℂ} (hv : weightedHilbertMatrix x w *ᵥ v=(lam:ℂ) • v)
    (hn : star v ⬝ᵥ v=1) :
    star v ⬝ᵥ (((hilbertSquareRemainder x w).map (fun z => (z:ℂ))) *ᵥ v)=(lam:ℂ)^2 := by
  let A := weightedHilbertMatrix x w
  have h := hermitian_commutator_eigenvector (weightedHilbertMatrix_isHermitian x w) (poleDiagonal x w) hv
  have hs := congrArg (fun T : Matrix ι ι ℂ => star v ⬝ᵥ (T *ᵥ v)) (weightedHilbertMatrix_square x w hx)
  simp only [add_mulVec,dotProduct_add,h,add_zero,←mulVec_mulVec,mulVec_smul,hv,dotProduct_smul,
    hn,smul_eq_mul,mul_one] at hs
  simpa only [sq] using hs.symm

/-- Uniform control of the Hermitian eigenvalues bounds its quadratic form on all vectors. -/
theorem norm_hermitian_form_le_of_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {B : ℝ} (hB : ∀j, |hA.eigenvalues j|≤B) (u : ι→ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖≤B*∑r,‖u r‖^2 := by
  let b := hA.eigenvectorBasis
  let U : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  have hu := (b.sum_repr' U).symm
  have he (j : ι) : Matrix.toEuclideanLin A (b j)=(hA.eigenvalues j:ℂ) • b j := by
    ext k
    simpa [Matrix.toLpLin_apply,b,RCLike.real_smul_eq_coe_smul] using congrFun (hA.mulVec_eigenvectorBasis j) k
  have hf : Matrix.toEuclideanLin A U=∑j,(inner ℂ (b j) U*(hA.eigenvalues j:ℂ)) • b j := by
    conv_lhs => rw [hu]
    simp_rw [map_sum,map_smul,he,smul_smul]
  have huq : inner ℂ U (Matrix.toEuclideanLin A U)=star u ⬝ᵥ (A *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]; rfl
  rw [←huq]
  rw [hf,inner_sum]
  calc
    _ ≤ ∑j,‖inner ℂ U ((inner ℂ (b j) U*(hA.eigenvalues j:ℂ)) • b j)‖ := norm_sum_le ..
    _ ≤ ∑j,B*‖inner ℂ (b j) U‖^2 := by
      refine sum_le_sum fun j _ => ?_
      rw [inner_smul_right,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_inner_symm U (b j)]
      nlinarith only [mul_le_mul_of_nonneg_right (hB j) (sq_nonneg ‖inner ℂ (b j) U‖)]
    _ = B*∑r,‖u r‖^2 := by
      rw [←mul_sum,b.sum_sq_norm_inner_right,EuclideanSpace.norm_sq_eq]

end AnalyticNumberTheory.AnalyticTools
