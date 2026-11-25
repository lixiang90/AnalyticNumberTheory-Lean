import AnalyticNumberTheory.AnalyticTools.SharpMixedHilbertKernel
import Mathlib.Analysis.Real.Pi.Bounds
import AnalyticNumberTheory.AnalyticTools.WeightedHilbertMatrix
import AnalyticNumberTheory.AnalyticTools.HilbertMixedForm

/-!
# Hilbert's inequality with individual local spacings

The row estimates for the second and fourth powers bound the eigenvalues of the
weighted Hilbert matrix. The mixed-pole constant is kept explicit.
-/

open Finset Matrix Real Complex
namespace AnalyticNumberTheory.AnalyticTools

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem quadratic_remainder_le (x w : ι→ℝ) (hw : ∀i,0<w i) {B : ℝ}
    (hrow : ∀s, (∑r,w r^2/(x r-x s)^2)≤B/(w s)^2) (v : ι→ℂ) :
    ‖star v ⬝ᵥ (((hilbertSquareRemainder x w).map (fun z => (z:ℂ))) *ᵥ v)‖ ≤
      (fun i => ‖v i‖) ⬝ᵥ ((B • (1 : Matrix ι ι ℝ)+(hilbertMixedMatrix x w+(hilbertMixedMatrix x w)ᵀ)) *ᵥ (fun i => ‖v i‖)) := by
  have hentry s t : |hilbertSquareRemainder x w s t|≤
      (B • (1 : Matrix ι ι ℝ)+(hilbertMixedMatrix x w+(hilbertMixedMatrix x w)ᵀ)) s t := by
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.transpose_apply]
    rcases eq_or_ne s t with rfl|hst
    · simp only [hilbertSquareRemainder,ite_true,
        Matrix.one_apply_eq,mul_one,hilbertMixedMatrix,sub_self,zero_pow (by decide : 2≠0),div_zero,add_zero]
      rw [abs_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _)]
      calc
        _ = (w s)^2*∑r,w r^2/(x r-x s)^2 := by
          rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; rw [div_pow,mul_pow]; ring
        _ ≤ _ := by
          convert mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg (w s)) using 1
          field_simp [(hw s).ne']
    · simp only [hilbertSquareRemainder,hst,ite_false,Matrix.one_apply_ne hst,mul_zero,zero_add,
        hilbertMixedMatrix,←neg_sub (x s) (x t),neg_sq]
      have hws := hw s
      have hwt := hw t
      rw [abs_of_nonneg (by positivity)]; apply le_of_eq; ring
  unfold dotProduct Matrix.mulVec
  refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
  rw [norm_mul,Pi.star_apply,norm_star]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (sum_le_sum fun t _ => ?_)
  simp only [norm_mul,Matrix.map_apply,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hentry s t) (norm_nonneg _)

/-- The weighted Hilbert estimate in terms of bounds for the quadratic, quartic and
mixed-pole row sums. -/
theorem weightedHilbertMatrix_form_le (x w : ι→ℝ) (hx : Function.Injective x) (hw : ∀i,0<w i)
    {B C K : ℝ} (hC : 0≤C) (hrow : ∀s, (∑r,w r^2/(x r-x s)^2)≤B/(w s)^2)
    (hfour : ∀s, (∑r,w r^2/(x r-x s)^4)≤C/(w s)^6)
    (hmix : ∀s t,s≠t → (∑r,w r^2/((x r-x s)^2*(x r-x t)^2))≤
      K*(1/(w s)^2+1/(w t)^2)/(x s-x t)^2) (u : ι→ℂ) :
    ‖star u ⬝ᵥ (weightedHilbertMatrix x w *ᵥ u)‖≤
      Real.sqrt (B+2*(K+Real.sqrt (K^2+C)))*∑r,‖u r‖^2 := by
  let A := weightedHilbertMatrix x w
  have hA := weightedHilbertMatrix_isHermitian x w
  apply norm_hermitian_form_le_of_eigenvalues hA _ u
  intro j
  let v := ⇑(hA.eigenvectorBasis j)
  let f := fun i => ‖v i‖
  have hn : ∑i,‖v i‖^2=1 := by
    rw [←EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis j),hA.eigenvectorBasis.orthonormal.1 j,one_pow]
  have hn' : f ⬝ᵥ f=1 := by simpa only [f,dotProduct,sq] using hn
  have hnv : star v ⬝ᵥ v=1 := by
    rw [←Complex.ofReal_one,←hn,Complex.ofReal_sum]; refine sum_congr rfl fun i _ => ?_
    dsimp [Pi.star_apply]
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  have hv : A *ᵥ v=(hA.eigenvalues j:ℂ) • v := by
    simpa [A,v,RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis j
  have he := congrArg norm (weightedHilbert_eigen_remainder x w hx hv hnv)
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs] at he
  have hh := quadratic_remainder_le x w hw hrow v
  rw [he] at hh
  let T := hilbertMixedMatrix x w
  have hD := quadratic_form_le_of_gram_majorant T hC (hilbertMixedMatrix_gram_le x w hw hfour hmix)
    f (fun _ => norm_nonneg _) hn'
  change _ ≤ f ⬝ᵥ ((B • (1 : Matrix ι ι ℝ)+(T+Tᵀ)) *ᵥ f) at hh
  rw [add_mulVec,dotProduct_add,smul_mulVec,dotProduct_smul,one_mulVec,hn',add_mulVec,dotProduct_add,
    mulVec_transpose,dotProduct_comm f (f ᵥ* T),←dotProduct_mulVec] at hh
  simp only [smul_eq_mul,mul_one] at hh
  exact Real.abs_le_sqrt (by nlinarith)

/-- Passing from a mixed-pole estimate to the weighted Montgomery–Vaughan
inequality. Each term on the right carries its own local gap. -/
theorem weighted_hilbert_of_mixed_estimate (x δ : ι→ℝ) (hδ : ∀i,0<δ i)
    (hsep : ∀i j,i≠j → δ i≤|x i-x j|) {K : ℝ}
    (hmix : ∀s t,s≠t → (∑r,δ r/((x r-x s)^2*(x r-x t)^2))≤
      K*(1/δ s+1/δ t)/(x s-x t)^2) (u : ι→ℂ) :
    ‖∑s,∑t,star (u s)*u t/((x s-x t:ℝ):ℂ)‖≤
      Real.sqrt (π^2/3+2*(K+Real.sqrt (K^2+π^4/45)))*∑s,‖u s‖^2/δ s := by
  let w := fun s => Real.sqrt (δ s)
  have hw s : 0<w s := Real.sqrt_pos.mpr (hδ s)
  have hs s : w s^2=δ s := Real.sq_sqrt (hδ s).le
  have h6 s : w s^6=δ s^3 := by rw [show 6=2*3 by decide,pow_mul,hs]
  have hx : Function.Injective x := by
    intro i j he
    by_contra hij
    have := hsep i j hij
    simpa [he,not_le_of_gt (hδ i)] using this
  let v := fun s => u s/(w s:ℂ)
  have H := weightedHilbertMatrix_form_le x w hx hw (B:=π^2/3) (C:=π^4/45) (K:=K) (by positivity)
    (fun s => by simp_rw [hs,div_div];exact hilbert_quadratic_row x δ hδ hsep s)
    (fun s => by simp_rw [h6,hs,div_div];exact hilbert_quartic_row x δ hδ hsep s)
    (fun s t h => by simpa only [hs] using hmix s t h) v
  have heq : star v ⬝ᵥ (weightedHilbertMatrix x w *ᵥ v)=I*∑s,∑t,star (u s)*u t/((x s-x t:ℝ):ℂ) := by
    simp only [Matrix.mulVec,dotProduct]
    rw [mul_sum];refine sum_congr rfl fun s _ => ?_
    rw [mul_sum,mul_sum];refine sum_congr rfl fun t _ => ?_
    simp only [Pi.star_apply,v,weightedHilbertMatrix,Complex.star_def,map_div₀,conj_ofReal,ofReal_div,ofReal_mul]
    have hws : (w s : ℂ)≠0 := by exact_mod_cast (hw s).ne'
    have hwt : (w t : ℂ)≠0 := by exact_mod_cast (hw t).ne'
    simp only [div_eq_mul_inv]
    calc
      _ = I*(starRingEnd ℂ (u s))*u t*((x s-x t:ℝ):ℂ)⁻¹*
          ((w s:ℂ)⁻¹*w s)*((w t:ℂ)⁻¹*w t) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hws,inv_mul_cancel₀ hwt]; ring
  have hn : (∑r,‖v r‖^2)=∑r,‖u r‖^2/δ r := by
    refine sum_congr rfl fun r _ => ?_
    dsimp only [v]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (hw r).le,div_pow,hs]
  rwa [heq,norm_mul,norm_I,one_mul,hn] at H

/-- Montgomery and Vaughan's explicit real Hilbert constant from the mixed-pole bound four. -/
noncomputable def weightedHilbertConstant : ℝ :=
  Real.sqrt (π^2/3+2*(4+Real.sqrt (16+π^4/45)))

theorem weightedHilbertConstant_pos : 0<weightedHilbertConstant := by
  unfold weightedHilbertConstant; positivity

/-- A rational numerical upper bound for the weighted Hilbert constant. -/
theorem weightedHilbertConstant_lt : weightedHilbertConstant<4.452 := by
  have h2 := pow_lt_pow_left₀ Real.pi_lt_d4 Real.pi_pos.le (by decide : 2≠0)
  have h4 := pow_lt_pow_left₀ Real.pi_lt_d4 Real.pi_pos.le (by decide : 4≠0)
  have hinner : Real.sqrt (16+π^4/45)<4.263 := by
    apply (Real.sqrt_lt' (by norm_num)).mpr; nlinarith only [h4]
  unfold weightedHilbertConstant
  apply (Real.sqrt_lt' (by norm_num)).mpr
  nlinarith only [h2,hinner]

/-- The weighted Montgomery–Vaughan inequality on the real line, with constant
strictly less than 4.452 and a separate gap for every coefficient. -/
theorem weighted_hilbert_inequality (x δ : ι→ℝ) (hδ : ∀i,0<δ i)
    (hsep : ∀i j,i≠j → δ i≤|x i-x j|) (u : ι→ℂ) :
    ‖∑s,∑t,star (u s)*u t/((x s-x t:ℝ):ℂ)‖≤
      weightedHilbertConstant*∑s,‖u s‖^2/δ s := by
  simpa only [weightedHilbertConstant,show (4:ℝ)^2=16 by norm_num] using
    weighted_hilbert_of_mixed_estimate x δ hδ hsep (K:=4) (fun _ _ hs => hilbert_mixed_quadratic_row_sharp x δ hδ hsep hs) u

end AnalyticNumberTheory.AnalyticTools
