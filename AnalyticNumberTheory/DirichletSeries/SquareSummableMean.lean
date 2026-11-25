import AnalyticNumberTheory.AnalyticTools.ConvergentDiagonal
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials

/-!
# Mean squares of Dirichlet polynomials with square-summable coefficients

At a fixed real part, square summability gives a finite limiting diagonal
for polynomials truncated at a height-dependent length comparable to the height.
-/

open Real Complex Finset Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.DirichletSeries

/-- A finite Dirichlet polynomial is continuous on each vertical line. -/
theorem continuous_vertical_dirichletPoly (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    Continuous (fun t : ℝ => dirichletPoly a N ((σ:ℂ)+t*I)) := by
  unfold dirichletPoly
  apply continuous_finsetSum
  intro n hn
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hn).1; omega)
  simp only [Complex.cpow_def_of_ne_zero hn']
  fun_prop

private theorem sum_tail {E : Type*} [AddCommGroup E] (f : ℕ → E) {m n : ℕ} (hmn : m≤n) :
    (∑ j ∈ Icc 1 n, f j)-(∑ j ∈ Icc 1 m, f j) = ∑ j ∈ Icc 1 n, if m<j then f j else 0 := by
  classical
  have he : (Icc 1 n).filter (fun j => j≤m) = Icc 1 m := by
    ext j; simp only [mem_filter,mem_Icc]; omega
  have h := sum_filter_add_sum_filter_not (Icc 1 n) (fun j => j≤m) f
  rw [he] at h
  simp only [not_le] at h
  rw [←sum_filter,sub_eq_iff_eq_add,add_comm]; exact h.symm

/-- A Dirichlet polynomial of linearly growing length tends in normalized
square mean to the infinite diagonal. The coefficient at index zero is unused. -/
theorem tendsto_dirichletPoly_squareMean (a : ℕ → ℂ) (σ : ℝ) (N : ℝ → ℕ)
    {L : ℝ} (hL : 0≤L)
    (hsize : ∀ᶠ T : ℝ in atTop, ⌊T⌋₊+1≤N T ∧ (N T:ℝ)≤L*T)
    (hs : Summable (fun n : ℕ => ‖a (n+1)‖^2*((n+1:ℕ):ℝ)^(-2*σ))) :
    Tendsto (fun T : ℝ => intervalSquareMean 1 T T
      (fun t : ℝ => dirichletPoly a (N T) ((σ:ℂ)+t*I))) atTop
      (𝓝 (∑' n : ℕ, ‖a (n+1)‖^2*((n+1:ℕ):ℝ)^(-2*σ))) := by
  let D (n : ℕ) := ∑ j ∈ Icc 1 n, ‖a j‖^2*(j:ℝ)^(-2*σ)
  have hd : Tendsto D atTop (𝓝 (∑' n : ℕ, ‖a (n+1)‖^2*((n+1:ℕ):ℝ)^(-2*σ))) := by
    apply hs.hasSum.tendsto_sum_nat.congr
    intro n
    dsimp [D]
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih]
  apply tendsto_squareMean_of_convergent_diagonal (fun n t => dirichletPoly a n ((σ:ℂ)+t*I))
    D (K:=2*π) (L:=L) N (fun n => continuous_vertical_dirichletPoly a n σ) hd (by positivity) hL hsize
  · intro n _ T ht
    exact dirichletPoly_mean_sq_asymp a n σ ht
  · intro m n hmn T ht
    let b (j : ℕ) := if m<j then a j else 0
    have hp (t : ℝ) : ‖dirichletPoly a m ((σ:ℂ)+t*I)-dirichletPoly a n ((σ:ℂ)+t*I)‖ =
        ‖dirichletPoly b n ((σ:ℂ)+t*I)‖ := by
      rw [norm_sub_rev]
      apply congrArg norm
      unfold dirichletPoly
      simpa [b,ite_mul] using sum_tail (fun j => a j*(j:ℂ)^(-((σ:ℂ)+t*I))) hmn
    have he : D n-D m = ∑ j ∈ Icc 1 n, ‖b j‖^2*(j:ℝ)^(-2*σ) := by
      apply (sum_tail _ hmn).trans
      apply sum_congr rfl
      intro j _
      by_cases h : m<j <;> simp [b,h]
    simp only [Pi.sub_apply,hp]
    rw [he]
    have H := (abs_le.mp (dirichletPoly_mean_sq_asymp b n σ ht)).2
    have hpos : 0≤∑ j ∈ Icc 1 n, ‖b j‖^2*(j:ℝ)^(-2*σ) := sum_nonneg fun _ _ => by positivity
    linarith only [H,hpos]
  · intro m n hmn
    apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmn)
    exact fun j _ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)

end AnalyticNumberTheory.DirichletSeries
