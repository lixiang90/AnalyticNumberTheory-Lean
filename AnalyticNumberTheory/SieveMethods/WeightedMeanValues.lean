import AnalyticNumberTheory.SieveMethods.SeparatedMeanValues
import AnalyticNumberTheory.AnalyticTools.WeightedHilbertInequality

/-!
# Mean values of Dirichlet polynomials with individual frequency spacings

Applying the weighted Hilbert inequality at the two endpoints gives an
error involving the first moment of the squared coefficients.
-/
noncomputable section
open Real Complex Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.SieveMethods

/-- Mean square of an exponential polynomial, with an individual spacing
for each frequency. -/
theorem weighted_frequency_mean_square {ι : Type*} (S : Finset ι) (x δ : ι→ℝ) (c : ι→ℂ)
    (hδ : ∀i∈S,0<δ i) (hsep : ∀ i∈S,∀j∈S,i≠j → δ i≤ |x i-x j|) (a b : ℝ) :
    |(∫ t in a..b, ‖∑i∈S,c i*Complex.exp (I*(x i:ℂ)*t)‖^2)-(b-a)*(∑i∈S,‖c i‖^2)|≤
      2*(weightedHilbertConstant*∑i∈S,‖c i‖^2/δ i) := by
  classical
  have hx : Set.InjOn x (S : Set ι) := by
    intro i hi j hj he
    by_contra hn
    have H := hsep i hi j hj hn
    rw [he,sub_self,abs_zero] at H
    exact (not_lt_of_ge H) (hδ i hi)
  apply frequency_mean_square_of_hilbert S x c hx
  intro u hu
  let f (i j : ι) := u i*star (u j)/((x i-x j:ℝ):ℂ)
  have hh := weighted_hilbert_inequality (fun i : ↥S => x i.val) (fun i : ↥S => δ i.val)
    (fun i => hδ i i.prop) (fun i j h => hsep i i.prop j j.prop (fun he => h (Subtype.ext he)))
    (fun i => star (u i.val))
  have hsum : (∑i : ↥S,∑j : ↥S,f i.val j.val)=∑i∈S,∑j∈S,f i j := by
    calc _ = ∑ i : ↥S, ∑j∈S,f i.val j := sum_congr rfl fun i _ => sum_coe_sort S (f i.val)
         _ = _ := sum_coe_sort S (fun i => ∑j∈S,f i j)
  simp only [star_star,norm_star] at hh
  change ‖∑i : ↥S,∑j : ↥S,f i.val j.val‖≤_ at hh
  rw [hsum,sum_coe_sort S (fun i => ‖u i‖^2/δ i)] at hh
  rw [sum_congr rfl (fun i hi => congrArg (fun v : ℝ => v^2/δ i) (hu i hi))] at hh
  convert hh using 2
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases he : i=j
  · subst j;simp [f]
  · simp [he,f]

private theorem log_nat_step {m n : ℕ} (hm : 1≤m) (hmn : m<n) :
    (2*(m:ℝ))⁻¹≤Real.log n-Real.log m := by
  have hp : 0<(m:ℝ) := Nat.cast_pos.mpr hm
  have hq : 0<(m:ℝ)+1 := by positivity
  have hmn' : (m:ℝ)+1≤n := by exact_mod_cast hmn
  have hl := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div hp.ne' hq.ne'] at hl
  have hm' : (1:ℝ)≤m := by exact_mod_cast hm
  calc (2*(m:ℝ))⁻¹ ≤ ((m:ℝ)+1)⁻¹ := inv_anti₀ hq (by linarith)
       _ = 1-m/((m:ℝ)+1) := by field_simp;ring
       _ ≤ Real.log ((m:ℝ)+1)-Real.log m := by linarith
       _ ≤ _ := by linarith [Real.log_le_log hq hmn']

/-- The weighted Montgomery–Vaughan mean-value theorem for Dirichlet
polynomials on any vertical line and any finite interval. -/
theorem weighted_dirichletPoly_mean_square (a : ℕ→ℂ) (N : ℕ) (σ A B : ℝ) :
    |(∫ t in A..B,‖dirichletPoly a N ((σ:ℂ)+(t:ℂ)*I)‖^2)-
      (B-A)*(∑n∈Icc 1 N,‖a n‖^2*(n:ℝ)^(-2*σ))|≤
      4*weightedHilbertConstant*(∑n∈Icc 1 N,(n:ℝ)*‖a n‖^2*(n:ℝ)^(-2*σ)) := by
  let S := Icc 1 N
  let x := fun n : ℕ => -Real.log n
  let c := fun n : ℕ => a n*(((n:ℝ)^(-σ):ℝ):ℂ)
  let δ := fun n : ℕ => (2*(n:ℝ))⁻¹
  have hd (n : ℕ) (hn : n∈S) : 0<δ n := by
    have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
    dsimp [δ];positivity
  have hsep (m : ℕ) (hm : m∈S) (n : ℕ) (hn : n∈S) (hne : m≠n) : δ m≤ |x m-x n| := by
    dsimp only [δ,x];rw [neg_sub_neg]
    rcases lt_or_gt_of_ne hne with h|h
    · exact (log_nat_step (mem_Icc.mp hm).1 h).trans (le_abs_self _)
    · rw [abs_sub_comm]
      have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
      have hnm : (n:ℝ)≤m := by exact_mod_cast h.le
      exact (inv_anti₀ (show 0<2*(n:ℝ) by positivity) (by linarith : 2*(n:ℝ)≤2*m)).trans
        ((log_nat_step (mem_Icc.mp hn).1 h).trans (le_abs_self _))
  have hn (n : ℕ) : ‖c n‖^2=‖a n‖^2*(n:ℝ)^(-2*σ) := by
    dsimp only [c];rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ←Real.rpow_natCast ((n:ℝ)^(-σ)) 2,←Real.rpow_mul (Nat.cast_nonneg _)];congr 2;push_cast;ring
  have hv (t : ℝ) : dirichletPoly a N ((σ:ℂ)+(t:ℂ)*I)=∑n∈S,c n*Complex.exp (I*(x n:ℂ)*t) := by
    apply sum_congr rfl
    intro n hn'
    have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn').1
    dsimp only [x,c]
    rw [mul_assoc]
    congr 1
    rw [←Complex.ofReal_natCast,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),←Complex.ofReal_log hp.le,
      Real.rpow_def_of_pos hp,Complex.ofReal_exp,←Complex.exp_add]
    congr 1;push_cast;ring
  have H := weighted_frequency_mean_square S x δ c hd hsep A B
  simp only [←hv,hn] at H
  have hδsum : (∑n∈S,‖a n‖^2*(n:ℝ)^(-2*σ)/δ n)=2*(∑n∈S,(n:ℝ)*‖a n‖^2*(n:ℝ)^(-2*σ)) := by
    rw [mul_sum];apply sum_congr rfl
    intro n _;dsimp [δ];rw [div_inv_eq_mul];ring
  rw [hδsum] at H
  exact H.trans_eq (by ring)

end AnalyticNumberTheory.SieveMethods
