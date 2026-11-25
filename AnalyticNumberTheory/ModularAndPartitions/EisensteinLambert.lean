import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The Lambert series at complex weight

Absolute locally uniform convergence gives separate holomorphy in the
nome and in the weight. At integral weight the coefficients are divisor sums.
-/

open Complex Real Filter Set
open scoped Topology
namespace AnalyticNumberTheory.ModularAndPartitions

private noncomputable def lambertTerm (q s : ℂ) (p : ℕ+×ℕ+) : ℂ :=
  ((p.2:ℕ):ℂ)^(s-1)*q^(p.1*p.2:ℕ)

/-- The two-variable Lambert series `∑ m,n≥1 n^(s−1) q^(mn)`. -/
noncomputable def eisensteinLambert (q s : ℂ) : ℂ := ∑' p : ℕ+×ℕ+,lambertTerm q s p

private theorem norm_lambertTerm_le {q s : ℂ} {r : ℝ} {k : ℕ}
    (hq : ‖q‖≤r) (hs : s.re-1≤k) (p : ℕ+×ℕ+) :
    ‖lambertTerm q s p‖≤((p.2:ℕ):ℝ)^k*r^(p.1*p.2:ℕ) := by
  have hn' : 0<((p.2:ℕ):ℝ) := by exact_mod_cast p.2.2
  have hn : 1≤((p.2:ℕ):ℝ) := by exact_mod_cast p.2.2
  rw [lambertTerm,norm_mul,norm_pow,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hn',
    Complex.sub_re,Complex.one_re,←Real.rpow_natCast ((p.2:ℕ):ℝ) k]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn hs)
    (pow_le_pow_left₀ (norm_nonneg q) hq _) (pow_nonneg (norm_nonneg _) _) (by positivity)

private theorem summable_lambert_majorant (k : ℕ) {r : ℝ} (hr : 0≤r) (hr' : r<1) :
    Summable fun p : ℕ+×ℕ+ => ((p.2:ℕ):ℝ)^k*r^(p.1*p.2:ℕ) := by
  exact summable_prod_mul_pow k (by simpa only [Real.norm_of_nonneg hr] using hr')

theorem summable_eisensteinLambert {q : ℂ} (hq : ‖q‖<1) (s : ℂ) :
    Summable (lambertTerm q s) := by
  apply Summable.of_norm_bounded (summable_lambert_majorant ⌈s.re-1⌉₊ (norm_nonneg q) hq)
  exact norm_lambertTerm_le le_rfl (Nat.le_ceil _)

/-- The Lambert series is entire in the complex weight. -/
theorem differentiable_eisensteinLambert_weight {q : ℂ} (hq : ‖q‖<1) :
    Differentiable ℂ (eisensteinLambert q) := by
  intro s
  let U := {w : ℂ | w.re<s.re+1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hs : s∈U := by dsimp [U]; linarith
  apply DifferentiableWithinAt.differentiableAt _ (hU.mem_nhds hs)
  apply Complex.differentiableOn_tsum_of_summable_norm
    (summable_lambert_majorant ⌈s.re⌉₊ (norm_nonneg q) hq) _ hU _ s hs
  · intro p w _
    have hn : ((p.2:ℕ):ℂ)≠0 := Nat.cast_ne_zero.mpr p.2.2.ne'
    apply DifferentiableAt.differentiableWithinAt
    unfold lambertTerm
    fun_prop (disch := exact hn)
  · intro p w hw; apply norm_lambertTerm_le le_rfl
    change w.re<s.re+1 at hw
    linarith only [hw,Nat.le_ceil s.re]

/-- The nome variable is holomorphic on the open unit disk. -/
theorem differentiableOn_eisensteinLambert_nome (s : ℂ) :
    DifferentiableOn ℂ (fun q => eisensteinLambert q s) {q | ‖q‖<1} := by
  intro q hq
  let r := (1+‖q‖)/2
  have hq' : ‖q‖<1 := hq
  have hr : 0≤r := by dsimp [r]; positivity
  have hr' : r<1 := by dsimp [r]; linarith
  let U := {w : ℂ | ‖w‖<r}
  have hU : IsOpen U := isOpen_lt continuous_norm continuous_const
  have hqu : q∈U := by dsimp [U,r]; linarith
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableWithinAt.differentiableAt _ (hU.mem_nhds hqu)
  apply Complex.differentiableOn_tsum_of_summable_norm
    (summable_lambert_majorant ⌈s.re-1⌉₊ hr hr') _ hU _ q hqu
  · intro p w _; unfold lambertTerm; fun_prop
  · intro p w hw; exact norm_lambertTerm_le (le_of_lt hw) (Nat.le_ceil _) p

/-- Iterating the absolutely convergent double sum by its first index. -/
theorem eisensteinLambert_eq_iterated {q : ℂ} (hq : ‖q‖<1) (s : ℂ) :
    eisensteinLambert q s=∑' m : ℕ+,∑' n : ℕ+,((n:ℕ):ℂ)^(s-1)*q^(m*n:ℕ) :=
  (summable_eisensteinLambert hq s).tsum_prod

/-- At a positive integer weight the Lambert coefficients are divisor powers. -/
theorem eisensteinLambert_nat_succ {q : ℂ} (hq : ‖q‖<1) (k : ℕ) :
    eisensteinLambert q (k+1)=∑' n : ℕ+,(ArithmeticFunction.sigma k (n:ℕ):ℂ)*q^(n:ℕ) := by
  rw [eisensteinLambert_eq_iterated hq]
  simp only [add_sub_cancel_right,Complex.cpow_natCast]
  exact tsum_prod_pow_eq_tsum_sigma k hq

end AnalyticNumberTheory.ModularAndPartitions
