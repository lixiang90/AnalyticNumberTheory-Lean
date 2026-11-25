import AnalyticNumberTheory.ModularAndPartitions.RademacherSeries

/-!
# Uniform truncation of the Rademacher series

The individual terms at denominator `k` decay as `k^(-3/2)`, with an
exponential factor `exp(π√(2n/3)/k)`. Summing beyond `N` gives an error
uniform in both the partition number and the truncation index.
-/

open Real Finset Filter
open scoped Topology
namespace AnalyticNumberTheory.ModularAndPartitions

private theorem rpow_neg_three_halves_step {k : ℕ} (hk : 0<k) :
    ((k+1:ℕ):ℝ)^(-(3/2:ℝ)) ≤ 2*((√(k:ℝ))⁻¹-(√((k+1:ℕ):ℝ))⁻¹) := by
  let x := √(k:ℝ)
  let y := √((k+1:ℕ):ℝ)
  have hx : 0<x := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hy : 0<y := Real.sqrt_pos.mpr (by positivity)
  have hxy : x≤y := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
  have H : y^2-x^2=1 := by dsimp [x,y]; rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]; push_cast; ring
  have hex : ((k+1:ℕ):ℝ)^(-(3/2:ℝ))=(y^3)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    congr 1
    dsimp [y]; rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (by positivity)]
    congr 1; norm_num
  rw [hex]
  change _≤2*(x⁻¹-y⁻¹)
  have hd : y-x=1/(x+y) := (eq_div_iff (add_pos hx hy).ne').mpr (by nlinarith only [H])
  rw [show x⁻¹-y⁻¹=(y-x)/(x*y) by field_simp,hd]
  rw [inv_eq_one_div]
  have hpos := mul_pos hx hy
  field_simp [hx.ne',hy.ne',(add_pos hx hy).ne']
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0≤y*(2*y+x) by positivity)]

/-- The Rademacher truncation error, uniform in both `n` and `N`, with
an explicit constant and its exponential dependence on `√n/N`. -/
theorem partitionCount_sub_rademacherPartialSum_uniform {n N : ℕ} (hn : 1≤n) (hN : 1≤N) :
    let c := π*√(2/3)
    ‖(partitionCount n:ℂ)-∑ k ∈ Icc 1 N, (√(k:ℝ):ℂ)*
      rademacherKloostermanSum dedekindSum k n*(rademacherPsi k n:ℂ)‖ ≤
      (c^3/(3*π*√2))*Real.exp (c*√(n:ℝ)/(N:ℝ))/√(N:ℝ) := by
  intro c
  let F (k : ℕ) := (√(k:ℝ):ℂ)*rademacherKloostermanSum dedekindSum k n*(rademacherPsi k n:ℂ)
  let A := c^3/(6*π*√2)*Real.exp (c*√(n:ℝ)/(N:ℝ))
  let P (m : ℕ) := ∑ j ∈ range m,F (j+1)
  have hC : 0<c := by dsimp [c]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hstep (m : ℕ) (hm : N≤m) :
      ‖F (m+1)‖≤2*A*((√(m:ℝ))⁻¹-(√((m+1:ℕ):ℝ))⁻¹) := by
    let k : ℕ+ := ⟨m+1,by omega⟩
    have H := norm_rademacherTerm_le dedekindSum hn k
    change ‖F (m+1)‖≤(c^3/(6*π*√2))*Real.exp (c*√(n:ℝ)/((m+1:ℕ):ℝ))*((m+1:ℕ):ℝ)^(-(3/2:ℝ)) at H
    apply H.trans
    have h₁ : Real.exp (c*√(n:ℝ)/((m+1:ℕ):ℝ))≤Real.exp (c*√(n:ℝ)/(N:ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hN)
      exact_mod_cast (show N≤m+1 by omega)
    have h₂ := rpow_neg_three_halves_step (k:=m) (by omega)
    calc _ ≤ A*((m+1:ℕ):ℝ)^(-(3/2:ℝ)) := by dsimp [A]; gcongr
         _ ≤ A*(2*((√(m:ℝ))⁻¹-(√((m+1:ℕ):ℝ))⁻¹)) := mul_le_mul_of_nonneg_left h₂ hA
         _ = _ := by ring
  have hbound (M : ℕ) (hm : N≤M) :
      ‖P M-P N‖≤2*A*((√(N:ℝ))⁻¹-(√(M:ℝ))⁻¹) := by
    induction M,hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have he : P (m+1)-P N=(P m-P N)+F (m+1) := by dsimp [P]; rw [sum_range_succ]; ring
      rw [he]; apply (norm_add_le ..).trans
      exact (add_le_add ih (hstep m hm)).trans_eq (by ring)
  have hlim : Tendsto P atTop (𝓝 (partitionCount n:ℂ)) :=
    ((hasSum_pnat_iff_hasSum_succ (f:=F)).mp (rademacherSeriesFormula n hn)).tendsto_sum_nat
  have he (m : ℕ) : P m=∑ k ∈ Icc 1 m,F k := by
    induction m with
    | zero => simp [P]
    | succ m ih => change (∑ j ∈ range (m+1), F (j+1))=_
                   rw [sum_range_succ,sum_Icc_succ_top (by omega),←ih]
  have H : ‖(partitionCount n:ℂ)-P N‖≤2*A*(√(N:ℝ))⁻¹ := by
    apply le_of_tendsto ((hlim.sub_const (P N)).norm)
    filter_upwards [eventually_ge_atTop N] with M hM
    apply (hbound M hM).trans
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
  rw [he] at H
  apply H.trans_eq
  dsimp [A]; ring

/-- The classical uniform remainder `O(N^(-1/2) exp(2π n/N²))` in the
finite expansion for the partition number. -/
theorem exists_rademacher_uniform_error_constant :
    ∃ C : ℝ, 0<C ∧ ∀ {n N : ℕ}, 1≤n → 1≤N →
      ‖(partitionCount n:ℂ)-∑ k ∈ Icc 1 N, (√(k:ℝ):ℂ)*
        rademacherKloostermanSum dedekindSum k n*(rademacherPsi k n:ℂ)‖ ≤
        C*Real.exp (2*π*(n:ℝ)/(N:ℝ)^2)/√(N:ℝ) := by
  let c : ℝ := π*√(2/3)
  let d := c^2/(8*π)
  refine ⟨(c^3/(3*π*√2))*Real.exp d, by dsimp [c,d]; positivity,?_⟩
  intro n N hn hN
  have H := partitionCount_sub_rademacherPartialSum_uniform hn hN
  apply H.trans
  have hS : c*√(n:ℝ)/(N:ℝ)≤d+2*π*(n:ℝ)/(N:ℝ)^2 := by
    have Hx (x : ℝ) : c*x≤d+2*π*x^2 := by
      dsimp [d]; have hp := Real.pi_pos
      field_simp [hp.ne']; nlinarith [sq_nonneg (4*π*x-c)]
    have h := Hx (√(n:ℝ)/(N:ℝ))
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg n)] at h
    convert h using 1 <;> ring
  have he := Real.exp_le_exp.mpr hS
  rw [Real.exp_add] at he
  change (c^3/(3*π*√2))*Real.exp (c*√(n:ℝ)/(N:ℝ))/√(N:ℝ) ≤ _
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc _ ≤ (c^3/(3*π*√2))*(Real.exp d*Real.exp (2*π*(n:ℝ)/(N:ℝ)^2)) :=
             mul_le_mul_of_nonneg_left he (by dsimp [c]; positivity)
       _ = _ := by ring

end AnalyticNumberTheory.ModularAndPartitions
