import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik
import AnalyticNumberTheory.AnalyticTools.ReducedRootSum

/-! # Totient weights after regrouping by the conductor cofactor -/
noncomputable section
open Real Finset
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.PrimeDistribution

/-- Reorder the lifts of a primitive character by the cofactor between its
conductor and its modulus. The conductor cutoff stays inside the cofactor sum. -/
theorem totient_conductor_cofactor_bound (N : ℕ) (F : ℕ→ℝ) (hF : ∀d,0≤F d) :
    (∑q∈Icc 1 N,(q.totient:ℝ)⁻¹*∑d∈q.divisors with 2≤d,F d)≤
      ∑k∈Icc 1 N,(k.totient:ℝ)⁻¹*∑d∈Icc 2 (N/k),(d.totient:ℝ)⁻¹*F d := by
  let G (k d : ℕ) := if 2≤d then ((k*d).totient:ℝ)⁻¹*F d else 0
  have hrow (q:ℕ) : (q.totient:ℝ)⁻¹*∑d∈q.divisors with 2≤d,F d =
      ∑k∈q.divisors,G k (q/k) := by
    rw [sum_filter,mul_sum]
    trans ∑k∈q.divisors,(q.totient:ℝ)⁻¹*(if 2≤q/k then F (q/k) else 0)
    · exact (Nat.sum_div_divisors q (fun d => (q.totient:ℝ)⁻¹*(if 2≤d then F d else 0))).symm
    apply sum_congr rfl;intro k hk
    simp [G,Nat.mul_div_cancel' (Nat.mem_divisors.mp hk).1,mul_ite]
  simp_rw [hrow]
  rw [sum_Icc_divisors_swap N G]
  apply sum_le_sum;intro k hk
  have hsel : (Icc 1 (N/k)).filter (fun d => 2≤d)=Icc 2 (N/k) := by ext d;simp;omega
  simp only [G,←sum_filter,hsel,mul_sum]
  apply sum_le_sum;intro d hd
  have hk₀ := Nat.totient_pos.mpr (mem_Icc.mp hk).1
  have hd₀ := Nat.totient_pos.mpr (show 0<d by have := (mem_Icc.mp hd).1;omega)
  have hφ : (k.totient:ℝ)*d.totient≤(k*d).totient := by exact_mod_cast Nat.totient_super_multiplicative k d
  have hv := inv_anti₀ (mul_pos (Nat.cast_pos.mpr hk₀) (Nat.cast_pos.mpr hd₀)) hφ
  rw [mul_inv_rev] at hv
  exact (mul_le_mul_of_nonneg_right hv (hF d)).trans_eq (by ring)

/-- Removing a second factor k makes the sum of reciprocal totients
bounded independently of the cutoff. -/
theorem sum_inv_mul_inv_totient_bounded :
    ∃ C : ℝ,0<C ∧ ∀N : ℕ,(∑k∈Icc 1 N,(k.totient:ℝ)⁻¹*(k:ℝ)⁻¹)≤C := by
  let a (k:ℕ) := (k:ℝ)^(-(3/2:ℝ))
  have ha : Summable a := Real.summable_nat_rpow.mpr (by norm_num)
  have hnn (k:ℕ) : 0≤a k := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hZ : 0≤∑'k,a k := tsum_nonneg hnn
  refine ⟨20*(1+∑'k,a k),by linarith only [hZ],?_⟩
  intro N
  have hterm (k) (hk:k∈Icc 1 N) : (k.totient:ℝ)⁻¹*(k:ℝ)⁻¹≤20*a k := by
    have hk₀ : 0<k := (mem_Icc.mp hk).1
    have hk' : 0<(k:ℝ) := Nat.cast_pos.mpr hk₀
    let w (j:ℕ) : ℝ := if j.Coprime k then sqrt ((k:ℝ)/j) else 0
    have h0 (j) : 0≤w j := by dsimp only [w];split <;> positivity
    have hs := (single_le_sum (f:=w) (fun j _ => h0 j) (mem_Icc.mpr ⟨le_rfl,hk₀⟩)).trans (reduced_sqrt_ratio_sum_le hk₀)
    change w 1≤_ at hs
    simp [w] at hs
    have hφ := Nat.cast_pos (α:=ℝ).mpr (Nat.totient_pos.mpr hk₀)
    have hv : (k.totient:ℝ)⁻¹≤20*(k:ℝ)^(-(1/2:ℝ)) := by
      rw [Real.rpow_neg hk'.le,←Real.sqrt_eq_rpow,←div_eq_mul_inv,←one_div,div_le_div_iff₀ hφ (Real.sqrt_pos.mpr hk')];linarith only [hs]
    have he : a k=(k:ℝ)^(-(1/2:ℝ))*(k:ℝ)⁻¹ := by
      dsimp only [a];rw [←Real.rpow_neg_one,←Real.rpow_add hk'];congr 1;ring
    rw [he]
    exact (mul_le_mul_of_nonneg_right hv (inv_nonneg.mpr hk'.le)).trans_eq (by ring)
  have hh := sum_le_sum (s:=Icc 1 N) hterm
  rw [←mul_sum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left ((ha.sum_le_tsum _ (fun k _ => hnn k)).trans (by linarith)) (by norm_num))

end AnalyticNumberTheory.PrimeDistribution
