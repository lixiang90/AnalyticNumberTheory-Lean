import AnalyticNumberTheory.PrimeDistribution.MaximalProgressionReduction
import AnalyticNumberTheory.PrimeDistribution.BarbanConductorWeights

/-! # The zero-density proof with maximal endpoints in progressions -/
noncomputable section
open Finset
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- A maximal prime number theorem and a maximal primitive-character mean
bound the progression discrepancy, with a single logarithmic loss from
the multiples of each conductor. -/
theorem maximal_progression_mean_of_primitive :
    ∃ C : ℝ, 0<C ∧ ∀ {x Q E P : ℝ}, 4≤x → 1≤Q → Q≤x →
      (∀y,0≤y → y≤x → |Chebyshev.psi y-y|≤E) →
      (∑d∈Icc 2 ⌊Q⌋₊,(d.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ d with χ.IsPrimitive,maximalPsiCharNorm x χ)≤P →
      (∑q∈Icc 1 ⌊Q⌋₊,maximalPsiAPError x q) ≤
        C*(E+P)*Real.log x+Q*(Real.log x)^2/Real.log 2 := by
  obtain ⟨C,hC,HC⟩ := sum_inv_totient_le_mul_log
  refine ⟨2*C,by positivity,?_⟩
  intro x Q E P hx hQ hQx hE hP
  let N := ⌊Q⌋₊
  let f (d : ℕ) := ∑χ : DirichletCharacter ℂ d with χ.IsPrimitive,maximalPsiCharNorm x χ
  have hx₀ : 0≤x := by linarith
  have hQ₀ : 0≤Q := by linarith
  have hf (d : ℕ) : 0≤f d := sum_nonneg (fun χ _ => (norm_nonneg _).trans (norm_psiChar_le_maximalPsiCharNorm χ hx₀ le_rfl))
  have hmesh := sum_le_sum (s:=Icc 1 N) (fun q hq => maximalPsiAPError_le_primitive_conductors (mem_Icc.mp hq).1 (by linarith : 1≤x) hE)
  simp only [sum_add_distrib,←sum_mul] at hmesh
  have hN : (N:ℝ)≤Q := Nat.floor_le hQ₀
  have hlog : 0≤Real.log x := Real.log_nonneg (by linarith)
  have hlog₂ : 0<Real.log 2 := Real.log_pos one_lt_two
  have hφ : (∑q∈Icc 1 N,(q.totient:ℝ)⁻¹)≤2*C*Real.log x := by
    have hh := Real.log_le_log (by positivity : 0<(N:ℝ)+2) (show (N:ℝ)+2≤x^2 by nlinarith)
    rw [Real.log_pow] at hh
    push_cast at hh
    apply (HC N).trans
    nlinarith only [mul_le_mul_of_nonneg_left hh hC.le]
  have hs := totient_conductor_cofactor_bound N f hf
  have hbound : (∑q∈Icc 1 N,(q.totient:ℝ)⁻¹*∑ d∈q.divisors with 2≤d,f d) ≤(2*C*Real.log x)*P := by
    apply hs.trans
    calc _ ≤ ∑k∈Icc 1 N,(k.totient:ℝ)⁻¹*P := by
           apply sum_le_sum;intro k hk
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           apply le_trans _ hP
           exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self N k)) (fun d _ _=>mul_nonneg (by positivity) (hf d))
         _ ≤ _ := by
           rw [←sum_mul];apply mul_le_mul_of_nonneg_right hφ
           exact (sum_nonneg (s:=Icc 2 N) (fun d _=>mul_nonneg (by positivity) (hf d))).trans hP
  have hmods : (∑q∈Icc 1 N,Real.log (q:ℝ)/Real.log 2)*Real.log x≤Q*(Real.log x)^2/Real.log 2 := by
    have hu (q : ℕ) (hq : q∈Icc 1 N) := Real.log_le_log (by exact_mod_cast (mem_Icc.mp hq).1 : 0<(q:ℝ))
      (((Nat.cast_le.mpr (mem_Icc.mp hq).2).trans hN).trans hQx)
    have hm := sum_le_sum (fun q hq=>div_le_div_of_nonneg_right (hu q hq) hlog₂.le)
    simp only [sum_const,nsmul_eq_mul,Nat.card_Icc] at hm
    have he : N+1-1=N := by omega
    rw [he] at hm
    apply (mul_le_mul_of_nonneg_right (hm.trans (mul_le_mul_of_nonneg_right hN (div_nonneg hlog hlog₂.le))) hlog).trans_eq
    ring
  apply hmesh.trans
  have hE₀ := (abs_nonneg _).trans (hE x hx₀ le_rfl)
  linarith only [mul_le_mul_of_nonneg_right hφ hE₀,hbound,hmods]

/-- For each modulus both the residue and its endpoint may be chosen
independently. The zero-density method gives the explicit upper cutoff
exponent k+12 for a saving of k powers of the logarithm. -/
theorem bombieriVinogradov_maximal_of_density_explicit (H : PrimitivePsiExplicitBound) (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},4≤x → 1≤Q →
      Q≤Real.sqrt x/(Real.log x)^(k+12) →
      (∑q∈Icc 1 ⌊Q⌋₊,maximalPsiAPError x q)≤C*x/(Real.log x)^k := by
  obtain ⟨R,hR,HR⟩ := maximal_progression_mean_of_primitive
  obtain ⟨E,hE,HE⟩ := abs_psi_sub_id_maximal_le_log_power (k+1)
  obtain ⟨P,hP,HP⟩ := primitive_density_maximal_log_saving H ((k+1:ℕ):ℝ)
  have h₂ : 0<Real.log 2 := Real.log_pos one_lt_two
  refine ⟨R*(E+P)+1/Real.log 2,by positivity,?_⟩
  intro x Q hx hQ hcut
  let L := Real.log x
  have hL : 1≤L := (Real.le_log_iff_exp_le (by linarith : 0<x)).mpr (by linarith [Real.exp_one_lt_three])
  have hL₀ : 0<L := by linarith
  have hx₀ : 0≤x := by linarith
  have hQx : Q≤x := hcut.trans ((div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL)).trans (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))))
  have hm := HR hx hQ hQx (fun y hy hyx=>HE hx hy hyx) (P:=P*x/L^(k+1)) (by
    have hp := HP (by linarith : 2≤x) hL hQ (by simpa only [Nat.ceil_natCast,Real.sqrt_eq_rpow,Nat.add_assoc,Nat.reduceAdd] using hcut)
    simpa only [Real.rpow_natCast] using hp)
  have hlevel : Q≤x/L^(k+2) := by
    have hu : L^(k+2)≤L^(k+12) := pow_le_pow_right₀ hL (by omega)
    exact hcut.trans (div_le_div₀ hx₀ (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))) (pow_pos hL₀ _) hu)
  have herr : Q*L^2/Real.log 2≤(x/L^k)/Real.log 2 := by
    apply div_le_div_of_nonneg_right _ h₂.le
    apply (mul_le_mul_of_nonneg_right hlevel (sq_nonneg _)).trans_eq
    rw [pow_add];field_simp
  apply hm.trans
  change R*(E*x/L^(k+1)+P*x/L^(k+1))*L+Q*L^2/Real.log 2≤_
  apply (add_le_add (le_refl _) herr).trans_eq
  change _=(R*(E+P)+1/Real.log 2)*x/L^k
  rw [pow_succ];field_simp <;> ring

end AnalyticNumberTheory.PrimeDistribution
