import AnalyticNumberTheory.PrimeDistribution.PrimitiveZeroHeightWeights
import AnalyticNumberTheory.AdditiveNumberTheory.PageExceptionalWeights

/-! # Averaging on a dyadic block of primitive conductors

The common part of a character-wise error costs at most one copy per
modulus. The remaining zero weights are summed over the entire primitive
family, at a cost of order log Q / Q from the inverse totients.
-/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- The total order-weighted zero sum of one character. -/
def characterZeroWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) (w : ℂ→ℝ) : ℝ :=
  ∑z∈characterStripZeros χ T,(characterZeroMultiplicity χ z:ℝ)*w z

/-- A character-wise majorant may be summed on every subinterval (Q,R] of
(Q,2Q], keeping only the prime-to-modulus proportion in the common error. -/
theorem primitive_conductor_block_sum {Q R : ℕ} (hQ : 1≤Q) (hR : R≤2*Q)
    {U V T : ℝ} (hU : 0≤U) (hV : 0≤V) (w : ℂ→ℝ) (hw : ∀z,0≤w z)
    (f : (q : ℕ)→DirichletCharacter ℂ q→ℝ)
    (hf : ∀q∈Ioc Q R,∀χ : DirichletCharacter ℂ q,χ.IsPrimitive →
      f q χ≤U+V*characterZeroWeight χ T w) :
    (∑q∈Ioc Q R,(q.totient:ℝ)⁻¹*
       ∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,f q χ) ≤
      Q*U + (6*(1+Real.log (2*(Q:ℝ)))/Q)*V*primitiveFamilyZeroWeight (2*Q) T w := by
  let F (q : ℕ) := univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  let Z (q : ℕ) := ∑χ∈F q,characterZeroWeight χ T w
  let K := 6*(1+Real.log (2*(Q:ℝ)))/Q
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hK : 0≤K := by dsimp [K];positivity [Real.log_nonneg (by linarith : 1≤2*(Q:ℝ))]
  have hZ (q) : 0≤Z q := sum_nonneg (fun χ _ => sum_nonneg (fun z _ => mul_nonneg (Nat.cast_nonneg _) (hw z)))
  have hsum : (∑q∈Ioc Q R,Z q)≤primitiveFamilyZeroWeight (2*Q) T w := by
    unfold primitiveFamilyZeroWeight primitiveFamilyZeros primitiveCharacterFamily
    simp only [sum_sigma]
    exact sum_le_sum_of_subset_of_nonneg (show Ioc Q R⊆Icc 1 (2*Q) from fun q hq =>
      mem_Icc.mpr ⟨hQ.trans (mem_Ioc.mp hq).1.le,(mem_Ioc.mp hq).2.trans hR⟩) (fun q _ _ => hZ q)
  have hrow (q : ℕ) (hq : q∈Ioc Q R) : (q.totient:ℝ)⁻¹*(∑χ∈F q,f q χ) ≤ U+K*V*Z q := by
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hq
    have hpos := hQ.trans hlo.le
    letI : NeZero q := ⟨Nat.ne_of_gt hpos⟩
    have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hpos
    have hcard : ((F q).card:ℝ)≤q.totient := by
      exact_mod_cast (card_le_card (filter_subset _ _)).trans_eq (card_univ.trans (card_dirichletCharacter_eq_totient (q:=q)))
    have hfq := sum_le_sum (fun χ (hχ : χ∈F q) => hf q hq χ (mem_filter.mp hχ).2)
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at hfq
    have hqle : (q:ℝ)≤2*(Q:ℝ) := by exact_mod_cast hhi.trans hR
    have hk : (q.totient:ℝ)⁻¹≤K := by
      apply (le_div_iff₀ (zero_lt_one.trans_le hqr)).mpr
      have hq' : (Q:ℝ)≤q := by exact_mod_cast hlo.le
      have hφ' := AnalyticNumberTheory.AdditiveNumberTheory.div_totient_le_six_mul_log hpos
      rw [div_eq_mul_inv,mul_comm] at hφ'
      have hol := Real.log_le_log (by exact_mod_cast hpos : 0<(q:ℝ)) hqle
      exact (mul_le_mul_of_nonneg_left hq' (inv_nonneg.mpr hφ.le)).trans (hφ'.trans (by linarith))
    have ha : (q.totient:ℝ)⁻¹*((F q).card*U)≤U := by
      apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hU) (inv_nonneg.mpr hφ.le)).trans_eq
      field_simp
    apply (mul_le_mul_of_nonneg_left hfq (inv_nonneg.mpr hφ.le)).trans
    rw [mul_add]
    exact add_le_add ha ((mul_le_mul_of_nonneg_right hk (mul_nonneg hV (hZ q))).trans_eq (by ring))
  apply (sum_le_sum hrow).trans
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum]
  have hc : ((Ioc Q R).card:ℝ)≤Q := by rw [Nat.card_Ioc];exact_mod_cast (by omega : R-Q≤Q)
  exact add_le_add (mul_le_mul_of_nonneg_right hc hU) (mul_le_mul_of_nonneg_left hsum (mul_nonneg hK hV))

/-- Maximum of the magnitude of a character Chebyshev sum over real endpoints
between zero and x. -/
def maximalPsiCharNorm {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup ((fun y => ‖psiChar y χ‖) '' Set.Icc 0 x)

theorem norm_psiChar_le_maximalPsiCharNorm {q : ℕ} {x y : ℝ} (χ : DirichletCharacter ℂ q)
    (hy : 0≤y) (hyx : y≤x) : ‖psiChar y χ‖≤maximalPsiCharNorm x χ := by
  unfold maximalPsiCharNorm
  apply le_csSup (s:= (fun t => ‖psiChar t χ‖) '' Set.Icc 0 x) _ ⟨y,⟨hy,hyx⟩,rfl⟩
  refine ⟨(Real.log 4+4)*x,?_⟩
  rintro z ⟨v,hv,rfl⟩
  exact (norm_psiChar_le_const_mul_self hv.1 χ).trans (mul_le_mul_of_nonneg_left hv.2 (by positivity))

/-- Single-character input needed by the zero-density proof of the mean-value
theorem. The symmetric zero sum includes real zeros with analytic multiplicity. -/
def PrimitivePsiExplicitBound : Prop :=
  ∃ C : ℝ,0<C ∧ ∀{x y : ℝ} {q : ℕ},4≤x → 0≤y → y≤x → 2≤q → (q:ℝ)≤2*Real.sqrt x →
    ∀ χ : DirichletCharacter ℂ q,χ.IsPrimitive →
      ‖psiChar y χ‖≤C*(Real.sqrt x*(1+Real.log ((q:ℝ)*x))^2+
        characterZeroWeight χ (Real.sqrt x) (fun z => x^z.re/(1+|z.im|)))

end AnalyticNumberTheory.PrimeDistribution
