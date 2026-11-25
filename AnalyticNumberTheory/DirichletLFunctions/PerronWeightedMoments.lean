import AnalyticNumberTheory.AnalyticTools.ReciprocalHeightIntegrals
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveFamilyFourthStrips
import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthMoment

/-! # Fourth moments with the Perron weight over primitive conductors -/
noncomputable section
open Complex Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem weighted_fixed_mean {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i∈S, Continuous (f i)) (hf₀ : ∀ i∈S, ∀ t, 0≤f i t)
    {q T D : ℝ} (hq : 1≤q) (hT : 2≤T) (hD : 0≤D) (k : ℕ)
    (H : ∀ u : ℝ, 2≤u → (∑ i∈S, ∫t in -u..u,f i t) ≤ D*u*(Real.log (q*u))^k) :
    (∑ i∈S,∫t in -T..T, f i t/‖(1/2:ℂ)+(t:ℂ)*I‖) ≤
      (18*(2:ℝ)^k/Real.log 2)*D*(Real.log (q*T))^(k+1) := by
  let F (t : ℝ) := ∑i∈S,f i t
  have cf : Continuous F := continuous_finsetSum _ hf
  have hpos t : 0≤F t := sum_nonneg (fun i hi => hf₀ i hi t)
  have h₂ : 0<Real.log 2 := Real.log_pos one_lt_two
  have hqT : 2≤q*T := hT.trans (le_mul_of_one_le_left (by linarith) hq)
  let L := Real.log (q*T)
  have hL : Real.log 2≤L := Real.log_le_log (by norm_num) hqT
  have hL₀ : 0≤L := h₂.le.trans hL
  have hu {u : ℝ} (h : 2≤u) (h' : u≤2*T) : (∫t in -u..u,F t) ≤ D*(2*L)^k*u := by
    dsimp only [F]
    rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable ..)]
    have hx : 0<q*u := by positivity
    have hy : Real.log (q*u) ≤ 2*L := by
      have hh := Real.log_le_log hx (show q*u≤(q*T)*2 by nlinarith only [mul_le_mul_of_nonneg_left h' (by linarith : 0≤q)])
      rw [Real.log_mul (by linarith : q*T≠0) (by norm_num)] at hh
      linarith only [hh,hL]
    have hqu : 1≤q*u := one_le_mul_of_one_le_of_one_le hq (by linarith)
    exact (H u h).trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_nonneg hqu) hy k) (by positivity : 0≤D*u)).trans_eq (by ring))
  have hh := critical_perron_integral_of_linear_mean cf hpos hT (by positivity : 0≤D*(2*L)^k)
    (fun u h h' => hu h h')
  have cden : Continuous (fun t : ℝ => ‖(1/2:ℂ)+(t:ℂ)*I‖) := by fun_prop
  have hne (t : ℝ) : ‖(1/2:ℂ)+(t:ℂ)*I‖≠0 := by
    have h := Complex.abs_re_le_norm ((1/2:ℂ)+(t:ℂ)*I)
    simp at h
    linarith
  rw [←intervalIntegral.integral_finsetSum (f:=fun i t => f i t/‖(1/2:ℂ)+(t:ℂ)*I‖)
    (fun i hi => ((hf i hi).div cden hne).intervalIntegrable ..)]
  simp only [←sum_div]
  apply hh.trans
  have htlog : Real.log T≤L := Real.log_le_log (by linarith)
    (le_mul_of_one_le_left (by linarith) hq)
  have hr : 2+Real.log T/Real.log 2≤3*L/Real.log 2 := by
    apply (le_div_iff₀ h₂).mpr
    field_simp
    linarith
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0≤6*(D*(2*L)^k))).trans_eq
  dsimp only [L];rw [mul_pow,pow_succ];ring

private theorem weighted_conductor_fourth (G : ((q:ℕ) × DirichletCharacter ℂ q) → ℂ → ℂ)
    (hG : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      Continuous (fun t : ℝ => G ⟨q,χ⟩ ((1/2:ℂ)+(t:ℂ)*I)))
    (k : ℕ) {D : ℝ} (hD : 0<D)
    (H : ∀ {q : ℕ} [NeZero q] {u : ℝ}, 2≤u →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫t in -u..u, ‖G ⟨q,χ⟩ ((1/2:ℂ)+(t:ℂ)*I)‖^4)
        ≤ D*q.totient*u*(Real.log (q*u))^k) {Q : ℕ} {T : ℝ} (hQ : 1≤Q) (hT : 2≤T) :
    (∑ p∈PrimeDistribution.primitiveCharacterFamily Q, (p.1.totient:ℝ)⁻¹*
        ∫ t in -T..T, ‖G p ((1/2:ℂ)+(t:ℂ)*I)‖^4/‖(1/2:ℂ)+(t:ℂ)*I‖) ≤
      ((18*(2:ℝ)^k/Real.log 2)*D)*Q*(Real.log (Q*T))^(k+1) := by
  let C := (18*(2:ℝ)^k/Real.log 2)*D
  have hC : 0≤C := by dsimp [C];positivity
  simp only [PrimeDistribution.primitiveCharacterFamily,sum_sigma]
  apply (sum_le_sum (g:=fun _ : ℕ => C*(Real.log (Q*T))^(k+1)) (fun q hq => ?_)).trans_eq
  · simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_one_sub_one]
    dsimp only [C];ring
  · obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
    haveI : NeZero q := ⟨by omega⟩
    have hf := weighted_fixed_mean ((univ:Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive))
      (fun χ t => ‖G ⟨q,χ⟩ ((1/2:ℂ)+t*I)‖^4) (fun χ _ => (hG χ).norm.pow 4)
      (fun χ _ t => by positivity) (by exact_mod_cast hq₁ : (1:ℝ)≤q) hT
      (by positivity : 0≤D*(q.totient:ℝ)) k (fun u hu => H hu)
    have hφ : (0:ℝ)<q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq₁)
    have ht : 1≤(q:ℝ)*T := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hq₁) (by linarith)
    have hl := Real.log_le_log (by linarith : (0:ℝ)<q*T)
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hqQ : (q:ℝ)≤Q) (by linarith : 0≤T))
    rw [←mul_sum]
    apply (mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hφ.le)).trans
    calc _ = C*(Real.log (q*T))^(k+1) := by dsimp only [C];field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg ht) hl _) hC

private theorem family_eval {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    familyLFunction ⟨q,χ⟩=χ.LFunction := by
  funext s
  simp only [familyLFunction,dif_neg (NeZero.ne q)]

/-- Primitive L-functions through conductor Q, with the Perron weights
1/φ(q) and 1/|1/2+it|. The single extra logarithm sums the heights. -/
theorem primitive_perron_fourth_moment :
    ∃ C > 0, ∀ {Q : ℕ} {T : ℝ}, 1≤Q → 2≤T →
      (∑ p∈PrimeDistribution.primitiveCharacterFamily Q, (p.1.totient:ℝ)⁻¹*
        ∫ t in -T..T, ‖familyLFunction p ((1/2:ℂ)+t*I)‖^4 / ‖(1/2:ℂ)+t*I‖)
        ≤ C*Q*(Real.log (Q*T))^5 := by
  obtain ⟨D,hD,H⟩ := primitive_family_fourth_narrow_symmetric
  refine ⟨(18*(2:ℝ)^4/Real.log 2)*D,by positivity,fun hQ hT => ?_⟩
  apply weighted_conductor_fourth familyLFunction _ 4 hD _ hQ hT
  · intro q _ χ
    simp only [family_eval]
    exact continuous_iff_continuousAt.mpr fun t =>
      (analyticAt_LFunction_re_lt_one χ (z:=(1/2:ℂ)+t*I) (by norm_num)).continuousAt.comp (f:=fun u : ℝ => (1/2:ℂ)+u*I) (by fun_prop)
  · intro q _ u hu
    simpa only [family_eval,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using H (q:=q) (σ:=1/2) hu (by
      rw [sub_self,abs_zero];positivity [Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by exact_mod_cast NeZero.pos q : (1:ℝ)≤q) (by linarith : 1≤u))])

/-- Fourth moments of the derivatives of primitive L-functions in the same
Perron integral. Cauchy's formula contributes four powers of the logarithm. -/
theorem primitive_perron_deriv_fourth_moment :
    ∃ C > 0, ∀ {Q : ℕ} {T : ℝ}, 1≤Q → 2≤T →
      (∑ p∈PrimeDistribution.primitiveCharacterFamily Q, (p.1.totient:ℝ)⁻¹*
        ∫ t in -T..T, ‖deriv (familyLFunction p) ((1/2:ℂ)+t*I)‖^4 / ‖(1/2:ℂ)+t*I‖)
        ≤ C*Q*(Real.log (Q*T))^9 := by
  obtain ⟨D,hD,H⟩ := primitive_family_deriv_fourth_narrow_symmetric
  refine ⟨(18*(2:ℝ)^8/Real.log 2)*D,by positivity,fun hQ hT => ?_⟩
  apply weighted_conductor_fourth (fun p => deriv (familyLFunction p)) _ 8 hD _ hQ hT
  · intro q _ χ
    simp only [family_eval]
    exact continuous_iff_continuousAt.mpr fun t =>
      (analyticAt_LFunction_re_lt_one χ (z:=(1/2:ℂ)+t*I) (by norm_num)).deriv.continuousAt.comp (f:=fun u : ℝ => (1/2:ℂ)+u*I) (by fun_prop)
  · intro q _ u hu
    simpa only [family_eval,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using H (q:=q) (σ:=1/2) hu (by
      rw [sub_self,abs_zero];positivity [Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by exact_mod_cast NeZero.pos q : (1:ℝ)≤q) (by linarith : 1≤u))])

end AnalyticNumberTheory.DirichletLFunctions
