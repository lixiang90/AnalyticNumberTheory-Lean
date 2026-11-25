import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityInputs

/-!
# Assembling Montgomery's primitive-family estimate

A dyadic symmetric fourth moment is available at any scale at least Q²L.
Adding the modulus-one term and joining the two ranges at four fifths recovers
a single bound for the full family of primitive conductors.
-/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Dyadic fourth-moment input on the subtype of primitive conductors. The
cutoff scale can be enlarged, in particular to Q²(L+2) for sparse sampling. -/
theorem primitive_fourth_dyadic_at_scale :
    ∃B : ℝ,0<B ∧ ∀{Q L X : ℕ},1≤Q → 1≤L → Q^2*L≤X → ∀ j : ℕ,
      (∑p∈(primitiveCharacterFamily Q).attach,∫t in -(2^j*(L:ℝ))..2^j*L,‖familyLFunction p.val ((1/2:ℂ)+t*I)‖^4)≤
        B*(2^j*(X:ℝ))*(1+Real.log (2^j*(X:ℝ)))^4 := by
  obtain ⟨B,hB,H⟩ := primitive_conductors_critical_fourth_moment
  refine ⟨B,hB,?_⟩;intro Q L X hQ hL hX j
  let F := primitiveCharacterFamily Q
  let U := (2:ℝ)^j*L
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hU : 1≤U := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by exact_mod_cast hL)
  have hscale : (Q:ℝ)^2*U≤(2:ℝ)^j*X := by
    have hr : (Q:ℝ)^2*L≤X := by exact_mod_cast hX
    dsimp only [U];nlinarith only [mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤2^j by positivity)]
  have hqp : (Q:ℝ)*U≤(Q:ℝ)^2*U := mul_le_mul_of_nonneg_right
    (by nlinarith only [hqr,sq_nonneg ((Q:ℝ)-1)]) (by linarith)
  have hp := one_le_mul_of_one_le_of_one_le hqr hU
  have hl := Real.log_le_log (by linarith : 0<(Q:ℝ)*U) (hqp.trans hscale)
  change (∑p∈F.attach,∫t in (-U)..U,_)≤_
  rw [sum_attach F (fun p => ∫t in (-U)..U,‖familyLFunction p ((1/2:ℂ)+t*I)‖^4)]
  apply (H hQ hU).trans
  rw [mul_assoc B]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hscale hB.le)
    (pow_le_pow_left₀ (by linarith [Real.log_nonneg hp]) (add_le_add_right hl 1) 4) (by positivity) (by positivity)

/-- Promoting a logarithmic exponent on [2,∞) costs at most two per power. -/
theorem log_pow_le_scaled_log_pow {a b : ℕ} (hab : a≤b) {Y : ℝ} (hY : 2≤Y) :
    (Real.log Y)^a≤(2:ℝ)^(b-a)*(Real.log Y)^b := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hab
  have h : 1/2≤Real.log Y := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log zero_lt_two hY)
  have hp := one_le_pow₀ (show 1≤2*Real.log Y by linarith) (n:=n)
  rw [mul_pow] at hp
  calc (Real.log Y)^a ≤ (Real.log Y)^a*((2:ℝ)^n*(Real.log Y)^n) :=
          le_mul_of_one_le_right (pow_nonneg (by linarith) _) hp
       _ = _ := by rw [Nat.add_sub_cancel_left,pow_add];ring

/-- Adding the principal character and treating the range up to four fifths
by Ingham gives the full, symmetric primitive-conductor estimate. -/
theorem primitive_conductors_montgomery_join (k : ℕ) (hk : 8≤k)
    (H : ∃D : ℝ,0<D ∧ ∀{Q : ℕ}{σ T : ℝ},1≤Q → σ∈Set.Icc (4/5:ℝ) 1 → 2≤T →
      (primitiveFamilyZeroCount Q σ T:ℝ)≤ D*((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^k)
    (P : ∃E : ℝ,0<E ∧ ∀{σ T : ℝ},σ∈Set.Icc (4/5:ℝ) 1 → 2≤T →
      (characterDensityCount (1 : DirichletCharacter ℂ 1) σ T:ℝ)≤ E*T^(montgomeryExponent σ)*(Real.log T)^k) :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ}{σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) 1 → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^k := by
  obtain ⟨D,hD,HH⟩ := H
  obtain ⟨E,hE,HP⟩ := P
  obtain ⟨B,hB,HB⟩ := primitive_conductors_montgomery_left
  refine ⟨(2:ℝ)^(k-8)*B+E+D,by positivity,?_⟩
  intro Q σ T hQ hσ hT
  let H := (Q:ℝ)^2*T
  let Y := (Q:ℝ)*T
  have hr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have ht : T≤Y := le_mul_of_one_le_left (by linarith) hr
  have hbase : T≤H := le_mul_of_one_le_left (by linarith) (one_le_pow₀ hr)
  have hy := hT.trans ht
  have hlog := Real.log_nonneg (by linarith : 1≤Y)
  have hpow : 0≤H^(montgomeryExponent σ) := Real.rpow_nonneg (by linarith) _
  change _ ≤ ((2:ℝ)^(k-8)*B+E+D)*H^(montgomeryExponent σ)*(Real.log Y)^k
  by_cases hleft : σ≤4/5
  · have hb := HB hQ ⟨hσ.1,hleft⟩ hT
    change _≤B*H^(montgomeryExponent σ)*(Real.log Y)^8 at hb
    apply hb.trans
    have hn := mul_le_mul_of_nonneg_left (log_pow_le_scaled_log_pow hk hy)
      (mul_nonneg hB.le hpow)
    nlinarith only [hn,mul_nonneg (add_nonneg hE.le hD.le) (mul_nonneg hpow (pow_nonneg hlog k))]
  · have hright : σ∈Set.Icc (4/5:ℝ) 1 := ⟨by linarith,hσ.2⟩
    have h := HH hQ hright hT
    change _≤D*H^(montgomeryExponent σ)*(Real.log Y)^k at h
    have he : 0 ≤ montgomeryExponent σ := by
      unfold montgomeryExponent;exact div_nonneg (by linarith [hσ.2]) (by linarith [hσ.1])
    have hp := (HP hright hT).trans (mul_le_mul (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith : 0≤T) hbase he) hE.le)
      (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) ht) k)
      (pow_nonneg (Real.log_nonneg (by linarith)) _) (mul_nonneg hE.le hpow))
    have hs := congrArg (fun n : ℕ => (n:ℝ)) (primitive_density_sum_eq_principal_add hQ σ T)
    push_cast at hs
    rw [hs]
    nlinarith only [h,hp,mul_nonneg (mul_nonneg (by positivity : 0≤(2:ℝ)^(k-8)) hB.le) (mul_nonneg hpow (pow_nonneg hlog k))]

end AnalyticNumberTheory.PrimeDistribution
