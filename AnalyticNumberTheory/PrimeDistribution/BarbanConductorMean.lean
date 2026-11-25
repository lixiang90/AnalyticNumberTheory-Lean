import AnalyticNumberTheory.PrimeDistribution.BarbanConductorWeights
import AnalyticNumberTheory.PrimeDistribution.BarbanConductorSplit

/-!
# The conductor contribution to the Barban–Davenport–Halberstam mean square

Keeping the upper conductor endpoint Q/k allows the large-sieve term
linear in that endpoint to be summed with a convergent cofactor weight.
-/
noncomputable section
open Finset Real
namespace AnalyticNumberTheory.PrimeDistribution

/-- The contribution of the primitive conductors above one to Barban's
mean square, throughout the range x/(log x)^A ≤ Q ≤ x. -/
theorem barban_conductor_mean (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ {x Q : ℝ},2≤x → x/(Real.log x)^A≤Q → Q≤x →
    (∑q∈Icc 1 ⌊Q⌋₊,(q.totient:ℝ)⁻¹*∑d∈q.divisors with 2≤d,primitivePsiEnergy x d)
      ≤ C*x*Q*Real.log x := by
  obtain ⟨C,hC,HC⟩ := barban_primitive_energy_split A hA.le
  obtain ⟨B,hB,HB⟩ := sum_inv_totient_le_mul_log
  obtain ⟨Z,hZ,HZ⟩ := sum_inv_mul_inv_totient_bounded
  let K := Real.log 4+4
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨2*B*(C+2*K)+2*K*Z,by positivity,?_⟩
  intro x Q hx hlower hupper
  let ℓ := Real.log x
  let P := ℓ^A
  have hx₀ : 0<x := by linarith
  have hℓ : 0<ℓ := Real.log_pos (by linarith)
  have hP : 0<P := Real.rpow_pos_of_pos hℓ _
  have hQ : 0<Q := (div_pos hx₀ hP).trans_le hlower
  have hxP : x≤Q*P := (div_le_iff₀ hP).mp hlower
  have hℓ₁ : 1≤ℓ := by
    by_contra! hh
    have hp' := Real.rpow_lt_one hℓ.le hh hA
    exact (not_lt.mpr hxP) ((mul_lt_of_lt_one_right hQ hp').trans_le hupper)
  let J := Icc 1 ⌊Q⌋₊
  let w (k:ℕ) := (k.totient:ℝ)⁻¹
  let Tail (k:ℕ) := ∑d∈Icc 2 (⌊Q⌋₊/k),(d.totient:ℝ)⁻¹*primitivePsiEnergy x d
  let S := (C+2*K)*x*Q
  let M := 2*K*x*Q*ℓ
  have hs₀ : 0≤S := by dsimp only [S];positivity
  have hm₀ : 0≤M := by dsimp only [M];positivity
  have hfloor := Nat.floor_le hQ.le
  have hlog : Real.log ((⌊Q⌋₊:ℝ)+2)≤2*ℓ := by
    have ht : (⌊Q⌋₊:ℝ)+2 ≤ x^2 := by nlinarith only [hfloor,hupper,hx,sq_nonneg (x-2)]
    simpa only [Real.log_pow,Nat.cast_ofNat,ℓ] using Real.log_le_log (by positivity) ht
  have hw : (∑k∈J,w k) ≤ 2*B*ℓ := (HB _).trans
    ((mul_le_mul_of_nonneg_left hlog hB.le).trans_eq (by ring))
  have hwk : (∑k∈J,w k*(k:ℝ)⁻¹) ≤ Z := HZ _
  have hsmall : C*x^2/P≤C*x*Q := by
    apply (div_le_iff₀ hP).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hxP (mul_nonneg hC.le hx₀.le)]
  have htail : 2*x/ℓ^(A+1)≤2*Q/ℓ := by
    rw [Real.rpow_add hℓ,Real.rpow_one]
    change 2*x/(P*ℓ) ≤ _
    rw [div_le_div_iff₀ (mul_pos hP hℓ) hℓ]
    nlinarith only [mul_le_mul_of_nonneg_right hxP hℓ.le]
  have hk (k) (_:k∈J) : Tail k≤S+M*(k:ℝ)⁻¹ := by
    have hk' : ((⌊Q⌋₊/k:ℕ):ℝ)≤Q*(k:ℝ)⁻¹ := by
      rw [←div_eq_mul_inv];exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right hfloor (Nat.cast_nonneg _))
    have hh := HC hx hℓ₁ (⌊Q⌋₊/k)
    change Tail k ≤ C*x^2/P+(2*(_ : ℝ)+2*x/ℓ^(A+1))*(K*x*ℓ) at hh
    apply hh.trans
    calc _ ≤ C*x*Q+(2*(Q*(k:ℝ)⁻¹)+2*Q/ℓ)*(K*x*ℓ) :=
          add_le_add hsmall (mul_le_mul_of_nonneg_right (add_le_add (by linarith only [hk']) htail)
            (mul_nonneg (mul_nonneg hK.le hx₀.le) hℓ.le))
         _ = _ := by dsimp only [S,M];field_simp;ring
  have htotal := totient_conductor_cofactor_bound ⌊Q⌋₊ (primitivePsiEnergy x) (primitivePsiEnergy_nonneg x)
  apply htotal.trans
  change (∑k∈J,w k*Tail k)≤_
  calc _ ≤ ∑k∈J,w k*(S+M*(k:ℝ)⁻¹) := sum_le_sum (fun k hk' => mul_le_mul_of_nonneg_left (hk k hk') (inv_nonneg.mpr (Nat.cast_nonneg _)))
       _ = (∑k∈J,w k)*S+(∑k∈J,w k*(k:ℝ)⁻¹)*M := by
         simp only [sum_mul,←sum_add_distrib];apply sum_congr rfl;intro k _;ring
       _ ≤ 2*B*ℓ*S+Z*M := add_le_add (mul_le_mul_of_nonneg_right hw hs₀) (mul_le_mul_of_nonneg_right hwk hm₀)
       _ = _ := by dsimp only [S,M,ℓ];ring

end AnalyticNumberTheory.PrimeDistribution
