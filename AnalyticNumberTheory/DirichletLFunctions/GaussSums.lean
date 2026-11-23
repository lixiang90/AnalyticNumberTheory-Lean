import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Gauss Sums for Dirichlet Characters

This file develops the theory of Gauss sums attached to complex Dirichlet characters:

`gaussSum χ a := ∑ x : ZMod q, χ x * exp (2 * π * I * a * x / q)`

bridging Mathlib's `AddChar`/`MulChar` Gauss sum `_root_.gaussSum` and `ZMod.stdAddChar`,
and establishing:

- Sign, conjugation, and Fourier inversion identities (`gaussSum_neg_one`,
  `star_gaussSum`, `gaussSum_star`, `gaussSum_eq_dft_neg`).
- Separability `gaussSum χ a = star (χ a) * gaussSum χ 1` when `Nat.Coprime a q` or
  `χ` is primitive.
- Fundamental modulus identity `‖gaussSum χ 1‖ = √q` and `gaussSum χ 1 * star (gaussSum χ 1) = q`
  for primitive characters.
- Exact reduction of imprimitive Gauss sums to the inducing primitive Gauss sum times a
  Möbius / Ramanujan divisor sum factor, including `gaussSum χ 1 = μ(q/d) * χ*(q/d) * gaussSum χ* 1`
  and `gaussSum 1 a = ∑_{ℓ ∣ gcd(a, q)} μ(q / ℓ) * ℓ`.
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius Classical

namespace AnalyticNumberTheory.DirichletLFunctions

private theorem sum_zmod_eq_sum_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ a : ZMod q, f a = ∑ a ∈ Finset.range q, f (a : ZMod q) := by
  refine Finset.sum_bij (fun a _ ↦ a.val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a₁ _ a₂ _ h
    exact ZMod.val_injective q h
  · intro b hb
    refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)
  · intro a _
    simp

section DefinitionsAndBridge

variable {q : ℕ} [NeZero q]

/-- The Gauss sum `G(χ, a) = ∑_{x mod q} χ(x) exp(2πi a x / q)` associated to a complex
Dirichlet character `χ` modulo `q` and residue `a : ZMod q`. -/
noncomputable def gaussSum (χ : DirichletCharacter ℂ q) (a : ZMod q) : ℂ :=
  _root_.gaussSum χ (ZMod.stdAddChar.mulShift a)

/-- At `a = 1`, `gaussSum χ 1` coincides with Mathlib's `_root_.gaussSum χ ZMod.stdAddChar`. -/
theorem gaussSum_one_eq_mathlib (χ : DirichletCharacter ℂ q) :
    gaussSum χ 1 = _root_.gaussSum χ ZMod.stdAddChar := by
  simp [gaussSum]

/-- Explicit finite-sum formula over `ZMod q` for `gaussSum χ a`. -/
theorem gaussSum_eq_sum_zmod (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    gaussSum χ a =
      ∑ x : ZMod q, χ x * Complex.exp (2 * Real.pi * Complex.I * ((a * x).val : ℂ) / (q : ℂ)) := by
  simp only [gaussSum, _root_.gaussSum, AddChar.mulShift_apply, ZMod.stdAddChar_apply,
    ZMod.toCircle_apply]

/-- Explicit finite-sum formula over `Finset.range q` for `gaussSum χ (a : ZMod q)` with `a : ℤ`. -/
theorem gaussSum_int_eq_sum_range (χ : DirichletCharacter ℂ q) (a : ℤ) :
    gaussSum χ (a : ZMod q) =
      ∑ x ∈ Finset.range q,
        χ x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ)) := by
  simp only [gaussSum, _root_.gaussSum, AddChar.mulShift_apply]
  rw [sum_zmod_eq_sum_range (fun x ↦ χ x * ZMod.stdAddChar ((a : ZMod q) * x))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hcoe : ((a : ZMod q) * (x : ZMod q)) = (((a * (x : ℤ) : ℤ)) : ZMod q) := by
    push_cast
    rfl
  rw [hcoe, ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- Explicit finite-sum formula over `Finset.range q` for `gaussSum χ (a : ZMod q)` with `a : ℕ`. -/
theorem gaussSum_nat_eq_sum_range (χ : DirichletCharacter ℂ q) (a : ℕ) :
    gaussSum χ (a : ZMod q) =
      ∑ x ∈ Finset.range q,
        χ x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ)) := by
  simpa using gaussSum_int_eq_sum_range χ (a : ℤ)

/-- Relation between `gaussSum` and Mathlib's discrete Fourier transform `ZMod.dft`. -/
theorem dft_eq_gaussSum (χ : DirichletCharacter ℂ q) (k : ZMod q) :
    ZMod.dft χ k = gaussSum χ (-k) :=
  DirichletCharacter.fourierTransform_eq_gaussSum_mulShift χ k

end DefinitionsAndBridge

section BasicIdentities

variable {q : ℕ} [NeZero q]

/-- Value of `gaussSum χ 0`: equals `q.totient` if `χ = 1`, and `0` otherwise. -/
theorem gaussSum_zero_right (χ : DirichletCharacter ℂ q) :
    gaussSum χ 0 = if χ = 1 then (q.totient : ℂ) else 0 := by
  simp only [gaussSum, AddChar.mulShift_zero]
  split_ifs with h
  · rw [h, gaussSum_one_one, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  · exact gaussSum_one_right h

/-- Negating the frequency multiplies `gaussSum χ a` by `χ (-1)`:
`gaussSum χ (-a) = χ (-1) * gaussSum χ a`. -/
theorem gaussSum_neg (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    gaussSum χ (-a) = χ (-1) * gaussSum χ a := by
  have hshift : ZMod.stdAddChar.mulShift (-a) = (ZMod.stdAddChar.mulShift a)⁻¹ := by
    ext x
    simp [AddChar.mulShift_apply, AddChar.inv_apply]
  rw [gaussSum, hshift, gaussSum_inv_right, gaussSum]

/-- At `a = -1`, `gaussSum χ (-1) = χ (-1) * gaussSum χ 1`. -/
theorem gaussSum_neg_one (χ : DirichletCharacter ℂ q) :
    gaussSum χ (-1) = χ (-1) * gaussSum χ 1 :=
  gaussSum_neg χ 1

/-- Complex conjugation of `gaussSum χ a`:
`star (gaussSum χ a) = χ (-1) * gaussSum (star χ) a`. -/
theorem star_gaussSum (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    star (gaussSum χ a) = χ (-1) * gaussSum (star χ) a := by
  rw [gaussSum, star_gaussSum_eq, MulChar.star_eq_inv, gaussSum]
  have hinv : (ZMod.stdAddChar.mulShift a)⁻¹ =
      (ZMod.stdAddChar.mulShift a).mulShift (-1 : ZMod q) := by
    rw [AddChar.inv_mulShift]
  rw [hinv, show (-1 : ZMod q) = ((-1 : (ZMod q)ˣ) : ZMod q) by simp,
    gaussSum_mulShift_eq, inv_inv, Units.val_neg, Units.val_one]

/-- `gaussSum (star χ) a = χ (-1) * star (gaussSum χ a)`. -/
theorem gaussSum_star (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    gaussSum (star χ) a = χ (-1) * star (gaussSum χ a) := by
  rw [star_gaussSum, ← mul_assoc, ← map_mul, mul_neg_one, neg_neg, map_one, one_mul]

/-- `gaussSum χ⁻¹ a = χ (-1) * star (gaussSum χ a)`. -/
theorem gaussSum_inv (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    gaussSum χ⁻¹ a = χ (-1) * star (gaussSum χ a) := by
  simpa [MulChar.star_eq_inv] using gaussSum_star χ a

/-- Conjugating `χ` preserves the modulus of `gaussSum χ a`. -/
theorem norm_gaussSum_star (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖gaussSum (star χ) a‖ = ‖gaussSum χ a‖ := by
  rw [gaussSum_star, norm_mul, χ.norm_neg_one, one_mul, norm_star]

/-- Inverting `χ` preserves the modulus of `gaussSum χ a`. -/
theorem norm_gaussSum_inv (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖gaussSum χ⁻¹ a‖ = ‖gaussSum χ a‖ := by
  simpa [MulChar.star_eq_inv] using norm_gaussSum_star χ a

end BasicIdentities

section SeparabilityAndModulus

variable {q : ℕ} [NeZero q]

/-- Separability when `IsUnit a`: `gaussSum χ a = star (χ a) * gaussSum χ 1`. -/
theorem gaussSum_eq_star_mul_of_isUnit (χ : DirichletCharacter ℂ q) {a : ZMod q}
    (ha : IsUnit a) :
    gaussSum χ a = star (χ a) * gaussSum χ 1 := by
  rw [gaussSum, ← ha.unit_spec, gaussSum_mulShift_eq, MulChar.star_apply', ha.unit_spec,
    gaussSum_one_eq_mathlib]

/-- Separability when `Nat.Coprime a q`: `gaussSum χ a = star (χ a) * gaussSum χ 1`. -/
theorem gaussSum_eq_star_mul_of_coprime (χ : DirichletCharacter ℂ q) {a : ℕ}
    (ha : Nat.Coprime a q) :
    gaussSum χ a = star (χ a) * gaussSum χ 1 :=
  gaussSum_eq_star_mul_of_isUnit χ ((ZMod.isUnit_iff_coprime a q).mpr ha)

/-- Separability for primitive characters (`∀ a : ZMod q`):
if `χ` is primitive, then `gaussSum χ a = star (χ a) * gaussSum χ 1` for every `a`. -/
theorem gaussSum_eq_star_mul_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (a : ZMod q) :
    gaussSum χ a = star (χ a) * gaussSum χ 1 := by
  rw [gaussSum, _root_.gaussSum_mulShift_of_isPrimitive _ hχ,
    MulChar.star_apply', gaussSum_one_eq_mathlib]

/-- Inverse-character separability for primitive characters:
`gaussSum χ a = χ⁻¹ a * gaussSum χ 1`. -/
theorem gaussSum_eq_inv_mul_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (a : ZMod q) :
    gaussSum χ a = χ⁻¹ a * gaussSum χ 1 := by
  simpa [MulChar.star_apply'] using gaussSum_eq_star_mul_of_isPrimitive hχ a

/-- Fourier inversion form for a primitive character `χ`:
`∑ a : ZMod q, star (χ a) * exp(2πi n a / q) = χ n * gaussSum (star χ) 1`. -/
theorem sum_star_char_mul_cexp_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (n : ZMod q) :
    ∑ a : ZMod q, star (χ a) *
        Complex.exp (2 * Real.pi * Complex.I * ((n * a).val : ℂ) / (q : ℂ)) =
      χ n * gaussSum (star χ) 1 := by
  have hprim : (star χ).IsPrimitive := by
    rw [MulChar.star_eq_inv]
    exact hχ.inv
  have h1 := gaussSum_eq_star_mul_of_isPrimitive hprim n
  rw [gaussSum_eq_sum_zmod] at h1
  simpa only [MulChar.star_apply, star_star] using h1

/-- Fundamental modulus identity for primitive Gauss sums: `‖gaussSum χ 1‖ = √q`. -/
theorem norm_gaussSum_one_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ 1‖ = Real.sqrt q := by
  rw [gaussSum_one_eq_mathlib]
  exact DirichletCharacter.norm_gaussSum_stdAddChar hχ

/-- For primitive `χ`, `gaussSum χ 1 ≠ 0`. -/
theorem gaussSum_one_ne_zero_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum χ 1 ≠ 0 := by
  intro h0
  have hnorm := norm_gaussSum_one_of_isPrimitive hχ
  rw [h0, norm_zero] at hnorm
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos q))
  linarith

/-- For primitive `χ`, `gaussSum χ 1 * star (gaussSum χ 1) = q`. -/
theorem gaussSum_one_mul_star_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum χ 1 * star (gaussSum χ 1) = (q : ℂ) := by
  have hnorm := norm_gaussSum_one_of_isPrimitive hχ
  have hmul : gaussSum χ 1 * star (gaussSum χ 1) = ((‖gaussSum χ 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmul, hnorm, Real.sq_sqrt (Nat.cast_nonneg q)]
  push_cast
  rfl

/-- For primitive `χ`, `gaussSum χ 1 * gaussSum (star χ) 1 = χ (-1) * q`. -/
theorem gaussSum_one_mul_gaussSum_star_of_isPrimitive {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    gaussSum χ 1 * gaussSum (star χ) 1 = χ (-1) * (q : ℂ) := by
  rw [gaussSum_star, mul_left_comm, gaussSum_one_mul_star_of_isPrimitive hχ]

/-- Modulus of `gaussSum χ a` for primitive `χ`: equals `√q` when `IsUnit a`, and `0` otherwise. -/
theorem norm_gaussSum_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (a : ZMod q) :
    ‖gaussSum χ a‖ = if IsUnit a then Real.sqrt q else 0 := by
  rw [gaussSum_eq_star_mul_of_isPrimitive hχ a, norm_mul, norm_star,
    norm_gaussSum_one_of_isPrimitive hχ]
  split_ifs with ha
  · rw [← ha.unit_spec, χ.unit_norm_eq_one ha.unit, one_mul]
  · rw [χ.map_nonunit ha, norm_zero, zero_mul]

end SeparabilityAndModulus

section ImprimitiveReduction

private theorem sum_range_cexp_int_div {m : ℕ} (hm : 0 < m) (a : ℤ) :
    ∑ v ∈ Finset.range m,
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (v : ℂ) / (m : ℂ)) =
      if (m : ℤ) ∣ a then (m : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (m : ℂ))
  have hsum : (∑ v ∈ Finset.range m,
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (v : ℂ) / (m : ℂ))) =
      ∑ v ∈ Finset.range m, ζ ^ v := by
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hsum]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hζ_iff : ζ = 1 ↔ (m : ℤ) ∣ a := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hdiv : (a : ℂ) / (m : ℂ) = (k : ℂ) := by
        have hk' : (2 * Real.pi * Complex.I) * ((a : ℂ) / (m : ℂ)) =
            (2 * Real.pi * Complex.I) * (k : ℂ) := by
          calc
            (2 * Real.pi * Complex.I) * ((a : ℂ) / (m : ℂ))
                = 2 * Real.pi * Complex.I * (a : ℂ) / (m : ℂ) := by ring
            _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
            _ = (2 * Real.pi * Complex.I) * (k : ℂ) := by ring
        exact mul_left_cancel₀ h2pi hk'
      have ha_eq : (a : ℂ) = ((k * (m : ℤ) : ℤ) : ℂ) := by
        push_cast
        rw [← hdiv]
        field_simp [hm0]
      have ha_int : a = k * (m : ℤ) := Int.cast_injective ha_eq
      exact ⟨k, by rw [ha_int, mul_comm]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have ha_eq : (a : ℂ) = (m : ℂ) * (k : ℂ) := by exact_mod_cast hk
      rw [ha_eq]
      field_simp [hm0]
  split_ifs with hdvd
  · have hζ1 : ζ = 1 := hζ_iff.mpr hdvd
    simp [hζ1]
  · have hζne : ζ ≠ 1 := fun h ↦ hdvd (hζ_iff.mp h)
    have hζm : ζ ^ m = 1 := by
      dsimp only [ζ]
      rw [← Complex.exp_nat_mul]
      have hexp : (m : ℂ) * (2 * Real.pi * Complex.I * (a : ℂ) / (m : ℂ)) =
          (a : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp [hm0]
      rw [hexp, Complex.exp_eq_one_iff]
      exact ⟨a, rfl⟩
    have hmul : (∑ v ∈ Finset.range m, ζ ^ v) * (ζ - 1) = 0 := by
      rw [geom_sum_mul, hζm, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hζne)

private theorem char_eq_primitive_mul_moebius {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℕ) :
    χ x = χ.primitiveCharacter x *
      ∑ k ∈ (q / χ.conductor).divisors, if k ∣ x then (μ k : ℂ) else 0 := by
  let d := χ.conductor
  let r := q / d
  have hd_dvd : d ∣ q := χ.conductor_dvd_level
  have hq_eq : q = d * r := (Nat.mul_div_cancel' hd_dvd).symm
  have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd_dvd)
    (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hsum_gcd : ∑ k ∈ r.divisors, (if k ∣ x then (μ k : ℂ) else 0) =
      if Nat.Coprime x r then 1 else 0 := by
    have hsub : ∑ k ∈ r.divisors, (if k ∣ x then (μ k : ℂ) else 0) =
        ∑ k ∈ (Nat.gcd x r).divisors, (μ k : ℂ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
      ext k
      simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hkr, _⟩, hkx⟩
        exact ⟨⟨hkx, hkr⟩, fun h0 ↦ hr_pos.ne' (Nat.gcd_eq_zero_iff.mp h0).2⟩
      · rintro ⟨⟨hkx, hkr⟩, _⟩
        exact ⟨⟨hkr, hr_pos.ne'⟩, hkx⟩
    rw [hsub]
    have hmu : (∑ k ∈ (Nat.gcd x r).divisors, μ k) =
        if Nat.gcd x r = 1 then 1 else 0 := by
      rw [← ArithmeticFunction.coe_mul_zeta_apply]
      rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    have hmuC : (∑ k ∈ (Nat.gcd x r).divisors, (μ k : ℂ)) =
        if Nat.Coprime x r then 1 else 0 := by
      have := congrArg (Int.cast (R := ℂ)) hmu
      push_cast at this
      simpa [Nat.Coprime] using this
    exact hmuC
  rw [hsum_gcd]
  split_ifs with hxr
  · rw [mul_one]
    by_cases hxd : Nat.Coprime x d
    · have hxq : Nat.Coprime x q := by
        rw [hq_eq]
        exact Nat.Coprime.mul_right hxd hxr
      have hx_int : χ ((x : ℤ) : ZMod q) = χ.primitiveCharacter ((x : ℤ) : ZMod d) :=
        (χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hxq)).symm
      simpa using hx_int
    · have hxq : ¬ Nat.Coprime x q := fun h ↦ hxd (h.coprime_dvd_right hd_dvd)
      have h1 : χ x = 0 := by
        rw [← Int.cast_natCast x, χ.apply_eq_zero_iff]
        exact mt Nat.isCoprime_iff_coprime.mp hxq
      have h2 : χ.primitiveCharacter x = 0 := by
        rw [← Int.cast_natCast x, χ.primitiveCharacter.apply_eq_zero_iff]
        exact mt Nat.isCoprime_iff_coprime.mp hxd
      rw [h1, h2]
  · have hxq : ¬ Nat.Coprime x q := by
      intro h
      exact hxr (h.coprime_dvd_right (Nat.div_dvd_of_dvd hd_dvd))
    have h1 : χ x = 0 := by
      rw [← Int.cast_natCast x, χ.apply_eq_zero_iff]
      exact mt Nat.isCoprime_iff_coprime.mp hxq
    simp [h1]

/-- **Exact imprimitive Gauss sum reduction formula**:
for any Dirichlet character `χ` modulo `q` (`[NeZero q]`) with conductor `d := χ.conductor`,
primitive character `χ* := χ.primitiveCharacter`, and cofactor `r := q / d`,
`gaussSum χ a = (∑ ℓ ∈ (Nat.gcd a.natAbs r).divisors, μ(r / ℓ) * ℓ * χ*(r / ℓ) * star (χ*(a / ℓ))) * gaussSum χ* 1`. -/
theorem gaussSum_eq_sum_divisors_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a : ℤ) :
    let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    let d := χ.conductor
    let r := q / d
    let χs := χ.primitiveCharacter
    gaussSum χ (a : ZMod q) =
      (∑ ℓ ∈ (Nat.gcd a.natAbs r).divisors,
        (μ (r / ℓ) : ℂ) * (ℓ : ℂ) * χs (r / ℓ : ℕ) * star (χs ((a / (ℓ : ℤ)) : ZMod d))) *
        gaussSum χs 1 := by
  intro _ d r χs
  have hd_pos : 0 < d := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have : NeZero d := ⟨hd_pos.ne'⟩
  have hd_dvd : d ∣ q := χ.conductor_dvd_level
  have hq_eq : q = d * r := (Nat.mul_div_cancel' hd_dvd).symm
  have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd_dvd) hd_pos
  rw [gaussSum_int_eq_sum_range]
  simp_rw [char_eq_primitive_mul_moebius χ]
  have hswap : (∑ x ∈ Finset.range q,
      (χs x * ∑ k ∈ r.divisors, if k ∣ x then (μ k : ℂ) else 0) *
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ))) =
      ∑ k ∈ r.divisors, (μ k : ℂ) *
        ∑ x ∈ (Finset.range q).filter (fun x ↦ k ∣ x),
          χs x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ)) := by
    calc
      ∑ x ∈ Finset.range q,
          (χs x * ∑ k ∈ r.divisors, if k ∣ x then (μ k : ℂ) else 0) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ))
          = ∑ x ∈ Finset.range q, ∑ k ∈ r.divisors,
              (μ k : ℂ) * (if k ∣ x then
                χs x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ))
              else 0) := by
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            split_ifs <;> ring
      _ = ∑ k ∈ r.divisors, ∑ x ∈ Finset.range q,
              (μ k : ℂ) * (if k ∣ x then
                χs x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ))
              else 0) := Finset.sum_comm
      _ = ∑ k ∈ r.divisors, (μ k : ℂ) *
            ∑ x ∈ (Finset.range q).filter (fun x ↦ k ∣ x),
              χs x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ)) := by
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [← Finset.mul_sum, Finset.sum_filter]
  rw [hswap]
  have hinner (k : ℕ) (hk : k ∈ r.divisors) :
      ∑ x ∈ (Finset.range q).filter (fun x ↦ k ∣ x),
          χs x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ)) =
        (if ((r / k : ℕ) : ℤ) ∣ a then
          ((r / k : ℕ) : ℂ) * χs (k : ZMod d) *
            star (χs ((a / ((r / k : ℕ) : ℤ)) : ZMod d)) * gaussSum χs 1
        else 0) := by
    have hk_dvd : k ∣ r := Nat.dvd_of_mem_divisors hk
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    let m := r / k
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hr_pos hk_dvd) hk_pos
    have hkm : k * m = r := Nat.mul_div_cancel' hk_dvd
    have hq_kdm : q = k * (d * m) := by rw [hq_eq, ← hkm]; ring
    have hbij : ∑ x ∈ (Finset.range q).filter (fun x ↦ k ∣ x),
          χs x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ)) =
        ∑ uv ∈ Finset.range d ×ˢ Finset.range m,
          χs (k * (uv.1 + d * uv.2) : ℕ) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) *
              ((k * (uv.1 + d * uv.2) : ℕ) : ℂ) / (q : ℂ)) := by
      symm
      refine Finset.sum_bij (fun uv _ ↦ k * (uv.1 + d * uv.2)) ?_ ?_ ?_ ?_
      · intro uv huv
        simp only [Finset.mem_product, Finset.mem_range] at huv
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, dvd_mul_right k _⟩
        have hlt : uv.1 + d * uv.2 < d * m := by
          have : uv.2 + 1 ≤ m := huv.2
          calc
            uv.1 + d * uv.2 < d + d * uv.2 := by linarith [huv.1]
            _ = d * (uv.2 + 1) := by ring
            _ ≤ d * m := Nat.mul_le_mul_left d this
        rw [hq_kdm]
        exact Nat.mul_lt_mul_of_pos_left hlt hk_pos
      · intro uv₁ huv₁ uv₂ huv₂ h
        simp only [Finset.mem_product, Finset.mem_range] at huv₁ huv₂
        have heq : uv₁.1 + d * uv₁.2 = uv₂.1 + d * uv₂.2 := Nat.mul_left_cancel hk_pos h
        have h1 : uv₁.1 = uv₂.1 := by
          have hmod := congrArg (· % d) heq
          simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt huv₁.1,
            Nat.mod_eq_of_lt huv₂.1] using hmod
        have h2 : uv₁.2 = uv₂.2 := by
          have hdiv := congrArg (· / d) heq
          simpa [Nat.add_mul_div_left _ _ hd_pos, Nat.div_eq_of_lt huv₁.1,
            Nat.div_eq_of_lt huv₂.1] using hdiv
        exact Prod.ext h1 h2
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        obtain ⟨y, rfl⟩ := hx.2
        have hy_lt : y < d * m := by
          rw [hq_kdm] at hx
          exact Nat.lt_of_mul_lt_mul_left hx.1
        refine ⟨(y % d, y / d), ?_, ?_⟩
        · simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨Nat.mod_lt y hd_pos, Nat.div_lt_of_lt_mul (mul_comm d m ▸ hy_lt)⟩
        · dsimp only
          rw [Nat.mod_add_div]
      · intro _ _; rfl
    rw [hbij, Finset.sum_product]
    have hterm (u v : ℕ) :
        χs (k * (u + d * v) : ℕ) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) *
              ((k * (u + d * v) : ℕ) : ℂ) / (q : ℂ)) =
          χs (k : ZMod d) * (χs (u : ZMod d) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / ((d * m : ℕ) : ℂ))) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (v : ℂ) / (m : ℂ)) := by
      have hchar : χs (k * (u + d * v) : ℕ) = χs (k : ZMod d) * χs (u : ZMod d) := by
        push_cast
        rw [map_mul, ZMod.natCast_self, zero_mul, add_zero]
      have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
      have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
      have hqC : (q : ℂ) = (k : ℂ) * (d : ℂ) * (m : ℂ) := by exact_mod_cast hq_kdm.trans (by ring)
      have hexp : 2 * Real.pi * Complex.I * (a : ℂ) * ((k * (u + d * v) : ℕ) : ℂ) / (q : ℂ) =
          2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / ((d * m : ℕ) : ℂ) +
            2 * Real.pi * Complex.I * (a : ℂ) * (v : ℂ) / (m : ℂ) := by
        rw [hqC]
        push_cast
        field_simp [hkC, hdC, hmC]
      rw [hchar, hexp, Complex.exp_add]
      ring
    simp_rw [hterm]
    calc
      ∑ u ∈ Finset.range d, ∑ v ∈ Finset.range m,
          χs (k : ZMod d) * (χs (u : ZMod d) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / ((d * m : ℕ) : ℂ))) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (v : ℂ) / (m : ℂ))
          = (∑ u ∈ Finset.range d,
              χs (k : ZMod d) * (χs (u : ZMod d) *
                Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / ((d * m : ℕ) : ℂ)))) *
              (∑ v ∈ Finset.range m,
                Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (v : ℂ) / (m : ℂ))) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun u _ ↦ ?_
            exact (Finset.mul_sum _ _ _).symm
      _ = (∑ u ∈ Finset.range d,
              χs (k : ZMod d) * (χs (u : ZMod d) *
                Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / ((d * m : ℕ) : ℂ)))) *
              (if (m : ℤ) ∣ a then (m : ℂ) else 0) := by
            rw [sum_range_cexp_int_div hm_pos a]
      _ = if (m : ℤ) ∣ a then
            (m : ℂ) * χs (k : ZMod d) *
              star (χs ((a / (m : ℤ)) : ZMod d)) * gaussSum χs 1
          else 0 := by
            split_ifs with hdvd_a
            · have ha_div : (a : ℂ) = ((a / (m : ℤ) : ℤ) : ℂ) * (m : ℂ) := by
                have := Int.ediv_mul_cancel hdvd_a
                exact_mod_cast this.symm
              have hgauss : ∑ u ∈ Finset.range d,
                  χs (u : ZMod d) *
                    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / ((d * m : ℕ) : ℂ)) =
                  gaussSum χs ((a / (m : ℤ)) : ZMod d) := by
                rw [gaussSum_int_eq_sum_range]
                refine Finset.sum_congr rfl fun u _ ↦ ?_
                have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
                have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
                congr 2
                rw [ha_div]
                push_cast
                dsimp only [d]
                field_simp [hmC, hdC]
              rw [← Finset.mul_sum, hgauss,
                gaussSum_eq_star_mul_of_isPrimitive χ.primitiveCharacter_isPrimitive]
              ring
            · simp
  have hsub_inner :
      ∑ k ∈ r.divisors, (μ k : ℂ) *
          ∑ x ∈ (Finset.range q).filter (fun x ↦ k ∣ x),
            χs x * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x : ℂ) / (q : ℂ)) =
        ∑ k ∈ r.divisors, (μ k : ℂ) *
          if ((r / k : ℕ) : ℤ) ∣ a then
            ((r / k : ℕ) : ℂ) * χs (k : ZMod d) *
              star (χs ((a / ((r / k : ℕ) : ℤ)) : ZMod d)) * gaussSum χs 1
          else 0 :=
    Finset.sum_congr rfl fun k hk ↦ by rw [hinner k hk]
  rw [hsub_inner]
  have hsum_r : (∑ k ∈ r.divisors, (μ k : ℂ) *
        if ((r / k : ℕ) : ℤ) ∣ a then
          ((r / k : ℕ) : ℂ) * χs (k : ZMod d) *
            star (χs ((a / ((r / k : ℕ) : ℤ)) : ZMod d)) * gaussSum χs 1
        else 0) =
      (∑ ℓ ∈ r.divisors,
        if (ℓ : ℤ) ∣ a then
          (μ (r / ℓ) : ℂ) * (ℓ : ℂ) * χs (r / ℓ : ℕ) *
            star (χs ((a / (ℓ : ℤ)) : ZMod d)) * gaussSum χs 1
        else 0) := by
    refine Finset.sum_bij (fun k _ ↦ r / k) ?_ ?_ ?_ ?_
    · intro k hk
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hk), hr_pos.ne'⟩
    · intro k₁ hk₁ k₂ hk₂ h
      have h1 := Nat.div_div_self (Nat.dvd_of_mem_divisors hk₁) hr_pos.ne'
      have h2 := Nat.div_div_self (Nat.dvd_of_mem_divisors hk₂) hr_pos.ne'
      rw [← h1, ← h2, h]
    · intro ℓ hℓ
      refine ⟨r / ℓ, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hℓ), hr_pos.ne'⟩,
        Nat.div_div_self (Nat.dvd_of_mem_divisors hℓ) hr_pos.ne'⟩
    · intro k hk
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hk) hr_pos.ne']
      split_ifs <;> ring
  rw [hsum_r]
  have hfilter : (∑ ℓ ∈ r.divisors,
        if (ℓ : ℤ) ∣ a then
          (μ (r / ℓ) : ℂ) * (ℓ : ℂ) * χs (r / ℓ : ℕ) *
            star (χs ((a / (ℓ : ℤ)) : ZMod d)) * gaussSum χs 1
        else 0) =
      (∑ ℓ ∈ (Nat.gcd a.natAbs r).divisors,
        (μ (r / ℓ) : ℂ) * (ℓ : ℂ) * χs (r / ℓ : ℕ) *
          star (χs ((a / (ℓ : ℤ)) : ZMod d))) * gaussSum χs 1 := by
    rw [← Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
    ext ℓ
    simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Nat.dvd_gcd_iff, hr_pos.ne',
      not_false_eq_true, and_true]
    have hgcd_ne : Nat.gcd a.natAbs r ≠ 0 := by
      intro h
      exact hr_pos.ne' (Nat.gcd_eq_zero_iff.mp h).2
    simp only [hgcd_ne, not_false_eq_true, and_true]
    constructor
    · rintro ⟨hℓr, hℓa⟩
      exact ⟨Int.natCast_dvd.mp hℓa, hℓr⟩
    · rintro ⟨hℓa, hℓr⟩
      exact ⟨hℓr, Int.natCast_dvd.mpr hℓa⟩
  exact hfilter

/-- **Imprimitive Gauss sum reduction at `a = 1`**:
`gaussSum χ 1 = μ(q / d) * χ*(q / d) * gaussSum χ* 1`, where `d = χ.conductor` and
`χ* = χ.primitiveCharacter`. -/
theorem gaussSum_one_eq_moebius_mul_primitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    gaussSum χ 1 =
      (μ (q / χ.conductor) : ℂ) * χ.primitiveCharacter (q / χ.conductor : ℕ) *
        gaussSum χ.primitiveCharacter 1 := by
  intro _
  have h := gaussSum_eq_sum_divisors_primitive χ 1
  dsimp only at h
  have hgcd : Nat.gcd (1 : ℤ).natAbs (q / χ.conductor) = 1 := by simp
  rw [Int.cast_one] at h
  rw [h, hgcd, Nat.divisors_one, Finset.sum_singleton]
  simp

/-- **Ramanujan sum formula** for the principal character `χ = 1`:
`gaussSum 1 a = ∑ ℓ ∈ (Nat.gcd a.natAbs q).divisors, μ (q / ℓ) * ℓ`. -/
theorem gaussSum_principal_eq_ramanujan {q : ℕ} [NeZero q] (a : ℤ) :
    gaussSum (1 : DirichletCharacter ℂ q) (a : ZMod q) =
      ∑ ℓ ∈ (Nat.gcd a.natAbs q).divisors, (μ (q / ℓ) : ℂ) * (ℓ : ℂ) := by
  have h := gaussSum_eq_sum_divisors_primitive (1 : DirichletCharacter ℂ q) a
  have hcond : (1 : DirichletCharacter ℂ q).conductor = 1 := DirichletCharacter.conductor_one
  have hprim : (1 : DirichletCharacter ℂ q).primitiveCharacter = 1 :=
    DirichletCharacter.primitiveCharacter_one
  dsimp only at h
  have : NeZero (1 : DirichletCharacter ℂ q).conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
  have : Subsingleton (ZMod (1 : DirichletCharacter ℂ q).conductor) :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [ZMod.card, hcond])
  have h1 : ∀ z : ZMod (1 : DirichletCharacter ℂ q).conductor,
      (1 : DirichletCharacter ℂ q).primitiveCharacter z = 1 := by
    intro z
    rw [hprim, MulChar.one_apply (isUnit_of_subsingleton z)]
  have hg1 : gaussSum (1 : DirichletCharacter ℂ q).primitiveCharacter 1 = 1 := by
    rw [gaussSum_eq_sum_zmod, Fintype.sum_subsingleton _ 0, h1 0]
    simp
  rw [hg1, mul_one] at h
  simp_rw [h1, star_one, mul_one] at h
  rw [h, hcond, Nat.div_one]

/-- At `a = 1`, the Gauss sum of the principal character modulo `q` equals `μ(q)`. -/
theorem gaussSum_principal_one (q : ℕ) [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) 1 = (μ q : ℂ) := by
  simpa using gaussSum_principal_eq_ramanujan (q := q) 1

/-- If `¬ Squarefree (q / χ.conductor)`, then `gaussSum χ 1 = 0`. -/
theorem gaussSum_one_eq_zero_of_not_squarefree {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (h : ¬ Squarefree (q / χ.conductor)) :
    gaussSum χ 1 = 0 := by
  rw [gaussSum_one_eq_moebius_mul_primitive, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  simp

/-- If `¬ Nat.Coprime (q / χ.conductor) χ.conductor`, then `gaussSum χ 1 = 0`. -/
theorem gaussSum_one_eq_zero_of_not_coprime {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (h : ¬ Nat.Coprime (q / χ.conductor) χ.conductor) :
    gaussSum χ 1 = 0 := by
  rw [gaussSum_one_eq_moebius_mul_primitive]
  have hz : χ.primitiveCharacter (q / χ.conductor : ℕ) = 0 := by
    rw [MulChar.apply_eq_zero_iff, ZMod.isUnit_iff_coprime]
    exact h
  rw [hz, mul_zero, zero_mul]

/-- Exact modulus of `gaussSum χ 1` for an arbitrary character `χ` modulo `q`:
equals `√(χ.conductor)` if `Squarefree (q / χ.conductor)` and `Nat.Coprime (q / χ.conductor) χ.conductor`,
and `0` otherwise. -/
theorem norm_gaussSum_one_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ 1‖ =
      if Squarefree (q / χ.conductor) ∧ Nat.Coprime (q / χ.conductor) χ.conductor then
        Real.sqrt χ.conductor
      else 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  split_ifs with h
  · rw [gaussSum_one_eq_moebius_mul_primitive, norm_mul, norm_mul,
      norm_gaussSum_one_of_isPrimitive χ.primitiveCharacter_isPrimitive]
    have hmu : ‖(μ (q / χ.conductor) : ℂ)‖ = 1 := by
      have h1 : |μ (q / χ.conductor)| = 1 :=
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree h.1
      have h1C : ((|μ (q / χ.conductor)| : ℤ) : ℝ) = 1 := by exact_mod_cast h1
      simpa [Complex.norm_intCast] using h1C
    have hunit : IsUnit ((q / χ.conductor : ℕ) : ZMod χ.conductor) :=
      (ZMod.isUnit_iff_coprime _ _).mpr h.2
    have hχ : ‖χ.primitiveCharacter (q / χ.conductor : ℕ)‖ = 1 := by
      simpa using χ.primitiveCharacter.unit_norm_eq_one hunit.unit
    rw [hmu, hχ, one_mul, one_mul]
  · rw [not_and_or] at h
    rcases h with hns | hnc
    · rw [gaussSum_one_eq_zero_of_not_squarefree χ hns, norm_zero]
    · rw [gaussSum_one_eq_zero_of_not_coprime χ hnc, norm_zero]

/-- Universal upper bound `‖gaussSum χ 1‖ ≤ √q` for every Dirichlet character `χ` modulo `q`. -/
theorem norm_gaussSum_one_le_sqrt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ 1‖ ≤ Real.sqrt q := by
  rw [norm_gaussSum_one_eq]
  split_ifs
  · exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level))
  · exact Real.sqrt_nonneg q

end ImprimitiveReduction

end AnalyticNumberTheory.DirichletLFunctions
