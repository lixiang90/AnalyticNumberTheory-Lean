import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# The Hardy–Littlewood–Vinogradov Circle Method

This file develops the foundational analytical and Diophantine framework of the
Hardy–Littlewood–Ramanujan–Vinogradov circle method:

- The additive character `e(α) = exp(2πi α)` on `ℝ`, its algebraic properties, periodicity,
  modulus `‖e α‖ = 1`, bridge to `AddCircle.fourier`, period-1 shift invariance of integrals,
  and orthogonality `∫ α in (0 : ℝ)..1, e (α * m) = if m = 0 then 1 else 0`.
- General finite exponential sums `expSum` and `genExpSum`, exact `s`-fold representation-count
  integral identities over `[0, 1]` and shifted unit intervals `[x, x + 1]` (including binary,
  ternary, and power-sum specializations), and Parseval's identity.
- Dirichlet's rational approximation theorem for arbitrary real parameters `Q ≥ 1`.
- Formal major arcs `majorArc`, `majorArcs`, and minor arcs `minorArcs` forming a measurable
  partition of the shifted unit interval `[-(1 / Q), 1 - 1 / Q]` (as well as `[δ, 1 + δ]` and
  fixed-radius variants), complete proofs of pairwise disjointness via Farey gap bounds when
  `2 * P ≤ Q`, Lebesgue measure estimates, and the Dirichlet minor-arc characterization `P < q ≤ Q`.
- Integral decomposition `representationIntegral = majorArcIntegral + minorArcIntegral`, the
  major-arc sum decomposition `∑_{q ≤ P} ∑_{a coprime q} ∫_{majorArc q a}`, centered major-arc
  coordinate shifts, and general minor-arc bounds.
-/

noncomputable section

open Complex Finset MeasureTheory Set
open scoped Topology Classical

namespace AnalyticNumberTheory.AdditiveNumberTheory

section AdditiveCharacter

/-- The standard additive character `e(α) = exp(2πi α)` for `α : ℝ`. -/
def e (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * α * Complex.I)

/-- Unfolding lemma for `e`. -/
theorem e_def (α : ℝ) : e α = Complex.exp (2 * Real.pi * α * Complex.I) := rfl

/-- `e 0 = 1`. -/
@[simp]
theorem e_zero : e 0 = 1 := by
  simp [e]

/-- `e 1 = 1`. -/
@[simp]
theorem e_one : e 1 = 1 := by
  unfold e
  simpa [mul_comm, mul_assoc] using Complex.exp_two_pi_mul_I

/-- `e` vanishes nowhere. -/
theorem e_ne_zero (α : ℝ) : e α ≠ 0 :=
  Complex.exp_ne_zero _

/-- Additive-to-multiplicative law `e (α + β) = e α * e β`. -/
theorem e_add (α β : ℝ) : e (α + β) = e α * e β := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Negation law `e (-α) = (e α)⁻¹`. -/
theorem e_neg (α : ℝ) : e (-α) = (e α)⁻¹ := by
  unfold e
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- Subtraction law `e (α - β) = e α * e (-β)`. -/
theorem e_sub_eq_mul_neg (α β : ℝ) : e (α - β) = e α * e (-β) := by
  rw [sub_eq_add_neg, e_add]

/-- Division law `e (α - β) = e α / e β`. -/
theorem e_sub (α β : ℝ) : e (α - β) = e α / e β := by
  rw [e_sub_eq_mul_neg, e_neg, div_eq_mul_inv]

/-- Product of `e` over a finite set equals `e` of the sum. -/
theorem e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, e_add, ih]

/-- Natural-number power identity `(e α) ^ n = e (α * n)`. -/
theorem e_pow (α : ℝ) (n : ℕ) : e α ^ n = e (α * (n : ℝ)) := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Integer power identity `(e α) ^ m = e (α * m)`. -/
theorem e_zpow (α : ℝ) (m : ℤ) : e α ^ m = e (α * (m : ℝ)) := by
  unfold e
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- `e (m : ℝ) = 1` for every integer `m : ℤ`. -/
@[simp]
theorem e_intCast (m : ℤ) : e (m : ℝ) = 1 := by
  have h : e (1 * (m : ℝ)) = e 1 ^ m := (e_zpow 1 m).symm
  simpa using h

/-- `e (n : ℝ) = 1` for every natural number `n : ℕ`. -/
@[simp]
theorem e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  simpa using e_intCast (n : ℤ)

/-- Integer shift invariance `e (α + m) = e α` for `m : ℤ`. -/
@[simp]
theorem e_add_intCast (α : ℝ) (m : ℤ) : e (α + m) = e α := by
  rw [e_add, e_intCast, mul_one]

/-- Natural-number shift invariance `e (α + n) = e α` for `n : ℕ`. -/
@[simp]
theorem e_add_natCast (α : ℝ) (n : ℕ) : e (α + n) = e α := by
  rw [e_add, e_natCast, mul_one]

/-- `e` is 1-periodic on `ℝ`. -/
theorem e_periodic : Function.Periodic e 1 := by
  intro α
  simpa using e_add_intCast α 1

/-- `α ↦ e (α * m)` is 1-periodic for every `m : ℤ`. -/
theorem e_periodic_mul_int (m : ℤ) : Function.Periodic (fun α : ℝ => e (α * (m : ℝ))) 1 := by
  intro α
  dsimp only
  have h : (α + 1) * (m : ℝ) = α * (m : ℝ) + (m : ℤ) := by ring
  rw [h, e_add_intCast]

/-- `α ↦ e (α * n)` is 1-periodic for every `n : ℕ`. -/
theorem e_periodic_mul_nat (n : ℕ) : Function.Periodic (fun α : ℝ => e (α * (n : ℝ))) 1 := by
  simpa using e_periodic_mul_int (n : ℤ)

/-- Complex conjugation of `e α` equals `e (-α)`. -/
@[simp]
theorem star_e (α : ℝ) : star (e α) = e (-α) := by
  unfold e
  change starRingEnd ℂ (Complex.exp (2 * Real.pi * α * Complex.I)) =
    Complex.exp (2 * Real.pi * (-α : ℝ) * Complex.I)
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- Modulus identity `‖e α‖ = 1` for every `α : ℝ`. -/
@[simp]
theorem norm_e (α : ℝ) : ‖e α‖ = 1 := by
  unfold e
  have harg : (2 * Real.pi * (α : ℂ) * Complex.I) = ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * α)

/-- `e` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_e : Continuous e := by
  unfold e
  fun_prop

/-- `e` is measurable on `ℝ`. -/
@[fun_prop]
theorem measurable_e : Measurable e :=
  continuous_e.measurable

/-- Bridge between `e (α * m)` and Mathlib's `fourier` on `UnitAddCircle`. -/
theorem e_eq_fourier (m : ℤ) (α : ℝ) :
    e (α * (m : ℝ)) = fourier (T := 1) m (α : UnitAddCircle) := by
  rw [fourier_coe_apply]
  unfold e
  congr 1
  push_cast
  ring

end AdditiveCharacter

section PeriodicityAndOrthogonality

/-- Period-1 shift invariance of interval integrals:
`∫ α in x..(x + 1), f α = ∫ α in (0 : ℝ)..1, f α`. -/
theorem intervalIntegral_periodic_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Function.Periodic f 1) (x : ℝ) :
    ∫ α in x..(x + 1), f α = ∫ α in (0 : ℝ)..1, f α := by
  simpa using hf.intervalIntegral_add_eq x 0

/-- Period-1 invariance of interval integrals between any two starting points `x` and `y`. -/
theorem intervalIntegral_periodic_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Function.Periodic f 1) (x y : ℝ) :
    ∫ α in x..(x + 1), f α = ∫ α in y..(y + 1), f α :=
  hf.intervalIntegral_add_eq x y

/-- Period-1 shift invariance as a set integral over `Set.Ioc x (x + 1)`. -/
theorem setIntegral_Ioc_periodic_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Function.Periodic f 1) (x : ℝ) :
    ∫ α in Set.Ioc x (x + 1), f α = ∫ α in (0 : ℝ)..1, f α := by
  rw [← intervalIntegral.integral_of_le (by linarith : x ≤ x + 1)]
  exact intervalIntegral_periodic_add hf x

/-- Period-1 shift invariance as a set integral over `Set.Icc x (x + 1)`. -/
theorem setIntegral_Icc_periodic_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Function.Periodic f 1) (x : ℝ) :
    ∫ α in Set.Icc x (x + 1), f α = ∫ α in (0 : ℝ)..1, f α := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact setIntegral_Ioc_periodic_eq hf x

/-- **Orthogonality of the additive character**:
for every `m : ℤ`, `∫ α in (0 : ℝ)..1, e (α * m) = if m = 0 then 1 else 0`. -/
theorem intervalIntegral_e_mul_int (m : ℤ) :
    ∫ α in (0 : ℝ)..1, e (α * (m : ℝ)) = if m = 0 then (1 : ℂ) else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    let c : ℂ := 2 * Real.pi * (m : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          (Int.cast_ne_zero.mpr hm))
        Complex.I_ne_zero
    let F : ℝ → ℂ := fun α => e (α * (m : ℝ)) / c
    have he_eq : ∀ α : ℝ, e (α * (m : ℝ)) = Complex.exp (c * (α : ℂ)) := by
      intro α
      unfold e
      congr 1
      dsimp [c]
      push_cast
      ring
    have hderiv : ∀ α ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (e (α * (m : ℝ))) α := by
      intro α _
      have hlin : HasDerivAt (fun t : ℝ => c * (t : ℂ)) (c * 1) α :=
        ((hasDerivAt_id α).ofReal_comp).const_mul c
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
          (Complex.exp (c * (α : ℂ)) * (c * 1)) α := hlin.cexp
      have hF : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c)
          (Complex.exp (c * (α : ℂ)) * (c * 1) / c) α := hexp.div_const c
      have hF_eq : (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c) = F := by
        ext t
        simp [F, he_eq t]
      rw [hF_eq] at hF
      convert hF using 1
      rw [he_eq α, mul_one, mul_div_cancel_right₀ _ hc]
    have hint : IntervalIntegrable (fun α : ℝ => e (α * (m : ℝ))) volume 0 1 :=
      (continuous_e.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp [F]

/-- Shifted orthogonality integral on any interval `[x, x + 1]` for `m : ℤ`. -/
theorem intervalIntegral_e_mul_int_shift (m : ℤ) (x : ℝ) :
    ∫ α in x..(x + 1), e (α * (m : ℝ)) = if m = 0 then (1 : ℂ) else 0 := by
  rw [intervalIntegral_periodic_add (e_periodic_mul_int m) x]
  exact intervalIntegral_e_mul_int m

/-- Orthogonality integral on `Set.Icc x (x + 1)` for `m : ℤ`. -/
theorem setIntegral_Icc_e_mul_int (m : ℤ) (x : ℝ) :
    ∫ α in Set.Icc x (x + 1), e (α * (m : ℝ)) = if m = 0 then (1 : ℂ) else 0 := by
  rw [setIntegral_Icc_periodic_eq (e_periodic_mul_int m) x]
  exact intervalIntegral_e_mul_int m

/-- Two-character orthogonality for integers `m, n : ℤ` over `[x, x + 1]`. -/
theorem intervalIntegral_e_mul_sub_int_shift (m n : ℤ) (x : ℝ) :
    ∫ α in x..(x + 1), e (α * (m : ℝ)) * e (-α * (n : ℝ)) =
      if m = n then (1 : ℂ) else 0 := by
  have hfun : (fun α : ℝ => e (α * (m : ℝ)) * e (-α * (n : ℝ))) =
      fun α : ℝ => e (α * ((m - n : ℤ) : ℝ)) := by
    ext α
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [hfun, intervalIntegral_e_mul_int_shift (m - n) x]
  simp [sub_eq_zero]

/-- Two-character orthogonality for integers `m, n : ℤ` over `[0, 1]`. -/
theorem intervalIntegral_e_mul_sub_int (m n : ℤ) :
    ∫ α in (0 : ℝ)..1, e (α * (m : ℝ)) * e (-α * (n : ℝ)) =
      if m = n then (1 : ℂ) else 0 := by
  simpa using intervalIntegral_e_mul_sub_int_shift m n 0

/-- Two-character orthogonality for natural numbers `m, n : ℕ` over `[x, x + 1]`. -/
theorem intervalIntegral_e_mul_nat_sub_shift (m n : ℕ) (x : ℝ) :
    ∫ α in x..(x + 1), e (α * (m : ℝ)) * e (-α * (n : ℝ)) =
      if m = n then (1 : ℂ) else 0 := by
  simpa [Int.cast_natCast, Int.cast_inj] using
    intervalIntegral_e_mul_sub_int_shift (m : ℤ) (n : ℤ) x

/-- Two-character orthogonality for natural numbers `m, n : ℕ` over `[0, 1]`. -/
theorem intervalIntegral_e_mul_nat_sub (m n : ℕ) :
    ∫ α in (0 : ℝ)..1, e (α * (m : ℝ)) * e (-α * (n : ℝ)) =
      if m = n then (1 : ℂ) else 0 := by
  simpa using intervalIntegral_e_mul_nat_sub_shift m n 0

end PeriodicityAndOrthogonality

section ExponentialSumsAndRepresentationCounts

/-- Finite `ℕ`-indexed exponential sum `∑ n ∈ A, w n * e (α * n)`. -/
def expSum (w : ℕ → ℂ) (A : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ A, w n * e (α * (n : ℝ))

/-- General finite exponential sum `∑ u ∈ B, w u * e (α * f u)` for integer phases `f : κ → ℤ`. -/
def genExpSum {κ : Type*} (w : κ → ℂ) (f : κ → ℤ) (B : Finset κ) (α : ℝ) : ℂ :=
  ∑ u ∈ B, w u * e (α * (f u : ℝ))

/-- `expSum` is a special case of `genExpSum`. -/
theorem expSum_eq_genExpSum (w : ℕ → ℂ) (A : Finset ℕ) (α : ℝ) :
    expSum w A α = genExpSum w (fun n : ℕ => (n : ℤ)) A α := by
  simp [expSum, genExpSum]

/-- `genExpSum` is continuous in `α`. -/
@[fun_prop]
theorem continuous_genExpSum {κ : Type*} (w : κ → ℂ) (f : κ → ℤ) (B : Finset κ) :
    Continuous (genExpSum w f B) := by
  unfold genExpSum
  refine continuous_finsetSum _ fun u _ => ?_
  exact continuous_const.mul (continuous_e.comp (continuous_id.mul continuous_const))

/-- `expSum` is continuous in `α`. -/
@[fun_prop]
theorem continuous_expSum (w : ℕ → ℂ) (A : Finset ℕ) : Continuous (expSum w A) := by
  rw [funext (expSum_eq_genExpSum w A)]
  exact continuous_genExpSum _ _ _

/-- `genExpSum` is 1-periodic in `α`. -/
theorem periodic_genExpSum {κ : Type*} (w : κ → ℂ) (f : κ → ℤ) (B : Finset κ) :
    Function.Periodic (genExpSum w f B) 1 := by
  intro α
  unfold genExpSum
  refine Finset.sum_congr rfl fun u _ => ?_
  have h := e_periodic_mul_int (f u) α
  dsimp only at h
  rw [h]

/-- `expSum` is 1-periodic in `α`. -/
theorem periodic_expSum (w : ℕ → ℂ) (A : Finset ℕ) :
    Function.Periodic (expSum w A) 1 := by
  intro α
  simpa [expSum_eq_genExpSum] using periodic_genExpSum w (fun n : ℕ => (n : ℤ)) A α

/-- Triangle inequality bound for `genExpSum`. -/
theorem norm_genExpSum_le {κ : Type*} (w : κ → ℂ) (f : κ → ℤ) (B : Finset κ) (α : ℝ) :
    ‖genExpSum w f B α‖ ≤ ∑ u ∈ B, ‖w u‖ := by
  unfold genExpSum
  refine (norm_sum_le B _).trans_eq ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [norm_mul, norm_e, mul_one]

/-- Triangle inequality bound for `expSum`. -/
theorem norm_expSum_le (w : ℕ → ℂ) (A : Finset ℕ) (α : ℝ) :
    ‖expSum w A α‖ ≤ ∑ n ∈ A, ‖w n‖ := by
  rw [expSum_eq_genExpSum]
  exact norm_genExpSum_le w (fun n : ℕ => (n : ℤ)) A α

/-- Conjugate formula for `genExpSum`. -/
theorem star_genExpSum {κ : Type*} (w : κ → ℂ) (f : κ → ℤ) (B : Finset κ) (α : ℝ) :
    star (genExpSum w f B α) = ∑ u ∈ B, star (w u) * e (-α * (f u : ℝ)) := by
  unfold genExpSum
  rw [star_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [star_mul', star_e]
  congr 2
  ring

/-- Conjugate formula for `expSum`. -/
theorem star_expSum (w : ℕ → ℂ) (A : Finset ℕ) (α : ℝ) :
    star (expSum w A α) = ∑ n ∈ A, star (w n) * e (-α * (n : ℝ)) := by
  simpa [expSum_eq_genExpSum] using star_genExpSum w (fun n : ℕ => (n : ℤ)) A α

/-- General `s`-fold weighted representation count for integer phase functions `f i`. -/
def repCountGen {κ : Type*} (s : ℕ) (w : Fin s → κ → ℂ) (f : Fin s → κ → ℤ)
    (B : Fin s → Finset κ) (N : ℤ) : ℂ :=
  ∑ u ∈ (Fintype.piFinset B).filter (fun u => ∑ i : Fin s, f i (u i) = N),
    ∏ i : Fin s, w i (u i)

/-- `s`-fold weighted representation count on `Finset ℕ` domains `A i`. -/
def repCountFin (s : ℕ) (w : Fin s → ℕ → ℂ) (A : Fin s → Finset ℕ) (N : ℕ) : ℂ :=
  ∑ n ∈ (Fintype.piFinset A).filter (fun n => ∑ i : Fin s, n i = N),
    ∏ i : Fin s, w i (n i)

/-- Full `s`-fold weighted representation count `∑_{n₁ + ... + n_s = N} ∏ w_i(n_i)`
over non-negative integers `n_i : ℕ`. -/
def repCount (s : ℕ) (w : Fin s → ℕ → ℂ) (N : ℕ) : ℂ :=
  repCountFin s w (fun _ => Finset.range (N + 1)) N

/-- Any `Fin s → ℕ` tuple with sum `N` has every coordinate `< N + 1`, so `repCountFin` agrees
with `repCount` whenever each `A i` contains `Finset.range (N + 1)`. -/
theorem repCountFin_eq_repCount_of_range_subset {s : ℕ} {w : Fin s → ℕ → ℂ}
    {A : Fin s → Finset ℕ} {N : ℕ} (hA : ∀ i : Fin s, Finset.range (N + 1) ⊆ A i) :
    repCountFin s w A N = repCount s w N := by
  unfold repCount repCountFin
  congr 1
  ext n
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨_, hsum⟩
    refine ⟨fun i => ?_, hsum⟩
    have hle : n i ≤ ∑ j : Fin s, n j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    omega
  · rintro ⟨hn, hsum⟩
    exact ⟨fun i => hA i (Finset.mem_range.mpr (hn i)), hsum⟩

/-- **General `s`-fold representation-count integral identity** over any shifted unit interval
`[x, x + 1]`:
`∫ α in x..(x + 1), (∏ i, genExpSum (w i) (f i) (B i) α) * e (-α * N) = repCountGen s w f B N`. -/
theorem integral_prod_genExpSum_mul_e_neg_shift {κ : Type*} (s : ℕ) (w : Fin s → κ → ℂ)
    (f : Fin s → κ → ℤ) (B : Fin s → Finset κ) (N : ℤ) (x : ℝ) :
    ∫ α in x..(x + 1), (∏ i : Fin s, genExpSum (w i) (f i) (B i) α) * e (-α * (N : ℝ)) =
      repCountGen s w f B N := by
  have hexpand : ∀ α : ℝ,
      (∏ i : Fin s, genExpSum (w i) (f i) (B i) α) * e (-α * (N : ℝ)) =
        ∑ u ∈ Fintype.piFinset B,
          (∏ i : Fin s, w i (u i)) * e (α * (((∑ i : Fin s, f i (u i)) - N : ℤ) : ℝ)) := by
    intro α
    unfold genExpSum
    rw [Finset.prod_univ_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
    congr 1
    have hprod_e :
        (∏ i : Fin s, e (α * (f i (u i) : ℝ))) =
          e (∑ i : Fin s, α * (f i (u i) : ℝ)) :=
      (e_sum Finset.univ fun i => α * (f i (u i) : ℝ)).symm
    rw [hprod_e, ← e_add]
    congr 1
    rw [← Finset.mul_sum]
    push_cast
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, intervalIntegral_e_mul_int_shift, sub_eq_zero,
      mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    rfl
  · intro u _
    exact (continuous_const.mul
      (continuous_e.comp (continuous_id.mul continuous_const))).intervalIntegrable x (x + 1)

/-- **General `s`-fold representation-count integral identity** over `[0, 1]`. -/
theorem integral_prod_genExpSum_mul_e_neg {κ : Type*} (s : ℕ) (w : Fin s → κ → ℂ)
    (f : Fin s → κ → ℤ) (B : Fin s → Finset κ) (N : ℤ) :
    ∫ α in (0 : ℝ)..1, (∏ i : Fin s, genExpSum (w i) (f i) (B i) α) * e (-α * (N : ℝ)) =
      repCountGen s w f B N := by
  simpa using integral_prod_genExpSum_mul_e_neg_shift s w f B N 0

/-- **Weighted `ℕ`-indexed representation-count integral identity** over `[x, x + 1]`:
`∫ α in x..(x + 1), (∏ i, expSum (w i) (A i) α) * e (-α * N) = repCountFin s w A N`. -/
theorem integral_prod_expSum_mul_e_neg_shift (s : ℕ) (w : Fin s → ℕ → ℂ)
    (A : Fin s → Finset ℕ) (N : ℕ) (x : ℝ) :
    ∫ α in x..(x + 1), (∏ i : Fin s, expSum (w i) (A i) α) * e (-α * (N : ℝ)) =
      repCountFin s w A N := by
  have h := integral_prod_genExpSum_mul_e_neg_shift s w (fun _ n => (n : ℤ)) A (N : ℤ) x
  have hexp : ∀ α : ℝ,
      (∏ i : Fin s, expSum (w i) (A i) α) * e (-α * (N : ℝ)) =
        (∏ i : Fin s, genExpSum (w i) (fun n => (n : ℤ)) (A i) α) *
          e (-α * ((N : ℤ) : ℝ)) := by
    intro α
    simp [expSum_eq_genExpSum]
  simp_rw [hexp, h]
  unfold repCountGen repCountFin
  congr 1
  ext n
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  exact and_congr_right fun _ => by exact_mod_cast Iff.rfl

/-- **Weighted `ℕ`-indexed representation-count integral identity** over `[0, 1]`:
`∫ α in (0 : ℝ)..1, (∏ i, expSum (w i) (A i) α) * e (-α * N) = repCountFin s w A N`. -/
theorem integral_prod_expSum_mul_e_neg (s : ℕ) (w : Fin s → ℕ → ℂ)
    (A : Fin s → Finset ℕ) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, (∏ i : Fin s, expSum (w i) (A i) α) * e (-α * (N : ℝ)) =
      repCountFin s w A N := by
  simpa using integral_prod_expSum_mul_e_neg_shift s w A N 0

/-- Full representation-count integral identity over `[0, 1]` using `A i = Finset.range (N + 1)`:
`∫ α in (0 : ℝ)..1, (∏ i, expSum (w i) (Finset.range (N + 1)) α) * e (-α * N) = repCount s w N`. -/
theorem integral_prod_expSum_range_mul_e_neg (s : ℕ) (w : Fin s → ℕ → ℂ) (N : ℕ) :
    ∫ α in (0 : ℝ)..1,
        (∏ i : Fin s, expSum (w i) (Finset.range (N + 1)) α) * e (-α * (N : ℝ)) =
      repCount s w N :=
  integral_prod_expSum_mul_e_neg s w (fun _ => Finset.range (N + 1)) N

/-- Uniform power specialization of the representation-count integral identity over `[x, x + 1]`. -/
theorem integral_expSum_pow_mul_e_neg_shift (s : ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (N : ℕ) (x : ℝ) :
    ∫ α in x..(x + 1), expSum w A α ^ s * e (-α * (N : ℝ)) =
      repCountFin s (fun _ => w) (fun _ => A) N := by
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    integral_prod_expSum_mul_e_neg_shift s (fun _ => w) (fun _ => A) N x

/-- Uniform power specialization of the representation-count integral identity over `[0, 1]`. -/
theorem integral_expSum_pow_mul_e_neg (s : ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, expSum w A α ^ s * e (-α * (N : ℝ)) =
      repCountFin s (fun _ => w) (fun _ => A) N := by
  simpa using integral_expSum_pow_mul_e_neg_shift s w A N 0

/-- Uniform power specialization for general integer-phase exponential sums over `[x, x + 1]`. -/
theorem integral_genExpSum_pow_mul_e_neg_shift {κ : Type*} (s : ℕ) (w : κ → ℂ) (f : κ → ℤ)
    (B : Finset κ) (N : ℤ) (x : ℝ) :
    ∫ α in x..(x + 1), genExpSum w f B α ^ s * e (-α * (N : ℝ)) =
      repCountGen s (fun _ => w) (fun _ => f) (fun _ => B) N := by
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    integral_prod_genExpSum_mul_e_neg_shift s (fun _ => w) (fun _ => f) (fun _ => B) N x

/-- Uniform power specialization for general integer-phase exponential sums over `[0, 1]`. -/
theorem integral_genExpSum_pow_mul_e_neg {κ : Type*} (s : ℕ) (w : κ → ℂ) (f : κ → ℤ)
    (B : Finset κ) (N : ℤ) :
    ∫ α in (0 : ℝ)..1, genExpSum w f B α ^ s * e (-α * (N : ℝ)) =
      repCountGen s (fun _ => w) (fun _ => f) (fun _ => B) N := by
  simpa using integral_genExpSum_pow_mul_e_neg_shift s w f B N 0

/-- Explicit binary (`s = 2`) representation-count integral identity over `[x, x + 1]`. -/
theorem integral_expSum_mul_expSum_mul_e_neg_shift (w₁ w₂ : ℕ → ℂ) (A₁ A₂ : Finset ℕ)
    (N : ℕ) (x : ℝ) :
    ∫ α in x..(x + 1), expSum w₁ A₁ α * expSum w₂ A₂ α * e (-α * (N : ℝ)) =
      ∑ n₁ ∈ A₁, ∑ n₂ ∈ A₂, if n₁ + n₂ = N then w₁ n₁ * w₂ n₂ else 0 := by
  have hexpand : ∀ α : ℝ,
      expSum w₁ A₁ α * expSum w₂ A₂ α * e (-α * (N : ℝ)) =
        ∑ n₁ ∈ A₁, ∑ n₂ ∈ A₂,
          (w₁ n₁ * w₂ n₂) * e (α * (((n₁ + n₂ : ℕ) : ℤ) - (N : ℤ) : ℝ)) := by
    intro α
    unfold expSum
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n₂ _ => ?_
    have hmul : w₁ n₁ * e (α * (n₁ : ℝ)) * (w₂ n₂ * e (α * (n₂ : ℝ))) * e (-α * (N : ℝ)) =
        (w₁ n₁ * w₂ n₂) * (e (α * (n₁ : ℝ)) * e (α * (n₂ : ℝ)) * e (-α * (N : ℝ))) := by ring
    rw [hmul, ← e_add, ← e_add]
    congr 2
    push_cast
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n₁ _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n₂ _ => ?_
      rw [intervalIntegral.integral_const_mul]
      have hcast : (((n₁ + n₂ : ℕ) : ℤ) - (N : ℤ) : ℝ) =
          ((((n₁ + n₂ : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) := by push_cast; rfl
      rw [hcast, intervalIntegral_e_mul_int_shift]
      simp only [mul_ite, mul_one, mul_zero]
      split_ifs with h1 h2 <;> first | rfl | omega
    · intro n₂ _
      exact (continuous_const.mul
        (continuous_e.comp (continuous_id.mul continuous_const))).intervalIntegrable x (x + 1)
  · intro n₁ _
    refine (continuous_finsetSum A₂ fun n₂ _ => continuous_const.mul
      (continuous_e.comp (continuous_id.mul continuous_const))).intervalIntegrable x (x + 1)

/-- Explicit binary (`s = 2`) representation-count integral identity over `[0, 1]`. -/
theorem integral_expSum_mul_expSum_mul_e_neg (w₁ w₂ : ℕ → ℂ) (A₁ A₂ : Finset ℕ) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, expSum w₁ A₁ α * expSum w₂ A₂ α * e (-α * (N : ℝ)) =
      ∑ n₁ ∈ A₁, ∑ n₂ ∈ A₂, if n₁ + n₂ = N then w₁ n₁ * w₂ n₂ else 0 := by
  simpa using integral_expSum_mul_expSum_mul_e_neg_shift w₁ w₂ A₁ A₂ N 0

/-- Explicit ternary (`s = 3`) representation-count integral identity over `[x, x + 1]`. -/
theorem integral_expSum_mul_three_mul_e_neg_shift (w₁ w₂ w₃ : ℕ → ℂ) (A₁ A₂ A₃ : Finset ℕ)
    (N : ℕ) (x : ℝ) :
    ∫ α in x..(x + 1),
        expSum w₁ A₁ α * expSum w₂ A₂ α * expSum w₃ A₃ α * e (-α * (N : ℝ)) =
      ∑ n₁ ∈ A₁, ∑ n₂ ∈ A₂, ∑ n₃ ∈ A₃,
        if n₁ + n₂ + n₃ = N then w₁ n₁ * w₂ n₂ * w₃ n₃ else 0 := by
  have hexpand : ∀ α : ℝ,
      expSum w₁ A₁ α * expSum w₂ A₂ α * expSum w₃ A₃ α * e (-α * (N : ℝ)) =
        ∑ n₁ ∈ A₁, ∑ n₂ ∈ A₂, ∑ n₃ ∈ A₃,
          (w₁ n₁ * w₂ n₂ * w₃ n₃) * e (α * (((n₁ + n₂ + n₃ : ℕ) : ℤ) - (N : ℤ) : ℝ)) := by
    intro α
    unfold expSum
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n₁ _ => ?_
    have hmul₁ :
        w₁ n₁ * e (α * (n₁ : ℝ)) * (∑ n₂ ∈ A₂, w₂ n₂ * e (α * (n₂ : ℝ))) =
          ∑ n₂ ∈ A₂, w₁ n₁ * e (α * (n₁ : ℝ)) * (w₂ n₂ * e (α * (n₂ : ℝ))) :=
      Finset.mul_sum _ _ _
    rw [hmul₁, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n₂ _ => ?_
    have hmul₂ :
        w₁ n₁ * e (α * (n₁ : ℝ)) * (w₂ n₂ * e (α * (n₂ : ℝ))) *
            (∑ n₃ ∈ A₃, w₃ n₃ * e (α * (n₃ : ℝ))) =
          ∑ n₃ ∈ A₃,
            w₁ n₁ * e (α * (n₁ : ℝ)) * (w₂ n₂ * e (α * (n₂ : ℝ))) *
              (w₃ n₃ * e (α * (n₃ : ℝ))) :=
      Finset.mul_sum _ _ _
    rw [hmul₂, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n₃ _ => ?_
    have hmul : w₁ n₁ * e (α * (n₁ : ℝ)) * (w₂ n₂ * e (α * (n₂ : ℝ))) *
          (w₃ n₃ * e (α * (n₃ : ℝ))) * e (-α * (N : ℝ)) =
        (w₁ n₁ * w₂ n₂ * w₃ n₃) *
          (e (α * (n₁ : ℝ)) * e (α * (n₂ : ℝ)) * e (α * (n₃ : ℝ)) * e (-α * (N : ℝ))) := by ring
    rw [hmul, ← e_add, ← e_add, ← e_add]
    congr 2
    push_cast
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n₁ _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n₂ _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun n₃ _ => ?_
        rw [intervalIntegral.integral_const_mul]
        have hcast : (((n₁ + n₂ + n₃ : ℕ) : ℤ) - (N : ℤ) : ℝ) =
            ((((n₁ + n₂ + n₃ : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) := by push_cast; rfl
        rw [hcast, intervalIntegral_e_mul_int_shift]
        simp only [mul_ite, mul_one, mul_zero]
        split_ifs with h1 h2 <;> first | rfl | omega
      · intro n₃ _
        exact (continuous_const.mul
          (continuous_e.comp (continuous_id.mul continuous_const))).intervalIntegrable x (x + 1)
    · intro n₂ _
      refine (continuous_finsetSum A₃ fun n₃ _ => continuous_const.mul
        (continuous_e.comp (continuous_id.mul continuous_const))).intervalIntegrable x (x + 1)
  · intro n₁ _
    refine (continuous_finsetSum A₂ fun n₂ _ => continuous_finsetSum A₃ fun n₃ _ =>
      continuous_const.mul
        (continuous_e.comp (continuous_id.mul continuous_const))).intervalIntegrable x (x + 1)

/-- Explicit ternary (`s = 3`) representation-count integral identity over `[0, 1]`. -/
theorem integral_expSum_mul_three_mul_e_neg (w₁ w₂ w₃ : ℕ → ℂ) (A₁ A₂ A₃ : Finset ℕ) (N : ℕ) :
    ∫ α in (0 : ℝ)..1,
        expSum w₁ A₁ α * expSum w₂ A₂ α * expSum w₃ A₃ α * e (-α * (N : ℝ)) =
      ∑ n₁ ∈ A₁, ∑ n₂ ∈ A₂, ∑ n₃ ∈ A₃,
        if n₁ + n₂ + n₃ = N then w₁ n₁ * w₂ n₂ * w₃ n₃ else 0 := by
  simpa using integral_expSum_mul_three_mul_e_neg_shift w₁ w₂ w₃ A₁ A₂ A₃ N 0

/-- Uniform ternary cube specialization `∫ S(α)^3 e(-α N) dα` over `[0, 1]`. -/
theorem integral_expSum_pow_three_mul_e_neg (w : ℕ → ℂ) (A : Finset ℕ) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, expSum w A α ^ 3 * e (-α * (N : ℝ)) =
      ∑ n₁ ∈ A, ∑ n₂ ∈ A, ∑ n₃ ∈ A,
        if n₁ + n₂ + n₃ = N then w n₁ * w n₂ * w n₃ else 0 := by
  have hpow : ∀ α : ℝ, expSum w A α ^ 3 = expSum w A α * expSum w A α * expSum w A α := by
    intro α; ring
  simp_rw [hpow]
  exact integral_expSum_mul_three_mul_e_neg w w w A A A N

/-- **Parseval's identity** for finite exponential sums on `[x, x + 1]`:
`∫ α in x..(x + 1), ‖expSum w A α‖ ^ 2 = ∑ n ∈ A, ‖w n‖ ^ 2`. -/
theorem integral_norm_sq_expSum_shift (w : ℕ → ℂ) (A : Finset ℕ) (x : ℝ) :
    ∫ α in x..(x + 1), ‖expSum w A α‖ ^ 2 = ∑ n ∈ A, ‖w n‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hcont : Continuous (fun α : ℝ => ‖expSum w A α‖ ^ 2) :=
    (continuous_expSum w A).norm.pow 2
  have hint : IntervalIntegrable (fun α : ℝ => ‖expSum w A α‖ ^ 2) volume x (x + 1) :=
    hcont.intervalIntegrable x (x + 1)
  have hcast :
      ((∫ α in x..(x + 1), ‖expSum w A α‖ ^ 2 : ℝ) : ℂ) =
        ∫ α in x..(x + 1), ((‖expSum w A α‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.ofRealCLM.intervalIntegral_comp_comm hint).symm
  rw [hcast]
  have hnorm_sq : ∀ α : ℝ,
      ((‖expSum w A α‖ ^ 2 : ℝ) : ℂ) = expSum w A α * star (expSum w A α) := by
    intro α
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hnorm_sq]
  have hexpand : ∀ α : ℝ,
      expSum w A α * star (expSum w A α) =
        ∑ m ∈ A, ∑ n ∈ A, (w m * star (w n)) * (e (α * (m : ℝ)) * e (-α * (n : ℝ))) := by
    intro α
    rw [star_expSum, expSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · have hsum_rhs :
        (∑ m ∈ A, ∫ α in x..(x + 1), ∑ n ∈ A,
            (w m * star (w n)) * (e (α * (m : ℝ)) * e (-α * (n : ℝ)))) =
          ((∑ n ∈ A, ‖w n‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul, intervalIntegral_e_mul_nat_sub_shift,
          mul_ite, mul_one, mul_zero]
        simp only [Finset.sum_ite_eq, hm, ↓reduceIte]
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      · intro n _
        exact (continuous_const.mul ((continuous_e.comp (continuous_id.mul continuous_const)).mul
          (continuous_e.comp ((continuous_neg.comp continuous_id).mul
            continuous_const)))).intervalIntegrable x (x + 1)
    exact hsum_rhs
  · intro m _
    refine (continuous_finsetSum A fun n _ => continuous_const.mul
      ((continuous_e.comp (continuous_id.mul continuous_const)).mul
        (continuous_e.comp ((continuous_neg.comp continuous_id).mul
          continuous_const)))).intervalIntegrable x (x + 1)

/-- **Parseval's identity** for finite exponential sums on `[0, 1]`. -/
theorem integral_norm_sq_expSum (w : ℕ → ℂ) (A : Finset ℕ) :
    ∫ α in (0 : ℝ)..1, ‖expSum w A α‖ ^ 2 = ∑ n ∈ A, ‖w n‖ ^ 2 := by
  simpa using integral_norm_sq_expSum_shift w A 0

end ExponentialSumsAndRepresentationCounts

section DirichletApproximation

/-- **Dirichlet's rational approximation theorem** (strict inequality form):
for every `α : ℝ` and real `Q ≥ 1`, there exist `a : ℤ` and `q : ℕ` with `1 ≤ q ≤ Q`,
`Nat.Coprime a.natAbs q`, and `|α - a / q| < 1 / (q * Q)`. -/
theorem dirichlet_rational_approx_lt (α : ℝ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (q : ℕ),
      1 ≤ q ∧ (q : ℝ) ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * Q) := by
  have hn_pos : 0 < ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  obtain ⟨r, hr_le, hr_den⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn_pos
  refine ⟨r.num, r.den, r.pos, ?_, r.reduced, ?_⟩
  · exact (Nat.cast_le.mpr hr_den).trans (Nat.floor_le (zero_le_one.trans hQ))
  · have hq_pos : (0 : ℝ) < (r.den : ℝ) := Nat.cast_pos.mpr r.pos
    have hQ_pos : 0 < Q := zero_lt_one.trans_le hQ
    have hQ_lt : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Q
    have hden_lt : (r.den : ℝ) * Q < ((⌊Q⌋₊ : ℝ) + 1) * (r.den : ℝ) := by
      nlinarith
    have hinv_lt : 1 / (((⌊Q⌋₊ : ℝ) + 1) * (r.den : ℝ)) < 1 / ((r.den : ℝ) * Q) :=
      one_div_lt_one_div_of_lt (mul_pos hq_pos hQ_pos) hden_lt
    rw [Rat.cast_def] at hr_le
    exact hr_le.trans_lt hinv_lt

/-- **Dirichlet's rational approximation theorem**:
for every `α : ℝ` and real `Q ≥ 1`, there exist `a : ℤ` and `q : ℕ` with `1 ≤ q ≤ Q`,
`Nat.Coprime a.natAbs q`, and `|α - a / q| ≤ 1 / (q * Q)`. -/
theorem dirichlet_rational_approx (α : ℝ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (q : ℕ),
      1 ≤ q ∧ (q : ℝ) ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * Q) := by
  obtain ⟨a, q, hq1, hqQ, hcop, hlt⟩ := dirichlet_rational_approx_lt α hQ
  exact ⟨a, q, hq1, hqQ, hcop, hlt.le⟩

/-- Natural-number parameter version of Dirichlet's rational approximation theorem. -/
theorem dirichlet_rational_approx_nat (α : ℝ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (q : ℕ),
      1 ≤ q ∧ q ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (Q : ℝ)) := by
  have hQ_real : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  obtain ⟨a, q, hq1, hqQ, hcop, hle⟩ := dirichlet_rational_approx α hQ_real
  exact ⟨a, q, hq1, by exact_mod_cast hqQ, hcop, hle⟩

end DirichletApproximation

section MajorAndMinorArcs

/-- Major arc `𝔐(q, a) = [a/q - 1/(q*Q), a/q + 1/(q*Q)]` centered at `a / q`. -/
def majorArc (q : ℕ) (a : ℤ) (Q : ℝ) : Set ℝ :=
  Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Q)) ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Q))

/-- Fixed-width major arc `[a/q - 1/Q, a/q + 1/Q]` centered at `a / q`. -/
def majorArcFixed (q : ℕ) (a : ℤ) (Q : ℝ) : Set ℝ :=
  Set.Icc ((a : ℝ) / (q : ℝ) - 1 / Q) ((a : ℝ) / (q : ℝ) + 1 / Q)

/-- Scaled major arc `majorArc q a (N / P)` of half-width `P / (q * N)`. -/
def majorArcScaled (q : ℕ) (a : ℤ) (P N : ℝ) : Set ℝ :=
  majorArc q a (N / P)

/-- Finite set of major-arc denominators `1 ≤ q ≤ P`. -/
def majorArcDenoms (P : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊P⌋₊

/-- Finite set of coprime numerators `0 ≤ a < q` with `Nat.Coprime a q`. -/
def coprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- The union of all major arcs `majorArc q a Q` for `1 ≤ q ≤ P`, `0 ≤ a < q`, `Nat.Coprime a q`. -/
def majorArcs (P Q : ℝ) : Set ℝ :=
  ⋃ q ∈ majorArcDenoms P, ⋃ a ∈ coprimeResidues q, majorArc q (a : ℤ) Q

/-- The minor arcs complementing `majorArcs P Q` inside the shifted unit interval
`[-(1 / Q), 1 - 1 / Q]`. -/
def minorArcs (P Q : ℝ) : Set ℝ :=
  Set.Icc (-(1 / Q)) (1 - 1 / Q) \ majorArcs P Q

/-- Fixed-width major arcs union for `1 ≤ q ≤ P`, `0 ≤ a < q`, `Nat.Coprime a q`. -/
def majorArcsFixed (P Q : ℝ) : Set ℝ :=
  ⋃ q ∈ majorArcDenoms P, ⋃ a ∈ coprimeResidues q, majorArcFixed q (a : ℤ) Q

/-- Fixed-width minor arcs inside `[-(1 / Q), 1 - 1 / Q]`. -/
def minorArcsFixed (P Q : ℝ) : Set ℝ :=
  Set.Icc (-(1 / Q)) (1 - 1 / Q) \ majorArcsFixed P Q

/-- Scaled major arcs `majorArcs P (N / P)` with half-width `P / (q * N)`. -/
def majorArcsScaled (P N : ℝ) : Set ℝ :=
  majorArcs P (N / P)

/-- Scaled minor arcs `minorArcs P (N / P)` inside `[-(P / N), 1 - P / N]`. -/
def minorArcsScaled (P N : ℝ) : Set ℝ :=
  minorArcs P (N / P)

/-- Characterization of membership in `majorArc q a Q`. -/
theorem mem_majorArc_iff {q : ℕ} {a : ℤ} {Q α : ℝ} :
    α ∈ majorArc q a Q ↔ |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * Q) := by
  simp only [majorArc, Set.mem_Icc, abs_sub_le_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Characterization of membership in `majorArcFixed q a Q`. -/
theorem mem_majorArcFixed_iff {q : ℕ} {a : ℤ} {Q α : ℝ} :
    α ∈ majorArcFixed q a Q ↔ |α - (a : ℝ) / (q : ℝ)| ≤ 1 / Q := by
  simp only [majorArcFixed, Set.mem_Icc, abs_sub_le_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Every `majorArc q a Q` is measurable. -/
theorem measurableSet_majorArc (q : ℕ) (a : ℤ) (Q : ℝ) :
    MeasurableSet (majorArc q a Q) :=
  measurableSet_Icc

/-- Every `majorArcFixed q a Q` is measurable. -/
theorem measurableSet_majorArcFixed (q : ℕ) (a : ℤ) (Q : ℝ) :
    MeasurableSet (majorArcFixed q a Q) :=
  measurableSet_Icc

/-- `majorArcs P Q` is measurable. -/
theorem measurableSet_majorArcs (P Q : ℝ) : MeasurableSet (majorArcs P Q) := by
  refine Finset.measurableSet_biUnion (majorArcDenoms P) fun q _ => ?_
  exact Finset.measurableSet_biUnion (coprimeResidues q) fun a _ => measurableSet_majorArc q a Q

/-- `minorArcs P Q` is measurable. -/
theorem measurableSet_minorArcs (P Q : ℝ) : MeasurableSet (minorArcs P Q) :=
  measurableSet_Icc.diff (measurableSet_majorArcs P Q)

/-- `majorArcsFixed P Q` is measurable. -/
theorem measurableSet_majorArcsFixed (P Q : ℝ) : MeasurableSet (majorArcsFixed P Q) := by
  refine Finset.measurableSet_biUnion (majorArcDenoms P) fun q _ => ?_
  exact Finset.measurableSet_biUnion (coprimeResidues q) fun a _ =>
    measurableSet_majorArcFixed q a Q

/-- `minorArcsFixed P Q` is measurable. -/
theorem measurableSet_minorArcsFixed (P Q : ℝ) : MeasurableSet (minorArcsFixed P Q) :=
  measurableSet_Icc.diff (measurableSet_majorArcsFixed P Q)

/-- **Farey gap lower bound**: any two distinct reduced fractions `a₁/q₁` and `a₂/q₂`
with `1 ≤ q₁, q₂` satisfy `|a₁/q₁ - a₂/q₂| ≥ 1 / (q₁ * q₂)`. -/
theorem farey_gap_of_ne {q₁ q₂ : ℕ} {a₁ a₂ : ℤ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (hcop₁ : Nat.Coprime a₁.natAbs q₁) (hcop₂ : Nat.Coprime a₂.natAbs q₂)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)| := by
  have hq₁_pos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast hq₁
  have hq₂_pos : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂
  have hnum_ne : a₁ * (q₂ : ℤ) - a₂ * (q₁ : ℤ) ≠ 0 := by
    intro hzero
    have heq : a₁ * (q₂ : ℤ) = a₂ * (q₁ : ℤ) := sub_eq_zero.mp hzero
    have hnat_eq : a₁.natAbs * q₂ = a₂.natAbs * q₁ := by
      have habs := congrArg Int.natAbs heq
      simpa [Int.natAbs_mul] using habs
    have hdvd₁ : q₁ ∣ q₂ := by
      have hdiv : q₁ ∣ q₂ * a₁.natAbs := ⟨a₂.natAbs, by linarith⟩
      exact hcop₁.symm.dvd_of_dvd_mul_right hdiv
    have hdvd₂ : q₂ ∣ q₁ := by
      have hdiv : q₂ ∣ q₁ * a₂.natAbs := ⟨a₁.natAbs, by linarith⟩
      exact hcop₂.symm.dvd_of_dvd_mul_right hdiv
    have hq_eq : q₁ = q₂ := Nat.dvd_antisymm hdvd₁ hdvd₂
    subst hq_eq
    have ha_eq : a₁ = a₂ := mul_right_cancel₀ (by exact_mod_cast (show q₁ ≠ 0 by omega)) heq
    exact hne (by simp [ha_eq])
  have h1 : (1 : ℝ) ≤ |((a₁ * (q₂ : ℤ) - a₂ * (q₁ : ℤ) : ℤ) : ℝ)| := by
    norm_cast
    exact Int.one_le_abs hnum_ne
  have hdiff : (a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ) =
      ((a₁ * (q₂ : ℤ) - a₂ * (q₁ : ℤ) : ℤ) : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    push_cast
    field_simp [hq₁_pos.ne', hq₂_pos.ne']
  rw [hdiff, abs_div, abs_of_pos (mul_pos hq₁_pos hq₂_pos)]
  exact div_le_div_of_nonneg_right h1 (mul_pos hq₁_pos hq₂_pos).le

/-- Same-denominator separation: if `q₁ = q₂ ≥ 1` and `a₁ ≠ a₂`, then
`|a₁/q₁ - a₂/q₁| ≥ 1 / q₁`. -/
theorem farey_gap_same_den {q : ℕ} {a₁ a₂ : ℤ} (hq : 1 ≤ q) (hne : a₁ ≠ a₂) :
    1 / (q : ℝ) ≤ |(a₁ : ℝ) / (q : ℝ) - (a₂ : ℝ) / (q : ℝ)| := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 : (1 : ℝ) ≤ |((a₁ - a₂ : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
  have hdiff : (a₁ : ℝ) / (q : ℝ) - (a₂ : ℝ) / (q : ℝ) = ((a₁ - a₂ : ℤ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  rw [hdiff, abs_div, abs_of_pos hq_pos]
  exact div_le_div_of_nonneg_right h1 hq_pos.le

/-- General interval disjointness from center separation exceeding the sum of radii. -/
theorem disjoint_Icc_of_radius_sum_lt {c₁ c₂ r₁ r₂ : ℝ} (h : r₁ + r₂ < |c₁ - c₂|) :
    Disjoint (Set.Icc (c₁ - r₁) (c₁ + r₁)) (Set.Icc (c₂ - r₂) (c₂ + r₂)) := by
  rw [Set.disjoint_left]
  intro α hα₁ hα₂
  have d₁ : |α - c₁| ≤ r₁ := abs_sub_le_iff.mpr ⟨by linarith [hα₁.2], by linarith [hα₁.1]⟩
  have d₂ : |α - c₂| ≤ r₂ := abs_sub_le_iff.mpr ⟨by linarith [hα₂.2], by linarith [hα₂.1]⟩
  have tri : |c₁ - c₂| ≤ |α - c₁| + |α - c₂| := by
    calc
      |c₁ - c₂| = |(c₁ - α) + (α - c₂)| := by ring_nf
      _ ≤ |c₁ - α| + |α - c₂| := abs_add_le _ _
      _ = |α - c₁| + |α - c₂| := by rw [abs_sub_comm c₁ α]
  linarith

/-- **Disjointness of major arcs** for arbitrary numerators when `2 * P ≤ Q` and `2 < Q`. -/
theorem majorArc_disjoint_of_two_lt {P Q : ℝ} {q₁ q₂ : ℕ} {a₁ a₂ : ℤ}
    (hq₁_ge : 1 ≤ q₁) (hq₂_ge : 1 ≤ q₂) (hq₁_le : (q₁ : ℝ) ≤ P) (hq₂_le : (q₂ : ℝ) ≤ P)
    (hcop₁ : Nat.Coprime a₁.natAbs q₁) (hcop₂ : Nat.Coprime a₂.natAbs q₂)
    (hPQ : 2 * P ≤ Q) (hQ2 : 2 < Q) (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (majorArc q₁ a₁ Q) (majorArc q₂ a₂ Q) := by
  have hq₁_pos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast hq₁_ge
  have hq₂_pos : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂_ge
  have hQ_pos : 0 < Q := by linarith
  refine disjoint_Icc_of_radius_sum_lt ?_
  by_cases hqq : q₁ = q₂
  · subst hqq
    have ha_ne : a₁ ≠ a₂ := fun h => hne (by simp [h])
    have hgap : 1 / (q₁ : ℝ) ≤ |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₁ : ℝ)| :=
      farey_gap_same_den hq₁_ge ha_ne
    have hrad : 1 / ((q₁ : ℝ) * Q) + 1 / ((q₁ : ℝ) * Q) < 1 / (q₁ : ℝ) := by
      have h2Q : 2 < Q := hQ2
      have hdiv : 2 / ((q₁ : ℝ) * Q) < 1 / (q₁ : ℝ) := by
        rw [div_lt_div_iff₀ (mul_pos hq₁_pos hQ_pos) hq₁_pos]
        nlinarith
      linarith [show (1 : ℝ) / ((q₁ : ℝ) * Q) + 1 / ((q₁ : ℝ) * Q) = 2 / ((q₁ : ℝ) * Q) by ring]
    exact hrad.trans_le hgap
  · have hsum_lt : (q₁ : ℝ) + (q₂ : ℝ) < Q := by
      have hlt : (q₁ : ℝ) < (q₂ : ℝ) ∨ (q₂ : ℝ) < (q₁ : ℝ) := by
        rcases lt_or_gt_of_ne hqq with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      rcases hlt with h | h <;> linarith
    have hgap : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)| :=
      farey_gap_of_ne hq₁_ge hq₂_ge hcop₁ hcop₂ hne
    have hrad :
        1 / ((q₁ : ℝ) * Q) + 1 / ((q₂ : ℝ) * Q) < 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := by
      have hsum_eq :
          1 / ((q₁ : ℝ) * Q) + 1 / ((q₂ : ℝ) * Q) =
            ((q₁ : ℝ) + (q₂ : ℝ)) / ((q₁ : ℝ) * (q₂ : ℝ) * Q) := by
        field_simp [hq₁_pos.ne', hq₂_pos.ne', hQ_pos.ne']
        ring
      have hrhs_eq :
          1 / ((q₁ : ℝ) * (q₂ : ℝ)) = Q / ((q₁ : ℝ) * (q₂ : ℝ) * Q) := by
        field_simp [hq₁_pos.ne', hq₂_pos.ne', hQ_pos.ne']
      rw [hsum_eq, hrhs_eq]
      exact div_lt_div_of_pos_right hsum_lt (mul_pos (mul_pos hq₁_pos hq₂_pos) hQ_pos)
    exact hrad.trans_le hgap

/-- **Disjointness of major arcs** for arbitrary numerators when `2 * P < Q`. -/
theorem majorArc_disjoint_of_lt {P Q : ℝ} {q₁ q₂ : ℕ} {a₁ a₂ : ℤ}
    (hq₁_ge : 1 ≤ q₁) (hq₂_ge : 1 ≤ q₂) (hq₁_le : (q₁ : ℝ) ≤ P) (hq₂_le : (q₂ : ℝ) ≤ P)
    (hcop₁ : Nat.Coprime a₁.natAbs q₁) (hcop₂ : Nat.Coprime a₂.natAbs q₂)
    (hPQ : 2 * P < Q) (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (majorArc q₁ a₁ Q) (majorArc q₂ a₂ Q) := by
  have hP1 : (1 : ℝ) ≤ P := (by exact_mod_cast hq₁_ge : (1 : ℝ) ≤ q₁).trans hq₁_le
  exact majorArc_disjoint_of_two_lt hq₁_ge hq₂_ge hq₁_le hq₂_le hcop₁ hcop₂ hPQ.le
    (by linarith) hne

/-- **Disjointness of major arcs in `majorArcs P Q`** under the sharp hypothesis `2 * P ≤ Q`.
Unlike the unrestricted case, no strict `2 * P < Q` or `2 < Q` assumption is needed because
`q = 1` admits only the single residue `a = 0` in `coprimeResidues 1`. -/
theorem majorArc_disjoint {P Q : ℝ} {q₁ q₂ a₁ a₂ : ℕ}
    (hq₁ : q₁ ∈ majorArcDenoms P) (ha₁ : a₁ ∈ coprimeResidues q₁)
    (hq₂ : q₂ ∈ majorArcDenoms P) (ha₂ : a₂ ∈ coprimeResidues q₂)
    (hPQ : 2 * P ≤ Q) (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (majorArc q₁ (a₁ : ℤ) Q) (majorArc q₂ (a₂ : ℤ) Q) := by
  simp only [majorArcDenoms, Finset.mem_Icc] at hq₁ hq₂
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range] at ha₁ ha₂
  have hP_nonneg : 0 ≤ P :=
    le_trans (by positivity) ((by exact_mod_cast hq₁.1 : (1 : ℝ) ≤ q₁).trans
      ((Nat.cast_le.mpr hq₁.2).trans (Nat.floor_le (by
        by_contra hneg
        have hfl0 : ⌊P⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hneg)
        omega))))
  have hq₁_le : (q₁ : ℝ) ≤ P := (Nat.cast_le.mpr hq₁.2).trans (Nat.floor_le hP_nonneg)
  have hq₂_le : (q₂ : ℝ) ≤ P := (Nat.cast_le.mpr hq₂.2).trans (Nat.floor_le hP_nonneg)
  have hcop₁ : Nat.Coprime (a₁ : ℤ).natAbs q₁ := by simpa using ha₁.2
  have hcop₂ : Nat.Coprime (a₂ : ℤ).natAbs q₂ := by simpa using ha₂.2
  have hne_int : (q₁, (a₁ : ℤ)) ≠ (q₂, (a₂ : ℤ)) := fun h => by
    apply hne
    have hqeq : q₁ = q₂ := congrArg Prod.fst h
    have haeq : (a₁ : ℤ) = (a₂ : ℤ) := congrArg Prod.snd h
    exact Prod.ext hqeq (Int.ofNat.inj haeq)
  have hQ2 : 2 < Q := by
    by_cases hqq : q₁ = q₂
    · subst hqq
      have ha_ne : a₁ ≠ a₂ := fun h => hne (by simp [h])
      have hq_ge2 : 2 ≤ q₁ := by omega
      have hP2 : (2 : ℝ) ≤ P := (by exact_mod_cast hq_ge2 : (2 : ℝ) ≤ q₁).trans hq₁_le
      linarith
    · have hq_ge2 : 2 ≤ q₁ ∨ 2 ≤ q₂ := by omega
      rcases hq_ge2 with h | h
      · have hP2 : (2 : ℝ) ≤ P := (by exact_mod_cast h : (2 : ℝ) ≤ q₁).trans hq₁_le
        linarith
      · have hP2 : (2 : ℝ) ≤ P := (by exact_mod_cast h : (2 : ℝ) ≤ q₂).trans hq₂_le
        linarith
  exact majorArc_disjoint_of_two_lt hq₁.1 hq₂.1 hq₁_le hq₂_le hcop₁ hcop₂ hPQ hQ2 hne_int

/-- **Disjointness of fixed-width major arcs** `majorArcFixed q a Q` when `2 * P ^ 2 < Q`. -/
theorem majorArcFixed_disjoint {P Q : ℝ} {q₁ q₂ : ℕ} {a₁ a₂ : ℤ}
    (hq₁_ge : 1 ≤ q₁) (hq₂_ge : 1 ≤ q₂) (hq₁_le : (q₁ : ℝ) ≤ P) (hq₂_le : (q₂ : ℝ) ≤ P)
    (hcop₁ : Nat.Coprime a₁.natAbs q₁) (hcop₂ : Nat.Coprime a₂.natAbs q₂)
    (hPQ : 2 * P ^ 2 < Q) (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (majorArcFixed q₁ a₁ Q) (majorArcFixed q₂ a₂ Q) := by
  have hq₁_pos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast hq₁_ge
  have hq₂_pos : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂_ge
  have hP_pos : 0 < P := lt_of_lt_of_le (by norm_num) ((by exact_mod_cast hq₁_ge : (1 : ℝ) ≤ q₁).trans hq₁_le)
  have hQ_pos : 0 < Q := by nlinarith
  refine disjoint_Icc_of_radius_sum_lt ?_
  have hgap : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)| :=
    farey_gap_of_ne hq₁_ge hq₂_ge hcop₁ hcop₂ hne
  have hqq : 2 * ((q₁ : ℝ) * (q₂ : ℝ)) < Q := by nlinarith
  have hrad : 1 / Q + 1 / Q < 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    have h2 : (1 : ℝ) / Q + 1 / Q = 2 / Q := by ring
    rw [h2, div_lt_div_iff₀ hQ_pos (mul_pos hq₁_pos hq₂_pos)]
    linarith
  exact hrad.trans_le hgap

/-- Every major arc in `majorArcs P Q` lies inside the fundamental interval `[-(1 / Q), 1 - 1 / Q]`
when `1 ≤ P` and `2 * P ≤ Q`. -/
theorem majorArc_subset_Icc {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q) {q a : ℕ}
    (hq : q ∈ majorArcDenoms P) (ha : a ∈ coprimeResidues q) :
    majorArc q (a : ℤ) Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q) := by
  simp only [majorArcDenoms, Finset.mem_Icc] at hq
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range] at ha
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.1
  have hq_le : (q : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le (zero_le_one.trans hP))
  have hQ2 : 2 ≤ Q := by linarith
  have hQ_pos : 0 < Q := by linarith
  intro α hα
  rw [majorArc, Set.mem_Icc] at hα
  rw [Set.mem_Icc]
  rcases Nat.eq_or_lt_of_le hq.1 with rfl | hq2
  · have ha0 : a = 0 := by omega
    subst ha0
    simp only [Nat.cast_zero, Int.cast_zero, Nat.cast_one, zero_div, one_mul, zero_sub,
      zero_add] at hα
    have h1Q : 1 / Q ≤ 1 - 1 / Q := by
      have : 2 / Q ≤ 1 := (div_le_one hQ_pos).mpr hQ2
      linarith [show (1 : ℝ) / Q + 1 / Q = 2 / Q by ring]
    exact ⟨hα.1, hα.2.trans h1Q⟩
  · have ha_pos : 1 ≤ a := by
      by_contra h0
      have ha0 : a = 0 := by omega
      subst ha0
      have hcop := ha.2
      simp only [Nat.coprime_zero_left] at hcop
      omega
    have ha_le : a + 1 ≤ q := ha.1
    have ha_ge_real : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
    have ha_le_real : (a : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast ha_le
    have hleft : -(1 / Q) ≤ (a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Q) := by
      have hnonneg : 0 ≤ (a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Q) := by
        rw [sub_nonneg, div_le_div_iff₀ (mul_pos hq_pos hQ_pos) hq_pos]
        have hQ1 : 1 ≤ Q := by linarith
        have haQ : 1 ≤ (a : ℝ) * Q := by nlinarith
        calc
          1 * (q : ℝ) = (q : ℝ) := one_mul _
          _ ≤ ((a : ℝ) * Q) * (q : ℝ) := le_mul_of_one_le_left hq_pos.le haQ
          _ = (a : ℝ) * ((q : ℝ) * Q) := by ring
      linarith [one_div_nonneg.mpr hQ_pos.le]
    have hright : (a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Q) ≤ 1 - 1 / Q := by
      have hqQ : (q : ℝ) + 1 ≤ Q := by linarith
      have hdiv : ((a : ℝ) * Q + 1) / ((q : ℝ) * Q) ≤ (Q - 1) / Q := by
        rw [div_le_div_iff₀ (mul_pos hq_pos hQ_pos) hQ_pos]
        have hstep : (a : ℝ) * Q + 1 ≤ (Q - 1) * (q : ℝ) := by
          have h1 : (a : ℝ) * Q + 1 ≤ ((q : ℝ) - 1) * Q + 1 := by nlinarith
          have h2 : ((q : ℝ) - 1) * Q + 1 = (q : ℝ) * Q - Q + 1 := by ring
          have h3 : (q : ℝ) * Q - Q + 1 ≤ (q : ℝ) * Q - (q : ℝ) := by linarith
          linarith
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hstep hQ_pos.le
      have hl : (a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Q) = ((a : ℝ) * Q + 1) / ((q : ℝ) * Q) := by
        field_simp [hq_pos.ne', hQ_pos.ne']
      have hr : (1 : ℝ) - 1 / Q = (Q - 1) / Q := by
        field_simp [hQ_pos.ne']
      rw [hl, hr]
      exact hdiv
    exact ⟨hleft.trans hα.1, hα.2.trans hright⟩

/-- When `1 ≤ P` and `2 * P ≤ Q`, `majorArcs P Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q)`. -/
theorem majorArcs_subset_Icc {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q) :
    majorArcs P Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q) := by
  intro α hα
  simp only [majorArcs, Set.mem_iUnion, exists_prop] at hα
  obtain ⟨q, hq, a, ha, hmem⟩ := hα
  exact majorArc_subset_Icc hP hPQ hq ha hmem

/-- `minorArcs P Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q)`. -/
theorem minorArcs_subset_Icc (P Q : ℝ) :
    minorArcs P Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q) :=
  Set.sdiff_subset

/-- `majorArcs P Q` and `minorArcs P Q` are disjoint. -/
theorem disjoint_majorArcs_minorArcs (P Q : ℝ) :
    Disjoint (majorArcs P Q) (minorArcs P Q) :=
  disjoint_sdiff_self_right

/-- **Measurable partition of `[-(1 / Q), 1 - 1 / Q]`**:
when `1 ≤ P` and `2 * P ≤ Q`, `majorArcs P Q ∪ minorArcs P Q = Set.Icc (-(1 / Q)) (1 - 1 / Q)`. -/
theorem majorArcs_union_minorArcs {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q) :
    majorArcs P Q ∪ minorArcs P Q = Set.Icc (-(1 / Q)) (1 - 1 / Q) :=
  Set.union_sdiff_cancel (majorArcs_subset_Icc hP hPQ)

/-- **Dirichlet characterization of minor arcs**:
every `α ∈ minorArcs P Q` (with `1 ≤ P`, `2 * P ≤ Q`) admits a rational approximation `a / q`
with `P < q ≤ Q`, `Nat.Coprime a.natAbs q`, and `|α - a / q| < 1 / (q * Q)`. -/
theorem mem_minorArcs_approx_lt {P Q α : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q)
    (hα : α ∈ minorArcs P Q) :
    ∃ (a : ℤ) (q : ℕ),
      P < (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * Q) := by
  have hQ1 : 1 ≤ Q := by linarith
  have hQ2 : 2 ≤ Q := by linarith
  have hQ_pos : 0 < Q := by linarith
  obtain ⟨hα_Icc, hα_not⟩ := hα
  rw [Set.mem_Icc] at hα_Icc
  obtain ⟨a, q, hq_ge1, hq_leQ, hcop, hdist⟩ := dirichlet_rational_approx_lt α hQ1
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_ge1
  refine ⟨a, q, ?_, hq_leQ, hcop, hdist⟩
  by_contra hleP
  push Not at hleP
  have ha_nonneg : 0 ≤ a := by
    by_contra haneg
    push Not at haneg
    have ha_le_neg1 : (a : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt haneg
    have hgap : 1 / ((q : ℝ) * Q) ≤ α - (a : ℝ) / (q : ℝ) := by
      have h1q : 1 / (q : ℝ) ≤ -((a : ℝ) / (q : ℝ)) := by
        rw [← neg_div, div_le_div_iff_of_pos_right hq_pos]
        linarith
      have hq1Q : (q : ℝ) + 1 ≤ Q := by linarith
      have hdiff : 1 / ((q : ℝ) * Q) ≤ 1 / (q : ℝ) - 1 / Q := by
        have h1 : 1 / (q : ℝ) - 1 / Q = (Q - (q : ℝ)) / ((q : ℝ) * Q) := by
          field_simp [hq_pos.ne', hQ_pos.ne']
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith) (mul_pos hq_pos hQ_pos).le
      linarith [hα_Icc.1]
    have hdist' : α - (a : ℝ) / (q : ℝ) < 1 / ((q : ℝ) * Q) :=
      (le_abs_self _).trans_lt hdist
    linarith
  have ha_lt_q : a < (q : ℤ) := by
    by_contra hage
    push Not at hage
    have ha_ge_q : (1 : ℝ) ≤ (a : ℝ) / (q : ℝ) := by
      rw [one_le_div hq_pos]
      exact_mod_cast hage
    have hgap : 1 / ((q : ℝ) * Q) ≤ (a : ℝ) / (q : ℝ) - α := by
      have hq1 : 1 / ((q : ℝ) * Q) ≤ 1 / Q := by
        rw [div_le_div_iff₀ (mul_pos hq_pos hQ_pos) hQ_pos]
        nlinarith [show (1 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq_ge1]
      linarith [hα_Icc.2]
    have hdist' : (a : ℝ) / (q : ℝ) - α < 1 / ((q : ℝ) * Q) := by
      rw [← abs_sub_comm] at hdist
      exact (le_abs_self _).trans_lt hdist
    linarith
  have htoNat_eq : a.toNat = a.natAbs := Int.ofNat.inj
    ((Int.toNat_of_nonneg ha_nonneg).trans (Int.natAbs_of_nonneg ha_nonneg).symm)
  apply hα_not
  simp only [majorArcs, Set.mem_iUnion, exists_prop]
  refine ⟨q, ?_, a.toNat, ?_, ?_⟩
  · simp only [majorArcDenoms, Finset.mem_Icc]
    exact ⟨hq_ge1, Nat.le_floor hleP⟩
  · simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · exact_mod_cast (show (a.toNat : ℤ) < (q : ℤ) by
        rw [Int.toNat_of_nonneg ha_nonneg]; exact ha_lt_q)
    · rw [htoNat_eq]
      exact hcop
  · rw [mem_majorArc_iff]
    simpa [Int.toNat_of_nonneg ha_nonneg] using hdist.le

/-- Non-strict Dirichlet characterization on minor arcs: every `α ∈ minorArcs P Q` satisfies
`∃ a q, P < q ≤ Q ∧ Nat.Coprime a.natAbs q ∧ |α - a / q| ≤ 1 / (q * Q)`. -/
theorem mem_minorArcs_approx {P Q α : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q)
    (hα : α ∈ minorArcs P Q) :
    ∃ (a : ℤ) (q : ℕ),
      P < (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * Q) := by
  obtain ⟨a, q, hPq, hqQ, hcop, hlt⟩ := mem_minorArcs_approx_lt hP hPQ hα
  exact ⟨a, q, hPq, hqQ, hcop, hlt.le⟩

/-- Lebesgue measure of a single major arc `majorArc q a Q`. -/
theorem volume_majorArc {q : ℕ} (_hq : 1 ≤ q) (a : ℤ) {Q : ℝ} (_hQ : 0 < Q) :
    volume (majorArc q a Q) = ENNReal.ofReal (2 / ((q : ℝ) * Q)) := by
  rw [majorArc, Real.volume_Icc]
  congr 1
  ring

/-- Upper bound on the Lebesgue measure of `majorArcs P Q`:
`volume (majorArcs P Q) ≤ ENNReal.ofReal (2 * P / Q)` when `0 ≤ P` and `0 < Q`. -/
theorem volume_majorArcs_le {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 < Q) :
    volume (majorArcs P Q) ≤ ENNReal.ofReal (2 * P / Q) := by
  calc
    volume (majorArcs P Q) ≤
        ∑ q ∈ majorArcDenoms P, ∑ a ∈ coprimeResidues q, volume (majorArc q (a : ℤ) Q) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine Finset.sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ = ∑ q ∈ majorArcDenoms P, ∑ _a ∈ coprimeResidues q,
          ENNReal.ofReal (2 / ((q : ℝ) * Q)) := by
      refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun a _ => ?_
      exact volume_majorArc (Finset.mem_Icc.mp hq).1 a hQ
    _ = ∑ q ∈ majorArcDenoms P,
          ENNReal.ofReal (((coprimeResidues q).card : ℝ) * (2 / ((q : ℝ) * Q))) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ∑ q ∈ majorArcDenoms P, ENNReal.ofReal (2 / Q) := by
      refine Finset.sum_le_sum fun q hq => ENNReal.ofReal_le_ofReal ?_
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      have hcard : ((coprimeResidues q).card : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Finset.card_filter_le (Finset.range q) _).trans_eq (Finset.card_range q)
      calc
        ((coprimeResidues q).card : ℝ) * (2 / ((q : ℝ) * Q))
            ≤ (q : ℝ) * (2 / ((q : ℝ) * Q)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 / Q := by field_simp [hq_pos.ne']
    _ = ENNReal.ofReal (((majorArcDenoms P).card : ℝ) * (2 / Q)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * P / Q) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hcard : ((majorArcDenoms P).card : ℝ) ≤ P := by
        rw [majorArcDenoms, Nat.card_Icc, Nat.add_sub_cancel]
        exact Nat.floor_le hP
      calc
        ((majorArcDenoms P).card : ℝ) * (2 / Q) ≤ P * (2 / Q) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * P / Q := by ring

end MajorAndMinorArcs

section IntegralDecompositionAndBounds

/-- The representation integral `∫ α in (0 : ℝ)..1, f α`. -/
def representationIntegral (f : ℝ → ℂ) : ℂ :=
  ∫ α in (0 : ℝ)..1, f α

/-- The major-arc contribution `∫ α in majorArcs P Q, f α`. -/
def majorArcIntegral (f : ℝ → ℂ) (P Q : ℝ) : ℂ :=
  ∫ α in majorArcs P Q, f α

/-- The minor-arc contribution `∫ α in minorArcs P Q, f α`. -/
def minorArcIntegral (f : ℝ → ℂ) (P Q : ℝ) : ℂ :=
  ∫ α in minorArcs P Q, f α

/-- For any 1-periodic `f : ℝ → ℂ`, `representationIntegral f` equals the set integral over
any shifted closed unit interval `Set.Icc δ (1 + δ)`. -/
theorem representationIntegral_eq_setIntegral_Icc {f : ℝ → ℂ} (hf : Function.Periodic f 1)
    (δ : ℝ) :
    representationIntegral f = ∫ α in Set.Icc δ (1 + δ), f α := by
  rw [representationIntegral, ← setIntegral_Icc_periodic_eq hf δ, add_comm δ 1]

/-- **Integral decomposition into major arcs and minor arcs**:
`representationIntegral f = majorArcIntegral f P Q + minorArcIntegral f P Q`
whenever `f` is 1-periodic, `1 ≤ P`, `2 * P ≤ Q`, and `f` is integrable on `[-(1 / Q), 1 - 1 / Q]`. -/
theorem representationIntegral_eq_majorArcIntegral_add_minorArcIntegral {f : ℝ → ℂ}
    (hf : Function.Periodic f 1) {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q)
    (hint : IntegrableOn f (Set.Icc (-(1 / Q)) (1 - 1 / Q))) :
    representationIntegral f = majorArcIntegral f P Q + minorArcIntegral f P Q := by
  have hshift : representationIntegral f = ∫ α in Set.Icc (-(1 / Q)) (1 - 1 / Q), f α := by
    rw [representationIntegral_eq_setIntegral_Icc hf (-(1 / Q)), sub_eq_add_neg]
  rw [hshift, majorArcIntegral, minorArcIntegral,
    ← MeasureTheory.setIntegral_union (disjoint_majorArcs_minorArcs P Q)
      (measurableSet_minorArcs P Q)
      (hint.mono_set (majorArcs_subset_Icc hP hPQ))
      (hint.mono_set (minorArcs_subset_Icc P Q)),
    majorArcs_union_minorArcs hP hPQ]

/-- Continuous-integrand convenience version of
`representationIntegral_eq_majorArcIntegral_add_minorArcIntegral`. -/
theorem representationIntegral_eq_majorArcIntegral_add_minorArcIntegral_of_continuous
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hcont : Continuous f) {P Q : ℝ}
    (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q) :
    representationIntegral f = majorArcIntegral f P Q + minorArcIntegral f P Q :=
  representationIntegral_eq_majorArcIntegral_add_minorArcIntegral hf hP hPQ
    hcont.continuousOn.integrableOn_Icc

/-- **Major-arc sum decomposition**:
when `2 * P ≤ Q` and `f` is integrable on `majorArcs P Q`,
`majorArcIntegral f P Q = ∑ q ∈ majorArcDenoms P, ∑ a ∈ coprimeResidues q, ∫ α in majorArc q a Q, f α`. -/
theorem majorArcIntegral_eq_sum {f : ℝ → ℂ} {P Q : ℝ} (hPQ : 2 * P ≤ Q)
    (hint : IntegrableOn f (majorArcs P Q)) :
    majorArcIntegral f P Q =
      ∑ q ∈ majorArcDenoms P, ∑ a ∈ coprimeResidues q, ∫ α in majorArc q (a : ℤ) Q, f α := by
  have hint_arc : ∀ q ∈ majorArcDenoms P, ∀ a ∈ coprimeResidues q,
      IntegrableOn f (majorArc q (a : ℤ) Q) := by
    intro q hq a ha
    refine hint.mono_set fun α hα => ?_
    simp only [majorArcs, Set.mem_iUnion, exists_prop]
    exact ⟨q, hq, a, ha, hα⟩
  have houter :
      (∫ α in majorArcs P Q, f α) =
        ∑ q ∈ majorArcDenoms P,
          ∫ α in ⋃ a ∈ coprimeResidues q, majorArc q (a : ℤ) Q, f α := by
    refine MeasureTheory.integral_biUnion_finset (majorArcDenoms P) ?_ ?_ ?_
    · intro q _
      exact Finset.measurableSet_biUnion (coprimeResidues q) fun a _ => measurableSet_majorArc q a Q
    · intro q₁ hq₁ q₂ hq₂ hne
      change Disjoint (⋃ a ∈ coprimeResidues q₁, majorArc q₁ (a : ℤ) Q)
        (⋃ a ∈ coprimeResidues q₂, majorArc q₂ (a : ℤ) Q)
      rw [Set.disjoint_iUnion₂_left]
      intro a₁ ha₁
      rw [Set.disjoint_iUnion₂_right]
      intro a₂ ha₂
      exact majorArc_disjoint hq₁ ha₁ hq₂ ha₂ hPQ (fun h => hne (congrArg Prod.fst h))
    · intro q hq
      exact MeasureTheory.integrableOn_finset_iUnion.mpr fun a ha => hint_arc q hq a ha
  rw [majorArcIntegral, houter]
  refine Finset.sum_congr rfl fun q hq => ?_
  refine MeasureTheory.integral_biUnion_finset (coprimeResidues q) ?_ ?_ ?_
  · intro a _
    exact measurableSet_majorArc q a Q
  · intro a₁ ha₁ a₂ ha₂ hne
    exact majorArc_disjoint hq ha₁ hq ha₂ hPQ (fun h => hne (congrArg Prod.snd h))
  · intro a ha
    exact hint_arc q hq a ha

/-- Continuous-integrand convenience version of `majorArcIntegral_eq_sum`. -/
theorem majorArcIntegral_eq_sum_of_continuous {f : ℝ → ℂ} (hcont : Continuous f)
    {P Q : ℝ} (hPQ : 2 * P ≤ Q) :
    majorArcIntegral f P Q =
      ∑ q ∈ majorArcDenoms P, ∑ a ∈ coprimeResidues q, ∫ α in majorArc q (a : ℤ) Q, f α := by
  refine majorArcIntegral_eq_sum hPQ ?_
  exact MeasureTheory.integrableOn_finset_iUnion.mpr fun q _ =>
    MeasureTheory.integrableOn_finset_iUnion.mpr fun a _ =>
      hcont.continuousOn.integrableOn_Icc

/-- Change of variables `α = a / q + β` on a major arc `majorArc q a Q`, expressing its
set integral as a centered interval integral over `[-(1 / (q * Q)), 1 / (q * Q)]`. -/
theorem setIntegral_majorArc_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {q : ℕ} (hq : 1 ≤ q) (a : ℤ) {Q : ℝ} (hQ : 0 < Q) :
    ∫ α in majorArc q a Q, f α =
      ∫ β in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)), f ((a : ℝ) / (q : ℝ) + β) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hle : (a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Q) ≤ (a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Q) := by
    have : 0 ≤ 1 / ((q : ℝ) * Q) := by positivity
    linarith
  rw [majorArc, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_comp_add_left f ((a : ℝ) / (q : ℝ))]
  congr 1

/-- **General minor-arc bound (explicit pointwise bound)**:
if `m ⊆ Set.Icc δ (1 + δ)` is measurable, `‖F α‖ ≤ M` for all `α ∈ m` (`0 ≤ M`),
and `H` is 1-periodic with `‖H‖` integrable on `[δ, 1 + δ]`, then
`‖∫ α in m, F α * H α‖ ≤ M * ∫ α in (0 : ℝ)..1, ‖H α‖`. -/
theorem norm_setIntegral_mul_le_of_bound {m : Set ℝ} {δ : ℝ} (hm_meas : MeasurableSet m)
    (hm_sub : m ⊆ Set.Icc δ (1 + δ)) {F H : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ α ∈ m, ‖F α‖ ≤ M) (hFH_int : IntegrableOn (fun α => F α * H α) m)
    (hH_int : IntegrableOn (fun α => ‖H α‖) (Set.Icc δ (1 + δ)))
    (hH_per : Function.Periodic H 1) :
    ‖∫ α in m, F α * H α‖ ≤ M * ∫ α in (0 : ℝ)..1, ‖H α‖ := by
  have hnorm_per : Function.Periodic (fun α : ℝ => ‖H α‖) 1 := fun α => by
    dsimp only
    rw [hH_per α]
  have hMH_int : IntegrableOn (fun α => M * ‖H α‖) m :=
    (hH_int.mono_set hm_sub).const_mul M
  have hnorm_int : IntegrableOn (fun α => ‖F α * H α‖) m := hFH_int.norm
  calc
    ‖∫ α in m, F α * H α‖ ≤ ∫ α in m, ‖F α * H α‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ α in m, M * ‖H α‖ := by
      refine MeasureTheory.setIntegral_mono_on hnorm_int hMH_int hm_meas fun α hα => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hF α hα) (norm_nonneg _)
    _ = M * ∫ α in m, ‖H α‖ := MeasureTheory.integral_const_mul M _
    _ ≤ M * ∫ α in Set.Icc δ (1 + δ), ‖H α‖ := by
      refine mul_le_mul_of_nonneg_left ?_ hM
      refine MeasureTheory.setIntegral_mono_set hH_int
        (MeasureTheory.ae_of_all _ fun α => norm_nonneg (H α))
        (Filter.Eventually.of_forall fun α hα => hm_sub hα)
    _ = M * ∫ α in (0 : ℝ)..1, ‖H α‖ := by
      rw [add_comm 1 δ, setIntegral_Icc_periodic_eq hnorm_per δ]

/-- **General minor-arc bound (`sSup` form)**:
for measurable `m ⊆ Set.Icc δ (1 + δ)`, 1-periodic `H`, and `BddAbove ((fun α => ‖F α‖) '' m)`,
`‖∫ α in m, F α * H α‖ ≤ sSup ((fun α => ‖F α‖) '' m) * ∫ α in (0 : ℝ)..1, ‖H α‖`. -/
theorem norm_setIntegral_mul_le_sSup {m : Set ℝ} {δ : ℝ} (hm_meas : MeasurableSet m)
    (hm_sub : m ⊆ Set.Icc δ (1 + δ)) {F H : ℝ → ℂ}
    (hbdd : BddAbove ((fun α => ‖F α‖) '' m))
    (hFH_int : IntegrableOn (fun α => F α * H α) m)
    (hH_int : IntegrableOn (fun α => ‖H α‖) (Set.Icc δ (1 + δ)))
    (hH_per : Function.Periodic H 1) :
    ‖∫ α in m, F α * H α‖ ≤ sSup ((fun α => ‖F α‖) '' m) * ∫ α in (0 : ℝ)..1, ‖H α‖ := by
  by_cases hm_empty : m = ∅
  · subst hm_empty
    simp
  · obtain ⟨α₀, hα₀⟩ := Set.nonempty_iff_ne_empty.mpr hm_empty
    have hM : 0 ≤ sSup ((fun α => ‖F α‖) '' m) :=
      (norm_nonneg (F α₀)).trans (le_csSup hbdd ⟨α₀, hα₀, rfl⟩)
    exact norm_setIntegral_mul_le_of_bound hm_meas hm_sub hM
      (fun α hα => le_csSup hbdd ⟨α, hα, rfl⟩) hFH_int hH_int hH_per

/-- **Minor-arc bound for `∫_{minorArcs P Q} F(α) G(α)^(s - 1) e(-α N) dα`**
given an explicit bound `‖F α‖ ≤ M` on `minorArcs P Q` (with continuous `F, G` and 1-periodic `G`). -/
theorem norm_minorArcIntegral_mul_pow_e_neg_le_of_bound {F G : ℝ → ℂ}
    (hF_cont : Continuous F) (hG_cont : Continuous G) (hG_per : Function.Periodic G 1)
    {P Q M : ℝ} (hM : 0 ≤ M) (hF_bd : ∀ α ∈ minorArcs P Q, ‖F α‖ ≤ M) (s : ℕ) (N : ℤ) :
    ‖∫ α in minorArcs P Q, F α * G α ^ (s - 1) * e (-α * (N : ℝ))‖ ≤
      M * ∫ α in (0 : ℝ)..1, ‖G α‖ ^ (s - 1) := by
  have heq_integrand :
      (fun α : ℝ => F α * G α ^ (s - 1) * e (-α * (N : ℝ))) =
        fun α : ℝ => F α * (G α ^ (s - 1) * e (-α * (N : ℝ))) := by
    ext α; ring
  have hH_per : Function.Periodic (fun α : ℝ => G α ^ (s - 1) * e (-α * (N : ℝ))) 1 := by
    intro α
    dsimp only
    rw [hG_per α]
    have hneg : -(α + 1) * (N : ℝ) = -α * (N : ℝ) + ((-N : ℤ) : ℝ) := by push_cast; ring
    rw [hneg, e_add_intCast]
  have hH_cont : Continuous (fun α : ℝ => G α ^ (s - 1) * e (-α * (N : ℝ))) :=
    (hG_cont.pow (s - 1)).mul (continuous_e.comp ((continuous_neg.comp continuous_id).mul continuous_const))
  have hFH_cont : Continuous (fun α : ℝ => F α * (G α ^ (s - 1) * e (-α * (N : ℝ)))) :=
    hF_cont.mul hH_cont
  have hH_norm :
      (fun α : ℝ => ‖G α ^ (s - 1) * e (-α * (N : ℝ))‖) = fun α : ℝ => ‖G α‖ ^ (s - 1) := by
    ext α
    rw [norm_mul, norm_pow, norm_e, mul_one]
  rw [heq_integrand]
  have hres := norm_setIntegral_mul_le_of_bound (measurableSet_minorArcs P Q)
    (minorArcs_subset_Icc P Q) hM hF_bd
    (hFH_cont.continuousOn.integrableOn_Icc.mono_set (minorArcs_subset_Icc P Q))
    (hH_cont.norm.continuousOn.integrableOn_Icc)
    hH_per
  simpa [hH_norm] using hres

/-- **Minor-arc bound (`sSup` form)** matching
`‖∫_{minorArcs} F(α) G(α)^{s-1} dα‖ ≤ (sup_{α ∈ m} ‖F(α)‖) * ∫_0^1 ‖G(α)‖^{s-1} dα`. -/
theorem norm_minorArcIntegral_mul_pow_le_sSup {F G : ℝ → ℂ}
    (hF_cont : Continuous F) (hG_cont : Continuous G) (hG_per : Function.Periodic G 1)
    (P Q : ℝ) (s : ℕ) :
    ‖∫ α in minorArcs P Q, F α * G α ^ (s - 1)‖ ≤
      sSup ((fun α => ‖F α‖) '' minorArcs P Q) * ∫ α in (0 : ℝ)..1, ‖G α‖ ^ (s - 1) := by
  have hH_per : Function.Periodic (fun α : ℝ => G α ^ (s - 1)) 1 := fun α => by
    dsimp only; rw [hG_per α]
  have hH_cont : Continuous (fun α : ℝ => G α ^ (s - 1)) := hG_cont.pow (s - 1)
  have hFH_cont : Continuous (fun α : ℝ => F α * G α ^ (s - 1)) := hF_cont.mul hH_cont
  have hbdd : BddAbove ((fun α => ‖F α‖) '' minorArcs P Q) := by
    have hcomp : IsCompact (Set.Icc (-(1 / Q)) (1 - 1 / Q)) := isCompact_Icc
    exact (hcomp.image hF_cont.norm).bddAbove.mono
      (Set.image_mono (minorArcs_subset_Icc P Q))
  have hres := norm_setIntegral_mul_le_sSup (measurableSet_minorArcs P Q)
    (minorArcs_subset_Icc P Q) hbdd
    (hFH_cont.continuousOn.integrableOn_Icc.mono_set (minorArcs_subset_Icc P Q))
    (hH_cont.norm.continuousOn.integrableOn_Icc)
    hH_per
  simpa only [norm_pow] using hres

/-- **Minor-arc bound (`sSup` form with oscillatory phase `e(-α N)`)**:
`‖∫_{minorArcs} F(α) G(α)^{s-1} e(-α N) dα‖ ≤ (sup_{α ∈ m} ‖F(α)‖) * ∫_0^1 ‖G(α)‖^{s-1} dα`. -/
theorem norm_minorArcIntegral_mul_pow_e_neg_le_sSup {F G : ℝ → ℂ}
    (hF_cont : Continuous F) (hG_cont : Continuous G) (hG_per : Function.Periodic G 1)
    (P Q : ℝ) (s : ℕ) (N : ℤ) :
    ‖∫ α in minorArcs P Q, F α * G α ^ (s - 1) * e (-α * (N : ℝ))‖ ≤
      sSup ((fun α => ‖F α‖) '' minorArcs P Q) * ∫ α in (0 : ℝ)..1, ‖G α‖ ^ (s - 1) := by
  have heq_integrand :
      (fun α : ℝ => F α * G α ^ (s - 1) * e (-α * (N : ℝ))) =
        fun α : ℝ => F α * (G α ^ (s - 1) * e (-α * (N : ℝ))) := by
    ext α; ring
  have hH_per : Function.Periodic (fun α : ℝ => G α ^ (s - 1) * e (-α * (N : ℝ))) 1 := by
    intro α
    dsimp only
    rw [hG_per α]
    have hneg : -(α + 1) * (N : ℝ) = -α * (N : ℝ) + ((-N : ℤ) : ℝ) := by push_cast; ring
    rw [hneg, e_add_intCast]
  have hH_cont : Continuous (fun α : ℝ => G α ^ (s - 1) * e (-α * (N : ℝ))) :=
    (hG_cont.pow (s - 1)).mul
      (continuous_e.comp ((continuous_neg.comp continuous_id).mul continuous_const))
  have hFH_cont : Continuous (fun α : ℝ => F α * (G α ^ (s - 1) * e (-α * (N : ℝ)))) :=
    hF_cont.mul hH_cont
  have hH_norm :
      (fun α : ℝ => ‖G α ^ (s - 1) * e (-α * (N : ℝ))‖) = fun α : ℝ => ‖G α‖ ^ (s - 1) := by
    ext α
    rw [norm_mul, norm_pow, norm_e, mul_one]
  have hbdd : BddAbove ((fun α => ‖F α‖) '' minorArcs P Q) := by
    have hcomp : IsCompact (Set.Icc (-(1 / Q)) (1 - 1 / Q)) := isCompact_Icc
    exact (hcomp.image hF_cont.norm).bddAbove.mono
      (Set.image_mono (minorArcs_subset_Icc P Q))
  rw [heq_integrand]
  have hres := norm_setIntegral_mul_le_sSup (measurableSet_minorArcs P Q)
    (minorArcs_subset_Icc P Q) hbdd
    (hFH_cont.continuousOn.integrableOn_Icc.mono_set (minorArcs_subset_Icc P Q))
    (hH_cont.norm.continuousOn.integrableOn_Icc)
    hH_per
  simpa [hH_norm] using hres

section FixedWidthAndScaledVariants

/-- Disjointness of fixed-width major arcs inside `majorArcsFixed P Q` when `2 * P ^ 2 < Q`. -/
theorem majorArcFixed_disjoint_range {P Q : ℝ} {q₁ q₂ a₁ a₂ : ℕ}
    (hq₁ : q₁ ∈ majorArcDenoms P) (ha₁ : a₁ ∈ coprimeResidues q₁)
    (hq₂ : q₂ ∈ majorArcDenoms P) (ha₂ : a₂ ∈ coprimeResidues q₂)
    (hPQ : 2 * P ^ 2 < Q) (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (majorArcFixed q₁ (a₁ : ℤ) Q) (majorArcFixed q₂ (a₂ : ℤ) Q) := by
  simp only [majorArcDenoms, Finset.mem_Icc] at hq₁ hq₂
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range] at ha₁ ha₂
  have hP_nonneg : 0 ≤ P := by
    by_contra hneg
    have hfl0 : ⌊P⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hneg)
    omega
  have hq₁_le : (q₁ : ℝ) ≤ P := (Nat.cast_le.mpr hq₁.2).trans (Nat.floor_le hP_nonneg)
  have hq₂_le : (q₂ : ℝ) ≤ P := (Nat.cast_le.mpr hq₂.2).trans (Nat.floor_le hP_nonneg)
  have hcop₁ : Nat.Coprime (a₁ : ℤ).natAbs q₁ := by simpa using ha₁.2
  have hcop₂ : Nat.Coprime (a₂ : ℤ).natAbs q₂ := by simpa using ha₂.2
  have hne_int : (q₁, (a₁ : ℤ)) ≠ (q₂, (a₂ : ℤ)) := fun h =>
    hne (Prod.ext (congrArg (Prod.fst : ℕ × ℤ → ℕ) h)
      (Int.ofNat.inj (congrArg (Prod.snd : ℕ × ℤ → ℤ) h)))
  exact majorArcFixed_disjoint hq₁.1 hq₂.1 hq₁_le hq₂_le hcop₁ hcop₂ hPQ hne_int

/-- Every fixed-width major arc in `majorArcsFixed P Q` lies inside `[-(1 / Q), 1 - 1 / Q]`
when `1 ≤ P` and `2 * P ^ 2 < Q`. -/
theorem majorArcFixed_subset_Icc {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q) {q a : ℕ}
    (hq : q ∈ majorArcDenoms P) (ha : a ∈ coprimeResidues q) :
    majorArcFixed q (a : ℤ) Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q) := by
  simp only [majorArcDenoms, Finset.mem_Icc] at hq
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range] at ha
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.1
  have hq_le : (q : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le (zero_le_one.trans hP))
  have h2PQ : 2 * P < Q := by nlinarith
  have hQ2 : 2 < Q := by linarith
  have hQ_pos : 0 < Q := by linarith
  intro α hα
  rw [majorArcFixed, Set.mem_Icc] at hα
  rw [Set.mem_Icc]
  rcases Nat.eq_or_lt_of_le hq.1 with rfl | hq2
  · have ha0 : a = 0 := by omega
    subst ha0
    simp only [Nat.cast_zero, Int.cast_zero, Nat.cast_one, zero_div, zero_sub, zero_add] at hα
    have h1Q : 1 / Q ≤ 1 - 1 / Q := by
      have : 2 / Q ≤ 1 := (div_le_one hQ_pos).mpr hQ2.le
      linarith [show (1 : ℝ) / Q + 1 / Q = 2 / Q by ring]
    exact ⟨hα.1, hα.2.trans h1Q⟩
  · have ha_pos : 1 ≤ a := by
      by_contra h0
      have ha0 : a = 0 := by omega
      subst ha0
      have hcop := ha.2
      simp only [Nat.coprime_zero_left] at hcop
      omega
    have ha_le : a + 1 ≤ q := ha.1
    have ha_ge_real : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
    have ha_le_real : (a : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast ha_le
    have hleft : -(1 / Q) ≤ (a : ℝ) / (q : ℝ) - 1 / Q := by
      have hqQ : (q : ℝ) ≤ Q := by linarith
      have h1 : 1 / Q ≤ 1 / (q : ℝ) := one_div_le_one_div_of_le hq_pos hqQ
      have h2 : 1 / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) :=
        div_le_div_of_nonneg_right ha_ge_real hq_pos.le
      linarith [one_div_nonneg.mpr hQ_pos.le]
    have hright : (a : ℝ) / (q : ℝ) + 1 / Q ≤ 1 - 1 / Q := by
      have h1 : (a : ℝ) / (q : ℝ) ≤ 1 - 1 / (q : ℝ) := by
        rw [le_sub_iff_add_le, ← add_div, div_le_one hq_pos]
        exact ha_le_real
      have h2 : 2 / Q ≤ 1 / (q : ℝ) := by
        rw [div_le_div_iff₀ hQ_pos hq_pos]
        linarith
      linarith [show (1 : ℝ) / Q + 1 / Q = 2 / Q by ring]
    exact ⟨hleft.trans hα.1, hα.2.trans hright⟩

/-- When `1 ≤ P` and `2 * P ^ 2 < Q`, `majorArcsFixed P Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q)`. -/
theorem majorArcsFixed_subset_Icc {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q) :
    majorArcsFixed P Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q) := by
  intro α hα
  simp only [majorArcsFixed, Set.mem_iUnion, exists_prop] at hα
  obtain ⟨q, hq, a, ha, hmem⟩ := hα
  exact majorArcFixed_subset_Icc hP hPQ hq ha hmem

/-- Measurable partition for fixed-width arcs when `1 ≤ P` and `2 * P ^ 2 < Q`. -/
theorem majorArcsFixed_union_minorArcsFixed {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q) :
    majorArcsFixed P Q ∪ minorArcsFixed P Q = Set.Icc (-(1 / Q)) (1 - 1 / Q) :=
  Set.union_sdiff_cancel (majorArcsFixed_subset_Icc hP hPQ)

/-- Fixed-width major and minor arcs are disjoint. -/
theorem disjoint_majorArcsFixed_minorArcsFixed (P Q : ℝ) :
    Disjoint (majorArcsFixed P Q) (minorArcsFixed P Q) :=
  disjoint_sdiff_self_right

/-- Fixed-width minor arcs are contained in `[-(1 / Q), 1 - 1 / Q]`. -/
theorem minorArcsFixed_subset_Icc (P Q : ℝ) :
    minorArcsFixed P Q ⊆ Set.Icc (-(1 / Q)) (1 - 1 / Q) :=
  Set.sdiff_subset

/-- **Dirichlet characterization on fixed-width minor arcs**:
every `α ∈ minorArcsFixed P Q` (with `1 ≤ P`, `2 * P ^ 2 < Q`) admits `a : ℤ`, `q : ℕ`
with `P < q ≤ Q`, `Nat.Coprime a.natAbs q`, and `|α - a / q| < 1 / (q * Q)`. -/
theorem mem_minorArcsFixed_approx_lt {P Q α : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q)
    (hα : α ∈ minorArcsFixed P Q) :
    ∃ (a : ℤ) (q : ℕ),
      P < (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * Q) := by
  have h2PQ : 2 * P < Q := by nlinarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ_pos : 0 < Q := by linarith
  obtain ⟨hα_Icc, hα_not⟩ := hα
  rw [Set.mem_Icc] at hα_Icc
  obtain ⟨a, q, hq_ge1, hq_leQ, hcop, hdist⟩ := dirichlet_rational_approx_lt α hQ1
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_ge1
  refine ⟨a, q, ?_, hq_leQ, hcop, hdist⟩
  by_contra hleP
  push Not at hleP
  have ha_nonneg : 0 ≤ a := by
    by_contra haneg
    push Not at haneg
    have ha_le_neg1 : (a : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt haneg
    have hgap : 1 / ((q : ℝ) * Q) ≤ α - (a : ℝ) / (q : ℝ) := by
      have h1q : 1 / (q : ℝ) ≤ -((a : ℝ) / (q : ℝ)) := by
        rw [← neg_div, div_le_div_iff_of_pos_right hq_pos]
        linarith
      have hq1Q : (q : ℝ) + 1 ≤ Q := by linarith
      have hdiff : 1 / ((q : ℝ) * Q) ≤ 1 / (q : ℝ) - 1 / Q := by
        have h1 : 1 / (q : ℝ) - 1 / Q = (Q - (q : ℝ)) / ((q : ℝ) * Q) := by
          field_simp [hq_pos.ne', hQ_pos.ne']
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith) (mul_pos hq_pos hQ_pos).le
      linarith [hα_Icc.1]
    have hdist' : α - (a : ℝ) / (q : ℝ) < 1 / ((q : ℝ) * Q) :=
      (le_abs_self _).trans_lt hdist
    linarith
  have ha_lt_q : a < (q : ℤ) := by
    by_contra hage
    push Not at hage
    have ha_ge_q : (1 : ℝ) ≤ (a : ℝ) / (q : ℝ) := by
      rw [one_le_div hq_pos]
      exact_mod_cast hage
    have hgap : 1 / ((q : ℝ) * Q) ≤ (a : ℝ) / (q : ℝ) - α := by
      have hq1 : 1 / ((q : ℝ) * Q) ≤ 1 / Q := by
        rw [div_le_div_iff₀ (mul_pos hq_pos hQ_pos) hQ_pos]
        nlinarith [show (1 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq_ge1]
      linarith [hα_Icc.2]
    have hdist' : (a : ℝ) / (q : ℝ) - α < 1 / ((q : ℝ) * Q) := by
      rw [← abs_sub_comm] at hdist
      exact (le_abs_self _).trans_lt hdist
    linarith
  have htoNat_eq : a.toNat = a.natAbs := Int.ofNat.inj
    ((Int.toNat_of_nonneg ha_nonneg).trans (Int.natAbs_of_nonneg ha_nonneg).symm)
  apply hα_not
  simp only [majorArcsFixed, Set.mem_iUnion, exists_prop]
  refine ⟨q, ?_, a.toNat, ?_, ?_⟩
  · simp only [majorArcDenoms, Finset.mem_Icc]
    exact ⟨hq_ge1, Nat.le_floor hleP⟩
  · simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · exact_mod_cast (show (a.toNat : ℤ) < (q : ℤ) by
        rw [Int.toNat_of_nonneg ha_nonneg]; exact ha_lt_q)
    · rw [htoNat_eq]
      exact hcop
  · rw [mem_majorArcFixed_iff]
    have hle_Q : 1 / ((q : ℝ) * Q) ≤ 1 / Q := by
      rw [div_le_div_iff₀ (mul_pos hq_pos hQ_pos) hQ_pos]
      nlinarith [show (1 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq_ge1]
    simpa [Int.toNat_of_nonneg ha_nonneg] using hdist.le.trans hle_Q

/-- Major-arc contribution on `majorArcsFixed P Q`. -/
def majorArcIntegralFixed (f : ℝ → ℂ) (P Q : ℝ) : ℂ :=
  ∫ α in majorArcsFixed P Q, f α

/-- Minor-arc contribution on `minorArcsFixed P Q`. -/
def minorArcIntegralFixed (f : ℝ → ℂ) (P Q : ℝ) : ℂ :=
  ∫ α in minorArcsFixed P Q, f α

/-- Integral decomposition for fixed-width major and minor arcs when `1 ≤ P` and `2 * P ^ 2 < Q`. -/
theorem representationIntegral_eq_majorArcIntegralFixed_add_minorArcIntegralFixed
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) {P Q : ℝ} (hP : 1 ≤ P) (hPQ : 2 * P ^ 2 < Q)
    (hint : IntegrableOn f (Set.Icc (-(1 / Q)) (1 - 1 / Q))) :
    representationIntegral f =
      majorArcIntegralFixed f P Q + minorArcIntegralFixed f P Q := by
  have hshift : representationIntegral f = ∫ α in Set.Icc (-(1 / Q)) (1 - 1 / Q), f α := by
    rw [representationIntegral_eq_setIntegral_Icc hf (-(1 / Q)), sub_eq_add_neg]
  rw [hshift, majorArcIntegralFixed, minorArcIntegralFixed,
    ← MeasureTheory.setIntegral_union (disjoint_majorArcsFixed_minorArcsFixed P Q)
      (measurableSet_minorArcsFixed P Q)
      (hint.mono_set (majorArcsFixed_subset_Icc hP hPQ))
      (hint.mono_set (minorArcsFixed_subset_Icc P Q)),
    majorArcsFixed_union_minorArcsFixed hP hPQ]

/-- Fixed-width major-arc sum decomposition when `2 * P ^ 2 < Q`. -/
theorem majorArcIntegralFixed_eq_sum {f : ℝ → ℂ} {P Q : ℝ} (hPQ : 2 * P ^ 2 < Q)
    (hint : IntegrableOn f (majorArcsFixed P Q)) :
    majorArcIntegralFixed f P Q =
      ∑ q ∈ majorArcDenoms P,
        ∑ a ∈ coprimeResidues q, ∫ α in majorArcFixed q (a : ℤ) Q, f α := by
  have hint_arc : ∀ q ∈ majorArcDenoms P, ∀ a ∈ coprimeResidues q,
      IntegrableOn f (majorArcFixed q (a : ℤ) Q) := by
    intro q hq a ha
    refine hint.mono_set fun α hα => ?_
    simp only [majorArcsFixed, Set.mem_iUnion, exists_prop]
    exact ⟨q, hq, a, ha, hα⟩
  have houter :
      (∫ α in majorArcsFixed P Q, f α) =
        ∑ q ∈ majorArcDenoms P,
          ∫ α in ⋃ a ∈ coprimeResidues q, majorArcFixed q (a : ℤ) Q, f α := by
    refine MeasureTheory.integral_biUnion_finset (majorArcDenoms P) ?_ ?_ ?_
    · intro q _
      exact Finset.measurableSet_biUnion (coprimeResidues q) fun a _ =>
        measurableSet_majorArcFixed q a Q
    · intro q₁ hq₁ q₂ hq₂ hne
      change Disjoint (⋃ a ∈ coprimeResidues q₁, majorArcFixed q₁ (a : ℤ) Q)
        (⋃ a ∈ coprimeResidues q₂, majorArcFixed q₂ (a : ℤ) Q)
      rw [Set.disjoint_iUnion₂_left]
      intro a₁ ha₁
      rw [Set.disjoint_iUnion₂_right]
      intro a₂ ha₂
      exact majorArcFixed_disjoint_range hq₁ ha₁ hq₂ ha₂ hPQ (fun h => hne (congrArg Prod.fst h))
    · intro q hq
      exact MeasureTheory.integrableOn_finset_iUnion.mpr fun a ha => hint_arc q hq a ha
  rw [majorArcIntegralFixed, houter]
  refine Finset.sum_congr rfl fun q hq => ?_
  refine MeasureTheory.integral_biUnion_finset (coprimeResidues q) ?_ ?_ ?_
  · intro a _
    exact measurableSet_majorArcFixed q a Q
  · intro a₁ ha₁ a₂ ha₂ hne
    exact majorArcFixed_disjoint_range hq ha₁ hq ha₂ hPQ (fun h => hne (congrArg Prod.snd h))
  · intro a ha
    exact hint_arc q hq a ha

/-- Change of variables `α = a / q + β` on a fixed-width major arc `majorArcFixed q a Q`. -/
theorem setIntegral_majorArcFixed_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {q : ℕ} (_hq : 1 ≤ q) (a : ℤ) {Q : ℝ} (_hQ : 0 < Q) :
    ∫ α in majorArcFixed q a Q, f α =
      ∫ β in (-(1 / Q))..(1 / Q), f ((a : ℝ) / (q : ℝ) + β) := by
  have hle : (a : ℝ) / (q : ℝ) - 1 / Q ≤ (a : ℝ) / (q : ℝ) + 1 / Q := by
    have : 0 ≤ 1 / Q := by positivity
    linarith
  rw [majorArcFixed, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_comp_add_left f ((a : ℝ) / (q : ℝ))]
  congr 1

/-- Minor-arc bound on `minorArcsFixed P Q` given an explicit bound `‖F α‖ ≤ M`. -/
theorem norm_minorArcIntegralFixed_mul_pow_e_neg_le_of_bound {F G : ℝ → ℂ}
    (hF_cont : Continuous F) (hG_cont : Continuous G) (hG_per : Function.Periodic G 1)
    {P Q M : ℝ} (hM : 0 ≤ M) (hF_bd : ∀ α ∈ minorArcsFixed P Q, ‖F α‖ ≤ M) (s : ℕ) (N : ℤ) :
    ‖∫ α in minorArcsFixed P Q, F α * G α ^ (s - 1) * e (-α * (N : ℝ))‖ ≤
      M * ∫ α in (0 : ℝ)..1, ‖G α‖ ^ (s - 1) := by
  have heq_integrand :
      (fun α : ℝ => F α * G α ^ (s - 1) * e (-α * (N : ℝ))) =
        fun α : ℝ => F α * (G α ^ (s - 1) * e (-α * (N : ℝ))) := by
    ext α; ring
  have hH_per : Function.Periodic (fun α : ℝ => G α ^ (s - 1) * e (-α * (N : ℝ))) 1 := by
    intro α
    dsimp only
    rw [hG_per α]
    have hneg : -(α + 1) * (N : ℝ) = -α * (N : ℝ) + ((-N : ℤ) : ℝ) := by push_cast; ring
    rw [hneg, e_add_intCast]
  have hH_cont : Continuous (fun α : ℝ => G α ^ (s - 1) * e (-α * (N : ℝ))) :=
    (hG_cont.pow (s - 1)).mul
      (continuous_e.comp ((continuous_neg.comp continuous_id).mul continuous_const))
  have hFH_cont : Continuous (fun α : ℝ => F α * (G α ^ (s - 1) * e (-α * (N : ℝ)))) :=
    hF_cont.mul hH_cont
  have hH_norm :
      (fun α : ℝ => ‖G α ^ (s - 1) * e (-α * (N : ℝ))‖) = fun α : ℝ => ‖G α‖ ^ (s - 1) := by
    ext α
    rw [norm_mul, norm_pow, norm_e, mul_one]
  rw [heq_integrand]
  have hres := norm_setIntegral_mul_le_of_bound (measurableSet_minorArcsFixed P Q)
    (minorArcsFixed_subset_Icc P Q) hM hF_bd
    (hFH_cont.continuousOn.integrableOn_Icc.mono_set (minorArcsFixed_subset_Icc P Q))
    (hH_cont.norm.continuousOn.integrableOn_Icc)
    hH_per
  simpa [hH_norm] using hres

/-- Scaled major arcs are disjoint whenever `0 < P` and `2 * P ^ 2 ≤ N`. -/
theorem majorArcScaled_disjoint {P N : ℝ} {q₁ q₂ a₁ a₂ : ℕ}
    (hq₁ : q₁ ∈ majorArcDenoms P) (ha₁ : a₁ ∈ coprimeResidues q₁)
    (hq₂ : q₂ ∈ majorArcDenoms P) (ha₂ : a₂ ∈ coprimeResidues q₂)
    (hP_pos : 0 < P) (hPN : 2 * P ^ 2 ≤ N) (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (majorArcScaled q₁ (a₁ : ℤ) P N) (majorArcScaled q₂ (a₂ : ℤ) P N) := by
  have hPQ : 2 * P ≤ N / P := (le_div_iff₀ hP_pos).mpr (by nlinarith)
  exact majorArc_disjoint hq₁ ha₁ hq₂ ha₂ hPQ hne

/-- Measurable partition for scaled major/minor arcs when `1 ≤ P` and `2 * P ^ 2 ≤ N`. -/
theorem majorArcsScaled_union_minorArcsScaled {P N : ℝ} (hP : 1 ≤ P) (hPN : 2 * P ^ 2 ≤ N) :
    majorArcsScaled P N ∪ minorArcsScaled P N = Set.Icc (-(P / N)) (1 - P / N) := by
  have hP_pos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hPQ : 2 * P ≤ N / P := (le_div_iff₀ hP_pos).mpr (by nlinarith)
  simpa [majorArcsScaled, minorArcsScaled, one_div_div] using
    majorArcs_union_minorArcs hP hPQ

/-- Dirichlet approximation characterization on `minorArcsScaled P N` when `1 ≤ P` and
`2 * P ^ 2 ≤ N`. -/
theorem mem_minorArcsScaled_approx {P N α : ℝ} (hP : 1 ≤ P) (hPN : 2 * P ^ 2 ≤ N)
    (hα : α ∈ minorArcsScaled P N) :
    ∃ (a : ℤ) (q : ℕ),
      P < (q : ℝ) ∧ (q : ℝ) ≤ N / P ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / (q : ℝ)| ≤ P / ((q : ℝ) * N) := by
  have hP_pos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hPQ : 2 * P ≤ N / P := (le_div_iff₀ hP_pos).mpr (by nlinarith)
  obtain ⟨a, q, hPq, hqNP, hcop, hdist⟩ := mem_minorArcs_approx hP hPQ hα
  refine ⟨a, q, hPq, hqNP, hcop, ?_⟩
  have heq : 1 / ((q : ℝ) * (N / P)) = P / ((q : ℝ) * N) := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := lt_trans hP_pos hPq
    have hN_pos : 0 < N := by nlinarith
    field_simp [hq_pos.ne', hN_pos.ne', hP_pos.ne']
  rwa [heq] at hdist

end FixedWidthAndScaledVariants

end IntegralDecompositionAndBounds

end AnalyticNumberTheory.AdditiveNumberTheory
