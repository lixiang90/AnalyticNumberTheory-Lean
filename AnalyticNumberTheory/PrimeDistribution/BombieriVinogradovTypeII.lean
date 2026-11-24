import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovBilinear
import AnalyticNumberTheory.ExponentialSums.VaughanIdentity

/-!
# The Type II mean value in Bombieri–Vinogradov

Dyadic rectangles localize the two factors in Vaughan's identity. Inside an
active rectangle their lengths have product at most the von Mangoldt cutoff.
-/

noncomputable section

open Finset
open scoped Classical ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.PrimeDistribution

/-- The Type II character sum in Vaughan's identity with equal splitting parameters. -/
def vaughanTypeIICharacter (X U : ℕ) (q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  cutoffCharacterBilinear (Ioc U (X/U)) (Ioc U X)
    (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun n => (Λ n : ℂ)) (fun m => X/m) q χ

private lemma dyadic_shape {m i : ℕ} (hm : 0 < m) (hi : Nat.log 2 m = i) :
    2^i ≤ m ∧ m < 2^i * 2 := by
  subst i
  exact ⟨Nat.pow_log_le_self 2 hm.ne', by simpa [pow_succ] using Nat.lt_pow_succ_log_self one_lt_two m⟩

private lemma dyadic_sieve_factor {M N Q U X : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hQ : 0 ≤ Q) (hU : 0 < U) (hMN : M*N ≤ X) (hUM : U ≤ 2*M) (hUN : U ≤ 2*N) :
    Real.sqrt (M+Q^2) * Real.sqrt (N+Q^2) * (Real.sqrt M * Real.sqrt N) ≤
      4 * (X + Q^2 * Real.sqrt X + Q * X / Real.sqrt U) := by
  have hX : 0 ≤ X := (mul_nonneg hM hN).trans hMN
  have hsu := Real.sqrt_pos.mpr hU
  have hsm := Real.sq_sqrt hM
  have hsn := Real.sq_sqrt hN
  have hsU := Real.sq_sqrt hU.le
  have hsM : Real.sqrt U ≤ 2*Real.sqrt M := by
    nlinarith only [hUM, hsU, hsm, hM, Real.sqrt_nonneg U, Real.sqrt_nonneg M,
      sq_nonneg (Real.sqrt U - 2*Real.sqrt M)]
  have hsN : Real.sqrt U ≤ 2*Real.sqrt N := by
    nlinarith only [hUN, hsU, hsn, hN, Real.sqrt_nonneg U, Real.sqrt_nonneg N,
      sq_nonneg (Real.sqrt U - 2*Real.sqrt N)]
  have hs (t : ℝ) (ht : 0 ≤ t) : Real.sqrt (t+Q^2) ≤ Real.sqrt t + Q := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ht, mul_nonneg (Real.sqrt_nonneg t) hQ]
  have hroot : Real.sqrt M * Real.sqrt N ≤ Real.sqrt X := by
    rw [← Real.sqrt_mul hM]; exact Real.sqrt_le_sqrt hMN
  have hcross (m n : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hu : Real.sqrt U ≤ 2*m)
      (hmn : m^2 * n^2 ≤ X) : m*n^2 ≤ 2*X / Real.sqrt U := by
    apply (le_div_iff₀ hsu).mpr
    calc
      _ ≤ m * n^2 * (2*m) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = 2*(m^2*n^2) := by ring
      _ ≤ _ := by linarith
  have h1 := hcross _ _ (Real.sqrt_nonneg M) (Real.sqrt_nonneg N) hsM (by rwa [hsm, hsn])
  have h2 := hcross _ _ (Real.sqrt_nonneg N) (Real.sqrt_nonneg M) hsN (by rwa [hsm, hsn, mul_comm])
  calc
    _ ≤ (Real.sqrt M+Q) * (Real.sqrt N+Q) * (Real.sqrt M * Real.sqrt N) := by gcongr <;> apply hs <;> assumption
    _ = M*N + Q^2*(Real.sqrt M * Real.sqrt N) +
        Q * (Real.sqrt M*(Real.sqrt N)^2 + Real.sqrt N*(Real.sqrt M)^2) := by
      rw [← hsm, ← hsn] at ⊢
      ring_nf
      simp [Real.sqrt_sq (Real.sqrt_nonneg _)]
      ring
    _ ≤ X + Q^2*Real.sqrt X + Q*(2*X / Real.sqrt U + 2*X / Real.sqrt U) :=
      add_le_add (add_le_add hMN (mul_le_mul_of_nonneg_left hroot (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hQ)
    _ = X + Q^2*Real.sqrt X + 4*(Q*X / Real.sqrt U) := by ring
    _ ≤ _ := by linarith only [hX, mul_nonneg (sq_nonneg Q) (Real.sqrt_nonneg X)]

private lemma row_energy {S : Finset ℕ} {U M X : ℕ} (hM : 1 ≤ M) (hMX : M ≤ X)
    (hS : S ⊆ Icc 1 (2*M)) :
    coefficientEnergy S (fun m => (vaughanTypeIICoeff U m : ℂ)) ≤
      (2 * (M : ℝ)) * (1 + Real.log (2*(X : ℝ)))^3 := by
  have hcoeff := calc
    coefficientEnergy S (fun m => (vaughanTypeIICoeff U m : ℂ)) ≤ ∑ m ∈ S, ((m.divisors.card : ℝ))^2 := by
      refine sum_le_sum fun m _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_vaughanTypeIICoeff_le_divisors U m) 2
    _ ≤ ∑ m ∈ Icc 1 (2*M), ((m.divisors.card : ℝ))^2 := sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => sq_nonneg _
    _ ≤ _ := sum_Icc_card_divisors_sq_le (2*M)
  apply hcoeff.trans
  rw [max_eq_left (by omega)]
  push_cast
  have hm := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*M by omega) : 1 ≤ 2*(M:ℝ))
  gcongr

private lemma column_energy {T : Finset ℕ} {N X : ℕ} (hN : 1 ≤ N) (hNX : N ≤ X)
    (hT : T ⊆ Icc 1 (2*N)) :
    coefficientEnergy T (fun n => (Λ n : ℂ)) ≤
      (2 * (N : ℝ)) * (1 + Real.log (2*(X : ℝ)))^2 := by
  have hx : 1 ≤ (2*(X:ℝ)) := by exact_mod_cast (show 1 ≤ 2*X by omega)
  have hc := calc
    coefficientEnergy T (fun n => (Λ n : ℂ)) ≤ ∑ n ∈ T, (1 + Real.log (2*(X:ℝ)))^2 := by
      refine sum_le_sum fun n hn => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      apply pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
      have hn' := mem_Icc.mp (hT hn)
      apply ArithmeticFunction.vonMangoldt_le_log.trans
      exact (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast (show n ≤ 2*X by omega) : (n:ℝ) ≤ 2*(X:ℝ))).trans
        (by linarith)
    _ ≤ ∑ n ∈ Icc 1 (2*N), (1 + Real.log (2*(X:ℝ)))^2 :=
      sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => sq_nonneg _
  simpa [Nat.card_Icc] using hc

private lemma energy_product {S T : Finset ℕ} {U M N X : ℕ}
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hMX : M ≤ X) (hNX : N ≤ X)
    (hS : S ⊆ Icc 1 (2*M)) (hT : T ⊆ Icc 1 (2*N)) :
    Real.sqrt (coefficientEnergy S (fun m => (vaughanTypeIICoeff U m : ℂ))) *
    Real.sqrt (coefficientEnergy T (fun n => (Λ n : ℂ))) ≤
      2 * (Real.sqrt M * Real.sqrt N) * (1 + Real.log (2*(X:ℝ)))^3 := by
  let L := 1 + Real.log (2*(X:ℝ))
  have hl : 1 ≤ L := by
    dsimp [L]; linarith [Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*X by omega) : 1 ≤ 2*(X:ℝ))]
  have hL := (show 0 ≤ L by linarith)
  have hE := mul_le_mul (Real.sqrt_le_sqrt (row_energy (U:=U) hM hMX hS))
    (Real.sqrt_le_sqrt (column_energy hN hNX hT)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply hE.trans
  change Real.sqrt (2*M*L^3) * Real.sqrt (2*N*L^2) ≤ 2*(Real.sqrt M*Real.sqrt N)*L^3
  rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_left (by positivity)]
  have hpow : L^5 ≤ L^6 := pow_le_pow_right₀ hl (by decide)
  calc
    _ = (4*M*N)*L^5 := by ring
    _ ≤ (4*M*N)*L^6 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring_nf; rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]; ring

private def dyadicPart (S : Finset ℕ) (i : ℕ) := S.filter (fun n => Nat.log 2 n = i)

private lemma dyadicPart_bounds {S : Finset ℕ} {X i : ℕ} (hS : S ⊆ Icc 1 X) {n : ℕ}
    (hn : n ∈ dyadicPart S i) : 2^i ≤ n ∧ n < 2^i * 2 :=
  dyadic_shape (mem_Icc.mp (hS (mem_filter.mp hn).1)).1 (mem_filter.mp hn).2

private theorem typeII_block {X U Q : ℕ} (hX : 1 ≤ X) (hU : 1 ≤ U) (hQ : 1 ≤ Q)
    {S T : Finset ℕ} (hS : S ⊆ Ioc U X) (hT : T ⊆ Ioc U X)
    (i j : ℕ) (hj : j ≤ Nat.log 2 X) :
    primitiveCharacterMean Q (cutoffCharacterBilinear (dyadicPart S i) (dyadicPart T j)
      (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun n => (Λ n : ℂ)) (fun m => X/m)) ≤
      8 * (Nat.log 2 X + 1 : ℝ) * (1 + Real.log (2*(X:ℝ)))^3 *
      ((X:ℝ) + (Q:ℝ)^2 * Real.sqrt X + (Q:ℝ) * X / Real.sqrt U) := by
  let M := 2^i
  let N := 2^j
  let R := dyadicPart S i
  let C := dyadicPart T j
  let L := 1 + Real.log (2*(X:ℝ))
  have hL : 0 ≤ L := by
    have hx : 1 ≤ 2*(X:ℝ) := by exact_mod_cast (show 1 ≤ 2*X by omega)
    dsimp [L]; linarith [Real.log_nonneg hx]
  have hS' : S ⊆ Icc 1 X := fun n hn => by have := mem_Ioc.mp (hS hn); apply mem_Icc.mpr; omega
  have hT' : T ⊆ Icc 1 X := fun n hn => by have := mem_Ioc.mp (hT hn); apply mem_Icc.mpr; omega
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  have hN : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
  have hrow : R ⊆ Ioc (M-1) (M-1+M) := by
    intro n hn
    have hh : M ≤ n ∧ n < M*2 := dyadicPart_bounds hS' hn
    apply mem_Ioc.mpr; omega
  have hcol : C ⊆ Ioc (N-1) (N-1+N) := by
    intro n hn
    have hh : N ≤ n ∧ n < N*2 := dyadicPart_bounds hT' hn
    apply mem_Ioc.mpr; omega
  by_cases active : ∃ m ∈ R, ∃ n ∈ C, n ≤ X/m
  · obtain ⟨m, hm, n, hn, hcut⟩ := active
    have hms := mem_Ioc.mp (hS (mem_filter.mp hm).1)
    have hns := mem_Ioc.mp (hT (mem_filter.mp hn).1)
    have hmM : M ≤ m ∧ m < M*2 := dyadicPart_bounds hS' hm
    have hnN : N ≤ n ∧ n < N*2 := dyadicPart_bounds hT' hn
    have hMN : M*N ≤ X := (Nat.mul_le_mul hmM.1 hnN.1).trans
      (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega : 0<m)).mp hcut)
    have he := energy_product (U:=U) hM hN (hmM.1.trans hms.2) (hnN.1.trans hns.2)
      (show R ⊆ Icc 1 (2*M) by intro t ht; have := mem_Ioc.mp (hrow ht); apply mem_Icc.mpr; omega)
      (show C ⊆ Icc 1 (2*N) by intro t ht; have := mem_Ioc.mp (hcol ht); apply mem_Icc.mpr; omega)
    have hs := primitiveCharacterMean_cutoff_pow_two hQ hM j (N-1) hrow hcol
      (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun n => (Λ n : ℂ)) (fun m => X/m)
    have hfactor := dyadic_sieve_factor (X := (X:ℝ)) (Nat.cast_nonneg M) (Nat.cast_nonneg N) (Nat.cast_nonneg Q)
      (by exact_mod_cast hU : (0:ℝ) < U) (by exact_mod_cast hMN)
      (by exact_mod_cast (show U ≤ 2*M by omega)) (by exact_mod_cast (show U ≤ 2*N by omega))
    let F := Real.sqrt ((M:ℝ)+(Q:ℝ)^2) * Real.sqrt ((N:ℝ)+(Q:ℝ)^2)
    let E := Real.sqrt (M:ℝ) * Real.sqrt (N:ℝ)
    let Z := (X:ℝ) + (Q:ℝ)^2 * Real.sqrt X + (Q:ℝ) * X / Real.sqrt U
    change F * E ≤ 4 * Z at hfactor
    change _ ≤ 2*E*L^3 at he
    apply hs.trans
    calc
      _ ≤ (j+1:ℝ)*F * (2*E*L^3) := mul_le_mul_of_nonneg_left he (by dsimp [F]; positivity)
      _ = (2*(j+1:ℝ)*L^3) * (F*E) := by ring
      _ ≤ (2*(Nat.log 2 X+1:ℝ)*L^3) * (4*Z) := by
        have hZ : 0 ≤ Z := by dsimp [Z]; positivity
        apply mul_le_mul _ hfactor (by dsimp [F,E]; positivity) (by positivity)
        gcongr
      _ = _ := by dsimp only [L,Z]; ring
  · have hz (q : ℕ) (χ : DirichletCharacter ℂ q) :
        cutoffCharacterBilinear R C (fun m => (vaughanTypeIICoeff U m : ℂ))
          (fun n => (Λ n : ℂ)) (fun m => X/m) q χ = 0 := by
      apply sum_eq_zero
      intro m hm
      have he : C.filter (· ≤ X/m) = ∅ :=
        filter_eq_empty_iff.mpr fun n hn hcut => active ⟨m, hm, n, hn, hcut⟩
      simp [characterPolynomial, he]
    have hfun : cutoffCharacterBilinear R C (fun m => (vaughanTypeIICoeff U m : ℂ))
        (fun n => (Λ n : ℂ)) (fun m => X/m) = fun _ _ => 0 := funext fun q => funext (hz q)
    rw [show dyadicPart S i = R from rfl, show dyadicPart T j = C from rfl, hfun]
    simp only [primitiveCharacterMean, norm_zero, mul_zero, sum_const_zero]
    change 0 ≤ 8 * _ * L^3 * _
    positivity

private theorem cutoff_dyadic_expansion {S T : Finset ℕ} {X : ℕ} (hS : S ⊆ Icc 1 X)
    (hT : T ⊆ Icc 1 X) (a b : ℕ → ℂ) (c : ℕ → ℕ) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ i ∈ range (Nat.log 2 X+1), ∑ j ∈ range (Nat.log 2 X+1),
      cutoffCharacterBilinear (dyadicPart S i) (dyadicPart T j) a b c q χ) =
      cutoffCharacterBilinear S T a b c q χ := by
  let J := range (Nat.log 2 X+1)
  have hmap (D : Finset ℕ) (hD : D ⊆ Icc 1 X) : ∀ n ∈ D, Nat.log 2 n ∈ J :=
    fun n hn => mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp (hD hn)).2))
  have cols (m : ℕ) (j : ℕ) :
      characterPolynomial ((dyadicPart T j).filter (· ≤ c m)) b q χ =
      ∑ n ∈ dyadicPart T j, if n ≤ c m then b n * χ n else 0 := by
    rw [characterPolynomial, sum_filter]
  unfold cutoffCharacterBilinear
  apply Eq.trans _ (sum_fiberwise_of_maps_to (hmap S hS) _)
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  simp_rw [← mul_sum, cols]
  congr 1
  rw [characterPolynomial, sum_filter]
  exact sum_fiberwise_of_maps_to (hmap T hT) _

/-- Explicit Type II first moment for all primitive characters of modulus at most `Q`.
The logarithmic factor counts dyadic blocks, the inner cutoff, and the coefficient energies. -/
theorem primitiveCharacterMean_vaughanTypeII_dyadic {X U Q : ℕ} (hX : 1 ≤ X)
    (hU : 1 ≤ U) (hQ : 1 ≤ Q) :
    primitiveCharacterMean Q (vaughanTypeIICharacter X U) ≤
      8 * (Nat.log 2 X+1 : ℝ)^3 * (1 + Real.log (2*(X:ℝ)))^3 *
      ((X:ℝ) + (Q:ℝ)^2 * Real.sqrt X + (Q:ℝ) * X / Real.sqrt U) := by
  let S := Ioc U (X/U)
  let T := Ioc U X
  let J := range (Nat.log 2 X+1)
  let F := fun i j => cutoffCharacterBilinear (dyadicPart S i) (dyadicPart T j)
    (fun m => (vaughanTypeIICoeff U m : ℂ)) (fun n => (Λ n : ℂ)) (fun m => X/m)
  have hS : S ⊆ Ioc U X := fun n hn => mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans (Nat.div_le_self ..)⟩
  have hcover : vaughanTypeIICharacter X U = fun q χ => ∑ i ∈ J, ∑ j ∈ J, F i j q χ := by
    funext q χ
    apply (cutoff_dyadic_expansion _ _ _ _ _ _ _).symm
    · intro n hn; have := mem_Ioc.mp (hS hn); apply mem_Icc.mpr; omega
    · intro n hn; have := mem_Ioc.mp hn; apply mem_Icc.mpr; omega
  rw [hcover]
  apply (primitiveCharacterMean_sum_le Q J _).trans
  apply (sum_le_sum (fun i _ => primitiveCharacterMean_sum_le Q J (F i))).trans
  apply (sum_le_sum (fun i (_ : i ∈ J) => sum_le_sum (fun j (hj : j ∈ J) =>
    typeII_block hX hU hQ hS (Subset.rfl : T ⊆ Ioc U X) i j (Nat.le_of_lt_succ (mem_range.mp hj))))).trans_eq
  simp only [J, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

private lemma log_dyadic_count_le {X : ℕ} (hX : 1 ≤ X) :
    (Nat.log 2 X + 1 : ℝ) ≤ 2 * (1 + Real.log X) := by
  have hpow : (2 : ℝ) ^ (Nat.log 2 X) ≤ X := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : X ≠ 0)
  have h := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at h
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith only [mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 X)), h]

/-- The Type II mean with one ordinary sixth power of a logarithm. -/
theorem primitiveCharacterMean_vaughanTypeII {X U Q : ℕ} (hX : 1 ≤ X) (hU : 1 ≤ U) (hQ : 1 ≤ Q) :
    primitiveCharacterMean Q (vaughanTypeIICharacter X U) ≤
      512 * (1+Real.log X)^6 *
      ((X:ℝ) + (Q:ℝ)^2 * Real.sqrt X + (Q:ℝ) * X / Real.sqrt U) := by
  apply (primitiveCharacterMean_vaughanTypeII_dyadic hX hU hQ).trans
  have hx : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hX0 : (0:ℝ) < X := by exact_mod_cast hX
  have hL : 1+Real.log (2*(X:ℝ)) ≤ 2*(1+Real.log X) := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hL0 : 0 ≤ 1+Real.log (2*(X:ℝ)) := by
    have := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*X by omega) : 1 ≤ 2*(X:ℝ))
    linarith
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    _ ≤ 8 * (2*(1+Real.log X))^3 * (2*(1+Real.log X))^3 := by
      gcongr
      exact log_dyadic_count_le hX
    _ = _ := by ring

/-- Contribution of the Type II sum from conductors exceeding `R`, with the
`1/φ(q)` weight that occurs after passage to primitive characters. -/
theorem sum_largeConductor_vaughanTypeII_le {X U Q : ℕ} (hX : 1 ≤ X) (hU : 1 ≤ U)
    (hQ : 1 ≤ Q) {R : ℝ} (hR : 0 < R) :
    ∑ q ∈ (Icc 2 Q).filter (fun q : ℕ => R < (q:ℝ)), (q.totient:ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
        ‖vaughanTypeIICharacter X U q χ‖ ≤
      4096 * (1+Real.log Q) * (1+Real.log X)^6 *
        ((X:ℝ)/R + Q * Real.sqrt X + (X:ℝ)/Real.sqrt U) := by
  let D := (Icc 2 Q).filter (fun q : ℕ => R < (q:ℝ))
  let J := range (Nat.log 2 Q+1)
  let A (q : ℕ) := ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
    ‖vaughanTypeIICharacter X U q χ‖
  let L := (1+Real.log X)^6
  let Z := (X:ℝ)/R + Q * Real.sqrt X + (X:ℝ)/Real.sqrt U
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hA (q : ℕ) : 0 ≤ A q := sum_nonneg fun _ _ => norm_nonneg _
  change (∑ q ∈ D, (q.totient:ℝ)⁻¹ * A q) ≤ _
  have hj (q : ℕ) (hq : q ∈ D) : Nat.log 2 q ∈ J :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp (mem_filter.mp hq).1).2))
  rw [← sum_fiberwise_of_maps_to hj]
  have hblock (j : ℕ) (_hj : j ∈ J) :
      ∑ q ∈ D.filter (fun q => Nat.log 2 q = j), (q.totient:ℝ)⁻¹ * A q ≤ 2048*L*Z := by
    let d := 2^j
    let H := D.filter (fun q => Nat.log 2 q = j)
    have hd : 0 < d := Nat.pow_pos (by decide : 0 < 2)
    have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
    by_cases hn : H.Nonempty
    · obtain ⟨n, hn⟩ := hn
      have hnD : n ∈ D := (mem_filter.mp hn).1
      have hnr := (mem_filter.mp hnD).2
      have hnn := mem_Icc.mp (mem_filter.mp hnD).1
      have hdn : d ≤ n ∧ n < d*2 := dyadic_shape (by omega) (mem_filter.mp hn).2
      have hR2 : R ≤ (d:ℝ)*2 := hnr.le.trans (by exact_mod_cast hdn.2.le)
      have hdQ : (d:ℝ) ≤ Q := by exact_mod_cast hdn.1.trans hnn.2
      have hsub : H ⊆ Icc 1 (2*d) := by
        intro q hq
        have hD : q ∈ D := (mem_filter.mp hq).1
        have hq' := mem_Icc.mp (mem_filter.mp hD).1
        have hqd : d ≤ q ∧ q < d*2 := dyadic_shape (by omega) (mem_filter.mp hq).2
        apply mem_Icc.mpr; omega
      have hmoment := primitiveCharacterMean_vaughanTypeII hX hU (show 1 ≤ 2*d by omega)
      change primitiveCharacterMean (2*d) _ ≤ 512 * L * _ at hmoment
      unfold primitiveCharacterMean primitiveCharacterFamily at hmoment
      rw [sum_sigma] at hmoment
      simp_rw [← mul_sum] at hmoment
      change ∑ q ∈ Icc 1 (2*d), ((q:ℝ)/q.totient) * A q ≤ _ at hmoment
      have hsum : (d:ℝ) * (∑ q ∈ H, (q.totient:ℝ)⁻¹ * A q) ≤
          ∑ q ∈ Icc 1 (2*d), ((q:ℝ)/q.totient) * A q := by
        rw [mul_sum]
        apply (sum_le_sum (g := fun q : ℕ => ((q:ℝ)/q.totient)*A q) _).trans
        · exact sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => mul_nonneg (by positivity) (hA q)
        · intro q hq
          have hD : q ∈ D := (mem_filter.mp hq).1
          have hq' := mem_Icc.mp (mem_filter.mp hD).1
          have hqd : d ≤ q ∧ q < d*2 := dyadic_shape (by omega) (mem_filter.mp hq).2
          rw [← mul_assoc, ← div_eq_mul_inv]
          gcongr
          exact_mod_cast hqd.1
      calc
        _ ≤ (512*L*((X:ℝ) + ((2*d:ℕ):ℝ)^2*Real.sqrt X + ((2*d:ℕ):ℝ)*X/Real.sqrt U)) / d :=
          (le_div_iff₀ hdr).mpr (by simpa [mul_comm] using hsum.trans hmoment)
        _ ≤ _ := by
          have hX := Nat.cast_nonneg (α:=ℝ) X
          have hratio : (X:ℝ)/d ≤ 2*((X:ℝ)/R) := by
            rw [div_le_iff₀ hdr, mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc, le_div_iff₀ hR]
            nlinarith only [mul_le_mul_of_nonneg_left hR2 hX]
          have hmid := mul_le_mul_of_nonneg_right hdQ (Real.sqrt_nonneg X)
          have htail : 0 ≤ (X:ℝ)/Real.sqrt U := by positivity
          have hprim : ((X:ℝ) + ((2*d:ℕ):ℝ)^2*Real.sqrt X + ((2*d:ℕ):ℝ)*X/Real.sqrt U) / d ≤ 4*Z := by
            push_cast
            calc
              _ = X/(d:ℝ) + 4*((d:ℝ)*Real.sqrt X) + 2*((X:ℝ)/Real.sqrt U) := by
                field_simp [hdr.ne']; ring
              _ ≤ _ := by dsimp [Z]; linarith [div_nonneg hX hR.le]
          rw [mul_div_assoc]
          calc
            _ ≤ 512*L*(4*Z) := mul_le_mul_of_nonneg_left hprim (by positivity)
            _ = _ := by ring
    · rw [show D.filter (fun q => Nat.log 2 q = j) = ∅ from not_nonempty_iff_eq_empty.mp hn, sum_empty]
      positivity
  apply (sum_le_sum hblock).trans
  simp only [J, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  apply (mul_le_mul_of_nonneg_right (log_dyadic_count_le hQ) (by positivity : 0 ≤ 2048*L*Z)).trans_eq
  dsimp only [L,Z]; ring

end AnalyticNumberTheory.PrimeDistribution
