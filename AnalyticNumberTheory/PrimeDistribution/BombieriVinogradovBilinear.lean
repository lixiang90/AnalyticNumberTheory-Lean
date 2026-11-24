import AnalyticNumberTheory.SieveMethods.LargeSieve

/-!
# Bilinear large sieve for primitive Dirichlet characters

This file develops the mean-value estimates used for the Type II terms in
Vaughan's decomposition of the von Mangoldt function.
-/

noncomputable section

open Finset
open scoped Classical
open AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.PrimeDistribution

/-- The finite family of primitive characters used by the multiplicative large sieve. -/
def primitiveCharacterFamily (Q : ℕ) : Finset ((q : ℕ) × DirichletCharacter ℂ q) :=
  (Icc 1 Q).sigma fun q => univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive

/-- The first absolute moment with the usual multiplicative large sieve weight. -/
def primitiveCharacterMean (Q : ℕ) (F : (q : ℕ) → DirichletCharacter ℂ q → ℂ) : ℝ :=
  ∑ p ∈ primitiveCharacterFamily Q, ((p.1 : ℝ) / p.1.totient) * ‖F p.1 p.2‖

private lemma mean_mono {Q : ℕ} {F G : (q : ℕ) → DirichletCharacter ℂ q → ℂ}
    (h : ∀ q χ, ‖F q χ‖ ≤ ‖G q χ‖) : primitiveCharacterMean Q F ≤ primitiveCharacterMean Q G :=
  sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (h p.1 p.2) (by positivity)

private lemma mean_add_le (Q : ℕ) (F G : (q : ℕ) → DirichletCharacter ℂ q → ℂ) :
    primitiveCharacterMean Q (fun q χ => F q χ + G q χ) ≤
      primitiveCharacterMean Q F + primitiveCharacterMean Q G := by
  unfold primitiveCharacterMean
  rw [← sum_add_distrib]
  refine sum_le_sum fun p _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

/-- The triangle inequality for a finite sum of character families. -/
theorem primitiveCharacterMean_sum_le {ι : Type*} (Q : ℕ) (J : Finset ι)
    (F : ι → (q : ℕ) → DirichletCharacter ℂ q → ℂ) :
    primitiveCharacterMean Q (fun q χ => ∑ j ∈ J, F j q χ) ≤
      ∑ j ∈ J, primitiveCharacterMean Q (F j) := by
  classical
  unfold primitiveCharacterMean
  rw [sum_comm]
  refine sum_le_sum fun p _ => ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

/-- A character polynomial supported on an arbitrary finite set of integers. -/
def characterPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ S, a n * χ n

/-- The coefficient square sum on a finite set. -/
def coefficientEnergy (S : Finset ℕ) (a : ℕ → ℂ) : ℝ := ∑ n ∈ S, ‖a n‖ ^ 2

private theorem energy_nonneg (S : Finset ℕ) (a : ℕ → ℂ) : 0 ≤ coefficientEnergy S a :=
  sum_nonneg fun _ _ => sq_nonneg _

private lemma energy_mono {S T : Finset ℕ} (h : S ⊆ T) (a : ℕ → ℂ) :
    coefficientEnergy S a ≤ coefficientEnergy T a :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => sq_nonneg _

private theorem characterPolynomial_mean_sq {Q M N : ℕ} (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    {S : Finset ℕ} (hS : S ⊆ Ioc M (M + N)) (a : ℕ → ℂ) :
    ∑ p ∈ primitiveCharacterFamily Q, ((p.1 : ℝ) / p.1.totient) *
      ‖characterPolynomial S a p.1 p.2‖ ^ 2 ≤ (N + (Q : ℝ)^2) * coefficientEnergy S a := by
  let b (n : ℕ) := if n ∈ S then a n else 0
  have h := character_large_sieve_add_sq b M hN hQ
  have hf : (Ioc M (M+N)).filter (· ∈ S) = S := by
    ext n
    exact mem_filter.trans ⟨And.right, fun hn => ⟨hS hn, hn⟩⟩
  have hb (q : ℕ) (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ Ioc M (M+N), b n * χ n) = characterPolynomial S a q χ := by
    simp only [b, ite_mul, zero_mul, ← sum_filter, hf, characterPolynomial]
  have he : (∑ n ∈ Ioc M (M+N), ‖b n‖ ^ 2) = coefficientEnergy S a := by
    simp only [b, apply_ite Norm.norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
      ← sum_filter, hf, coefficientEnergy]
  simp_rw [hb] at h
  rw [he] at h
  simpa only [primitiveCharacterFamily, sum_sigma, ← mul_sum] using h

/-- A bilinear estimate for two possibly sparse character polynomials on intervals
of lengths `M` and `N`. -/
theorem primitiveCharacterMean_bilinear {Q A M B N : ℕ} (hQ : 1 ≤ Q)
    (hM : 1 ≤ M) (hN : 1 ≤ N) {S T : Finset ℕ}
    (hS : S ⊆ Ioc A (A+M)) (hT : T ⊆ Ioc B (B+N)) (a b : ℕ → ℂ) :
    primitiveCharacterMean Q (fun q χ => characterPolynomial S a q χ * characterPolynomial T b q χ) ≤
      Real.sqrt ((M : ℝ) + Q^2) * Real.sqrt ((N : ℝ) + Q^2) *
      (Real.sqrt (coefficientEnergy S a) * Real.sqrt (coefficientEnergy T b)) := by
  let w (p : (q : ℕ) × DirichletCharacter ℂ q) := (p.1 : ℝ) / p.1.totient
  let f (p : (q : ℕ) × DirichletCharacter ℂ q) := ‖characterPolynomial S a p.1 p.2‖
  let g (p : (q : ℕ) × DirichletCharacter ℂ q) := ‖characterPolynomial T b p.1 p.2‖
  have hw p : 0 ≤ w p := by dsimp only [w]; positivity
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (primitiveCharacterFamily Q)
    (fun p => Real.sqrt (w p) * f p) (fun p => Real.sqrt (w p) * g p)
  simp only [mul_pow, Real.sq_sqrt (hw _)] at hCS
  have heq p : Real.sqrt (w p) * f p * (Real.sqrt (w p) * g p) = w p * (f p * g p) := by
    have := Real.sq_sqrt (hw p)
    nlinarith only [congrArg (fun x => x * (f p * g p)) this]
  simp_rw [heq] at hCS
  unfold primitiveCharacterMean
  simp_rw [norm_mul]
  apply hCS.trans
  have h1 := Real.sqrt_le_sqrt (characterPolynomial_mean_sq hQ hM hS a)
  have h2 := Real.sqrt_le_sqrt (characterPolynomial_mean_sq hQ hN hT b)
  apply (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  ring

/-- Character bilinear form with a row-dependent upper limit on the inner variable.
The choice `c m = X / m` gives Vaughan's hyperbolic cutoff. -/
def cutoffCharacterBilinear (S T : Finset ℕ) (a b : ℕ → ℂ) (c : ℕ → ℕ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m ∈ S, (a m * χ m) * characterPolynomial (T.filter (· ≤ c m)) b q χ

private lemma cutoffCharacterBilinear_split (S T : Finset ℕ) (a b : ℕ → ℂ) (c : ℕ → ℕ)
    (H q : ℕ) (χ : DirichletCharacter ℂ q) :
    cutoffCharacterBilinear S T a b c q χ =
      (cutoffCharacterBilinear (S.filter (fun m => c m ≤ H)) (T.filter (· ≤ H)) a b c q χ +
      cutoffCharacterBilinear (S.filter (fun m => ¬ c m ≤ H)) (T.filter (fun n => ¬ n ≤ H)) a b c q χ) +
      characterPolynomial (S.filter (fun m => ¬ c m ≤ H)) a q χ *
        characterPolynomial (T.filter (· ≤ H)) b q χ := by
  classical
  unfold cutoffCharacterBilinear
  rw [← sum_filter_add_sum_filter_not S (fun m => c m ≤ H)]
  have hleft (m : ℕ) (hm : c m ≤ H) :
      ((T.filter (· ≤ H)).filter (· ≤ c m)) = T.filter (· ≤ c m) := by
    ext n
    simp only [mem_filter, and_assoc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.trans hm, h.2⟩⟩
  have hright (m : ℕ) (hm : ¬ c m ≤ H) :
      characterPolynomial (T.filter (· ≤ c m)) b q χ =
      characterPolynomial ((T.filter (fun n => ¬ n ≤ H)).filter (· ≤ c m)) b q χ +
      characterPolynomial (T.filter (· ≤ H)) b q χ := by
    unfold characterPolynomial
    rw [← sum_filter_add_sum_filter_not (T.filter (· ≤ c m)) (fun n => n ≤ H)]
    rw [add_comm]
    congr 1
    · congr 1
      ext n
      simp only [mem_filter]
      tauto
    · congr 1
      ext n
      simp only [mem_filter, and_assoc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.trans (by omega), h.2⟩⟩
  rw [add_assoc]
  congr 1
  · exact sum_congr rfl fun m hm => by rw [hleft m (mem_filter.mp hm).2]
  · unfold characterPolynomial
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun m hm => by
      have hh := hright m (mem_filter.mp hm).2
      unfold characterPolynomial at hh
      rw [hh, mul_add]

private lemma energy_filter_add (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (a : ℕ → ℂ) :
    coefficientEnergy (S.filter p) a + coefficientEnergy (S.filter (fun n => ¬ p n)) a =
      coefficientEnergy S a :=
  sum_filter_add_sum_filter_not S p _

private lemma sqrt_pair_le {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    Real.sqrt a₁ * Real.sqrt b₁ + Real.sqrt a₂ * Real.sqrt b₂ ≤
      Real.sqrt (a₁ + a₂) * Real.sqrt (b₁ + b₂) := by
  have h := Real.sum_sqrt_mul_sqrt_le (univ : Finset (Fin 2))
    (f := ![a₁, a₂]) (g := ![b₁, b₂])
    (by intro i; fin_cases i <;> simpa) (by intro i; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

/-- The large sieve for a bilinear form with arbitrary row-dependent cutoffs.
Splitting the column interval into halves at each step costs one factor `k + 1`
for an interval of length `2^k`. -/
theorem primitiveCharacterMean_cutoff_pow_two {Q A M : ℕ} (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (k B : ℕ) {S T : Finset ℕ} (hS : S ⊆ Ioc A (A+M)) (hT : T ⊆ Ioc B (B+2^k))
    (a b : ℕ → ℂ) (c : ℕ → ℕ) :
    primitiveCharacterMean Q (cutoffCharacterBilinear S T a b c) ≤
      (k+1 : ℝ) * (Real.sqrt ((M : ℝ) + Q^2) * Real.sqrt ((2^k : ℕ) + (Q : ℝ)^2)) *
      (Real.sqrt (coefficientEnergy S a) * Real.sqrt (coefficientEnergy T b)) := by
  classical
  induction k generalizing B S T with
  | zero =>
    let R := S.filter (fun m => B + 1 ≤ c m)
    have heq (q : ℕ) (χ : DirichletCharacter ℂ q) :
        cutoffCharacterBilinear S T a b c q χ = characterPolynomial R a q χ * characterPolynomial T b q χ := by
      unfold cutoffCharacterBilinear characterPolynomial R
      rw [sum_mul, sum_filter]
      refine sum_congr rfl fun m hm => ?_
      split_ifs with hc
      · have hf : T.filter (· ≤ c m) = T := filter_eq_self.mpr fun n hn =>
          (mem_Ioc.mp (hT hn)).2.trans (by simpa using hc)
        rw [hf]
      · have hf : T.filter (· ≤ c m) = ∅ := filter_eq_empty_iff.mpr fun n hn => by
          have h := (mem_Ioc.mp (hT hn)).1
          omega
        simp [hf]
    simp_rw [show cutoffCharacterBilinear S T a b c =
      (fun q χ => characterPolynomial R a q χ * characterPolynomial T b q χ) from funext fun q => funext (heq q)]
    simp only [pow_zero, Nat.cast_zero, zero_add, one_mul, Nat.cast_one] at *
    exact (primitiveCharacterMean_bilinear hQ hM (N := 1) (by decide)
      ((filter_subset _ _).trans hS) hT a b).trans (by
        have hRS : R ⊆ S := filter_subset _ _
        norm_num only [Nat.cast_one]
        gcongr
        exact energy_mono hRS a)
  | succ k ih =>
    let H := B + 2^k
    let S₁ := S.filter (fun m => c m ≤ H)
    let S₂ := S.filter (fun m => ¬ c m ≤ H)
    let T₁ := T.filter (· ≤ H)
    let T₂ := T.filter (fun n => ¬ n ≤ H)
    have hS₁ : S₁ ⊆ S := filter_subset _ _
    have hS₂ : S₂ ⊆ S := filter_subset _ _
    have hT₁ : T₁ ⊆ T := filter_subset _ _
    have hT₂ : T₂ ⊆ T := filter_subset _ _
    have hTL : T₁ ⊆ Ioc B (B+2^k) := fun n hn => mem_Ioc.mpr
      ⟨(mem_Ioc.mp (hT (hT₁ hn))).1, (mem_filter.mp hn).2⟩
    have hTR : T₂ ⊆ Ioc H (H+2^k) := by
      intro n hn
      have h := (mem_Ioc.mp (hT (hT₂ hn))).2
      rw [pow_succ] at h
      exact mem_Ioc.mpr ⟨lt_of_not_ge (mem_filter.mp hn).2, by dsimp [H]; omega⟩
    let L := Real.sqrt ((M : ℝ) + Q^2) * Real.sqrt ((2^k : ℕ) + (Q : ℝ)^2)
    let E := Real.sqrt (coefficientEnergy S a) * Real.sqrt (coefficientEnergy T b)
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hsums : coefficientEnergy S₁ a + coefficientEnergy S₂ a = coefficientEnergy S a :=
      energy_filter_add S _ a
    have hsumt : coefficientEnergy T₁ b + coefficientEnergy T₂ b = coefficientEnergy T b :=
      energy_filter_add T _ b
    have hpair := sqrt_pair_le (energy_nonneg S₁ a) (energy_nonneg S₂ a)
      (energy_nonneg T₁ b) (energy_nonneg T₂ b)
    rw [hsums, hsumt] at hpair
    have hleft := ih B (hS₁.trans hS) hTL
    have hright := ih H (hS₂.trans hS) hTR
    have hrect := primitiveCharacterMean_bilinear hQ hM (Nat.one_le_pow _ _ (by decide : 0 < 2))
      (hS₂.trans hS) hTL a b
    let F := cutoffCharacterBilinear S₁ T₁ a b c
    let G := cutoffCharacterBilinear S₂ T₂ a b c
    let P := fun q χ => characterPolynomial S₂ a q χ * characterPolynomial T₁ b q χ
    have split := mean_add_le Q (fun q χ => F q χ + G q χ) P
    have split₂ := mean_add_le Q F G
    have heq : cutoffCharacterBilinear S T a b c = (fun q χ => (F q χ + G q χ) + P q χ) :=
      funext fun q => funext fun χ => cutoffCharacterBilinear_split S T a b c H q χ
    rw [heq]
    apply split.trans
    apply (add_le_add split₂ hrect).trans
    have hrec : primitiveCharacterMean Q F + primitiveCharacterMean Q G ≤ (k+1 : ℝ) * L * E := by
      apply (add_le_add hleft hright).trans
      change (k+1 : ℝ) * L * _ + (k+1 : ℝ) * L * _ ≤ _
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hpair (by positivity)
    have hrectE : Real.sqrt (coefficientEnergy S₂ a) * Real.sqrt (coefficientEnergy T₁ b) ≤ E :=
      mul_le_mul (Real.sqrt_le_sqrt (energy_mono hS₂ a)) (Real.sqrt_le_sqrt (energy_mono hT₁ b))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply (add_le_add hrec (mul_le_mul_of_nonneg_left hrectE hL)).trans
    have hLp : L ≤ Real.sqrt ((M : ℝ) + Q^2) * Real.sqrt ((2^(k+1) : ℕ) + (Q : ℝ)^2) := by
      dsimp only [L]
      gcongr
      exact Nat.le_succ k
    calc
      _ = ((k+1 : ℝ)+1) * L * E := by ring
      _ ≤ _ := by
        rw [Nat.cast_succ]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLp (by positivity)) hE

end AnalyticNumberTheory.PrimeDistribution
