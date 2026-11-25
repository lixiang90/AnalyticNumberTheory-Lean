import AnalyticNumberTheory.AdditiveNumberTheory.Waring
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.ExponentialSums.VinogradovMeanValue

/-!
# Minor arcs in Waring's problem

Apply Weyl's inequality to the monomial phase and Hua's lemma to its moments.
The Waring convention includes the zero base, which contributes one to the sum.
-/

open Finset Polynomial MeasureTheory

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Separate the zero base from the sum on the positive integers. -/
theorem waringSum_eq_one_add {k : ℕ} (hk : 1 ≤ k) (P : ℕ) (α : ℝ) :
    waringSum k P α = 1 + ∑ x ∈ Icc 1 P, e (α * (x : ℝ) ^ k) := by
  have hbox : range (P + 1) = insert 0 (Icc 1 P) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  simp [waringSum, genExpSum, hbox, zero_pow (by omega : k ≠ 0)]

/-- On the minor arcs the Dirichlet approximant has denominator between `Q` and `T`.
Weyl's inequality then bounds every point on these arcs uniformly. -/
theorem norm_waringSum_le_on_minorArcs {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℕ), 1 ≤ P → ∀ {Q T α : ℝ}, 1 ≤ Q → 2 * Q ≤ T →
      α ∈ minorArcs Q T → ‖waringSum k P α‖ ≤
        1 + C * (P : ℝ) ^ (1 + ε) *
          (Q⁻¹ + (P : ℝ)⁻¹ + T * (P : ℝ) ^ (-(k : ℝ))) ^ ((2 : ℝ) ^ (1 - (k : ℤ))) := by
  obtain ⟨C, hC, hW⟩ := ExponentialSums.weyl_inequality hk hε
  refine ⟨C, hC, fun P hP Q T α hQ hQT hα => ?_⟩
  obtain ⟨a, q, hQq, hqT, hc, happ⟩ := mem_minorArcs_approx hQ hQT hα
  have hq : 0 < (q : ℝ) := by linarith
  have hqN : 1 ≤ q := by exact_mod_cast (hQ.trans hQq.le)
  have happ' : |α - a / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.trans ?_
    rw [sq]
    gcongr
  have hw := hW (monomial k α) (natDegree_monomial_le _) a q hqN hc (by simpa using happ')
    0 P hP
  have hsum : ‖∑ x ∈ Icc 1 P, e (α * (x : ℝ) ^ k)‖ ≤
      C * (P : ℝ) ^ (1 + ε) *
      ((q : ℝ)⁻¹ + (P : ℝ)⁻¹ + q * (P : ℝ) ^ (-(k : ℝ))) ^ ((2 : ℝ) ^ (1 - (k : ℤ))) := by
    have hI : Ioc 0 P = Icc 1 P := by ext x; simp [Nat.lt_iff_add_one_le]
    simpa only [zero_add, hI, eval_monomial, e, ExponentialSums.e] using hw
  rw [waringSum_eq_one_add hk]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one]
  refine add_le_add le_rfl (hsum.trans ?_)
  have hinv : (q : ℝ)⁻¹ ≤ Q⁻¹ := inv_anti₀ (by linarith) hQq.le
  gcongr

/-- Hua's moment bound for the sum that includes the base zero. -/
theorem integral_norm_waringSum_le {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ,
      (∫ α in (0 : ℝ)..1, ‖waringSum k P α‖ ^ (2 ^ k)) ≤
        C * (1 + (P : ℝ) ^ ((2 ^ k : ℝ) - k + ε)) := by
  obtain ⟨C, hC, hH⟩ := ExponentialSums.hua_lemma k hε
  let B := (2 : ℝ) ^ (2 ^ k - 1 : ℕ)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B * (1 + C), by positivity, fun P => ?_⟩
  let F := fun α : ℝ => ∑ x ∈ Icc 1 P, e (α * (x : ℝ) ^ k)
  have hF : Continuous F :=
    continuous_finsetSum _ fun _ _ => continuous_e.comp (continuous_id.mul continuous_const)
  have hW : Continuous (waringSum k P) := continuous_genExpSum _ _ _
  have hFi : IntervalIntegrable (fun α => ‖F α‖ ^ (2 ^ k)) volume 0 1 :=
    (hF.norm.pow _).intervalIntegrable _ _
  have hH' : (∫ α in (0 : ℝ)..1, ‖F α‖ ^ (2 ^ k)) ≤
      C * (P : ℝ) ^ ((2 ^ k : ℝ) - k + ε) := by simpa [F, e] using hH P
  calc (∫ α in (0 : ℝ)..1, ‖waringSum k P α‖ ^ (2 ^ k)) ≤
        ∫ α in (0 : ℝ)..1, B * (1 + ‖F α‖ ^ (2 ^ k)) := by
          apply intervalIntegral.integral_mono_on zero_le_one ((hW.norm.pow _).intervalIntegrable _ _)
            ((continuous_const.mul (continuous_const.add (hF.norm.pow _))).intervalIntegrable _ _)
          intro α _
          change ‖waringSum k P α‖ ^ (2 ^ k) ≤ B * (1 + ‖F α‖ ^ (2 ^ k))
          rw [waringSum_eq_one_add hk]
          change ‖1 + F α‖ ^ (2 ^ k) ≤ _
          calc _ ≤ (‖(1 : ℂ)‖ + ‖F α‖) ^ (2 ^ k) := by gcongr; exact norm_add_le _ _
            _ ≤ _ := by simpa [B] using add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) (norm_nonneg (F α)) (2 ^ k)
    _ ≤ _ := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
            (intervalIntegrable_const (c := (1 : ℝ))) hFi, intervalIntegral.integral_const]
          simp only [sub_zero, smul_eq_mul, one_mul]
          have hP : 0 ≤ (P : ℝ) ^ ((2 ^ k : ℝ) - k + ε) := by positivity
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hB.le
          nlinarith

/-- Hua's moment controls the integral on any measurable subset of a period
where the Weyl sum is at most `M`. -/
theorem norm_waringIntegral_subset_le {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P r n : ℕ) {U : Set ℝ} {u M : ℝ}, MeasurableSet U →
      U ⊆ Set.Icc u (u + 1) → 0 ≤ M → (∀ α ∈ U, ‖waringSum k P α‖ ≤ M) →
      ‖∫ α in U, waringSum k P α ^ (r + 2 ^ k) * e (-α * n)‖ ≤
        M ^ r * (C * (1 + (P : ℝ) ^ ((2 ^ k : ℝ) - k + ε))) := by
  obtain ⟨C, hC, hH⟩ := integral_norm_waringSum_le hk hε
  refine ⟨C, hC, fun P r n U u M hU hu hM hb => ?_⟩
  let W := waringSum k P
  have hW : Continuous W := continuous_genExpSum _ _ _
  have hi : IntegrableOn (fun α => ‖W α‖ ^ (2 ^ k)) (Set.Icc u (u + 1)) :=
    (hW.norm.pow (2 ^ k)).continuousOn.integrableOn_compact
    (isCompact_Icc (a := u) (b := u + 1))
  have hshift : (∫ α in Set.Icc u (u + 1), ‖W α‖ ^ (2 ^ k)) =
      ∫ α in (0 : ℝ)..1, ‖W α‖ ^ (2 ^ k) :=
    setIntegral_Icc_periodic_eq (fun α => by dsimp [W]; rw [show waringSum k P (α + 1)
      = waringSum k P α from periodic_genExpSum _ _ _ α]) u
  apply (norm_integral_le_integral_norm _).trans
  simp only [norm_mul, norm_pow, norm_e, mul_one, pow_add]
  calc _ ≤ ∫ α in U, M ^ r * ‖W α‖ ^ (2 ^ k) := by
          apply setIntegral_mono_on _ ((hi.mono_set hu).const_mul _) hU
          · intro α hα
            gcongr
            exact hb α hα
          · exact (((hW.norm.pow r).mul (hW.norm.pow (2 ^ k))).continuousOn.integrableOn_compact
              isCompact_Icc).mono_set hu
       _ ≤ M ^ r * ∫ α in Set.Icc u (u + 1), ‖W α‖ ^ (2 ^ k) := by
          rw [MeasureTheory.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (setIntegral_mono_set hi
            (ae_of_all _ fun _ => by positivity) (Filter.Eventually.of_forall hu)) (pow_nonneg hM _)
       _ ≤ _ := by rw [hshift]; exact mul_le_mul_of_nonneg_left (hH P) (pow_nonneg hM _)

/-- Each of the `r` excess variables supplies one power of the minor-arc pointwise
bound. The other variables contribute Hua's moment. -/
theorem norm_waringMinorArcIntegral_le {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P r n : ℕ) {Q T M : ℝ}, 0 ≤ M →
      (∀ α ∈ minorArcs Q T, ‖waringSum k P α‖ ≤ M) →
      ‖∫ α in minorArcs Q T, waringSum k P α ^ (r + 2 ^ k) * e (-α * n)‖ ≤
        M ^ r * (C * (1 + (P : ℝ) ^ ((2 ^ k : ℝ) - k + ε))) := by
  obtain ⟨C, hC, h⟩ := norm_waringIntegral_subset_le hk hε
  refine ⟨C, hC, fun P r n Q T M hM hb => h P r n (u := -(1 / T)) (measurableSet_minorArcs Q T) ?_ hM hb⟩
  simpa only [sub_eq_add_neg, add_comm] using minorArcs_subset_Icc Q T

/-- With denominator cutoff `P^η` and precision `P^(k-η)`, Weyl's inequality
gives a power saving over the length, uniformly in the frequency on the minor arcs. -/
theorem norm_waringSum_minorArcs_power_saving {k : ℕ} (hk : 2 ≤ k) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∀ (P : ℕ), 2 ≤ P → ∀ α ∈
      minorArcs ((P : ℝ) ^ η) ((P : ℝ) ^ ((k : ℝ) - η)),
      ‖waringSum k P α‖ ≤ C * (P : ℝ) ^ (1 - δ) := by
  let d := (2 : ℝ) ^ (1 - (k : ℤ))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  let δ := η * d / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ < 1 := by dsimp [δ]; nlinarith [mul_le_mul_of_nonneg_left hd1 hη.le]
  obtain ⟨C, hC, hw⟩ := norm_waringSum_le_on_minorArcs (by omega : 1 ≤ k) hδ
  refine ⟨δ, 1 + C * 3 ^ d, hδ, hδ', by positivity, fun P hP α hα => ?_⟩
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hQ : 1 ≤ (P : ℝ) ^ η := Real.one_le_rpow hP1 hη.le
  have hQT : 2 * (P : ℝ) ^ η ≤ (P : ℝ) ^ ((k : ℝ) - η) := by
    calc _ ≤ (P : ℝ) ^ (1 : ℝ) * (P : ℝ) ^ η := by rw [Real.rpow_one]; gcongr
      _ = (P : ℝ) ^ (1 + η) := (Real.rpow_add hP0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hinv : (P : ℝ)⁻¹ ≤ (P : ℝ) ^ (-η) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hbase : ((P : ℝ) ^ η)⁻¹ + (P : ℝ)⁻¹ + (P : ℝ) ^ ((k : ℝ) - η) *
      (P : ℝ) ^ (-(k : ℝ)) ≤ 3 * (P : ℝ) ^ (-η) := by
    rw [← Real.rpow_neg hP0.le, ← Real.rpow_add hP0]
    ring_nf
    linarith
  have hmain : C * (P : ℝ) ^ (1 + δ) * (3 * (P : ℝ) ^ (-η)) ^ d =
      C * 3 ^ d * (P : ℝ) ^ (1 - δ) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hP0.le _),
      ← Real.rpow_mul hP0.le]
    calc _ = C * 3 ^ d * ((P : ℝ) ^ (1 + δ) * (P : ℝ) ^ (-η * d)) := by ring
      _ = _ := by rw [← Real.rpow_add hP0]; dsimp [δ]; ring_nf
  refine (hw P (by omega) hQ hQT hα).trans ?_
  calc _ ≤ 1 + C * (P : ℝ) ^ (1 + δ) * (3 * (P : ℝ) ^ (-η)) ^ d := by
            gcongr
       _ ≤ _ := by
            rw [hmain, add_mul, one_mul]
            gcongr
            exact Real.one_le_rpow hP1 (by linarith)

/-- The minor-arc power saving is uniform in the target and in measurable subsets of the arcs. -/
theorem waringMinorSubset_power_saving {k s : ℕ} (hk : 2 ≤ k) (hs : 2 ^ k < s)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (P : ℕ), 2 ≤ P → ∀ (n : ℕ) {U : Set ℝ}, MeasurableSet U →
      U ⊆ minorArcs ((P : ℝ) ^ η) ((P : ℝ) ^ ((k : ℝ) - η)) →
      ‖∫ α in U,
        waringSum k P α ^ s * e (-α * n)‖ ≤ C * (P : ℝ) ^ ((s : ℝ) - k - δ) := by
  obtain ⟨d, A, hd, _, hA, hpoint⟩ := norm_waringSum_minorArcs_power_saving hk hη hη'
  let r := s - 2 ^ k
  have hrs : r + 2 ^ k = s := Nat.sub_add_cancel hs.le
  have hr : 0 < (r : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hs)
  let δ := (r : ℝ) * d / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, hmoment⟩ := norm_waringIntegral_subset_le (by omega : 1 ≤ k) hδ
  refine ⟨δ, A ^ r * (2 * B), hδ, by positivity, fun P hP n U hU hu => ?_⟩
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
  have hP0 : (0 : ℝ) < P := by linarith
  have hsub := hu.trans (minorArcs_subset_Icc _ _)
  rw [show 1 - 1 / (P : ℝ) ^ ((k : ℝ) - η) = -(1 / (P : ℝ) ^ ((k : ℝ) - η)) + 1 by ring] at hsub
  have h := hmoment P r n hU hsub (by positivity) (fun α hα => hpoint P hP α (hu hα))
  rw [hrs] at h
  have hdeg : k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hdegR : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hdeg
  have hone : 1 ≤ (P : ℝ) ^ ((2 : ℝ) ^ k - k + δ) :=
    Real.one_le_rpow hP1 (by linarith)
  refine h.trans ?_
  calc _ ≤ (A * (P : ℝ) ^ (1 - d)) ^ r * (B * (2 * (P : ℝ) ^ ((2 : ℝ) ^ k - k + δ))) := by
            gcongr
            linarith
       _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast ((P : ℝ) ^ (1 - d)) r, ← Real.rpow_mul hP0.le]
          have he : (1 - d) * (r : ℝ) + ((2 : ℝ) ^ k - k + δ) = (s : ℝ) - k - δ := by
            have hrs' : (r : ℝ) + (2 : ℝ) ^ k = (s : ℝ) := by exact_mod_cast hrs
            dsimp [δ]
            linarith only [hrs']
          rw [← he, Real.rpow_add hP0 ((1 - d) * (r : ℝ)) ((2 : ℝ) ^ k - k + δ)]
          ring

/-- Above Hua's moment threshold, the minor arcs are smaller by a power of `P`
than the natural scale `P^(s-k)`. The saving is uniform in the target integer. -/
theorem waringMinorArc_power_saving {k s : ℕ} (hk : 2 ≤ k) (hs : 2 ^ k < s)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (P : ℕ), 2 ≤ P → ∀ n : ℕ,
      ‖∫ α in minorArcs ((P : ℝ) ^ η) ((P : ℝ) ^ ((k : ℝ) - η)),
        waringSum k P α ^ s * e (-α * n)‖ ≤ C * (P : ℝ) ^ ((s : ℝ) - k - δ) := by
  obtain ⟨δ, C, hδ, hC, h⟩ := waringMinorSubset_power_saving hk hs hη hη'
  exact ⟨δ, C, hδ, hC, fun P hP n => h P hP n (measurableSet_minorArcs _ _) Set.Subset.rfl⟩

/-- Enlarging each major arc to the fixed half-width `1/T` shrinks its complement. -/
theorem minorArcsFixed_subset_minorArcs (Q : ℝ) {T : ℝ} (hT : 0 < T) :
    minorArcsFixed Q T ⊆ minorArcs Q T := by
  rintro α ⟨hα, hnot⟩
  refine ⟨hα, fun h => hnot ?_⟩
  simp only [majorArcs, Set.mem_iUnion, exists_prop] at h
  obtain ⟨q, hq, a, ha, h⟩ := h
  simp only [majorArcsFixed, Set.mem_iUnion, exists_prop]
  refine ⟨q, hq, a, ha, mem_majorArcFixed_iff.mpr ((mem_majorArc_iff.mp h).trans ?_)⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
  exact one_div_le_one_div_of_le hT (le_mul_of_one_le_left hT.le hq1)

/-- Uniform power saving for the fixed-width minor arcs above Hua's moment threshold. -/
theorem waringMinorArcFixed_power_saving {k s : ℕ} (hk : 2 ≤ k) (hs : 2 ^ k < s)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (P : ℕ), 2 ≤ P → ∀ n : ℕ,
      ‖minorArcIntegralFixed (fun α => waringSum k P α ^ s * e (-α * n))
        ((P : ℝ) ^ η) ((P : ℝ) ^ ((k : ℝ) - η))‖ ≤ C * (P : ℝ) ^ ((s : ℝ) - k - δ) := by
  obtain ⟨δ, C, hδ, hC, h⟩ := waringMinorSubset_power_saving hk hs hη hη'
  refine ⟨δ, C, hδ, hC, fun P hP n => h P hP n (measurableSet_minorArcsFixed _ _)
    (minorArcsFixed_subset_minorArcs _ ?_)⟩
  exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < P)) _

end AnalyticNumberTheory.AdditiveNumberTheory
