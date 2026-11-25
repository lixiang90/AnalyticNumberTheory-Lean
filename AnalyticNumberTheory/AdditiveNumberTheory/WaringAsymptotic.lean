import AnalyticNumberTheory.AdditiveNumberTheory.WaringMajorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.WaringMinorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.WaringFourierInversion

/-!
# The circle-method asymptotic for Waring representations

A fixed-width Farey dissection separates the arithmetic singular series from
the real singular integral after rescaling the frequency by `P^k`.
-/

open Finset MeasureTheory Filter
open scoped Topology Asymptotics

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Exact fixed-width Farey dissection of a Waring representation count. -/
theorem waringCount_eq_arcIntegralsFixed {k s P n : ℕ} (hk : 0 < k) (hn : n < (P + 1) ^ k)
    {B T : ℝ} (hB : 1 ≤ B) (hBT : 2 * B ^ 2 < T) :
    (waringCount k s n : ℂ) =
      majorArcIntegralFixed (fun α => waringSum k P α ^ s * e (-α * n)) B T +
      minorArcIntegralFixed (fun α => waringSum k P α ^ s * e (-α * n)) B T := by
  rw [← integral_waringSum_pow hk hn 0, zero_add]
  refine representationIntegral_eq_majorArcIntegralFixed_add_minorArcIntegralFixed ?_ hB hBT ?_
  · intro α
    change waringSum k P (α + 1) ^ s * e (-(α + 1) * n) = _
    rw [show waringSum k P (α + 1) = waringSum k P α from periodic_genExpSum _ _ _ α]
    congr 1
    rw [show -(α + 1) * (n : ℝ) = -α * n + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring,
      e_add_intCast]
  · exact (((continuous_genExpSum _ _ _).pow s).mul
      (continuous_e.comp (continuous_neg.mul continuous_const))).continuousOn.integrableOn_Icc

/-- On passing from the arc displacement `β` to `γ = P^k β`, the target becomes `n/P^k`. -/
theorem integral_waringMajorArcModel_rescale (k s : ℕ) {P : ℝ} (hP : 0 < P) (n T : ℝ) :
    (∫ β in (-(1 / T))..(1 / T), waringOscillatoryIntegral k (β * P ^ k) ^ s * e (-β * n)) =
      (P ^ k)⁻¹ • ∫ γ in (-(P ^ k / T))..(P ^ k / T),
        waringOscillatoryIntegral k γ ^ s * e (-γ * (n / P ^ k)) := by
  let F (γ : ℝ) := waringOscillatoryIntegral k γ ^ s * e (-γ * (n / P ^ k))
  have he (β : ℝ) : waringOscillatoryIntegral k (β * P ^ k) ^ s * e (-β * n) = F (β * P ^ k) := by
    dsimp [F]
    congr 2
    field_simp
  simp_rw [he]
  rw [intervalIntegral.integral_comp_mul_right F (pow_ne_zero k hP.ne')]
  congr 2 <;> ring

private theorem majorArcsFixed_floor (A T : ℝ) : majorArcsFixed (⌊A⌋₊ : ℝ) T = majorArcsFixed A T := by
  simp [majorArcsFixed, majorArcDenoms]

/-- Uniform major-arc comparison with the truncated singular factors for arbitrary targets. -/
theorem norm_waringMajorArc_sub_truncated_le {k s P n : ℕ} (hks : k ≤ s) (hP : 0 < P)
    {A T : ℝ} (hA : 1 ≤ A) (hAT : 2 * A ^ 2 < T) :
    ‖majorArcIntegralFixed (fun α => waringSum k P α ^ s * e (-α * n)) A T -
      (P : ℂ) ^ (s - k) * ((∑ q ∈ Icc 1 ⌊A⌋₊, waringSingularTerm k s n q) *
        ∫ γ in (-((P : ℝ) ^ k / T))..((P : ℝ) ^ k / T),
          waringOscillatoryIntegral k γ ^ s * e (-γ * (n / (P : ℝ) ^ k)))‖ ≤
      A ^ 2 * ((2 / T) * (s * ((P : ℝ) + 1) ^ (s - 1) *
        (1 + 2 * A * (1 + 2 * Real.pi * (1 / T) * (P : ℝ) ^ k)))) := by
  let B := ⌊A⌋₊
  have hB : 1 ≤ B := Nat.le_floor hA
  have hBA : (B : ℝ) ≤ A := Nat.floor_le (by linarith)
  have hBT : 2 * (B : ℝ) ^ 2 < T := lt_of_le_of_lt (by gcongr) hAT
  have hT : 0 < T := lt_of_le_of_lt (by positivity) hAT
  have hm := norm_waringMajorArcIntegralFixed_sub_main_le k s P n hB hBT
  simp only [majorArcIntegralFixed, B, majorArcsFixed_floor] at hm
  rw [integral_waringMajorArcModel_rescale k s (by exact_mod_cast hP) n T,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast] at hm
  have hpc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hfactor (S J : ℂ) : S * (P : ℂ) ^ s * (((P : ℂ) ^ k)⁻¹ * J) = P ^ (s-k) * (S * J) := by
    rw [show s = s - k + k from (Nat.sub_add_cancel hks).symm] at ⊢
    simp only [Nat.add_sub_cancel, pow_add]
    field_simp
  rw [hfactor] at hm
  exact hm.trans (by gcongr)

/-- Explicit comparison with the truncated, rescaled singular series and integral.
The minor-arc contribution is retained for any disjoint fixed-width dissection. -/
theorem norm_waringCount_sub_truncated_le {k s P n : ℕ} (hk : 0 < k) (hks : k ≤ s) (hP : 0 < P)
    (hn : n < (P + 1) ^ k) {A T : ℝ} (hA : 1 ≤ A) (hAT : 2 * A ^ 2 < T) :
    ‖(waringCount k s n : ℂ) -
      (P : ℂ) ^ (s - k) * ((∑ q ∈ Icc 1 ⌊A⌋₊, waringSingularTerm k s n q) *
        ∫ γ in (-((P : ℝ) ^ k / T))..((P : ℝ) ^ k / T),
          waringOscillatoryIntegral k γ ^ s * e (-γ * (n / (P : ℝ) ^ k)))‖ ≤
      A ^ 2 * ((2 / T) * (s * ((P : ℝ) + 1) ^ (s - 1) *
        (1 + 2 * A * (1 + 2 * Real.pi * (1 / T) * (P : ℝ) ^ k)))) +
      ‖minorArcIntegralFixed (fun α => waringSum k P α ^ s * e (-α * n)) A T‖ := by
  rw [waringCount_eq_arcIntegralsFixed hk hn hA hAT, add_sub_right_comm]
  exact (norm_add_le _ _).trans (add_le_add (norm_waringMajorArc_sub_truncated_le hks hP hA hAT) le_rfl)

/-- The power cutoffs give a disjoint dissection and reciprocal frequency scale. -/
theorem waringArcParameters {p : ℝ} (hp : 2 < p) {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ p ^ (1/10 : ℝ) ∧ 2 * (p ^ (1/10 : ℝ)) ^ 2 < p ^ ((k : ℝ) - 1/10) ∧
      p ^ k / p ^ ((k : ℝ) - 1/10) = p ^ (1/10 : ℝ) := by
  have hp1 : 1 < p := by linarith
  have hp0 := zero_lt_one.trans hp1
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨Real.one_le_rpow hp1.le (by norm_num), ?_, ?_⟩
  · calc 2 * (p ^ (1 / 10 : ℝ)) ^ 2 < p ^ (1 : ℝ) * (p ^ (1 / 10 : ℝ)) ^ 2 := by
           rw [Real.rpow_one]; gcongr
         _ = p ^ (1 + (1/10 : ℝ) * 2) := by
           rw [Real.rpow_add hp0, Real.rpow_mul hp0.le, Real.rpow_two]
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  · rw [Real.rpow_sub hp0, Real.rpow_natCast]
    field_simp

/-- The integrated major-arc approximation loses half a power below the main scale. -/
theorem waringMajorError_le {p : ℝ} (hp : 2 < p) {k s : ℕ} (hk : 2 ≤ k) (hs : 0 < s) :
    let A := p ^ (1/10 : ℝ)
    let T := p ^ ((k : ℝ) - 1/10)
    A ^ 2 * ((2 / T) * (s * (p + 1) ^ (s - 1) *
      (1 + 2 * A * (1 + 2 * Real.pi * (1 / T) * p ^ k)))) ≤
      (2 * s * 2 ^ (s-1) * (3 + 4 * Real.pi)) * p ^ ((s : ℝ) - k - 1/2) := by
  intro A T
  obtain ⟨hA, _, hratio⟩ := waringArcParameters hp hk
  change p ^ k / T = A at hratio
  have hp0 : 0 < p := by linarith
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hw : 2 / T = 2 * A / p ^ k := by rw [← hratio]; field_simp
  have hbr : 1 + 2 * A * (1 + 2 * Real.pi * (1 / T) * p ^ k) ≤ (3 + 4 * Real.pi) * A ^ 2 := by
    rw [show 2 * Real.pi * (1 / T) * p ^ k = 2 * Real.pi * (p ^ k / T) by ring, hratio]
    change 1 ≤ A at hA
    nlinarith [sq_nonneg (A-1)]
  calc _ ≤ A ^ 2 * ((2 / T) * (s * (2 * p) ^ (s - 1) * ((3 + 4 * Real.pi) * A ^ 2))) := by
           gcongr; linarith
       _ = (2 * s * 2 ^ (s-1) * (3 + 4 * Real.pi)) * ((A ^ 5 * p ^ (s-1)) / p ^ k) := by
           rw [hw, mul_pow]; ring
       _ = _ := by
           congr 1
           rw [← Real.rpow_natCast A 5, ← Real.rpow_natCast p (s-1), ← Real.rpow_natCast p k]
           dsimp [A]
           rw [← Real.rpow_mul hp0.le, ← Real.rpow_add hp0, ← Real.rpow_sub hp0,
             Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
           congr 1
           norm_num
           ring

/-- With denominator cutoff `P^(1/10)`, the normalized truncated main term
approximates the counting function with a power saving uniform in the target. -/
theorem waringCount_truncated_power_saving {k s : ℕ} (hk : 2 ≤ k) (hs : 2 ^ k < s) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (P n : ℕ), 3 ≤ P → n < (P+1)^k →
      let A := (P : ℝ) ^ (1/10 : ℝ)
      ‖(waringCount k s n : ℂ) / (P : ℂ) ^ (s-k) -
          (∑ q ∈ Icc 1 ⌊A⌋₊, waringSingularTerm k s n q) *
          ∫ γ in (-A)..A, waringOscillatoryIntegral k γ ^ s * e (-γ * (n / (P : ℝ)^k))‖ ≤
        C * (P : ℝ) ^ (-δ) := by
  obtain ⟨d, D, hd, hD, hminor⟩ := waringMinorArcFixed_power_saving hk hs
    (by norm_num : (0 : ℝ) < 1/10) (by norm_num)
  let K := (2 * (s : ℝ) * 2 ^ (s-1) * (3 + 4 * Real.pi))
  have hs0 : 0 < s := (Nat.zero_le _).trans_lt hs
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := min (1/2 : ℝ) d
  refine ⟨δ, K + D, lt_min (by norm_num) hd, by positivity, fun P n hP hn => ?_⟩
  intro A
  have hp : (2 : ℝ) < P := by exact_mod_cast (by omega : 2 < P)
  have hp1 : (1 : ℝ) ≤ P := by linarith
  have hp0 : (0 : ℝ) < P := by linarith
  have hks := (Nat.lt_two_pow_self (n := k)).trans hs
  obtain ⟨hA, hAT, hratio⟩ := waringArcParameters hp hk
  have h := norm_waringCount_sub_truncated_le (by omega : 0 < k) hks.le (by omega : 0 < P)
    hn hA hAT
  rw [hratio] at h
  have hraw := h.trans (add_le_add (waringMajorError_le hp hk hs0) (hminor P (by omega) n))
  let M := (∑ q ∈ Icc 1 ⌊A⌋₊, waringSingularTerm k s n q) *
    ∫ γ in (-A)..A, waringOscillatoryIntegral k γ ^ s * e (-γ * (n / (P : ℝ)^k))
  change ‖(waringCount k s n : ℂ) / (P : ℂ) ^ (s-k) - M‖ ≤ _
  have hpc : (P : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [show (waringCount k s n : ℂ) / (P : ℂ) ^ (s-k) - M =
    ((waringCount k s n : ℂ) - P ^ (s-k)*M) / (P : ℂ)^(s-k) by field_simp,
    norm_div, norm_pow, Complex.norm_natCast, div_le_iff₀ (pow_pos hp0 _)]
  apply hraw.trans
  change K * _ + D * _ ≤ _
  rw [add_mul, add_mul, ← Real.rpow_natCast (P : ℝ) (s-k), Nat.cast_sub hks.le,
    mul_assoc K, mul_assoc D, ← Real.rpow_add hp0]
  apply add_le_add <;> gcongr
  · linarith [show δ ≤ 1/2 from min_le_left _ _]
  · linarith [show δ ≤ d from min_le_right _ _]

private theorem two_mul_le_two_pow {k : ℕ} (hk : 2 ≤ k) : 2*k ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

private theorem waringSingularTerm_sum_Icc (k s n Q : ℕ) :
    (∑ q ∈ Icc 1 Q, waringSingularTerm k s n q) =
    ∑ q ∈ range (Q+1), waringSingularTerm k s n q := by
  have h : range (Q+1) = insert 0 (Icc 1 Q) := by
    ext q
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  simp [h, waringSingularTerm, coprimeResidues]

/-- Simultaneously removing both truncations is uniform in the frequency target
and in the singular series parameter. -/
theorem tendsto_waringTruncated_sub_singularFactors {k s : ℕ} (hk' : 0<k) (hs' : 2*k<s)
    {ι : Type*} {l : Filter ι} (A t : ι → ℝ) (n : ι → ℕ) (hA : Tendsto A l atTop) :
    Tendsto (fun i => (∑ q ∈ Icc 1 ⌊A i⌋₊, waringSingularTerm k s (n i) q) *
      (∫ γ in (-(A i))..(A i), waringOscillatoryIntegral k γ ^ s * e (-γ * t i)) -
      waringSingularSeries k s (n i) * waringSingularIntegral s k (t i)) l (𝓝 0) := by
  have hks : k<s := by omega
  let S (i : ι) := ∑ q ∈ Icc 1 ⌊A i⌋₊, waringSingularTerm k s (n i) q
  let J (i : ι) := ∫ γ in (-(A i))..(A i), waringOscillatoryIntegral k γ ^ s * e (-γ * t i)
  let L := ∫ γ : ℝ, ‖waringOscillatoryIntegral k γ ^ s‖
  let tail (i : ι) := ∫ γ in (Set.Ioc (-(A i)) (A i))ᶜ, ‖waringOscillatoryIntegral k γ ^ s‖
  have hQ : Tendsto (fun i => ⌊A i⌋₊+1) l atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) (tendsto_nat_floor_atTop.comp hA)
  have hS : Tendsto (fun i => ‖S i - waringSingularSeries k s (n i)‖) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hQ.eventually (Metric.tendstoUniformly_iff.mp
      (tendstoUniformly_waringSingularSeries hk' hs') ε hε)] with i hi
    simpa only [S, waringSingularTerm_sum_Icc, Real.dist_eq, sub_zero,
      abs_norm, dist_eq_norm, norm_norm, norm_sub_rev] using hi (n i)
  obtain ⟨B, hB⟩ := exists_bound_waringSingularTerm_sum hk' hs'
  have htail : Tendsto tail l (𝓝 0) := (tendsto_waringSingularIntegral_tail hk' hks).comp hA
  have hsmall := (htail.const_mul B).add (hS.mul_const L)
  simp only [mul_zero, zero_mul, add_zero] at hsmall
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ hsmall
  filter_upwards [hA.eventually_ge_atTop 0] with i hi
  let a := waringSingularSeries k s (n i)
  let b := waringSingularIntegral s k (t i)
  change ‖S i * J i - a*b‖ ≤ _
  rw [show S i * J i - a*b = S i * (J i - b) + (S i - a)*b by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  apply add_le_add
  · have hSi : ‖S i‖ ≤ B := hB _ _
    apply mul_le_mul hSi _ (norm_nonneg _) ((norm_nonneg _).trans hSi)
    rw [norm_sub_rev]
    exact norm_waringSingularIntegral_sub_truncation_le hk' hks hi (t i)
  · exact mul_le_mul_of_nonneg_left (norm_waringSingularIntegral_le _ _ _) (norm_nonneg _)

/-- The normalized Waring count is approximated by the full singular series
times the full singular integral, for any varying target with `n < (P+1)^k`. -/
theorem tendsto_waringCount_sub_singularFactors {k s : ℕ} (hk : 2 ≤ k) (hs : 2 ^ k < s)
    {ι : Type*} {l : Filter ι} (P n : ι → ℕ) (hP : Tendsto P l atTop)
    (hn : ∀ᶠ i in l, n i < (P i + 1)^k) :
    Tendsto (fun i => (waringCount k s (n i) : ℂ) / (P i : ℂ) ^ (s-k) -
      waringSingularSeries k s (n i) * waringSingularIntegral s k (n i / (P i : ℝ)^k)) l (𝓝 0) := by
  let A (i : ι) := (P i : ℝ) ^ (1/10 : ℝ)
  let t (i : ι) := n i / (P i : ℝ)^k
  let M (i : ι) := (∑ q ∈ Icc 1 ⌊A i⌋₊, waringSingularTerm k s (n i) q) *
    ∫ γ in (-(A i))..(A i), waringOscillatoryIntegral k γ ^ s * e (-γ * t i)
  have hp : Tendsto (fun i => (P i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hP
  have hA : Tendsto A l atTop := (tendsto_rpow_atTop (by norm_num)).comp hp
  obtain ⟨δ,C,hδ,_,hC⟩ := waringCount_truncated_power_saving hk hs
  have hmain : Tendsto (fun i => (waringCount k s (n i) : ℂ) / (P i : ℂ)^(s-k) - M i) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ (by
      simpa using (((tendsto_rpow_neg_atTop hδ).comp hp).const_mul C))
    filter_upwards [hP.eventually_ge_atTop 3,hn] with i hi hni
    exact hC _ _ hi hni
  have hf := tendsto_waringTruncated_sub_singularFactors (by omega : 0<k) ((two_mul_le_two_pow hk).trans_lt hs) A t n hA
  simpa only [M,t,sub_add_sub_cancel,add_zero] using hmain.add hf

/-- **Waring's asymptotic formula.** For `s > 2^k` nonnegative variables, the
number of representations equals the singular series times
`Γ(1+1/k)^s / Γ(s/k) · n^(s/k-1)`, up to `o(n^(s/k-1))`. -/
theorem waringCount_asymptotic {k s : ℕ} (hk : 2 ≤ k) (hs : 2 ^ k < s) :
    (fun n : ℕ => (waringCount k s n : ℂ) - waringSingularSeries k s n *
      ((Real.Gamma (1 / k + 1) ^ s / Real.Gamma ((s : ℝ)/k) * (n : ℝ) ^ ((s : ℝ)/k - 1) : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (((n : ℝ) ^ ((s : ℝ)/k - 1) : ℝ) : ℂ)) := by
  let r := (s : ℝ)/k - 1
  let c := Real.Gamma (1 / k + 1) ^ s / Real.Gamma ((s : ℝ)/k)
  let u (n : ℕ) := (n : ℝ) ^ (1 / (k : ℝ))
  let P (n : ℕ) := ⌊u n⌋₊ + 1
  have hk0 : 0 < k := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hks := (Nat.lt_two_pow_self (n := k)).trans hs
  have hu : Tendsto u atTop atTop := (tendsto_rpow_atTop (one_div_pos.mpr hkr)).comp tendsto_natCast_atTop_atTop
  have hP : Tendsto P atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_succ _) (tendsto_nat_floor_atTop.comp hu)
  have hP0 (n : ℕ) : 0 < (P n : ℝ) := by dsimp [P]; positivity
  have huP (n : ℕ) : u n < P n := by simpa only [P, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (u n)
  have huk (n : ℕ) : u n ^ k = n := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), one_div_mul_cancel hkr.ne', Real.rpow_one]
  have hnP (n : ℕ) : (n : ℝ) < (P n : ℝ)^k := by
    rw [← huk n]
    exact pow_lt_pow_left₀ (huP n) (by dsimp [u]; positivity) hk0.ne'
  have hn (n : ℕ) : n < (P n + 1)^k := by
    have h : n < (P n)^k := by exact_mod_cast hnP n
    exact h.trans_le (Nat.pow_le_pow_left (Nat.le_succ _) k)
  let t (n : ℕ) := n / (P n : ℝ)^k
  let err (n : ℕ) := (waringCount k s n : ℂ) / (P n : ℂ)^(s-k) -
    waringSingularSeries k s n * waringSingularIntegral s k (t n)
  have herr : Tendsto err atTop (𝓝 0) := tendsto_waringCount_sub_singularFactors hk hs P id hP
    (Eventually.of_forall hn)
  have hexp : (k : ℝ) * r = (s-k : ℕ) := by
    rw [Nat.cast_sub hks.le]
    dsimp [r]
    field_simp
  have hpow (n : ℕ) : ((P n : ℝ)^k)^r = (P n : ℝ)^(s-k) := by
    rw [← Real.rpow_natCast_mul (hP0 n).le, hexp, Real.rpow_natCast]
  have hupow (n : ℕ) : u n ^ (s-k) = (n : ℝ)^r := by
    rw [← Real.rpow_natCast, ← hexp, Real.rpow_natCast_mul (by dsimp [u]; positivity), huk]
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    exact fun h => False.elim ((Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hp _).ne') h)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := (tendsto_zero_iff_norm_tendsto_zero.mp herr).mul_const ((2:ℝ)^(s-k))
  rw [zero_mul] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by linarith
  have hpositive := Real.rpow_pos_of_pos hnr r
  have hu1 : 1 ≤ u n := Real.one_le_rpow hn1 (by positivity)
  have hPu : (P n : ℝ) ≤ 2*u n := by
    dsimp [P]
    push_cast
    linarith [Nat.floor_le (zero_le_one.trans hu1)]
  have hlevel := waringSingularIntegral_eq_density hk0 hks (t := t n)
    (div_pos hnr (pow_pos (hP0 n) _)) ((div_lt_one (pow_pos (hP0 n) _)).mpr (hnP n))
  change waringSingularIntegral s k (t n) = ((c * (t n)^r : ℝ) : ℂ) at hlevel
  have ht : (t n)^r = (n : ℝ)^r / (P n : ℝ)^(s-k) := by
    dsimp only [t]
    rw [Real.div_rpow hnr.le (pow_nonneg (hP0 n).le _), hpow]
  have hpc : (P n : ℂ) ≠ 0 := by exact_mod_cast (hP0 n).ne'
  have hnrc : (((n : ℝ)^r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpositive.ne'
  change ‖((waringCount k s n : ℂ) - waringSingularSeries k s n * ((c * (n : ℝ)^r : ℝ) : ℂ)) /
    (((n : ℝ)^r : ℝ) : ℂ)‖ ≤ ‖err n‖ * _
  have he : ((waringCount k s n : ℂ) - waringSingularSeries k s n * ((c * (n : ℝ)^r : ℝ) : ℂ)) /
      (((n : ℝ)^r : ℝ) : ℂ) = err n * ((P n : ℂ)^(s-k) / (((n : ℝ)^r : ℝ) : ℂ)) := by
    dsimp only [err]
    rw [hlevel, ht]
    push_cast
    field_simp
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpositive,
    div_le_iff₀ hpositive, ← hupow, ← mul_pow]
  exact pow_le_pow_left₀ (hP0 n).le hPu _

/-- A uniform positive lower bound for the singular series gives
representations of every sufficiently large integer. -/
theorem eventually_waringCount_pos_of_singularSeries {k s : ℕ} (hk : 2 ≤ k) (hs : 2 ^ k < s)
    (hS : ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop, b ≤ ‖waringSingularSeries k s n‖) :
    ∀ᶠ n : ℕ in atTop, 0 < waringCount k s n := by
  obtain ⟨b, hb, hS⟩ := hS
  let c := Real.Gamma (1 / k + 1) ^ s / Real.Gamma ((s : ℝ)/k)
  let r := (s : ℝ)/k - 1
  have hkr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsr : (0 : ℝ) < s := by exact_mod_cast (Nat.zero_le _).trans_lt hs
  have hc : 0 < c := div_pos (pow_pos (Real.Gamma_pos_of_pos (by positivity)) _)
    (Real.Gamma_pos_of_pos (div_pos hsr hkr))
  have happ := (waringCount_asymptotic hk hs).bound (show 0 < b*c/2 by positivity)
  filter_upwards [happ, hS, eventually_ge_atTop (1:ℕ)] with n hn hSn hpos
  by_contra! hz
  have hz' : waringCount k s n = 0 := by omega
  have hx : 0 < (n : ℝ)^r := Real.rpow_pos_of_pos (by exact_mod_cast hpos) _
  change ‖(waringCount k s n : ℂ) - waringSingularSeries k s n * ((c*(n : ℝ)^r : ℝ) : ℂ)‖ ≤
    b*c/2 * ‖(((n : ℝ)^r : ℝ) : ℂ)‖ at hn
  rw [hz', Nat.cast_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hc hx), abs_of_pos hx] at hn
  have hle := mul_le_mul_of_nonneg_right hSn (mul_pos hc hx).le
  nlinarith [mul_pos (mul_pos hb hc) hx]

end AnalyticNumberTheory.AdditiveNumberTheory
