import AnalyticNumberTheory.AdditiveNumberTheory.Waring
import AnalyticNumberTheory.AdditiveNumberTheory.WaringSingularSeries
import AnalyticNumberTheory.AdditiveNumberTheory.WaringSingularIntegral
import AnalyticNumberTheory.ExponentialSums.VinogradovMeanValue

/-!
# The major-arc approximation in Waring's problem

A rational phase has a fixed mean on each complete block of length `q`. Freezing
the residual phase on one such block costs at most its variation times the block
length. The variations telescope and the final incomplete block costs at most
`2q`. The Weyl sum includes both endpoints `0` and `P`.
-/

noncomputable section
open Finset MeasureTheory
open AnalyticNumberTheory.ExponentialSums (completeExpSum)
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Approximate a periodically weighted sum by its period mean times an integral.
`V` controls the variation of the continuous weight on the positive real axis. -/
theorem norm_periodic_sum_sub_mean_integral_le {q : ℕ} (hq : 0 < q) (w : ℕ → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (hperiod : ∀ m j, w (m * q + j) = w j)
    (g : ℝ → ℂ) (hg : Continuous g) (hgn : ∀ t, ‖g t‖ ≤ 1)
    (V : ℝ → ℝ) (hV : MonotoneOn V (Set.Ici 0))
    (hvar : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖g t - g u‖ ≤ V t - V u) (P : ℕ) :
    ‖∑ j ∈ range P, w j * g j -
      ((∑ j ∈ range q, w j) / (q : ℂ)) * ∫ t in (0 : ℝ)..P, g t‖ ≤
        2 * q * (1 + V P - V 0) := by
  let c := (∑ j ∈ range q, w j) / (q : ℂ)
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hc : ‖c‖ ≤ 1 := by
    rw [show ‖c‖ = ‖∑ j ∈ range q, w j‖ / (q : ℝ) by simp [c], div_le_one hq']
    exact (norm_sum_le _ _).trans ((sum_le_sum fun j _ => hw j).trans_eq (by simp))
  let E (n : ℕ) := ∑ j ∈ range n, w j * g j - c * ∫ t in (0 : ℝ)..n, g t
  have hstep (u r : ℕ) : E (u + r) = E u +
      ((∑ j ∈ range r, w (u + j) * g (u + j : ℕ)) - c * ∫ t in (u : ℝ)..(u + r : ℕ), g t) := by
    dsimp only [E]
    rw [sum_range_add, ← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 u)
      (hg.intervalIntegrable u (u + r : ℕ))]
    ring
  have hfull (m : ℕ) :
      ‖E (m * q)‖ ≤ 2 * q * (V (m * q : ℕ) - V 0) := by
    induction m with
    | zero => simp [E]
    | succ m ih =>
      let u := m * q
      let B := V ((u + q : ℕ) : ℝ) - V u
      have hblock (t : ℝ) (hlt : (u : ℝ) ≤ t) (hrt : t ≤ (u + q : ℕ)) :
          ‖g t - g u‖ ≤ B := by
        have hnd : 0 ≤ t := (Nat.cast_nonneg _).trans hlt
        exact (hvar _ _ (Nat.cast_nonneg _) hlt).trans (sub_le_sub_right
          (hV (Set.mem_Ici.mpr hnd) (Set.mem_Ici.mpr (Nat.cast_nonneg (u + q))) hrt) _)
      have hs : ‖∑ j ∈ range q, w (u + j) * (g (u + j : ℕ) - g u)‖ ≤ q * B := by
        apply (norm_sum_le _ _).trans
        calc _ ≤ ∑ _j ∈ range q, (1 : ℝ) * B := by
               refine sum_le_sum fun j hj => ?_
               rw [norm_mul]
               exact mul_le_mul (hw _) (hblock _ (by exact_mod_cast Nat.le_add_right u j)
                 (by exact_mod_cast Nat.add_le_add_left (mem_range.mp hj).le u)) (norm_nonneg _) zero_le_one
             _ = _ := by simp
      have hi : ‖∫ t in (u : ℝ)..(u + q : ℕ), g t - g u‖ ≤ q * B := by
        have haz : (u : ℝ) ≤ ((u + q : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right u q
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => g t - g u)
          (a := (u : ℝ)) (b := (u + q : ℕ)) fun t ht => by
            rw [Set.uIoc_of_le haz] at ht
            exact hblock _ ht.1.le ht.2
        simpa [abs_of_nonneg (sub_nonneg.mpr haz), mul_comm] using h
      have hmean : c * (q : ℂ) = ∑ j ∈ range q, w j := div_mul_cancel₀ _ (by exact_mod_cast hq.ne')
      have heq : E (u + q) = E u +
          ((∑ j ∈ range q, w (u + j) * (g (u + j : ℕ) - g u)) -
            c * ∫ t in (u : ℝ)..(u + q : ℕ), g t - g u) := by
        rw [hstep, intervalIntegral.integral_sub (hg.intervalIntegrable ..) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
        have hw' (j : ℕ) : w (u + j) = w j := hperiod m j
        simp_rw [hw']
        rw [← hmean]
        push_cast
        simp [Algebra.smul_def, mul_assoc]
      rw [Nat.succ_mul]
      change ‖E (u + q)‖ ≤ _
      rw [heq]
      calc _ ≤ ‖E u‖ + (‖∑ j ∈ range q, w (u + j) * (g (u + j : ℕ) - g u)‖ +
              ‖c‖ * ‖∫ t in (u : ℝ)..(u + q : ℕ), g t - g u‖) := by
              apply (norm_add_le _ _).trans (add_le_add le_rfl ?_)
              simpa only [norm_mul] using norm_sub_le (∑ j ∈ range q, w (u + j) * (g (u + j : ℕ) - g u))
                (c * ∫ t in (u : ℝ)..(u + q : ℕ), g t - g u)
           _ ≤ 2 * q * (V (u : ℝ) - V 0) + (q * B + 1 * (q * B)) :=
             add_le_add ih (add_le_add hs (mul_le_mul hc hi (norm_nonneg _) zero_le_one))
           _ = _ := by dsimp [B, u]; ring
  let u := P / q * q
  let r := P % q
  have hur : u + r = P := Nat.div_add_mod' P q
  have hsum : ‖∑ j ∈ range r, w (u + j) * g (u + j : ℕ)‖ ≤ r := by
    apply (norm_sum_le _ _).trans
    calc _ ≤ ∑ _j ∈ range r, (1 : ℝ) * 1 := by
           refine sum_le_sum fun j _ => ?_
           rw [norm_mul]
           exact mul_le_mul (hw _) (hgn _) (norm_nonneg _) zero_le_one
         _ = _ := by simp
  have hint : ‖∫ t in (u : ℝ)..(u + r : ℕ), g t‖ ≤ r := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (u : ℝ)) (b := (u + r : ℕ))
      (fun t _ => hgn t)
    simpa using h
  have hru : (r : ℝ) ≤ q := Nat.cast_le.mpr (Nat.mod_lt P hq).le
  have huP : (u : ℝ) ≤ P := Nat.cast_le.mpr (by omega)
  have hVle := hV (Set.mem_Ici.mpr (Nat.cast_nonneg u)) (Set.mem_Ici.mpr (Nat.cast_nonneg P)) huP
  change ‖E P‖ ≤ _
  calc _ = ‖E (u + r)‖ := by rw [hur]
       _ ≤ ‖E u‖ + (r + r : ℝ) := by
         rw [hstep]
         apply (norm_add_le _ _).trans (add_le_add le_rfl ?_)
         apply (norm_sub_le _ _).trans (add_le_add hsum ?_)
         rw [norm_mul]
         simpa using mul_le_mul hc hint (norm_nonneg _) zero_le_one
       _ ≤ 2 * q * (V u - V 0) + (q + q : ℝ) := add_le_add (hfull _) (add_le_add hru hru)
       _ ≤ _ := by nlinarith only [mul_nonneg hq'.le (sub_nonneg.mpr hVle)]

private theorem norm_e_sub_e_le (u v : ℝ) : ‖e u - e v‖ ≤ 2 * Real.pi * |u - v| := by
  have heq (w : ℝ) : e w = Complex.exp (Complex.I * ((2 * Real.pi * w : ℝ) : ℂ)) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [show e u - e v = e v * (e (u - v) - 1) by rw [mul_sub, ← e_add, mul_one]; congr 2; ring,
    norm_mul, norm_e, one_mul, heq]
  simpa [abs_mul, abs_of_nonneg Real.pi_nonneg] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (u - v)))

/-- Uniform approximation near a rational frequency `a/q`, including the two endpoints
of the Weyl sum. Coprimality of `a` and `q` is unnecessary. -/
theorem norm_waringSum_majorArc_sub_integral_le (k P a : ℕ) {q : ℕ} (hq : 0 < q) (β : ℝ) :
    ‖waringSum k P ((a : ℝ) / q + β) -
        (completeExpSum q a k / (q : ℂ)) * ∫ t in (0 : ℝ)..P, e (β * t ^ k)‖ ≤
      1 + 2 * q * (1 + 2 * Real.pi * |β| * (P : ℝ) ^ k) := by
  let w (n : ℕ) := e ((a : ℝ) / q * n ^ k)
  let g (t : ℝ) := e (β * t ^ k)
  let V (t : ℝ) := 2 * Real.pi * |β| * t ^ k
  let _ : NeZero q := ⟨hq.ne'⟩
  have hchar (n : ℕ) : w n = ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q) ^ k) := by
    rw [show (a : ZMod q) * (n : ZMod q) ^ k = (((a : ℤ) * (n : ℤ) ^ k : ℤ) : ZMod q) by simp,
      ZMod.stdAddChar_coe]
    unfold w e
    congr 1
    push_cast
    ring
  have hp (m j : ℕ) : w (m * q + j) = w j := by
    rw [hchar, hchar]
    simp
  have hmean : ∑ j ∈ range q, w j = completeExpSum q a k := by
    refine sum_congr rfl fun j _ => ?_
    unfold w e
    congr 1
    push_cast
    ring
  have hV : MonotoneOn V (Set.Ici 0) := by
    intro u hu t _ hut
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hut k) (by positivity)
  have hvar (u t : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) : ‖g t - g u‖ ≤ V t - V u := by
    apply (norm_e_sub_e_le _ _).trans_eq
    rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hu hut k))]
    dsimp only [V]
    ring
  have h := norm_periodic_sum_sub_mean_integral_le hq w (fun n => (norm_e _).le) hp g
    (continuous_e.comp (continuous_const.mul (continuous_id.pow k)))
    (fun _ => (norm_e _).le) V hV hvar P
  rw [hmean] at h
  have hsum : waringSum k P ((a : ℝ) / q + β) = ∑ j ∈ range (P + 1), w j * g j := by
    unfold waringSum genExpSum
    refine sum_congr rfl fun j _ => ?_
    dsimp only [w, g]
    push_cast
    simp [add_mul, e_add]
  rw [hsum, sum_range_succ, add_sub_right_comm]
  calc _ ≤ ‖∑ j ∈ range P, w j * g j -
              (completeExpSum q a k / (q : ℂ)) * ∫ t in (0 : ℝ)..P, g t‖ + ‖w P * g P‖ :=
           norm_add_le _ _
       _ ≤ 2 * q * (1 + V P - V 0) + 1 := add_le_add h (by simp [w, g, norm_e])
       _ ≤ _ := by dsimp only [V]; nlinarith only [show 0 ≤ (q : ℝ) * (2 * Real.pi * |β| * 0 ^ k) by positivity]

/-- Scaling the continuous model to the unit interval gives the oscillatory integral
used in the singular integral for Waring's problem. -/
theorem integral_waringPhase_eq_scaled (k : ℕ) (P β : ℝ) :
    (∫ t in (0 : ℝ)..P, e (β * t ^ k)) = (P : ℂ) * waringOscillatoryIntegral k (β * P ^ k) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (fun t : ℝ => e (β * t ^ k))
    (a := (0 : ℝ)) (b := 1) P
  simpa [waringOscillatoryIntegral, mul_pow, mul_assoc, Algebra.smul_def] using h.symm

/-- The unit-interval oscillatory factor is Lipschitz in its frequency. -/
theorem lipschitz_waringOscillatoryIntegral (k : ℕ) :
    LipschitzWith ⟨2 * Real.pi, by positivity⟩ (waringOscillatoryIntegral k) := by
  apply LipschitzWith.of_dist_le_mul
  intro β γ
  rw [dist_eq_norm, Real.dist_eq]
  change _ ≤ (2 * Real.pi) * |β - γ|
  unfold waringOscillatoryIntegral
  rw [← intervalIntegral.integral_sub
    (f := fun t : ℝ => e (β * t ^ k)) (g := fun t : ℝ => e (γ * t ^ k))
    ((continuous_e.comp (continuous_const.mul (continuous_id.pow k))).intervalIntegrable ..)
    ((continuous_e.comp (continuous_const.mul (continuous_id.pow k))).intervalIntegrable ..)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t => e (β * t ^ k) - e (γ * t ^ k)) (C := 2 * Real.pi * |β - γ|) (by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      apply (norm_e_sub_e_le _ _).trans
      rw [← sub_mul, abs_mul, abs_of_nonneg (pow_nonneg ht.1.le _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht.1.le ht.2)) (by positivity))
  simpa using h

private theorem norm_pow_sub_pow_bound (z w : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (s : ℕ) :
    ‖z ^ s - w ^ s‖ ≤ s * R ^ (s - 1) * ‖z - w‖ := by
  cases s with
  | zero => simp
  | succ s =>
    induction s with
    | zero => simp
    | succ s ih =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [show z ^ (s + 1 + 1) - w ^ (s + 1 + 1) =
          z * (z ^ (s + 1) - w ^ (s + 1)) + w ^ (s + 1) * (z - w) by ring]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul, norm_pow]
      calc _ ≤ R * ((s + 1 : ℕ) * R ^ s * ‖z - w‖) + R ^ (s + 1) * ‖z - w‖ :=
             add_le_add (mul_le_mul hz ih (norm_nonneg _) hR)
               (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw _) (norm_nonneg _))
           _ = _ := by push_cast; ring

/-- On any subinterval `[u,v] ⊆ [-η,η]` of a major arc around `a/q`, the complete Weyl
sum separates from the continuous integral. The error is linear in the interval length. -/
theorem norm_waringMajorArc_integral_sub_main_le (k s P a n : ℕ) {q : ℕ} (hq : 0 < q)
    {u v η : ℝ} (hu : -η ≤ u) (huv : u ≤ v) (hv : v ≤ η) :
    ‖(∫ β in u..v, waringSum k P ((a : ℝ) / q + β) ^ s * e (-((a : ℝ) / q + β) * n)) -
        (((completeExpSum q a k / (q : ℂ)) * P) ^ s * e (-((a : ℝ) / q) * n)) *
          ∫ β in u..v, waringOscillatoryIntegral k (β * (P : ℝ) ^ k) ^ s * e (-β * n)‖ ≤
      (v - u) * (s * ((P : ℝ) + 1) ^ (s - 1) * (1 + 2 * q * (1 + 2 * Real.pi * η * (P : ℝ) ^ k))) := by
  let c := completeExpSum q a k / (q : ℂ)
  let M (β : ℝ) := (c * P) * waringOscillatoryIntegral k (β * (P : ℝ) ^ k)
  let F (β : ℝ) := waringSum k P ((a : ℝ) / q + β)
  let G (β : ℝ) := e (-((a : ℝ) / q + β) * n)
  have hF : Continuous F := (continuous_genExpSum _ _ _).comp (continuous_const.add continuous_id)
  have hM : Continuous M := continuous_const.mul ((lipschitz_waringOscillatoryIntegral k).continuous.comp
    (continuous_id.mul continuous_const))
  have hG : Continuous G := continuous_e.comp ((continuous_const.add continuous_id).neg.mul continuous_const)
  have hmodel : ((c * P) ^ s * e (-((a : ℝ) / q) * n)) *
        (∫ β in u..v, waringOscillatoryIntegral k (β * (P : ℝ) ^ k) ^ s * e (-β * n)) =
        ∫ β in u..v, (M β) ^ s * G β := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun β _ => ?_
    simp only [M, G, mul_pow, neg_add, add_mul, e_add]
    ring
  change ‖(∫ β in u..v, F β ^ s * G β) - _‖ ≤ _
  rw [hmodel, ← intervalIntegral.integral_sub (f := fun β => F β ^ s * G β)
    (g := fun β => M β ^ s * G β) ((hF.pow s).mul hG |>.intervalIntegrable ..)
    ((hM.pow s).mul hG |>.intervalIntegrable ..)]
  have hc : ‖c‖ ≤ 1 := by
    rw [show ‖c‖ = ‖completeExpSum q a k‖ / (q : ℝ) by simp [c], div_le_one (Nat.cast_pos.mpr hq)]
    unfold completeExpSum
    apply (norm_sum_le _ _).trans
    simp [Complex.norm_exp, Complex.mul_re, ← Nat.cast_pow]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
    (f := fun β => F β ^ s * G β - M β ^ s * G β)
    (C := s * ((P : ℝ) + 1) ^ (s - 1) * (1 + 2 * q * (1 + 2 * Real.pi * η * (P : ℝ) ^ k))) (by
      intro β hβ
      rw [Set.uIoc_of_le huv] at hβ
      have hb : |β| ≤ η := abs_le.mpr ⟨hu.trans hβ.1.le, hβ.2.trans hv⟩
      have hfn : ‖F β‖ ≤ (P : ℝ) + 1 := by
        simpa [F, waringSum] using norm_genExpSum_le (fun _ : ℕ => (1 : ℂ))
          (fun j : ℕ => (j : ℤ) ^ k) (range (P + 1)) ((a : ℝ) / q + β)
      have hmn : ‖M β‖ ≤ (P : ℝ) + 1 := by
        calc ‖M β‖ ≤ (1 * (P : ℝ)) * 1 := by
               simp only [M, norm_mul, Complex.norm_natCast]
               gcongr
               exact norm_waringOscillatoryIntegral_le_one _ _
             _ ≤ _ := by linarith
      have hdiff := norm_waringSum_majorArc_sub_integral_le k P a hq β
      rw [integral_waringPhase_eq_scaled, ← mul_assoc] at hdiff
      rw [← sub_mul, norm_mul, show ‖G β‖ = 1 from norm_e _, mul_one]
      apply (norm_pow_sub_pow_bound _ _ (by positivity) hfn hmn s).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hdiff.trans (by gcongr))
  simpa [abs_of_nonneg (sub_nonneg.mpr huv), mul_comm] using h

/-- On the disjoint union of fixed-width arcs the arithmetic factor is a truncated
singular series. There are at most `B²` arcs, each of length `2/Q`. -/
theorem norm_waringMajorArcIntegralFixed_sub_main_le (k s P n : ℕ) {B : ℕ} (hB : 1 ≤ B)
    {Q : ℝ} (hBQ : 2 * (B : ℝ) ^ 2 < Q) :
    ‖majorArcIntegralFixed (fun α => waringSum k P α ^ s * e (-α * n)) B Q -
      (∑ q ∈ Icc 1 B, waringSingularTerm k s n q) * (P : ℂ) ^ s *
        ∫ β in (-(1 / Q))..(1 / Q), waringOscillatoryIntegral k (β * (P : ℝ) ^ k) ^ s * e (-β * n)‖ ≤
      (B : ℝ) ^ 2 * ((2 / Q) * (s * ((P : ℝ) + 1) ^ (s - 1) *
        (1 + 2 * B * (1 + 2 * Real.pi * (1 / Q) * (P : ℝ) ^ k)))) := by
  let F (α : ℝ) := waringSum k P α ^ s * e (-α * n)
  let J := ∫ β in (-(1 / Q))..(1 / Q), waringOscillatoryIntegral k (β * (P : ℝ) ^ k) ^ s * e (-β * n)
  let A (q a : ℕ) := (completeExpSum q a k / (q : ℂ)) ^ s * e (-(a : ℝ) * n / q)
  let D := (2 / Q) * (s * ((P : ℝ) + 1) ^ (s - 1) *
    (1 + 2 * (B : ℝ) * (1 + 2 * Real.pi * (1 / Q) * (P : ℝ) ^ k)))
  have hQ : 0 < Q := lt_of_le_of_lt (by positivity) hBQ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint (q : ℕ) (hq : q ∈ Icc 1 B) (a : ℕ) :
      ‖(∫ α in majorArcFixed q (a : ℤ) Q, F α) - A q a * (P : ℂ) ^ s * J‖ ≤ D := by
    have hq1 := (mem_Icc.mp hq).1
    have hh := norm_waringMajorArc_integral_sub_main_le k s P a n hq1
      (η := 1 / Q) (u := -(1 / Q)) (v := 1 / Q) le_rfl (neg_le_self (by positivity)) le_rfl
    rw [setIntegral_majorArcFixed_eq _ hq1 _ hQ]
    dsimp only [F, A, J]
    push_cast
    have he : -(a : ℝ) * n / q = -((a : ℝ) / q) * n := by ring
    rw [he, show (completeExpSum q a k / (q : ℂ)) ^ s * e (-((a : ℝ) / q) * n) * P ^ s =
        ((completeExpSum q a k / (q : ℂ)) * P) ^ s * e (-((a : ℝ) / q) * n) by rw [mul_pow]; ring]
    apply hh.trans
    dsimp [D]
    rw [show 1 / Q - -(1 / Q) = 2 / Q by ring]
    gcongr
    exact_mod_cast (mem_Icc.mp hq).2
  have hF : Continuous F := ((continuous_genExpSum _ _ _).pow s).mul
    (continuous_e.comp (continuous_id.neg.mul continuous_const))
  have hint : IntegrableOn F (majorArcsFixed (B : ℝ) Q) :=
    (hF.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (majorArcsFixed_subset_Icc (by exact_mod_cast hB) hBQ)
  change ‖majorArcIntegralFixed F (B : ℝ) Q - _ * _ * J‖ ≤ (B : ℝ) ^ 2 * D
  rw [majorArcIntegralFixed_eq_sum hBQ hint]
  simp only [majorArcDenoms, Nat.floor_natCast]
  have hmodel : (∑ q ∈ Icc 1 B, waringSingularTerm k s n q) * (P : ℂ) ^ s * J =
      ∑ q ∈ Icc 1 B, ∑ a ∈ coprimeResidues q, A q a * (P : ℂ) ^ s * J := by
    simp only [waringSingularTerm, A, sum_mul]
  rw [hmodel, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc _ ≤ ∑ _q ∈ Icc 1 B, (B : ℝ) * D := by
         refine sum_le_sum fun q hq => ?_
         rw [← sum_sub_distrib]
         apply (norm_sum_le _ _).trans
         calc _ ≤ ∑ _a ∈ coprimeResidues q, D := sum_le_sum fun a _ => hpoint q hq a
              _ ≤ _ := by
                rw [sum_const, nsmul_eq_mul]
                apply mul_le_mul_of_nonneg_right _ hD
                exact_mod_cast (card_filter_le ..).trans ((card_range q).le.trans (mem_Icc.mp hq).2)
       _ = _ := by simp; ring

end AnalyticNumberTheory.AdditiveNumberTheory
