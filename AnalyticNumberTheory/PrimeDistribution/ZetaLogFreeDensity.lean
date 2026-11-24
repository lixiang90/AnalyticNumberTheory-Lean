import AnalyticNumberTheory.PrimeDistribution.LogFreeZeroDensity
import AnalyticNumberTheory.RiemannZeta.TuranDetection

/-!
# A log-free zero-density theorem for the Riemann zeta function

The zero count includes multiplicities and both signs of the ordinate.
Only zeros at height at least four enter the Turán argument. The remaining
compact set contributes an absolute constant.
-/

noncomputable section
open Finset Complex MeasureTheory
open scoped Classical
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- All nontrivial zeta zeros of height at most `T` to the right of `σ`. -/
def zetaDensityZeros (σ T : ℝ) : Finset ℂ := (nontrivialZerosUpTo T).filter (fun z => σ≤z.re)

/-- The two-sided zeta zero count, with multiplicities. -/
def zetaDensityCount (σ T : ℝ) : ℝ := ∑ z ∈ zetaDensityZeros σ T,(zeroMultiplicity z:ℝ)

private def highZeros (σ T : ℝ) := (zetaDensityZeros σ T).filter (fun z => 4≤|z.im|)

private theorem high_zero_count_near_one :
    ∃ C > 0, ∃ A > 0, ∀ {T σ η Y : ℝ},
    0≤T → T+3≤Y → 0<η → η≤1/1024 → 1≤η*Real.log Y → 4*(1-σ)≤η →
    ∑ z ∈ highZeros σ T,(zeroMultiplicity z:ℝ) ≤ C*Real.exp (A*(η*Real.log Y)) := by
  let Z (_ : ℕ) (σ T : ℝ) := ∑ z ∈ highZeros σ T,(zeroMultiplicity z:ℝ)
  suffices hI : ∃ C > 0, ∃ K > 0, ∀ {Q : ℕ} {T σ η Y X U : ℝ} {M : ℕ},
      1 ≤ Q → 0≤T → (Q:ℝ)*(T+3)≤Y → 0<η → η≤1/1024 → 1≤η*Real.log Y →
      4*(1-σ)≤η → 1≤X → X≤U → C*(1+η*Real.log Y)≤M →
      1024*(η*Real.log X)≤M → 128*(M:ℝ)≤η*Real.log U →
      ((1/128:ℝ)^(2*M+1))^2*η*Z Q σ T ≤ K*(1+η*Real.log Y) * ∑ m ∈ Icc M (2*M),
        ∑ χ ∈ primitiveCharacterFamily Q, ∫ t in (-(T+1))..(T+1),
          ‖∑ p ∈ turanPrimes X U,turanMangoldtTerm χ.2 η t m p‖^2 by
    obtain ⟨C,hC,A,hA,H⟩ := turan_count_of_prime_mean_integral Z hI
    refine ⟨C,hC,A,hA,?_⟩
    intro T σ η Y hT hY
    exact H (Q:=1) le_rfl hT (by simpa only [Nat.cast_one,one_mul] using hY)
  obtain ⟨C,hC,K,hK,H⟩ := zeta_turan_local_estimates
  refine ⟨C,hC,K,hK,?_⟩
  intro Q T σ η Y X U M hQ hT hY hη hη' hg hgap hX hU hM hlow hhigh
  let F := primitiveCharacterFamily Q
  let χ₀ : (q : ℕ) × DirichletCharacter ℂ q := ⟨1,1⟩
  have hχ : χ₀ ∈ F := mem_sigma.mpr ⟨mem_Icc.mpr ⟨le_rfl,hQ⟩,
    mem_filter.mpr ⟨mem_univ _,DirichletCharacter.isPrimitive_one_level_one⟩⟩
  let S := highZeros σ T
  let P (χ : (q : ℕ) × DirichletCharacter ℂ q) (m : ℕ) (t : ℝ) :=
    ∑ p ∈ turanPrimes X U,turanMangoldtTerm χ.2 η t m p
  have hTY : T+3 ≤ Y := (le_mul_of_one_le_left (by linarith : 0≤T+3) (by exact_mod_cast hQ)).trans hY
  have hmem (z : ℂ) (hz : z∈S) : riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ |z.im|≤T ∧ 4≤|z.im| := by
    obtain ⟨ha,hb⟩ := mem_filter.mp hz
    obtain ⟨ha',hσ⟩ := mem_filter.mp ha
    obtain ⟨hz',_,hr,ht⟩ := mem_nontrivialZerosUpTo.mp ha'
    exact ⟨hz',hσ,hr,ht,hb⟩
  have ht' (z : ℂ) (hz : z∈S) (t : ℝ) (ht : t∈Set.Ioc (z.im-η/2) (z.im+η/2)) :
      3≤|t| ∧ |t|+2≤Y := by
    have hd : |t-z.im|≤η/2 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hh := hmem z hz
    have hback := abs_sub_abs_le_abs_sub z.im t
    rw [abs_sub_comm] at hback
    exact ⟨by linarith [hh.2.2.2.2],by linarith [hh.2.2.2.1,abs_sub_abs_le_abs_sub t z.im]⟩
  have hK' : 0≤K*(1+η*Real.log Y) := by positivity
  have hn := weighted_zero_detection_integral S (Icc M (2*M)) Complex.im (fun z => (zeroMultiplicity z:ℝ)) (P χ₀)
    hT hη (by linarith) (show 0≤(1/128:ℝ)^(2*M+1) by positivity) hK'
    (fun z hz => (hmem z hz).2.2.2.1) (fun z _ => Nat.cast_nonneg _) (fun m _ => continuous_turan_prime_detector ..)
    (fun t _ => by
      let V := S.filter (fun z => t∈Set.Ioc (z.im-η/2) (z.im+η/2))
      by_cases hv : V.Nonempty
      · obtain ⟨z,hz⟩ := hv
        have hh := ht' z (mem_filter.mp hz).1 t (mem_filter.mp hz).2
        apply (H hh.1 hh.2 hη hη' hg).1 V
        intro u hu
        obtain ⟨hus,htu⟩ := mem_filter.mp hu
        have hd := hmem u hus
        exact ⟨hd.1,turan_detector_distance hη hgap hd.2.1 hd.2.2.1 htu⟩
      · change ∑ z ∈ V,(zeroMultiplicity z:ℝ) ≤ _
        rw [not_nonempty_iff_eq_empty.mp hv,sum_empty]; exact hK')
    (fun z hz t ht => by
      have hh := ht' z hz t ht
      have hd := hmem z hz
      exact (H hh.1 hh.2 hη hη' hg).2 hd.1 (turan_detector_distance hη hgap hd.2.1 hd.2.2.1 ht) hX hU hM hlow hhigh)
  rw [show -T-1 = -(T+1) by ring] at hn
  apply hn.trans
  apply mul_le_mul_of_nonneg_left _ hK'
  apply sum_le_sum; intro m hm
  apply single_le_sum (f:=fun χ => ∫ t in (-(T+1))..(T+1), ‖P χ m t‖^2) _ hχ
  intro χ _
  exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

/-- **Log-free zeta zero density.** Both signs of the ordinate and all
multiplicities are counted. The constants are independent of `T` and `σ`. -/
theorem zetaDensityCount_log_free :
    ∃ C > 0, ∃ A > 0, ∀ {T σ : ℝ}, 0≤T → σ∈Set.Icc (0:ℝ) 1 →
      zetaDensityCount σ T ≤ C*(T+2)^(A*(1-σ)) := by
  obtain ⟨C,hC,A,hA,H⟩ := high_zero_count_near_one
  obtain ⟨K,hK,HK⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  let A' := max (8*A) 8192
  let C' := max (4*K*Real.log 4+C*Real.exp (4097*A)) K
  have hC' : 0<C' := hK.trans_le (le_max_right ..)
  have hA' : 0<A' := (by norm_num : (0:ℝ)<8192).trans_le (le_max_right ..)
  refine ⟨C',hC',A',hA',?_⟩
  intro T σ hT hσ
  let V := T+2
  let d := 1-σ
  have hd : 0≤d := sub_nonneg.mpr hσ.2
  have hd' : d≤1 := by dsimp [d]; linarith [hσ.1]
  have hV : 2≤V := by dsimp [V]; linarith
  have hV1 : 1≤V := by linarith
  have hVp : 0<V := by linarith
  have hl := Real.log_nonneg hV1
  by_cases hn : 4*d≤1/1024
  · let Y := Real.exp 1024 * V^2
    have hY : T+3≤Y := by
      have hh : T+3 ≤ V^2 := by dsimp only [V]; nlinarith [sq_nonneg T]
      exact hh.trans (le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by norm_num)))
    have hlog : Real.log Y = 1024+2*Real.log V := by
      simp only [Y,Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ hVp.ne'),Real.log_exp,Real.log_pow,Nat.cast_ofNat]
    have hp : 0<Real.log Y := by linarith
    let η := max (4*d) (1/Real.log Y)
    have hη : 0<η := lt_of_lt_of_le (by positivity : 0<1/Real.log Y) (le_max_right ..)
    have hη' : η≤1/1024 := max_le hn ((div_le_iff₀ hp).mpr (by linarith))
    have hx : η*Real.log Y=max (4*d*Real.log Y) 1 := by
      dsimp only [η]; rw [max_mul_of_nonneg _ _ hp.le,one_div,inv_mul_cancel₀ hp.ne']
    have hbig := H hT hY hη hη' (hx ▸ le_max_right ..) (le_max_left ..)
    have he : η*Real.log Y ≤ 4097+8*d*Real.log V := by
      rw [hx,hlog]; apply max_le
      · nlinarith only [hd']
      · nlinarith [mul_nonneg hd hl]
    have highbd : ∑ z ∈ highZeros σ T,(zeroMultiplicity z:ℝ) ≤
        (C*Real.exp (4097*A))*V^(A'*d) := by
      calc
        _ ≤ C*Real.exp (A*(η*Real.log Y)) := hbig
        _ ≤ C*Real.exp (A*(4097+8*d*Real.log V)) := by gcongr
        _ = (C*Real.exp (4097*A))*V^((8*A)*d) := by
          rw [Real.rpow_def_of_pos hVp,mul_assoc C (Real.exp _) (Real.exp _),←Real.exp_add]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hV1 (mul_le_mul_of_nonneg_right (le_max_left ..) hd)) (by positivity)
    let low := (zetaDensityZeros σ T).filter (fun z => ¬4≤|z.im|)
    have hsub : low⊆nontrivialZerosUpTo 4 := by
      intro z hz
      obtain ⟨hmem,ht⟩ := mem_filter.mp hz
      obtain ⟨h1,h2,h3,_⟩ := mem_nontrivialZerosUpTo.mp (mem_filter.mp hmem).1
      exact mem_nontrivialZerosUpTo.mpr ⟨h1,h2,h3,le_of_lt (lt_of_not_ge ht)⟩
    have hlow := (sum_le_sum_of_subset_of_nonneg (f:=fun z => (zeroMultiplicity z:ℝ)) hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
      (HK 4 (by norm_num))
    have hlow' : (∑ z ∈ low,(zeroMultiplicity z:ℝ)) ≤ 4*K*Real.log 4*V^(A'*d) := by
      apply hlow.trans
      rw [mul_comm K 4]
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hV1 (by positivity))
    have heq : zetaDensityCount σ T = (∑ z ∈ low,(zeroMultiplicity z:ℝ)) + ∑ z ∈ highZeros σ T,(zeroMultiplicity z:ℝ) := by
      rw [add_comm]; exact (sum_filter_add_sum_filter_not ..).symm
    rw [heq]
    calc
      _ ≤ (4*K*Real.log 4+C*Real.exp (4097*A))*V^(A'*d) := by rw [add_mul]; exact add_le_add hlow' highbd
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
  · have hsub : zetaDensityZeros σ T ⊆ nontrivialZerosUpTo V := by
      intro z hz
      obtain ⟨h1,h2,h3,h4⟩ := mem_nontrivialZerosUpTo.mp (mem_filter.mp hz).1
      exact mem_nontrivialZerosUpTo.mpr ⟨h1,h2,h3,h4.trans (by dsimp [V]; linarith)⟩
    have hh := (sum_le_sum_of_subset_of_nonneg (f:=fun z => (zeroMultiplicity z:ℝ)) hsub (fun _ _ _ => Nat.cast_nonneg _)).trans (HK V hV)
    have ha : 2 ≤ A'*d := (by linarith : 2≤8192*d).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hd)
    apply hh.trans
    calc
      _ ≤ K*V*V := by gcongr; linarith [Real.log_le_sub_one_of_pos hVp]
      _ = K*V^(2:ℝ) := by rw [Real.rpow_two]; ring
      _ ≤ _ := mul_le_mul (le_max_right ..) (Real.rpow_le_rpow_of_exponent_le hV1 ha) (by positivity) hC'.le


end AnalyticNumberTheory.PrimeDistribution
