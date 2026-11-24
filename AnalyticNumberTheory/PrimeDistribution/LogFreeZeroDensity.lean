import AnalyticNumberTheory.PrimeDistribution.DirichletZeroCountDensity
import AnalyticNumberTheory.PrimeDistribution.ZeroDensityIntegration
import AnalyticNumberTheory.SieveMethods.TuranPrimeMean

/-!
# Log-free zero density for primitive Dirichlet characters

Integrating the Turán prime detector around every zero retains multiplicities.
The denominator from the interval length cancels one power of the disk radius
in the prime-supported hybrid large sieve.
-/

noncomputable section

open Finset Complex MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.PrimeDistribution

lemma turan_detector_distance {σ η t : ℝ} {z : ℂ} (_hη : 0 < η)
    (hg : 4*(1-σ) ≤ η) (hz : σ ≤ z.re) (hz' : z.re < 1)
    (ht : t ∈ Set.Ioc (z.im-η/2) (z.im+η/2)) :
    ‖(((1+η:ℝ):ℂ)+(t:ℂ)*I)-z‖ ≤ 2*η := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp only [sub_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero,
    sub_im,add_im,mul_I_im,zero_add]
  rw [abs_of_nonneg (by linarith : 0≤1+η-z.re)]
  have hh : |t-z.im| ≤ η/2 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  linarith

lemma continuous_turan_prime_detector {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X U η : ℝ) (m : ℕ) :
    Continuous (fun t => ∑ p ∈ turanPrimes X U, turanMangoldtTerm χ η t m p) := by
  apply continuous_finsetSum
  intro p hp
  have hprime := (mem_filter.mp hp).2
  have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  apply Continuous.const_mul
  apply Continuous.const_mul
  apply Continuous.const_cpow _ (Or.inl hp')
  fun_prop

/-- The local density reduction to a family of prime-polynomial mean squares. -/
theorem turan_zero_count_integral :
    ∃ C > 0, ∃ K > 0, ∀ {Q : ℕ} {T σ η Y X U : ℝ} {M : ℕ},
    0 ≤ T → (Q:ℝ)*(T+3) ≤ Y → 0 < η → η ≤ 1/1024 → 1 ≤ η*Real.log Y →
    4*(1-σ) ≤ η → 1 ≤ X → X ≤ U → C*(1+η*Real.log Y) ≤ M →
    1024*(η*Real.log X) ≤ M → 128*(M:ℝ) ≤ η*Real.log U →
    ((1/128:ℝ)^(2*M+1))^2*η*(primitiveFamilyZeroCount Q σ T:ℝ) ≤
      (K*(1+η*Real.log Y)) * ∑ m ∈ Icc M (2*M), ∑ χ ∈ primitiveCharacterFamily Q,
      ∫ t in (-(T+1))..(T+1), ‖∑ p ∈ turanPrimes X U, turanMangoldtTerm χ.2 η t m p‖^2 := by
  obtain ⟨C,hC,HC⟩ := LFunction_turan_prime_detector
  obtain ⟨K,hK,HK⟩ := LFunction_turan_local_zero_count
  refine ⟨C,hC,K,hK,?_⟩
  intro Q T σ η Y X U M hT hY hη hη' hg hgap hX hU hM hlow hhigh
  let F := primitiveCharacterFamily Q
  let S (χ : (q : ℕ) × DirichletCharacter ℂ q) := nonprincipalDensityFinset χ.2 σ T
  let w (χ : (q : ℕ) × DirichletCharacter ℂ q) (z : ℂ) := (characterZeroMultiplicity χ.2 z:ℝ)
  let D (χ : (q : ℕ) × DirichletCharacter ℂ q) (m : ℕ) (t : ℝ) := ∑ p ∈ turanPrimes X U, turanMangoldtTerm χ.2 η t m p
  let orders := Icc M (2*M)
  let δ := (1/128:ℝ)^(2*M+1)
  have hone (χ : (q : ℕ) × DirichletCharacter ℂ q) (hχ : χ∈F) :
      δ^2*η*(∑ z ∈ S χ,w χ z) ≤ K*(1+η*Real.log Y) * ∑ m ∈ orders, ∫ t in (-(T+1))..(T+1), ‖D χ m t‖^2 := by
    have hq := mem_Icc.mp (mem_sigma.mp hχ).1
    let : NeZero χ.1 := ⟨by omega⟩
    have hqR : (χ.1:ℝ) ≤ Q := by exact_mod_cast hq.2
    have hqY (t : ℝ) (ht : t∈Set.Icc (-T-1) (T+1)) : (χ.1:ℝ)*(|t|+2) ≤ Y := by
      have habs : |t| ≤ T+1 := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
      apply le_trans _ hY
      exact mul_le_mul hqR (by linarith) (by positivity) (by positivity)
    have hmem (z : ℂ) (hz : z∈S χ) := (mem_nonprincipalDensityFinset χ.2).mp hz
    rw [show -(T+1) = -T-1 by ring]
    apply weighted_zero_detection_integral (S χ) orders Complex.im (w χ) (D χ) hT hη (by linarith)
      (show 0≤δ by positivity) (by positivity)
      (fun z hz => (hmem z hz).2.2.2.2.2) (fun z _ => Nat.cast_nonneg _)
      (fun m _ => continuous_turan_prime_detector ..)
    · intro t ht
      let Z := (S χ).filter (fun z => t ∈ Set.Ioc (z.im-η/2) (z.im+η/2))
      by_cases hn : Z.Nonempty
      · obtain ⟨z,hz⟩ := hn
        have hnχ := (hmem z (mem_filter.mp hz).1).1
        have hb := HK hnχ (hqY t ht) hη hη' hg Z (fun u hu => by
          obtain ⟨huz,htu⟩ := mem_filter.mp hu
          obtain ⟨_,hu',_,hσ,hu1,_⟩ := hmem u huz
          exact ⟨hu',turan_detector_distance hη hgap hσ hu1 htu⟩)
        simpa only [w,characterZeroMultiplicity,dite_eq_left (NeZero.ne χ.1)] using hb
      · change ∑ z ∈ Z, w χ z ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hn,sum_empty]; positivity
    · intro z hz t ht
      obtain ⟨hnχ,hL,_,hzσ,hz1,hzT⟩ := hmem z hz
      have hr := abs_le.mp hzT
      have ht' : t ∈ Set.Icc (-T-1) (T+1) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
      exact HC hnχ (hqY t ht') hη hη' hg hX hU hL (turan_detector_distance hη hgap hzσ hz1 ht) hM hlow hhigh
  have hsum := sum_le_sum hone
  unfold primitiveFamilyZeroCount
  push_cast
  change δ^2*η*(∑ χ ∈ F, ∑ z ∈ S χ,w χ z) ≤
    K*(1+η*Real.log Y)*(∑ m ∈ orders, ∑ χ ∈ F, ∫ t in (-(T+1))..(T+1), ‖D χ m t‖^2)
  simpa only [←mul_sum,sum_comm (s:=F) (t:=orders)] using hsum

/-- Optimize the detector order for any counting function reduced to the
primitive-family prime means. -/
theorem turan_count_of_prime_mean_integral (Z : ℕ → ℝ → ℝ → ℝ)
    (hI : ∃ C > 0, ∃ K > 0, ∀ {Q : ℕ} {T σ η Y X U : ℝ} {M : ℕ},
    1 ≤ Q → 0 ≤ T → (Q:ℝ)*(T+3) ≤ Y → 0 < η → η ≤ 1/1024 → 1 ≤ η*Real.log Y →
    4*(1-σ) ≤ η → 1 ≤ X → X ≤ U → C*(1+η*Real.log Y) ≤ M →
    1024*(η*Real.log X) ≤ M → 128*(M:ℝ) ≤ η*Real.log U →
    ((1/128:ℝ)^(2*M+1))^2*η*Z Q σ T ≤
      (K*(1+η*Real.log Y)) * ∑ m ∈ Icc M (2*M), ∑ χ ∈ primitiveCharacterFamily Q,
      ∫ t in (-(T+1))..(T+1), ‖∑ p ∈ turanPrimes X U, turanMangoldtTerm χ.2 η t m p‖^2) :
    ∃ C > 0, ∃ A > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ η Y : ℝ},
    0 ≤ T → (Q:ℝ)*(T+3) ≤ Y → 0 < η → η ≤ 1/1024 → 1 ≤ η*Real.log Y →
    4*(1-σ) ≤ η → Z Q σ T ≤ C*Real.exp (A*(η*Real.log Y)) := by
  obtain ⟨C,hC,K,hK,HI⟩ := hI
  let L := max C 16384 + 1
  let R := 2*L+1
  let B := 128*R
  let V := 6*Real.pi^3*B*(B+2*mertensOneBound)
  have hLC : C≤L := by dsimp [L]; linarith [le_max_left C (16384:ℝ)]
  have hL : 16384≤L := by dsimp [L]; linarith [le_max_right C (16384:ℝ)]
  have hR : 1≤R := by dsimp [R]; linarith
  have hB : 16≤B := by dsimp [B]; linarith
  have hV : 0<V := by dsimp only [V]; positivity [mertensOneBound_pos]
  refine ⟨K*V,by positivity,128*(4*R+2)+R+2,by positivity,?_⟩
  intro Q hQ T σ η Y hT hY hη hη' hg hgap
  have hqR : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hY1 : 1 ≤ Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hqR) (by linarith : 0≤T+3)]
  have hYp : 0 < Y := by linarith
  let a := η*Real.log Y
  have ha : 1 ≤ a := hg
  let M := ⌈L*(1+a)⌉₊
  have hM0 : L*(1+a) ≤ M := Nat.le_ceil _
  have hM1 : (M:ℝ) ≤ R*a := by
    have hh := Nat.ceil_lt_add_one (show 0≤L*(1+a) by positivity)
    change (M:ℝ)<L*(1+a)+1 at hh
    dsimp only [R]; nlinarith [mul_nonneg (by linarith : 0≤L) (sub_nonneg.mpr ha)]
  have hlow : 1024*(η*Real.log (Y^(16:ℝ))) ≤ M := by
    rw [Real.log_rpow hYp]
    have hh := mul_le_mul_of_nonneg_right hL (by linarith : 0≤a)
    change L*(1+η*Real.log Y) ≤ M at hM0
    dsimp only [a] at hh; linarith
  have hhigh : 128*(M:ℝ) ≤ η*Real.log (Y^B) := by
    rw [Real.log_rpow hYp]; dsimp only [B]
    calc
      _ ≤ 128*(R*a) := by gcongr
      _ = _ := by dsimp only [a]; ring
  let b := 2*M+1
  let count := Z Q σ T
  have hive := HI (M:=M) hQ hT hY hη hη' hg hgap
    (Real.one_le_rpow hY1 (by norm_num : (0:ℝ)≤16)) (Real.rpow_le_rpow_of_exponent_le hY1 hB)
    ((mul_le_mul_of_nonneg_right hLC (by linarith : 0≤1+a)).trans hM0) hlow hhigh
  have hmean := sum_le_sum (s:=Icc M (2*M)) (fun m _ => turan_prime_family_mean hQ hT hY (le_refl (16:ℝ)) hB hη.le m)
  simp only [sum_const,nsmul_eq_mul] at hmean
  have hcard : (Icc M (2*M)).card = M+1 := by rw [Nat.card_Icc]; omega
  rw [hcard] at hmean
  have hcombined := hive.trans (mul_le_mul_of_nonneg_left hmean (by positivity))
  change ((1/128:ℝ)^b)^2*η*count ≤ K*(1+a)*((↑(M+1):ℝ)*(V*η^2*Real.log Y)) at hcombined
  have hrest : ((1/128:ℝ)^b)^2 * count ≤ K*V*((1+a)*((M:ℝ)+1)*a) := by
    apply le_of_mul_le_mul_left (a:=η) (by
      calc
        _ = ((1/128:ℝ)^b)^2*η*count := by ring
        _ ≤ _ := hcombined
        _ = _ := by push_cast; dsimp only [a]; ring) hη
  have hZ : count ≤ K*V*(((128:ℝ)^b)^2 * ((1+a)*((M:ℝ)+1)*a)) := by
    have hh := mul_le_mul_of_nonneg_left hrest (show 0≤((128:ℝ)^b)^2 by positivity)
    calc
      _ = ((128:ℝ)^b)^2 * (((1/128:ℝ)^b)^2 * count) := by norm_num [div_pow,inv_pow]
      _ ≤ _ := hh
      _ = _ := by ring
  apply hZ.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpow : ((128:ℝ)^b)^2 ≤ Real.exp (128*(4*R+2)*a) := by
    calc
      _ ≤ (Real.exp 128 ^ b)^2 := by gcongr; linarith [Real.add_one_le_exp (128:ℝ)]
      _ = Real.exp ((2:ℝ)*(b*128)) := by rw [←Real.exp_nat_mul,←Real.exp_nat_mul]; norm_num
      _ ≤ _ := by apply Real.exp_le_exp.mpr; dsimp only [b]; push_cast; linarith
  have he1 : 1+a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have he2 : (M:ℝ)+1 ≤ Real.exp (R*a) := (by linarith [Real.add_one_le_exp (M:ℝ)] : (M:ℝ)+1≤Real.exp M).trans (Real.exp_le_exp.mpr hM1)
  have he3 : a ≤ Real.exp a := by linarith
  calc
    _ ≤ Real.exp (128*(4*R+2)*a)*(Real.exp a*Real.exp (R*a)*Real.exp a) := by gcongr
    _ = _ := by rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]; congr 1; ring


/-- In the near-one regime choose the detector order proportional to `η log Y`
and a fixed pair of powers of `Y` for the prime support. -/
theorem turan_zero_count_near_one :
    ∃ C > 0, ∃ A > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ η Y : ℝ},
    0 ≤ T → (Q:ℝ)*(T+3) ≤ Y → 0 < η → η ≤ 1/1024 → 1 ≤ η*Real.log Y →
    4*(1-σ) ≤ η → (primitiveFamilyZeroCount Q σ T:ℝ) ≤ C*Real.exp (A*(η*Real.log Y)) := by
  apply turan_count_of_prime_mean_integral (fun Q σ T => (primitiveFamilyZeroCount Q σ T:ℝ))
  obtain ⟨C,hC,K,hK,H⟩ := turan_zero_count_integral
  refine ⟨C,hC,K,hK,?_⟩
  intro Q T σ η Y X U M _
  exact H

/-- **Log-free zero density.** Count the nontrivial zeros of all nonprincipal
primitive Dirichlet characters of moduli up to `Q`, with multiplicities and
both signs of the ordinate. The constants are absolute. -/
theorem primitiveFamilyZeroCount_log_free :
    ∃ C > 0, ∃ A > 0, ∀ {Q : ℕ}, 1 ≤ Q → ∀ {T σ : ℝ}, 0 ≤ T → σ ∈ Set.Icc (0:ℝ) 1 →
      (primitiveFamilyZeroCount Q σ T:ℝ) ≤ C*((Q:ℝ)*(T+2))^(A*(1-σ)) := by
  obtain ⟨C,hC,A,hA,H⟩ := turan_zero_count_near_one
  obtain ⟨K,hK,HK⟩ := primitiveFamilyZeroCount_le
  let C' := max (C*Real.exp (4097*A)) K
  let A' := max (8*A) 45072
  have hC' : 0 < C' := lt_of_lt_of_le hK (le_max_right ..)
  have hA' : 0 < A' := lt_of_lt_of_le (by norm_num : (0:ℝ)<45072) (le_max_right ..)
  refine ⟨C',hC',A',hA',?_⟩
  intro Q hQ T σ hT hσ
  let V := (Q:ℝ)*(T+2)
  let d := 1-σ
  have hd : 0 ≤ d := sub_nonneg.mpr hσ.2
  have hd' : d ≤ 1 := by dsimp only [d]; linarith [hσ.1]
  have hq : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hV : 2 ≤ V := by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr hq) hT]
  have hV1 : 1 ≤ V := by linarith
  have hVp : 0<V := by linarith
  have hl := Real.log_nonneg hV1
  by_cases hnear : 4*d ≤ 1/1024
  · let Y := Real.exp 1024 * V^2
    have hY : (Q:ℝ)*(T+3) ≤ Y := by
      have hQV : (Q:ℝ)*(T+3) ≤ 2*V := by dsimp only [V]; nlinarith [mul_nonneg (show 0≤(Q:ℝ) by positivity) hT]
      have h2 : 2*V ≤ V^2 := by nlinarith [mul_nonneg (by linarith : 0≤V-2) hVp.le]
      exact hQV.trans (h2.trans (le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by norm_num))))
    have hlog : Real.log Y = 1024+2*Real.log V := by
      simp only [Y,Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ hVp.ne'),Real.log_exp,Real.log_pow,Nat.cast_ofNat]
    have hlogp : 0 < Real.log Y := by linarith
    let η := max (4*d) (1/Real.log Y)
    have hη : 0 < η := lt_of_lt_of_le (by positivity : 0<1/Real.log Y) (le_max_right ..)
    have hη' : η ≤ 1/1024 := max_le hnear ((div_le_iff₀ hlogp).mpr (by linarith))
    have hmass : η*Real.log Y = max (4*d*Real.log Y) 1 := by
      dsimp only [η]; rw [max_mul_of_nonneg _ _ hlogp.le,one_div,inv_mul_cancel₀ hlogp.ne']
    have hg : 1 ≤ η*Real.log Y := hmass ▸ le_max_right ..
    have hh := H hQ hT hY hη hη' hg (le_max_left ..)
    have he : η*Real.log Y ≤ 4097+8*d*Real.log V := by
      rw [hmass,hlog]; apply max_le
      · nlinarith only [hd']
      · nlinarith [mul_nonneg hd hl]
    apply hh.trans
    change C*Real.exp (A*(η*Real.log Y)) ≤ C'*V^(A'*d)
    calc
      _ ≤ C*Real.exp (A*(4097+8*d*Real.log V)) := by gcongr
      _ = (C*Real.exp (4097*A))*V^((8*A)*d) := by
        rw [Real.rpow_def_of_pos hVp,mul_assoc C (Real.exp _) (Real.exp _),←Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul (le_max_left ..)
        (Real.rpow_le_rpow_of_exponent_le hV1 (mul_le_mul_of_nonneg_right (le_max_left ..) hd)) (by positivity) hC'.le
  · have hdlarge : 11+16*d ≤ 45072*d := by linarith
    apply (HK hQ hT hσ).trans
    change K*(1+Real.log V)^11*V^(16*d) ≤ C'*V^(A'*d)
    have hlogV : 1+Real.log V ≤ V := by linarith [Real.log_le_sub_one_of_pos hVp]
    calc
      _ ≤ K*V^11*V^(16*d) := by gcongr
      _ = K*V^(11+16*d) := by rw [mul_assoc,←Real.rpow_natCast V 11,←Real.rpow_add hVp]; norm_num
      _ ≤ _ := mul_le_mul (le_max_right ..) (Real.rpow_le_rpow_of_exponent_le hV1
        (hdlarge.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hd))) (by positivity) hC'.le


end AnalyticNumberTheory.PrimeDistribution
