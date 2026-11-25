import AnalyticNumberTheory.PrimeDistribution.HuxleyRationalBalance
import AnalyticNumberTheory.PrimeDistribution.HuxleyTypeI
import AnalyticNumberTheory.PrimeDistribution.HuxleyTypeII
import AnalyticNumberTheory.PrimeDistribution.HuxleyMobiusDistribution
import AnalyticNumberTheory.PrimeDistribution.HuxleyZeroDetector
import AnalyticNumberTheory.PrimeDistribution.InghamDensity

/-!
# Huxley's zero-density theorem

The large-value bound for the polynomial detector and the weak distribution
of the Möbius mollifier yield the rational Huxley exponent, and hence
the uniform density constant `12/5` on the full half-strip.
-/
noncomputable section
open Complex Real Finset Filter MeasureTheory Asymptotics
open scoped ArithmeticFunction.Moebius Classical
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

private theorem unit_interval_zero_count :
    ∃ K> (0:ℝ), ∀ {T : ℕ}, 1≤T → ∀ {σ : ℝ}, 1/2≤σ → ∀ S : Finset ℂ,
      (∀ z∈S, riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ (T:ℝ)≤z.im ∧ z.im≤2*T) →
      ∀ u : ℝ, ((S.filter (fun z => u≤z.im ∧ z.im≤u+1)).card:ℝ) ≤ K*(1+Real.log T) := by
  obtain ⟨C,hC,h⟩ := sum_zeroMultiplicity_strip_le
  refine ⟨5*C,by positivity,?_⟩
  intro T hT σ hσ S hS u
  let W := S.filter (fun z => u≤z.im ∧ z.im≤u+1)
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : 0<(T:ℝ) := by linarith
  have hL : 0≤1+Real.log T := by linarith [Real.log_nonneg hTr]
  change (W.card:ℝ) ≤ _
  rcases W.eq_empty_or_nonempty with he | ⟨w,hw⟩
  · rw [he,card_empty,Nat.cast_zero]; positivity
  obtain ⟨hws,hw₁,hw₂⟩ := mem_filter.mp hw
  have hu : 0≤u := by linarith [(hS w hws).2.2.2.1]
  have hu' : u+2≤4*T := by linarith [(hS w hws).2.2.2.2]
  have h₀ : (W.card:ℝ) ≤ ∑ z∈W, (zeroMultiplicity z:ℝ) := by
    rw [show (W.card:ℝ)=∑ _z∈W,(1:ℝ) by simp]
    refine sum_le_sum fun z hz => ?_
    obtain ⟨hh,h₁,h₂,_⟩ := hS z (mem_filter.mp hz).1
    exact_mod_cast (zeroMultiplicity_pos_iff (by linarith) h₂).mpr hh
  have h₁ := h u W (by
    intro z hz
    obtain ⟨hzs,ha,hb⟩ := mem_filter.mp hz
    obtain ⟨hz₀,hz₁,hz₂,_⟩ := hS z hzs
    exact ⟨hz₀,by linarith,hz₂,abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have hlog := Real.log_le_log (by linarith : 0<u+2) hu'
  rw [Real.log_mul (by norm_num) hT0.ne'] at hlog
  rw [abs_of_nonneg hu] at h₁
  apply (h₀.trans h₁).trans
  have hh : Real.log (u+2) ≤ 5*(1+Real.log T) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4), Real.log_nonneg hTr]
  exact (mul_le_mul_of_nonneg_left hh hC.le).trans_eq (by ring)

private theorem huxley_rational_large_band :
    ∃ D>(0:ℝ), ∀ᶠ T : ℕ in atTop, ∀ {σ : ℝ}, σ∈Set.Icc (3/4:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z∈S, riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ (T:ℝ)≤z.im ∧ z.im≤2*T) →
      (S.card:ℝ) ≤ D*(1+Real.log T)^21*(T:ℝ)^(huxleyRationalExponent σ) := by
  obtain ⟨A,hA,hdetect⟩ := huxley_zero_detector
  obtain ⟨K,hK,hunit⟩ := unit_interval_zero_count
  obtain ⟨M,hM,hmob⟩ := huxley_mobius_weak_distribution
  obtain ⟨C₁,hC₁,hI⟩ := huxley_typeI_count hK
  obtain ⟨C₂,hC₂,hII⟩ := huxley_typeII_count hK hM
  let P := (1+8*A)^3
  have hP : 0<P := by dsimp [P]; positivity
  refine ⟨5*C₁+2*C₂*P,by positivity,?_⟩
  have hlog : ∀ᶠ T : ℕ in atTop, 4≤Real.log T :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hdetect,hlog,eventually_ge_atTop 16] with T hd hlog hT σ hσ S hS
  have hTr : (16:ℝ)≤T := by exact_mod_cast hT
  have hT0 : 0<(T:ℝ) := by linarith
  have hT₁ : 1≤T := by omega
  let X := ⌊(T:ℝ)^(huxleyRationalMollifierExponent σ)⌋₊
  let Y := (T:ℝ)^(huxleyRationalCutoffExponent σ)
  let Z := (T:ℝ)^(huxleyRationalExponent σ)
  let L := 1+Real.log T
  let V := 1/(8*A*L*Y^(1/2-σ))
  have hL : 1≤L := by dsimp [L]; linarith
  have hY0 : 0<Y := Real.rpow_pos_of_pos hT0 _
  have hZ : 0≤Z := Real.rpow_nonneg hT0.le _
  have hV : 0<V := by dsimp [V]; positivity
  obtain ⟨hX,_,hXP,hPT,hTY,hY⟩ := huxley_cutoff_range_of_conditions (by linarith : 1≤(T:ℝ)) (huxley_rational_cutoff_conditions hσ)
  have hXT : X≤T := Nat.cast_le.mp (hXP.trans hPT)
  have hXY : (X:ℝ)≤Y := (hXP.trans hPT).trans hTY
  have hTY' : (16:ℝ)≤Y := hTr.trans hTY
  have hY₁ : 1≤Y := by linarith
  have hgap : 1/Real.log T ≤ σ-1/2 := (div_le_iff₀ (by linarith)).mpr
    (by nlinarith only [mul_nonneg (sub_nonneg.mpr (hσ.1)) (sub_nonneg.mpr hlog),hlog,hσ.1])
  let large (z : ℂ) := (1/8:ℝ)≤‖∑ n∈Ioc X ⌊Y⌋₊, inghamRieszCoeff X Y n*(n:ℂ)^(-z)‖
  let S₁ := S.filter large
  let S₂ := S.filter (fun z => ¬large z)
  have hS₁ : S₁⊆S := filter_subset ..
  have hS₂ : S₂⊆S := filter_subset ..
  have hbal := huxley_balance_cutoffs_of_conditions (by linarith : 1≤(T:ℝ)) hσ (huxley_rational_cutoff_conditions hσ)
  change (⌊Y⌋₊:ℝ)^(2*(1-σ))+(T:ℝ)*(X:ℝ)^(4-6*σ) ≤ 5*Z ∧
    (T:ℝ)^(1/3:ℝ)*(X:ℝ)^(2/3:ℝ)*(Y^(1/2-σ))^(4/3:ℝ)+
    T*(X:ℝ)^(2/5:ℝ)*(Y^(1/2-σ))^(12/5:ℝ) ≤ 2*Z at hbal
  have hc₁ := hI hT₁ hX ((Nat.one_le_floor_iff _).mpr hY₁) ((Nat.floor_le hY0.le).trans hY)
    hσ (inghamRieszCoeff X Y) (norm_inghamRieszCoeff hY0 X) S₁
    (fun z hz => ⟨(hS z (hS₁ hz)).2.1,(hS z (hS₁ hz)).2.2.2⟩)
    (hunit hT₁ (by linarith [hσ.1] : 1/2≤σ) S₁ (fun z hz => hS z (hS₁ hz)))
    (fun z hz => (mem_filter.mp hz).2)
  have h₁ : (S₁.card:ℝ) ≤ C₁*L^21*(5*Z) := hc₁.trans (mul_le_mul_of_nonneg_left hbal.1 (by positivity))
  let J (z : ℂ) := ∫ v in -(4*(T:ℝ))..4*T, (1/(1+|v|)^4)*
    (‖riemannZeta ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖*
      ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖)
  have hJ (z : ℂ) : 0≤J z := intervalIntegral.integral_nonneg (by linarith : -(4*(T:ℝ))≤4*T) (fun _ _ => by positivity)
  have hd₂ (z : ℂ) (hz : z∈S₂) : V≤J z := by
    obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := hS z (hS₂ hz)
    have he := (hd X Y z hX hXT hXY hTY' hY (by linarith) h₂ h₃ h₄ h₀).resolve_left (mem_filter.mp hz).2
    change 1/8 ≤ A*L*Y^(1/2-z.re)*J z at he
    have hb := Real.rpow_le_rpow_of_exponent_le hY₁ (by linarith : 1/2-z.re≤1/2-σ)
    apply (div_le_iff₀ (by positivity : 0<8*A*L*Y^(1/2-σ))).mpr
    linarith only [he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity : 0≤A*L)) (hJ z))]
  have him (z : ℂ) (hz : z∈S₂) : 0≤z.im ∧ z.im≤2*T :=
    ⟨hT0.le.trans (hS z (hS₂ hz)).2.2.2.1,(hS z (hS₂ hz)).2.2.2.2⟩
  have hf (j : ℕ) (_ : j<2*T+1) : ((S₂.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ K*(1+Real.log T) := by
    apply le_trans _ (hunit hT₁ (by linarith [hσ.1] : 1/2≤σ) S₂ (fun z hz => hS z (hS₂ hz)) (j:ℝ))
    apply Nat.cast_le.mpr; apply card_le_card
    intro z hz
    obtain ⟨hs,hj⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hs,by simpa only [←hj] using Nat.floor_le (him z hs).1,
      by simpa only [←hj] using (Nat.lt_floor_add_one z.im).le⟩
  have hc₂ := hII hT₁ hX hV him hf hd₂ (hmob hX hXT)
  have vpow {k : ℝ} (hk : 0≤k) (hk' : k≤3) :
      V^(-k) ≤ P*L^3*(Y^(1/2-σ))^k := by
    have he : (8*A*L)^k ≤ P*L^3 := by
      calc
        _ ≤ ((1+8*A)*L)^k := Real.rpow_le_rpow (by positivity) (by linarith) hk
        _ ≤ ((1+8*A)*L)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le
          (one_le_mul_of_one_le_of_one_le (by linarith) hL) hk'
        _ = _ := by dsimp [P]; norm_cast; ring
    dsimp only [V]
    rw [Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,Real.mul_rpow (by positivity : 0≤8*A*L) (by positivity)]
    exact mul_le_mul_of_nonneg_right he (by positivity)
  have h₃ := vpow (by norm_num : 0≤(4/3:ℝ)) (by norm_num)
  have h₄ := vpow (by norm_num : 0≤(12/5:ℝ)) (by norm_num)
  have hsum : (T:ℝ)^(1/3:ℝ)*(X:ℝ)^(2/3:ℝ)*V^(-(4/3):ℝ)+
      T*(X:ℝ)^(2/5:ℝ)*V^(-(12/5):ℝ) ≤ P*L^3*(2*Z) := by
    calc
      _ ≤ (T:ℝ)^(1/3:ℝ)*(X:ℝ)^(2/3:ℝ)*(P*L^3*(Y^(1/2-σ))^(4/3:ℝ))+
          T*(X:ℝ)^(2/5:ℝ)*(P*L^3*(Y^(1/2-σ))^(12/5:ℝ)) := by gcongr
      _ = P*L^3*((T:ℝ)^(1/3:ℝ)*(X:ℝ)^(2/3:ℝ)*(Y^(1/2-σ))^(4/3:ℝ)+
          T*(X:ℝ)^(2/5:ℝ)*(Y^(1/2-σ))^(12/5:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbal.2 (by positivity)
  have h₂ := hc₂.trans (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤C₂*L^10))
  have hc : (S.card:ℝ)=S₁.card+(S₂.card:ℝ) := by exact_mod_cast (card_filter_add_card_filter_not (s:=S) large).symm
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by decide : 13≤21)) (by positivity : 0≤C₂*P*Z)
  change (S.card:ℝ)≤(5*C₁+2*C₂*P)*L^21*Z
  linarith only [hc,h₁,h₂,hh]

/-- The full dyadic density estimate includes the left part of the strip via
Ingham's exponent, and all bounded heights via the finite zero count. -/
theorem ingham_huxley_zeroDensity_band :
    ∃ D>(0:ℝ), ∀ {T : ℕ}, 1≤T → ∀ {σ : ℝ}, σ∈Set.Icc (1/2:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z∈S, riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ (T:ℝ)≤z.im ∧ z.im≤2*T) →
      (S.card:ℝ) ≤ D*(1+Real.log T)^21*(T:ℝ)^(inghamHuxleyExponent σ) := by
  obtain ⟨A,hA,ha⟩ := ingham_zeroDensity_band
  obtain ⟨B,hB,hb⟩ := huxley_rational_large_band
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  let F := (zeroDensityN 0 (2*(N:ℝ)):ℝ)
  let D := max A (max B F)
  have hAD : A≤D := le_max_left ..
  have hBD : B≤D := (le_max_left ..).trans (le_max_right ..)
  have hFD : F≤D := (le_max_right ..).trans (le_max_right ..)
  refine ⟨D,hA.trans_le hAD,?_⟩
  intro T hT σ hσ S hS
  have hTr : (1:ℝ)≤T := by exact_mod_cast hT
  have hL : 1≤1+Real.log T := by linarith [Real.log_nonneg hTr]
  have hP : 0 ≤ inghamHuxleyExponent σ := (ingham_huxley_exponent_bounds hσ).1
  have hZ : 1≤(T:ℝ)^(inghamHuxleyExponent σ) := Real.one_le_rpow hTr hP
  by_cases hlarge : N≤T
  · by_cases hs : 3/4≤σ
    · have hp := (hN T hlarge ⟨hs,hσ.2⟩ S hS).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBD (by positivity : 0≤(1+Real.log T)^21)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      simpa only [inghamHuxleyExponent,ite_eq_left hs] using hp
    · have hh := ha hT hσ S hS
      rw [inghamHuxleyExponent,ite_eq_right hs]
      exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul hAD (pow_le_pow_right₀ hL (by decide : 10≤21))
        (pow_nonneg (zero_le_one.trans hL) _) (hA.le.trans hAD)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have hsub : S⊆zeroDensityFinset 0 (2*(N:ℝ)) := by
      intro z hz
      obtain ⟨hz₀,hz₁,hz₂,hz₃,hz₄⟩ := hS z hz
      have hTN : (T:ℝ)≤N := by exact_mod_cast (show T≤N by omega)
      exact mem_zeroDensityFinset.mpr ⟨hz₀,by linarith [hσ.1],hz₂,by linarith,by linarith⟩
    have hf : (S.card:ℝ) ≤ F := by dsimp [F]; rw [zeroDensityN_eq_card]; exact_mod_cast card_le_card hsub
    exact hf.trans (hFD.trans ((le_mul_of_one_le_right (hA.le.trans hAD) (one_le_pow₀ hL)).trans
      (le_mul_of_one_le_right (by positivity) hZ)))

/-- The uniform linear Huxley coefficient also gives the finite band
estimate on the whole right half-strip. -/
theorem huxley_zeroDensity_band :
    ∃ D>(0:ℝ), ∀ {T : ℕ}, 1≤T → ∀ {σ : ℝ}, σ∈Set.Icc (1/2:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z∈S, riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ (T:ℝ)≤z.im ∧ z.im≤2*T) →
      (S.card:ℝ) ≤ D*(1+Real.log T)^21*(T:ℝ)^(huxleyExponent σ) := by
  obtain ⟨D,hD,H⟩ := ingham_huxley_zeroDensity_band
  refine ⟨D,hD,?_⟩
  intro T hT σ hσ S hS
  have ht : (1:ℝ)≤T := by exact_mod_cast hT
  exact (H hT hσ S hS).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ht (ingham_huxley_exponent_bounds hσ).2)
    (mul_nonneg hD.le (pow_nonneg (by linarith [Real.log_nonneg ht]) _)))

/-- The piecewise Ingham–Huxley exponent for the full distinct count. -/
theorem ingham_huxley_zeroDensity_distinct :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2≤T →
      (zeroDensityN σ T:ℝ) ≤ D*T^(inghamHuxleyExponent σ)*(Real.log T)^22 := by
  obtain ⟨C,hC,H⟩ := ingham_huxley_zeroDensity_band
  exact zeroDensity_of_dyadic_power_bound inghamHuxleyExponent 21 (fun _ h => (ingham_huxley_exponent_bounds h).1) hC H

/-- The piecewise Ingham–Huxley exponent with analytic multiplicities. -/
theorem ingham_huxley_zeroDensity_with_multiplicity :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2≤T →
      (∑ z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤D*T^(inghamHuxleyExponent σ)*(Real.log T)^23 :=
  zeroDensity_with_multiplicity_of_power_bound inghamHuxleyExponent 22 ingham_huxley_zeroDensity_distinct

/-- Distinct zeros on the full range of Huxley's rational exponent. -/
theorem huxley_rational_zeroDensity_distinct :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (3/4:ℝ) 1, ∀ T : ℝ, 2≤T →
      (zeroDensityN σ T:ℝ)≤D*T^(huxleyRationalExponent σ)*(Real.log T)^22 := by
  obtain ⟨D,hD,H⟩ := ingham_huxley_zeroDensity_distinct
  refine ⟨D,hD,?_⟩
  intro σ hσ T hT
  simpa only [inghamHuxleyExponent,ite_eq_left hσ.1] using H σ ⟨by linarith [hσ.1],hσ.2⟩ T hT

/-- Huxley's rational exponent on its full closed range, including
multiplicities and retaining twenty-three powers of the logarithm. -/
theorem huxley_rational_zeroDensity_with_multiplicity :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (3/4:ℝ) 1, ∀ T : ℝ, 2≤T →
      (∑ z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤D*T^(huxleyRationalExponent σ)*(Real.log T)^23 := by
  obtain ⟨D,hD,H⟩ := ingham_huxley_zeroDensity_with_multiplicity
  refine ⟨D,hD,?_⟩
  intro σ hσ T hT
  simpa only [inghamHuxleyExponent,ite_eq_left hσ.1] using H σ ⟨by linarith [hσ.1],hσ.2⟩ T hT

private theorem huxley_logarithm_loss {T : ℝ} (hT : 2≤T) :
    (Real.log T)^23≤32*(Real.log T)^28 := by
  have hL : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log zero_lt_two hT)
  have hs := one_le_pow₀ (by linarith : 1≤2*Real.log T) (n:=5)
  have hl := mul_le_mul_of_nonneg_right hs (pow_nonneg (by linarith : 0≤Real.log T) 23)
  linarith only [hl]

/-- Classical rational Huxley density bound with twenty-eight logarithms. -/
theorem huxley_rational_zeroDensity_classical :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (3/4:ℝ) 1, ∀ T : ℝ, 2≤T →
      (∑ z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤
        D*T^((5*σ-3)*(1-σ)/(σ^2+σ-1))*(Real.log T)^28 := by
  obtain ⟨D,hD,H⟩ := huxley_rational_zeroDensity_with_multiplicity
  refine ⟨32*D,by positivity,?_⟩
  intro σ hσ T hT
  have hp := huxley_logarithm_loss hT
  exact (H σ hσ T hT).trans ((mul_le_mul_of_nonneg_left hp (by positivity : 0≤D*T^(huxleyRationalExponent σ))).trans_eq (by unfold huxleyRationalExponent;ring))

/-- Huxley's global estimate for distinct zeros throughout the closed right
half of the critical strip. -/
theorem huxley_zeroDensity_distinct :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2≤T →
      (zeroDensityN σ T:ℝ) ≤ D*T^(huxleyExponent σ)*(Real.log T)^22 := by
  obtain ⟨C,hC,h⟩ := huxley_zeroDensity_band
  exact zeroDensity_of_dyadic_power_bound huxleyExponent 21
    (fun σ hσ => by dsimp [huxleyExponent]; linarith [hσ.2]) hC h

/-- The count with multiplicity costs one further logarithm. -/
theorem huxley_zeroDensity_with_multiplicity :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2≤T →
      (∑ ρ∈zeroDensityFinset σ T,(zeroMultiplicity ρ:ℝ)) ≤
        D*T^(huxleyExponent σ)*(Real.log T)^23 :=
  zeroDensity_with_multiplicity_of_power_bound huxleyExponent 22 huxley_zeroDensity_distinct

/-- Huxley's zero-density theorem in the conventional formulation with
twenty-eight logarithms and positive ordinates counted with multiplicity. -/
theorem huxley_zeroDensity_classical :
    ∃ D>(0:ℝ), ∀ σ∈Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2≤T →
      (∑ ρ∈zeroDensityFinset σ T,(zeroMultiplicity ρ:ℝ)) ≤
        D*T^(12*(1-σ)/5)*(Real.log T)^28 := by
  obtain ⟨C,hC,h⟩ := huxley_zeroDensity_with_multiplicity
  refine ⟨32*C,by positivity,?_⟩
  intro σ hσ T hT
  have hlog := huxley_logarithm_loss hT
  have he : huxleyExponent σ = 12*(1-σ)/5 := by dsimp [huxleyExponent]; ring
  apply (h σ hσ T hT).trans
  rw [he]; apply (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤C*T^(12*(1-σ)/5))).trans_eq
  ring

/-- Density hypothesis with coefficient twelve fifths, ready for prime
distribution in polynomially short intervals. -/
theorem huxley_zeroDensity : ZeroDensityHypothesis (12/5) 22 := by
  obtain ⟨C,hC,h⟩ := huxley_zeroDensity_distinct
  refine ⟨C,hC,fun σ hσ T hT => ?_⟩
  simpa only [huxleyExponent,show (Real.log T)^(22:ℝ)=(Real.log T)^22 by norm_cast] using h σ hσ T hT

/-- Prime number theorem in intervals of exponent greater than seven twelfths
assuming a super-logarithmic zero-free region. -/
theorem huxley_primePi_shortInterval_of_superLogZeroFree (hz : SuperLogZeroFreeHypothesis)
    {θ : ℝ} (hθ : 7/12<θ) (hθ' : θ<1) :
    (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] fun x => x^θ/Real.log x := by
  apply primePi_shortInterval_of_theta_equivalent hθ'.le
  apply theta_shortInterval_of_psi_equivalent (by linarith) hθ'.le
  exact psi_shortInterval_isEquivalent_of_zeroDensity huxley_zeroDensity truncatedExplicitFormula
    hz (by linarith) hθ' (by linarith)

end AnalyticNumberTheory.PrimeDistribution
