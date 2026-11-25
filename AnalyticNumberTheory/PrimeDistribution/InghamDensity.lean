import AnalyticNumberTheory.PrimeDistribution.InghamZeroDetector
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamTypeI
import AnalyticNumberTheory.PrimeDistribution.InghamTypeII
import AnalyticNumberTheory.PrimeDistribution.InghamDyadic
import AnalyticNumberTheory.PrimeDistribution.InghamApplications

/-!
# Ingham's zero-density theorem

For `1/2 ≤ σ ≤ 1`, the number of zeros of zeta up to height `T` has
power exponent `3(1−σ)/(2−σ)`. The finite-polynomial and critical-line
integral alternatives give the same exponent at the balanced cutoff.
-/
noncomputable section
open Finset Complex Real Filter MeasureTheory
open scoped ArithmeticFunction.Moebius Classical
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

private theorem ingham_unit_density :
    ∃ K > (0:ℝ), ∀ {X : ℕ}, 1 ≤ X → ∀ {σ : ℝ}, σ ∈ Set.Icc (1/2:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z ∈ S, riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.re < 1 ∧ (X:ℝ) ≤ z.im ∧ z.im ≤ 2*X) →
      ∀ j < 2*X+1, ((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ K*(1+Real.log X) := by
  obtain ⟨C₀,hC₀,hzeros⟩ := sum_zeroMultiplicity_strip_le
  let K := 5*C₀
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro X hX σ hσ S hS j hj
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : 0 < (X:ℝ) := by linarith
  let W := S.filter (fun z => ⌊z.im⌋₊=j)
  have hb := hzeros (j:ℝ) W (by
    intro z hz
    obtain ⟨hS',hj'⟩ := mem_filter.mp hz
    obtain ⟨hz₁,hz₂,hz₃,hz₄,hz₅⟩ := hS z hS'
    have hf := Nat.floor_le (hX0.le.trans hz₄)
    have hf' := Nat.lt_floor_add_one z.im
    rw [hj'] at hf hf'
    exact ⟨hz₁, by linarith [hσ.1], hz₃, abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have hh : (W.card:ℝ) ≤ ∑ z ∈ W, (zeroMultiplicity z : ℝ) := by
    rw [show (W.card:ℝ) = ∑ _z ∈ W, (1:ℝ) by simp]
    refine sum_le_sum fun z hz => ?_
    obtain ⟨h₁,h₂,h₃,_⟩ := hS z (mem_filter.mp hz).1
    exact_mod_cast (zeroMultiplicity_pos_iff (by linarith [hσ.1]) h₃).mpr h₁
  apply (hh.trans hb).trans
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have harg : (j:ℝ)+2 ≤ 4*X := by exact_mod_cast (show j+2 ≤ 4*X by omega)
  have h := Real.log_le_log (by positivity) harg
  rw [Real.log_mul (by norm_num) hX0.ne'] at h
  have hlog : Real.log ((j:ℝ)+2) ≤ 5*(1+Real.log X) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4), Real.log_nonneg hXr]
  exact (mul_le_mul_of_nonneg_left hlog hC₀.le).trans_eq (by dsimp [K]; ring)

private theorem ingham_large_band :
    ∃ E > (0:ℝ), ∀ᶠ X : ℕ in atTop, ∀ {σ : ℝ}, σ ∈ Set.Icc (1/2:ℝ) 1 →
      1/Real.log X ≤ σ-1/2 → ∀ S : Finset ℂ,
      (∀ z ∈ S, riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.re < 1 ∧ (X:ℝ) ≤ z.im ∧ z.im ≤ 2*X) →
      (S.card:ℝ) ≤ E*(1+Real.log X)^6*(X:ℝ)^(inghamExponent σ) := by
  obtain ⟨A,hA,hdet⟩ := ingham_zero_detector
  obtain ⟨D,hD,hII⟩ := ingham_typeII_count
  obtain ⟨K,hK,hunit⟩ := ingham_unit_density
  let C₁ := 64*(2304*π^3*K)*2^5
  let C₂ := 1+D*K^3*(8*A)^4
  have hc₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hc₂ : 0 < C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁+C₂,by positivity,?_⟩
  filter_upwards [hdet,eventually_ge_atTop 2] with X hd hX σ hσ hgap S hS
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : 0 < (X:ℝ) := by linarith
  let L := 1+Real.log X
  let Y := inghamCutoff (X:ℝ) σ
  let Z := (X:ℝ)^(inghamExponent σ)
  have hZ : 0 ≤ Z := Real.rpow_nonneg hX0.le _
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by linarith : 1≤(X:ℝ))]
  obtain ⟨hXY,hY⟩ := inghamCutoff_range (by linarith : 1≤(X:ℝ)) hσ
  change (X:ℝ) ≤ Y at hXY
  change Y ≤ _ at hY
  have hY1 : 1 ≤ Y := (by linarith : 1≤(X:ℝ)).trans hXY
  have hY0 : 0 < Y := by linarith
  have hYF : 1 ≤ ⌊Y⌋₊ := (Nat.one_le_floor_iff _).mpr hY1
  let P (z : ℂ) := (1/8:ℝ) ≤ ‖∑ n∈Ioc X ⌊Y⌋₊, inghamRieszCoeff X Y n*(n:ℂ)^(-z)‖
  let S₁ := S.filter P
  let S₂ := S.filter fun z => ¬P z
  have hre (z : ℂ) (hz : z ∈ S₁) : z.re ∈ Set.Icc σ (σ+1) := by
    obtain ⟨_,h₁,h₂,_⟩ := hS z (mem_filter.mp hz).1
    exact ⟨h₁, by linarith [hσ.1]⟩
  have him (z : ℂ) (hz : z ∈ S₁) : 0 ≤ z.im ∧ z.im < (2*X+1:ℕ) := by
    obtain ⟨_,_,_,h₁,h₂⟩ := hS z (mem_filter.mp hz).1
    exact ⟨hX0.le.trans h₁,by push_cast; linarith⟩
  have hI := ingham_typeI_count_log_five (by omega) hYF (norm_inghamRieszCoeff hY0 X) (S:=S₁) (V:=1/8)
    ⟨by linarith [hσ.1],hσ.2⟩ (by positivity : 0≤K*L) (by norm_num) hre him
    (hunit (by omega) hσ S₁ (fun z hz => hS z (mem_filter.mp hz).1)) (fun z hz => (mem_filter.mp hz).2)
  have hlogY : 1+Real.log (⌊Y⌋₊:ℝ) ≤ 2*L := by
    have hh := (Real.log_le_log (by exact_mod_cast (by omega : 0<⌊Y⌋₊)) (Nat.floor_le hY0.le)).trans
      (Real.log_le_log hY0 hY)
    rw [Real.log_rpow hX0] at hh
    dsimp only [L]; linarith [Real.log_nonneg (by linarith : 1 ≤ (X:ℝ))]
  have hpY : (⌊Y⌋₊:ℝ)^(2*(1-σ)) ≤ Z :=
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hY0.le) (by linarith [hσ.2])).trans_eq
      (inghamCutoff_balance hX0 hσ.2).1
  have hI' : (S₁.card:ℝ) ≤ C₁*L^6*Z := by
    have hp : 0 ≤ 1+Real.log (⌊Y⌋₊:ℝ) := by linarith [Real.log_nonneg (by exact_mod_cast hYF : (1:ℝ)≤⌊Y⌋₊)]
    have hu : (S₁.card:ℝ)*(1/8:ℝ)^2 ≤ (2304*π^3*(K*L))*(2*L)^5*Z := by
      apply hI.trans; gcongr
    dsimp only [C₁]; linarith only [hu]
  let J (z : ℂ) := ∫ v in -(4*(X:ℝ))..4*X, (1/(1+|v|)^4)*
    (‖riemannZeta ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖*
      ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖)
  have hJ (z : ℂ) : 0 ≤ J z := intervalIntegral.integral_nonneg (by linarith : -(4*(X:ℝ))≤4*X)
    (fun v _ => by positivity)
  have hc (z : ℂ) (hz : z ∈ S₂) : 1/(8*(A*L*Y^(1/2-σ))) ≤ J z := by
    obtain ⟨hzS,hnot⟩ := mem_filter.mp hz
    obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := hS z hzS
    have he := (hd Y z hXY hY (by linarith) h₂ h₃ h₄ h₀).resolve_left hnot
    have hb := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith : 1/2-z.re ≤ 1/2-σ)
    apply (div_le_iff₀ (by positivity)).mpr
    change 1/8 ≤ A*L*Y^(1/2-z.re)*J z at he
    have he' := he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity : 0≤A*L)) (hJ z))
    linarith only [he']
  have ht := hII (by omega : 1 ≤ X) (by positivity : 0 ≤ K*L)
    (by positivity : 0 ≤ 1/(8*(A*L*Y^(1/2-σ))))
    (fun z (hz : z ∈ S₂) => ⟨hX0.le.trans (hS z (mem_filter.mp hz).1).2.2.2.1,(hS z (mem_filter.mp hz).1).2.2.2.2⟩)
    (hunit (by omega) hσ S₂ (fun z hz => hS z (mem_filter.mp hz).1)) hc
  have hII' : (S₂.card:ℝ) ≤ C₂*L^5*Z := ingham_balanced_cubic (by linarith) hσ.2
    (Nat.cast_nonneg _) hA hD hK.le ht
  have hcard : (S.card:ℝ) = S₁.card+(S₂.card:ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s:=S) P).symm
  have hII'' := hII'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 5≤6)) hc₂.le) hZ)
  change (S.card:ℝ) ≤ (C₁+C₂)*L^6*Z
  linarith only [hcard,hI',hII'']

/-- Uniform density estimate on a dyadic band, also for a subset of the zeros. -/
theorem ingham_zeroDensity_band_log_six :
    ∃ C > (0:ℝ), ∀ {X : ℕ}, 1 ≤ X → ∀ {σ : ℝ}, σ ∈ Set.Icc (1/2:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z ∈ S, riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.re < 1 ∧ (X:ℝ) ≤ z.im ∧ z.im ≤ 2*X) →
      (S.card:ℝ) ≤ C*(1+Real.log X)^6*(X:ℝ)^(inghamExponent σ) := by
  obtain ⟨E,hE,hlarge⟩ := ingham_large_band
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlarge.and (eventually_ge_atTop 2))
  obtain ⟨D,hD,hcrude⟩ := zeroDensityN_le_mul_log
  let F := (zeroDensityN 0 (2*(N:ℝ)) : ℝ)
  let B := 8*D*Real.exp 2
  let C := max F (max E B)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hB : 0 < B := by dsimp [B]; positivity
  have hEC : E ≤ C := (le_max_left ..).trans (le_max_right ..)
  have hBC : B ≤ C := (le_max_right ..).trans (le_max_right ..)
  refine ⟨C,hE.trans_le hEC,?_⟩
  intro X hX σ hσ S hS
  let L := 1+Real.log X
  let Z := (X:ℝ)^(inghamExponent σ)
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : 0 < (X:ℝ) := by linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hXr]
  have hZ : 1 ≤ Z := Real.one_le_rpow hXr (div_nonneg (by linarith [hσ.2]) (by linarith [hσ.2]))
  have hbase {T : ℝ} (hT : 2*X ≤ T) : (S.card:ℝ) ≤ zeroDensityN 0 T := by
    rw [zeroDensityN_eq_card]
    refine Nat.cast_le.mpr (card_le_card (fun z hz => ?_))
    obtain ⟨hz₀,hz₁,hz₂,hz₃,hz₄⟩ := hS z hz
    exact mem_zeroDensityFinset.mpr ⟨hz₀,by linarith [hσ.1],hz₂,by linarith,hz₄.trans hT⟩
  by_cases hx : N ≤ X
  · obtain ⟨hdet,hx₂⟩ := hN X hx
    have hX₂ : (2:ℝ) ≤ X := by exact_mod_cast hx₂
    by_cases hg : 1/Real.log X ≤ σ-1/2
    · apply (hdet hσ hg S hS).trans
      change E*L^6*Z ≤ C*L^6*Z
      gcongr
    · have ha := hbase (T:=2*X) le_rfl
      have hb := hcrude 0 (2*X) (by linarith)
      have hc := ingham_near_half (by linarith : 1 < (X:ℝ)) hσ (by simpa [one_div] using (le_of_not_ge hg))
      change (X:ℝ) ≤ Real.exp 2*Z at hc
      have hlog : Real.log (2*(X:ℝ)+2) ≤ 4*L := by
        have h := Real.log_le_log (by linarith : 0<2*(X:ℝ)+2) (by linarith : 2*(X:ℝ)+2 ≤ 4*X)
        rw [Real.log_mul (by norm_num) hX0.ne'] at h
        dsimp only [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(4:ℝ)), Real.log_nonneg hXr]
      have hh := (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤D*(2*(X:ℝ))))
      have hhh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity : 0≤8*D)) (by linarith : 0≤L)
      have h₁ : (S.card:ℝ) ≤ B*L*Z := by dsimp only [B]; linarith only [ha,hb,hh,hhh]
      exact h₁.trans (mul_le_mul_of_nonneg_right (mul_le_mul hBC
        (by simpa using pow_le_pow_right₀ hL (by decide : 1≤6) : L ≤ L^6) (by linarith) (hB.le.trans hBC)) (by linarith))
  · have hf := hbase (T:=2*(N:ℝ)) (by exact_mod_cast (show 2*X ≤ 2*N by omega))
    change (S.card:ℝ) ≤ F at hf
    apply hf.trans
    change F ≤ C*L^6*Z
    have hc : F ≤ C := le_max_left ..
    exact hc.trans ((le_mul_of_one_le_right (hF.trans hc) (one_le_pow₀ hL)).trans
        (le_mul_of_one_le_right (by positivity) hZ))

/-- The global Ingham bound for distinct zeros, with seven logarithms. -/
theorem ingham_zeroDensity_log_seven :
    ∃C > (0:ℝ), ∀σ∈Set.Icc (1/2:ℝ) 1,∀T : ℝ,2≤T →
      (zeroDensityN σ T:ℝ)≤C*T^(inghamExponent σ)*(Real.log T)^7 := by
  obtain ⟨C,hC,H⟩ := ingham_zeroDensity_band_log_six
  exact zeroDensity_of_dyadic_power_bound inghamExponent 6
    (fun σ hσ => div_nonneg (by linarith [hσ.2]) (by linarith [hσ.2])) hC H

/-- Ingham's density estimate with orders of vanishing and eight logarithms. -/
theorem ingham_zeroDensity_with_multiplicity_log_eight :
    ∃C > (0:ℝ), ∀σ∈Set.Icc (1/2:ℝ) 1,∀T : ℝ,2≤T →
      (∑ρ∈zeroDensityFinset σ T,(zeroMultiplicity ρ:ℝ))≤C*T^(inghamExponent σ)*(Real.log T)^8 :=
  zeroDensity_with_multiplicity_of_power_bound inghamExponent 7 ingham_zeroDensity_log_seven

/-- The traditional, weaker logarithmic form of the band estimate. -/
theorem ingham_zeroDensity_band :
    ∃ C > (0:ℝ), ∀ {X : ℕ}, 1 ≤ X → ∀ {σ : ℝ}, σ ∈ Set.Icc (1/2:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z ∈ S, riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.re < 1 ∧ (X:ℝ) ≤ z.im ∧ z.im ≤ 2*X) →
      (S.card:ℝ) ≤ C*(1+Real.log X)^10*(X:ℝ)^(inghamExponent σ) := by
  obtain ⟨C,hC,H⟩ := ingham_zeroDensity_band_log_six
  refine ⟨C,hC,?_⟩
  intro X hX σ hσ S hS
  have hlog := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
  exact (H hX hσ S hS).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith : 1≤1+Real.log X) (by decide : 6≤10)) hC.le)
      (by positivity))

/-- **Ingham's zero-density theorem** with the density exponent
`3(1−σ)/(2−σ)` and eleven powers of the logarithm for distinct zeros. -/
theorem ingham_zeroDensity : InghamDensityEstimate := by
  obtain ⟨C,hC,h⟩ := ingham_zeroDensity_band
  exact ingham_density_of_dyadic_bound hC h

/-- The classical count with multiplicities has the same density exponent. -/
theorem ingham_zeroDensity_with_multiplicity :
    ∃ C > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ zeroDensityFinset σ T, (zeroMultiplicity ρ:ℝ)) ≤
        C*T^(inghamExponent σ)*(Real.log T)^12 :=
  ingham_density_with_multiplicity_of_card ingham_zeroDensity

/-- The linear density hypothesis with coefficient 3 follows unconditionally. -/
theorem ingham_linear_zeroDensity : ZeroDensityHypothesis 3 11 :=
  zeroDensityHypothesis_of_ingham_bound ingham_zeroDensity

/-- With the super-logarithmic zero-free hypothesis, Ingham's density bound
gives the von Mangoldt asymptotic at every fixed exponent above two thirds. -/
theorem psi_shortInterval_two_thirds_of_superLogZeroFree (hZF : SuperLogZeroFreeHypothesis)
    {θ : ℝ} (hθ : 2/3 < θ) (hθ' : θ < 1) :
    Asymptotics.IsEquivalent atTop (fun x : ℝ => Chebyshev.psi (x+x^θ)-Chebyshev.psi x)
      (fun x => x^θ) :=
  ingham_psi_shortInterval_of_superLogZeroFree ingham_zeroDensity hZF hθ hθ'

/-- Under the same zero-free hypothesis, ordinary prime counts have main term
`x^θ / log x` for every fixed `2/3 < θ < 1`. -/
theorem primePi_shortInterval_two_thirds_of_superLogZeroFree (hZF : SuperLogZeroFreeHypothesis)
    {θ : ℝ} (hθ : 2/3 < θ) (hθ' : θ < 1) :
    Asymptotics.IsEquivalent atTop (fun x : ℝ => primePi (x+x^θ)-primePi x)
      (fun x => x^θ/Real.log x) :=
  ingham_primePi_shortInterval_of_superLogZeroFree ingham_zeroDensity hZF hθ hθ'

end AnalyticNumberTheory.PrimeDistribution
