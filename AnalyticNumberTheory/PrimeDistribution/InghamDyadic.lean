import AnalyticNumberTheory.PrimeDistribution.InghamBalance
import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik

/-!
# Summing Ingham's dyadic density estimates

The dyadic estimate is uniform for arbitrary subsets of one height band.
Summing the bands costs a logarithm. Local multiplicity control passes from
distinct zeros to the count with orders of vanishing.
-/
noncomputable section
open Finset Filter Complex
open scoped Classical Topology
namespace AnalyticNumberTheory.PrimeDistribution

private lemma logBlock_shape {n : ℕ} (hn : n ≠ 0) :
    2^(Nat.log 2 n) ≤ n ∧ n < 2*2^(Nat.log 2 n) :=
  ⟨Nat.pow_log_le_self 2 hn, by simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self one_lt_two n⟩

/-- Sum positive-height bands for any nonnegative density exponent. The number of bands costs one logarithm. -/
theorem zeroDensity_of_dyadic_power_bound (e : ℝ → ℝ) (k : ℕ)
    (he : ∀ σ ∈ Set.Icc (1/2:ℝ) 1, 0≤e σ) {C : ℝ} (hC : 0 < C)
    (hband : ∀ {X : ℕ}, 1 ≤ X → ∀ {σ : ℝ}, σ ∈ Set.Icc (1/2:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z ∈ S, riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.re < 1 ∧ (X:ℝ) ≤ z.im ∧ z.im ≤ 2*X) →
      (S.card:ℝ) ≤ C*(1+Real.log X)^k*(X:ℝ)^(e σ)) :
    ∃ D > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (zeroDensityN σ T:ℝ) ≤ D*T^(e σ)*(Real.log T)^(k+1) := by
  let F := (zeroDensityN 0 1 : ℝ)
  let K := F+3*C
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hK : 0 < K := by dsimp only [K]; linarith
  refine ⟨K*3^(k+1), by positivity, ?_⟩
  intro σ hσ T hT
  let p := e σ
  let L := 1+Real.log T
  have hT0 : 0<T := by linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by linarith : 1≤T)]
  have hp : 0 ≤ p := he σ hσ
  have hpow : 1 ≤ T^p := Real.one_le_rpow (by linarith) hp
  have hz : (zeroDensityN σ T:ℝ) ≤ K*L^(k+1)*T^p := by
    let W := zeroDensityFinset σ T
    let S := W.filter (fun z => 1 ≤ z.im)
    let V := W.filter (fun z => ¬1 ≤ z.im)
    have hv : V ⊆ zeroDensityFinset 0 1 := by
      intro z h
      obtain ⟨hzW,him⟩ := mem_filter.mp h
      obtain ⟨h₁,h₂,h₃,h₄,_⟩ := mem_zeroDensityFinset.mp hzW
      exact mem_zeroDensityFinset.mpr ⟨h₁,by linarith [hσ.1],h₃,h₄,by linarith⟩
    have hlow : (V.card:ℝ) ≤ F := by dsimp [F]; rw [zeroDensityN_eq_card]; exact_mod_cast card_le_card hv
    let I := range (Nat.log 2 ⌊T⌋₊+1)
    let idx (z : ℂ) := Nat.log 2 ⌊z.im⌋₊
    have hmap (z : ℂ) (hz : z ∈ S) : idx z ∈ I := mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_mono (mem_zeroDensityFinset.mp (mem_filter.mp hz).1).2.2.2.2)))
    have hTnat : 1 ≤ ⌊T⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
    have hfT := Nat.floor_le hT0.le
    have hbnd (i : ℕ) (hi : i ∈ I) : ((S.filter (fun z => idx z=i)).card:ℝ) ≤ C*L^k*T^p := by
      let X := 2^i
      have hX : 1 ≤ X := Nat.one_le_pow _ _ (by decide)
      have hXT : (X:ℝ) ≤ T := by
        apply le_trans _ hfT
        exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt_succ (mem_range.mp hi))).trans
          (Nat.pow_log_le_self 2 (by omega : ⌊T⌋₊≠0))
      have h := hband hX hσ (S.filter (fun z => idx z=i)) (by
        intro z hz
        obtain ⟨hzS,hi'⟩ := mem_filter.mp hz
        obtain ⟨hzW,hlo⟩ := mem_filter.mp hzS
        obtain ⟨h₁,h₂,h₃,h₄,_⟩ := mem_zeroDensityFinset.mp hzW
        have hn := (Nat.one_le_floor_iff _).mpr hlo
        have hshape := logBlock_shape (by omega : ⌊z.im⌋₊≠0)
        change Nat.log 2 ⌊z.im⌋₊ = i at hi'
        rw [hi'] at hshape
        refine ⟨h₁,h₂,h₃,(Nat.cast_le.mpr hshape.1).trans (Nat.floor_le h₄.le),?_⟩
        have htop : (⌊z.im⌋₊:ℝ)+1 ≤ 2*X := by exact_mod_cast (show ⌊z.im⌋₊+1 ≤ 2*X by omega)
        exact (Nat.lt_floor_add_one _).le.trans htop)
      apply h.trans
      change C*(1+Real.log X)^k*(X:ℝ)^p ≤ C*(1+Real.log T)^k*T^p
      have hlogX := Real.log_nonneg (by exact_mod_cast hX : 1≤(X:ℝ))
      gcongr
    have hcard : (S.card:ℝ) = ∑ i ∈ I, ((S.filter (fun z => idx z=i)).card:ℝ) := by
      simpa only [sum_const, nsmul_eq_mul,mul_one] using (sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))).symm
    have hI : (I.card:ℝ) ≤ 3*L := by
      have hp : (2:ℝ)^(Nat.log 2 ⌊T⌋₊) ≤ T := (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : ⌊T⌋₊≠0) :
        (2:ℝ)^(Nat.log 2 ⌊T⌋₊) ≤ (⌊T⌋₊:ℝ)).trans hfT
      have h := Real.log_le_log (by positivity) hp
      rw [Real.log_pow] at h
      have h₂ : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      dsimp [I,L]; simp only [card_range,Nat.cast_add,Nat.cast_one]
      nlinarith only [h, mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 ⌊T⌋₊)),
        Real.log_nonneg (by linarith : 1≤T)]
    have hupp : (S.card:ℝ) ≤ 3*C*L^(k+1)*T^p := by
      rw [hcard]
      apply (sum_le_sum hbnd).trans
      simp only [sum_const,nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right hI (by positivity)).trans_eq (by rw [pow_succ]; ring)
    have htotal : (W.card:ℝ) = (S.card:ℝ)+V.card := by
      exact_mod_cast (card_filter_add_card_filter_not (s:=W) (fun z => 1≤z.im)).symm
    rw [zeroDensityN_eq_card]
    change (W.card:ℝ) ≤ _
    rw [htotal]
    have hf : F ≤ F*L^(k+1)*T^p := (le_mul_of_one_le_right hF (one_le_pow₀ hL)).trans
      (le_mul_of_one_le_right (by positivity) hpow)
    dsimp only [K]
    linarith only [hupp,hlow.trans hf]
  have hlog₂ : (1/2:ℝ) ≤ Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans
    (Real.log_le_log zero_lt_two hT)
  have hL' : L ≤ 3*Real.log T := by dsimp [L]; linarith
  apply hz.trans
  calc
    _ ≤ K*(3*Real.log T)^(k+1)*T^p := by gcongr
    _ = _ := by dsimp only [p]; rw [mul_pow]; ring

/-- The conventional count with multiplicities obeys the same power of `T`,
with one further logarithm from the local multiplicity bound. -/
theorem zeroDensity_with_multiplicity_of_power_bound (e : ℝ → ℝ) (k : ℕ)
    (hcount : ∃ D > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (zeroDensityN σ T:ℝ) ≤ D*T^(e σ)*(Real.log T)^k) :
    ∃ C > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ zeroDensityFinset σ T, (zeroMultiplicity ρ:ℝ)) ≤
        C*T^(e σ)*(Real.log T)^(k+1) := by
  obtain ⟨D,hD,hd⟩ := hcount
  obtain ⟨M,hM,hm⟩ := analyticOrderNatAt_xi_le_log
  refine ⟨3*D*M,by positivity,?_⟩
  intro σ hσ T hT
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hTT : T+6 ≤ T^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T),sq_nonneg (T-2)]
  have hlt := Real.log_le_log (by linarith : 0<T+6) hTT
  rw [Real.log_pow] at hlt
  norm_num only [Nat.cast_ofNat] at hlt
  have hone (ρ : ℂ) (hρ : ρ ∈ zeroDensityFinset σ T) : (zeroMultiplicity ρ:ℝ) ≤ M*(3*Real.log T) := by
    obtain ⟨hz,hre,hre',him,hT'⟩ := mem_zeroDensityFinset.mp hρ
    have hpos : 0<ρ.re := by linarith [hσ.1]
    rw [zeroMultiplicity_eq_xi hpos hre']
    apply (hm ρ (RiemannZeta.xi_eq_zero_iff.mpr ⟨hz,hpos,hre'⟩)).trans
    rw [abs_of_pos him]
    exact mul_le_mul_of_nonneg_left ((Real.log_le_log (by linarith) (by linarith : ρ.im+6≤T+6)).trans hlt) hM.le
  apply (sum_le_sum hone).trans
  simp only [sum_const, nsmul_eq_mul, ← zeroDensityN_eq_card]
  have h := hd σ hσ T hT
  exact (mul_le_mul_of_nonneg_right h (by positivity : 0≤M*(3*Real.log T))).trans_eq (by rw [pow_succ]; ring)

/-- Sum the dyadic bands with Ingham's exponent, uniformly up to the one-line. -/
theorem ingham_density_of_dyadic_bound {C : ℝ} (hC : 0 < C)
    (hband : ∀ {X : ℕ}, 1 ≤ X → ∀ {σ : ℝ}, σ ∈ Set.Icc (1/2:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z ∈ S, riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.re < 1 ∧ (X:ℝ) ≤ z.im ∧ z.im ≤ 2*X) →
      (S.card:ℝ) ≤ C*(1+Real.log X)^10*(X:ℝ)^(inghamExponent σ)) :
    ∃ D > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (zeroDensityN σ T:ℝ) ≤ D*T^(inghamExponent σ)*(Real.log T)^11 :=
  zeroDensity_of_dyadic_power_bound inghamExponent 10 (fun σ hσ =>
    div_nonneg (by linarith [hσ.2]) (by linarith [hσ.2])) hC hband

/-- The conventional count with multiplicities obeys the same power of `T`,
with one further logarithm from the local multiplicity bound. -/
theorem ingham_density_with_multiplicity_of_card
    (hcount : ∃ D > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (zeroDensityN σ T:ℝ) ≤ D*T^(inghamExponent σ)*(Real.log T)^11) :
    ∃ C > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ zeroDensityFinset σ T, (zeroMultiplicity ρ:ℝ)) ≤
        C*T^(inghamExponent σ)*(Real.log T)^12 :=
  zeroDensity_with_multiplicity_of_power_bound inghamExponent 11 hcount

end AnalyticNumberTheory.PrimeDistribution
