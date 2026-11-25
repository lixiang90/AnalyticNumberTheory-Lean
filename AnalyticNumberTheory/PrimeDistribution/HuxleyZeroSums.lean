import AnalyticNumberTheory.PrimeDistribution.HuxleyDensity
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalZeroSums

/-!
# A density estimate for the zero sum at the seven-twelfths threshold

The available exponential saving is the product of the common distance of
the zeros from the one-line and the margin in `log x − (12/5) log T`.
The logarithmic factors are uniform when that margin is small compared
with `log x`.
-/
noncomputable section
open Finset Complex Real Filter
open scoped Classical
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- Huxley's density estimate as a two-sided bound on the total multiplicity
in a box, extended to the left edge of the critical strip. -/
theorem huxley_symmetric_zero_density :
    ∃ C>(0:ℝ), ∀ {T σ : ℝ}, 2≤T → σ≤1 →
      (∑ z∈(nontrivialZerosUpTo T).filter (fun z => σ≤z.re),(zeroMultiplicity z:ℝ)) ≤
        C*(1+Real.log T)^23*T^((12/5)*(1-σ)) := by
  obtain ⟨D,hD,hd⟩ := huxley_zeroDensity_distinct
  obtain ⟨M,hM,hm⟩ := analyticOrderNatAt_xi_le_log
  obtain ⟨B,hB,hb⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  let C := max (6*M*D) B
  refine ⟨C,hB.trans_le (le_max_right ..),?_⟩
  intro T σ hT hσ
  let W := (nontrivialZerosUpTo T).filter (fun z => σ≤z.re)
  let L := 1+Real.log T
  let Z := T^((12/5)*(1-σ))
  have hT0 : 0<T := by linarith
  have hl := Real.log_nonneg (by linarith : 1≤T)
  have hL : 1≤L := by dsimp [L]; linarith
  have hZ : 0≤Z := Real.rpow_nonneg hT0.le _
  by_cases hs : 1/2≤σ
  · let P := zeroDensityFinset σ T
    have hcard : (W.card:ℝ) ≤ 2*(zeroDensityN σ T:ℝ) := by
      have hsub : W ⊆ P ∪ P.image star := by
        intro z hz
        obtain ⟨hzw,hβ⟩ := mem_filter.mp hz
        have hsym : z∈zeroDensityFinsetSymmetric T := mem_zeroDensityFinsetSymmetric.mpr (mem_nontrivialZerosUpTo.mp hzw)
        rcases mem_union.mp hsym with hp | hn
        · obtain ⟨hh,_,h₁,h₂,h₃⟩ := mem_zeroDensityFinset.mp hp
          exact mem_union_left _ (mem_zeroDensityFinset.mpr ⟨hh,hβ,h₁,h₂,h₃⟩)
        · obtain ⟨w,hw,rfl⟩ := mem_image.mp hn
          obtain ⟨hh,_,h₁,h₂,h₃⟩ := mem_zeroDensityFinset.mp hw
          exact mem_union_right _ (mem_image.mpr ⟨w,mem_zeroDensityFinset.mpr ⟨hh,by simpa using hβ,h₁,h₂,h₃⟩,rfl⟩)
      have hh := (card_le_card hsub).trans (card_union_le ..)
      have hhi : (P.image star).card ≤ P.card := card_image_le
      rw [zeroDensityN_eq_card]
      exact_mod_cast (show W.card≤2*P.card by omega)
    have horders (z : ℂ) (hz : z∈W) : (zeroMultiplicity z:ℝ) ≤ M*(3*L) := by
      obtain ⟨hz₀,hz₁,hz₂,hz₃⟩ := mem_nontrivialZerosUpTo.mp (mem_filter.mp hz).1
      rw [zeroMultiplicity_eq_xi hz₁ hz₂]
      apply (hm z (xi_eq_zero_iff.mpr ⟨hz₀,hz₁,hz₂⟩)).trans
      apply mul_le_mul_of_nonneg_left _ hM.le
      have hl' := Real.log_le_log (by linarith [abs_nonneg z.im] : 0 < |z.im|+6) (by linarith : |z.im|+6≤4*T)
      rw [Real.log_mul (by norm_num) hT0.ne'] at hl'
      dsimp [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    have hu := hd σ ⟨hs,hσ⟩ T hT
    change (zeroDensityN σ T:ℝ) ≤ D*Z*(Real.log T)^22 at hu
    have hh := sum_le_sum horders
    simp only [sum_const,nsmul_eq_mul] at hh
    have hlog : Real.log T≤L := by dsimp [L]; linarith
    have hc := hcard.trans (mul_le_mul_of_nonneg_left (hu.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hl hlog 22) (mul_nonneg hD.le hZ))) (by norm_num : (0:ℝ)≤2))
    apply (hh.trans (mul_le_mul_of_nonneg_right hc (by positivity))).trans
    calc
      _ = (6*M*D)*L^23*Z := by ring
      _ ≤ _ := by change _ ≤ C*L^23*Z; gcongr; exact le_max_left ..
  · have hex : 1 ≤ (12/5)*(1-σ) := by linarith
    have hp : T≤Z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤T) hex
    have hlp : Real.log T ≤ L^23 := (by dsimp [L]; linarith : Real.log T ≤ L).trans
      (by simpa using pow_le_pow_right₀ hL (by decide : 1≤23))
    apply (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.cast_nonneg _)).trans
    apply (hb T hT).trans
    calc
      _ ≤ B*Z*L^23 := by gcongr
      _ = B*L^23*Z := by ring
      _ ≤ _ := by change _ ≤ C*L^23*Z; gcongr; exact le_max_right ..

/-- A common zero-free width preserves the entire margin in the density
estimate, with only the number of unit shells lost. -/
theorem huxley_zero_sum_margin :
    ∃ C>(0:ℝ), ∀ {x T δ F : ℝ}, 1<x → 2≤T → 0≤F →
      (12/5)*Real.log T+F ≤ Real.log x →
      (∀ z∈nontrivialZerosUpTo T, δ≤1-z.re) →
      (∑ z∈nontrivialZerosUpTo T,(zeroMultiplicity z:ℝ)*x^(z.re-1)) ≤
        C*(1+Real.log x)^24*Real.exp (-F*δ) := by
  obtain ⟨D,hD,hd⟩ := huxley_symmetric_zero_density
  refine ⟨D*Real.exp 1,by positivity,?_⟩
  intro x T δ F hx hT hF hmargin hgap
  let S := nontrivialZerosUpTo T
  let L := Real.log x
  let A := (12/5)*Real.log T
  let g (z : ℂ) := (1-z.re)*L
  let idx (z : ℂ) := ⌊g z⌋₊
  let J := ⌊L⌋₊+1
  have hLp : 0<L := Real.log_pos hx
  have hT0 : 0<T := by linarith
  have hLT : 0≤Real.log T := Real.log_nonneg (by linarith)
  have hA : 0≤A := by dsimp [A]; positivity
  have hl : Real.log T ≤ L := by dsimp [L]; linarith
  have hAL : A≤L := by dsimp only [A,L]; linarith
  have hw (z : ℂ) : 0≤(zeroMultiplicity z:ℝ) := Nat.cast_nonneg _
  have hgr (z : ℂ) (hz : z∈S) : 0≤g z ∧ g z≤L := by
    obtain ⟨_,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
    exact ⟨mul_nonneg (by linarith) hLp.le,by dsimp [g]; nlinarith only [mul_nonneg h₀.le hLp.le]⟩
  have hmap (z : ℂ) (hz : z∈S) : idx z∈range J := mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hgr z hz).2))
  have hsep (z : ℂ) (hz : z∈S) :
      x^(z.re-1) ≤ Real.exp (-A*(1-z.re))*Real.exp (-F*δ) := by
    rw [Real.rpow_def_of_pos (by linarith),←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [A]
    nlinarith only [mul_le_mul_of_nonneg_right hmargin (sub_nonneg.mpr (mem_nontrivialZerosUpTo.mp hz).2.2.1.le),
      mul_le_mul_of_nonneg_left (hgap z hz) hF]
  have hbase : ∑ z∈S, (zeroMultiplicity z:ℝ)*Real.exp (-A*(1-z.re)) ≤
      (J:ℝ)*((D*(1+Real.log T)^23)*Real.exp 1) := by
    rw [←sum_fiberwise_of_maps_to hmap]
    have hb (n : ℕ) (_ : n∈range J) :
        ∑ z∈S.filter (fun z => idx z=n),(zeroMultiplicity z:ℝ)*Real.exp (-A*(1-z.re)) ≤
          (D*(1+Real.log T)^23)*Real.exp 1 := by
      let σ := 1-((n:ℝ)+1)/L
      have hσ : σ≤1 := by dsimp [σ]; linarith [div_nonneg (by positivity : 0≤(n:ℝ)+1) hLp.le]
      have hz' (z : ℂ) (hz : z ∈ S.filter (fun z => idx z=n)) :
          (n:ℝ)/L ≤ 1-z.re ∧ σ≤z.re := by
        obtain ⟨hs,he⟩ := mem_filter.mp hz
        change ⌊g z⌋₊=n at he
        have hf := Nat.floor_le (hgr z hs).1
        have hf' := Nat.lt_floor_add_one (g z)
        rw [he] at hf hf'
        refine ⟨(div_le_iff₀ hLp).mpr hf,?_⟩
        have hh := (le_div_iff₀ hLp).mpr hf'.le
        dsimp [σ]; linarith
      have hsub : S.filter (fun z => idx z=n) ⊆ S.filter (fun z => σ≤z.re) :=
        fun z hz => mem_filter.mpr ⟨(mem_filter.mp hz).1,(hz' z hz).2⟩
      have hh := (sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hw z)).trans (hd hT hσ)
      calc
        _ ≤ ∑ z∈S.filter (fun z => idx z=n),(zeroMultiplicity z:ℝ)*Real.exp (-A*((n:ℝ)/L)) := by
          apply sum_le_sum; intro z hz
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hz' z hz).1 (neg_nonpos.mpr hA))) (hw z)
        _ ≤ (D*(1+Real.log T)^23*T^((12/5)*(1-σ)))*Real.exp (-A*((n:ℝ)/L)) := by
          rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
        _ ≤ _ := by
          rw [Real.rpow_def_of_pos hT0, mul_assoc, ←Real.exp_add]
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          calc Real.log T*((12/5)*(1-σ))+ -A*((n:ℝ)/L) = A/L := by dsimp [σ,A]; ring
               _ ≤ 1 := (div_le_one hLp).mpr hAL
    apply (sum_le_sum hb).trans_eq; simp
  have hh := sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hsep z hz) (hw z))
  simp_rw [←mul_assoc] at hh
  rw [←sum_mul] at hh
  have hJ : (J:ℝ)≤1+L := by dsimp [J]; push_cast; linarith [Nat.floor_le hLp.le]
  apply (hh.trans (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le)).trans
  have hp : (J:ℝ)*((D*(1+Real.log T)^23)*Real.exp 1) ≤ (1+L)*((D*(1+L)^23)*Real.exp 1) := by gcongr
  exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans_eq (by dsimp [L]; ring)

end AnalyticNumberTheory.PrimeDistribution
