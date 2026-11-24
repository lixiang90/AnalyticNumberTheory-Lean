import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import AnalyticNumberTheory.PrimeDistribution.DirichletPolynomialSampling
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik

/-!
# A power-saving zero-density theorem

A finite Möbius detector, the mean square of Dirichlet polynomials and the
local Jensen zero count yield `N(σ,T) ≪ T^(4(1−σ)) (log T)^11`.
The counting function here counts distinct zeros, as in `zeroDensityN`.
-/

noncomputable section

open Finset Filter Complex
open scoped Classical Topology
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.PrimeDistribution

private def blockCoeff (X i n : ℕ) : ℂ :=
  if X < n ∧ n ≤ X^2 ∧ Nat.log 2 n = i then zetaDetectorCoeff X n else 0

private def blocks (X : ℕ) : Finset ℕ :=
  (range (Nat.log 2 (X^2)+1)).filter fun i => X < 2*(2^i) ∧ 2^i ≤ X^2

private lemma logBlock_shape {n : ℕ} (hn : n ≠ 0) :
    2^(Nat.log 2 n) ≤ n ∧ n < 2*2^(Nat.log 2 n) :=
  ⟨Nat.pow_log_le_self 2 hn, by simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self one_lt_two n⟩

private lemma tail_by_blocks (X : ℕ) (s : ℂ) :
    ∑ n ∈ Ioc X (X^2), zetaDetectorCoeff X n*(n:ℂ)^(-s) =
      ∑ i ∈ blocks X, dirichletPoly (blockCoeff X i) (2*2^i) s := by
  have hmap (n : ℕ) (hn : n ∈ Ioc X (X^2)) : Nat.log 2 n ∈ blocks X := by
    obtain ⟨hX,hr⟩ := mem_Ioc.mp hn
    have h := logBlock_shape (by omega : n ≠ 0)
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hr)), hX.trans h.2, h.1.trans hr⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun i hi => ?_
  unfold dirichletPoly
  simp only [blockCoeff, ite_mul, zero_mul, ← sum_filter]
  congr 1
  ext n
  simp only [mem_filter,mem_Ioc,mem_Icc]
  constructor
  · rintro ⟨⟨h₁,h₂⟩, h₃⟩
    have h := logBlock_shape (by omega : n ≠ 0)
    rw [h₃] at h
    exact ⟨⟨by omega,h.2.le⟩,h₁,h₂,h₃⟩
  · tauto

private lemma block_energy {X i : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) :
    dirichletPolyEnergy (blockCoeff X i) (2*2^i) σ ≤
      (2*(2^i:ℕ) : ℝ) * (1+Real.log (2*(2^i:ℕ):ℝ))^3 * ((2^i:ℕ):ℝ)^(-2*σ) := by
  let M := 2^i
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  have hcoef (n : ℕ) (_ : n ∈ Icc 1 (2*M)) :
      ‖blockCoeff X i n‖^2*(n:ℝ)^(-2*σ) ≤ (n.divisors.card:ℝ)^2*(M:ℝ)^(-2*σ) := by
    unfold blockCoeff
    split_ifs with h
    · have hmn : M ≤ n := by dsimp [M]; rw [← h.2.2]; exact (logBlock_shape (by omega : n ≠ 0)).1
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_zetaDetectorCoeff_le ..) 2)
        (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM) (by exact_mod_cast hmn) (by linarith))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]; positivity
  apply (sum_le_sum hcoef).trans
  rw [← sum_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h := sum_Icc_card_divisors_sq_le (2*M)
  rw [max_eq_left (by omega)] at h
  exact_mod_cast h

private lemma block_count_le {X : ℕ} (hX : 1 ≤ X) :
    ((blocks X).card : ℝ) ≤ 5*(1+Real.log X) := by
  have hcard : (blocks X).card ≤ Nat.log 2 (X^2)+1 :=
    (card_le_card (filter_subset ..)).trans_eq (card_range _)
  have hpow : (2:ℝ)^(Nat.log 2 (X^2)) ≤ (X:ℝ)^2 := by
    exact_mod_cast Nat.pow_log_le_self 2 (by positivity : X^2≠0)
  have h := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hlog₂ : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
  have hcar : ((blocks X).card:ℝ) ≤ (Nat.log 2 (X^2)+1:ℕ) := Nat.cast_le.mpr hcard
  push_cast at hcar
  nlinarith only [hcar,h,hlog,mul_le_mul_of_nonneg_left hlog₂ (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (X^2)))]

private theorem sampled_block {X i : ℕ} (hX : 1 ≤ X) (hi : i ∈ blocks X)
    {S : Finset ℂ} {σ K : ℝ} (hσ : σ ∈ Set.Icc (3/4:ℝ) 1) (hK : 0 ≤ K)
    (hre : ∀ z ∈ S, z.re ∈ Set.Icc σ (σ+1)) (him : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < (2*X+1:ℕ))
    (hcount : ∀ j < 2*X+1, ((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ K*(1+Real.log X)) :
    ∑ z ∈ S, ‖dirichletPoly (blockCoeff X i) (2*2^i) z‖^2 ≤
      (18*(10+4*Real.pi)*3^7*K) * (1+Real.log X)^8 * (X:ℝ)^(4*(1-σ)) := by
  let M := 2^i
  let L := 1+Real.log X
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  obtain ⟨hXM,hMX⟩ := (mem_filter.mp hi).2
  change X < 2*M at hXM
  change M ≤ X^2 at hMX
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ)<M := by linarith
  have hX0 : (0:ℝ)<X := by linarith
  have hl : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hXr]
  have hlog : 1+Real.log (2*(M:ℝ)) ≤ 3*L := by
    rw [Real.log_mul (by norm_num) hM0.ne']
    have h := Real.log_le_log hM0 (by exact_mod_cast hMX : (M:ℝ) ≤ (X:ℝ)^2)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    dsimp only [L]; linarith [Real.log_nonneg hXr, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog0 : 0 ≤ 1+Real.log (2*(M:ℝ)) := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2*(M:ℝ)); linarith
  have hsave : (M:ℝ)^2*(M:ℝ)^(-2*σ) ≤ (X:ℝ)^(4*(1-σ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hM0]
    have h := Real.rpow_le_rpow hM0.le (by exact_mod_cast hMX : (M:ℝ) ≤ (X:ℝ)^2) (by linarith [hσ.2] : 0 ≤ 2+ -2*σ)
    apply h.trans_eq
    rw [← Real.rpow_two, ← Real.rpow_mul hX0.le]; congr 1; ring
  have hlen : 2*((2*X+1:ℕ):ℝ)+2*Real.pi*(2*M:ℕ) ≤ (10+4*Real.pi)*(M:ℝ) := by
    push_cast
    have hxm : (X:ℝ)<2*M := by exact_mod_cast hXM
    nlinarith
  have he := block_energy (X:=X) (i:=i) (by linarith [hσ.1] : 0 ≤ σ)
  change _ ≤ (2*(M:ℝ))*(1+Real.log (2*(M:ℝ)))^3*(M:ℝ)^(-2*σ) at he
  have hs := dirichletPoly_sampling_strip (K:=K*L) (by positivity) hre him hcount
    (blockCoeff X i) (N:=2*M) (by omega)
  apply hs.trans
  push_cast at hlen ⊢
  change 9*(K*L)*(_ * (1+Real.log (2*(M:ℝ)))^4 * _) ≤ _
  calc
    _ ≤ 9*(K*L)*(((10+4*Real.pi)*M)*(3*L)^4*((2*(M:ℝ))*(3*L)^3*(M:ℝ)^(-2*σ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul _ (he.trans (by gcongr)) (sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
      gcongr
    _ = (18*(10+4*Real.pi)*3^7*K)*L^8 * ((M:ℝ)^2*(M:ℝ)^(-2*σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

/-- Zero-density estimate on one dyadic band, uniformly for any subset of its zeros. -/
theorem zeta_zeroDensity_band :
    ∃ C > 0, ∀ {X : ℕ}, 1 ≤ X → ∀ {σ : ℝ}, σ ∈ Set.Icc (3/4:ℝ) 1 → ∀ S : Finset ℂ,
      (∀ z ∈ S, riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.re < 1 ∧ (X:ℝ) ≤ z.im ∧ z.im ≤ 2*X) →
      (S.card:ℝ) ≤ C*(1+Real.log X)^10*(X:ℝ)^(4*(1-σ)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp zetaDetector_large_at_zero
  obtain ⟨C₀,hC₀,hzeros⟩ := sum_zeroMultiplicity_strip_le
  let K := 5*C₀
  let D := 18*(10+4*Real.pi)*3^7*K
  let F := (zeroDensityN 0 (2*(N₀:ℝ)) : ℝ)
  have hD : 0 < D := by dsimp [D,K]; positivity
  refine ⟨max (100*D) F, (by positivity : 0<100*D).trans_le (le_max_left ..),?_⟩
  intro X hX σ hσ S hS
  let L := 1+Real.log X
  let V := (X:ℝ)^(4*(1-σ))
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : 0 < (X:ℝ) := by linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hXr]
  have hV : 1 ≤ V := Real.one_le_rpow hXr (by linarith [hσ.2])
  by_cases hlarge : N₀ ≤ X
  · have him (z : ℂ) (hz : z ∈ S) : 0 ≤ z.im ∧ z.im < (2*X+1:ℕ) := by
      obtain ⟨_,_,_,ht,ht'⟩ := hS z hz
      push_cast
      constructor <;> linarith
    have hre (z : ℂ) (hz : z ∈ S) : z.re ∈ Set.Icc σ (σ+1) := by
      obtain ⟨_, hr,hr',_⟩ := hS z hz
      exact ⟨hr, by linarith [hσ.1]⟩
    have hcount (j : ℕ) (hj : j < 2*X+1) :
        ((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ K*L := by
      let W := S.filter (fun z => ⌊z.im⌋₊=j)
      have hb := hzeros (j:ℝ) W (by
        intro z hz
        obtain ⟨hS',hj'⟩ := mem_filter.mp hz
        obtain ⟨hz₁,hz₂,hz₃,hz₄,hz₅⟩ := hS z hS'
        have hz0 := (him z hS').1
        have hf := Nat.floor_le hz0
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
      have harg : (j:ℝ)+2 ≤ 4*X := by
        exact_mod_cast (show j+2 ≤ 4*X by omega)
      have h := Real.log_le_log (by positivity) harg
      rw [Real.log_mul (by norm_num) hX0.ne'] at h
      have hlog : Real.log ((j:ℝ)+2) ≤ 5*L := by
        dsimp only [L]
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4), Real.log_nonneg hXr]
      exact (mul_le_mul_of_nonneg_left hlog hC₀.le).trans_eq (by dsimp [K]; ring)
    let J := blocks X
    let P (i : ℕ) (z : ℂ) := dirichletPoly (blockCoeff X i) (2*2^i) z
    have each (z : ℂ) (hz : z ∈ S) : (1:ℝ)/4 ≤ (J.card:ℝ) * ∑ i ∈ J, ‖P i z‖^2 := by
      obtain ⟨hz₁, hz₂, _, ht, ht'⟩ := hS z hz
      have hz0 := (him z hz).1
      have hd := hN₀ X hlarge (hσ.1.trans hz₂) (by rwa [abs_of_nonneg hz0]) (by rwa [abs_of_nonneg hz0]) hz₁
      rw [tail_by_blocks] at hd
      have hn : 1/2 ≤ ∑ i ∈ J, ‖P i z‖ := hd.trans (norm_sum_le ..)
      have hcs := sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun i => ‖P i z‖)
      simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
      exact (by nlinarith [pow_le_pow_left₀ (by norm_num : 0≤(1/2:ℝ)) hn 2] : 1/4 ≤ (∑ i ∈ J, ‖P i z‖)^2).trans hcs
    have heach := sum_le_sum each
    simp only [sum_const,nsmul_eq_mul, ←mul_sum] at heach
    rw [sum_comm] at heach
    have hd (i : ℕ) (hi : i∈J) : ∑ z ∈ S, ‖P i z‖^2 ≤ D*L^8*V :=
      sampled_block hX hi hσ (by dsimp [K]; positivity) hre him hcount
    have ha := mul_le_mul_of_nonneg_left (sum_le_sum hd) (Nat.cast_nonneg (α:=ℝ) J.card)
    simp only [sum_const,nsmul_eq_mul] at ha
    have hJ : (J.card:ℝ) ≤ 5*L := block_count_le hX
    have hr : (S.card:ℝ) ≤ 100*D*L^10*V := by
      have hb := heach.trans ha
      have hbound : (J.card:ℝ)*((J.card:ℝ)*(D*L^8*V)) ≤ (5*L)*((5*L)*(D*L^8*V)) := by gcongr
      nlinarith only [hb.trans hbound]
    exact hr.trans (by change 100*D*L^10*V ≤ max (100*D) F*L^10*V; gcongr; exact le_max_left ..)
  · have hsub : S ⊆ zeroDensityFinset 0 (2*(N₀:ℝ)) := by
      intro z hz
      obtain ⟨hz₁,hz₂,hz₃,ht,ht'⟩ := hS z hz
      have hX' : (X:ℝ) ≤ N₀ := by exact_mod_cast (show X ≤ N₀ by omega)
      exact mem_zeroDensityFinset.mpr ⟨hz₁,by linarith [hσ.1],hz₃,by linarith,by linarith⟩
    have hf : (S.card:ℝ) ≤ F := by
      dsimp only [F]; rw [zeroDensityN_eq_card]; exact_mod_cast card_le_card hsub
    change (S.card:ℝ) ≤ max (100*D) F * L^10*V
    exact hf.trans ((le_max_right ..).trans ((le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)).trans
      (le_mul_of_one_le_right (by positivity) hV)))

/-- An unconditional zero-density theorem: uniformly for `1/2 ≤ σ ≤ 1` and `T ≥ 2`,
the number of distinct nontrivial zeros with `Re(ρ) ≥ σ` and `0 < Im(ρ) ≤ T` is
`O(T^(4(1−σ)) (log T)^11)`. -/
theorem zeta_zeroDensity : ZeroDensityHypothesis 4 11 := by
  obtain ⟨C,hC,hband⟩ := zeta_zeroDensity_band
  obtain ⟨D,hD,hcrude⟩ := zeroDensityN_le_mul_log
  let F := (zeroDensityN 0 1 : ℝ)
  let K := F+3*C+2*D
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hK : 0 < K := by dsimp only [K]; linarith
  refine ⟨K*3^11, by positivity, ?_⟩
  intro σ hσ T hT
  let p := 4*(1-σ)
  let L := 1+Real.log T
  have hT0 : 0<T := by linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by linarith : 1≤T)]
  have hp : 0 ≤ p := by dsimp [p]; linarith [hσ.2]
  have hpow : 1 ≤ T^p := Real.one_le_rpow (by linarith) hp
  have hz : (zeroDensityN σ T:ℝ) ≤ K*L^11*T^p := by
    by_cases hσ' : 3/4 ≤ σ
    · let W := zeroDensityFinset σ T
      let S := W.filter (fun z => 1 ≤ z.im)
      let V := W.filter (fun z => ¬1 ≤ z.im)
      have hv : V ⊆ zeroDensityFinset 0 1 := by
        intro z h
        obtain ⟨hzW,him⟩ := mem_filter.mp h
        obtain ⟨h₁,h₂,h₃,h₄,_⟩ := mem_zeroDensityFinset.mp hzW
        exact mem_zeroDensityFinset.mpr ⟨h₁,by linarith,h₃,h₄,by linarith⟩
      have hlow : (V.card:ℝ) ≤ F := by dsimp [F]; rw [zeroDensityN_eq_card]; exact_mod_cast card_le_card hv
      let I := range (Nat.log 2 ⌊T⌋₊+1)
      let idx (z : ℂ) := Nat.log 2 ⌊z.im⌋₊
      have hmap (z : ℂ) (hz : z ∈ S) : idx z ∈ I := mem_range.mpr
        (Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_mono (mem_zeroDensityFinset.mp (mem_filter.mp hz).1).2.2.2.2)))
      have hTnat : 1 ≤ ⌊T⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
      have hfT := Nat.floor_le hT0.le
      have hbnd (i : ℕ) (hi : i ∈ I) : ((S.filter (fun z => idx z=i)).card:ℝ) ≤ C*L^10*T^p := by
        let X := 2^i
        have hX : 1 ≤ X := Nat.one_le_pow _ _ (by decide)
        have hXT : (X:ℝ) ≤ T := by
          apply le_trans _ hfT
          exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt_succ (mem_range.mp hi))).trans
            (Nat.pow_log_le_self 2 (by omega : ⌊T⌋₊≠0))
        have h := hband hX ⟨hσ',hσ.2⟩ (S.filter (fun z => idx z=i)) (by
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
        change C*(1+Real.log X)^10*(X:ℝ)^p ≤ C*(1+Real.log T)^10*T^p
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
      have hupp : (S.card:ℝ) ≤ 3*C*L^11*T^p := by
        rw [hcard]
        apply (sum_le_sum hbnd).trans
        simp only [sum_const,nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right hI (by positivity)).trans_eq (by ring)
      have htotal : (W.card:ℝ) = (S.card:ℝ)+V.card := by
        exact_mod_cast (card_filter_add_card_filter_not (s:=W) (fun z => 1≤z.im)).symm
      rw [zeroDensityN_eq_card]
      change (W.card:ℝ) ≤ _
      rw [htotal]
      have hf : F ≤ F*L^11*T^p := (le_mul_of_one_le_right hF (one_le_pow₀ hL)).trans
        (le_mul_of_one_le_right (by positivity) hpow)
      dsimp only [K]
      nlinarith only [hupp,hlow.trans hf,mul_nonneg (mul_nonneg hD.le (pow_nonneg (by linarith : 0≤L) 11)) (by positivity : 0≤T^p)]
    · have hp' : 1 ≤ p := by dsimp only [p]; linarith
      have hTp : T ≤ T^p := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤T) hp'
      have hlog : Real.log (T+2) ≤ 2*L := by
        have ht := Real.log_le_log (by linarith : 0<T+2) (by linarith : T+2≤2*T)
        rw [Real.log_mul (by norm_num) hT0.ne'] at ht
        dsimp only [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ)),Real.log_nonneg (by linarith : 1≤T)]
      apply (hcrude σ T hT).trans
      calc
        _ ≤ D*T^p*(2*L) := by gcongr; exact Real.log_nonneg (by linarith)
        _ = 2*D*L*T^p := by ring
        _ ≤ K*L^11*T^p := by
          have hl11 : L ≤ L^11 := by simpa using pow_le_pow_right₀ hL (by decide : 1≤11)
          have hkD : 2*D ≤ K := by dsimp only [K]; linarith
          gcongr
  have hlog₂ : (1/2:ℝ) ≤ Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans
    (Real.log_le_log zero_lt_two hT)
  have hL' : L ≤ 3*Real.log T := by dsimp [L]; linarith
  apply hz.trans
  calc
    _ ≤ K*(3*Real.log T)^11*T^p := by gcongr
    _ = _ := by rw [show (Real.log T)^(11:ℝ) = (Real.log T)^11 by norm_cast]; dsimp only [p]; ring

/-- The conventional count with multiplicities obeys the same power of `T`,
with one further logarithm from the local multiplicity bound. -/
theorem zeta_zeroDensity_with_multiplicity :
    ∃ C > 0, ∀ σ ∈ Set.Icc (1/2:ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ zeroDensityFinset σ T, (zeroMultiplicity ρ:ℝ)) ≤
        C*T^(4*(1-σ))*(Real.log T)^12 := by
  obtain ⟨D,hD,hd⟩ := zeta_zeroDensity
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
  rw [show (Real.log T)^(11:ℝ) = (Real.log T)^11 by norm_cast] at h
  exact (mul_le_mul_of_nonneg_right h (by positivity : 0≤M*(3*Real.log T))).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
