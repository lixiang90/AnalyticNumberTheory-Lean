import AnalyticNumberTheory.SieveMethods.HuxleyLocalMean

/-!
# Huxley's large-values inequality

Local mean estimates are applied on shorter ordinate intervals chosen from the
large-value level and coefficient energy. This gives a quadratic term and a
sixth-power term in the level, uniformly in the real parts of the sample points.
-/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.SieveMethods

variable {ι : Type*}

/-- Cover a finite set of ordinates in a height interval by shorter intervals. -/
theorem ordinate_cover_count (S : Finset ι) (t : ι → ℝ) {a T H B : ℝ}
    (hT : 0 ≤ T) (hH : 0 < H) (hB : 0 ≤ B) (ht : ∀ i∈S, a≤t i ∧ t i≤a+T)
    (hlocal : ∀ U ⊆ S, (∀ i∈U, ∀ j∈U, |t j-t i| ≤ H) → (U.card:ℝ) ≤ B) :
    (S.card:ℝ) ≤ (1+T/H)*B := by
  let N := ⌊T/H⌋₊+1
  let idx (i : ι) := ⌊(t i-a)/H⌋₊
  have hmap (i : ι) (hi : i∈S) : idx i∈range N :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith [(ht i hi).2]) hH.le)))
  have hb (k : ℕ) (_ : k∈range N) : ((S.filter (fun i => idx i=k)).card:ℝ) ≤ B := by
    apply hlocal _ (filter_subset ..)
    have hf (i : ι) (hi : i ∈ S.filter (fun i => idx i=k)) : (k:ℝ)*H ≤ t i-a ∧ t i-a < ((k:ℝ)+1)*H := by
      obtain ⟨his,hik⟩ := mem_filter.mp hi
      have h₁ := Nat.floor_le (div_nonneg (sub_nonneg.mpr (ht i his).1) hH.le)
      have h₂ := Nat.lt_floor_add_one ((t i-a)/H)
      change ⌊(t i-a)/H⌋₊=k at hik
      rw [hik] at h₁ h₂
      exact ⟨(le_div_iff₀ hH).mp h₁,(div_lt_iff₀ hH).mp h₂⟩
    intro i hi j hj
    exact abs_le.mpr ⟨by linarith [(hf i hi).2,(hf j hj).1],by linarith [(hf i hi).1,(hf j hj).2]⟩
  have hsum := sum_le_sum hb
  have hcard : (S.card:ℝ) = ∑ k∈range N, ((S.filter (fun i => idx i=k)).card:ℝ) := by
    simpa only [sum_const,nsmul_eq_mul,mul_one] using (sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))).symm
  rw [hcard]
  apply hsum.trans
  simp only [sum_const,nsmul_eq_mul,card_range]
  apply mul_le_mul_of_nonneg_right _ hB
  dsimp only [N]; push_cast
  linarith [Nat.floor_le (div_nonneg hT hH.le)]

/-- Huxley's large-values bound with a coefficient energy majorant `G`.
The form multiplied through by `V^6` includes zero values of both parameters.
The logarithms are explicit for arbitrary polynomial length and ordinate range. -/
theorem huxley_dirichletPoly_large_values (S : Finset ι) (a : ℕ → ℂ) {N : ℕ} (hN : 1≤N)
    (z : ι → ℂ) {σ V G K T t₀ : ℝ} (hV : 0 ≤ V) (hK : 0 ≤ K) (hT : 1 ≤ T)
    (hre : ∀ i∈S, σ ≤ (z i).re) (ht : ∀ i∈S, t₀≤(z i).im ∧ (z i).im≤t₀+T)
    (hcell : ∀ u : ℝ, ((S.filter (fun i => u ≤ (z i).im ∧ (z i).im ≤ u+1)).card:ℝ) ≤ K)
    (hG : ∑ n∈Icc 1 N, ‖a n‖^2*(n:ℝ)^(-2*σ) ≤ G)
    (hlarge : ∀ i∈S, V ≤ ‖dirichletPoly a N (z i)‖) :
    let B := G*((1+8000*π)*(1+Real.log N))
    (S.card:ℝ)*V^6 ≤ 128*K*N*(1+Real.log (T+1))*(B*V^4+T*B^3) := by
  let A := (1+8000*π)*(1+Real.log N)
  let B := G*A
  let L := 1+Real.log (T+1)
  let W := 2*K*N*L
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hA : 0≤A := by dsimp [A]; have := Real.log_nonneg hNr; positivity
  have hG0 : 0≤G := (sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hG
  have hB : 0≤B := mul_nonneg hG0 hA
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg (by linarith : 1≤T+1)]
  have hW : 0≤W := by dsimp [W]; positivity
  change (S.card:ℝ)*V^6 ≤ 128*K*N*L*(B*V^4+T*B^3)
  have hu (U : Finset ι) (hU : U⊆S) (H : ℝ) (hH : 0≤H)
      (hd : ∀ i∈U, ∀ j∈U, |(z j).im-(z i).im| ≤ H) :
      (U.card:ℝ)*V^2 ≤ B*(W+(U.card:ℝ)*Real.sqrt (1+H)) := by
    let H' := min T H
    have hp : 0≤H' := le_min (by linarith) hH
    have hw (i : ι) (hi : i∈U) (j : ι) (hj : j∈U) : |(z j).im-(z i).im|≤H' := by
      obtain ⟨hi₁,hi₂⟩ := ht i (hU hi)
      obtain ⟨hj₁,hj₂⟩ := ht j (hU hj)
      exact le_min (abs_le.mpr ⟨by linarith,by linarith⟩) (hd i hi j hj)
    have hcell' (u : ℝ) : ((U.filter (fun i => u≤(z i).im ∧ (z i).im≤u+1)).card:ℝ) ≤ K :=
      (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hU))).trans (hcell u)
    have h := huxley_local_large_values U a hN z hV hK hp (fun i hi => hre i (hU hi)) hcell' hw (fun i hi => hlarge i (hU hi))
    have hl := Real.log_le_log (by linarith : 0<H'+1) (add_le_add_left (min_le_left T H) 1)
    have hs := Real.sqrt_le_sqrt (add_le_add_right (min_le_right T H) 1)
    have hlog : 0≤1+Real.log (H'+1) := by linarith [Real.log_nonneg (by linarith : 1≤H'+1)]
    apply h.trans
    dsimp only [B,W,L,A]
    gcongr
  have hS : (S.card:ℝ) ≤ (1+T)*K := by
    simpa only [div_one] using ordinate_cover_count S (fun i => (z i).im) (by linarith : 0≤T) (by norm_num : 0<(1:ℝ)) hK ht
      (fun U hU hdist => by
        rcases U.eq_empty_or_nonempty with rfl | hne
        · simpa using hK
        · obtain ⟨i,hi,hmin⟩ := exists_min_image U (fun j => (z j).im) hne
          apply (Nat.cast_le.mpr (card_le_card (t:={j ∈ S | (z i).im≤(z j).im ∧ (z j).im≤(z i).im+1}) _)).trans (hcell _)
          intro j hj; exact mem_filter.mpr ⟨hU hj,hmin j hj,by linarith [(abs_le.mp (hdist i hi j hj)).2]⟩)
  by_cases hm : V^2 ≤ 4*B
  · have hv := pow_le_pow_left₀ (sq_nonneg _) hm 3
    have hh := mul_le_mul hS hv (by positivity) (by positivity)
    have hKN : K ≤ K*N := le_mul_of_one_le_right hK hNr
    have hKL : K ≤ K*N*L := hKN.trans (le_mul_of_one_le_right (by positivity) hL)
    have hTL : (1+T)*K ≤ 2*T*(K*N*L) := by
      apply (mul_le_mul_of_nonneg_right (by linarith : 1+T ≤ 2*T) hK).trans
      exact mul_le_mul_of_nonneg_left hKL (by linarith)
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hTL (pow_nonneg (by positivity : 0≤4*B) 3))
    have hex : 0≤(K*N*L)*(B*V^4) := by positivity
    nlinarith only [hh',hex]
  · have hm' : 4*B<V^2 := lt_of_not_ge hm
    by_cases hz : B=0
    · have hh := hu S (Subset.rfl) T (by linarith) (fun i hi j hj => abs_le.mpr
        ⟨by linarith [(ht i hi).2,(ht j hj).1],by linarith [(ht i hi).1,(ht j hj).2]⟩)
      rw [hz,zero_mul] at hh
      have hh' := mul_le_mul_of_nonneg_right hh (pow_nonneg hV 4)
      rw [hz]; nlinarith only [hh']
    have hB' : 0<B := lt_of_le_of_ne hB (Ne.symm hz)
    have hV' : 0<V^2 := by linarith
    let H := (V^2/(4*B))^2
    have hR : 1≤V^2/(4*B) := (one_le_div (by positivity)).mpr hm'.le
    have hH : 1≤H := by dsimp [H]; nlinarith [sq_nonneg (V^2/(4*B)-1)]
    have hhs : B*Real.sqrt (1+H) ≤ V^2/2 := by
      have hs := Real.sqrt_le_sqrt (by linarith : 1+H≤4*H)
      have h₁ : Real.sqrt (4*H) = 2*(V^2/(4*B)) := by
        rw [show 4*H=(2*(V^2/(4*B)))^2 by dsimp [H]; ring,Real.sqrt_sq (by positivity)]
      rw [h₁] at hs
      apply (mul_le_mul_of_nonneg_left hs hB).trans_eq
      field_simp; ring
    have hcnt (U : Finset ι) (hU : U⊆S) (hd : ∀ i∈U, ∀ j∈U, |(z j).im-(z i).im|≤H) :
        (U.card:ℝ) ≤ 2*B*W/V^2 := by
      have hh := hu U hU H (by linarith) hd
      have hh' := mul_le_mul_of_nonneg_left hhs (Nat.cast_nonneg (α:=ℝ) U.card)
      apply (le_div_iff₀ hV').mpr
      linarith only [hh,hh']
    have Hpos : 0 < H := by linarith
    have hh := ordinate_cover_count S (fun i => (z i).im) (by linarith : 0≤T) Hpos
      (by positivity : 0≤2*B*W/V^2) ht hcnt
    have hpow := mul_le_mul_of_nonneg_right hh (pow_nonneg hV 6)
    have hval : (1+T/H)*(2*B*W/V^2)*V^6 = 4*K*N*L*(B*V^4+16*T*B^3) := by
      have hVnz : V≠0 := by intro h; simp [h] at hV'
      dsimp only [H,W]; field_simp [hVnz]; ring
    apply (hpow.trans_eq hval).trans
    have hpu : 0 ≤ (K*N*L)*(B*V^4) := by positivity
    have hpv : 0 ≤ (K*N*L)*(T*B^3) := by positivity
    linarith only [hpu,hpv]

end AnalyticNumberTheory.SieveMethods
