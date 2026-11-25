import AnalyticNumberTheory.ExponentialSums.LogPhaseCorrelations
import AnalyticNumberTheory.SieveMethods.HalaszMontgomery
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Local large-value estimates for Dirichlet polynomials

A bound on the number of ordinates in every unit interval controls the
near-diagonal part of the Gram matrix. The correlation at larger separations
is bounded by the square root of the length of the ordinate window.
-/
noncomputable section
open Finset Real Complex
open scoped Classical ComplexConjugate
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.SieveMethods

variable {ι : Type*}

/-- The reciprocal-distance kernel averaged over a finite set of ordinates
with at most `K` points in any closed interval of length one. -/
theorem reciprocal_distance_sum_le (S : Finset ι) (t : ι → ℝ) {K T x : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hcell : ∀ u : ℝ, ((S.filter (fun i => u ≤ t i ∧ t i ≤ u+1)).card:ℝ) ≤ K)
    (hnear : ∀ i∈S, |t i-x| ≤ T) :
    ∑ i∈S, 1/(1+|t i-x|) ≤ 2*K*(1+Real.log (T+1)) := by
  let J := ⌊T⌋₊+1
  let j (i : ι) := ⌊|t i-x|⌋₊
  have hmap (i : ι) (hi : i∈S) : j i ∈ range J :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hnear i hi)))
  rw [←sum_fiberwise_of_maps_to hmap]
  have hblock (k : ℕ) (_ : k∈range J) :
      ∑ i∈S.filter (fun i => j i=k), 1/(1+|t i-x|) ≤ 2*K*(1/((k:ℝ)+1)) := by
    let A := S.filter (fun i => x+k ≤ t i ∧ t i ≤ x+k+1)
    let B := S.filter (fun i => x-k-1 ≤ t i ∧ t i ≤ x-k-1+1)
    let F := S.filter (fun i => j i=k)
    have hf : F ⊆ A ∪ B := by
      intro i hi
      obtain ⟨his,hki⟩ := mem_filter.mp hi
      change ⌊|t i-x|⌋₊=k at hki
      have hlo := Nat.floor_le (abs_nonneg (t i-x))
      have hup := Nat.lt_floor_add_one |t i-x|
      rw [hki] at hlo hup
      rcases le_total x (t i) with h | h
      · rw [abs_of_nonneg (by linarith)] at hlo hup
        exact mem_union_left _ (mem_filter.mpr ⟨his,by constructor <;> linarith⟩)
      · rw [abs_of_nonpos (by linarith)] at hlo hup
        exact mem_union_right _ (mem_filter.mpr ⟨his,by constructor <;> linarith⟩)
    have hc : (F.card:ℝ) ≤ 2*K := by
      have hn := (card_le_card hf).trans (card_union_le ..)
      have hr : (F.card:ℝ) ≤ (A.card:ℝ)+(B.card:ℝ) := by exact_mod_cast hn
      linarith only [hr,hcell (x+k),hcell (x-k-1)]
    have hh (i : ι) (hi : i ∈ F) : 1/(1+|t i-x|) ≤ 1/((k:ℝ)+1) := by
      have hd : ⌊|t i-x|⌋₊=k := (mem_filter.mp hi).2
      have h := Nat.floor_le (abs_nonneg (t i-x))
      rw [hd] at h
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    apply (sum_le_sum hh).trans
    simp only [sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  apply (sum_le_sum hblock).trans
  rw [←mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hJ : (J:ℝ) ≤ T+1 := by dsimp [J]; push_cast; linarith [Nat.floor_le hT]
  have hR : 0 < (J:ℝ) := by dsimp [J]; positivity
  apply le_trans _ (add_le_add_right (Real.log_le_log hR hJ) 1)
  simpa only [harmonic, Rat.cast_sum,Rat.cast_inv,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,
    Nat.cast_add,Nat.cast_one,one_div] using harmonic_le_one_add_log J

/-- Sampled mean estimate in a window of width `H` in the half-plane
`Re(s) ≥ σ`. The energy is computed on the line `Re(s) = σ`. -/
theorem huxley_local_large_values (S : Finset ι) (a : ℕ → ℂ) {N : ℕ} (hN : 1≤N)
    (z : ι → ℂ) {σ V K H : ℝ} (hV : 0 ≤ V) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hre : ∀ i∈S, σ ≤ (z i).re)
    (hcell : ∀ u : ℝ, ((S.filter (fun i => u ≤ (z i).im ∧ (z i).im ≤ u+1)).card:ℝ) ≤ K)
    (hdist : ∀ i∈S, ∀ j∈S, |(z j).im-(z i).im| ≤ H)
    (hlarge : ∀ i∈S, V ≤ ‖dirichletPoly a N (z i)‖) :
    (S.card:ℝ)*V^2 ≤ (∑ n∈Icc 1 N, ‖a n‖^2*(n:ℝ)^(-2*σ))*
      ((1+8000*π)*(1+Real.log N))*
      (2*K*N*(1+Real.log (H+1))+(S.card:ℝ)*Real.sqrt (1+H)) := by
  let b (n : ℕ) := a n*(n:ℂ)^(-(σ:ℂ))
  let s (i : ι) := z i-(σ:ℂ)
  have heq (i : ι) : dirichletPoly b N (s i) = dirichletPoly a N (z i) := by
    unfold dirichletPoly
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hn).1)
    dsimp only [b,s]; rw [mul_assoc,←Complex.cpow_add _ _ hn0]; congr 2; ring
  have hb (n : ℕ) (hn : n∈Icc 1 N) : ‖b n‖^2 = ‖a n‖^2*(n:ℝ)^(-2*σ) := by
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    dsimp only [b]; rw [norm_mul,mul_pow]
    have hn' : ‖(n:ℂ)^(-(σ:ℂ))‖ = (n:ℝ)^(-σ) := by
      rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
    rw [hn',←Real.rpow_mul_natCast hn0.le]; congr 2 <;> push_cast <;> ring
  have h := halasz_montgomery_dirichletPoly_large_values S b N s hV (fun i hi => (heq i).symm ▸ hlarge i hi)
  rw [sum_congr rfl hb] at h
  let A := (1+8000*π)*(1+Real.log N)
  let P := 2*K*N*(1+Real.log (H+1))+(S.card:ℝ)*Real.sqrt (1+H)
  let G := ∑ n∈Icc 1 N, ‖a n‖^2*(n:ℝ)^(-2*σ)
  have hA : 0 ≤ A := by dsimp [A]; have := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N); positivity
  have hG : 0 ≤ G := sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hP : 0 ≤ P := by dsimp [P]; have := Real.log_nonneg (by linarith : 1 ≤ H+1); positivity
  have hrow (i : ι) (hi : i∈S) : ∑ j∈S, ‖dirichletPoly (fun _ => 1) N (conj (s i)+s j)‖ ≤ A*P := by
    let d (j : ι) := (z j).im-(z i).im
    have hz (j : ι) (hj : j ∈ S) :
        ‖dirichletPoly (fun _ => 1) N (conj (s i)+s j)‖ ≤ A*(N*(1/(1+|d j|))+Real.sqrt (1+H)) := by
      let w := conj (s i)+s j
      have hr : 0 ≤ w.re := by simp only [w,s,Complex.add_re,Complex.conj_re,Complex.sub_re,Complex.ofReal_re]; linarith [hre i hi,hre j hj]
      have him : w.im = d j := by simp [w,s,d]; ring
      have hcorr := dirichlet_correlation_bound hN hr w.im
      rw [Complex.re_add_im] at hcorr
      simp only [dirichletPoly,one_mul]
      apply hcorr.trans
      change A*(N/(1+|w.im|)+Real.sqrt (1+|w.im|)) ≤ _
      rw [him,div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ hA
      gcongr; exact hdist i hi j hj
    have hb' := sum_le_sum hz
    simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul] at hb'
    apply hb'.trans
    dsimp only [P]
    apply mul_le_mul_of_nonneg_left _ hA
    apply add_le_add_left
    apply (mul_le_mul_of_nonneg_left (reciprocal_distance_sum_le S (fun j => (z j).im) hK hH hcell (hdist i hi)) (Nat.cast_nonneg N)).trans_eq
    ring
  by_cases hS : S.Nonempty
  · have hcard : 0 < (S.card:ℝ) := by exact_mod_cast card_pos.mpr hS
    have hb' := h.trans (mul_le_mul_of_nonneg_left (sum_le_sum hrow) hG)
    simp only [sum_const,nsmul_eq_mul] at hb'
    change ((S.card:ℝ)*V)^2 ≤ G*((S.card:ℝ)*(A*P)) at hb'
    change (S.card:ℝ)*V^2 ≤ G*A*P
    apply le_of_mul_le_mul_left (a:=(S.card:ℝ)) _ hcard
    convert hb' using 1 <;> ring
  · change (S.card:ℝ)*V^2 ≤ G*A*P
    simp only [not_nonempty_iff_eq_empty.mp hS,card_empty,Nat.cast_zero,zero_mul]
    exact mul_nonneg (mul_nonneg hG hA) hP

end AnalyticNumberTheory.SieveMethods
