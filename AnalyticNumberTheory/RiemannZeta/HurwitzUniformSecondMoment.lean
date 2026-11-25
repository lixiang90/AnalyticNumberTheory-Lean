import AnalyticNumberTheory.RiemannZeta.HurwitzCorrectedBlockMean
import AnalyticNumberTheory.RiemannZeta.HurwitzUniformWaveEnergy

/-!
# The uniform square-root error in the Hurwitz critical-line moment

Summing the corrected discrepancy over all cutoff blocks and removing the
moving-polynomial off-diagonal costs O(√T (a^(-1/2)+1+log T)).
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped Interval
namespace AnalyticNumberTheory.RiemannZeta

private theorem cutoff_mono : Monotone hardyCutoff := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hij) 2) (by positivity)

private theorem corrected_mean : ∃ C : ℝ,0<C ∧ ∀ {a T : ℝ}, a∈Ioc (0:ℝ) 1 → 8*Real.pi≤T →
    let N := ⌊Real.sqrt (T/(2*Real.pi))⌋₊+1
    |∫t in (8*Real.pi)..T,‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-
      ‖hurwitzWaveSum a N t‖^2|≤C*Real.sqrt T*((Real.sqrt a)⁻¹+(1+Real.log T)) := by
  obtain ⟨C,hC,H⟩ := hurwitz_corrected_block_mean
  let D := 16/Real.log 2+8
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨C*(2+2*D),by positivity,?_⟩
  intro a T ha ht N
  let M := hardyCutoffIndex T
  let b := hardyCutoff 2
  let f := fun t : ℝ => ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-‖hurwitzWaveSum a N t‖^2
  let A := (Real.sqrt a)⁻¹
  have hA : 0≤A := by dsimp [A];positivity
  have hb : b=8*Real.pi := by dsimp [b,hardyCutoff];norm_num;ring
  have hbT : b≤T := hb ▸ ht
  have hT : 4≤T := by linarith [Real.pi_gt_three]
  have hp : 0<T := by linarith
  have hM : 2≤M := (le_hardyCutoffIndex_iff hp.le).mpr hbT
  have hMt : hardyCutoff M≤T := (le_hardyCutoffIndex_iff hp.le).mp le_rfl
  have htM : T≤hardyCutoff (M+1) := le_of_lt (not_le.mp fun h => by
    have h' := (le_hardyCutoffIndex_iff hp.le).mpr h;change M+1≤M at h';omega)
  have hMroot : (M:ℝ)≤Real.sqrt T := (Nat.floor_le (Real.sqrt_nonneg _)).trans
    (Real.sqrt_le_sqrt (div_le_self hp.le (by linarith [Real.pi_gt_three])))
  have hMN : N=M+1 := rfl
  have hroot : 2≤Real.sqrt T := Real.le_sqrt_of_sq_le (by linarith)
  have hNr : (N:ℝ)≤2*Real.sqrt T := by rw [hMN,Nat.cast_add,Nat.cast_one];linarith
  have hN : 1≤N := by omega
  have hnT : (N:ℝ)≤T := hNr.trans (by nlinarith [Real.sq_sqrt hp.le,sq_nonneg (Real.sqrt T-2)] )
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hN) hnT
  have hi (x y : ℝ) : IntervalIntegrable f volume x y :=
    (((continuous_hurwitz_critical_line a).norm.pow 2).intervalIntegrable ..).sub (hurwitzWaveSum_sq_intervalIntegrable a N x y)
  let J := fun j : ℕ => ∫t in (hardyCutoff j)..(min (hardyCutoff (j+1)) T),f t
  have he : (∫t in b..T,f t)=∑j∈Finset.Icc 2 M,J j := by
    rw [←Finset.Ico_add_one_right_eq_Icc,sum_Ico_succ_top hM]
    have hcalc : (∑j∈Finset.Ico 2 M,J j)=∫t in b..(hardyCutoff M),f t := by
      apply (sum_congr rfl (g:=fun j => ∫t in (hardyCutoff j)..(hardyCutoff (j+1)),f t) (fun j hj=>?_)).trans
      · exact intervalIntegral.sum_integral_adjacent_intervals_Ico hM (fun j _=>hi ..)
      · dsimp [J];rw [min_eq_left ((cutoff_mono (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2)).trans hMt)]
    rw [hcalc,show J M=(∫t in (hardyCutoff M)..T,f t) by dsimp [J];rw [min_eq_right htM] ]
    exact (intervalIntegral.integral_add_adjacent_intervals (hi b (hardyCutoff M)) (hi (hardyCutoff M) T)).symm
  have hJ (j : ℕ) (hj : j∈Finset.Icc 2 M) : |J j|≤C*(A+2+∑n∈Finset.Icc 1 N,criticalCosineGap j n) := by
    obtain ⟨hj',hjM⟩ := Finset.mem_Icc.mp hj
    apply H ha hj' (by omega)
    exact ⟨le_min (cutoff_mono (Nat.le_succ _)) ((cutoff_mono hjM).trans hMt),min_le_left ..⟩
  have hsum := (abs_sum_le_sum_abs J (Finset.Icc 2 M)).trans (sum_le_sum hJ)
  rw [←mul_sum,sum_add_distrib] at hsum
  have h₁ : (∑_j∈Finset.Icc 2 M,(A+2))≤(M:ℝ)*(A+2) := by
    simp only [sum_const,nsmul_eq_mul,Nat.card_Icc]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact_mod_cast (by omega : M+1-2≤M)
  have hgap (m n : ℕ) : 0≤criticalCosineGap m n := by unfold criticalCosineGap;split_ifs <;>positivity
  have h₂ := (sum_le_sum_of_subset_of_nonneg (f:=fun j=>∑n∈Finset.Icc 1 N,criticalCosineGap j n)
    (show Finset.Icc 2 M⊆Finset.Icc 1 N from Finset.Icc_subset_Icc (by decide) (by omega))
    (fun i _ _=>sum_nonneg (fun n _=>hgap i n))).trans (sum_criticalCosineGap N hN)
  have hL : 0≤1+Real.log N := by have := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN);linarith
  have h := mul_le_mul hNr (show 1+Real.log N≤1+Real.log T by linarith) hL (by positivity)
  have h' := mul_le_mul_of_nonneg_right hMroot (show 0≤A+2 by linarith)
  change |∫t in (8*Real.pi)..T,f t|≤_
  rw [←hb,he]
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hC.le).trans
  change C*((M:ℝ)*(A+2)+D*N*(1+Real.log N))≤C*(2+2*D)*Real.sqrt T*(A+(1+Real.log T))
  rw [show C*(2+2*D)*Real.sqrt T*(A+(1+Real.log T))=
      C*((2+2*D)*Real.sqrt T*(A+(1+Real.log T))) by ring]
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hΛ := Real.log_nonneg (show 1≤T by linarith)
  nlinarith only [h',mul_le_mul_of_nonneg_left h hD.le,
    mul_nonneg hA (Real.sqrt_nonneg T),mul_nonneg hD.le (mul_nonneg hA (Real.sqrt_nonneg T)),
    mul_nonneg (Real.sqrt_nonneg T) hΛ]

/-- After removing the exact moving harmonic diagonal from the actual
critical-line square, the error is uniform in every real shift in (0,1]. -/
theorem hurwitz_critical_diagonal_uniform : ∃ C : ℝ,0<C ∧ ∀ {a T : ℝ}, a∈Ioc (0:ℝ) 1 → 8*Real.pi≤T →
    |∫t in (8*Real.pi)..T,‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-
      hurwitzCriticalDiagonal a t|≤C*Real.sqrt T*((Real.sqrt a)⁻¹+(1+Real.log T)) := by
  obtain ⟨C,hC,H⟩ := corrected_mean
  obtain ⟨D,hD,J⟩ := hurwitz_wave_energy_uniform
  refine ⟨C+D,by positivity,?_⟩
  intro a T ha ht
  let N := ⌊Real.sqrt (T/(2*Real.pi))⌋₊+1
  let f := fun t : ℝ => ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2
  let g := fun t : ℝ => ‖hurwitzWaveSum a N t‖^2
  let d := hurwitzCriticalDiagonal a
  let b := 8*Real.pi
  have hf : IntervalIntegrable f volume b T := ((continuous_hurwitz_critical_line a).norm.pow 2).intervalIntegrable ..
  have hg : IntervalIntegrable g volume b T := hurwitzWaveSum_sq_intervalIntegrable a N b T
  have hd : IntervalIntegrable d volume b T := (hurwitzCriticalDiagonal_monotone ha.1).intervalIntegrable
  have h₁ := H ha ht
  have h₂ := J ha ht
  change |∫t in b..T,f t-g t|≤_ at h₁
  change |∫t in b..T,g t-d t|≤_ at h₂
  change |∫t in b..T,f t-d t|≤_
  rw [intervalIntegral.integral_sub hf hg] at h₁
  rw [intervalIntegral.integral_sub hg hd] at h₂
  rw [intervalIntegral.integral_sub hf hd]
  exact (abs_sub_le (∫t in b..T,f t) (∫t in b..T,g t) (∫t in b..T,d t)).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end AnalyticNumberTheory.RiemannZeta
