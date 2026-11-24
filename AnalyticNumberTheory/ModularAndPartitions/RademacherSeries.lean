import AnalyticNumberTheory.ModularAndPartitions.PartitionFareyCoefficients
import AnalyticNumberTheory.ModularAndPartitions.PartitionRademacherIntegral

/-!
# Summation of the Rademacher arc integrals

Each denominator has at most `k` reduced numerators. An error of order
`1/(k√k N)` per arc therefore gives a total truncation error of order
`N⁻¹/²`. Absolute convergence then identifies the unordered series.
-/

open Complex Real Filter Finset
open scoped Topology
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.ModularAndPartitions

private theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ k ∈ Icc 1 N, (√(k:ℝ))⁻¹ ≤ 2*√N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hpos : 0 < √((N+1:ℕ):ℝ) := by positivity
    have hmono : √(N:ℝ) ≤ √((N+1:ℕ):ℝ) := Real.sqrt_le_sqrt (by norm_num)
    have h1 := Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ (N+1:ℕ) by positivity)
    have hstep : (√((N+1:ℕ):ℝ))⁻¹ ≤ 2*(√((N+1:ℕ):ℝ)-√(N:ℝ)) := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      push_cast at h2 ⊢
      push_cast at hmono
      nlinarith only [h1,h2,sq_nonneg (√((N:ℝ)+1)-√(N:ℝ))]
    linarith

private noncomputable def seriesTerm (n k : ℕ) : ℂ :=
  (√(k:ℝ):ℂ)*rademacherKloostermanSum dedekindSum k n*(rademacherPsi k n:ℂ)

private theorem sum_phase_main (n k : ℕ) :
    ∑ h ∈ (range k).filter (fun h => h.Coprime k),
      rademacherPhase h k n * ((√(k:ℝ):ℂ)*(rademacherPsi k n:ℂ)) = seriesTerm n k := by
  rw [← sum_mul]
  unfold seriesTerm rademacherKloostermanSum rademacherPhase
  ring

/-- Summing the individual Bessel approximation errors produces a partial
sum estimate with the same `N⁻¹/²` error as the modular transformation. -/
theorem partitionCount_sub_rademacherPartialSum_le_of_arc_bound {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (harc : ∀ {N k : ℕ}, 0 < k → k ≤ N → ∀ L R : ℝ,
      (1/((k:ℝ)*(2*N)) ≤ L ∧ L ≤ 1/((k:ℝ)*N)) →
      (1/((k:ℝ)*(2*N)) ≤ R ∧ R ≤ 1/((k:ℝ)*N)) →
      ‖rademacherArcIntegral n k N L R - (√(k:ℝ):ℂ)*(rademacherPsi k n:ℂ)‖ ≤
        B/((k:ℝ)*√k*N)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 0 < N →
      ‖(partitionCount n : ℂ) - ∑ k ∈ Icc 1 N,
        (√(k:ℝ):ℂ)*rademacherKloostermanSum dedekindSum k n*(rademacherPsi k n:ℂ)‖ ≤ C/√N := by
  obtain ⟨A,hA,ha⟩ := partitionCount_sub_sum_rademacherArcs_le n
  refine ⟨A+2*B,by positivity,fun {N} hN => ?_⟩
  let F (k h : ℕ) := rademacherPhase h k n * rademacherArcIntegral n k N
    (-fareyFullLeft N (mkRat h k)) (fareyRight N (mkRat h k))
  let G (k h : ℕ) := rademacherPhase h k n * ((√(k:ℝ):ℂ)*(rademacherPsi k n:ℂ))
  let S (k : ℕ) := (range k).filter (fun h => h.Coprime k)
  have hsingle {k : ℕ} (hk : k ∈ Icc 1 N) {h : ℕ} (hh : h ∈ S k) :
      ‖F k h-G k h‖ ≤ B/((k:ℝ)*√k*N) := by
    dsimp only [F,G]
    rw [← mul_sub, norm_mul, norm_rademacherPhase, one_mul]
    obtain ⟨hk,hkN⟩ := mem_Icc.mp hk
    obtain ⟨hlt,hcop⟩ := mem_filter.mp hh
    obtain ⟨hl,hr⟩ := fareyReduced_width_bounds hk hkN (mem_range.mp hlt) hcop
    exact harc hk hkN _ _ hl hr
  have hgroup {k : ℕ} (hk : k ∈ Icc 1 N) :
      ‖(∑ h ∈ S k, F k h)-(∑ h ∈ S k, G k h)‖ ≤ (B/N)*(√(k:ℝ))⁻¹ := by
    rw [← sum_sub_distrib]
    apply (norm_sum_le ..).trans
    apply (sum_le_sum fun h hh => hsingle hk hh).trans
    rw [sum_const, nsmul_eq_mul]
    have hcard : ((S k).card:ℝ) ≤ k := by exact_mod_cast (card_filter_le ..).trans_eq (card_range k)
    have hk' : (0:ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    have hle := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ B/((k:ℝ)*√k*N))
    exact hle.trans_eq (by field_simp)
  let U := ∑ k ∈ Icc 1 N, ∑ h ∈ S k, F k h
  let V := ∑ k ∈ Icc 1 N, ∑ h ∈ S k, G k h
  have hd : ‖U-V‖ ≤ (2*B)/√N := by
    dsimp only [U,V]
    rw [← sum_sub_distrib]
    apply (norm_sum_le ..).trans
    apply (sum_le_sum fun k hk => hgroup hk).trans
    rw [← mul_sum]
    apply (mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by positivity : 0 ≤ B/N)).trans_eq
    have hs := Real.sq_sqrt (Nat.cast_nonneg N)
    have hp : 0 < √(N:ℝ) := by positivity
    field_simp
    linear_combination B*hs
  have hv : V = ∑ k ∈ Icc 1 N, seriesTerm n k := sum_congr rfl (fun k _ => sum_phase_main n k)
  change ‖(partitionCount n:ℂ) - ∑ k ∈ Icc 1 N, seriesTerm n k‖ ≤ _
  rw [← hv, add_div]
  exact (show ‖(partitionCount n:ℂ)-V‖ ≤ ‖(partitionCount n:ℂ)-U‖+‖U-V‖ by simpa only [dist_eq_norm] using dist_triangle (partitionCount n:ℂ) U V).trans (add_le_add (ha hN) hd)

set_option maxHeartbeats 650000 in
/-- An arc estimate with summable total error identifies the convergent
Rademacher series with the partition number. -/
theorem rademacherSeriesFormula_of_arc_bound
    (harc : ∀ n : ℕ, 1 ≤ n → ∃ B : ℝ, 0 ≤ B ∧ ∀ {N k : ℕ}, 0 < k → k ≤ N → ∀ L R : ℝ,
      (1/((k:ℝ)*(2*N)) ≤ L ∧ L ≤ 1/((k:ℝ)*N)) →
      (1/((k:ℝ)*(2*N)) ≤ R ∧ R ≤ 1/((k:ℝ)*N)) →
      ‖rademacherArcIntegral n k N L R - (√(k:ℝ):ℂ)*(rademacherPsi k n:ℂ)‖ ≤
        B/((k:ℝ)*√k*N)) : RademacherSeriesFormula dedekindSum := by
  intro n hn
  obtain ⟨B,hB,hb⟩ := harc n hn
  obtain ⟨C,hC,hbound⟩ := partitionCount_sub_rademacherPartialSum_le_of_arc_bound hB hb
  change HasSum (fun k : ℕ+ => seriesTerm n k) _
  apply (hasSum_pnat_iff_hasSum_succ (f := seriesTerm n)).mpr
  have hs : Summable fun k : ℕ => ‖seriesTerm n (k+1)‖ :=
    (summable_pnat_iff_summable_succ (f := fun k => ‖seriesTerm n k‖)).mp (summable_norm_rademacherTerm dedekindSum hn)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs,tendsto_iff_norm_sub_tendsto_zero]
  have heq (N : ℕ) : ∑ k ∈ range N, seriesTerm n (k+1) = ∑ k ∈ Icc 1 N, seriesTerm n k := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih]
  have hlim : Tendsto (fun N : ℕ => C/√N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  rw [heq,norm_sub_rev]
  exact hbound hN

/-- Rademacher's exact, absolutely convergent expansion of the integer
partition number at each positive integer, with its Dedekind-sum phases. -/
theorem rademacherSeriesFormula : RademacherSeriesFormula dedekindSum := by
  apply rademacherSeriesFormula_of_arc_bound
  intro n hn
  obtain ⟨C,hC,H⟩ := norm_rademacherArcIntegral_sub_psi_le n hn
  refine ⟨C,hC.le,?_⟩
  intro N k hk hkN L R hL hR
  apply H hk (by exact_mod_cast hkN) _ hL.2 _ hR.2
  · simpa only [mul_left_comm,mul_comm,mul_assoc] using hL.1
  · simpa only [mul_left_comm,mul_comm,mul_assoc] using hR.1

/-- The error after retaining denominators up to `N` is at most
`C(n)/√N`, for all positive integer cutoffs. -/
theorem partitionCount_sub_rademacherPartialSum_le {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 0 < N →
      ‖(partitionCount n : ℂ) - ∑ k ∈ Icc 1 N,
        (√(k:ℝ):ℂ)*rademacherKloostermanSum dedekindSum k n*(rademacherPsi k n:ℂ)‖ ≤ C/√N := by
  obtain ⟨B,hB,H⟩ := norm_rademacherArcIntegral_sub_psi_le n hn
  apply partitionCount_sub_rademacherPartialSum_le_of_arc_bound hB.le
  intro N k hk hkN L R hL hR
  apply H hk (by exact_mod_cast hkN) _ hL.2 _ hR.2
  · simpa only [mul_left_comm,mul_comm,mul_assoc] using hL.1
  · simpa only [mul_left_comm,mul_comm,mul_assoc] using hR.1

end AnalyticNumberTheory.ModularAndPartitions
