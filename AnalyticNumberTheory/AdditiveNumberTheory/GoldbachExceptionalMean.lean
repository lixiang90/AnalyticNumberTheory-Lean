import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachFrequencyWindows
import AnalyticNumberTheory.AdditiveNumberTheory.CircleMethod
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import AnalyticNumberTheory.SieveMethods.FrequencyWindows

/-! # Short-arc second moment of von Mangoldt sums

Gallagher's integral inequality localizes the coefficients to windows of
length at most `1/T`. Brun–Titchmarsh bounds their mass uniformly for
`N ≤ (1/T)²`, independently of the phases attached to the coefficients.
-/

noncomputable section

open Finset Real MeasureTheory AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.SieveMethods
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem sum_vonMangoldt_Icc_le_seven (N : ℕ) : ∑n∈Icc 1 N,Λ n≤7*(N:ℝ) := by
  rw [←Nat.floor_natCast N (R:=ℝ),←psi_eq_sum_Icc,Nat.floor_natCast]
  have h := psi_le_const_mul_self (Nat.cast_nonneg N)
  nlinarith [mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (by norm_num : 0<(4:ℝ))) (Nat.cast_nonneg (α:=ℝ) N)]

/-- A uniform second moment on a centered short arc, valid for arbitrary
complex coefficients dominated by the von Mangoldt function. -/
theorem vonMangoldt_shortArc_mean_square {N : ℕ} {T : ℝ} (hT : 0<T)
    (hT1 : T≤1) (hN : (N:ℝ)≤(1/T)^2) (a : ℕ → ℂ)
    (ha : ∀ n∈Icc 1 N, ‖a n‖≤Λ n) :
    ∫ t in (-T)..T, ‖expSum a (Icc 1 N) t‖^2 ≤ 175*Real.pi^3*N := by
  let S := Icc 1 N
  let ξ := fun n : ℕ => -2*Real.pi*(n:ℝ)
  let W := fun u : ℝ => S.filter (fun n => |u-T*ξ n|≤1/2)
  let B := fun u : ℝ => ∑ n∈W u,Λ n
  have hH : 1≤1/T := (one_le_div hT).2 hT1
  have hB (u : ℝ) : B u≤50*(1/T) := by
    apply sum_vonMangoldt_window_le hH hN (W u) (filter_subset ..)
    intro m hm n hn
    have hm' := (abs_le.mp (mem_filter.mp hm).2).1
    have hn' := (abs_le.mp (mem_filter.mp hn).2).2
    dsimp only [ξ] at hm' hn'
    have h : (n:ℝ)-m≤1/(2*Real.pi*T) := (le_div_iff₀ (by positivity)).2 (by nlinarith only [hm',hn'])
    apply h.trans (one_div_le_one_div_of_le hT _)
    nlinarith [mul_le_mul_of_nonneg_right Real.two_le_pi hT.le]
  have hsum (u : ℝ) : ‖∑n∈W u,a n‖≤B u :=
    (norm_sum_le ..).trans (sum_le_sum fun n hn => ha n (mem_filter.mp hn).1)
  have hpoint (u : ℝ) : ‖∑n∈W u,a n‖^2 ≤ (50*(1/T))*B u := by
    rw [sq]
    exact mul_le_mul ((hsum u).trans (hB u)) (hsum u) (norm_nonneg _) (by positivity)
  obtain ⟨hBi,hBI⟩ := frequencyWindow_integral S (fun n => T*ξ n)
    (fun n => (Λ n:ℝ))
  change Integrable B at hBi
  change (∫u : ℝ,B u)=∑n∈S,Λ n at hBI
  have hint := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg ‖∑n∈W u,a n‖))
    (hBi.const_mul (50*(1/T))) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul,hBI] at hint
  have hψ := sum_vonMangoldt_Icc_le_seven N
  have hGall := tent_gallagher_frequency_bound S ξ a hT
  have hphase (t : ℝ) : (∑n∈S,a n*Complex.exp (-(Complex.I*(t:ℂ)*(ξ n:ℂ))))=expSum a S t := by
    apply sum_congr rfl; intro n hn
    rw [e_def]
    congr 2
    dsimp [ξ]
    push_cast
    ring
  simp_rw [hphase] at hGall
  apply hGall.trans
  change (Real.pi^3/2)*T*(∫u : ℝ, ‖∑n∈W u,a n‖^2)≤_
  calc _ ≤ (Real.pi^3/2)*T*((50*(1/T))*(7*N)) :=
          mul_le_mul_of_nonneg_left (hint.trans (mul_le_mul_of_nonneg_left hψ (by positivity))) (by positivity)
       _ = _ := by field_simp; ring

/-- The corresponding cubic moment on a short arc. The logarithm-free
bound holds for absolute values, including a real or complex character twist. -/
theorem vonMangoldt_shortArc_mean_cube {N : ℕ} {T : ℝ} (hT : 0<T)
    (hT1 : T≤1) (hN : (N:ℝ)≤(1/T)^2) (a : ℕ → ℂ)
    (ha : ∀ n∈Icc 1 N, ‖a n‖≤Λ n) :
    ∫ t in (-T)..T, ‖expSum a (Icc 1 N) t‖^3 ≤ 1225*Real.pi^3*N^2 := by
  have hcont := (continuous_expSum a (Icc 1 N)).norm
  have hub (t : ℝ) : ‖expSum a (Icc 1 N) t‖ ≤ 7*(N:ℝ) :=
    (norm_expSum_le ..).trans ((sum_le_sum ha).trans (sum_vonMangoldt_Icc_le_seven N))
  have hpoint (t : ℝ) : ‖expSum a (Icc 1 N) t‖^3 ≤ 7*(N:ℝ)*‖expSum a (Icc 1 N) t‖^2 := by
    simpa only [pow_succ,mul_comm] using mul_le_mul_of_nonneg_right (hub t) (sq_nonneg ‖expSum a (Icc 1 N) t‖)
  calc _ ≤ ∫t in (-T)..T, 7*(N:ℝ)*‖expSum a (Icc 1 N) t‖^2 :=
            intervalIntegral.integral_mono_on (by linarith) ((hcont.pow 3).intervalIntegrable ..)
              ((continuous_const.mul (hcont.pow 2)).intervalIntegrable ..) (fun t _ => hpoint t)
       _ = (7*(N:ℝ))*(∫t in (-T)..T, ‖expSum a (Icc 1 N) t‖^2) := intervalIntegral.integral_const_mul ..
       _ ≤ (7*(N:ℝ))*(175*Real.pi^3*N) := mul_le_mul_of_nonneg_left
            (vonMangoldt_shortArc_mean_square hT hT1 hN a ha) (by positivity)
       _ = _ := by ring

end AnalyticNumberTheory.AdditiveNumberTheory
