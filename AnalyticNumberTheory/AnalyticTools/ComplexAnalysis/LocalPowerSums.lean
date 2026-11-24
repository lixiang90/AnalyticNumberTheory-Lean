import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.Liouville

/-!
# Local power sums of zeros

After removing the zeros in a half-radius disk, Cauchy's estimates for the
remaining logarithmic derivative bound all of its Taylor coefficients. The
normalization gives the inverse powers of the distances to the zeros directly.
-/

noncomputable section
open Complex Filter Metric Finset MeromorphicOn
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Taylor coefficient with the alternating sign appropriate to logarithmic
derivatives of Dirichlet series. -/
def signedTaylorCoeff (g : ℂ → ℂ) (c : ℂ) (k : ℕ) : ℂ :=
  (-1:ℂ)^k / (k.factorial:ℂ) * iteratedDeriv k g c

theorem signedTaylorCoeff_congr {g h : ℂ → ℂ} {c : ℂ} (he : g =ᶠ[𝓝 c] h) (k : ℕ) :
    signedTaylorCoeff g c k = signedTaylorCoeff h c k := by
  simp only [signedTaylorCoeff,he.iteratedDeriv_eq]

theorem signedTaylorCoeff_add {g h : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c) (hh : AnalyticAt ℂ h c) (k : ℕ) :
    signedTaylorCoeff (fun z => g z+h z) c k = signedTaylorCoeff g c k + signedTaylorCoeff h c k := by
  simp only [signedTaylorCoeff,iteratedDeriv_fun_add hg.contDiffAt hh.contDiffAt,mul_add]

theorem signedTaylorCoeff_inv_sub (a c : ℂ) (k : ℕ) :
    signedTaylorCoeff (fun w => (w-a)⁻¹) c k = (c-a)⁻¹^(k+1) := by
  have he := congrFun (iter_deriv_inv_linear_sub k (1:ℂ) a) c
  simp only [one_mul,one_pow,mul_one] at he
  rw [signedTaylorCoeff,iteratedDeriv_eq_iterate,he,show (-1-(k:ℤ)) = -(↑(k+1:ℕ):ℤ) by omega,
    zpow_neg,zpow_natCast,inv_pow]
  have hk : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hsg : (-1:ℂ)^k*(-1)^k=1 := by rw [← mul_pow]; simp
  calc
    _ = (((-1:ℂ)^k*(-1)^k)*((k.factorial:ℂ)/(k.factorial:ℂ)))*((c-a)^(k+1))⁻¹ := by ring
    _ = _ := by rw [hsg,div_self hk,one_mul,one_mul]

/-- Taylor coefficients of the logarithmic derivative are inverse-power sums
over the zeros at distance at most 3/8 from the center, with an exponentially
bounded analytic remainder controlled by the original 3/4-disk growth. -/
theorem local_logDeriv_power_sum {f : ℂ → ℂ} {c : ℂ} {M : ℝ} (hM : 0<M)
    (hf : AnalyticOnNhd ℂ f (closedBall c (3/4))) (hc : f c ≠ 0)
    (hb : ∀ z ∈ sphere c (3/4), ‖f z/f c‖ ≤ M) :
    ∃ Z : Finset ℂ, (Z : Set ℂ) = zeroSet f c (3/8) ∧
      (∑ u ∈ Z, (analyticOrderNatAt f u:ℝ)) ≤ Real.log M / Real.log 2 ∧
      ∀ k : ℕ, ‖signedTaylorCoeff (logDeriv f) c k -
        ∑ u ∈ Z, (analyticOrderNatAt f u:ℂ)*(c-u)⁻¹^(k+1)‖ ≤
        352*(Real.log M)*(16/5:ℝ)^k := by
  classical
  have hf' : AnalyticOnNhd ℂ f (closedBall c (3/8)) := hf.mono (closedBall_subset_closedBall (by norm_num : (3/8:ℝ) ≤ 3/4))
  let D := MeromorphicOn.divisor f (closedBall c (3/8))
  let Z := (D.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hZ : (Z:Set ℂ)=zeroSet f c (3/8) := by
    simpa only [Z,Set.Finite.coe_toFinset,D] using divisor_support_eq_zeroSet (by norm_num) hf' hc
  have hzmem {u : ℂ} (hu : u∈Z) : u ∈ closedBall c (3/8) ∧ f u=0 := by
    apply mem_zeroSet.mp; rw [← hZ]; exact hu
  have hdiv (u : ℂ) (hu : u∈Z) : D u = (analyticOrderNatAt f u:ℤ) := by
    dsimp only [D]
    rw [AnalyticOnNhd.divisor_apply hf' (hzmem hu).1,← Nat.cast_analyticOrderNatAt
      (analyticOrderAt_ne_top_of_closedBall (by norm_num) hf' hc (hzmem hu).1)]
    simp
  refine ⟨Z,hZ,?_,fun k => ?_⟩
  · have h := zeroCount_half_le (R:=3/4) (by norm_num) (show 0<M*‖f c‖ by positivity) hf hc
      (fun z hz => by have h := hb z hz; rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr hc)] at h; exact h)
    norm_num at h
    rw [Real.log_mul hM.ne' (norm_ne_zero_iff.mpr hc),add_sub_cancel_right,zeroCount_eq_sum_analyticOrderNatAt
      (by norm_num) hf' hc hZ] at h
    exact_mod_cast h
  · obtain ⟨g,hg,hgn,hgb,hs⟩ := extract_ball_zeros (by norm_num : 0<(3/8:ℝ))
      (by norm_num : (3/8:ℝ)<3/4) hf hc hb
    norm_num at hgb
    let P := fun z : ℂ => ∑ u ∈ Z, (analyticOrderNatAt f u:ℂ)*(z-u)⁻¹
    have hfa : AnalyticAt ℂ f c := hf c (mem_closedBall_self (by norm_num))
    have hga : AnalyticAt ℂ g c := hg c (mem_closedBall_self (by norm_num))
    have hne (u : ℂ) (hu : u∈Z) : c-u ≠ 0 := sub_ne_zero.mpr (by
      intro he; exact hc (he ▸ (hzmem hu).2))
    have hpa (u : ℂ) (hu : u∈Z) : AnalyticAt ℂ (fun z => (analyticOrderNatAt f u:ℂ)*(z-u)⁻¹) c :=
      analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (hne u hu))
    have hlocal : logDeriv f =ᶠ[𝓝 c] fun z => P z+logDeriv g z := by
      filter_upwards [ball_mem_nhds c (by norm_num : 0<(3/4:ℝ)),hfa.continuousAt.eventually_ne hc] with z hz hzn
      have h := hs z hz hzn
      have hfin : (∑ᶠ u, (D u:ℂ)/(z-u)) = P z := by
        rw [finsum_eq_sum_of_support_subset _ (s:=Z)]
        · apply sum_congr rfl
          intro u hu
          rw [hdiv u hu,Int.cast_natCast,div_eq_mul_inv]
        · intro u hu
          by_contra hn
          have hd : D u=0 := by
            by_contra hd
            exact hn ((D.finiteSupport (isCompact_closedBall _ _)).mem_toFinset.mpr hd)
          simpa [Function.mem_support,hd] using hu
      change logDeriv f z-(∑ᶠ u,(D u:ℂ)/(z-u))=logDeriv g z at h
      rw [hfin] at h; linear_combination h
    have hgs (z : ℂ) (hz : z∈closedBall c (5/16)) : AnalyticAt ℂ (logDeriv g) z := by
      have hm := closedBall_subset_closedBall (by norm_num : (5/16:ℝ)≤3/8) hz
      have ha := hg z (closedBall_subset_closedBall (by norm_num : (3/8:ℝ)≤3/4) hm)
      exact ha.deriv.div ha (hgn z hm)
    have hP : signedTaylorCoeff P c k = ∑ u ∈ Z, (analyticOrderNatAt f u:ℂ)*(c-u)⁻¹^(k+1) := by
      unfold signedTaylorCoeff P
      rw [iteratedDeriv_fun_sum (fun u hu => (hpa u hu).contDiffAt),mul_sum]
      apply sum_congr rfl
      intro u _
      rw [iteratedDeriv_const_mul_field,mul_left_comm]
      exact congrArg ((analyticOrderNatAt f u:ℂ)*·) (signedTaylorCoeff_inv_sub u c k)
    rw [signedTaylorCoeff_congr hlocal,signedTaylorCoeff_add (Finset.analyticAt_fun_sum _ hpa)
      (hgs c (mem_closedBall_self (by norm_num))),hP,add_sub_cancel_left]
    have hgbd (z : ℂ) (hz : z∈sphere c (5/16)) : ‖logDeriv g z‖ ≤ 352*Real.log M := by
      have h := landau_logDeriv_le_of_ne_zero (by norm_num : (0:ℝ)≤5/16) (by norm_num : (5/16:ℝ)<3/8)
        (hg.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))).differentiableOn
        (fun w hw => hgn w (ball_subset_closedBall hw))
        (fun w hw => by rw [norm_div]; exact hgb w ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) hw))
        (sphere_subset_closedBall hz)
      norm_num at h
      exact h
    have hdiff : DifferentiableOn ℂ (logDeriv g) (closedBall c (5/16)) := fun z hz => (hgs z hz).differentiableAt.differentiableWithinAt
    have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num : 0<(5/16:ℝ))
      (DifferentiableOn.diffContOnCl_ball hdiff (fun _ hx => hx)) hgbd
    rw [signedTaylorCoeff,norm_mul,norm_div,norm_pow]
    simp only [norm_neg,norm_one,one_pow,Complex.norm_natCast]
    calc
      _ ≤ (1/(k.factorial:ℝ))*(k.factorial*(352*Real.log M)/(5/16:ℝ)^k) := by gcongr
      _ = _ := by rw [show (16/5:ℝ) = (5/16:ℝ)⁻¹ by norm_num,inv_pow]; field_simp

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
