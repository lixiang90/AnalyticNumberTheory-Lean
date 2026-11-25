import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachLogParameters
import AnalyticNumberTheory.AdditiveNumberTheory.PageParameterBounds
import AnalyticNumberTheory.AdditiveNumberTheory.PageExceptionalWeightDecay

/-!
# Numerical errors in the ternary Page argument

The ordinary arcs, minor arcs and cubic approximation errors all allow a
full inverse logarithm. The exceptional arithmetic weight determines the
smaller exponent used in the common bound.
-/

open Real
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Simplify the analytic errors at the twelfth-power logarithmic cutoff. -/
theorem goldbach_page_analytic_errors {x M L A : ℝ} (hx : 0<x) (hL : 1≤L)
    (hM : 1≤M) (hMhi : M≤L^12) (hMlo : L^6≤2*sqrt M) (hxlo : L^6≤x^(1/5:ℝ))
    (hA : 0≤A) :
    let D := A*x/L^30
    86*M^2*(D/x)+34/sqrt M+70000*(2/sqrt M+x^(-(1/5:ℝ)))*L^5+
      (54*M/(x/M)*D^3)/x^2 ≤ (86*A+68+350000+54*A^3)/L^(2/5:ℝ) := by
  let D := A*x/L^30
  have hl : 0<L := zero_lt_one.trans_le hL
  have hm : 0<M := zero_lt_one.trans_le hM
  have hs := sqrt_pos.mpr hm
  have hu : L^(2/5:ℝ)≤L := (rpow_le_rpow_of_exponent_le hL (by norm_num : (2/5:ℝ)≤1)).trans_eq (rpow_one _)
  have hL6 : L≤L^6 := by simpa using pow_le_pow_right₀ hL (by decide : 1≤6)
  have hM2 : M^2≤L^24 := (pow_le_pow_left₀ hm.le hMhi 2).trans_eq (by ring)
  have hD : 0≤D := by dsimp [D];positivity
  have hmajor : 86*M^2*(D/x)≤86*A/L := by
    calc
      _ ≤ 86*L^24*(D/x) := by gcongr
      _ = 86*A/L^6 := by dsimp [D];field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hl hL6
  have hinv : 1/sqrt M≤2/L^6 := (div_le_div_iff₀ hs (by positivity)).mpr (by linarith)
  have htrunc : 34/sqrt M≤68/L := by
    have h := hinv.trans (div_le_div_of_nonneg_left (by norm_num) hl hL6)
    simp only [div_eq_mul_inv] at h ⊢
    linarith only [h]
  have hminor : (2/sqrt M+x^(-(1/5:ℝ)))*L^5 ≤ 5/L := by
    rw [Real.rpow_neg hx.le,←one_div]
    have ht := one_div_le_one_div_of_le (by positivity) hxlo
    calc
      _ ≤ (4/L^6+1/L^6)*L^5 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact add_le_add (by simp only [div_eq_mul_inv] at hinv ⊢; linarith only [hinv]) ht
      _ = _ := by field_simp <;> ring
  have hcubic : (54*M/(x/M)*D^3)/x^2 ≤ 54*A^3/L := by
    calc
      _ = (54*A^3/L^90)*M^2 := by dsimp [D];field_simp <;> ring
      _ ≤ (54*A^3/L^90)*L^24 := by gcongr
      _ = 54*A^3/L^66 := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hl (by simpa using pow_le_pow_right₀ hL (by decide : 1≤66))
  change 86*M^2*(D/x)+34/sqrt M+70000*(2/sqrt M+x^(-(1/5:ℝ)))*L^5+(54*M/(x/M)*D^3)/x^2≤_
  apply le_trans _ (div_le_div_of_nonneg_left (by positivity) (rpow_pos_of_pos hl _) hu)
  have hmnr := mul_le_mul_of_nonneg_left hminor (by norm_num : (0:ℝ)≤70000)
  simp only [div_eq_mul_inv] at hmajor htrunc hcubic hmnr ⊢
  linarith only [hmajor,htrunc,hcubic,hmnr]

/-- Bound the missing singular-series terms for the conductor selected by Page. -/
theorem goldbach_page_missing_weight {d M : ℕ} {K L c : ℝ} (hL : 1≤L) (hK : 2≤K)
    (hlog : log (K+2)=sqrt (L/2)) (hc : 0<c) (hM : 1≤M)
    (hMhi : (M:ℝ)≤L^12) (hMlo : L^6≤2*sqrt M)
    (he : d=0 ∨ ∃ χ : DirichletCharacter ℂ d, PageExceptionalCharacter K c χ) :
    48/sqrt d ≤ (96+48*12960*c*(2*(2+50*12)^5))/L^(2/5:ℝ) := by
  let U := L^(2/5:ℝ)
  have hLp := zero_lt_one.trans_le hL
  have hu : 0<U := rpow_pos_of_pos hLp _
  have hs : 0<sqrt (L/2) := sqrt_pos.mpr (by positivity)
  have hlogM : 0≤log M := log_nonneg (by exact_mod_cast hM)
  have hbase : 0≤log ((M:ℝ)+2) := log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) M])
  have hmul : 1≤(1+log M)^2 := one_le_pow₀ (by linarith)
  rcases he with rfl|⟨χ,hχ⟩
  · simp;positivity
  by_cases hdm : d≤M
  · have H := page_exceptional_reciprocal_sqrt hK hχ
    rw [hlog] at H
    have hlogd : log ((d:ℝ)+2)≤log ((M:ℝ)+2) := by gcongr
    have hdpos : 0≤log ((d:ℝ)+2) := log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
    have hbound : log ((d:ℝ)+2)^3≤(1+log M)^2*log ((M:ℝ)+2)^3 :=
      (pow_le_pow_left₀ hdpos hlogd 3).trans (le_mul_of_one_le_left (by positivity) hmul)
    have hw := page_log_weight_saving hL hM 12 hMhi
    change (1+log M)^2*log ((M:ℝ)+2)^3/sqrt (L/2) ≤ 2*(2+50*12)^5/U at hw
    have hh : 1/sqrt d ≤ 12960*c*(2*(2+50*12)^5/U) := by
      apply H.trans
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hbound hs.le).trans hw) (by positivity)
    change _≤_/U
    apply (le_div_iff₀ hu).mpr
    have hn := (le_div_iff₀ hu).mp (show 1/sqrt d≤(12960*c*(2*(2+50*12)^5))/U by
      simpa only [mul_div_assoc] using hh)
    simp only [div_eq_mul_inv] at hn ⊢
    linarith only [hn]
  · have hsr : sqrt (M:ℝ)≤sqrt (d:ℝ) := sqrt_le_sqrt (by exact_mod_cast (le_of_not_ge hdm))
    have hU : U ≤ L^6 := by
      dsimp [U];rw [←rpow_natCast L 6];apply rpow_le_rpow_of_exponent_le hL;norm_num
    have hinv : 48/sqrt d≤96/U := (div_le_div_iff₀ (by
      exact lt_of_lt_of_le (sqrt_pos.mpr (show (0:ℝ)<M by exact_mod_cast hM)) hsr) hu).mpr
      (by linarith only [hU,hMlo,hsr])
    apply hinv.trans
    apply div_le_div_of_nonneg_right _ hu.le
    linarith only [show 0≤48*12960*c*(2*(2+50*12)^5) by positivity]

end AnalyticNumberTheory.AdditiveNumberTheory
