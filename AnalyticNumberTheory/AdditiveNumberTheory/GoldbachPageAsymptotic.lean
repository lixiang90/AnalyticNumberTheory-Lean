import AnalyticNumberTheory.AdditiveNumberTheory.PageMajorArcParameters
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachPageErrors
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachDeweighting

/-!
# The ternary Goldbach asymptotic from Page's exceptional character theorem

Ordinary and exceptional arcs use the same character selected for the whole
range of moduli. The finite estimate states a numerical lower cutoff for
log N and retains the dependence of its coefficient on the Page estimates.
-/

open Real Filter Asymptotics Finset MeasureTheory
open scoped Topology
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Coefficient of the normalized error with a twelfth-power modulus cutoff
and thirty logarithms of pointwise saving. -/
noncomputable def goldbachPageConstant (c A : ℝ) : ℝ :=
  (86*A+68+350000+54*A^3) +
  (66150*π^3)*(77760*π^2*c)*(2*(2+50*12)^5) +
  (96+48*12960*c*(2*(2+50*12)^5))

set_option maxRecDepth 4096 in
/-- A finite ternary Goldbach estimate obtained by isolating the exceptional
character. The interval of validity is independent of the selected character. -/
theorem page_goldbachTernary_finite :
    ∃ c A b : ℝ, 0<c ∧ c≤1/4 ∧ 0<A ∧ 0<b ∧ ∀ {N : ℕ}, 2≤N →
      pageGoldbachLogThreshold≤log N →
      |goldbachTernaryWeighted N-goldbachTernarySingularSeries N*((N-1).choose 2:ℕ)| ≤
        goldbachPageConstant c (pageMajorArcLogConstant A b 12 30) *
          ((N:ℝ)^2/(log N)^(2/5:ℝ)) := by
  obtain ⟨c,A,b,hc,hc4,hA,hb,H⟩ := page_majorArc_parameters 12 30
  refine ⟨c,A,b,hc,hc4,hA,hb,?_⟩
  intro N hN hlarge
  let L := log (N:ℝ)
  let M := ⌊L^12⌋₊
  let K := exp (sqrt (log (sqrt N)))-2
  let U := L^(2/5:ℝ)
  let C := pageMajorArcLogConstant A b 12 30
  let D := C*N/L^30
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  obtain ⟨hL2,hM,hMhi,hMlo,hNM,hxlo,hY,hK,hMK,hlog⟩ := goldbach_log_cutoffs hn hlarge
  change 2≤L at hL2
  have hL : 1≤L := by linarith
  have hm : 0<(M:ℝ) := by exact_mod_cast hM
  have hC := pageMajorArcLogConstant_pos A b 12 30
  change 0<C at hC
  have hD : 0≤D := by dsimp [D];positivity
  have hU : 0<U := rpow_pos_of_pos (by linarith) _
  obtain ⟨e₀,he,hgood,hbad⟩ := H hM hMhi hNM hY hK hMK (by simp)
  let d := e₀.1
  let W := (1+log M)^2*log ((M:ℝ)+2)^3/log (K+2)
  let J := (66150*π^3)*(77760*π^2*c)
  let B := (N:ℝ)^2*J*W+54*M/((N:ℝ)/M)*D^3
  have hbad' : ∑ q ∈ (Icc 1 M).filter (d∣·), ∑ a ∈ coprimeResidues q,
      ‖∫ α in majorArc q a ((N:ℝ)/M), primeExpSum N α^3*e (-α*N)‖ ≤ B := by
    apply hbad.trans_eq
    dsimp only [B,D,J,W]
    ring
  have Hnorm := goldbachTernary_normalized_exceptional hM hNM hD hgood hbad'
  have Herr := goldbach_page_analytic_errors hn hL (by exact_mod_cast hM) hMhi hMlo hxlo hC.le
  have Hmiss := goldbach_page_missing_weight hL hK hlog hc hM hMhi hMlo (d:=d) (he.imp_right fun hp => ⟨e₀.2,hp⟩)
  have Hw : W ≤ 2*(2+50*12)^5/U := by
    dsimp only [W,U];rw [hlog];exact page_log_weight_saving hL hM 12 hMhi
  have hJ : 0≤J := by dsimp [J];positivity
  have hB : B/(N:ℝ)^2 = J*W+(54*M/((N:ℝ)/M)*D^3)/(N:ℝ)^2 := by
    dsimp only [B];field_simp
  rw [hB] at Hnorm
  have hf : |goldbachTernaryWeighted N-goldbachTernarySingularSeries N*((N-1).choose 2:ℕ)| /
      (N:ℝ)^2 ≤ goldbachPageConstant c C / U := by
    apply Hnorm.trans
    change 86*(M:ℝ)^2*(D/N)+34/sqrt M+70000*(2/sqrt M+(N:ℝ)^(-(1/5:ℝ)))*L^5+
      (J*W+54*M/((N:ℝ)/M)*D^3/(N:ℝ)^2)+48/sqrt d≤_
    change 86*(M:ℝ)^2*(D/N)+34/sqrt M+70000*(2/sqrt M+(N:ℝ)^(-(1/5:ℝ)))*L^5+
      54*M/((N:ℝ)/M)*D^3/(N:ℝ)^2≤(86*C+68+350000+54*C^3)/U at Herr
    change 48/sqrt d≤(96+48*12960*c*(2*(2+50*12)^5))/U at Hmiss
    change _≤((86*C+68+350000+54*C^3)+J*(2*(2+50*12)^5)+(96+48*12960*c*(2*(2+50*12)^5)))/U
    have hW := mul_le_mul_of_nonneg_left Hw hJ
    simp only [div_eq_mul_inv] at Herr Hmiss hW ⊢
    linarith only [Herr,Hmiss,hW]
  apply ((div_le_iff₀ (sq_pos_of_pos hn)).mp hf).trans_eq
  ring

/-- The weighted ternary asymptotic with saving two fifths of a logarithm,
from the common Page exceptional-character choice. -/
theorem page_goldbachTernaryWeighted_asymptotic :
    (fun N : ℕ => goldbachTernaryWeighted N-goldbachTernarySingularSeries N*(N:ℝ)^2/2) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^(2/5:ℝ)) := by
  obtain ⟨c,A,b,_,_,_,_,H⟩ := page_goldbachTernary_finite
  let C := goldbachPageConstant c (pageMajorArcLogConstant A b 12 30)
  apply IsBigO.of_bound (C+66)
  have hlim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),hlim.eventually_ge_atTop pageGoldbachLogThreshold,
    hlim.eventually_ge_atTop 1] with N hN ht hlog
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  let U := (log N)^(2/5:ℝ)
  have hu : 0<U := rpow_pos_of_pos (zero_lt_one.trans_le hlog) _
  have hux : U≤N := ((rpow_le_rpow_of_exponent_le hlog (by norm_num : (2/5:ℝ)≤1)).trans_eq
    (rpow_one _)).trans (Real.log_le_self hn.le)
  have hlin : (N:ℝ)≤(N:ℝ)^2/U := (le_div_iff₀ hu).mpr (by nlinarith [mul_le_mul_of_nonneg_left hux hn.le])
  have hm := (goldbachTernary_composition_error hN).trans (mul_le_mul_of_nonneg_left hlin (by norm_num : (0:ℝ)≤66))
  have hw := H hN ht
  change ‖goldbachTernaryWeighted N-_‖ ≤ (C+66)*‖(N:ℝ)^2/U‖
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (show 0≤(N:ℝ)^2/U by positivity)]
  exact (abs_sub_le _ _ _).trans ((add_le_add hw hm).trans_eq (by change C*(_/U)+66*(_/U)=_;ring))

/-- Ordered odd-prime triples with the logarithmic error inherited from Page's method. -/
theorem page_goldbachTernaryOddCount_asymptotic :
    (fun N : ℕ => (goldbachTernaryOddCount N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^(17/5:ℝ)) := by
  simpa only [show 3+(2/5:ℝ)=17/5 by norm_num] using
    goldbachTernary_deweight _ (fun _ => le_rfl) goldbachTernaryOddCount_le_count (by norm_num : (2/5:ℝ)≤1)
      page_goldbachTernaryWeighted_asymptotic

/-- The same Page estimate for representations by all primes, including two. -/
theorem page_goldbachTernaryCount_asymptotic :
    (fun N : ℕ => (goldbachTernaryCount N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^(17/5:ℝ)) := by
  simpa only [show 3+(2/5:ℝ)=17/5 by norm_num] using
    goldbachTernary_deweight _ goldbachTernaryOddCount_le_count (fun _ => le_rfl) (by norm_num : (2/5:ℝ)≤1)
      page_goldbachTernaryWeighted_asymptotic

end AnalyticNumberTheory.AdditiveNumberTheory
