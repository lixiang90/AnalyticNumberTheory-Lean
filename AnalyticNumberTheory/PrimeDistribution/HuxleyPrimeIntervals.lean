import AnalyticNumberTheory.RiemannZeta.VinogradovKorobov
import AnalyticNumberTheory.PrimeDistribution.HuxleyZeroSums
import AnalyticNumberTheory.PrimeDistribution.HuxleyIntervalParameters

/-!
# Prime intervals at the seven-twelfths threshold

Huxley's density estimate and the truncated explicit formula give a
quantitative prime number theorem in intervals just above `x^(7/12)`,
using the Vinogradov–Korobov zero-free region.
-/
noncomputable section
open Filter Real Finset
namespace AnalyticNumberTheory.PrimeDistribution

/-- Uniform von Mangoldt asymptotic with error
`O(h exp(−c (log log x)^a))` throughout the seven-twelfths boundary range.
The condition `1 < a` absorbs the fixed logarithmic factors in the density estimate. -/
theorem huxley_psi_interval_of_vinogradovKorobov_of_le (hz : VinogradovKorobovZeroFreeHypothesis)
    {a : ℝ} (ha : 1<a) :
    ∃ c>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop, ∀ h : ℝ,
      x^(7/12:ℝ)*Real.exp (huxleyIntervalCorrection a x) ≤ h → h≤x →
      |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤
        C*h*Real.exp (-c*(Real.log (Real.log x))^a) := by
  obtain ⟨d,hd,hgap⟩ := vinogradovKorobov_box_gap hz
  obtain ⟨A,hA,hzero⟩ := huxley_zero_sum_margin
  obtain ⟨B,hB,hexplicit⟩ := psi_interval_zero_sum_bound
  refine ⟨d/2,by positivity,2*B+A,by positivity,?_⟩
  filter_upwards [huxley_interval_parameters ha hd,hgap,eventually_ge_atTop (2:ℝ)] with x hp hg hx
  let L := Real.log x
  let l := Real.log L
  let E := l^a
  let F := huxleyIntervalCorrection a x
  let T := Real.exp ((5/12)*(L-F))
  let δ := d/vinogradovKorobovDenom x
  let e := Real.exp (-(d/2)*E)
  let m := x^(7/12:ℝ)*Real.exp F
  change 16≤L ∧ 1≤l ∧ 0<vinogradovKorobovDenom x ∧ F=vinogradovKorobovDenom x*E ∧ F≤L/2 ∧ 48*l≤d*E/2 ∧ 2*(1+d)*E≤F at hp
  obtain ⟨hL,hl,hD,hFE,hFL,habs,hbig⟩ := hp
  have hx0 : 0<x := by linarith
  have hLp : 0<L := by linarith
  have hlp : 0<l := by linarith
  have hE : 0<E := Real.rpow_pos_of_pos hlp _
  have hF : 0≤F := by rw [hFE]; positivity
  have hT0 : 0<T := Real.exp_pos _
  have hTL : Real.log T = (5/12)*(L-F) := Real.log_exp _
  have hT2 : 2≤T := by
    have hh : Real.log 2 ≤ (5/12)*(L-F) := by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
    exact (Real.log_le_log_iff (by norm_num) hT0).mp (hTL ▸ hh)
  have hTx : T≤x := by
    apply (Real.log_le_log_iff hT0 hx0).mp
    rw [hTL]; change _ ≤ L; linarith
  have hmargin : (12/5)*Real.log T+F ≤ Real.log x := by rw [hTL]; change _ ≤ L; linarith
  have hδ (z : ℂ) (hz : z∈nontrivialZerosUpTo T) : δ≤1-z.re := by
    apply (div_le_iff₀ hD).mpr
    obtain ⟨h₀,h₁,h₂,h₃⟩ := mem_nontrivialZerosUpTo.mp hz
    exact hg z (mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,h₃.trans hTx⟩)
  have hsum := hzero (by linarith : 1<x) hT2 hF hmargin hδ
  have hgapexp : -F*δ = -d*E := by dsimp only [δ]; rw [hFE]; field_simp
  rw [hgapexp] at hsum
  have hlogL : Real.log (1+L) ≤ 2*l := by
    have hh := Real.log_le_log (by linarith : 0<1+L) (by linarith : 1+L≤2*L)
    rw [Real.log_mul (by norm_num) hLp.ne'] at hh
    dsimp only [l]; linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hsave : (1+L)^24*Real.exp (-d*E) ≤ e := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by linarith : 0<1+L),←Real.exp_add]
    apply Real.exp_le_exp.mpr; norm_num only [Nat.cast_ofNat]; linarith only [hlogL,habs]
  have hsum' : (∑ z∈nontrivialZerosUpTo T,(zeroMultiplicity z:ℝ)*x^(z.re-1)) ≤ A*e := by
    apply hsum.trans
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsave hA.le
  have htquot : x/T = m*Real.exp (-(7/12)*F) := by
    calc
      x/T = Real.exp (L-(5/12)*(L-F)) := by rw [Real.exp_sub,Real.exp_log hx0]
      _ = _ := by dsimp only [m]; rw [Real.rpow_def_of_pos hx0,←Real.exp_add,←Real.exp_add]; congr 1; dsimp only [L]; ring
  have htr : Real.exp (-(7/12)*F)*L^2 ≤ e := by
    rw [←Real.rpow_two,Real.rpow_def_of_pos hLp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -(7/12)*F+l*2 ≤ -(d/2)*E
    linarith only [habs,hbig,hE,mul_nonneg hd.le hE.le]
  intro h hm hhx
  change m≤h at hm
  have hm0 : 0<m := by dsimp [m]; positivity
  have hh : 0≤h := hm0.le.trans hm
  have H := hexplicit hx hh hhx hT2 hTx
  have ht : x*L^2/T ≤ h*e := by
    calc
      x*L^2/T = m*(Real.exp (-(7/12)*F)*L^2) := by rw [←mul_assoc,←htquot]; ring
      _ ≤ _ := mul_le_mul hm htr (by positivity) hh
  have hsmall : L ≤ x*L^2/T := by
    have hq : 1≤x/T := (one_le_div hT0).mpr hTx
    have hq' := mul_le_mul_of_nonneg_right hq (sq_nonneg L)
    nlinarith only [hq', mul_nonneg hLp.le (by linarith : 0≤L-1), show x/T*L^2=x*L^2/T by ring]
  change |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤ (2*B+A)*h*e
  apply H.trans
  change B*(x*L^2/T+L)+h*_ ≤ _
  have ht' := mul_le_mul_of_nonneg_left (add_le_add ht (hsmall.trans ht)) hB.le
  linarith only [ht',mul_le_mul_of_nonneg_left hsum' hh]

/-- The quantitative seven-twelfths estimate is uniform for all lengths above
the threshold, including intervals extending beyond twice the starting point. -/
theorem huxley_psi_interval_of_vinogradovKorobov (hz : VinogradovKorobovZeroFreeHypothesis)
    {a : ℝ} (ha : 1<a) :
    ∃ c>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop, ∀ h : ℝ,
      x^(7/12:ℝ)*Real.exp (huxleyIntervalCorrection a x) ≤ h →
      |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤
        C*h*Real.exp (-c*(Real.log (Real.log x))^a) := by
  obtain ⟨c,hc,C,hC,hshort⟩ := huxley_psi_interval_of_vinogradovKorobov_of_le hz ha
  obtain ⟨B,hB,d,hd,hlong⟩ := abs_psi_sub_id_le_exp
  have hlogs := Real.tendsto_log_atTop.eventually ((isLittleO_log_rpow_rpow_atTop a
    (by norm_num : (0:ℝ)<1/2)).bound (div_pos hd hc))
  refine ⟨c,hc,max C (3*B),hC.trans_le (le_max_left ..),?_⟩
  filter_upwards [hshort,hlogs,eventually_ge_atTop (2:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0] with x hs hl hx hll
  change 0≤Real.log (Real.log x) at hll
  have hx' : 0<x := by linarith
  have hL : 0≤Real.log x := Real.log_nonneg (by linarith)
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hll _),
    ←Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg _)] at hl
  have hsav : c*(Real.log (Real.log x))^a ≤ d*Real.sqrt (Real.log x) := by
    calc _ ≤ c*((d/c)*Real.sqrt (Real.log x)) := mul_le_mul_of_nonneg_left hl hc.le
         _ = _ := by field_simp
  let E := Real.exp (-c*(Real.log (Real.log x))^a)
  have he : 0<E := Real.exp_pos _
  intro h hh
  have hh0 := (mul_pos (Real.rpow_pos_of_pos hx' (7/12:ℝ)) (Real.exp_pos _)).le.trans hh
  by_cases hhx : h≤x
  · exact (hs h hh hhx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left ..) hh0) he.le)
  have hxh := le_of_not_ge hhx
  have hbound (y : ℝ) (hy : x≤y) : |Chebyshev.psi y-y| ≤ B*y*E := by
    apply (hlong y (hx.trans hy)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB.le (hx'.le.trans hy))
    apply Real.exp_le_exp.mpr
    have hh' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.log_le_log hx' hy)) hd.le
    linarith
  have htri := abs_sub_le (Chebyshev.psi (x+h)-(x+h)) 0 (Chebyshev.psi x-x)
  have hbig : |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤ 3*B*h*E := by
    rw [sub_zero,zero_sub,abs_neg] at htri
    rw [show Chebyshev.psi (x+h)-(x+h)-(Chebyshev.psi x-x) = Chebyshev.psi (x+h)-Chebyshev.psi x-h by ring] at htri
    apply (htri.trans (add_le_add (hbound _ (by linarith)) (hbound x le_rfl))).trans
    nlinarith only [mul_le_mul_of_nonneg_right hxh (mul_nonneg hB.le he.le)]
  exact hbig.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) hh0) he.le)

/-- Huxley's quantitative short-interval estimate at the seven-twelfths
threshold, with the Vinogradov–Korobov zero-free region supplied unconditionally. -/
theorem huxley_psi_interval {a : ℝ} (ha : 1<a) :
    ∃ c>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop, ∀ h : ℝ,
      x^(7/12:ℝ)*Real.exp (huxleyIntervalCorrection a x) ≤ h →
      |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤
        C*h*Real.exp (-c*(Real.log (Real.log x))^a) :=
  huxley_psi_interval_of_vinogradovKorobov RiemannZeta.vinogradovKorobov_zero_gap ha

open scoped Asymptotics in
/-- The prime number theorem on every fixed power-length interval strictly
above the Huxley threshold. -/
theorem huxley_primePi_shortInterval {θ : ℝ} (hθ : 7/12<θ) (hθ' : θ<1) :
    (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] fun x => x^θ/Real.log x :=
  huxley_primePi_shortInterval_of_superLogZeroFree RiemannZeta.superLogZeroFree hθ hθ'

end AnalyticNumberTheory.PrimeDistribution
