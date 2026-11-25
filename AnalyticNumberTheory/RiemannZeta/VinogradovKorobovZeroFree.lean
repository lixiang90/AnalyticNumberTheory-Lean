import AnalyticNumberTheory.RiemannZeta.VinogradovKorobovGrowth
import AnalyticNumberTheory.RiemannZeta.LittlewoodZeroFreeRegion
import AnalyticNumberTheory.PrimeDistribution.VinogradovKorobovApplications

/-!
# The Vinogradov–Korobov zero-free region from strip growth

Landau's local formula is applied on disks of radius
`(log log t / log t)^(2/3)`. The three-halves growth estimate confines
the logarithm of the disk bound to a constant times `log log t`.
-/
noncomputable section
open Real Filter Complex Metric Set
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.RiemannZeta

private theorem disk_scales {L l : ℝ} (hL : 0<L) (hl : 0<l) :
    (l/L)^(2/3:ℝ)*(L^(2/3:ℝ)*l^(1/3:ℝ))=l ∧
    ((l/L)^(2/3:ℝ))^(3/2:ℝ)*L=l := by
  constructor
  · rw [Real.div_rpow hl.le hL.le,div_mul_eq_mul_div,←mul_assoc,mul_right_comm,
      mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hL _).ne',←Real.rpow_add hl]
    norm_num
  · rw [←Real.rpow_mul (div_nonneg hl.le hL.le),show (2/3:ℝ)*(3/2)=1 by norm_num,
      Real.rpow_one,div_mul_cancel₀ _ hL.ne']

/-- The three-halves zeta growth estimate implies the classical
Vinogradov–Korobov zero-free width. -/
theorem vinogradovKorobov_zero_free_of_stripGrowth (H : VinogradovKorobovStripGrowth) :
    ∃ d>(0:ℝ), ∀ᶠ T : ℝ in atTop, ∀ σ t : ℝ, T≤|t| →
      1-d/vinogradovKorobovDenom |t|≤σ → riemannZeta ((σ:ℂ)+t*I)≠0 := by
  obtain ⟨K,hK,B,hB,hgrowth⟩ := H
  obtain ⟨C,hC,hpole⟩ := neg_logDeriv_riemannZeta_one_add_le
  let A := 5+2*K
  let b := 1/(200*A)
  have hA : 0<A := by dsimp [A]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hAb : 20*A*b=1/10 := by dsimp only [b]; field_simp; ring
  have hlittle := Real.tendsto_log_atTop.eventually ((isLittleO_log_rpow_atTop
    (by norm_num : (0:ℝ)<1)).bound (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<1/4) (3/2:ℝ)))
  have hevent : ∀ᶠ u : ℝ in atTop, ∀ σ t : ℝ, |t|=u → 1-(b/10)/vinogradovKorobovDenom u≤σ →
      riemannZeta ((σ:ℂ)+t*I)≠0 := by
    filter_upwards [eventually_ge_atTop (32:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (max 4 (max B (2/b))),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 (4*b)),
      tendsto_vinogradovKorobovDenom.eventually_ge_atTop (max (4*b) (30*C*b)),hlittle]
      with u hu hlarge hl' hD' hsmall
    let L := Real.log u
    let l := Real.log L
    let D := vinogradovKorobovDenom u
    let R := (l/L)^(2/3:ℝ)
    let h := b/D
    let G := Real.exp ((3+2*K)*l)
    let M := Real.exp (A*l)
    change max 4 (max B (2/b))≤L at hlarge
    change max 1 (4*b)≤l at hl'
    change max (4*b) (30*C*b)≤D at hD'
    have hL4 := (le_max_left ..).trans hlarge
    have hLB := (le_max_left ..).trans ((le_max_right ..).trans hlarge)
    have hLb := (le_max_right ..).trans ((le_max_right ..).trans hlarge)
    have hl1 := (le_max_left ..).trans hl'
    have hlb := (le_max_right ..).trans hl'
    have hDb := (le_max_left ..).trans hD'
    have hDC := (le_max_right ..).trans hD'
    have hL : 0<L := by linarith
    have hl : 0<l := by linarith
    have hD : 0<D := by linarith
    have hR : 0<R := Real.rpow_pos_of_pos (div_pos hl hL) _
    have hh : 0<h := div_pos hb hD
    have hu0 : 0<u := by linarith
    have hRD : R*D=l := (disk_scales hL hl).1
    have hRL : R^(3/2:ℝ)*L=l := (disk_scales hL hl).2
    have hR' : R≤1/4 := by
      change ‖l‖≤(1/4:ℝ)^(3/2:ℝ)*‖L^(1:ℝ)‖ at hsmall
      rw [Real.rpow_one,Real.norm_of_nonneg hl.le,Real.norm_of_nonneg hL.le] at hsmall
      apply (Real.rpow_le_rpow (div_nonneg hl.le hL.le) ((div_le_iff₀ hL).mpr hsmall) (by norm_num : (0:ℝ)≤2/3)).trans_eq
      rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤1/4),show (3/2:ℝ)*(2/3)=1 by norm_num,Real.rpow_one]
    have hh' : h≤1/4 := (div_le_iff₀ hD).mpr (by linarith)
    have hfrac : h≤R/4 := (div_le_iff₀ hD).mpr (by linarith)
    have hDL : D≤L := by
      have hll : l≤L := (Real.log_le_sub_one_of_pos hL).trans (by linarith)
      apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hl.le hll (by norm_num : (0:ℝ)≤1/3))
        (Real.rpow_nonneg hL.le (2/3:ℝ))).trans_eq
      rw [←Real.rpow_add hL,show (2/3:ℝ)+1/3=1 by norm_num,Real.rpow_one]
    have hinv : 2/h≤L^2 := by
      dsimp only [h]; rw [div_div_eq_mul_div,div_le_iff₀ hb]
      have hbl := (div_le_iff₀ hb).mp hLb
      nlinarith only [hDL,mul_le_mul_of_nonneg_right hbl hL.le]
    have hstrip (z : ℂ) (hz : 1-R≤z.re) (_ : z.re≤2)
        (ht₁ : 3*u/4≤|z.im|) (ht₂ : |z.im|≤3*(3*u/4)) : ‖riemannZeta z‖≤G := by
      have htw : 16≤|z.im| := by linarith
      have hu2 : |z.im|≤u^2 := by nlinarith only [ht₂,hu,mul_nonneg hu0.le (by linarith : 0≤u-3)]
      have hlog := Real.log_le_log (by linarith : 0 < |z.im|) hu2
      rw [Real.log_pow] at hlog
      change Real.log |z.im|≤(2:ℝ)*L at hlog
      apply (hgrowth z R hR.le hR' hz htw).trans
      have hpow : K*R^(3/2:ℝ)*Real.log |z.im|≤2*K*l := by
        nlinarith only [mul_le_mul_of_nonneg_left hlog (mul_nonneg hK.le (Real.rpow_nonneg hR.le (3/2:ℝ))),
          congrArg (fun v : ℝ => K*v) hRL]
      have hp : B*(1+Real.log |z.im|)≤L^3 := by
        have hlin : 1+Real.log |z.im|≤L^2 := by nlinarith [sq_nonneg (L-2)]
        nlinarith only [mul_le_mul hLB hlin (by linarith [Real.log_nonneg (by linarith : 1≤|z.im|)]) hL.le]
      apply (mul_le_mul hp (Real.exp_le_exp.mpr hpow) (Real.exp_pos _).le (by positivity)).trans_eq
      dsimp only [G]
      rw [show (3+2*K)*l=3*l+2*K*l by ring,Real.exp_add]
      congr 1; simpa only [l,Nat.cast_ofNat,Real.exp_log hL] using (Real.exp_nat_mul l 3).symm
    intro σ t ht hσ
    by_cases hβ : 1≤σ
    · apply riemannZeta_ne_zero_of_one_le_re; simpa using hβ
    intro hzero
    have hdisc : ∀ y : ℝ, y=t ∨ y=2*t →
        AnalyticOnNhd ℂ riemannZeta (closedBall (zetaZeroDiskCenter h y) R) ∧
        riemannZeta (zetaZeroDiskCenter h y)≠0 ∧ ∀ w∈sphere (zetaZeroDiskCenter h y) R,
          ‖riemannZeta w/riemannZeta (zetaZeroDiskCenter h y)‖≤M := by
      intro y hy
      have hy' : u≤|y| ∧ |y|≤2*u := by
        rcases hy with rfl|rfl
        · rw [ht]; constructor <;> linarith
        · rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),ht]; constructor <;> linarith
      obtain ⟨ha,hn,hs⟩ := zeta_disk_bound_of_strip_norm hR' hh hh' (by linarith) hy'.1 hy'.2 hstrip
      refine ⟨ha,hn,fun w hw => ((hs w hw).trans (mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le)).trans_eq ?_⟩
      dsimp only [G,M,A]
      rw [show (5+2*K)*l=(3+2*K)*l+(2:ℕ)*l by push_cast; ring,Real.exp_add,Real.exp_nat_mul,Real.exp_log hL]
    have hgap : (b/10)/vinogradovKorobovDenom u=h/10 := by dsimp [h,D]; ring
    rw [hgap] at hσ
    have hden : 1+h-σ≤11*h/10 := by linarith
    have hdif : 1+h-σ≤R/2 := by linarith
    have hz := zeta_local_zero_inequality hh hR (lt_of_not_ge hβ) hdif hzero hdisc (hpole hh (by linarith))
    have hp : 3*C*h≤1/10 := by
      dsimp only [h]; rw [←mul_div_assoc,div_le_iff₀ hD]; linarith
    have hk : (20/R*Real.log M)*h=1/10 := by
      dsimp only [M,h]; rw [Real.log_exp,←hRD]; field_simp; nlinarith only [hAb]
    have hpos : 0<1+h-σ := by linarith
    have hsmall' : (40/11:ℝ)/h≤4/(1+h-σ) := by
      apply (div_le_div₀ (by norm_num : (0:ℝ)≤4) le_rfl hpos hden).trans_eq'; ring
    have hh'' := mul_le_mul_of_nonneg_right (hsmall'.trans hz) hh.le
    rw [add_mul,add_mul,hk,div_mul_cancel₀ _ hh.ne',div_mul_cancel₀ _ hh.ne'] at hh''
    linarith
  obtain ⟨T,hT⟩ := eventually_atTop.mp hevent
  refine ⟨b/10,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop T] with T' hT' σ t ht hσ
  exact hT |t| (hT'.trans ht) σ t rfl hσ

/-- Cubic cancellation for logarithmic exponential sums gives the classical
Vinogradov–Korobov zero-free region for the Riemann zeta function. -/
theorem vinogradovKorobov_zero_free_of_blocks (H : VinogradovKorobovBlockCancellation) :
    VinogradovKorobovZeroFreeHypothesis := by
  obtain ⟨d,hd,h⟩ := vinogradovKorobov_zero_free_of_stripGrowth (vinogradovKorobov_growth_of_blocks H)
  exact vinogradovKorobov_of_nonvanishing hd h

end AnalyticNumberTheory.RiemannZeta
