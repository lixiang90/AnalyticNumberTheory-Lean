import AnalyticNumberTheory.RiemannZeta.HurwitzRotatedCorrection
import AnalyticNumberTheory.RiemannZeta.HurwitzCorrectionAmplitude
import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalWaves

/-!
# Squaring the first-corrected Hurwitz approximation

Once the signed cross term with the first correction is retained, the
pointwise error is of order `(1+a^(-1/2))/x` at saddle coordinate `x`.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

theorem norm_hurwitzDirectSum_le_sqrt {a x : ℝ} (ha : 0<a) {s : ℂ} (hs : s.re=1/2) :
    ‖hurwitzDirectSum a x s‖≤(Real.sqrt a)⁻¹+2*Real.sqrt ⌊x-a⌋₊ := by
  let M := ⌊x-a⌋₊
  have hcut : Finset.Icc (0:ℕ) M=insert 0 (Finset.Icc 1 M) := by ext n;simp;omega
  unfold hurwitzDirectSum
  rw [show ⌊x-a⌋₊=M from rfl,hcut,sum_insert (by simp : 0∉Finset.Icc 1 M)]
  simp only [Nat.cast_zero,zero_add]
  apply (norm_add_le ..).trans
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha,neg_re,hs,Real.rpow_neg ha.le,←Real.sqrt_eq_rpow]
  apply add_le_add_right
  apply (norm_sum_le ..).trans
  apply le_trans _ (sum_Icc_inv_sqrt_le M)
  apply sum_le_sum;intro n hn
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  rw [←Complex.ofReal_natCast,←Complex.ofReal_add,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),neg_re,hs,
    Real.rpow_neg (by positivity),←Real.sqrt_eq_rpow]
  exact inv_anti₀ (Real.sqrt_pos.mpr hn') (Real.sqrt_le_sqrt (by linarith))

private theorem complex_square_split (p w r : ℂ) :
    |‖p+w+r‖^2-‖p‖^2-2*(conj p*w).re|≤2*‖p‖*‖r‖+(‖w‖+‖r‖)^2 := by
  have hsq (x y : ℂ) : ‖x+y‖^2=‖x‖^2+2*(conj x*y).re+‖y‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,add_re,add_im,mul_re,conj_re,conj_im];ring
  rw [add_assoc,hsq p (w+r),mul_add,add_re,
    show ‖p‖^2+2*((conj p*w).re+(conj p*r).re)+‖w+r‖^2-‖p‖^2-2*(conj p*w).re=
      2*(conj p*r).re+‖w+r‖^2 by ring]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (sq_nonneg ‖w+r‖)]
  have he := Complex.abs_re_le_norm (conj p*r)
  rw [norm_mul,Complex.norm_conj] at he
  have h := pow_le_pow_left₀ (norm_nonneg (w+r)) (norm_add_le w r) 2
  linarith only [he,h]

/-- The square of the critical-line value, including its explicit first
cross term; the error is uniform as the shift tends down to zero. -/
theorem hurwitz_corrected_square_error : ∃ C : ℝ,0<C ∧ ∀ {a t : ℝ} {N : ℕ},
    a∈Ioc (0:ℝ) 1 → 8*Real.pi≤t → ⌊hardySaddleRoot t⌋₊+1≤N →
    let x := hardySaddleRoot t
    let P := hurwitzWaveSum a N t
    let A := hurwitzCorrectionAmplitude ⌊x⌋₊ ((⌊x-a⌋₊:ℝ)+a) x
    |‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-‖P‖^2-2*(conj P*A).re|≤
      C*((Real.sqrt a)⁻¹+1)/x := by
  obtain ⟨K,hK,H⟩ := hurwitz_critical_rotated_first_correction
  obtain ⟨D,hD,J⟩ := riemannSiegelCorrection_bounded
  refine ⟨10*K+(D+K)^2,by positivity,?_⟩
  intro a t N ha ht hN x P A
  let s := (1/2:ℂ)+(t:ℂ)*I
  let E := Complex.exp ((hardyPhase t:ℂ)*I)
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s
  let R := E*Z-P-A
  have hp : 0<t := (by positivity : 0<8*Real.pi).trans_le ht
  have hx : 2≤x := Real.le_sqrt_of_sq_le ((le_div_iff₀ (by positivity : 0<2*Real.pi)).mpr (by linarith))
  have hx' : 0<x := by linarith
  have hxt : x^2=t/(2*Real.pi) := Real.sq_sqrt (by positivity)
  have htx : t=2*Real.pi*x^2 := by rw [hxt];field_simp
  have hσ : s.re=1/2 := by simp [s]
  have hE : ‖E‖=1 := Complex.norm_exp_ofReal_mul_I _
  have he : P=E*hurwitzDirectSum a x s+conj E*hurwitzReciprocalPoly a ⌊x⌋₊ s :=
    hurwitzWaveSum_eq ha hp.le (by linarith : 1≤x) hN
  have hA : E*hurwitzFirstCorrection a x s=A := rotated_hurwitzFirstCorrection hx' htx
  have hR := H ha hx htx
  change ‖E*Z-_-E*hurwitzFirstCorrection a x s‖≤_ at hR
  rw [←he,hA] at hR
  change ‖R‖≤K*x^(-(3/2:ℝ)) at hR
  have hP : ‖P‖≤(Real.sqrt a)⁻¹+4*Real.sqrt x := by
    rw [he];apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul,Complex.norm_conj,hE,one_mul,one_mul]
    have h := norm_hurwitzDirectSum_le_sqrt (x:=x) ha.1 hσ
    have h' := norm_hurwitzReciprocalPoly_le_sqrt hσ a ⌊x⌋₊
    have h₁ := Real.sqrt_le_sqrt (Nat.floor_le (show 0≤x-a by linarith [ha.2]))
    have h₂ := Real.sqrt_le_sqrt (show x-a≤x by linarith [ha.1])
    have h₃ := Real.sqrt_le_sqrt (Nat.floor_le hx'.le)
    linarith only [h,h',h₁,h₂,h₃]
  have hW : ‖A‖≤D*x^(-(1/2:ℝ)) := by
    rw [←hA,norm_mul,hE,one_mul,norm_hurwitzFirstCorrection hx',hσ,mul_comm D]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply J;obtain ⟨hl,hl'⟩ := hurwitzSaddleFraction_mem (show a≤x by linarith [ha.2])
    exact ⟨by linarith [Nat.floor_le hx'.le],by linarith [Nat.lt_floor_add_one x]⟩
  have hlow := Real.rpow_le_rpow_of_exponent_le (show 1≤x by linarith) (by norm_num : -(3/2:ℝ)≤ -(1/2))
  have hsl : ‖A‖+‖R‖≤(D+K)*x^(-(1/2:ℝ)) := by
    linarith only [hW,hR,mul_le_mul_of_nonneg_left hlow hK.le]
  have hsq := pow_le_pow_left₀ (add_nonneg (norm_nonneg A) (norm_nonneg R)) hsl 2
  rw [mul_pow,←Real.rpow_natCast (x^(-(1/2:ℝ))) 2,←Real.rpow_mul hx'.le,
    show -(1/2:ℝ)*(2:ℕ) = -1 by norm_num,Real.rpow_neg_one] at hsq
  have hcross := mul_le_mul hP hR (norm_nonneg _) (by positivity)
  have hpow : Real.sqrt x*x^(-(3/2:ℝ))=x⁻¹ := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hx',show (1/2:ℝ)+ -(3/2)= -1 by norm_num,Real.rpow_neg_one]
  have hpow' : x^(-(3/2:ℝ))≤x⁻¹ := by
    rw [←Real.rpow_neg_one];exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have ha' : 0≤(Real.sqrt a)⁻¹ := by positivity
  have H' := complex_square_split P A R
  rw [show P+A+R=E*Z by dsimp [R];ring,norm_mul,hE,one_mul] at H'
  apply H'.trans
  rw [show ((Real.sqrt a)⁻¹+4*Real.sqrt x)*(K*x^(-(3/2:ℝ)))=
    ((Real.sqrt a)⁻¹*K)*x^(-(3/2:ℝ))+4*K*(Real.sqrt x*x^(-(3/2:ℝ))) by ring,hpow] at hcross
  have h' := mul_le_mul_of_nonneg_left hpow' (mul_nonneg ha' hK.le)
  rw [div_eq_mul_inv]
  nlinarith only [hcross,h',hsq,mul_nonneg (mul_nonneg ha' (inv_nonneg.mpr hx'.le)) (add_nonneg (sq_nonneg (D+K)) (show 0≤8*K by positivity)),
      mul_nonneg hK.le (inv_nonneg.mpr hx'.le)]

end AnalyticNumberTheory.RiemannZeta
