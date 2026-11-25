import AnalyticNumberTheory.DirichletLFunctions.PeriodicFourierEnergy
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveHardyPhase
import AnalyticNumberTheory.RiemannZeta.HurwitzRotatedCorrection

/-!
# Positive-height reciprocal polynomial for arbitrary periodic coefficients

After the conductor-dependent rotation, the coefficients in the reciprocal
polynomial are the normalized discrete Fourier transform. The estimate
holds for any sharp reciprocal cutoff and includes imprimitive characters.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

def periodicReciprocalPoly {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (N : ℕ) (s : ℂ) :=
  ∑m∈range N,periodicDualWeight Φ ((m+1:ℕ):ZMod q)*((m:ℂ)+1)^(s-1)

private theorem shifted_dual_error (a y : ℝ) {t : ℝ} (ht : 2≤t) :
    let E := (Circle.exp (hardyPhase t):ℂ)
    let s := (1/2:ℂ)+t*I
    ‖E*hurwitzDualSum a y s-conj E*hurwitzReciprocalPoly a ⌊y⌋₊ s‖≤
      (8+2*Real.Gamma (1/2))*(⌊y⌋₊:ℝ)/t := by
  intro E s
  let N := ⌊y⌋₊
  let G := riemannDualGamma s
  let B := hurwitzReciprocalPoly a N s
  let S := hurwitzDualSum a y s
  have hp : 0<t := by linarith
  have hσ : s.re=1/2 := by simp [s]
  have hΓ := Real.Gamma_pos_of_pos (by norm_num : 0<(1/2:ℝ))
  have he : Real.exp (-(Real.pi/2)*t)≤1/t := by
    rw [neg_mul,Real.exp_neg,one_div];apply inv_anti₀ hp
    linarith only [Real.add_one_le_exp (Real.pi/2*t),mul_le_mul_of_nonneg_right (show 1≤Real.pi/2 by linarith [Real.pi_gt_three]) hp.le]
  have hneg (u : ℝ) : ‖hurwitzNegativeDual s u N‖≤N*Real.Gamma (1/2)/t := by
    have h := norm_hurwitzNegativeDual_critical hσ u N
    rw [show s.im=t by simp [s]] at h
    exact h.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  have hS : ‖S-G*B‖≤2*(N*Real.Gamma (1/2)/t) := by
    rw [show S-G*B=hurwitzNegativeDual s a N-hurwitzNegativeDual s (-a) N from hurwitzDualSum_sub_gamma ..]
    linarith only [norm_sub_le (hurwitzNegativeDual s a N) (hurwitzNegativeDual s (-a) N),hneg a,hneg (-a)]
  change ‖E*S-conj E*B‖≤_
  rw [show E*S-conj E*B=E*(S-G*B)+(E*G-conj E)*B by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul,show ‖E‖=1 from Circle.norm_coe _,one_mul]
  apply (add_le_add hS (mul_le_mul (hurwitz_rotated_gamma_error ht) (norm_hurwitzReciprocalPoly_le hσ a N)
    (norm_nonneg _) (by positivity))).trans_eq
  dsimp only [N];ring

/-- At every positive height at least two, with all periods and truncation
lengths explicit, replace the complete reciprocal gamma sum by one polynomial. -/
theorem periodic_reciprocal_rotated_error {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (hΦ : ∀r,‖Φ r‖≤1)
    (y : ℝ) {t : ℝ} (ht : 2≤t) :
    let R := (Circle.exp (primitiveHardyPhase q t):ℂ)
    let s := (1/2:ℂ)+t*I
    ‖R*periodicDualSum Φ y s-conj R*periodicReciprocalPoly Φ ⌊y⌋₊ s‖≤
      Real.sqrt q*((8+2*Real.Gamma (1/2))*(⌊y⌋₊:ℝ)/t) := by
  intro R s
  let A := (Circle.exp (hardyPhase t):ℂ)
  let V := (Circle.exp (t*Real.log q/2):ℂ)
  let z := fun r : ℕ => Φ ((r+1:ℕ):ZMod q)
  let a := fun r : ℕ => ((r+1:ℕ):ℝ)/q
  let N := ⌊y⌋₊
  let S := fun r => hurwitzDualSum (a r) y s
  let B := fun r => hurwitzReciprocalPoly (a r) N s
  let d : ℂ := ((Real.sqrt q)⁻¹:ℝ)
  let c := (8+2*Real.Gamma (1/2))*(N:ℝ)/t
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hV : ‖V‖=1 := Circle.norm_coe _
  have hd : ‖d‖=(Real.sqrt q)⁻¹ := by change ‖((_:ℝ):ℂ)‖=_;rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hrot : R=A*V := by dsimp only [R,A,V,primitiveHardyPhase];rw [Circle.exp_add,Circle.coe_mul]
  have hQ : (q:ℂ)^(-s)=d*(conj V*conj V) := by
    rw [←Complex.ofReal_natCast,critical_monomial_eq hq]
    dsimp only [V,d,Circle.coe_exp];rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,←Complex.exp_add]
    congr 2;push_cast;ring
  have hc : V*(conj V*conj V)=conj V := by
    rw [←mul_assoc,Complex.mul_conj,←Complex.sq_norm,hV];norm_num
  have hB : periodicReciprocalPoly Φ N s=d*∑r∈range q,z r*B r := by
    have term (m : ℕ) : periodicDualWeight Φ ((m+1:ℕ):ZMod q)*((m:ℂ)+1)^(s-1)=
        d*∑r∈range q,z r*(hurwitzShift (a r) (hurwitzOmega m)*((m:ℂ)+1)^(s-1)) := by
      rw [periodicDualWeight,←periodicFourierCoeff_eq_dft,periodicFourierCoeff,mul_assoc,sum_mul]
      apply congrArg (d*·);apply sum_congr rfl;intro r _;dsimp only [a,z];ring
    rw [periodicReciprocalPoly];simp_rw [term];rw [←mul_sum,sum_comm]
    apply congrArg (d*·);apply sum_congr rfl;intro r _
    dsimp only [B,hurwitzReciprocalPoly];rw [mul_sum]
  have he : R*periodicDualSum Φ y s-conj R*periodicReciprocalPoly Φ N s=
      (d*conj V)*(∑r∈range q,z r*(A*S r-conj A*B r)) := by
    rw [periodic_dualSum,hB,hrot,map_mul,hQ]
    change A*V*(d*(conj V*conj V)*∑r∈range q,z r*S r)-(conj A*conj V)*(d*∑r∈range q,z r*B r)=_
    rw [show ∀ X : ℂ,A*V*(d*(conj V*conj V)*X)=(V*(conj V*conj V))*(A*d*X) by intro;ring,hc]
    simp_rw [mul_sub,sum_sub_distrib]
    rw [show (∑r∈range q,z r*(A*S r))=A*∑r∈range q,z r*S r by rw [mul_sum];apply sum_congr rfl;intro r _;ring,
      show (∑r∈range q,z r*(conj A*B r))=conj A*∑r∈range q,z r*B r by rw [mul_sum];apply sum_congr rfl;intro r _;ring]
    ring
  rw [he,norm_mul,norm_mul,hd,Complex.norm_conj,hV,mul_one]
  have hsum : ‖∑r∈range q,z r*(A*S r-conj A*B r)‖≤(q:ℝ)*c := by
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑_r∈range q,c := by
              apply sum_le_sum;intro r _
              rw [norm_mul]
              exact (mul_le_mul (hΦ _) (shifted_dual_error (a r) y ht) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
         _ = _ := by simp
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
  change (Real.sqrt q)⁻¹*((q:ℝ)*c)=Real.sqrt q*c
  rw [←mul_assoc];congr 1
  rw [←div_eq_inv_mul,div_eq_iff (Real.sqrt_pos.mpr hq).ne',Real.mul_self_sqrt hq.le]

end AnalyticNumberTheory.DirichletLFunctions
