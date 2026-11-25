import AnalyticNumberTheory.DirichletLFunctions.PeriodicReciprocalPolynomial
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveMovingWaves

/-!
# Two critical-line polynomials for a periodic coefficient sequence

The cutoffs agree at conductor-scaled saddle height. The two coefficient
sequences are the original periodic weights and their unitary finite
Fourier transform.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

def periodicWaveWeight {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (i : Bool×ℕ) :=
  if i.1 then periodicDualWeight Φ i.2 else Φ i.2

def periodicCriticalPoly {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (N : ℕ) (t : ℝ) :=
  let R := (Circle.exp (primitiveHardyPhase q t):ℂ)
  let s := (1/2:ℂ)+t*I
  R*dirichletPoly (fun n : ℕ => Φ n) N s+conj R*periodicReciprocalPoly Φ N s

/-- Conductor-balanced sharp approximation for every bounded sequence. -/
theorem periodic_critical_polynomial_error {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (hΦ : ∀r,‖Φ r‖≤1) :
    ∃ C : ℝ,0<C ∧ ∀{t : ℝ},8*Real.pi*q≤t →
    |‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖-‖periodicCriticalPoly Φ (primitiveCriticalLength q t) t‖|≤
      C*t^(-(1/4:ℝ)) := by
  let J := 8+2*Real.Gamma (1/2)
  have hJ : 0<J := by dsimp [J];have := Real.Gamma_pos_of_pos (by norm_num : 0<(1/2:ℝ));positivity
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq₁ : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  let C := Real.sqrt q*(604+J)
  refine ⟨C*(2*Real.pi*q)^(1/4:ℝ),by dsimp [C];positivity,?_⟩
  intro t ht
  have ht' : 0<t := (by positivity : 0<8*Real.pi*q).trans_le ht
  have hqt : 2≤t := by nlinarith [mul_le_mul_of_nonneg_left hq₁ (show 0≤8*Real.pi by positivity),Real.pi_gt_three]
  let x := Real.sqrt (t/(2*Real.pi*q))
  have hx : 2≤x := Real.le_sqrt_of_sq_le ((le_div_iff₀ (by positivity : 0<2*Real.pi*q)).mpr (by linarith))
  have hx' : 0<x := by linarith
  have Hx : x^2=t/(2*Real.pi*q) := Real.sq_sqrt (by positivity)
  have ht₂ : t=2*Real.pi*(q:ℝ)*x^2 := by rw [Hx];field_simp
  have hlen : Real.sqrt ((q:ℝ)*t/(2*Real.pi))=(q:ℝ)*x := by
    rw [←Real.sqrt_sq (mul_nonneg hq.le hx'.le)];congr 1;rw [mul_pow,Hx];field_simp
  let y := (q:ℝ)*x
  let s := (1/2:ℂ)+t*I
  let N := ⌊y⌋₊
  let P := dirichletPoly (fun n : ℕ => Φ n) N s
  let B := periodicReciprocalPoly Φ N s
  let R := (Circle.exp (primitiveHardyPhase q t):ℂ)
  let S := periodicDualSum Φ y s
  let Z := ZMod.LFunction Φ s
  have hσ : s.re=1/2 := by simp [s]
  have h := periodicLFunction_logFree_sharp_afe Φ hΦ (s:=s) hx (le_mul_of_one_le_left hx'.le hq₁)
    (by rw [hσ];constructor <;>norm_num) (by rw [show s.im=t by simp [s],abs_of_pos ht',ht₂];ring)
  rw [hσ,show (1:ℝ)-1/2=1/2 by norm_num,←Real.sqrt_eq_rpow] at h
  change ‖Z-P-S‖≤Real.sqrt q*(604*x^(-(1/2:ℝ))) at h
  have H := periodic_reciprocal_rotated_error Φ hΦ y hqt
  change ‖R*S-conj R*B‖≤Real.sqrt q*(J*N/t) at H
  have hN : (N:ℝ)≤(q:ℝ)*x := Nat.floor_le (mul_nonneg hq.le hx'.le)
  have htx : (q:ℝ)*x^2≤t := by
    rw [ht₂];nlinarith [mul_le_mul_of_nonneg_right (show 1≤2*Real.pi by linarith [Real.pi_gt_three]) (mul_nonneg hq.le (sq_nonneg x))]
  have hfrac : (N:ℝ)/t≤x^(-(1/2:ℝ)) := by
    calc _ ≤ ((q:ℝ)*x)/(q*x^2) := div_le_div₀ (by positivity) hN (by positivity) htx
         _ = x^(-(1:ℝ)) := by rw [Real.rpow_neg hx'.le,Real.rpow_one];field_simp
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hG : ‖R*S-conj R*B‖≤Real.sqrt q*(J*x^(-(1/2:ℝ))) := by
    rw [mul_div_assoc] at H
    exact H.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfrac hJ.le) (Real.sqrt_nonneg _))
  have hR : ‖R‖=1 := Circle.norm_coe _
  have hi : primitiveCriticalLength q t=N := by rw [primitiveCriticalLength,hlen]
  rw [hi]
  change |‖Z‖-‖R*P+conj R*B‖|≤_
  have He := abs_norm_sub_norm_le (R*Z) (R*P+conj R*B)
  rw [norm_mul,hR,one_mul] at He
  apply He.trans
  rw [show R*Z-(R*P+conj R*B)=R*(Z-P-S)+(R*S-conj R*B) by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,hR,one_mul]
  apply (add_le_add h hG).trans_eq
  dsimp only [C,x]
  rw [Real.sqrt_eq_rpow (t/(2*Real.pi*q)),←Real.rpow_mul (by positivity : 0≤t/(2*Real.pi*q)),
    show (1/2:ℝ)*(-(1/2))= -(1/4) by norm_num,Real.div_rpow ht'.le (by positivity),Real.rpow_neg (by positivity : 0≤2*Real.pi*q),div_inv_eq_mul]
  ring

private theorem cutoff_sums {E : Type*} [AddCommMonoid E] {q : ℕ} [NeZero q] {t : ℝ} (ht : 0≤t)
    {N : ℕ} (hN : primitiveCriticalLength q t≤N) (f : Bool×ℕ→E) :
    (∑i∈scaledWaveIndex N,if scaledHardyEntry (Real.sqrt q) i.2≤t then f i else 0)=
      (∑n∈Finset.Icc 1 (primitiveCriticalLength q t),f (false,n))+
      ∑n∈Finset.Icc 1 (primitiveCriticalLength q t),f (true,n) := by
  rw [scaledWaveIndex,sum_product (f:=fun i => if scaledHardyEntry (Real.sqrt q) i.2≤t then f i else 0),Fintype.sum_bool]
  have H : ((Finset.Icc 1 N).filter (fun n=>scaledHardyEntry (Real.sqrt q) n≤t))=Finset.Icc 1 (primitiveCriticalLength q t) := by
    ext n;simp only [mem_filter,Finset.mem_Icc,scaledHardyEntry_iff ht];omega
  simp_rw [←sum_filter,H];apply add_comm

theorem weightedHardyPolynomial_periodic {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) {t : ℝ} (ht : 0≤t)
    {N : ℕ} (hN : primitiveCriticalLength q t≤N) :
    weightedHardyPolynomial (Real.sqrt q) (periodicWaveWeight Φ) N t=
      periodicCriticalPoly Φ (primitiveCriticalLength q t) t := by
  let w := periodicWaveWeight Φ
  let s := (1/2:ℂ)+t*I
  let R := (Circle.exp (primitiveHardyPhase q t):ℂ)
  let M := primitiveCriticalLength q t
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hur (n : ℕ) (hn : 0<n) :
      scaledHardyAngle (Real.sqrt q) n t=primitiveHardyPhase q t-t*Real.log n := by
    rw [scaledHardyAngle,primitiveHardyPhase,Real.log_div (Nat.cast_pos.mpr hn).ne' (Real.sqrt_pos.mpr hq).ne',Real.log_sqrt hq.le];ring
  have helem (n : ℕ) (hn : 0<n) : (((Real.sqrt n)⁻¹:ℝ):ℂ)*Complex.exp ((scaledHardyAngle (Real.sqrt q) n t:ℂ)*I)=R*(n:ℂ)^(-s) := by
    simp only [R,Circle.coe_exp]
    rw [←Complex.ofReal_natCast,critical_monomial_eq (Nat.cast_pos.mpr hn),hur n hn]
    push_cast;rw [sub_mul,Complex.exp_sub,div_eq_mul_inv,←Complex.exp_neg]
    rw [show -(↑t*Complex.log (n:ℂ)*I)=I*(-Complex.log (n:ℂ))*↑t by ring];ring
  have hd (n : ℕ) (hn : 0<n) : weightedHardyWave (Real.sqrt q) w (false,n) t=R*(Φ n*(n:ℂ)^(-s)) := by
    simp only [weightedHardyWave,w,periodicWaveWeight,Bool.false_eq_true,ite_false]
    rw [mul_assoc,helem n hn];ring
  have hr (n : ℕ) (hn : 0<n) : weightedHardyWave (Real.sqrt q) w (true,n) t=
      conj R*(periodicDualWeight Φ n*(n:ℂ)^(s-1)) := by
    have hp : (n:ℂ)^(s-1)=conj ((n:ℂ)^(-s)) := by
      rw [show s-1=conj (-s) by dsimp [s];simp [Complex.conj_ofNat];ring,←Complex.ofReal_natCast,Complex.cpow_conj]
      · simp
      · rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)];exact Real.pi_ne_zero.symm
    let v := scaledHardyAngle (Real.sqrt q) n t
    have hc : Complex.exp (((-v:ℝ):ℂ)*I)=conj (Complex.exp ((v:ℂ)*I)) := by
      rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I];push_cast;ring_nf
    change (periodicDualWeight Φ n*(((Real.sqrt n)⁻¹:ℝ):ℂ))*Complex.exp (((-v:ℝ):ℂ)*I)=_
    rw [hp,hc,mul_assoc,show (((Real.sqrt n)⁻¹:ℝ):ℂ)=conj (((Real.sqrt n)⁻¹:ℝ):ℂ) from (Complex.conj_ofReal _).symm,←map_mul]
    rw [show (((Real.sqrt n)⁻¹:ℝ):ℂ)*Complex.exp ((v:ℂ)*I)=R*(n:ℂ)^(-s) from helem n hn,map_mul];ring
  have he (K : ℕ) : ∑n∈Finset.Icc 1 K,periodicDualWeight Φ n*(n:ℂ)^(s-1)=periodicReciprocalPoly Φ K s := by
    induction K with
    | zero => simp [periodicReciprocalPoly]
    | succ K h => rw [sum_Icc_succ_top (by omega),h,periodicReciprocalPoly,periodicReciprocalPoly,sum_range_succ];push_cast;rfl
  change (∑i∈scaledWaveIndex N,if scaledHardyEntry (Real.sqrt q) i.2≤t then weightedHardyWave (Real.sqrt q) w i t else 0)=_
  rw [cutoff_sums ht hN,periodicCriticalPoly,dirichletPoly]
  simp_rw [mul_sum]
  apply congrArg₂ (·+·)
  · apply sum_congr rfl;intro n hn;exact hd n (Finset.mem_Icc.mp hn).1
  · rw [←he,mul_sum];apply sum_congr rfl;intro n hn;exact hr n (Finset.mem_Icc.mp hn).1

def periodicCriticalDiagonal {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) (t : ℝ) :=
  ∑n∈Finset.Icc 1 (primitiveCriticalLength q t),(‖Φ n‖^2+‖periodicDualWeight Φ n‖^2)/(n:ℝ)

theorem weightedHardyDiagonal_periodic {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) {t : ℝ} (ht : 0≤t)
    {N : ℕ} (hN : primitiveCriticalLength q t≤N) :
    weightedHardyDiagonal (Real.sqrt q) (periodicWaveWeight Φ) N t=periodicCriticalDiagonal Φ t := by
  have h (i : Bool×ℕ) : ‖enteredWave (scaledHardyEntry (Real.sqrt q) i.2) (weightedHardyWave (Real.sqrt q) (periodicWaveWeight Φ) i) t‖^2=
      if scaledHardyEntry (Real.sqrt q) i.2≤t then ‖periodicWaveWeight Φ i‖^2/(i.2:ℝ) else 0 := by
    change ‖if scaledHardyEntry (Real.sqrt q) i.2≤t then _ else 0‖^2=_;split_ifs
    · rw [norm_weightedHardyWave,mul_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg _),div_eq_mul_inv]
    · simp
  unfold weightedHardyDiagonal;simp_rw [h]
  rw [cutoff_sums ht hN,periodicCriticalDiagonal,←sum_add_distrib]
  apply sum_congr rfl;intro n _;dsimp [periodicWaveWeight];ring

end AnalyticNumberTheory.DirichletLFunctions
