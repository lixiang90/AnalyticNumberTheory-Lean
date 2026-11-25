import AnalyticNumberTheory.DirichletLFunctions.PrimitiveHardyPhase
import AnalyticNumberTheory.DirichletLFunctions.PeriodicLogFreeApproximation

/-!
# A symmetric critical-line polynomial for a primitive character

The two cutoffs in the primitive approximate functional equation agree
after choosing y=qx. The conductor-dependent phase rotates the resulting
polynomial into itself plus a constant unit times its conjugate.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

def primitiveCriticalLength (q : ℕ) (t : ℝ) := ⌊Real.sqrt ((q:ℝ)*t/(2*Real.pi))⌋₊

def primitiveRotatedPoly {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) :=
  (Circle.exp (primitiveHardyPhase q t):ℂ)*dirichletPoly (fun n : ℕ => χ n) N ((1/2:ℂ)+t*I)

def primitiveCriticalPolynomial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) :=
  primitiveRotatedPoly χ N t+primitiveHardyMultiplier χ*conj (primitiveRotatedPoly χ N t)

private theorem conjugate_polynomial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) :
    let s := (1/2:ℂ)+t*I
    (∑m∈range N,conj (χ ((m+1:ℕ):ZMod q))*((m:ℂ)+1)^(s-1))=conj (dirichletPoly (fun n : ℕ => χ n) N s) := by
  intro s
  rw [dirichletPoly,map_sum]
  have he (m : ℕ) : conj (χ ((m+1:ℕ):ZMod q))*((m:ℂ)+1)^(s-1)=
      conj (χ ((m+1:ℕ):ZMod q)*((m+1:ℕ):ℂ)^(-s)) := by
    rw [map_mul,show s-1=conj (-s) by dsimp [s];simp [Complex.conj_ofNat];ring,
      ←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,Complex.cpow_conj]
    · push_cast;simp
    · rw [Complex.arg_ofReal_of_nonneg (by positivity)];exact Real.pi_ne_zero.symm
  simp_rw [he]
  induction N with
  | zero => simp
  | succ N h => rw [sum_range_succ,sum_Icc_succ_top (by omega),h]

private theorem norm_polynomial_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) :
    ‖dirichletPoly (fun n : ℕ => χ n) N ((1/2:ℂ)+t*I)‖≤N := by
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑_n∈Finset.Icc 1 N,(1:ℝ) := by
            apply sum_le_sum;intro n hn
            rw [norm_mul,Complex.norm_natCast_cpow_of_pos (Finset.mem_Icc.mp hn).1,neg_re]
            apply mul_le_one₀ (χ.norm_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Finset.mem_Icc.mp hn).1);simp
       _ = _ := by simp

/-- Positive-height approximation by a symmetric polynomial of length
floor(sqrt(qt/(2π))), with a fourth-root error for each conductor. -/
theorem primitive_critical_polynomial_error {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ∃ C : ℝ,0<C ∧ ∀{t : ℝ},8*Real.pi*q≤t →
    |‖χ.LFunction ((1/2:ℂ)+t*I)‖-‖primitiveCriticalPolynomial χ (primitiveCriticalLength q t) t‖|≤
      C*t^(-(1/4:ℝ)) := by
  let J := 8+2*Real.Gamma (1/2)
  have hJ : 0<J := by dsimp [J];have := Real.Gamma_pos_of_pos (by norm_num : 0<(1/2:ℝ));positivity
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq₁ : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  let C := 604*Real.sqrt q+J
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
    rw [←Real.sqrt_sq (mul_nonneg hq.le hx'.le)]
    congr 1;rw [mul_pow,Hx];field_simp
  let s := (1/2:ℂ)+t*I
  let N := ⌊(q:ℝ)*x⌋₊
  let P := dirichletPoly (fun n : ℕ => χ n) N s
  let R := (Circle.exp (primitiveHardyPhase q t):ℂ)
  let G := primitiveDualGamma χ s
  let Z := χ.LFunction s
  have hσ : s.re=1/2 := by simp [s]
  have h := primitiveLFunction_logFree_sharp_afe (s:=s) hχ hx (le_mul_of_one_le_left hx'.le hq₁)
    (by rw [hσ];constructor <;>norm_num) (by rw [show s.im=t by simp [s],abs_of_pos ht',ht₂];ring)
  rw [conjugate_polynomial,hσ,show (1:ℝ)-1/2=1/2 by norm_num,←Real.sqrt_eq_rpow] at h
  change ‖Z-P-G*conj P‖≤Real.sqrt q*(604*x^(-(1/2:ℝ))) at h
  have H := primitive_gamma_phase_error hχ hqt
  change ‖R*G-primitiveHardyMultiplier χ*conj R‖≤J/t at H
  have hN : (N:ℝ)≤(q:ℝ)*x := Nat.floor_le (mul_nonneg hq.le hx'.le)
  have htx : (q:ℝ)*x^2≤t := by
    rw [ht₂];nlinarith [mul_le_mul_of_nonneg_right (show 1≤2*Real.pi by linarith [Real.pi_gt_three]) (mul_nonneg hq.le (sq_nonneg x))]
  have hfrac : (N:ℝ)/t≤x^(-(1/2:ℝ)) := by
    calc _ ≤ ((q:ℝ)*x)/(q*x^2) := div_le_div₀ (by positivity) hN (by positivity) htx
         _ = x^(-(1:ℝ)) := by rw [Real.rpow_neg hx'.le,Real.rpow_one];field_simp
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hG : ‖(R*G-primitiveHardyMultiplier χ*conj R)*conj P‖≤J*x^(-(1/2:ℝ)) := by
    rw [norm_mul,Complex.norm_conj]
    calc _ ≤ (J/t)*(N:ℝ) := mul_le_mul H (norm_polynomial_le χ N t) (norm_nonneg _) (by positivity)
         _ = J*((N:ℝ)/t) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hfrac hJ.le
  have hR : ‖R‖=1 := Circle.norm_coe _
  have hi : primitiveCriticalLength q t=N := by rw [primitiveCriticalLength,hlen]
  rw [hi]
  change |‖Z‖-‖R*P+primitiveHardyMultiplier χ*conj (R*P)‖|≤_
  have H := abs_norm_sub_norm_le (R*Z) (R*P+primitiveHardyMultiplier χ*conj (R*P))
  rw [norm_mul,hR,one_mul] at H
  apply H.trans
  rw [map_mul,show R*Z-(R*P+primitiveHardyMultiplier χ*(conj R*conj P))=
      R*(Z-P-G*conj P)+(R*G-primitiveHardyMultiplier χ*conj R)*conj P by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,hR,one_mul]
  apply (add_le_add h hG).trans_eq
  dsimp only [C,x]
  rw [Real.sqrt_eq_rpow (t/(2*Real.pi*q)),←Real.rpow_mul (by positivity : 0≤t/(2*Real.pi*q)),
    show (1/2:ℝ)*(-(1/2))= -(1/4) by norm_num,Real.div_rpow ht'.le (by positivity),Real.rpow_neg (by positivity : 0≤2*Real.pi*q),div_inv_eq_mul]
  ring

end AnalyticNumberTheory.DirichletLFunctions
