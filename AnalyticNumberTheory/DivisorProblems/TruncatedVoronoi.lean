import AnalyticNumberTheory.DivisorProblems.VoronoiCosineSum

/-!
# The truncated Voronoï formula for the divisor problem

The symmetric hyperbola sum is transformed one Fourier harmonic at a
time. The resulting square-root phases combine into the classical finite
cosine sum, uniformly in the truncation point.
-/

open Real Complex Finset
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

private theorem divisor_voronoi_log_bound {δ : ℝ} (hδ : 0<δ) :
    ∃ K>0, ∀ {x : ℝ} {N : ℕ},1≤N → (N:ℝ)≤x →
      |divisorError x-voronoiDivisorSum x N| ≤
      K*(Real.sqrt (x/N)+x^(1/4:ℝ))*(2*x)^δ*(1+Real.log (10*x))^3 := by
  obtain ⟨C,hC,hfour⟩ := sum_abs_divisor_sawtooth_truncation hδ
  let Z := ∑' h:ℕ,(h:ℝ)^(-(3/2):ℝ)
  have hZ : 0≤Z := tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
  let c := 1+(Real.log 2)⁻¹
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨8+2*C+498*c+Z,by positivity,?_⟩
  intro x N hN hNx
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hn' : 0<(N:ℝ) := by linarith
  have hx := hn.trans hNx
  have hx' : 0<x := by linarith
  let R := Real.sqrt (x/N)
  let P := x^(1/4:ℝ)
  let L := 1+Real.log (10*x)
  let Y := (2*x)^δ
  let J := ⌈Real.log x/Real.log 2⌉₊
  let Q := R+P
  let S := ∑ d∈Icc 1 ⌊Real.sqrt x⌋₊,sawtooth (x/d)
  let D := ∑ d∈Icc 1 ⌊Real.sqrt x⌋₊,sawtoothSineSum (divisorFourierCutoff d R) (x/d)
  let A := ∑ h∈Icc 1 ⌊Real.sqrt x/R⌋₊,(((h:ℝ)⁻¹:ℝ):ℂ)*
      ∑ n∈Ioc ⌊(h:ℝ)*R⌋ ⌊Real.sqrt x⌋,e ((h:ℝ)*x/n)
  let B := divisorDualBlocks x N
  have hR : 1≤R := Real.one_le_sqrt.mpr ((le_div_iff₀ hn').mpr (by simpa using hNx))
  have hP : 1≤P := Real.one_le_rpow hx (by norm_num)
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg (by linarith : 1≤10*x)]
  have hY : 1≤Y := Real.one_le_rpow (by linarith) hδ.le
  have hQ : 1≤Q := by dsimp [Q]; linarith
  have hQ₁ : R≤Q := by dsimp [Q]; linarith
  have hQ₂ : 1+P≤Q := by dsimp [Q]; linarith
  have hQ₃ : P≤Q := by dsimp [Q]; linarith
  have h₁ : |divisorError x+2*S|≤8 := abs_divisorError_add_two_sum_sawtooth_le hx
  have h₂ : |S+D|≤C*R*Y*L := by
    dsimp only [S,D]; rw [←sum_add_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans ((hfour hx hR).trans ?_)
    have hl := Real.log_le_log (by positivity : 0<4+2*x) (by linarith : 4+2*x≤10*x)
    dsimp only [Y,L]; gcongr
  have hD : D=A.im/Real.pi := sum_sawtoothSineSum_eq_reciprocalBlocks hx hR
  have hJ : (J:ℝ)≤c*L := by
    have H := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hx) h2.le)
    have hl := Real.log_le_log hx' (by linarith : x≤10*x)
    dsimp only [J,c,L] at *
    have h := mul_le_mul_of_nonneg_right hl (inv_nonneg.mpr h2.le)
    rw [div_eq_mul_inv] at H ⊢
    nlinarith only [H,h,Real.log_nonneg (by linarith : 1≤10*x),inv_nonneg.mpr h2.le]
  have hbound : ‖A-B‖≤249*(c*L)*Q*L*L := by
    have H := norm_divisorFourierBlocks_sub_dual_le hN hNx
    have hp : Real.sqrt (Real.sqrt x)=P := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hx'.le]
      congr 1; norm_num
    change ‖A-B‖≤249*J*(1+Real.sqrt (Real.sqrt x))*(1+Real.log (6+4*x))*(1+Real.log x) at H
    rw [hp] at H; apply H.trans
    have hl₁ : 1+Real.log (6+4*x)≤L := by
      dsimp only [L]; gcongr; linarith
    have hl₂ : 1+Real.log x≤L := by dsimp only [L]; gcongr; linarith
    have hlog : 0≤1+Real.log (6+4*x) := by linarith [Real.log_nonneg (by linarith : 1≤6+4*x)]
    have hlog' : 0≤1+Real.log x := by linarith [Real.log_nonneg hx]
    gcongr
  have h₃ : |2*D-2*B.im/Real.pi|≤498*c*Q*L^3 := by
    rw [hD,show 2*(A.im/Real.pi)-2*B.im/Real.pi=(2/Real.pi)*(A-B).im by rw [Complex.sub_im]; ring,
      abs_mul,abs_of_nonneg (by positivity : 0≤2/Real.pi)]
    have H := mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hbound)
      (by positivity : 0≤2/Real.pi)
    apply H.trans
    have hprod : 0≤249*(c*L)*Q*L*L := by positivity
    calc 2/Real.pi*(249*(c*L)*Q*L*L)≤2*(249*(c*L)*Q*L*L) :=
          mul_le_mul_of_nonneg_right ((div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])) hprod
         _ = _ := by ring
  have h₄ : |2*B.im/Real.pi-voronoiDivisorSum x N|≤Z*Q := by
    have H := divisorDualBlocks_im_eq_voronoi_sub_diagonal hx' N
    change 2*B.im/Real.pi=_ at H
    rw [H,sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (by positivity : 0≤x^(1/4:ℝ)/(Real.pi*Real.sqrt 2))]
    apply (mul_le_mul_of_nonneg_left (abs_voronoi_diagonal_le x N) (by positivity)).trans
    rw [mul_comm Z]
    apply mul_le_mul_of_nonneg_right _ hZ
    apply (div_le_self (Real.rpow_nonneg hx'.le _) ?_).trans hQ₃
    have H₁ : 1≤Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left H₁ Real.pi_pos.le,Real.pi_gt_three]
  let F := Q*Y*L^3
  have hL₁ : L≤L^3 := le_self_pow₀ hL (by norm_num)
  have hF : 1≤F := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ hY) (one_le_pow₀ hL)
  have hF₂ : R*Y*L≤F := by dsimp only [F]; gcongr
  have hF₃ : Q*L^3≤F := by dsimp only [F]; gcongr; exact le_mul_of_one_le_right (by linarith) hY
  have hF₄ : Q≤F := by dsimp only [F]; exact (le_mul_of_one_le_right (by linarith) hY).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL))
  have halg := abs_add_le (divisorError x+2*S) (-(2*(S+D)))
  have ha : |divisorError x-2*D| ≤8 + 2*(C*R*Y*L) := by
    rw [show divisorError x-2*D=(divisorError x+2*S)+ -(2*(S+D)) by ring]
    apply halg.trans; rw [abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num))
  have hb := (abs_sub_le (divisorError x) (2*D) (voronoiDivisorSum x N)).trans
    (add_le_add ha ((abs_sub_le (2*D) (2*B.im/Real.pi) _).trans (add_le_add h₃ h₄)))
  apply hb.trans
  change _ ≤ (8+2*C+498*c+Z)*Q*Y*L^3
  nlinarith only [mul_le_mul_of_nonneg_left hF (by norm_num : (0:ℝ)≤8),
    mul_le_mul_of_nonneg_left hF₂ (by positivity : 0≤2*C),
    mul_le_mul_of_nonneg_left hF₃ (by positivity : 0≤498*c),
    mul_le_mul_of_nonneg_left hF₄ hZ,show F=Q*Y*L^3 from rfl]

/-- Uniform truncated Voronoï formula. The exponent loss absorbs the three
logarithms from Fourier truncation, dyadic subdivision and Poisson summation. -/
theorem truncated_voronoi_divisor_formula {ε : ℝ} (hε : 0<ε) :
    ∃ C>0, ∀ {x : ℝ} {N : ℕ},1≤N → (N:ℝ)≤x →
      |divisorError x-voronoiDivisorSum x N| ≤
        C*x^ε*(x^(1/4:ℝ)+Real.sqrt (x/N)) := by
  let δ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,h⟩ := divisor_voronoi_log_bound hδ
  let c := (1+δ⁻¹)*(10:ℝ)^δ
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨K*(2:ℝ)^δ*c^3,by positivity,?_⟩
  intro x N hN hNx
  have hx : 1≤x := (show 1≤(N:ℝ) by exact_mod_cast hN).trans hNx
  have hx' : 0<x := by linarith
  have hten : 1≤10*x := by linarith
  have hl : 1+Real.log (10*x)≤c*x^δ := by
    have h₁ := Real.log_le_rpow_div (zero_le_one.trans hten) hδ
    have h₂ := Real.one_le_rpow hten hδ.le
    dsimp [c]; rw [Real.mul_rpow (by norm_num : 0≤(10:ℝ)) hx'.le] at h₁ h₂
    rw [div_eq_mul_inv] at h₁; nlinarith only [h₁,h₂]
  have hpow : x^δ*(x^δ)^3=x^ε := by
    rw [←Real.rpow_natCast (x^δ) 3,←Real.rpow_mul hx'.le,←Real.rpow_add hx']
    congr 1; dsimp [δ]; ring
  apply (h hN hNx).trans
  rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) hx'.le]
  have hL : 0≤1+Real.log (10*x) := by linarith [Real.log_nonneg hten]
  calc
    _ ≤ K*(Real.sqrt (x/N)+x^(1/4:ℝ))*((2:ℝ)^δ*x^δ)*(c*x^δ)^3 := by gcongr
    _ = (K*(2:ℝ)^δ*c^3)*(x^δ*(x^δ)^3)*(x^(1/4:ℝ)+Real.sqrt (x/N)) := by ring
    _ = _ := by rw [hpow]

/-- The uniform formula with an arbitrary real truncation point `y`.
The finite sum ranges over the positive integers at most `y`. -/
theorem truncated_voronoi_divisor_formula_real {ε : ℝ} (hε : 0<ε) :
    ∃ C>0, ∀ {x y : ℝ},1≤y → y≤x →
      |divisorError x-voronoiDivisorSum x ⌊y⌋₊| ≤
        C*x^ε*(x^(1/4:ℝ)+Real.sqrt (x/y)) := by
  obtain ⟨C,hC,H⟩ := truncated_voronoi_divisor_formula hε
  refine ⟨2*C,by positivity,?_⟩
  intro x y hy hyx
  have hx := hy.trans hyx
  have hy' : 0<y := by linarith
  have hx' : 0<x := by linarith
  have hn : 1≤⌊y⌋₊ := Nat.floor_pos.mpr hy
  have hn' : 1≤(⌊y⌋₊:ℝ) := by exact_mod_cast hn
  have hn0 : 0<(⌊y⌋₊:ℝ) := by linarith
  have hh : y≤2*(⌊y⌋₊:ℝ) := by linarith [Nat.lt_floor_add_one y]
  have hr : Real.sqrt (x/⌊y⌋₊)≤2*Real.sqrt (x/y) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [Real.sq_sqrt (by positivity),mul_pow,Real.sq_sqrt (by positivity)]
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hn0 hy').mpr
    nlinarith only [mul_le_mul_of_nonneg_left hh hx'.le, mul_nonneg hx'.le hn0.le]
  apply (H hn ((Nat.floor_le hy'.le).trans hyx)).trans
  calc
    _ ≤ C*x^ε*(x^(1/4:ℝ)+2*Real.sqrt (x/y)) := by gcongr
    _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hx'.le ε)) (Real.rpow_nonneg hx'.le (1/4))]

/-- The classical two-term error for the truncated Voronoï cosine formula,
for every real `1 ≤ y ≤ x`. -/
theorem truncated_voronoi_classical_error {ε : ℝ} (hε : 0<ε) :
    ∃ C>0, ∀ {x y : ℝ},1≤y → y≤x →
      |divisorError x-voronoiDivisorSum x ⌊y⌋₊| ≤
        C*(x^(1/6+ε)*y^(1/6:ℝ)+x^(1/2+ε)*y^(-(1/2):ℝ)) := by
  obtain ⟨C,hC,H⟩ := truncated_voronoi_divisor_formula_real hε
  refine ⟨2*C,by positivity,?_⟩
  intro x y hy hyx
  have hx := hy.trans hyx
  have hx' : 0<x := by linarith
  have hy' : 0<y := by linarith
  have hsx : 0<Real.sqrt x := Real.sqrt_pos.mpr hx'
  let P := x^(1/4:ℝ)
  let U := x^(1/6:ℝ)*y^(1/6:ℝ)
  let V := Real.sqrt (x/y)
  have hp : P=Real.sqrt (Real.sqrt x) := by
    dsimp [P]; rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hx'.le]; congr 1; norm_num
  have hUV : P≤U+V := by
    rcases le_total y (Real.sqrt x) with hl|hl
    · have hu : 0≤U := by unfold U; positivity
      apply le_trans (b:=V) _ (by linarith)
      rw [hp]; apply Real.sqrt_le_sqrt
      apply (le_div_iff₀ hy').mpr
      exact (mul_le_mul_of_nonneg_left hl hsx.le).trans_eq (Real.mul_self_sqrt hx'.le)
    · have H₁ : P=x^(1/6:ℝ)*(Real.sqrt x)^(1/6:ℝ) := by
        dsimp [P]; rw [Real.sqrt_eq_rpow,←Real.rpow_mul hx'.le,←Real.rpow_add hx']; congr 1; norm_num
      have hv₀ : 0≤V := Real.sqrt_nonneg _
      apply le_trans (b:=U) _ (by linarith)
      rw [H₁]; dsimp [U]; gcongr
  have hv : V=x^(1/2:ℝ)*y^(-(1/2):ℝ) := by
    dsimp [V]; rw [Real.sqrt_div hx'.le,Real.rpow_neg hy'.le,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,div_eq_mul_inv]
  apply (H hy hyx).trans
  change C*x^ε*(P+V) ≤ _
  have hU : 0≤U := by dsimp [U]; positivity
  have hz : P+V≤2*(U+V) := by linarith
  apply (mul_le_mul_of_nonneg_left hz (by positivity : 0≤C*x^ε)).trans_eq
  dsimp only [U]; rw [hv,Real.rpow_add hx',Real.rpow_add hx']; ring

end AnalyticNumberTheory.DivisorProblems
