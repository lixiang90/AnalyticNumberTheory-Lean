import AnalyticNumberTheory.PrimeDistribution.PerronZeroWindows
import AnalyticNumberTheory.PrimeDistribution.PerronCutoffBounds

/-! # A complex explicit formula at a fixed square-root height

The cutoff for the zeros is independent of the arithmetic endpoint.
The regularized weight includes real zeros without dividing by their
distance from the origin in an error term.
-/
noncomputable section
open Finset Real Complex AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.DirichletSeries
open scoped Classical ArithmeticFunction.vonMangoldt
namespace AnalyticNumberTheory.PrimeDistribution

/-- Replace the selected Perron height by √x and the half-integer arithmetic
endpoint by any real y in [1,x], retaining the signed complex zero sum. -/
theorem primitive_signed_explicit_of_perron (H : PrimitiveSignedPerronContourBound) :
    ∃ C : ℝ,0<C ∧ ∀{x y : ℝ}{q : ℕ},4≤x → 1≤y → y≤x → 2≤q →
      ∀χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ‖psiChar y χ+characterPerronZeroSum χ y (Real.sqrt x)‖ ≤
          C*Real.sqrt x*(1+Real.log ((q:ℝ)*x))^2 := by
  obtain ⟨C,hC,HC⟩ := H
  let J := jensenUnitZeroDensityConst
  let B := Real.log 4+4
  have hJ : 0<J := jensenUnitZeroDensityConst_pos
  have hB : 0<B := by dsimp [B];positivity
  refine ⟨400+16*C+402*J+64*B,by positivity,?_⟩
  intro x y q hx hy hyx hq χ hp
  haveI : NeZero q := ⟨by omega⟩
  have hχ : χ≠1 := by
    intro he
    have ha : χ.conductor=q := hp
    rw [he,DirichletCharacter.conductor_one] at ha;omega
  let R := Real.sqrt x
  let L := 1+Real.log ((q:ℝ)*x)
  let V := R*L^2
  have hx₀ : 0<x := by linarith
  have hq' : 2≤(q:ℝ) := by exact_mod_cast hq
  have hR : 2≤R := (Real.le_sqrt (by norm_num) hx₀.le).mpr (by linarith)
  have hR₀ : 0<R := by linarith
  have hsq : R^2=x := Real.sq_sqrt hx₀.le
  have hL : 1≤L := by dsimp [L];linarith [Real.log_nonneg (by nlinarith : 1≤(q:ℝ)*x)]
  have hV : 1≤V := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hL)
  have hRL : R*L≤V := mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg (sub_nonneg.mpr hL) (zero_le_one.trans hL)] : L≤L^2) hR₀.le
  have hlog (t : ℝ) (ht : 0≤t) (htu : t≤R+3) (ht₀ : 0<t) : Real.log ((q:ℝ)*t)≤L := by
    have ha : R+3≤2*x := by nlinarith only [hsq,hR,mul_nonneg hR₀.le (show 0≤R-2 by linarith)]
    have hb := Real.log_le_log (mul_pos (by linarith : 0<(q:ℝ)) ht₀) (mul_le_mul_of_nonneg_left (htu.trans ha) (Nat.cast_nonneg _))
    rw [show (q:ℝ)*(2*x)=2*((q:ℝ)*x) by ring,Real.log_mul (by norm_num) (by positivity : (q:ℝ)*x≠0)] at hb
    dsimp only [L];linarith only [hb,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hcount : (zeroCountL χ R:ℝ)≤6*J*V := by
    have hh := zeroCountL_le_mul_log hχ hR₀.le
    calc _ ≤ 3*J*(R+2)*Real.log ((q:ℝ)*(R+3)) := hh
         _ ≤ (3*J*(2*R))*L :=
           mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : R+2≤2*R) (by positivity))
             (hlog _ (by positivity) le_rfl (by positivity)) (Real.log_nonneg (by nlinarith)) (by positivity)
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hRL hJ.le]
  change _≤(400+16*C+402*J+64*B)*R*L^2
  have hfinal : (400+16*C+402*J+64*B)*R*L^2=(400+16*C+402*J+64*B)*V := by dsimp [V];ring
  rw [hfinal]
  have hsmall (hs : y≤64) : ‖psiChar y χ+characterPerronZeroSum χ y R‖≤(400+16*C+402*J+64*B)*V := by
    have hz := norm_characterPerronZeroSum_sub_endpoint χ hy (le_refl 1) R
    rw [characterPerronZeroSum_one,sub_zero,abs_of_nonneg (sub_nonneg.mpr hy)] at hz
    have hzero := hz.trans (mul_le_mul hcount (by linarith : y-1≤64) (sub_nonneg.mpr hy) (by positivity))
    have hψ := (norm_psiChar_le_const_mul_self (by linarith) χ).trans (mul_le_mul_of_nonneg_left hs hB.le)
    apply (norm_add_le _ _).trans
    nlinarith only [hzero,hψ,mul_le_mul_of_nonneg_left hV hB.le,mul_nonneg hC.le (zero_le_one.trans hV),
      mul_nonneg hJ.le (zero_le_one.trans hV),hV]
  by_cases hx' : 64≤x
  swap
  · exact hsmall (by linarith)
  by_cases hy' : 2≤y
  swap
  · exact hsmall (by linarith)
  let N := ⌊y⌋₊
  let h := (N:ℝ)+1/2
  let c := 1+1/Real.log (2*x)
  let A := R-1
  obtain ⟨hN,hc,hc',hA,Hpars⟩ := perron_halfInteger_sqrt_parameters χ hx' hy' hyx hq
  obtain ⟨T,hT,hcont⟩ := HC hq χ hp hN hc hc' hA
  obtain ⟨herr,hscale⟩ := Hpars hT
  have hT' : T∈Set.Icc (A+1/4) (A+3/4) := hT
  have hT₁ : R/2≤T := by dsimp [A] at hT';linarith only [hT'.1,hR]
  have hT₂ : T≤R := by dsimp [A] at hT';linarith only [hT'.2]
  have hRT : R≤T+1 := by dsimp [A] at hT';linarith only [hT'.1]
  have hT₀ : 0<T := by linarith
  have h₁ : 1≤h := by
    have hn : 2≤(N:ℝ) := by exact_mod_cast hN
    dsimp only [h];linarith
  have hmove : |y-h|≤1 := by
    have hn : (N:ℝ)≤y := Nat.floor_le (by linarith)
    have hn' : y<(N:ℝ)+1 := Nat.lt_floor_add_one y
    dsimp [h];rw [abs_le];constructor <;> linarith
  have he := norm_characterPerronZeroSum_sub_endpoint χ hy h₁ T
  have htotal : (zeroCountL χ T:ℝ)≤6*J*V := (Nat.cast_le.mpr (zeroCountL_mono χ hT₂)).trans hcount
  have hend : ‖characterPerronZeroSum χ y T-characterPerronZeroSum χ h T‖≤6*J*V := by
    apply he.trans;simpa using mul_le_mul htotal hmove (abs_nonneg _) (by positivity)
  have hg := norm_characterPerronZeroSum_sub_height hχ hy hT₀ hT₂ hRT
  have hsize : (y+1)/T≤4*R := (div_le_iff₀ hT₀).mpr (by nlinarith only [hsq,hyx,hR,mul_le_mul_of_nonneg_left hT₁ hR₀.le])
  have hlo := hlog (T+2) (by positivity) (by linarith) (by positivity)
  have hheight : ‖characterPerronZeroSum χ y R-characterPerronZeroSum χ y T‖≤12*J*V := by
    apply hg.trans
    apply (mul_le_mul hsize (mul_le_mul_of_nonneg_left hlo (by positivity : 0≤3*J)) (by
      apply mul_nonneg (by positivity [jensenUnitZeroDensityConst_pos]) (Real.log_nonneg (by nlinarith))) (by positivity)).trans
    nlinarith only [mul_le_mul_of_nonneg_left hRL hJ.le]
  let Iχ := dirichletContourIntegral (fun n : ℕ=>χ n*(Λ n:ℂ)) h c T
  have hr : ‖Iχ+characterPerronZeroSum χ h T‖≤C*(16*V) := hcont.trans (mul_le_mul_of_nonneg_left hscale hC.le)
  have hp' : ‖psiChar y χ-Iχ‖≤400*V := by rw [norm_sub_rev];exact herr
  have hdecomp : psiChar y χ+characterPerronZeroSum χ y R =
      (psiChar y χ-Iχ)+(Iχ+characterPerronZeroSum χ h T)+
      (characterPerronZeroSum χ y T-characterPerronZeroSum χ h T)+
      (characterPerronZeroSum χ y R-characterPerronZeroSum χ y T) := by abel
  rw [hdecomp]
  apply (norm_add_le _ _).trans
  have ht := add_le_add (add_le_add ((norm_add_le _ _).trans (add_le_add hp' hr)) hend) hheight
  have hk := norm_add_le ((psiChar y χ-Iχ)+(Iχ+characterPerronZeroSum χ h T))
      (characterPerronZeroSum χ y T-characterPerronZeroSum χ h T)
  nlinarith only [ht,hk,hheight,hend,hp',hr,mul_nonneg hB.le (zero_le_one.trans hV),mul_nonneg hJ.le (zero_le_one.trans hV)]

end AnalyticNumberTheory.PrimeDistribution
