import AnalyticNumberTheory.PrimeDistribution.TwistedPerron
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Half-integer Perron parameters for a prescribed truncation height -/
noncomputable section
open Finset Real Complex AnalyticNumberTheory.DirichletSeries
open scoped Classical ArithmeticFunction.vonMangoldt
namespace AnalyticNumberTheory.PrimeDistribution

/-- For every prescribed height 8 ≤ S ≤ sqrt x the elementary Perron
and contour errors are bounded by absolute constants times
(x/S)(1+log(qx))², uniformly in the arithmetic endpoint 2 ≤ y ≤ x. -/
theorem perron_halfInteger_height_parameters {x y S : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hS : 8≤S) (hSx : S^2≤x) (hy' : 2≤y) (hyx : y≤x) (hq : 2≤q) :
    let N := ⌊y⌋₊
    let h := (N:ℝ)+1/2
    let R := x/S
    let c := 1+1/Real.log (2*x)
    let A := S-1
    let L := 1+Real.log ((q:ℝ)*x)
    let J := 1+Real.log ((q:ℝ)*(A+3))
    2≤N ∧ 1<c ∧ c≤3/2 ∧ 4≤A ∧ ∀ {T : ℝ}, T∈Set.Icc (A+1/4) (A+3/4) →
      ‖dirichletContourIntegral (fun n : ℕ=>χ n*(Λ n:ℂ)) h c T-psiChar y χ‖≤400*(R*L^2) ∧
      (1+1/(c-1))*J+Real.sqrt h*J^2+(h^c+1)/T*J^2≤16*(R*L^2) := by
  have hy : 0≤y := by linarith
  have hqr : 2≤(q:ℝ) := by exact_mod_cast hq
  let R := x/S
  let L := 1+Real.log ((q:ℝ)*x)
  have hS₀ : 0<S := by linarith only [hS]
  have hx' : 64≤x := by nlinarith only [hSx,mul_self_le_mul_self (by norm_num : (0:ℝ)≤8) hS]
  have hx₀ : 0<x := by linarith only [hx']
  have hSR : S≤R := (le_div_iff₀ hS₀).mpr (by simpa only [sq] using hSx)
  have hR : 2≤R := by linarith only [hS,hSR]
  have hR₀ : 0<R := by linarith only [hR]
  have hR₂ : x≤R^2 := by
    have he : R*S=x := div_mul_cancel₀ _ hS₀.ne'
    simpa only [← sq, he] using mul_le_mul_of_nonneg_left hSR hR₀.le
  have hL : 1≤L := by dsimp [L];linarith [Real.log_nonneg (by nlinarith : 1≤(q:ℝ)*x)]
  let N := ⌊y⌋₊
  let h := (N:ℝ)+1/2
  let ℓ := Real.log (2*x)
  let c := 1+1/ℓ
  let A := S-1
  have hN : 2≤N := (Nat.le_floor_iff hy).mpr (by norm_cast)
  have h₀ : 0<h := by dsimp [h];positivity
  have hf : (N:ℝ)≤y := Nat.floor_le hy
  have hhx : h≤2*x := by dsimp [h];linarith
  have hlog : 2≤ℓ := by
    apply (Real.le_log_iff_exp_le (by positivity : 0<2*x)).mpr
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    nlinarith only [mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three.le,hx']
  have hℓ₀ : 0<ℓ := by linarith
  have hc : 1<c := by dsimp [c];linarith only [one_div_pos.mpr hℓ₀]
  have hc' : c≤3/2 := by
    dsimp [c];have ht := (div_le_iff₀ hℓ₀).mpr (by linarith : 1≤(1/2:ℝ)*ℓ);linarith only [ht]
  have hA : 4≤A := by dsimp [A];linarith
  refine ⟨hN,hc,hc',hA,?_⟩
  intro T hT
  change T∈Set.Icc (A+1/4) (A+3/4) at hT
  have hT₁ : S/2≤T := by dsimp [A] at hT;linarith only [hT.1,hS]
  have hT₂ : T≤S := by dsimp [A] at hT;linarith only [hT.2]
  have hT₀ : 0<T := by linarith
  have he := perron_twist_halfInteger_error_le χ hN hc (by linarith) (by linarith : 2≤T)
  have hhfloor : ⌊h⌋₊=N := (Nat.floor_eq_iff h₀.le).mpr (by dsimp [h];constructor <;> linarith)
  have hψ : psiChar y χ=psiChar h χ := by simp only [psiChar,hhfloor,N]
  let Iχ := dirichletContourIntegral (fun n : ℕ=>χ n*(Λ n:ℂ)) h c T
  have hℓ : ℓ≤Real.log ((q:ℝ)*x) := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hqr hx₀.le)
  have hcℓ : 1/(c-1)=ℓ := by dsimp [c];field_simp <;> ring
  have hpow : h^c≤6*x := by
    have hcancel : Real.log (2*x)*(1/ℓ)=1 := by change ℓ*(1/ℓ)=1;field_simp
    calc h^c ≤ (2*x)^c := Real.rpow_le_rpow h₀.le hhx (by linarith)
         _ = (2*x)*Real.exp 1 := by
           rw [show c=1+1/ℓ from rfl,Real.rpow_add (by positivity),Real.rpow_one,
             Real.rpow_def_of_pos (by positivity : 0<2*x),hcancel]
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hx₀.le]
  have hdiv : x/T≤2*R := (div_le_div_of_nonneg_left hx₀.le (half_pos hS₀) hT₁).trans_eq
    (by dsimp only [R]; ring)
  have hpdiv : h^c/T≤12*R := (div_le_div_of_nonneg_right hpow hT₀.le).trans (by linarith only [hdiv,(mul_div_assoc (6:ℝ) x T)])
  have hdiv' : h/T≤4*R := (div_le_div_of_nonneg_right hhx hT₀.le).trans (by linarith only [hdiv,(mul_div_assoc (2:ℝ) x T)])
  have hpow' : (h^c+1)/T≤13*R := by
    rw [add_div];have ht := (div_le_iff₀ hT₀).mpr (show (1:ℝ)≤1*T by linarith);linarith
  have hsqrt : Real.sqrt h≤2*R := by nlinarith only [Real.sq_sqrt h₀.le,Real.sqrt_nonneg h,hR₂,hhx,hR₀]
  let J := 1+Real.log ((q:ℝ)*(A+3))
  have hJ₀ : 0≤J := by dsimp [J];positivity [Real.log_nonneg (show 1≤(q:ℝ)*(A+3) by nlinarith)]
  have hJ : J≤L := by
    dsimp [J,L];gcongr
    dsimp [A]; nlinarith only [hSx,hS,mul_nonneg hS₀.le (show 0≤S-2 by linarith)]
  have hJ₂ := pow_le_pow_left₀ hJ₀ hJ 2
  have hfront : (1+1/(c-1))*J≤R*L^2 := by
    rw [hcℓ]
    apply (mul_le_mul (by dsimp [L];linarith only [hℓ] : 1+ℓ≤L) hJ hJ₀ (by linarith)).trans
    nlinarith only [le_mul_of_one_le_left (sq_nonneg L) (show 1≤R by linarith)]
  have hlogh : Real.log (2*h)≤L := by
    apply (Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hhx (by norm_num : (0:ℝ)≤2))).trans
    rw [Real.log_mul (by norm_num) (by positivity : 2*x≠0)]
    dsimp only [L,ℓ] at *;linarith only [hℓ,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlogh₀ : 0≤Real.log (2*h) := Real.log_nonneg (by dsimp [h];linarith only [(Nat.cast_nonneg N : (0:ℝ)≤N)])
  have hlogh₂ := pow_le_pow_left₀ hlogh₀ hlogh 2
  have hℓL : ℓ≤L := by dsimp [L];linarith only [hℓ]
  have he₁ : h^c/(T*(c-1)^2)≤12*R*L^2 := by
    have hh : h^c/(T*(c-1)^2)=(h^c/T)*ℓ^2 := by dsimp [c];field_simp <;> ring
    rw [hh];exact mul_le_mul hpdiv (pow_le_pow_left₀ hℓ₀.le hℓL 2) (sq_nonneg _) (by positivity)
  have he₂ : h*(Real.log (2*h))^2/T≤4*R*L^2 := by
    rw [mul_div_right_comm];exact mul_le_mul hdiv' hlogh₂ (sq_nonneg _) (by positivity)
  have hk₁ : 4/(Real.pi*Real.log 2)≤4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul Real.pi_gt_three.le Real.log_two_gt_d9.le (by norm_num) Real.pi_pos.le]
  have hk₂ : 64/Real.pi≤64 := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have herr : ‖Iχ-psiChar h χ‖≤400*(R*L^2) := by
    apply he.trans
    nlinarith only [mul_le_mul hk₁ he₁ (by positivity) (by norm_num),mul_le_mul hk₂ he₂ (by positivity) (by norm_num),
      mul_nonneg hR₀.le (sq_nonneg L)]
  refine ⟨by simpa only [hψ] using herr,?_⟩
  change (1+1/(c-1))*J+Real.sqrt h*J^2+(h^c+1)/T*J^2≤16*(R*L^2)
  nlinarith only [hfront,mul_le_mul hsqrt hJ₂ (sq_nonneg J) (by positivity : 0≤2*R),
    mul_le_mul hpow' hJ₂ (sq_nonneg J) (by positivity : 0≤13*R)]

end AnalyticNumberTheory.PrimeDistribution
