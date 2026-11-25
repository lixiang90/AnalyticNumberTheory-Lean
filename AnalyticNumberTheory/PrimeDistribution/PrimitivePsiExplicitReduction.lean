import AnalyticNumberTheory.PrimeDistribution.PrimitivePerronContourBound

/-! # From a half-integer Perron contour to the character explicit bound -/
noncomputable section
open Finset Real Complex AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open scoped Classical ArithmeticFunction.vonMangoldt
namespace AnalyticNumberTheory.PrimeDistribution

private theorem halfInteger_zero_weight_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {h x T U : ℝ} (hx : 0≤x) (hh : 0≤h) (hhx : h≤2*x) (hT : T≤U) :
    characterZeroWeight χ T (fun z=>h^z.re/(1+|z.im|)) ≤
      2*characterZeroWeight χ U (fun z=>x^z.re/(1+|z.im|)) := by
  unfold characterZeroWeight
  rw [mul_sum]
  have hsub : characterStripZeros χ T⊆characterStripZeros χ U := by
    intro z hz
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := (mem_characterStripZeros _).mp hz
    exact (mem_characterStripZeros _).mpr ⟨h₁,h₂,by linarith,h₄.trans hT,h₅⟩
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by positivity))
  apply sum_le_sum;intro z hz
  obtain ⟨hβ,hβ',_⟩ := (mem_characterStripZeros _).mp hz
  have hpow := Real.rpow_le_rpow hh hhx hβ.le
  rw [Real.mul_rpow (by norm_num) hx] at hpow
  have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hβ'.le
  rw [Real.rpow_one] at ht
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hpow.trans (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hx _))) (by positivity)) (Nat.cast_nonneg _)).trans_eq
  ring

/-- Transfer a selected-height Perron bound at half integers to arbitrary real
endpoints. Both the zero height and the common square-root error are measured
at x, uniformly for every character and every y between zero and x. -/
theorem primitive_psi_explicit_all_moduli_of_perron (H : PrimitivePerronContourBound) :
    ∃ C : ℝ, 0<C ∧ ∀{x y : ℝ} {q : ℕ},4≤x → 0≤y → y≤x → 2≤q →
      ∀ χ : DirichletCharacter ℂ q,χ.IsPrimitive →
        ‖psiChar y χ‖≤C*(Real.sqrt x*(1+Real.log ((q:ℝ)*x))^2+
          characterZeroWeight χ (Real.sqrt x) (fun z=>x^z.re/(1+|z.im|))) := by
  obtain ⟨C,hC,HC⟩ := H
  let B := Real.log 4+4
  have hB : 0<B := by dsimp [B];positivity
  refine ⟨8*B+16*C+400,by positivity,?_⟩
  intro x y q hx hy hyx hq χ hp
  haveI : NeZero q := ⟨by omega⟩
  have hqr : 2≤(q:ℝ) := by exact_mod_cast hq
  let R := Real.sqrt x
  let L := 1+Real.log ((q:ℝ)*x)
  let Z := characterZeroWeight χ R (fun z=>x^z.re/(1+|z.im|))
  have hx₀ : 0<x := by linarith
  have hR : 2≤R := (Real.le_sqrt (by norm_num) hx₀.le).mpr (by linarith)
  have hR₀ : 0<R := by linarith
  have hR₂ : R^2=x := Real.sq_sqrt hx₀.le
  have hL : 1≤L := by dsimp [L];linarith [Real.log_nonneg (by nlinarith : 1≤(q:ℝ)*x)]
  have hL₂ : 1≤L^2 := one_le_pow₀ hL
  have hZ : 0≤Z := sum_nonneg (fun z _=>mul_nonneg (Nat.cast_nonneg _) (by positivity))
  change ‖psiChar y χ‖≤(8*B+16*C+400)*(R*L^2+Z)
  have htriv (h : y≤8*R) : ‖psiChar y χ‖≤(8*B+16*C+400)*(R*L^2+Z) := by
    have hh := (norm_psiChar_le_const_mul_self hy χ).trans (mul_le_mul_of_nonneg_left h hB.le)
    have ht : R≤R*L^2+Z := by linarith only [le_mul_of_one_le_right hR₀.le hL₂,hZ]
    apply hh.trans
    calc B*(8*R)=(8*B)*R := by ring
         _ ≤ _ := mul_le_mul (by linarith) ht hR₀.le (by positivity)
  by_cases hx' : 64≤x
  swap
  · apply htriv (hyx.trans ?_)
    nlinarith only [hR₂,hR₀,mul_nonneg hR₀.le (show 0≤8-R by nlinarith)]
  by_cases hy' : 2≤y
  swap
  · exact htriv (by linarith)
  let N := ⌊y⌋₊
  let h := (N:ℝ)+1/2
  let ℓ := Real.log (2*x)
  let c := 1+1/ℓ
  let A := R-1
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
  have hR' : 8≤R := (Real.le_sqrt (by norm_num) hx₀.le).mpr (by linarith)
  have hA : 4≤A := by dsimp [A];linarith
  obtain ⟨T,hT,hcont⟩ := HC hq χ hp hN hc hc' hA
  have hT₁ : R/2≤T := by dsimp [A] at hT;linarith only [hT.1,hR']
  have hT₂ : T≤R := by dsimp [A] at hT;linarith only [hT.2]
  have hT₀ : 0<T := by linarith
  have he := perron_twist_halfInteger_error_le χ hN hc (by linarith) (by linarith : 2≤T)
  have hhfloor : ⌊h⌋₊=N := (Nat.floor_eq_iff h₀.le).mpr (by dsimp [h];constructor <;> linarith)
  have hψ : psiChar y χ=psiChar h χ := by simp only [psiChar,hhfloor,N]
  let Iχ := dirichletContourIntegral (fun n : ℕ=>χ n*(Λ n:ℂ)) h c T
  have hψI : ‖psiChar y χ‖≤‖Iχ‖+‖Iχ-psiChar h χ‖ := by
    rw [hψ];simpa using norm_sub_le Iχ (Iχ-psiChar h χ)
  have hℓ : ℓ≤Real.log ((q:ℝ)*x) := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hqr hx₀.le)
  have hcℓ : 1/(c-1)=ℓ := by dsimp [c];field_simp <;> ring
  have hpow : h^c≤6*x := by
    have hcancel : Real.log (2*x)*(1/ℓ)=1 := by change ℓ*(1/ℓ)=1;field_simp
    calc h^c ≤ (2*x)^c := Real.rpow_le_rpow h₀.le hhx (by linarith)
         _ = (2*x)*Real.exp 1 := by
           rw [show c=1+1/ℓ from rfl,Real.rpow_add (by positivity),Real.rpow_one,
             Real.rpow_def_of_pos (by positivity : 0<2*x),hcancel]
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hx₀.le]
  have hdiv : x/T≤2*R := (div_le_iff₀ hT₀).mpr (by nlinarith only [hR₂,mul_le_mul_of_nonneg_right hT₁ hR₀.le])
  have hpdiv : h^c/T≤12*R := (div_le_div_of_nonneg_right hpow hT₀.le).trans (by linarith only [hdiv,(mul_div_assoc (6:ℝ) x T)])
  have hdiv' : h/T≤4*R := (div_le_div_of_nonneg_right hhx hT₀.le).trans (by linarith only [hdiv,(mul_div_assoc (2:ℝ) x T)])
  have hpow' : (h^c+1)/T≤13*R := by
    rw [add_div];have ht := (div_le_iff₀ hT₀).mpr (show (1:ℝ)≤1*T by linarith);linarith
  have hsqrt : Real.sqrt h≤2*R := by nlinarith only [Real.sq_sqrt h₀.le,Real.sqrt_nonneg h,hR₂,hhx,hR₀]
  let J := 1+Real.log ((q:ℝ)*(A+3))
  have hJ₀ : 0≤J := by dsimp [J];positivity [Real.log_nonneg (show 1≤(q:ℝ)*(A+3) by nlinarith)]
  have hJ : J≤L := by
    dsimp [J,L];gcongr
    dsimp [A];nlinarith only [hR₂,hR',mul_nonneg hR₀.le (show 0≤R-2 by linarith)]
  have hJ₂ := pow_le_pow_left₀ hJ₀ hJ 2
  have hfront : (1+1/(c-1))*J≤R*L^2 := by
    rw [hcℓ]
    apply (mul_le_mul (by dsimp [L];linarith only [hℓ] : 1+ℓ≤L) hJ hJ₀ (by linarith)).trans
    nlinarith only [le_mul_of_one_le_left (sq_nonneg L) (show 1≤R by linarith)]
  have hz := halfInteger_zero_weight_le χ hx₀.le h₀.le hhx hT₂
  have hraw : ‖Iχ‖≤C*(16*(R*L^2)+2*Z) := by
    apply hcont.trans;apply mul_le_mul_of_nonneg_left _ hC.le
    change (1+1/(c-1))*J+Real.sqrt h*J^2+(h^c+1)/T*J^2+_ ≤_
    nlinarith only [hfront,mul_le_mul hsqrt hJ₂ (sq_nonneg J) (by positivity : 0≤2*R),
      mul_le_mul hpow' hJ₂ (sq_nonneg J) (by positivity : 0≤13*R),hz]
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
  apply hψI.trans ((add_le_add hraw herr).trans ?_)
  nlinarith only [mul_nonneg hB.le (mul_nonneg hR₀.le (sq_nonneg L)),mul_nonneg hB.le hZ,mul_nonneg hC.le hZ,hZ]

/-- Specialization to the conductor range required for the density proof
of the Bombieri–Vinogradov theorem. -/
theorem primitivePsiExplicitBound_of_perron (H : PrimitivePerronContourBound) :
    PrimitivePsiExplicitBound := by
  obtain ⟨C,hC,h⟩ := primitive_psi_explicit_all_moduli_of_perron H
  exact ⟨C,hC,fun hx hy hyx hq _ χ hp => h hx hy hyx hq χ hp⟩

end AnalyticNumberTheory.PrimeDistribution
