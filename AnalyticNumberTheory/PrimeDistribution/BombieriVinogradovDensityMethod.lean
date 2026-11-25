import AnalyticNumberTheory.PrimeDistribution.DensityMeanCharacterSums
import AnalyticNumberTheory.PrimeDistribution.ConductorDyadicSummation
import AnalyticNumberTheory.PrimeDistribution.MaximalSmallConductors
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovReduction

/-!
# The zero-density route to the Bombieri–Vinogradov theorem

Summation over conductor blocks preserves the exponents eleven and ten of
the logarithm. A logarithmic cutoff separates these blocks from the small
conductors covered by Siegel–Walfisz.
-/
noncomputable section
open Finset Real Complex
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- Sum over all large conductors, with each character independently
maximized over real endpoints from zero up to x. -/
theorem primitive_large_conductor_mean_of_density (H : PrimitivePsiExplicitBound) :
    ∃ C : ℝ,0<C ∧ ∀{d D : ℕ}{x : ℝ},1≤d → 4≤x → (D:ℝ)≤Real.sqrt x →
      (∑q∈Ioc d D,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,maximalPsiCharNorm x χ) ≤
        C*(Real.sqrt x*D*(Real.log x)^11+x*(d:ℝ)^(-(1/3:ℝ))*(Real.log x)^10) := by
  obtain ⟨K,hK,HK⟩ := primitive_dyadic_mean_of_explicit_bound H
  let r := (2:ℝ)^(-(1/3:ℝ))
  have hr : r<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hfac : 0<(1-r)⁻¹ := inv_pos.mpr (sub_pos.mpr hr)
  refine ⟨K*(2+(1-r)⁻¹),by positivity,?_⟩;intro d D x hd hx hD
  let f (q : ℕ) := (q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,maximalPsiCharNorm x χ
  have hL := Real.log_nonneg (by linarith : 1≤x)
  by_cases hdD : d≤D
  · have hh := conductor_dyadic_summation f hd hdD (A:=K*Real.sqrt x*(Real.log x)^11)
      (B:=K*x*(Real.log x)^10) (by positivity) (by positivity) (by
        intro Q R hQ hQD hR
        exact (HK (hd.trans hQ) hR hx ((by exact_mod_cast hQD : (Q:ℝ)≤D).trans hD)).trans_eq (by ring))
    apply hh.trans
    change _≤K*(2+(1-r)⁻¹)*_
    dsimp only [r] at hfac ⊢
    nlinarith only [mul_nonneg (mul_nonneg hK.le hfac.le)
      (show 0≤Real.sqrt x*(D:ℝ)*(Real.log x)^11 by positivity),
      mul_nonneg hK.le (show 0≤x*(d:ℝ)^(-(1/3:ℝ))*(Real.log x)^10 by positivity)]
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hdD),sum_empty];positivity

private theorem floor_cube_neg_third {r : ℝ} (hr : 1≤r) :
    (⌊r^3⌋₊:ℝ)^(-(1/3:ℝ))≤2/r := by
  have hp := zero_lt_one.trans_le hr
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0<r^3/2)
    (Nat.div_two_lt_floor (one_le_pow₀ hr (n:=3))).le (by norm_num : -(1/3:ℝ)≤0)
  have he : (r^3/2)^(-(1/3:ℝ))=(2:ℝ)^(1/3:ℝ)/r := by
    rw [Real.div_rpow (by positivity) (by norm_num),←Real.rpow_natCast r 3,←Real.rpow_mul hp.le]
    push_cast
    rw [show (3:ℝ)*(-(1/3:ℝ))= -1 by ring,Real.rpow_neg_one,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    field_simp
  rw [he] at h
  have h₂ := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (by norm_num : (1/3:ℝ)≤1)
  apply h.trans
  simpa only [Real.rpow_one] using div_le_div_of_nonneg_right h₂ hp.le

/-- The primitive mean with an independent endpoint for every character. A desired integer
saving k costs k+11 at the upper conductor cutoff and 3(k+10) at the lower. -/
theorem primitive_density_maximal_log_saving (H : PrimitivePsiExplicitBound) (A : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},2≤x → 1≤Real.log x → 1≤Q →
      Q≤x^(1/2:ℝ)/(Real.log x)^(⌈A⌉₊+11) →
      (∑q∈Icc 2 ⌊Q⌋₊,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,maximalPsiCharNorm x χ)≤
        C*x/(Real.log x)^A := by
  let k := ⌈A⌉₊
  let e := 3*(k+10)
  obtain ⟨C,hC,HC⟩ := sum_smallConductor_maximalPsiChar_le A (show 0≤(e:ℝ) by positivity)
  obtain ⟨D,hD,HD⟩ := primitive_large_conductor_mean_of_density H
  refine ⟨C+3*D,by positivity,?_⟩
  intro x Q hx hl hQ hupper
  let L := Real.log x
  let r := L^(k+10)
  let d := ⌊r^3⌋₊
  let F (q : ℕ) := (q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,maximalPsiCharNorm x χ
  have hL : 1≤L := hl
  have hL₀ : 0<L := by linarith
  have hr : 1≤r := one_le_pow₀ hL
  have hd : 1≤d := (Nat.one_le_floor_iff _).mpr (one_le_pow₀ hr)
  have hlevel : Q≤Real.sqrt x/L^(k+11) := by simpa only [Real.sqrt_eq_rpow,L,k] using hupper
  have hfs := Nat.floor_le (show 0≤Q by linarith)
  have hsq : (⌊Q⌋₊:ℝ)≤Real.sqrt x :=
    hfs.trans (hlevel.trans (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL)))
  by_cases hx4 : 4≤x
  · have hlarge := HD hd hx4 hsq
    have h₁ : Real.sqrt x*⌊Q⌋₊*L^11≤x/L^k := by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfs.trans hlevel) (Real.sqrt_nonneg _)) (by positivity : 0≤L^11)).trans_eq
      rw [pow_add]
      have he := Real.sq_sqrt (show 0≤x by linarith)
      field_simp;nlinarith only [he]
    have h₂ : x*(d:ℝ)^(-(1/3:ℝ))*L^10≤2*x/L^k := by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (floor_cube_neg_third hr) (by linarith : 0≤x)) (by positivity : 0≤L^10)).trans_eq
      dsimp only [r];rw [pow_add];field_simp <;> ring
    have hka : L^A≤L^k := by
      rw [←Real.rpow_natCast];exact Real.rpow_le_rpow_of_exponent_le hL (Nat.le_ceil _)
    have hlarge' : (∑q∈Ioc d ⌊Q⌋₊,F q) ≤ 3*D*x/L^A := by
      exact hlarge.trans ((mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hD.le).trans
             ((le_of_eq (by ring)).trans (div_le_div_of_nonneg_left (by positivity : 0≤3*D*x) (Real.rpow_pos_of_pos hL₀ _) hka)))
    have hsmall := HC (Q:=Q) hx hl
    have he : (Real.log x)^(e:ℝ)=r^3 := by dsimp [r,e,L];rw [Real.rpow_natCast,mul_comm 3,pow_mul]
    rw [he] at hsmall
    have hsplit := sum_filter_add_sum_filter_not (Icc 2 ⌊Q⌋₊) (fun q => q≤d) F
    have hfl : ⌊min Q (r^3)⌋₊=min ⌊Q⌋₊ d := Nat.floor_mono.map_min
    have hI : (Icc 2 ⌊Q⌋₊).filter (fun q => q≤d)=Icc 2 ⌊min Q (r^3)⌋₊ := by
      ext q;simp only [mem_filter,mem_Icc,hfl,le_min_iff];tauto
    have hJ : (Icc 2 ⌊Q⌋₊).filter (fun q => ¬q≤d)=Ioc d ⌊Q⌋₊ := by
      ext q;simp only [mem_filter,mem_Icc,mem_Ioc];omega
    rw [hI,hJ] at hsplit
    change (∑q∈Icc 2 ⌊Q⌋₊,F q)≤_
    rw [←hsplit]
    exact (add_le_add hsmall hlarge').trans_eq (by dsimp only [L];ring)
  · have ht : Real.sqrt x<2 := (Real.sqrt_lt' (by norm_num)).mpr (by linarith)
    have hem : Icc 2 ⌊Q⌋₊=∅ := Icc_eq_empty_of_lt (by exact_mod_cast hsq.trans_lt ht)
    rw [hem,sum_empty];positivity

/-- Fixed-endpoint specialization of the maximal primitive mean with
the same upper cutoff. -/
theorem primitive_density_large_x_log_saving (H : PrimitivePsiExplicitBound) (A : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀{x Q : ℝ},2≤x → 1≤Real.log x → 1≤Q →
      Q≤x^(1/2:ℝ)/(Real.log x)^(⌈A⌉₊+11) →
      (∑q∈Icc 2 ⌊Q⌋₊,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,‖psiChar x χ‖)≤
        C*x/(Real.log x)^A := by
  obtain ⟨C,hC,H'⟩ := primitive_density_maximal_log_saving H A
  refine ⟨C,hC,?_⟩
  intro x Q hx hl hQ hupper
  apply le_trans _ (H' hx hl hQ hupper)
  exact sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left
    (sum_le_sum (fun χ _ => norm_psiChar_le_maximalPsiCharNorm χ (by linarith) le_rfl)) (by positivity))

/-- Bombieri–Vinogradov deduced by the zero-density method from the
single-character truncated explicit bound and the uniform Siegel–Walfisz theorem. -/
theorem bombieriVinogradov_of_density_explicit (H : PrimitivePsiExplicitBound) :
    BombieriVinogradovStatement := by
  apply bombieriVinogradov_of_large_x_primitive_mean
  intro A
  obtain ⟨C,hC,h⟩ := primitive_density_large_x_log_saving H A
  refine ⟨((⌈A⌉₊+11:ℕ):ℝ),by positivity,C,hC,?_⟩
  intro x Q hx hl hQ ht
  exact h hx hl hQ (by simpa only [Real.rpow_natCast] using ht)

end AnalyticNumberTheory.PrimeDistribution
