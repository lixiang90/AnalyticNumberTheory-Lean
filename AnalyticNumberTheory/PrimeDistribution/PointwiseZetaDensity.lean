import AnalyticNumberTheory.PrimeDistribution.PointwiseDensityBalance
import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaInputs
import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaDetector
import AnalyticNumberTheory.SieveMethods.SparseCharacterSampling
import AnalyticNumberTheory.DirichletLFunctions.AllHeightWeyl

/-!
# The zeta zero-density bound from a critical-line pointwise estimate

The single pole of zeta restricts zero detection at small heights. The
zeros below its polar cutoff are estimated by the Riemann–von Mangoldt
count. Weyl's one-sixth estimate makes the resulting density theorem
unconditional for zeta.
-/
noncomputable section
open Real Complex Finset Filter
open scoped ArithmeticFunction.Moebius Classical
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- Growth on the critical line, including bounded heights. -/
def CriticalZetaGrowth (a b : ℝ) : Prop :=
  ∃B : ℝ,0<B ∧ ∀t : ℝ,‖riemannZeta ((1/2:ℂ)+t*I)‖≤B*(|t|+2)^a*(1+Real.log (|t|+2))^b

private theorem pointwise_zeta_high {a b : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b) (hg : CriticalZetaGrowth a b) :
    ∃A : ℝ,0<A ∧ ∃D : ℝ,0<D ∧ ∀{L : ℕ} {σ : ℝ},1≤L → σ∈Set.Icc (3/4:ℝ) 1 → ∀S : Finset ℂ,
    let H := (L:ℝ)+2
    let Y := pointwiseDensityCutoff A b a H σ
    (∀z∈S,riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0<z.im ∧ z.im<L ∧ 96*Y^(1-σ)*(1+Real.log Y)^3≤z.im) →
    (S.card:ℝ)≤D*(1+Real.log H)^(9+2*b)*H^(pointwiseDensityExponent a σ) := by
  obtain ⟨B,hB,HB⟩ := hg
  obtain ⟨W,hW,HW⟩ := montgomery_zeta_zero_detector
  obtain ⟨K,hK,HK⟩ := zeta_density_sample_count_inputs
  obtain ⟨C,hC,Hfixed,_⟩ := sparse_character_family_mean
  obtain ⟨A,hA,D,hD,HD⟩ := pointwise_density_balanced ha hb hB hC (zero_le_one.trans hK) hW
  refine ⟨A,hA,D,hD,?_⟩
  intro L σ hL hσ S
  dsimp only
  intro hS
  let H := (L:ℝ)+2
  let Y := pointwiseDensityCutoff A b a H σ
  have hH : 1≤H := by dsimp [H];linarith [Nat.cast_nonneg (α:=ℝ) L]
  have hY := (pointwise_density_cutoff_estimates hA.le ha hb).choose_spec.2 hH hσ |>.1
  let F := (univ : Finset (DirichletCharacter ℂ 1))
  have hfc : F.card=1 := by change Fintype.card (DirichletCharacter ℂ 1)=1;rw [card_dirichletCharacter_eq_totient];decide
  let f (_ : DirichletCharacter ℂ 1) (t:ℝ) := ‖riemannZeta ((1/2:ℂ)+t*I)‖
  have hs := HK L S (fun z hz => by
    obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := hS z hz
    exact ⟨h₁,by linarith [hσ.1],h₃,h₄,h₅⟩)
  have Hs := HD (F:=F) (fun _ => 1) id (fun _ => S) hL hH hσ
    (by rw [hfc];simp [H])
    (fun _ _ => by simp [H]) (by simpa only [id_eq,Nat.cast_one,one_mul,F,H] using Hfixed 1 L)
    (fun _ _ z hz => ⟨(hS z hz).2.1,(hS z hz).2.2.1.le,(hS z hz).2.2.2.1.le,(hS z hz).2.2.2.2.1⟩)
    (fun _ _ => hs.1) f (fun _ _ => continuous_riemannZeta_half.norm) (fun _ _ _ => norm_nonneg _) (fun _ _ t => by
      simpa [f] using HB t)
  have hchar (χ : DirichletCharacter ℂ 1) (n : ℕ) : χ n=1 := by rw [Subsingleton.elim (n:ZMod 1) 1,map_one]
  have hi := Hs (fun hX χ _ z hz => by
    obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := hS z hz
    have h := HW hX hY hσ.1 h₂ h₃ h₆ h₁
    simpa only [PointwiseZeroDetector,id_eq,f,hchar,mul_one] using h)
  simpa only [F,sum_const,card_univ,card_dirichletCharacter_eq_totient,Nat.totient_one,one_nsmul,H] using hi

/-- The positive-height zeta count with analytic multiplicity under a hybrid
pointwise bound on the critical line. -/
theorem pointwise_zeta_density {a b : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b) (hg : CriticalZetaGrowth a b) :
    ∃C : ℝ,0<C ∧ ∀{σ T : ℝ},σ∈Set.Icc (3/4:ℝ) 1 → 2≤T →
    (∑z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ)) ≤
      C*T^(pointwiseDensityExponent a σ)*(Real.log T)^(10+2*b) := by
  obtain ⟨A,hA,D,hD,HD⟩ := pointwise_zeta_high ha hb hg
  obtain ⟨B,hB,HB⟩ := pointwise_density_cutoff_estimates hA.le ha hb
  obtain ⟨K,hK,HK⟩ := sum_zeroMultiplicity_strip_le
  obtain ⟨M,hM,HM⟩ := montgomery_zeta_low_zeros
  let E := D*K + M*(16*max 1 A)*B^4
  have hE : 0<E := by dsimp [E];positivity
  refine ⟨E*(12*30^(10+2*b)),by positivity,?_⟩
  intro σ T hs hT
  let L : ℕ := ⌈T⌉₊+16
  let H := (L:ℝ)+2
  let ℓ := 1+Real.log H
  let Y := pointwiseDensityCutoff A b a H σ
  let U := 96*Y^(1-σ)*(1+Real.log Y)^3
  let S := zeroDensityFinset σ T
  let P := S.filter (fun z => U≤z.im)
  let V := S.filter (fun z => ¬U≤z.im)
  have hL : 1≤L := by dsimp [L];omega
  have hLT : T<(L:ℝ) := by dsimp [L];push_cast;linarith [Nat.le_ceil T]
  have hH : 1≤H := by dsimp [H];linarith [Nat.cast_nonneg (α:=ℝ) L]
  have hHT : H≤12*T := by dsimp [H,L];push_cast;linarith [Nat.ceil_lt_add_one (by linarith : 0≤T)]
  have hℓ : 1≤ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hH]
  have hℓ' := zero_lt_one.trans_le hℓ
  let Z := H^(pointwiseDensityExponent a σ)
  have hZ : 0≤Z := Real.rpow_nonneg (zero_le_one.trans hH) _
  obtain ⟨hy,hl,_,hpow⟩ := HB hH hs
  change 16≤Y at hy
  change 1+Real.log Y≤B*ℓ at hl
  change Y^(2*(1-σ))≤16*max 1 A*ℓ^(3+2*b)*Z at hpow
  have hPc := HD hL hs P (fun z hz => by
    obtain ⟨hz,hu⟩ := mem_filter.mp hz
    obtain ⟨hz₀,h₁,h₂,h₃,h₄⟩ := mem_zeroDensityFinset.mp hz
    exact ⟨hz₀,h₁,h₂,h₃,h₄.trans_lt hLT,hu⟩)
  have hPm (z : ℂ) (hz : z∈P) : (zeroMultiplicity z:ℝ)≤K*ℓ := by
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := mem_zeroDensityFinset.mp (mem_filter.mp hz).1
    have hh := HK z.im {z} (fun w hw => by
      obtain rfl := mem_singleton.mp hw
      exact ⟨h₁,by linarith [hs.1],h₃,by simp⟩)
    simp only [sum_singleton,abs_of_pos h₄] at hh
    apply hh.trans (mul_le_mul_of_nonneg_left _ hK.le)
    dsimp [ℓ];linarith [Real.log_le_log (by linarith : 0<z.im+2) (by dsimp [H];linarith : z.im+2≤H)]
  have hp := sum_le_sum hPm
  rw [sum_const,nsmul_eq_mul] at hp
  have hp' := hp.trans (mul_le_mul_of_nonneg_right hPc (mul_nonneg hK.le hℓ'.le))
  have hv := HM (show 0<σ by linarith [hs.1]) hs.2 (by linarith : 1≤Y) V (fun z hz => by
    obtain ⟨hz,hu⟩ := mem_filter.mp hz
    obtain ⟨h₁,h₂,h₃,h₄,_⟩ := mem_zeroDensityFinset.mp hz
    exact ⟨h₁,h₂,h₃,h₄,(lt_of_not_ge hu).le⟩)
  have hvlog := pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : 1≤Y)] : 0≤1+Real.log Y) hl 4
  have hvpow := (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Y) (show 1-σ≤2*(1-σ) by linarith [hs.2])).trans hpow
  have hv' := hv.trans (mul_le_mul (mul_le_mul_of_nonneg_left hvpow hM.le) hvlog (by positivity) (by positivity))
  have hpowℓ : ℓ^(3+2*b)*(B*ℓ)^4≤B^4*ℓ^(10+2*b) := by
    rw [mul_pow,show ℓ^(3+2*b)*(B^4*ℓ^4)=B^4*(ℓ^(3+2*b)*ℓ^4) by ring,←Real.rpow_natCast ℓ 4,←Real.rpow_add hℓ']
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hℓ;push_cast;linarith
  have hpsum : ℓ^(9+2*b)*ℓ=ℓ^(10+2*b) := by
    rw [←Real.rpow_add_one hℓ'.ne'];congr 1;ring
  have hnum : (∑z∈S,(zeroMultiplicity z:ℝ))≤E*ℓ^(10+2*b)*Z := by
    rw [←sum_filter_add_sum_filter_not S (fun z => U≤z.im)]
    change _+_≤_
    change (∑z∈P,(zeroMultiplicity z:ℝ))≤D*ℓ^(9+2*b)*Z*(K*ℓ) at hp'
    dsimp only [E];nlinarith only [hp',hv',mul_le_mul_of_nonneg_left hpowℓ (show 0≤M*(16*max 1 A)*Z by positivity),congrArg (fun x => D*K*Z*x) hpsum]
  have hscale := pointwise_density_scale hb hH (by linarith : 0≤T) hT hHT (by nlinarith) (pointwiseDensityExponent_mem ha hs)
  rw [mul_assoc] at hnum
  exact hnum.trans ((mul_le_mul_of_nonneg_left hscale hE.le).trans_eq (by ring))

/-- Weyl's critical-line estimate gives the exponent (5/3)(1−σ)/(2σ−1) with
a twelfth power of log T, counting analytic multiplicity. -/
theorem weyl_zeta_density :
    ∃C : ℝ,0<C ∧ ∀{σ T : ℝ},σ∈Set.Icc (3/4:ℝ) 1 → 2≤T →
    (∑z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ)) ≤
      C*T^((5/3)*(1-σ)/(2*σ-1))*(Real.log T)^12 := by
  obtain ⟨B,hB,HB⟩ := LFunction_weyl_all_heights
  have hg : CriticalZetaGrowth (1/6) 1 := ⟨B,hB,fun t => by
    simpa [DirichletCharacter.LFunction_modOne_eq,add_comm] using HB (1:DirichletCharacter ℂ 1) t⟩
  obtain ⟨C,hC,HC⟩ := pointwise_zeta_density (a:=1/6) (b:=1) (by constructor <;> norm_num) zero_le_one hg
  refine ⟨C,hC,fun hs hT => ?_⟩
  convert HC hs hT using 1 <;> norm_num [pointwiseDensityExponent] <;> ring

end AnalyticNumberTheory.PrimeDistribution
