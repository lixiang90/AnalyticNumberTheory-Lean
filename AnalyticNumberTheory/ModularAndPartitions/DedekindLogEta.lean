import AnalyticNumberTheory.ModularAndPartitions.EisensteinContinuation
import AnalyticNumberTheory.ModularAndPartitions.DedekindEta
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The canonical holomorphic logarithm of the Dedekind eta function

The Fourier series fixes the additive branch at the cusp. Inversion
then follows by uniqueness of lifts through the complex exponential.
-/

open Complex Real Set Filter
open scoped Topology UpperHalfPlane MatrixGroups
namespace AnalyticNumberTheory.ModularAndPartitions

/-- Canonical analytic logarithm, normalized by its Fourier series at infinity. -/
noncomputable def dedekindLogEta (z : ℍ) : ℂ := π*I*(z:ℂ)/12-eisensteinLambert (eisensteinNome z) 0

theorem differentiableOn_dedekindLogEta :
    DifferentiableOn ℂ (fun z : ℂ => π*I*z/12-eisensteinLambert (eisensteinNome z) 0) {z | 0<z.im} := by
  apply DifferentiableOn.sub (by fun_prop)
  refine (differentiableOn_eisensteinLambert_nome 0).comp (by unfold eisensteinNome; fun_prop) ?_
  exact fun z hz => norm_eisensteinNome_lt_one hz

theorem continuous_dedekindLogEta : Continuous dedekindLogEta :=
  differentiableOn_dedekindLogEta.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)

private theorem lambert_zero_eq_log {q : ℂ} (hq : ‖q‖<1) :
    -eisensteinLambert q 0=∑' n : ℕ,Complex.log (1-q^(n+1)) := by
  rw [eisensteinLambert_eq_iterated hq,←tsum_neg]
  have h (m : ℕ+) : -(∑' n : ℕ+,((n:ℕ):ℂ)^((0:ℂ)-1)*q^(m*n:ℕ))=Complex.log (1-q^(m:ℕ)) := by
    have hp : ‖q^(m:ℕ)‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq m.2.ne'
    have H := (Complex.hasSum_taylorSeries_neg_log' hp)
    have H' : HasSum (fun n : ℕ+ => (q^(m:ℕ))^(n:ℕ)/(n:ℕ)) (-Complex.log (1-q^(m:ℕ))) := by
      apply (hasSum_pnat_iff_hasSum_succ (f:=fun n : ℕ => (q^(m:ℕ))^n/n)).mpr
      simpa only [Nat.cast_add,Nat.cast_one] using H
    rw [←neg_neg (Complex.log _),←H'.tsum_eq]; congr 1
    apply tsum_congr; intro n
    rw [zero_sub,Complex.cpow_neg_one,pow_mul,div_eq_mul_inv,mul_comm]
  simp_rw [h]
  exact tsum_pnat_eq_tsum_succ (f:=fun n : ℕ => Complex.log (1-q^n))

/-- Exponentiation recovers eta exactly with this choice of logarithm. -/
theorem exp_dedekindLogEta (z : ℍ) : Complex.exp (dedekindLogEta z)=dedekindEta z := by
  let q := eisensteinNome z
  have hq : ‖q‖<1 := norm_eisensteinNome_lt_one z.im_pos
  have hs : Summable (fun n : ℕ => q^(n+1)) := (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one hq)
  have hz (n : ℕ) : 1-q^(n+1)≠0 := by
    apply sub_ne_zero.mpr; intro e
    have H : ‖q^(n+1)‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [←e,norm_one] at H; exact lt_irrefl _ H
  have hlog : Summable (fun n : ℕ => Complex.log (1-q^(n+1))) := by
    simpa [sub_eq_add_neg] using Complex.summable_log_one_add_of_summable hs.neg
  rw [dedekindLogEta,sub_eq_add_neg,Complex.exp_add,lambert_zero_eq_log hq,
    Complex.cexp_tsum_eq_tprod hz hlog,dedekindEta_eq_cexp_mul_tprod]
  congr 1
  apply tprod_congr; intro n
  dsimp [q,eisensteinNome]
  rw [←Complex.exp_nat_mul]; push_cast; congr 2; ring

/-- Exact additive translation law for every integer translate. -/
theorem dedekindLogEta_T_zpow (m : ℤ) (z : ℍ) :
    dedekindLogEta ((ModularGroup.T^m) • z)=dedekindLogEta z+(m:ℂ)*π*I/12 := by
  have hz : (((ModularGroup.T^m) • z : ℍ):ℂ)=(z:ℂ)+m := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, Complex.ofReal_intCast,add_comm]
  have H : eisensteinNome ((z:ℂ)+m)=eisensteinNome z := by
    unfold eisensteinNome
    rw [mul_add,Complex.exp_add,show 2*(π:ℂ)*I*m=m*(2*π*I) by ring,Complex.exp_int_mul,
      Complex.exp_two_pi_mul_I,one_zpow,mul_one]
  simp only [dedekindLogEta,hz,H]; ring

/-- The exact inversion law for the cusp-normalized logarithm, with
the principal logarithm on the open right half-plane. -/
theorem dedekindLogEta_S (z : ℍ) :
    dedekindLogEta (ModularGroup.S • z)=dedekindLogEta z+Complex.log (-I*(z:ℂ))/2 := by
  let L (v : ℍ) := dedekindLogEta (ModularGroup.S • v)
  let R (v : ℍ) := dedekindLogEta v+Complex.log (-I*(v:ℂ))/2
  have hL : Continuous L := continuous_dedekindLogEta.comp (continuous_const_smul ((ModularGroup.S.map (Int.castRingHom ℝ)).toGL))
  have hC : Continuous (fun v : ℍ => Complex.log (-I*(v:ℂ))) := by
    apply continuous_iff_continuousAt.mpr; intro v
    have h : ContinuousAt (fun u : ℍ => -I*(u:ℂ)) v :=
      (continuous_const.mul UpperHalfPlane.continuous_coe).continuousAt
    exact h.clog (Complex.mem_slitPlane_iff.mpr (Or.inl (neg_I_mul_re_pos v)))
  have hR : Continuous R := continuous_dedekindLogEta.add (hC.div_const 2)
  have hE (v : ℍ) : Complex.exp (L v)=Complex.exp (R v) := by
    dsimp only [L,R]; rw [exp_dedekindLogEta,Complex.exp_add,exp_dedekindLogEta,dedekindEta_S_smul,
      Complex.cpow_def_of_ne_zero (fun e => by have h := neg_I_mul_re_pos v; rw [e] at h; simp at h)]
    rw [mul_comm (dedekindEta v)]; congr 2; ring
  have base : L UpperHalfPlane.I=R UpperHalfPlane.I := by
    have hI : ModularGroup.S • UpperHalfPlane.I=UpperHalfPlane.I := by
      apply UpperHalfPlane.ext; rw [UpperHalfPlane.modular_S_smul]; simp
    dsimp only [L,R]; rw [hI]; simp
  exact congrFun (Complex.isCoveringMap_exp.eq_of_comp_eq hL hR (funext fun v => Subtype.ext (hE v)) _ base) z

end AnalyticNumberTheory.ModularAndPartitions
