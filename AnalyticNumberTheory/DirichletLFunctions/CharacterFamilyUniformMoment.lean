import AnalyticNumberTheory.RiemannZeta.HurwitzMomentAllHeights
import AnalyticNumberTheory.DirichletLFunctions.CharacterMomentConstants
import AnalyticNumberTheory.AnalyticTools.ReducedRootSum

/-!
# Uniform second moment of a full Dirichlet character family

The average includes every character of the modulus. Orthogonality
expresses it in terms of Hurwitz moments indexed by reduced residues.
A uniform estimate for their inverse square roots controls the error
simultaneously in the modulus and the height.
-/

noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped Interval
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem sum_unit_reciprocal_roots (q : ℕ) [NeZero q] :
    (∑r∈characterUnitIndices q,(√(((r+1:ℕ):ℝ)/q))⁻¹)≤20*q.totient := by
  refine le_trans ?_ (reduced_sqrt_ratio_sum_le (NeZero.pos q))
  apply le_of_eq
  rw [←sum_filter]
  refine sum_bij (fun r _ => r+1) ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨hr,hu⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_pos _,mem_range.mp hr⟩,(ZMod.isUnit_iff_coprime ..).mp hu⟩
  · intro r _ s _ he;omega
  · intro n hn
    obtain ⟨hn,hc⟩ := mem_filter.mp hn
    obtain ⟨h1,hq⟩ := mem_Icc.mp hn
    refine ⟨n-1,mem_filter.mpr ⟨mem_range.mpr (by omega),(ZMod.isUnit_iff_coprime ..).mpr ?_⟩,by omega⟩
    rwa [show n-1+1=n by omega]
  · intro r _
    rw [←Real.sqrt_inv,inv_div]

/-- Uniform two-term mean square, averaged over the full family of modulus q.
The logarithmic cutoff B ≥ 3 is fixed, and the constant is independent of
both q and T. The arithmetic correction is a sum over the prime divisors of q. -/
theorem full_character_second_moment_uniform {B : ℝ} (hB : 3≤B) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q], ∀ {T : ℝ}, 0≤T →
      |(∫t in (0:ℝ)..T,∑χ : DirichletCharacter ℂ q,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)/(q.totient:ℝ)-
        (q.totient/q:ℝ)*(T*Real.log (max T B/(2*Real.pi))+
          (2*Real.eulerMascheroniConstant-1+Real.log q+primeDivisorLogSum q)*T)|
      ≤ C*(q.totient/q:ℝ)*(√T*min 1 (√T))*Real.log (max T B) := by
  obtain ⟨D,hD,HD⟩ := hurwitz_second_moment_uniform hB
  refine ⟨21*D,by positivity,?_⟩
  intro q _ T hT
  let P := (q.totient:ℝ)
  let k := P/q
  let S := characterUnitIndices q
  let a := fun r : ℕ => ((r+1:ℕ):ℝ)/q
  let c := fun r => Real.eulerMascheroniConstant-realDigamma (a r)-1
  let d := 2*Real.eulerMascheroniConstant-1+Real.log q+primeDivisorLogSum q
  let M := T*Real.log (max T B/(2*Real.pi))
  let V := √T*min 1 (√T)
  let l := Real.log (max T B)
  let E := fun r => (∫t in (0:ℝ)..T,hurwitzCriticalEnergy (a r) t)-(M+c r*T)
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hP : 0<P := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos _))
  have hk : 0<k := div_pos hP hq
  have hl : 1≤l := (Real.le_log_iff_exp_le (show 0<max T B by linarith [le_max_right T B])).mpr
    (Real.exp_one_lt_three.le.trans (hB.trans (le_max_right ..)))
  have hV : 0≤V := mul_nonneg (sqrt_nonneg _) (le_min zero_le_one (sqrt_nonneg _))
  have ha (r : ℕ) (hr : r∈S) : a r∈Ioc (0:ℝ) 1 := by
    have hi := mem_range.mp (mem_filter.mp hr).1
    exact ⟨div_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) hq,(div_le_one hq).mpr (by exact_mod_cast hi)⟩
  have hcard : (S.card:ℝ)=P := by dsimp only [S,P];exact_mod_cast card_characterUnitIndices q
  have hs : (∑r∈S,c r)=P*d := by
    apply (mul_right_inj' hk.ne').mp
    change characterFamilyLinearTerm q=k*(P*d)
    rw [characterFamilyLinearTerm_eq_prime_sum]
    dsimp only [d,k,P];ring
  have he (t : ℝ) : (∑χ : DirichletCharacter ℂ q,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)=k*∑r∈S,hurwitzCriticalEnergy (a r) t := by
    rw [character_family_critical_energy,←sum_filter];rfl
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum
    (f:=fun r t => hurwitzCriticalEnergy (a r) t) (fun r _ => (continuous_hurwitzCriticalEnergy _).intervalIntegrable ..)]
  have hm : (∑r∈S,(M+c r*T))=P*(M+d*T) := by
    rw [sum_add_distrib,sum_const,nsmul_eq_mul,←sum_mul,hcard,hs];ring
  have hid : k*(∑r∈S,∫t in (0:ℝ)..T,hurwitzCriticalEnergy (a r) t)/P - k*(M+d*T)
      = (∑r∈S,E r)/(q:ℝ) := by
    dsimp only [E];rw [sum_sub_distrib,hm];dsimp only [k]
    field_simp [hq.ne',hP.ne'] <;>ring
  change |_ - k*(M+d*T)|≤21*D*k*V*l
  rw [hid,abs_div,abs_of_pos hq]
  have hb (r : ℕ) (hr : r∈S) : |E r|≤D*V*((√(a r))⁻¹+l) := HD (ha r hr) hT
  have hsum := (abs_sum_le_sum_abs E S).trans (sum_le_sum hb)
  rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,hcard] at hsum
  have hw : (∑r∈S,(√(a r))⁻¹)≤20*P := sum_unit_reciprocal_roots q
  have hlim : (∑r∈S,(√(a r))⁻¹)+P*l≤21*P*l := by
    nlinarith only [hw,mul_nonneg hP.le (sub_nonneg.mpr hl)]
  have H := hsum.trans (mul_le_mul_of_nonneg_left hlim (mul_nonneg hD.le hV))
  exact (div_le_div_of_nonneg_right H hq.le).trans_eq (by dsimp only [k];ring)

end AnalyticNumberTheory.DirichletLFunctions
