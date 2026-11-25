import AnalyticNumberTheory.DirichletLFunctions.CharacterMomentOrthogonality
import AnalyticNumberTheory.DirichletLFunctions.CharacterHarmonics
import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalSecondMoment

/-!
# Two terms for the second moment of a full character family

Orthogonality at each height reduces the moment to a finite sum of
shifted Hurwitz moments. This includes the imprimitive characters.
-/
noncomputable section
open Real Complex Finset MeasureTheory Filter Set Asymptotics
open scoped Topology Interval
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Indices of the reduced residue classes represented by r+1 in [1,q]. -/
def characterUnitIndices (q : ℕ) [NeZero q] : Finset ℕ := (Finset.range q).filter (fun r => IsUnit ((r+1:ℕ):ZMod q))

theorem card_characterUnitIndices (q : ℕ) [NeZero q] : (characterUnitIndices q).card=q.totient := by
  have H := sum_shift_norm_char_sq (1 : DirichletCharacter ℂ q) 1
  have h (m : ℕ) : ‖(1:DirichletCharacter ℂ q) ((1+m:ℕ):ZMod q)‖^2=
      if IsUnit ((m+1:ℕ):ZMod q) then (1:ℝ) else 0 := by
    rw [Nat.add_comm 1 m];split_ifs with hm
    · rw [MulChar.one_apply hm];norm_num
    · rw [MulChar.map_nonunit _ hm];norm_num
  simp_rw [h] at H;rw [←sum_filter] at H;simpa [characterUnitIndices] using H

/-- The secondary constant for the sum over all characters of modulus q,
expressed as a finite digamma sum over the reduced residue system. -/
def characterFamilyLinearTerm (q : ℕ) [NeZero q] : ℝ :=
  (q.totient/q:ℝ)*∑r∈characterUnitIndices q,
    (Real.eulerMascheroniConstant-realDigamma (((r+1:ℕ):ℝ)/q)-1)

/-- The sum of the critical second moments over a fixed full family.
The T log(T/(2π)) coefficient is φ(q)^2/q. -/
theorem character_family_critical_second_moment (q : ℕ) [NeZero q] :
    (fun T : ℝ => (∫t in (1:ℝ)..T,∑χ : DirichletCharacter ℂ q,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)-
      (((q.totient:ℝ)^2/q)*(T*Real.log (T/(2*Real.pi)))+characterFamilyLinearTerm q*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  let S := characterUnitIndices q
  let a := fun r : ℕ => ((r+1:ℕ):ℝ)/q
  let g := fun r t => ‖HurwitzZeta.hurwitzZeta (a r:UnitAddCircle) ((1/2:ℂ)+(t:ℝ)*I)‖^2
  let c := fun r => Real.eulerMascheroniConstant-realDigamma (a r)-1
  let M := fun T => T*Real.log (T/(2*Real.pi))
  let k := (q.totient/q:ℝ)
  let E := fun r T => (∫t in (1:ℝ)..T,g r t)-(M T+c r*T)
  let V := fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have H (r : ℕ) (hr : r∈S) : E r =O[atTop] V := by
    apply hurwitz_critical_second_moment_expansion
    have h := Finset.mem_range.mp ((Finset.mem_filter.mp hr).1)
    exact ⟨div_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) hq,(div_le_one hq).mpr (by exact_mod_cast h)⟩
  have HH := (IsBigO.sum (s:=S) H).const_mul_left k
  apply HH.congr' _ (Filter.EventuallyEq.rfl)
  apply Filter.Eventually.of_forall;intro T
  have he (t : ℝ) : (∑χ : DirichletCharacter ℂ q,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)=k*∑r∈S,g r t := by
    rw [character_family_critical_energy,←sum_filter];rfl
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (f:=g)
    (fun r _ => ((continuous_hurwitz_critical_line (a r)).norm.pow 2).intervalIntegrable ..)]
  simp only [Finset.sum_apply]
  change k*(∑r∈S,E r T)=k*(∑r∈S,∫t in (1:ℝ)..T,g r t)-(((q.totient:ℝ)^2/q)*M T+characterFamilyLinearTerm q*T)
  simp only [E,sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,←sum_mul]
  rw [show S.card=q.totient from card_characterUnitIndices q]
  change _=k*_ - (((q.totient:ℝ)^2/q)*M T+(k*∑r∈S,c r)*T)
  dsimp only [k];ring

end AnalyticNumberTheory.DirichletLFunctions
