import AnalyticNumberTheory.ExponentialSums.ReciprocalExponentPairs
import AnalyticNumberTheory.DivisorProblems.VoronoiFourierBlocks

/-!
# Complementary reciprocal-phase bounds for the divisor problem
-/

open Real Finset
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

/-- On the dual side of the reciprocal B-process, the fifth-derivative
test yields a bound with leading term `A^(11/30) D^(-1/5)`. -/
theorem reciprocal_transformed_derivative_block :
    ∃ C≥1, ∀ {A D : ℝ} {a b : ℕ},1≤D → D^2≤A → D≤a → a≤b → (b:ℝ)≤2*D →
    ‖∑ n∈Ioc a b,e (A/n)‖≤
      C*(A^(11/30:ℝ)*D^(-(1/5):ℝ)+A^(61/120:ℝ)*D^(-(11/20):ℝ))+
        249*(1+Real.sqrt ((2*D)^3/A))*(1+Real.log (6+4*A/D^2)) := by
  obtain ⟨C,hC,H⟩ := reciprocal_saddle_fifth_derivative
  refine ⟨C,hC,?_⟩
  intro A D a b hD hDA ha hab hb
  have hD' : 0<D := by linarith
  have hC' : 0<C := by linarith
  have hA : 0<A := (sq_pos_of_pos hD').trans_le hDA
  have ha' : 0<(a:ℝ) := hD'.trans_le ha
  have hab' : (a:ℝ)≤b := by exact_mod_cast hab
  have hb' : 0<(b:ℝ) := ha'.trans_le hab'
  let W := A/D^2
  have hW : 1≤W := (one_le_div (sq_pos_of_pos hD')).mpr hDA
  let l := A/(b:ℝ)^2
  let u := A/(a:ℝ)^2
  have hl : 0<l := by dsimp [l]; positivity
  have hu : 0<u := by dsimp [u]; positivity
  have hleft : W/4≤(⌊l⌋₊:ℝ)+1 := by
    apply le_trans _ (Nat.lt_floor_add_one l).le
    dsimp [W,l]
    calc A/D^2/4 = A/(2*D)^2 := by field_simp; ring
         _ ≤ _ := by gcongr
  have hright : (⌊u⌋₊:ℝ)≤W := (Nat.floor_le hu.le).trans (by dsimp [u,W]; gcongr)
  let V := ∑ m∈Ioc ⌊l⌋₊ ⌊u⌋₊,reciprocalSaddleTerm A m
  have HV := H hA hW hleft hright
  have main : ‖V‖≤C*(A^(11/30:ℝ)*D^(-(1/5):ℝ)+A^(61/120:ℝ)*D^(-(11/20):ℝ)) := by
    apply HV.trans_eq
    rw [mul_add,mul_add]
    apply congrArg₂ (·+·) <;>
      apply Real.log_injOn_pos <;> first | (simp only [Set.mem_Ioi]; try dsimp [W]; positivity) | skip
    all_goals try dsimp [W]
    all_goals try simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow,Real.log_pow]
    all_goals ring
    all_goals positivity
  have ht := reciprocal_vanDerCorput_real_Ioc (hD.trans ha) hab' (by linarith) hA
  rw [←sum_natFloor_eq_intFloor ha'.le hb'.le,←sum_natFloor_eq_intFloor hl.le hu.le] at ht
  simp only [Nat.floor_natCast,Int.cast_natCast] at ht
  change ‖(∑ n∈Ioc a b,e (A/n))-V‖≤_ at ht
  have hE : 249*(1+Real.sqrt ((b:ℝ)^3/A))*(1+Real.log (6+4*A/(a:ℝ)^2))≤
      249*(1+Real.sqrt ((2*D)^3/A))*(1+Real.log (6+4*A/D^2)) := by
    have hlog := Real.log_nonneg (by linarith [show 0≤4*A/(a:ℝ)^2 by positivity] : 1≤6+4*A/(a:ℝ)^2)
    gcongr
  calc
    _ ≤ ‖(∑ n∈Ioc a b,e (A/n))-V‖+‖V‖ := by simpa only [sub_add_cancel] using norm_add_le ((∑ n∈Ioc a b,e (A/n))-V) V
    _ ≤ _ := by linarith only [ht,hE,main]

end AnalyticNumberTheory.DivisorProblems
