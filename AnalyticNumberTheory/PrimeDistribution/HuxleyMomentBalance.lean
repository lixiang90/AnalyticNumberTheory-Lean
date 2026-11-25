import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Balancing the two weak moments in a density estimate
-/
noncomputable section
open Real
namespace AnalyticNumberTheory.PrimeDistribution

private theorem huxley_power_branch {R V A L T X q k α β : ℝ}
    (hR : 0<R) (hV : 0<V) (hA : 0≤A) (hL : 0≤L) (hT : 0≤T) (hX : 0≤X)
    (hk : 0≤k) (he : (1-q)*k=1)
    (hh : R*V≤A*L^4*(T^α*X^β*R^q)) :
    R≤A^k*L^(4*k)*(T^(α*k)*X^(β*k)*V^(-k)) := by
  have haux : R^(1-q)≤(A*L^4*(T^α*X^β))/V := by
    rw [Real.rpow_sub hR,Real.rpow_one,div_le_div_iff₀ (Real.rpow_pos_of_pos hR _) hV]
    exact hh.trans_eq (by ring)
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hR.le _) haux hk
  rw [← Real.rpow_mul hR.le,he,Real.rpow_one] at h
  apply h.trans_eq
  rw [Real.div_rpow (by positivity) hV.le,Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hA (pow_nonneg hL _),Real.mul_rpow (Real.rpow_nonneg hT _) (Real.rpow_nonneg hX _),
    ← Real.rpow_natCast_mul hL,←Real.rpow_mul hT,←Real.rpow_mul hX,Real.rpow_neg hV.le]
  push_cast; ring

/-- Solve the two large-values branches for the cardinality R. -/
theorem huxley_weak_count_balance {R V A L T X : ℝ}
    (hR : 0<R) (hV : 0<V) (hA : 0≤A) (hL : 1≤L) (hT : 0≤T) (hX : 0≤X)
    (hh : R*V≤A*L^4*(T^(1/4:ℝ)*X^(1/2:ℝ)*R^(1/4:ℝ)+T^(5/12:ℝ)*X^(1/6:ℝ)*R^(7/12:ℝ))) :
    R≤(1+(2*A)^(4/3:ℝ)+(2*A)^(12/5:ℝ))*L^10*
      (T^(1/3:ℝ)*X^(2/3:ℝ)*V^(-(4/3):ℝ)+T*X^(2/5:ℝ)*V^(-(12/5):ℝ)) := by
  let U := T^(1/4:ℝ)*X^(1/2:ℝ)*R^(1/4:ℝ)
  let W := T^(5/12:ℝ)*X^(1/6:ℝ)*R^(7/12:ℝ)
  change R*V≤A*L^4*(U+W) at hh
  have hL0 : 0≤L := by linarith
  have hTW : 0≤T*X^(2/5:ℝ)*V^(-(12/5):ℝ) := by positivity
  have hTU : 0≤T^(1/3:ℝ)*X^(2/3:ℝ)*V^(-(4/3):ℝ) := by positivity
  rcases le_total W U with h | h
  · have hbranch : R*V≤(2*A)*L^4*U := hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left h (show 0≤A*L^4 by positivity)])
    have hb := huxley_power_branch hR hV (by positivity : 0≤2*A) hL0 hT hX (by norm_num : (0:ℝ)≤4/3)
      (q:=1/4) (by norm_num) hbranch
    norm_num at hb
    apply hb.trans
    apply mul_le_mul _ (le_add_of_nonneg_right hTW) hTU (by positivity)
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · linarith [Real.rpow_nonneg (show 0≤2*A by positivity) (12/5:ℝ)]
    · rw [←Real.rpow_natCast (x:=L) (n:=10)]; exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  · have hbranch : R*V≤(2*A)*L^4*W := hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left h (show 0≤A*L^4 by positivity)])
    have hb := huxley_power_branch hR hV (by positivity : 0≤2*A) hL0 hT hX (by norm_num : (0:ℝ)≤12/5)
      (q:=7/12) (by norm_num) hbranch
    norm_num at hb
    apply hb.trans
    apply mul_le_mul _ (le_add_of_nonneg_left hTU) hTW (by positivity)
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · linarith [Real.rpow_nonneg (show 0≤2*A by positivity) (4/3:ℝ)]
    · rw [←Real.rpow_natCast (x:=L) (n:=10)]; exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)



/-- Collect the occupancy, moment, and distribution factors into the two
powers of the height and the mollifier length. -/
theorem huxley_weak_moment_shape {P Z D : ℝ} (hP : 0<P) (hZ : 0<Z) (hD : 0<D) :
    ∃ A>0, ∀ {L T X R : ℝ}, 1≤L → 0≤T → 0≤X → 0≤R →
    ((P*L)*(Z*T*L^4))^(1/4:ℝ)*((5:ℝ)^(3/4:ℝ)*
       (((P*L)*(D*X*L^3))^(1/2:ℝ)*(π*R)^(1/4:ℝ)+
        ((P*L)*(D*T*X*L^7))^(1/6:ℝ)*(π*R)^(7/12:ℝ))) ≤
      A*L^4*(T^(1/4:ℝ)*X^(1/2:ℝ)*R^(1/4:ℝ)+T^(5/12:ℝ)*X^(1/6:ℝ)*R^(7/12:ℝ)) := by
  let c := (P*Z)^(1/4:ℝ)*5^(3/4:ℝ)
  let b := (P*D)^(1/2:ℝ)*π^(1/4:ℝ)
  let d := (P*D)^(1/6:ℝ)*π^(7/12:ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨c*b+c*d,by positivity,?_⟩
  intro L T X R hL hT hX hR
  have hL0 : 0≤L := by linarith
  have h₁ : ((P*L)*(Z*T*L^4))^(1/4:ℝ)=(P*Z)^(1/4:ℝ)*T^(1/4:ℝ)*L^(5/4:ℝ) := by
    rw [show (P*L)*(Z*T*L^4)=((P*Z)*T)*L^5 by ring,Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hT,←Real.rpow_natCast_mul hL0]; norm_num
  have h₂ : ((P*L)*(D*X*L^3))^(1/2:ℝ)=(P*D)^(1/2:ℝ)*X^(1/2:ℝ)*L^(2:ℝ) := by
    rw [show (P*L)*(D*X*L^3)=((P*D)*X)*L^4 by ring,Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hX,←Real.rpow_natCast_mul hL0]; norm_num
  have h₃ : ((P*L)*(D*T*X*L^7))^(1/6:ℝ)=(P*D)^(1/6:ℝ)*T^(1/6:ℝ)*X^(1/6:ℝ)*L^(4/3:ℝ) := by
    rw [show (P*L)*(D*T*X*L^7)=(((P*D)*T)*X)*L^8 by ring,Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hX,Real.mul_rpow (by positivity) hT,←Real.rpow_natCast_mul hL0]; norm_num
  rw [h₁,h₂,h₃,Real.mul_rpow pi_pos.le hR,Real.mul_rpow pi_pos.le hR]
  have hTmerge : T^(1/4:ℝ)*T^(1/6:ℝ)=T^(5/12:ℝ) := by
    rw [←Real.rpow_add_of_nonneg hT (by norm_num) (by norm_num)]; norm_num
  have hm₁ : L^(5/4:ℝ)*L^(2:ℝ)≤L^4 := by
    rw [←Real.rpow_add (by linarith : 0<L),←Real.rpow_natCast (x:=L) (n:=4)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hm₂ : L^(5/4:ℝ)*L^(4/3:ℝ)≤L^4 := by
    rw [←Real.rpow_add (by linarith : 0<L),←Real.rpow_natCast (x:=L) (n:=4)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  let U := T^(1/4:ℝ)*X^(1/2:ℝ)*R^(1/4:ℝ)
  let W := T^(5/12:ℝ)*X^(1/6:ℝ)*R^(7/12:ℝ)
  have hU : 0≤U := by dsimp [U]; positivity
  have hW : 0≤W := by dsimp [W]; positivity
  calc _ = c*b*(L^(5/4:ℝ)*L^(2:ℝ))*U+c*d*(L^(5/4:ℝ)*L^(4/3:ℝ))*W := by
             dsimp only [c,b,d,U,W]; rw [←hTmerge]; ring
       _ ≤ c*b*L^4*U+c*d*L^4*W := by gcongr
       _ ≤ _ := by
          change _≤(c*b+c*d)*L^4*(U+W)
          nlinarith only [mul_nonneg (show 0≤c*b*L^4 by positivity) hW,
                         mul_nonneg (show 0≤c*d*L^4 by positivity) hU]

end AnalyticNumberTheory.PrimeDistribution
