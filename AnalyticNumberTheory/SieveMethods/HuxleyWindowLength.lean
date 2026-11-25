import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Height subdivision at a large-value threshold

The window length is chosen so that its local sparse sampling error can
be absorbed into the threshold. When the continuous optimum falls below
one, the lower bound on the threshold suffices on a unit window.
-/
open Real
namespace AnalyticNumberTheory.SieveMethods

/-- A window giving simultaneous control of the local conductor cost and
the number of intervals needed to cover the original height range. -/
theorem huxley_window_length {D L : ℕ} (hD : 1≤D) (hL : 1≤L) {U : ℝ}
    (hU : Real.sqrt (3*D)*(1+Real.log (3*D))^2≤U) :
    ∃ W : ℕ,1≤W ∧ W≤L ∧
      Real.sqrt ((D:ℝ)*(W+2))*(1+Real.log ((D:ℝ)*(W+2)))^2≤U ∧
      (L:ℝ)/W+1≤2+6*(L:ℝ)*D*(1+Real.log ((D:ℝ)*(L+2)))^4/U^2 := by
  have hd : (1:ℝ)≤D := by exact_mod_cast hD
  have ht : (1:ℝ)≤L := by exact_mod_cast hL
  have hl₁ := Real.log_nonneg (show 1≤3*(D:ℝ) by linarith)
  have hU₀ : 0<U := lt_of_lt_of_le (mul_pos (Real.sqrt_pos.mpr (by linarith)) (sq_pos_of_pos (by linarith))) hU
  let ℓ := 1+Real.log ((D:ℝ)*(L+2))
  have hh : 1≤(D:ℝ)*(L+2) := one_le_mul_of_one_le_of_one_le hd (by linarith)
  have hℓ : 0<ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hh]
  let y := U^2/(3*D*ℓ^4)
  have hd₀ : 0<(D:ℝ) := by linarith
  have hy : 0<y := by dsimp only [y];positivity
  let W := max 1 (min L ⌊y⌋₊)
  have hw : 1≤W := le_max_left ..
  have hwL : W≤L := max_le hL (min_le_left ..)
  have hw₀ : (1:ℝ)≤W := by exact_mod_cast hw
  have hw' : 0<(W:ℝ) := by linarith
  refine ⟨W,hw,hwL,?_,?_⟩
  · by_cases h:W=1
    · rw [h,Nat.cast_one,show (1:ℝ)+2=3 by norm_num,mul_comm (D:ℝ)];exact hU
    have hwy : (W:ℝ)≤y := by
      have h' : 1< W := by omega
      have hmin : 1≤min L ⌊y⌋₊ := by dsimp [W] at h';omega
      have : W≤⌊y⌋₊ := by dsimp [W];omega
      exact (by exact_mod_cast this : (W:ℝ)≤⌊y⌋₊).trans (Nat.floor_le hy.le)
    have hlog : 1+Real.log ((D:ℝ)*(W+2))≤ℓ := by
      dsimp only [ℓ]
      gcongr
    have hlpos := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd (show 1≤(W:ℝ)+2 by linarith))
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlog 2) (Real.sqrt_nonneg _)).trans
    have hs := (le_div_iff₀ (show 0<3*(D:ℝ)*ℓ^4 by positivity)).mp hwy
    have hs' : (D:ℝ)*(W+2)*ℓ^4≤U^2 := by
      calc _ ≤ (D:ℝ)*(3*W)*ℓ^4 := by gcongr <;> linarith
           _ = (W:ℝ)*(3*D*ℓ^4) := by ring
           _ ≤ _ := hs
    have hwb : 0≤(D:ℝ)*(W+2) := by positivity
    apply (sq_le_sq₀ (by positivity) hU₀.le).mp
    rw [mul_pow,Real.sq_sqrt hwb,←pow_mul]
    exact hs'
  · change (L:ℝ)/W+1≤2+6*L*D*ℓ^4/U^2
    by_cases h:W=L
    · rw [←h,div_self hw'.ne'];linarith [show 0≤6*(W:ℝ)*D*ℓ^4/U^2 by positivity]
    have hmin : ⌊y⌋₊≤W := by dsimp [W] at *;omega
    have hyw : y≤2*W := by
      have hh' : (⌊y⌋₊:ℝ)≤W := by exact_mod_cast hmin
      linarith [Nat.lt_floor_add_one y]
    have ht' := (div_le_iff₀ (show 0<3*(D:ℝ)*ℓ^4 by positivity)).mp hyw
    have hbound : (L:ℝ)/W≤6*L*D*ℓ^4/U^2 := by
      rw [div_le_div_iff₀ hw' (sq_pos_of_pos hU₀)]
      nlinarith only [mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg (α:=ℝ) L)]
    linarith

end AnalyticNumberTheory.SieveMethods
