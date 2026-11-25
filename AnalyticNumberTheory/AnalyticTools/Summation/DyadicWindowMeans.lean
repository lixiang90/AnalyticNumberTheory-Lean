import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # Weighted mean values on expanding symmetric intervals -/
noncomputable section
open Real Finset MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools.Summation

private theorem summable_window_weights (k : ℕ) :
    Summable (fun n : ℕ => ((n:ℝ)+2)^k*(1/2:ℝ)^n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one k (r:=(1/2:ℝ)) (by norm_num)
  have hs := ((summable_nat_add_iff 2).mpr h).mul_left 4
  refine hs.congr fun n => ?_
  simp only [Nat.cast_add,Nat.cast_ofNat,pow_add]
  ring

/-- A quadratic decay on successive annuli controls a weighted mean
uniformly in the outer radius. The unweighted moment is allowed to grow
linearly in the radius times a fixed power of its logarithm. -/
theorem localized_dyadic_mean (k : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ {L A B : ℝ} {f g : ℝ → ℝ}, 0≤L → 0≤A → 0≤B →
    Continuous f → Continuous g → (∀ t,0≤f t) →
    (∀ t,g t≤A*f t) →
    (∀ (j : ℕ) (t : ℝ), 2^j*L≤|t| → g t≤(4*A/(2:ℝ)^(2*j))*f t) →
    (∀ j : ℕ, (∫ t in -(2^j*L)..2^j*L,f t) ≤ B*2^j*((j:ℝ)+1)^k) →
    ∀ n : ℕ, (∫ t in -(2^n*L)..2^n*L,g t) ≤ C*A*B := by
  let w (j : ℕ) := ((j:ℝ)+2)^k*(1/2:ℝ)^j
  have hw (j : ℕ) : 0≤w j := by dsimp [w];positivity
  have hsum : Summable w := summable_window_weights k
  have hm₀ : 0≤∑' j,w j := tsum_nonneg hw
  refine ⟨1+16*∑' j,w j,by positivity,?_⟩
  intro L A B f g hL hA hB hf hg hf₀ hcentral htail hm n
  let u (j : ℕ) := (2:ℝ)^j*L
  let M (j : ℕ) := ∫ t in -u j..u j,g t
  have hu (j : ℕ) : 0≤u j := by dsimp [u];positivity
  have hstep (j : ℕ) : M (j+1) ≤ M j+16*A*B*w j := by
    have hu' : u j≤u (j+1) := by dsimp [u];rw [pow_succ];linarith [mul_nonneg (show 0≤(2:ℝ)^j by positivity) hL]
    let D := 4*A/(2:ℝ)^(2*j)
    have hD : 0≤D := by dsimp [D];positivity
    have hs {a b : ℝ} (hab : a≤b) (ha : -u (j+1)≤a) (hb : b≤u (j+1))
        (hx : ∀ t ∈ Set.Icc a b,u j≤|t|) :
        (∫ t in a..b,g t) ≤ D*(B*2^(j+1)*(((j+1:ℕ):ℝ)+1)^k) := by
      calc _ ≤ ∫ t in a..b,D*f t := intervalIntegral.integral_mono_on hab (hg.intervalIntegrable ..)
                 ((hf.const_mul D).intervalIntegrable ..) (fun t ht => htail j t (hx t ht))
           _ = D*∫ t in a..b,f t := intervalIntegral.integral_const_mul ..
           _ ≤ _ := mul_le_mul_of_nonneg_left ((intervalIntegral.integral_mono_interval ha hab hb
                  (Filter.Eventually.of_forall hf₀) (hf.intervalIntegrable ..)).trans (hm (j+1))) hD
    have hl := hs (a:=-u (j+1)) (b:=-u j) (by linarith) le_rfl (by linarith [hu j])
      (fun t ht => (by linarith [ht.2,neg_le_abs t] : u j≤|t|))
    have hr := hs (a:=u j) (b:=u (j+1)) hu' (by linarith [hu j]) le_rfl
      (fun t ht => ht.1.trans (le_abs_self _))
    have he : M (j+1) = (∫ t in -u (j+1)..-u j,g t)+M j+(∫ t in u j..u (j+1),g t) := by
      dsimp only [M]
      rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable ..) (hg.intervalIntegrable ..),
        intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable ..) (hg.intervalIntegrable ..)]
    have hw' : 2*(D*(B*2^(j+1)*(((j+1:ℕ):ℝ)+1)^k)) = 16*A*B*w j := by
      dsimp [w,D];push_cast
      rw [show 2*j=j+j by omega,pow_add,pow_succ,one_div,inv_pow]
      rw [show (j:ℝ)+1+1=j+2 by ring]
      field_simp;ring
    rw [he,←hw'];linarith only [hl,hr]
  have hall (m : ℕ) : M m ≤ A*B+16*A*B*∑ j∈range m,w j := by
    induction m with
    | zero =>
      simp only [range_zero,sum_empty,mul_zero,add_zero]
      apply (intervalIntegral.integral_mono_on (by linarith [hu 0] : -u 0≤u 0)
        (hg.intervalIntegrable ..) ((hf.const_mul A).intervalIntegrable ..) (fun t _ => hcentral t)).trans
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_zero,zero_add,one_pow,pow_zero,mul_one,u] using hm 0) hA
    | succ m ih =>
      rw [sum_range_succ]
      linarith only [hstep m,ih]
  calc M n ≤ A*B+16*A*B*∑ j∈range n,w j := hall n
       _ ≤ A*B+16*A*B*∑' j,w j := by
             apply add_le_add le_rfl
             exact mul_le_mul_of_nonneg_left (hsum.sum_le_tsum (range n) (fun j _ => hw j)) (by positivity)
       _ = _ := by ring

end AnalyticNumberTheory.AnalyticTools.Summation
