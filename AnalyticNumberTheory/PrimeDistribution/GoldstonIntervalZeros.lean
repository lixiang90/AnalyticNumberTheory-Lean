import AnalyticNumberTheory.AnalyticTools.Summation.ReciprocalWindow
import AnalyticNumberTheory.PrimeDistribution.GoldstonTruncation
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalZeroSums

/-! # Sharp zero sums over a short interval under RH -/

noncomputable section

open Finset Filter Complex Real
open scoped Classical Topology
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.PrimeDistribution

/-- Between two heights, reciprocal summation over both signs of the
ordinates costs only the logarithm of their ratio times log T. -/
theorem reciprocal_zero_window_bound :
    ∃ K > 0, ∀ {U T : ℝ}, 2 ≤ U → U ≤ T →
      (∑ z ∈ nontrivialZerosUpTo T with U < |z.im|, (zeroMultiplicity z:ℝ)/|z.im|) ≤
        K*Real.log T*(1+Real.log (T/U)) := by
  obtain ⟨K,hK,H⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  refine ⟨K,hK,?_⟩
  intro U T hU hUT
  let S := (nontrivialZerosUpTo T).filter (fun z : ℂ => U < |z.im|)
  apply sum_div_height_window_le S (fun z : ℂ => |z.im|) (fun z => (zeroMultiplicity z:ℝ))
    (by linarith) hUT _ (fun _ _ => Nat.cast_nonneg _) _
  · intro z hz
    obtain ⟨ht,hu⟩ := mem_filter.mp hz
    exact ⟨hu.le,(mem_nontrivialZerosUpTo.mp ht).2.2.2⟩
  · intro u hu
    have hsub : S.filter (fun z : ℂ => |z.im| ≤ u) ⊆ nontrivialZerosUpTo u := by
      intro z hz
      obtain ⟨hz,hzu⟩ := mem_filter.mp hz
      obtain ⟨h₀,h₁,h₂,_⟩ := mem_nontrivialZerosUpTo.mp (mem_filter.mp hz).1
      exact mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,hzu⟩
    have hu₀ : 0 < u := by linarith [hu.1]
    calc
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => Nat.cast_nonneg (α:=ℝ) (zeroMultiplicity z))
      _ ≤ K*u*Real.log u := H u (hU.trans hu.1)
      _ ≤ K*u*Real.log T := mul_le_mul_of_nonneg_left (Real.log_le_log hu₀ hu.2) (by positivity)
      _ = _ := by ring

/-- Under RH, split the increment of the sharp zero sum at a free height
U. Differentiation controls the low zeros and reciprocal summation controls
the window U < |γ| ≤ T. -/
theorem sharpZetaZeroSum_increment_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C > 0, ∀ {x h U T : ℝ}, 0 < x → 0 ≤ h → h ≤ x → 2 ≤ U → U ≤ T →
      ‖sharpZetaZeroSum (x+h) T - sharpZetaZeroSum x T‖ ≤
        C*((h/Real.sqrt x)*U*Real.log T+Real.sqrt x*Real.log T*(1+Real.log (T/U))) := by
  obtain ⟨K,hK,HC⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  obtain ⟨D,hD,HW⟩ := reciprocal_zero_window_bound
  refine ⟨K+3*D,by positivity,?_⟩
  intro x h U T hx hh hhx hU hUT
  let S := nontrivialZerosUpTo T
  let m (z:ℂ) : ℝ := zeroMultiplicity z
  let w (z:ℂ) := ((x+h:ℝ):ℂ)^z/z-(x:ℂ)^z/z
  let r := Real.sqrt x
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hy := add_pos_of_pos_of_nonneg hx hh
  have hU0 : 0 < U := by linarith
  have hTlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hq : 0 ≤ Real.log (T/U) := Real.log_nonneg ((one_le_div hU0).mpr hUT)
  have hs (z : ℂ) (hz : z ∈ S) :
      m z*‖w z‖ ≤ if |z.im| ≤ U then m z*(h/r) else 3*r*(m z/|z.im|) := by
    obtain ⟨hzero,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
    have he := hRH z hzero h₀ h₁
    have hm : 0 ≤ m z := Nat.cast_nonneg _
    split_ifs with hcut
    · apply mul_le_mul_of_nonneg_left _ hm
      have hb := short_interval_cpow_bound hx hh h₀ h₁
      rw [he,show (1/2:ℝ)-1 = -(1/2) by ring,Real.rpow_neg hx.le,←Real.sqrt_eq_rpow] at hb
      simpa [w,r,div_eq_mul_inv] using hb
    · have him : 0 < |z.im| := hU0.trans (lt_of_not_ge hcut)
      have hyroot : Real.sqrt (x+h) ≤ 2*r := by
        nlinarith [Real.sq_sqrt hy.le,Real.sq_sqrt hx.le,Real.sqrt_nonneg (x+h),Real.sqrt_nonneg x]
      have hb : ‖w z‖ ≤ (3*r)/|z.im| := by
        apply (norm_sub_le _ _).trans
        rw [norm_div,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.norm_cpow_eq_rpow_re_of_pos hx,
          he,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,←add_div]
        apply div_le_div₀ (by positivity) (by linarith) him (Complex.abs_im_le_norm _)
      calc _ ≤ m z*((3*r)/|z.im|) := mul_le_mul_of_nonneg_left hb hm
           _ = _ := by ring
  have hsub : S.filter (fun z : ℂ => |z.im| ≤ U) ⊆ nontrivialZerosUpTo U := by
    intro z hz
    obtain ⟨hz,hzu⟩ := mem_filter.mp hz
    obtain ⟨h₀,h₁,h₂,_⟩ := mem_nontrivialZerosUpTo.mp hz
    exact mem_nontrivialZerosUpTo.mpr ⟨h₀,h₁,h₂,hzu⟩
  have hlo : (∑ z ∈ S with |z.im| ≤ U,m z) ≤ K*U*Real.log T :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
      ((HC U hU).trans (mul_le_mul_of_nonneg_left (Real.log_le_log hU0 hUT) (by positivity)))
  have hsum : (∑ z ∈ S,if |z.im| ≤ U then m z*(h/r) else 3*r*(m z/|z.im|)) =
      (∑ z ∈ S with |z.im| ≤ U,m z)*(h/r) + 3*r*(∑ z ∈ S with U < |z.im|,m z/|z.im|) := by
    rw [sum_mul,mul_sum,←sum_filter_add_sum_filter_not S (fun z : ℂ => |z.im| ≤ U)
      (fun z => if |z.im| ≤ U then m z*(h/r) else 3*r*(m z/|z.im|))]
    apply congrArg₂ (·+·)
    · exact sum_congr rfl fun z hz => ite_eq_left (mem_filter.mp hz).2
    · simp only [not_le]
      exact sum_congr rfl fun z hz => ite_eq_right (not_le.mpr (mem_filter.mp hz).2)
  have heq : sharpZetaZeroSum (x+h) T - sharpZetaZeroSum x T =
      ∑ z ∈ S,(zeroMultiplicity z:ℂ)*w z := by
    dsimp only [sharpZetaZeroSum,S,w]; rw [←sum_sub_distrib]
    apply sum_congr rfl; intro z _; ring
  rw [heq]
  calc
    _ ≤ ∑ z ∈ S,‖(zeroMultiplicity z:ℂ)*w z‖ := norm_sum_le _ _
    _ = ∑ z ∈ S,m z*‖w z‖ := by simp [m]
    _ ≤ _ := sum_le_sum hs
    _ = _ := hsum
    _ ≤ (K*U*Real.log T)*(h/r)+3*r*(D*Real.log T*(1+Real.log (T/U))) :=
        add_le_add (mul_le_mul_of_nonneg_right hlo (by positivity))
          (mul_le_mul_of_nonneg_left (HW hU hUT) (by positivity))
    _ ≤ _ := by
      change _ ≤ (K+3*D)*((h/r)*U*Real.log T+r*Real.log T*(1+Real.log (T/U)))
      nlinarith only [mul_nonneg (by positivity : 0 ≤ 3*D) (show 0 ≤ (h/r)*U*Real.log T by positivity),
        mul_nonneg hK.le (show 0 ≤ r*Real.log T*(1+Real.log (T/U)) by positivity)]

end AnalyticNumberTheory.PrimeDistribution
