import AnalyticNumberTheory.RiemannZeta.LogarithmicBlockGrowth
import AnalyticNumberTheory.RiemannZeta.LittlewoodZeroFreeRegion

/-!
# Arbitrarily small zeta growth exponents relative to the strip width

The order of logarithmic differencing is chosen before the width of the
strip. The remaining logarithm in the block bound is then absorbed by
a positive power of the height.
-/
open Real Filter
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

/-- Power savings for each fixed polynomial range of logarithmic
frequencies imply Littlewood's strip growth condition. -/
theorem littlewood_strip_growth_of_logarithmic_blocks (H : LogarithmicBlockCancellation) :
    LittlewoodStripGrowth := by
  intro ε hε
  let J := ⌈2/ε⌉₊+1
  have hJ : 1≤J := Nat.succ_pos _
  have hj : 0<(J:ℝ) := by exact_mod_cast hJ
  have hJe : 2/ε≤(J:ℝ) := (Nat.le_ceil _).trans (by dsimp [J]; push_cast; linarith)
  have hJε := (div_le_iff₀ hε).mp hJe
  obtain ⟨κ,C,hκ,hC,hblock⟩ := H J hJ
  let η := min κ (1/4)
  have hη : 0<η := lt_min hκ (by norm_num)
  obtain ⟨D,hD,hgrowth⟩ := zeta_strip_bound_from_blocks J hJ hη (min_le_left ..) (min_le_right ..) hC @hblock
  let d := ε*η-η/J
  have hd : 0<d := by
    dsimp [d]; apply sub_pos.mpr; rw [div_lt_iff₀ hj]
    nlinarith only [mul_lt_mul_of_pos_right (show 1<(J:ℝ)*ε by linarith) hη]
  have hlog := (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero
  have hconst : Tendsto (fun T : ℝ => (T^d)⁻¹) atTop (𝓝 0) := (tendsto_rpow_atTop hd).inv_tendsto_atTop
  have h0 : Tendsto (fun T : ℝ => D*((T^d)⁻¹+Real.log T/T^d)) atTop (𝓝 0) := by
    simpa using (hconst.add hlog).const_mul D
  refine ⟨η,hη,min_le_right ..,?_⟩
  filter_upwards [eventually_ge_atTop (256:ℝ),h0.eventually (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with T hT hs
  intro z hlo _ ht₁ ht₂
  have htp : 0<T := by linarith
  have hpow := Real.rpow_pos_of_pos htp d
  have hfactor : D*(1+Real.log T)≤T^d := by
    apply (div_le_one hpow).mp
    change D*((T^d)⁻¹+Real.log T/T^d)<1 at hs
    convert hs.le using 1; ring
  exact (hgrowth hT z hlo ht₁ ht₂).trans ((mul_le_mul_of_nonneg_right hfactor
    (Real.rpow_nonneg htp.le (η/J))).trans_eq (by rw [←Real.rpow_add htp]; congr 1; dsimp [d]; ring))

end AnalyticNumberTheory.RiemannZeta
