import AnalyticNumberTheory.SieveMethods.HuxleyCharacterLargeValues
import AnalyticNumberTheory.SieveMethods.PrimitiveConductorLcm

/-! # Sparse sampling in families of conductors with a common divisor -/
noncomputable section
open Finset Complex
namespace AnalyticNumberTheory.SieveMethods

/-- The correlation parameter of a nonempty admissible range is positive. -/
theorem one_le_common_conductor_level {b Q : ℕ} (hb : 1≤b) (hbQ : b≤Q) : 1≤Q^2/b := by
  apply (Nat.le_div_iff_mul_le hb).mpr
  simpa [sq] using hbQ.trans (Nat.le_mul_of_pos_left Q (hb.trans hbQ))

/-- In the full sparse mean on any height window, restricting all primitive
conductors to multiples of b replaces Q² by its integer quotient by b. -/
theorem common_conductor_window_mean :
    ∃ C : ℝ,0<C ∧ ∀{b Q : ℕ},1≤b → b≤Q →
      CharacterWindowMean (primitiveConductorMultiples Q b) (fun p n => p.2 n) (Q^2/b) C := by
  obtain ⟨C,hC,H⟩ := full_character_window_mean
  refine ⟨C,hC,?_⟩
  intro b Q hb hbQ L A
  exact H (one_le_common_conductor_level hb hbQ) (primitive_multiple_correlation_family Q hb) A

/-- Huxley's estimate for primitive characters with all conductors
divisible by b. Both the large-value threshold and the height term use
the reduced parameter ⌊Q²/b⌋. -/
theorem common_conductor_large_values :
    ∃c C : ℝ,0<c ∧ 0<C ∧ ∀{b Q : ℕ},1≤b → b≤Q →
      HalfPlaneCharacterLargeValues (primitiveConductorMultiples Q b) (fun p n => p.2 n) (Q^2/b) c C := by
  obtain ⟨c,C,hc,hC,H⟩ := character_large_values_of_correlation
  refine ⟨max c 4,2*C,lt_of_lt_of_le hc (le_max_left c _),by positivity,?_⟩
  intro b Q hb hbQ N hN
  have hD := one_le_common_conductor_level hb hbQ
  exact halfPlane_large_values_of_strip hD hc hC (fun p _ n => p.2.norm_le_one _)
    (H hD (primitive_multiple_correlation_family Q hb)) hN

end AnalyticNumberTheory.SieveMethods
