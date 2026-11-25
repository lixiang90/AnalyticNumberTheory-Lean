import AnalyticNumberTheory.SieveMethods.SelbergSharpInterval

/-!
# A finite-prime lower bound for the Selberg denominator

Separating the primes of a fixed squarefree modulus strengthens the elementary
harmonic lower bound. Each divisor of the modulus indexes one disjoint class
of squarefree denominators, characterized by its greatest common divisor with it.
-/

open Finset Real
namespace AnalyticNumberTheory.SieveMethods

/-- Harmonic sum restricted to integers coprime to a fixed modulus. -/
noncomputable def coprimeHarmonicSum (k M : ℕ) : ℝ :=
  ∑m∈(Icc 1 M).filter (fun n => n.Coprime k),(m:ℝ)⁻¹

/-- The elementary harmonic comparison with all local factors at the primes of k retained. -/
theorem selbergDenominator_ge_small_prime_model (k M : ℕ) (hk : Squarefree k) :
    (∑d∈k.divisors,(d.totient:ℝ)⁻¹*coprimeHarmonicSum k (M/d))≤selbergDenominator M := by
  let S := (Icc 1 M).filter Squarefree
  let T (d : ℕ) := ((Icc 1 (M/d)).filter (fun n => n.Coprime k)).filter Squarefree
  have hsplit : (∑s∈S,(s.totient:ℝ)⁻¹)=∑d∈k.divisors,∑s∈S.filter (fun n => n.gcd k=d),(s.totient:ℝ)⁻¹ := by
    rw [sum_fiberwise_of_maps_to]; intro i _;exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,hk.ne_zero⟩
  change _ ≤ selbergDenominator (M:ℝ)
  rw [selbergDenominator,Nat.floor_natCast]
  change _ ≤ ∑s∈S,(s.totient:ℝ)⁻¹
  rw [hsplit]
  refine sum_le_sum fun d hd => ?_
  obtain ⟨hdk,_⟩ := Nat.mem_divisors.mp hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdinj : Function.Injective (fun m : ℕ => d*m) := fun _ _ he => Nat.eq_of_mul_eq_mul_left hdpos he
  have hget (m : ℕ) (hm : m∈T d) : m.Coprime k ∧ m.Coprime d ∧ Squarefree m := by
    have h := (mem_filter.mp (mem_filter.mp hm).1).2
    exact ⟨h,h.coprime_dvd_right hdk,(mem_filter.mp hm).2⟩
  have hmaps : (T d).image (fun m => d*m)⊆S.filter (fun n => n.gcd k=d) := by
    intro s hs
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hs
    obtain ⟨hc,hc',hsq⟩ := hget m hm
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp (mem_filter.mp (mem_filter.mp hm).1).1
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos h₁,?_⟩,?_⟩,?_⟩
    · rw [mul_comm];exact (Nat.le_div_iff_mul_le hdpos).mp h₂
    · exact (Nat.squarefree_mul hc'.symm).mpr ⟨hk.squarefree_of_dvd hdk,hsq⟩
    · have hred := hc.coprime_dvd_right (Nat.div_dvd_of_dvd hdk)
      conv_lhs => rhs; rw [←Nat.mul_div_cancel' hdk]
      rw [Nat.gcd_mul_left];simpa using congrArg (d*·) hred.gcd_eq_one
  calc
    _ ≤ (d.totient:ℝ)⁻¹*∑s∈T d,(s.totient:ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_squarefree_coprime_inv_totient_ge_harmonic (M/d) k) (by positivity)
    _ = ∑s∈(T d).image (fun m => d*m),(s.totient:ℝ)⁻¹ := by
      rw [mul_sum,sum_image (g:=fun m : ℕ => d*m) (fun _ _ _ _ h => hdinj h)]
      refine sum_congr rfl fun m hm => ?_
      rw [Nat.totient_mul (hget m hm).2.1.symm,Nat.cast_mul,mul_inv]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hmaps (fun _ _ _ => by positivity)

end AnalyticNumberTheory.SieveMethods
