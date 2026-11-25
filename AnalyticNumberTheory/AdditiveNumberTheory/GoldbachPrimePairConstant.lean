import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach
import AnalyticNumberTheory.SieveMethods.PrimePairEight

/-! # The binary Goldbach singular series and the prime-pair sieve constant -/
noncomputable section
open Finset Real
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- The binary Goldbach singular series for a positive even integer is twice the
local factor in the prime-pair sieve, including every prime divisor of the integer. -/
theorem goldbachBinarySingularSeries_eq_twice_primePair {N : ℕ} (hn : 0<N) (he : Even N) :
    goldbachBinarySingularSeries N = 2*primePairSingularFactor N := by
  classical
  let S := N.primeFactors.filter (fun p => 2<p)
  let w (p : ℕ) : ℝ := 1+1/((p:ℝ)-2)
  have hf : HasProd (fun p : Nat.Primes => ∏ q ∈ S, if p.val=q then w q else 1) (∏ q ∈ S, w q) := by
    apply hasProd_prod
    intro q hq
    let p : Nat.Primes := ⟨q,Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1⟩
    apply (hasProd_ite_eq p (w q)).congr_fun
    intro u
    by_cases hu : u=p
    · subst u
      change (if q=q then w q else 1) = (if p=p then w q else 1)
      rw [if_pos rfl,if_pos rfl]
    · have hv : u.val≠q := fun h => hu (Subtype.ext h)
      simp [hu,hv]
  rw [(goldbachBinarySingularSeries_eq_tprod hn).2]
  have h := hasProd_goldbach_lower_factor.mul hf
  have h' : HasProd (fun p : Nat.Primes => 1 + singularTermBinary p N) ((2*twinPrimeEulerConstant)*(∏ q∈S,w q)) := by
    apply h.congr_fun
    intro p
    rw [prod_ite_eq, singularTermBinary_prime p.2]
    by_cases hp2 : p.val=2
    · have hpN : p.val ∣ N := hp2 ▸ even_iff_two_dvd.mp he
      have hnot : p.val∉S := fun h => (by have := (mem_filter.mp h).2; omega)
      simp only [if_pos hp2, if_neg hnot, if_pos hpN, mul_one, hp2]
      norm_num [even_iff_two_dvd.mp he]
    · have hp3 : 2<p.val := by have := p.2.two_le; omega
      have hpR : 2<(p.val:ℝ) := by exact_mod_cast hp3
      by_cases hpN : p.val∣N
      · have hmem : p.val ∈ S := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨p.2,hpN,hn.ne'⟩,hp3⟩
        simp only [hp2,if_false,hpN,hmem,if_true,w]
        field_simp [show (p.val:ℝ)-2≠0 by linarith,show (p.val:ℝ)-1≠0 by linarith]
        <;> ring
      · have hnot : p.val∉S := fun h => hpN (Nat.dvd_of_mem_primeFactors (mem_filter.mp h).1)
        simp [hp2,hnot,hpN,sub_eq_add_neg]
  exact h'.tprod_eq.trans (by dsimp [primePairSingularFactor,S,w]; ring)

/-- The coefficient eight in the prime-pair convention becomes four times the
binary singular series in the ordered Goldbach representation bound. -/
theorem goldbachRepCount_le_four_mul_singularSeries :
    ∃ C : ℝ, 0<C ∧ ∀ {N : ℕ}, 3≤N → Even N →
      (goldbachRepCount N:ℝ) ≤ 4*goldbachBinarySingularSeries N*((N:ℝ)/(log N)^2)*
        (1+C*(log (log N)/log N)) := by
  obtain ⟨C,hC,H⟩ := goldbachRepCount_eight
  refine ⟨C,hC,fun {N} hN he => ?_⟩
  rw [goldbachBinarySingularSeries_eq_twice_primePair (by omega) he]
  convert H hN he using 1 <;> ring

end AnalyticNumberTheory.AdditiveNumberTheory
