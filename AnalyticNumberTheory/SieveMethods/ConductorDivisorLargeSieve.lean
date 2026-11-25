import AnalyticNumberTheory.SieveMethods.LargeSieve
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveConductorSums

/-!
# The primitive inducers of all characters of one modulus

Reduced fractions with denominators dividing q belong to the grid of
spacing 1/q. The primitive character energies at those denominators can
therefore share one additive large-sieve bound.
-/
noncomputable section
open Real Finset Complex DirichletCharacter
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

private theorem common_denominator_spacing {q : ℕ} (hq : 1≤q) {p r : ℕ×ℕ}
    (hp : p∈fareyPairs q) (hr : r∈fareyPairs q) (hn : p≠r)
    (hdp : p.1∣q) (hdr : r.1∣q) :
    (q:ℝ)⁻¹≤distToInt (fareyFraction p-fareyFraction r) := by
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq
  have hm (i:ℕ×ℕ) (hi:i.1∣q) :
      (q:ℝ)*fareyFraction i=(((q/i.1)*i.2:ℕ):ℝ) := by
    have h : (q:ℝ)=i.1*((q/i.1:ℕ):ℝ) := by exact_mod_cast (Nat.mul_div_cancel' hi).symm
    have hn : (i.1:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos hi hq).ne'
    dsimp [fareyFraction];push_cast;field_simp
    linear_combination (i.2:ℝ)*h
  let t := fareyFraction p-fareyFraction r
  let m := round t
  let v : ℤ := ((q/p.1)*p.2:ℕ)-(((q/r.1)*r.2:ℕ):ℤ)-m*(q:ℤ)
  have he : (q:ℝ)*(t-m)=v := by
    dsimp only [t,v]
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,Nat.cast_mul] at hm ⊢
    linarith only [hm p hdp,hm r hdr]
  have hz : v≠0 := by
    intro hv
    rw [hv,Int.cast_zero] at he
    have ht := (mul_eq_zero.mp he).resolve_left hq'.ne'
    have hh := farey_pair_spacing hp hr hn
    change _≤|t-m| at hh
    rw [ht,abs_zero] at hh
    have : 0<(p.1:ℝ)*(r.1:ℝ) := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hdp hq))
      (Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hdr hq))
    exact (inv_pos.mpr this).not_ge hh
  have hx : (1:ℝ)≤|(v:ℝ)| := by
    have hh : (1:ℝ)≤v.natAbs := by exact_mod_cast (by omega : 1≤v.natAbs)
    simpa [Int.cast_abs] using hh
  rw [←he,abs_mul,abs_of_pos hq'] at hx
  change (q:ℝ)⁻¹≤|t-m|
  exact (inv_le_iff_one_le_mul₀ hq').mpr (by linarith only [hx])

/-- Sum of the primitive character energies over all divisors of q, with
the sharper factor q from the additive grid of common denominator q. -/
theorem primitive_divisors_large_sieve (a : ℕ→ℂ) (M : ℕ) {N q : ℕ} (hN : 1≤N) (hq : 1≤q) :
    (∑ d∈q.divisors,∑χ∈(univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.IsPrimitive),
      ‖∑n∈Ioc M (M+N),a n*χ n‖^2)≤((N:ℝ)-1+q)*∑n∈Ioc M (M+N),‖a n‖^2 := by
  let U (d:ℕ) := (range d).filter (fun j => j.Coprime d)
  let J := q.divisors.sigma U
  let f (i:Σ _ : ℕ,ℕ) := (i.1,i.2)
  have hmem (i) (hi:i∈J) : f i∈fareyPairs q := by
    obtain ⟨hd,hj⟩ := mem_sigma.mp hi
    exact mem_biUnion.mpr ⟨i.1,mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩,
      mem_image.mpr ⟨i.2,hj,rfl⟩⟩
  have hsp : WellSpacedModOne J (fun i => fareyFraction (f i)) (q:ℝ)⁻¹ := by
    have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
    refine ⟨inv_pos.mpr (by linarith),inv_le_one_of_one_le₀ hq₁,?_⟩
    intro i hi j hj hne
    have hne' : f i≠f j := by rintro he;apply hne;cases i;cases j;simpa [f] using he
    exact common_denominator_spacing hq (hmem i hi) (hmem j hj) hne'
      (Nat.dvd_of_mem_divisors (mem_sigma.mp hi).1) (Nat.dvd_of_mem_divisors (mem_sigma.mp hj).1)
  have hb := analytic_large_sieve J (fun i => fareyFraction (f i)) hsp a M hN
  simp only [J,Finset.sum_sigma,f,fareyFraction,inv_inv] at hb
  apply le_trans _ hb
  apply sum_le_sum;intro d hd
  have hd' := Nat.pos_of_mem_divisors hd
  have hφ : (0:ℝ)<d.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd')
  apply le_trans _ (character_sum_le_trigPoly_sum a M N d hd')
  exact le_mul_of_one_le_left (sum_nonneg (fun _ _ => sq_nonneg _))
    ((one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le d))

/-- Replacing each character modulo q by its primitive inducer gives an
unweighted mean square at most (N−1+q) times the coefficient energy. -/
theorem inducing_characters_large_sieve (a : ℕ→ℂ) (M : ℕ) {N q : ℕ} [NeZero q] (hN : 1≤N) :
    (∑χ : DirichletCharacter ℂ q,‖∑n∈Ioc M (M+N),a n*χ.primitiveCharacter n‖^2)≤
      ((N:ℝ)-1+q)*∑n∈Ioc M (M+N),‖a n‖^2 := by
  apply le_trans _ (primitive_divisors_large_sieve a M hN NeZero.one_le)
  rw [sum_by_primitive_conductor,←sum_attach q.divisors]
  apply le_of_eq;apply sum_congr rfl;intro d _
  let hd := Nat.dvd_of_mem_divisors d.property
  apply sum_congr rfl;intro ψ hψ
  have hψ' := (mem_filter.mp hψ).2
  congr 2
  apply sum_congr rfl;intro n _
  congr 1
  have he := primitiveCharacter_changeLevel_apply hd ψ (n:ℤ)
  have he' : ψ.primitiveCharacter (n:ℤ)=ψ (n:ℤ) := by
    by_cases h : IsCoprime (n:ℤ) (d.val:ℤ)
    · exact primitiveCharacter_apply_of_isCoprime ψ h
    · have h0 := (apply_eq_zero_iff ψ _).mpr h
      have h0' : ψ.primitiveCharacter (n:ℤ)=0 := by
        rw [apply_eq_zero_iff];rwa [(isPrimitive_def ψ).mp hψ']
      rw [h0,h0']
  simpa using he.trans he'

end AnalyticNumberTheory.SieveMethods
