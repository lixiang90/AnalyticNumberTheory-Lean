import AnalyticNumberTheory.ModularAndPartitions.DedekindSums

/-!
# Arithmetic congruences of Dedekind sums

Reciprocity and integrality determine the residue of the numerator.
This detects exactly which coprime pairs give a vanishing Dedekind sum.
-/

namespace AnalyticNumberTheory.ModularAndPartitions

/-- The integer `12 k s(h,k)`, multiplied by `h`, is congruent to
`h²+1` modulo `k`. -/
theorem dedekindSum_numerator_modEq {h k : ℕ} (hh : 0<h) (hk : 0<k)
    (hcop : Nat.Coprime h k) {m : ℤ} (hm : 12*(k:ℝ)*dedekindSum h k=m) :
    (h:ℤ)*m ≡ (h:ℤ)^2+1 [ZMOD (k:ℤ)] := by
  obtain ⟨v,hv⟩ := twelve_mul_dedekindSum_int (k:ℤ) h
  have he := dedekind_reciprocity hh hk hcop
  have H : (h:ℝ)^2+1-(h:ℝ)*m=(k:ℝ)*((v:ℝ)+3*h-k) := by
    linear_combination -he + (h:ℝ)*hm + (k:ℝ)*hv
  have H' : (h:ℤ)^2+1-(h:ℤ)*m=(k:ℤ)*(v+3*h-k) := by exact_mod_cast H
  exact Int.modEq_iff_dvd.mpr ⟨_,H'⟩

private theorem dedekind_zero_nat {h k : ℕ} (hk : 0<k) (hcop : Nat.Coprime h k)
    (hzero : dedekindSum h k=0) : (h:ℤ)^2 ≡ -1 [ZMOD (k:ℤ)] := by
  rcases Nat.eq_zero_or_pos h with rfl|hh
  · simp only [Nat.coprime_zero_left] at hcop
    simp [hcop,Int.ModEq]
  have HE := dedekindSum_numerator_modEq hh hk hcop (m:=0) (by rw [hzero]; simp)
  rw [Int.modEq_iff_dvd] at HE ⊢
  obtain ⟨v,hv⟩ := HE
  exact ⟨-v,by push_cast at hv ⊢; linear_combination -hv⟩

/-- Exact zero criterion for a reduced Dedekind sum with positive modulus. -/
theorem dedekindSum_eq_zero_iff {h : ℤ} {k : ℕ} (hk : 0<k) (hcop : IsCoprime h (k:ℤ)) :
    dedekindSum h k=0 ↔ h^2 ≡ -1 [ZMOD (k:ℤ)] := by
  refine ⟨fun hzero => ?_,dedekindSum_eq_zero_of_sq_modEq_neg_one⟩
  have hg : Int.gcd h k=1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  cases h with
  | ofNat n =>
    exact dedekind_zero_nat hk (by simpa [Int.gcd] using hg) hzero
  | negSucc n =>
    have hpos : dedekindSum ((n+1:ℕ):ℤ) k=0 := by
      change dedekindSum (-((n+1:ℕ):ℤ)) k=0 at hzero
      rw [dedekindSum_neg,neg_eq_zero] at hzero; exact hzero
    have H := dedekind_zero_nat hk (h:=n+1) (by simpa [Int.gcd] using hg) hpos
    change (-((n+1:ℕ):ℤ))^2 ≡ -1 [ZMOD (k:ℤ)]
    rw [neg_sq]; exact H

end AnalyticNumberTheory.ModularAndPartitions
