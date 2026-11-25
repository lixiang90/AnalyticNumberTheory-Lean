import AnalyticNumberTheory.ModularAndPartitions.DedekindCongruences

/-!
# The factor of three in the denominator of a Dedekind sum

The finite sawtooth sum gives integrality after multiplication by
twice the squared modulus. Combining this with reciprocity determines
when the integer numerator is divisible by three.
-/

namespace AnalyticNumberTheory.ModularAndPartitions

/-- Twice the square of the modulus clears all denominators of a Dedekind sum. -/
theorem two_mul_sq_dedekindSum_int (h : ℤ) (k : ℕ) :
    ∃ a : ℤ,2*(k:ℝ)^2*dedekindSum h k=a := by
  rcases Nat.eq_zero_or_pos k with rfl|hk
  · exact ⟨0,by simp⟩
  let A (r : ℕ) : ℤ := if (h:ℝ)*r/k=⌊(h:ℝ)*r/k⌋ then 0
    else (r:ℤ)*(2*h*r-2*k*⌊(h:ℝ)*r/k⌋-k)
  refine ⟨∑ r ∈ Finset.Icc 1 (k-1),A r,?_⟩
  rw [dedekindSum_eq_sum_div_mul h hk,Finset.mul_sum,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  dsimp [A,sawtoothEta]
  split_ifs <;> simp only [Int.cast_zero,Int.cast_mul,Int.cast_sub,Int.cast_natCast,Int.cast_ofNat,Int.fract,mul_zero]
  field_simp [show (k:ℝ)≠0 by positivity]

private theorem three_dvd_numerator_of_not_dvd {h : ℤ} {k : ℕ} (hk : ¬3∣k)
    {m : ℤ} (hm : 6*(k:ℝ)*dedekindSum h k=m) : 3∣m := by
  obtain ⟨a,ha⟩ := two_mul_sq_dedekindSum_int h k
  have H : (k:ℝ)*m=3*a := by linear_combination 3*ha-(k:ℝ)*hm
  have H' : (k:ℤ)*m=3*a := by exact_mod_cast H
  have hk' : ¬(3:ℤ)∣(k:ℤ) := by exact_mod_cast hk
  exact ((show Prime (3:ℤ) by norm_num).dvd_mul.mp ⟨a,H'⟩).resolve_left hk'

/-- For a reduced fraction, three divides the integer `6 k s(h,k)`
precisely when it does not divide the modulus. -/
theorem three_dvd_dedekindSum_numerator_iff {h k : ℕ} (hh : 0<h) (hk : 0<k)
    (hcop : Nat.Coprime h k) {m : ℤ} (hm : 6*(k:ℝ)*dedekindSum h k=m) :
    (3:ℤ)∣m ↔ ¬3∣k := by
  refine ⟨?_,fun h => three_dvd_numerator_of_not_dvd h hm⟩
  intro h₃ hk₃
  have H := dedekindSum_numerator_modEq hh hk hcop (m:=2*m) (by push_cast; linear_combination 2*hm)
  have Hd := Int.modEq_iff_dvd.mp H
  have H₃ : (3:ℤ)∣(h:ℤ)^2+1 := by
    have hk' : (3:ℤ)∣(k:ℤ) := by exact_mod_cast hk₃
    have HM : (3:ℤ)∣(h:ℤ)*(2*m) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h₃ _) _
    simpa using dvd_add (hk'.trans Hd) HM
  have Hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr H₃
  push_cast at Hz
  have hn : ∀ t : ZMod 3,t^2+1≠0 := by decide
  exact hn _ Hz

private theorem gcd_three_dvd_reverse_numerator {h k : ℕ} (hcop : Nat.Coprime h k)
    {m : ℤ} (hm : 6*(h:ℝ)*dedekindSum k h=m) : (Nat.gcd 3 k:ℤ)∣m := by
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left 3 k) with hh|hh
  · rw [hh]; simp
  · rw [hh]
    have hk₃ : 3∣k := hh ▸ Nat.gcd_dvd_right 3 k
    have hh₃ : ¬3∣h := by
      intro H
      have hD := Nat.dvd_gcd H hk₃
      rw [hcop.gcd_eq_one] at hD
      omega
    exact three_dvd_numerator_of_not_dvd hh₃ hm

/-- The reverse Dedekind numerator gains the factor `gcd(3,k)`. -/
theorem dedekindSum_reverse_numerator_dvd {h k : ℕ} (hcop : Nat.Coprime h k)
    {m : ℤ} (hm : 6*(h:ℝ)*dedekindSum k h=m) :
    (Nat.gcd 3 k:ℤ)*k∣(k:ℤ)*m := by
  obtain ⟨v,hv⟩ := gcd_three_dvd_reverse_numerator hcop hm
  refine ⟨v,?_⟩
  rw [hv]; ring

/-- The reciprocity congruence with its full modulus `k*gcd(3,k)`. -/
theorem dedekindSum_numerator_modEq_gcd_three {h k : ℕ} (hh : 0<h) (hk : 0<k)
    (hcop : Nat.Coprime h k) {m : ℤ} (hm : 12*(k:ℝ)*dedekindSum h k=m) :
    (h:ℤ)*m ≡ (h:ℤ)^2+1 [ZMOD (Nat.gcd 3 k:ℤ)*k] := by
  obtain ⟨v,hv⟩ := six_mul_dedekindSum_int (k:ℤ) h
  have HE : (h:ℝ)^2+1-(h:ℝ)*m=(k:ℝ)*(2*v+3*h-k) := by
    linear_combination -(dedekind_reciprocity hh hk hcop)+(h:ℝ)*hm+2*(k:ℝ)*hv
  have HE' : (h:ℤ)^2+1-(h:ℤ)*m=(k:ℤ)*(2*v+3*h-k) := by exact_mod_cast HE
  have h₁ := gcd_three_dvd_reverse_numerator hcop hv
  have h₂ : (Nat.gcd 3 k:ℤ)∣(3:ℤ) := by exact_mod_cast Nat.gcd_dvd_left 3 k
  have h₃ : (Nat.gcd 3 k:ℤ)∣(k:ℤ) := by exact_mod_cast Nat.gcd_dvd_right 3 k
  obtain ⟨v',hh'⟩ := dvd_sub (dvd_add (dvd_mul_of_dvd_right h₁ (2:ℤ))
    (dvd_mul_of_dvd_left h₂ (h:ℤ))) h₃
  apply Int.modEq_iff_dvd.mpr
  exact ⟨v',by rw [HE',hh']; ring⟩

/-- The divisibility criterion for signed representatives, including the unique
reduced fraction with zero numerator and positive modulus. -/
theorem three_dvd_dedekindSum_numerator_iff_int {h : ℤ} {k : ℕ} (hk : 0<k)
    (hcop : IsCoprime h (k:ℤ)) {m : ℤ} (hm : 6*(k:ℝ)*dedekindSum h k=m) :
    (3:ℤ)∣m ↔ ¬3∣k := by
  have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
  cases h with
  | ofNat n =>
    have hc : Nat.Coprime n k := by simpa [Int.gcd] using hg
    by_cases hz : n=0
    · subst n
      have h₁ : k=1 := by simpa using hc
      subst k
      simp at hm
      have hzero : m=0 := by exact_mod_cast hm.symm
      subst m; norm_num
    exact three_dvd_dedekindSum_numerator_iff (by omega) hk hc hm
  | negSucc n =>
    have hc : Nat.Coprime (n+1) k := by simpa [Int.gcd] using hg
    change 6*(k:ℝ)*dedekindSum (-((n+1:ℕ):ℤ)) k=m at hm
    rw [dedekindSum_neg] at hm
    have H := three_dvd_dedekindSum_numerator_iff (Nat.succ_pos n) hk hc (m:= -m)
      (by simp only [Int.cast_neg]; linear_combination -hm)
    simpa using H

/-- The full reciprocity congruence is invariant under negating the
representative of the reduced residue class. -/
theorem dedekindSum_numerator_modEq_gcd_three_int {h : ℤ} {k : ℕ} (hk : 0<k)
    (hcop : IsCoprime h (k:ℤ)) {m : ℤ} (hm : 12*(k:ℝ)*dedekindSum h k=m) :
    h*m ≡ h^2+1 [ZMOD (Nat.gcd 3 k:ℤ)*k] := by
  have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
  cases h with
  | ofNat n =>
    have hc : Nat.Coprime n k := by simpa [Int.gcd] using hg
    by_cases hz : n=0
    · subst n
      have h₁ : k=1 := by simpa using hc
      subst k
      simp [Int.ModEq]
    exact dedekindSum_numerator_modEq_gcd_three (by omega) hk hc hm
  | negSucc n =>
    have hc : Nat.Coprime (n+1) k := by simpa [Int.gcd] using hg
    change 12*(k:ℝ)*dedekindSum (-((n+1:ℕ):ℤ)) k=m at hm
    rw [dedekindSum_neg] at hm
    have H := dedekindSum_numerator_modEq_gcd_three (Nat.succ_pos n) hk hc (m:= -m)
      (by simp only [Int.cast_neg]; linear_combination -hm)
    change (-((n+1:ℕ):ℤ))*m ≡ (-((n+1:ℕ):ℤ))^2+1 [ZMOD _]
    simpa only [neg_mul,mul_neg,neg_sq] using H

end AnalyticNumberTheory.ModularAndPartitions
