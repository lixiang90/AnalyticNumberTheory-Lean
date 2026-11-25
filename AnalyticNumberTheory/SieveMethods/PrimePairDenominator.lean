import AnalyticNumberTheory.SieveMethods.PrimePairDenominatorMean

/-!
# Uniform removal of the prime divisors of a shift

Factoring each squarefree index into its part supported on the shift and
its coprime part costs exactly the product of the missing local Euler
factors. This gives a denominator estimate uniform in the even shift.
-/

open Finset Real
namespace AnalyticNumberTheory.SieveMethods

/-- Removing the odd prime divisors of `h` from the denominator costs at most
the corresponding Euler factors. -/
theorem primePairDenominator_two_le {h : ℕ} (hh : h≠0) (z : ℝ) :
    primePairDenominator 2 z ≤
      (∏p∈h.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2)))*primePairDenominator h z := by
  classical
  let A := (Icc 1 ⌊z⌋₊).filter (fun n => Squarefree n ∧ n.Coprime 2)
  let T := (Icc 1 ⌊z⌋₊).filter (fun n => Squarefree n ∧ n.Coprime h)
  let P := h.primeFactors.filter (fun p => 2<p)
  let w (p : ℕ) := ((p:ℝ)-2)⁻¹
  let F (t : Finset ℕ × ℕ) := (∏p∈t.1,w p)*(∏p∈t.2.primeFactors,w p)
  let pair (n : ℕ) := ((n.gcd h).primeFactors, n/(n.gcd h))
  have decomp (n : ℕ) (hn : n∈A) : (∏p∈(pair n).1,p)*(pair n).2=n := by
    have hs := (mem_filter.mp hn).2.1
    dsimp [pair];rw [Nat.prod_primeFactors_of_squarefree (hs.squarefree_of_dvd (Nat.gcd_dvd_left n h)),
      Nat.mul_div_cancel' (Nat.gcd_dvd_left n h)]
  have hinj : Set.InjOn pair (A:Set ℕ) := by
    intro x hx y hy he
    rw [← decomp x hx,← decomp y hy,he]
  have hmap : A.image pair⊆P.powerset ×ˢ T := by
    intro t ht;obtain ⟨n,hn,rfl⟩ := mem_image.mp ht
    obtain ⟨hN,hs,hodd⟩ := mem_filter.mp hn
    have hgd := Nat.gcd_dvd_left n h
    have hdiv := Nat.div_dvd_of_dvd hgd
    have hsf := hs.squarefree_of_dvd hdiv
    have hne : n/(n.gcd h)≠0 := hsf.ne_zero
    apply mem_product.mpr
    constructor
    · apply mem_powerset.mpr; intro p hp
      have ht := Nat.mem_primeFactors.mp hp
      have hpn := ht.2.1.trans hgd
      have hph := ht.2.1.trans (Nat.gcd_dvd_right n h)
      have hp2 : p≠2 := by rintro rfl;exact (Nat.prime_two.coprime_iff_not_dvd.mp hodd.symm) hpn
      exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨ht.1,hph,hh⟩,by have := ht.1.two_le;omega⟩
    · refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hne,(Nat.div_le_self ..).trans (mem_Icc.mp hN).2⟩,hsf,?_⟩
      apply (Nat.disjoint_primeFactors hne hh).mp
      rw [Nat.primeFactors_div_gcd hs hh]
      exact disjoint_sdiff_self_left
  have hweight (n : ℕ) (hn : n∈A) : (∏p∈n.primeFactors,w p)=F (pair n) := by
    have hs := (mem_filter.mp hn).2.1
    dsimp [F,pair]
    rw [Nat.primeFactors_gcd hs.ne_zero hh,Nat.primeFactors_div_gcd hs hh]
    have hpart : n.primeFactors\(n.primeFactors∩h.primeFactors)=n.primeFactors\h.primeFactors := by ext; simp
    rw [mul_comm,←hpart,prod_sdiff inter_subset_left]
  have hnonneg (p : ℕ) (hp : p.Prime) : 0≤w p := inv_nonneg.mpr (sub_nonneg.mpr (by exact_mod_cast hp.two_le))
  change ∑n∈A, (∏p∈n.primeFactors,w p) ≤ _
  calc _ = ∑t∈A.image pair,F t := by rw [sum_image hinj];exact sum_congr rfl hweight
       _ ≤ ∑t∈P.powerset ×ˢ T,F t := by
             apply sum_le_sum_of_subset_of_nonneg hmap
             intro t ht _
             have ht' := mem_product.mp ht
             have hs := mem_powerset.mp ht'.1
             exact mul_nonneg (prod_nonneg (fun p hp => hnonneg p (Nat.prime_of_mem_primeFactors (mem_filter.mp (hs hp)).1)))
               (prod_nonneg (fun p hp => hnonneg p (Nat.prime_of_mem_primeFactors hp)))
       _ = _ := by
             change (∑t∈P.powerset ×ˢ T,F t)=(∏p∈P,(1+1/((p:ℝ)-2)))*(∑n∈T,∏p∈n.primeFactors,w p)
             simp only [F,sum_product,←mul_sum,←sum_mul]
             rw [prod_one_add];simp only [one_div,w]

/-- Lower bound for the Selberg denominator with the exact prime-pair
singular factor and an absolute additive error, uniform in the shift. -/
theorem primePairDenominator_lower :
    ∃ L : ℝ, 0≤L ∧ ∀ {z : ℝ}, 2≤z → ∀ {h : ℕ}, h≠0 →
      log z-L ≤ 2*primePairSingularFactor h*primePairDenominator h z := by
  obtain ⟨L,hL,hl⟩ := primePairDenominator_two_lower
  refine ⟨L,hL,fun {z} hz {h} hh => (hl hz).trans ?_⟩
  rw [primePairSingularFactor,← mul_assoc 2 twinPrimeEulerConstant,mul_assoc (2*twinPrimeEulerConstant)]
  exact mul_le_mul_of_nonneg_left (primePairDenominator_two_le hh z) (mul_nonneg (by norm_num) twinPrimeEulerConstant_pos.le)

end AnalyticNumberTheory.SieveMethods
