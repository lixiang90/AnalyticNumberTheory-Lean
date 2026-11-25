import AnalyticNumberTheory.PrimeDistribution.FixedModulusZeroWeights
import AnalyticNumberTheory.PrimeDistribution.PrimitiveFamilyZeroPowerSum

/-! # Fixed-modulus density estimates with the power weight of the explicit formula -/

noncomputable section

open Complex Real Finset
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.PrimeDistribution

private lemma affine_rpow_endpoints {x H l r σ : ℝ} (hx : 0 < x) (hH : 0 < H) (a b : ℝ)
    (hs : σ ∈ Set.Icc l r) :
    x^σ * H^(a+b*σ) ≤ max (x^l * H^(a+b*l)) (x^r * H^(a+b*r)) := by
  have he (t : ℝ) : x^t*H^(a+b*t) = Real.exp ((Real.log x+b*Real.log H)*t+a*Real.log H) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hH, ← Real.exp_add]
    congr 1
    ring
  by_cases h : 0 ≤ Real.log x+b*Real.log H
  · apply le_max_of_le_right
    rw [he, he]
    exact Real.exp_le_exp.mpr (add_le_add (mul_le_mul_of_nonneg_left hs.2 h) le_rfl)
  · apply le_max_of_le_left
    rw [he, he]
    exact Real.exp_le_exp.mpr (add_le_add (mul_le_mul_of_nonpos_left hs.1 (le_of_not_ge h)) le_rfl)

/-- Interpolating Ingham's exponent separately on either side of four fifths
gives the three powers used to bound the mean twisted Chebyshev sum. -/
theorem ingham_power_weight_three_term {x H σ : ℝ} (hx : 0 < x) (hH : 1 ≤ H)
    (hs : σ ∈ Set.Icc (1/2 : ℝ) 1) :
    x^σ*H^(inghamExponent σ) ≤ Real.sqrt x*H + x^(4/5 : ℝ)*H^(3/5 : ℝ) + x := by
  have hH₀ := zero_lt_one.trans_le hH
  have hfirst := mul_nonneg (Real.sqrt_nonneg x) hH₀.le
  have hmiddle := mul_nonneg (Real.rpow_nonneg hx.le (4/5)) (Real.rpow_nonneg hH₀.le (3/5))
  by_cases hm : σ ≤ 4/5
  · have ha : inghamExponent σ ≤ 5/3+(-4/3)*σ := by linarith [inghamExponent_le_affine hs.2]
    have hu := affine_rpow_endpoints hx hH₀ (5/3) (-4/3) (show σ ∈ Set.Icc (1/2 : ℝ) (4/5) from ⟨hs.1,hm⟩)
    have hl : x^(1/2 : ℝ)*H^((5/3 : ℝ)+(-4/3)*(1/2)) = Real.sqrt x*H := by
      rw [show (5/3 : ℝ)+(-4/3)*(1/2) = 1 by norm_num, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hr : H^((5/3 : ℝ)+(-4/3)*(4/5)) = H^(3/5 : ℝ) := by norm_num
    rw [hl, hr] at hu
    have hcomp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH ha) (Real.rpow_nonneg hx.le σ)
    exact (hcomp.trans hu).trans (max_le (by linarith only [hfirst, hmiddle, hx.le])
      (by linarith only [hfirst, hmiddle, hx.le]))
  · have ha : inghamExponent σ ≤ 3+(-3)*σ := by
      unfold inghamExponent
      apply (div_le_iff₀ (by linarith [hs.2])).mpr
      nlinarith only [sq_nonneg (1-σ)]
    have hu := affine_rpow_endpoints hx hH₀ 3 (-3) (show σ ∈ Set.Icc (4/5 : ℝ) 1 from ⟨le_of_not_ge hm,hs.2⟩)
    have hl : H^((3 : ℝ)+(-3)*(4/5)) = H^(3/5 : ℝ) := by norm_num
    have hr : x^(1 : ℝ)*H^((3 : ℝ)+(-3)*1) = x := by norm_num
    rw [hl, hr] at hu
    have hcomp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH ha) (Real.rpow_nonneg hx.le σ)
    exact (hcomp.trans hu).trans (max_le (by linarith only [hfirst, hmiddle, hx.le])
      (by linarith only [hfirst, hmiddle, hx.le]))

/-- Fixed-modulus power sum over critical-strip zeros. With `H=qT` its three
terms are `√x H`, `x^(4/5) H^(3/5)`, and `x`. -/
theorem fixed_modulus_zero_power_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {x T : ℝ}, 2 ≤ x → 2 ≤ T →
      modulusZeroWeight q T (fun z => x^z.re) ≤
        C*(Real.sqrt x*((q : ℝ)*T) + x^(4/5 : ℝ)*((q : ℝ)*T)^(3/5 : ℝ) + x)*
          (1+Real.log x)*(1+Real.log ((q : ℝ)*T))^8 := by
  obtain ⟨A,hA,HA⟩ := modulusDensityCount_trivial
  obtain ⟨B,hB,HB⟩ := modulusDensityCount_ingham_log_eight
  refine ⟨A+B, by positivity, ?_⟩
  intro q _ x T hx hT
  let H := (q : ℝ)*T
  let L := 1+Real.log H
  let M := Real.sqrt x*H+x^(4/5 : ℝ)*H^(3/5 : ℝ)+x
  let S := modulusZeros q T
  let w := fun p : (Σ _ : DirichletCharacter ℂ q, ℂ) => (characterZeroMultiplicity p.1 p.2 : ℝ)
  have hx₀ : 0 < x := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hq (by linarith)
  have hH₀ := zero_lt_one.trans_le hH
  have hlog₀ := Real.log_nonneg hH
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hxlog := Real.log_nonneg (show 1 ≤ x by linarith)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hβ (p) (hp : p ∈ S) := (mem_characterStripZeros p.1).mp (mem_sigma.mp hp).2
  have htail (σ : ℝ) (hs : σ ∈ Set.Icc (1/2 : ℝ) 1) :
      x^σ*(∑ p ∈ S, w p*(if σ ≤ p.2.re then 1 else 0)) ≤ B*M*L^8 := by
    change x^σ*modulusZeroWeight q T (fun z => if σ ≤ z.re then 1 else 0) ≤ _
    rw [modulusZeroWeight_tail]
    apply (mul_le_mul_of_nonneg_left (HB (q := q) hs hT) (Real.rpow_nonneg hx₀.le _)).trans
    have h := ingham_power_weight_three_term hx₀ hH hs
    have hp := pow_le_pow_left₀ hlog₀ (show Real.log H ≤ L by dsimp [L]; linarith) 8
    have he := mul_le_mul h hp (pow_nonneg hlog₀ 8) hM
    change x^σ*(B*H^(inghamExponent σ)*(Real.log H)^8) ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left he hB.le]
  have hc (σ : ℝ) := HA (q := q) hT σ
  have hcount : (∑ p ∈ S, w p) ≤ A*H*Real.log H := by
    have he := hc 0
    rw [← modulusZeroWeight_tail] at he
    have hcard : (∑ p ∈ S,w p) = modulusZeroWeight q T (fun z => if 0 ≤ z.re then 1 else 0) :=
      sum_congr rfl fun p hp => by simp only [ite_eq_left (hβ p hp).1.le, mul_one]; rfl
    rw [hcard]
    apply he.trans
    calc
      _ ≤ A*(q : ℝ)*T*Real.log H := by
        apply mul_le_mul_of_nonneg_right _ hlog₀
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.totient_le q) hA.le
      _ = _ := by dsimp only [H]; ring
  have hsum := weighted_rpow_sum_le_of_tail S w (fun p => p.2.re) (by linarith : 1 ≤ x)
    (by norm_num : (1/2 : ℝ) ≤ 1) (fun _ _ => Nat.cast_nonneg _) (fun p hp => (hβ p hp).2.1.le) htail
  rw [← Real.sqrt_eq_rpow] at hsum
  change (∑ p ∈ S,w p*x^p.2.re) ≤ (A+B)*M*(1+Real.log x)*L^8
  have h₁ : Real.sqrt x*H ≤ M := by
    dsimp only [M]
    linarith [mul_nonneg (Real.rpow_nonneg hx₀.le (4/5)) (Real.rpow_nonneg hH₀.le (3/5))]
  have hL₈ : Real.log H ≤ L^8 := (show Real.log H ≤ L by dsimp [L]; linarith).trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 8))
  have hc₁ := mul_le_mul_of_nonneg_left (mul_le_mul h₁ hL₈ hlog₀ hM) hA.le
  have hw₁ := mul_le_mul_of_nonneg_left hcount (Real.sqrt_nonneg x)
  have hpos : 0 ≤ L^8 := pow_nonneg (by linarith) _
  nlinarith only [hsum, hw₁, hc₁, mul_nonneg (mul_nonneg (mul_nonneg hA.le hM) hxlog) hpos,
    mul_nonneg (mul_nonneg hB.le hM) hpos, mul_nonneg (mul_nonneg (mul_nonneg hB.le hM) hxlog) hpos]

end AnalyticNumberTheory.PrimeDistribution
