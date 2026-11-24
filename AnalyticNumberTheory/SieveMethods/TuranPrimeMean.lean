import AnalyticNumberTheory.SieveMethods.PrimeHybridSieve
import AnalyticNumberTheory.DirichletLFunctions.TuranPrimeWindow
import AnalyticNumberTheory.PrimeDistribution.Chebyshev

/-!
# Mean squares of prime sums in Turán's zero detector

The Poisson weight is at most one in every order. The prime-supported hybrid
large sieve and Mertens' first theorem then give a common mean-square bound
for the full character family.
-/
noncomputable section
open Complex Real Finset
open scoped Classical ArithmeticFunction
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

private theorem prime_window_mass {X U η : ℝ} (hU : 1≤U) (hη : 0≤η) (k : ℕ) :
    ∑ p ∈ turanPrimes X U, (p:ℝ)*‖((η*(Λ p/p)*turanWeight k (η*Real.log p):ℝ):ℂ)‖^2 ≤
      η^2*Real.log U*(Real.log U+mertensOneBound) := by
  let W := turanPrimes X U
  have hsub : W ⊆ Nat.primesLE ⌊U⌋₊ := by
    intro p hp; obtain ⟨hp,hprime⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp hp).2,hprime⟩
  have hmert := abs_mertens_one_sub_log_le hU
  have hsum : ∑ p ∈ W, Real.log p/p ≤ Real.log U+mertensOneBound := by
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)).trans ?_
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos)) (Nat.cast_nonneg _)
    · linarith [(abs_le.mp hmert).2]
  calc
    _ ≤ ∑ p ∈ W, (η^2*Real.log U)*(Real.log p/p) := by
      apply sum_le_sum; intro p hp
      have hp' : p.Prime := (mem_filter.mp hp).2
      have hp0 : 0<(p:ℝ) := Nat.cast_pos.mpr hp'.pos
      have hp1 : 1≤(p:ℝ) := by exact_mod_cast hp'.pos
      have hlog := Real.log_nonneg hp1
      have hle := Real.log_le_log hp0 ((Nat.le_floor_iff (by linarith : 0≤U)).mp (mem_Ioc.mp (mem_filter.mp hp).1).2)
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp',Complex.norm_real,Real.norm_eq_abs,sq_abs]
      have hw0 := turanWeight_nonneg k (mul_nonneg hη hlog)
      have hw1 := turanWeight_le_one k (mul_nonneg hη hlog)
      have hw : (η*(Real.log p/p)*turanWeight k (η*Real.log p))^2 ≤ (η*(Real.log p/p))^2 := by
        exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (by positivity) hw1) 2
      calc
        _ ≤ (p:ℝ)*(η*(Real.log p/p))^2 := mul_le_mul_of_nonneg_left hw hp0.le
        _ = (η^2*Real.log p)*(Real.log p/p) := by field_simp <;> ring
        _ ≤ _ := by gcongr
    _ = (η^2*Real.log U)*∑ p ∈ W,Real.log p/p := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg _) (Real.log_nonneg hU))

/-- The primitive-family mean square of the resonating prime polynomial,
uniformly in the derivative order k. The scale Y may be any upper bound
for Q(T+3). The explicit coefficient depends only on the upper exponent B. -/
theorem turan_prime_family_mean {Q : ℕ} (hQ : 1≤Q) {T Y A B η : ℝ}
    (hT : 0≤T) (hY : (Q:ℝ)*(T+3)≤Y) (hA : 16≤A) (hB : A≤B) (hη : 0≤η) (k : ℕ) :
    (∑ χ ∈ primitiveCharacterFamily Q, ∫ t in (-(T+1))..(T+1),
      ‖∑ p ∈ turanPrimes (Y^A) (Y^B),turanMangoldtTerm χ.2 η t k p‖^2) ≤
      (6*Real.pi^3*B*(B+2*mertensOneBound))*η^2*Real.log Y := by
  have hq : 1≤(Q:ℝ) := by exact_mod_cast hQ
  have h3 : 3≤Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0≤T+3 by linarith)]
  have hYp : 0<Y := by linarith
  have hL : 1/2≤Real.log Y := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h; exact h.trans (Real.log_le_log (by norm_num) (by linarith))
  let W := turanPrimes (Y^A) (Y^B)
  let a := fun p : ℕ => ((η*(Λ p/p)*turanWeight k (η*Real.log p):ℝ):ℂ)
  have hscale : ((Q:ℝ)^2*((T+1)+2))^8 ≤ Y^A := by
    have hq' : (Q:ℝ)≤Y := by nlinarith [mul_nonneg (show 0≤(Q:ℝ) by positivity) (show 0≤T+2 by linarith)]
    calc
      _ ≤ (Y^2)^8 := by
        apply pow_le_pow_left₀ (by positivity)
        calc
          _ = (Q:ℝ)*((Q:ℝ)*(T+3)) := by ring
          _ ≤ Y*Y := mul_le_mul hq' hY (by positivity) hYp.le
          _ = _ := by ring
      _ = Y^(16:ℝ) := by rw [←pow_mul]; norm_cast
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  have hU : 1≤Y^B := Real.one_le_rpow (by linarith) (by linarith)
  have hh := prime_hybrid_large_sieve W a hQ (T:=T+1) (by linarith) hscale (fun p hp =>
    ⟨(mem_filter.mp hp).2,(Nat.lt_floor_add_one _).trans_le (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).1)⟩)
  have hterm (χ : (q : ℕ) × DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) :
      turanMangoldtTerm χ.2 η t k p = a p*χ.2 p*(p:ℂ)^(-(I*(t:ℂ))) := by
    dsimp [turanMangoldtTerm,a]; rw [neg_mul, mul_comm (t:ℂ) I]; ring
  simp_rw [hterm]
  refine hh.trans ?_
  have hmass := prime_window_mass (X:=Y^A) hU hη k
  change (∑ p ∈ W,(p:ℝ)*‖a p‖^2) ≤ _ at hmass
  have hpos : 0<A*Real.log Y := by positivity
  rw [Real.log_rpow hYp] at hmass ⊢
  refine (mul_le_mul_of_nonneg_left hmass (by positivity)).trans ?_
  have hLpos : 0 < Real.log Y := by linarith
  have hBpos : 0 < B := by linarith
  have hMpos := mertensOneBound_pos
  have hM : mertensOneBound ≤ 2*mertensOneBound*Real.log Y := by
    nlinarith [mul_nonneg mertensOneBound_pos.le (sub_nonneg.mpr hL)]
  have hfactor : B*Real.log Y+mertensOneBound ≤ (B+2*mertensOneBound)*Real.log Y := by linarith
  calc
    _ ≤ (6*Real.pi^3/(A*Real.log Y))*(η^2*(B*Real.log Y)*((B+2*mertensOneBound)*Real.log Y)) := by gcongr
    _ = ((6*Real.pi^3*B*(B+2*mertensOneBound))*η^2*Real.log Y)/A := by field_simp <;> ring
    _ ≤ _ := div_le_self (by positivity) (by linarith)

end AnalyticNumberTheory.SieveMethods
