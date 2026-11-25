import AnalyticNumberTheory.SieveMethods.LinearSieve

/-!
# Positive main term for Kuhn's weighted sieve

At logarithmic level 3.98, subtracting half the sum of the upper sieves
over medium primes still leaves a positive multiple of the sifted main
term. Two subintervals give sufficient numerical precision.
-/
noncomputable section
open Finset Set Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- Logarithmic sieve level, measured in units of log z. -/
def kuhnLevel : ℝ := 199/50

/-- Upper cutoff for the tagged prime, measured in units of log z. -/
def kuhnPrimeExponent : ℝ := 27/10

/-- Normalizing constant for the initial branches of the linear sieve functions. -/
def kuhnScale : ℝ := 2*exp eulerMascheroniConstant

theorem kuhnScale_pos : 0<kuhnScale := by dsimp [kuhnScale]; positivity

private theorem kuhn_lower : kuhnScale*(27/100)≤linearSieveLower kuhnLevel := by
  rw [linearSieveLower_eq_of_le_four (by norm_num [kuhnLevel] : kuhnLevel∈Set.Icc 2 4)]
  have he := Real.exp_one_lt_d9
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0<(kuhnLevel-1)/exp 1 by dsimp [kuhnLevel]; positivity)
  rw [Real.log_div (by norm_num [kuhnLevel]) (exp_ne_zero _),Real.log_exp,inv_div] at hlog
  have he' : exp 1/(kuhnLevel-1)≤23/25 := (div_le_iff₀ (by norm_num [kuhnLevel])).mpr (by dsimp [kuhnLevel]; linarith)
  have hn : 27/100≤log (kuhnLevel-1)/kuhnLevel := (le_div_iff₀ (by norm_num [kuhnLevel])).mpr (by dsimp [kuhnLevel] at *; linarith)
  change kuhnScale*(27/100)≤kuhnScale*log (kuhnLevel-1)/kuhnLevel
  rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hn kuhnScale_pos.le

private theorem kuhn_interval {P : Finset ℕ} {g : ℕ → ℝ} {z a b α K L : ℝ}
    (hz : 2≤z) (ha : 1≤a) (hab : a≤b) (hb : b≤kuhnPrimeExponent)
    (hg : ∀p∈P,0≤g p) (H : SieveLogMassBounds P g 2 (z^kuhnPrimeExponent) L K)
    (hK : K≤log z/1000)
    (hint : ∀ t∈Set.Icc a b,1≤t → 1/(t*(kuhnLevel-t))≤α) (hα : 0≤α) :
    (∑p∈sievePrimeWindow P (z^a) (z^b),g p*(linearSieveUpper (kuhnLevel-log p/log z)+kuhnScale/1000))≤
      (b-a+1/1000)*(kuhnScale*α+kuhnScale/1000) := by
  have hz₁ : 1≤z := by linarith
  have hlog := log_pos (by linarith : 1<z)
  have hza : z≤z^a := by simpa using Real.rpow_le_rpow_of_exponent_le hz₁ ha
  have hbd := Real.rpow_le_rpow_of_exponent_le hz₁ hab
  have hupper := Real.rpow_le_rpow_of_exponent_le hz₁ hb
  let S := sievePrimeWindow P (z^a) (z^b)
  let c := kuhnScale*α+kuhnScale/1000
  have hc : 0≤c := by dsimp [c]; positivity [kuhnScale_pos]
  have hmass := (H (z^a) (z^b) (hz.trans hza) hbd hupper).2
  rw [log_div (rpow_pos_of_pos (by linarith : 0<z) b).ne' (rpow_pos_of_pos (by linarith : 0<z) a).ne',log_rpow (by linarith : 0<z),log_rpow (by linarith : 0<z)] at hmass
  change (∑p∈S,g p*log p)-(b*log z-a*log z)≤K at hmass
  have hsum : (∑p∈S,g p*log p)/log z≤b-a+1/1000 := (div_le_iff₀ hlog).mpr (by linarith only [hmass,hK])
  change _≤(b-a+1/1000)*c
  calc _ ≤ ∑p∈S,g p*log p/log z*c := by
          apply sum_le_sum; intro p hp
          obtain ⟨hP,hpa,hpb⟩ := mem_filter.mp hp
          have hp' : (0:ℝ)<p := by linarith [hz.trans (hza.trans hpa)]
          let t := log p/log z
          have ht : t∈Set.Icc a b := by
            have h₁ := log_le_log (rpow_pos_of_pos (by linarith : 0<z) a) hpa
            have h₂ := log_le_log hp' hpb.le
            rw [log_rpow (by linarith : 0<z)] at h₁ h₂
            exact ⟨(le_div_iff₀ hlog).mpr h₁,(div_le_iff₀ hlog).mpr h₂⟩
          have ht₁ := ha.trans ht.1
          have ht₂ := ht.2.trans hb
          have hv : kuhnLevel-t∈Set.Icc 1 3 := by dsimp only [kuhnLevel,kuhnPrimeExponent] at *; constructor <;> linarith
          have h₃ := hint t ht ht₁
          have h₄ : 1/(kuhnLevel-t)≤t*α := by
            have htpos : 0<t := by linarith
            have hypos : 0<kuhnLevel-t := by linarith [hv.1]
            apply (div_le_iff₀ hypos).mpr
            linarith only [(div_le_iff₀ (mul_pos htpos hypos)).mp h₃]
          have htest : linearSieveUpper (kuhnLevel-t)+kuhnScale/1000≤t*c := by
            rw [linearSieveUpper_eq_of_le_three hv]
            dsimp only [c]; change kuhnScale/(kuhnLevel-t)+kuhnScale/1000≤_
            have h₅ := mul_le_mul_of_nonneg_left h₄ kuhnScale_pos.le
            have h₆ := mul_le_mul_of_nonneg_right ht₁ (div_nonneg kuhnScale_pos.le (by norm_num : (0:ℝ)≤1000))
            rw [←mul_div_assoc,mul_one] at h₅
            linarith only [h₅,h₆]
          convert mul_le_mul_of_nonneg_left htest (hg p hP) using 1 <;> dsimp only [t] <;> ring
       _ = ((∑p∈S,g p*log p)/log z)*c := by rw [sum_div,sum_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_right hsum hc

/-- Positivity of the weighted linear sieve, uniform over finite prime sets
with the dimension-one logarithmic mass bound. -/
theorem kuhn_weight_positive {P : Finset ℕ} {g : ℕ → ℝ} {z K L : ℝ}
    (hz : 2≤z) (hg : ∀p∈P,0≤g p) (H : SieveLogMassBounds P g 2 (z^kuhnPrimeExponent) L K)
    (hK : K≤log z/1000) :
    kuhnScale/200≤linearSieveLower kuhnLevel-kuhnScale/1000-
      (1/2:ℝ)*∑p∈sievePrimeWindow P z (z^kuhnPrimeExponent),
        g p*(linearSieveUpper (kuhnLevel-log p/log z)+kuhnScale/1000) := by
  have h₁ := kuhn_interval (a:=1) (b:=3/2) (α:=17/50) hz le_rfl (by norm_num) (by norm_num [kuhnPrimeExponent]) hg H hK
    (fun t ht _ => by
      have ht₀ : 0<t := by linarith [ht.1]
      have hu : 0<kuhnLevel-t := by dsimp [kuhnLevel]; linarith [ht.2]
      apply (div_le_iff₀ (mul_pos ht₀ hu)).mpr
      dsimp [kuhnLevel]; nlinarith only [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2),ht.1]) (by norm_num)
  have h₂ := kuhn_interval (a:=3/2) (b:=kuhnPrimeExponent) (α:=29/100) hz (by norm_num) (by norm_num [kuhnPrimeExponent]) le_rfl hg H hK
    (fun t ht _ => by
      have ht₀ : 0<t := by linarith [ht.1]
      have hu : 0<kuhnLevel-t := by dsimp [kuhnLevel,kuhnPrimeExponent] at *; linarith [ht.2]
      apply (div_le_iff₀ (mul_pos ht₀ hu)).mpr
      dsimp [kuhnLevel,kuhnPrimeExponent] at *
      nlinarith only [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2),ht.1,ht.2]) (by norm_num)
  rw [Real.rpow_one] at h₁
  let T := z^(3/2:ℝ)
  let V := z^kuhnPrimeExponent
  have hzt : z≤T := by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤z) (by norm_num : (1:ℝ)≤3/2)
  have htv : T≤V := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num [kuhnPrimeExponent])
  have hset : sievePrimeWindow P z V=sievePrimeWindow P z T∪sievePrimeWindow P T V := by
    ext p; simp only [sievePrimeWindow,mem_filter,Finset.mem_union]; grind
  have hd : Disjoint (sievePrimeWindow P z T) (sievePrimeWindow P T V) := by
    apply Finset.disjoint_left.mpr; intro p hp hq; exact (not_le.mpr (mem_filter.mp hp).2.2) (mem_filter.mp hq).2.1
  change _≤_-_-1/2*∑p∈sievePrimeWindow P z V,_
  rw [hset,sum_union hd]; dsimp only [T,V] at *
  dsimp only [kuhnPrimeExponent] at *
  linarith only [h₁,h₂,kuhn_lower,kuhnScale_pos]

end AnalyticNumberTheory.SieveMethods
