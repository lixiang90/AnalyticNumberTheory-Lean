import AnalyticNumberTheory.SieveMethods.PrimePairUpperBound

/-!
# Partial sums over prime pairs

A uniform counting estimate extends to every upper endpoint at least three.
Summing reciprocal primes in dyadic blocks then gives a tail bounded by a
constant times the singular factor divided by the logarithm of the lower
endpoint.
-/

noncomputable section
open Finset Real Filter
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution Classical

/-- The uniform coefficient-eight estimate extends over the bounded initial
range by enlarging the constant in the relative logarithmic error. -/
theorem primePair_eight_all_of_eventual {A : ℝ} (hA : 0<A)
    (H : ∀ᶠ x : ℝ in atTop, ∀ {h : ℤ}, Even h.natAbs → h.natAbs≠0 →
      (primePairCount x h:ℝ)≤8*primePairSingularFactor h.natAbs*(x/(log x)^2)*
        (1+A*(log (log x)/log x))) :
    ∃ C : ℝ, 0<C ∧ ∀ {x : ℝ}, 3≤x → ∀ {h : ℤ}, Even h.natAbs → h.natAbs≠0 →
      (primePairCount x h:ℝ)≤8*primePairSingularFactor h.natAbs*(x/(log x)^2)*
        (1+C*(log (log x)/log x)) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp H
  let U := max M 3
  let L := log U
  let m := log (log 3)
  have hm : 0<m := log_pos ((Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three)
  have hl : 0<L := log_pos (by dsimp [U];linarith [le_max_right M 3])
  let b := L^3/(8*twinPrimeEulerConstant*m)
  let C := max A b
  have hb : 0<b := div_pos (pow_pos hl 3) (mul_pos (mul_pos (by norm_num) twinPrimeEulerConstant_pos) hm)
  refine ⟨C,hA.trans_le (le_max_left ..),?_⟩
  intro x hx h hh hh0
  let S := primePairSingularFactor h.natAbs
  let l := log x
  let r := log l/l
  have hx0 : 0<x := by linarith
  have hlx : 0<l := log_pos (by linarith)
  have hmx : m≤log l := Real.log_le_log (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)
  have hr : 0≤r := div_nonneg (hm.trans_le hmx).le hlx.le
  have hS := twinPrimeEulerConstant_le_primePairSingularFactor h.natAbs
  have hSpos : 0<S := twinPrimeEulerConstant_pos.trans_le hS
  by_cases hbig : M≤x
  · exact (hM x hbig hh hh0).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left ..) hr)) (by positivity))
  have hxU : x≤U := (not_le.mp hbig).le.trans (le_max_left ..)
  have hll : l≤L := Real.log_le_log hx0 hxU
  have hcount : (primePairCount x h:ℝ)≤x := by
    have he : primePairCount x h≤⌊x⌋₊ := by
      unfold primePairCount primeFinset
      exact (card_filter_le ..).trans (by rw [Nat.primesLE_eq_filter_Icc_one];exact (card_filter_le ..).trans (by simp))
    exact (by exact_mod_cast he : (primePairCount x h:ℝ)≤⌊x⌋₊).trans (Nat.floor_le hx0.le)
  have hscale : l^3≤8*S*C*log l := by
    calc _ ≤ L^3 := pow_le_pow_left₀ hlx.le hll 3
         _ = 8*twinPrimeEulerConstant*b*m := by dsimp [b];field_simp [twinPrimeEulerConstant_pos.ne',hm.ne']
         _ ≤ _ := by gcongr <;> first | exact hS | exact le_max_right A b | exact hmx
  have hkey : x ≤ 8*S*(x/l^2)*(C*(log l/l)) := by
    convert mul_le_mul_of_nonneg_right hscale (show 0≤x/l^3 by positivity) using 1 <;> field_simp [hlx.ne'] <;>ring
  exact hcount.trans (hkey.trans (by change _≤8*S*(x/l^2)*(1+C*r);gcongr;linarith))

/-- The reciprocal sum on a half-open interval of prime inputs. -/
def primePairReciprocalSum (h : ℤ) (a b : ℝ) :=
  ∑p∈(Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => p.Prime ∧ (primeShift h p).Prime),(p:ℝ)⁻¹

private theorem reciprocal_block {a K : ℝ} {h : ℤ} (ha : 3≤a) (hK : 0≤K)
    (H : (primePairCount (2*a) h:ℝ)≤K*((2*a)/log (2*a)^2)) :
    primePairReciprocalSum h a (2*a) ≤
      (2*K/log 2)*((log a)⁻¹-(log (2*a))⁻¹) := by
  let T := (Ioc ⌊a⌋₊ ⌊2*a⌋₊).filter (fun p => p.Prime ∧ (primeShift h p).Prime)
  have ha0 : 0<a := by linarith
  have hsub : T⊆(primeFinset (2*a)).filter (fun p => (primeShift h p).Prime) := by
    intro p hp
    obtain ⟨hi,hp',hs⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp hi).2,hp'⟩,hs⟩
  have hsum : (∑p∈T,(p:ℝ)⁻¹)≤∑_p∈T,a⁻¹ := by
    apply sum_le_sum;intro p hp
    exact inv_anti₀ ha0 (Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hp).1).1).le
  have hcard : (T.card:ℝ)≤primePairCount (2*a) h := by exact_mod_cast card_le_card hsub
  have hl := log_pos (show 1<a by linarith)
  have hc : 0<log 2 := log_pos (by norm_num)
  have hlog : 0<log 2 + log a := add_pos hc hl
  have hmono : (log (2*a)^2)⁻¹ ≤ ((log a)⁻¹-(log (2*a))⁻¹)/log 2 := by
    rw [log_mul (by norm_num) ha0.ne']
    field_simp [hc.ne',hl.ne',hlog.ne'];nlinarith [sq_nonneg (log 2),mul_nonneg hc.le hl.le]
  calc _ ≤ (T.card:ℝ)*a⁻¹ := by simpa [primePairReciprocalSum,T] using hsum
       _ ≤ (K*(2*a/log (2*a)^2))*a⁻¹ := mul_le_mul_of_nonneg_right (hcard.trans H) (inv_nonneg.mpr ha0.le)
       _ = (2*K)*(log (2*a)^2)⁻¹ := by field_simp
       _ ≤ _ := by convert mul_le_mul_of_nonneg_left hmono (show 0≤2*K by positivity) using 1 <;>ring

/-- A uniform finite tail bound, valid for any counting constant
K with Z(t,h) ≤ K t/log² t throughout the range t ≥ a. -/
theorem primePair_reciprocal_tail_of_count {a b K : ℝ} {h : ℤ} (ha : 3≤a) (hK : 0≤K)
    (H : ∀ t : ℝ, a≤t → (primePairCount t h:ℝ)≤K*(t/log t^2)) :
    primePairReciprocalSum h a b ≤ 2*K/(log 2*log a) := by
  let t (j : ℕ) := (2:ℝ)^j*a
  have ha0 : 0<a := by linarith
  have hlow (j : ℕ) : a≤t j := le_mul_of_one_le_left ha0.le (one_le_pow₀ (by norm_num))
  have hstep (j : ℕ) : t (j+1)=2*t j := by dsimp [t];ring
  have hsum (j : ℕ) : primePairReciprocalSum h a (t j)≤
      (2*K/log 2)*((log a)⁻¹-(log (t j))⁻¹) := by
    induction j with
    | zero => simp [t,primePairReciprocalSum]
    | succ j ih =>
      have hj := hlow j
      have hnext : t j ≤ 2*t j := by linarith
      have hc := reciprocal_block (h:=h) (ha.trans hj) hK (H _ (hj.trans hnext))
      have he : primePairReciprocalSum h a (t (j+1))=
          primePairReciprocalSum h a (t j)+primePairReciprocalSum h (t j) (2*t j) := by
        simp only [primePairReciprocalSum,Finset.sum_filter,hstep j]
        rw [← Ioc_union_Ioc_eq_Ioc (Nat.floor_mono hj) (Nat.floor_mono hnext),sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
      rw [he,hstep];linarith only [ih,hc]
  obtain ⟨j,hj⟩ := pow_unbounded_of_one_lt (b/a) (by norm_num : (1:ℝ)<2)
  have hbt : b≤t j := ((div_lt_iff₀ ha0).mp hj).le
  have hsub : primePairReciprocalSum h a b≤primePairReciprocalSum h a (t j) := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact filter_subset_filter _ (Ioc_subset_Ioc_right (Nat.floor_mono hbt))
    · intro p _ _;positivity
  have hp : 0≤(log (t j))⁻¹ := inv_nonneg.mpr (log_nonneg (by linarith [hlow j]))
  calc _ ≤ (2*K/log 2)*((log a)⁻¹-(log (t j))⁻¹) := hsub.trans (hsum j)
       _ ≤ (2*K/log 2)*(log a)⁻¹ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
       _ = _ := by ring

end AnalyticNumberTheory.SieveMethods
