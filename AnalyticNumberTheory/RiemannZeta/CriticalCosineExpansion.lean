import AnalyticNumberTheory.RiemannZeta.CriticalCosineKernels

/-!
# Expanding the sharp Riemann–Siegel polynomial

The entry height of each pair is the maximum of its two thresholds.
After the cosine product formula, the constant diagonal separates
pointwise before integration.
-/
noncomputable section
open Real Complex Finset MeasureTheory Set
open scoped Interval
namespace AnalyticNumberTheory.RiemannZeta

def hardyCutoffIndex (t : ℝ) := ⌊Real.sqrt (t/(2*Real.pi))⌋₊

/-- The finite elementary cosine polynomial with its moving cutoff. -/
def hardyCosineMain (t : ℝ) := 2*∑n∈Finset.Icc 1 (hardyCutoffIndex t),Real.cos (hardyAngle n t)/Real.sqrt n

def hardyCosineDiagonal (t : ℝ) := 2*∑n∈Finset.Icc 1 (hardyCutoffIndex t),(n:ℝ)⁻¹

def fromHeight (c : ℝ) (f : ℝ→ℝ) := (Ici c).indicator f

theorem fromHeight_apply (c : ℝ) (f : ℝ→ℝ) (t : ℝ) : fromHeight c f t=if c≤t then f t else 0 := by
  rfl

theorem fromHeight_intervalIntegrable (c : ℝ) {f : ℝ→ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fromHeight c f) volume a b := by
  rw [intervalIntegrable_iff,fromHeight,integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet]
  exact (hf.intervalIntegrable (μ:=volume) a b).def'.mono_set inter_subset_right

/-- Integrating past an entry height clips the lower endpoint exactly. -/
theorem integral_fromHeight {c a b : ℝ} (hab : a≤b) (hc : c≤b) (f : ℝ→ℝ) :
    (∫u in a..b,fromHeight c f u)=∫u in max a c..b,f u := by
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le (max_le hab hc),fromHeight,
    MeasureTheory.integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  rw [inter_comm,←Ioc_inter_Ioi]
  apply setIntegral_congr_set
  exact ae_eq_set_inter (Filter.Eventually.of_forall (fun _ => Iff.rfl)) (Ioi_ae_eq_Ici (a:=c) (μ:=volume)).symm

theorem hardyCutoffIndex_mono : Monotone hardyCutoffIndex := by
  intro s t h
  apply Nat.floor_mono
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h (by positivity))

theorem le_hardyCutoffIndex_iff {t : ℝ} (ht : 0≤t) {n : ℕ} : n≤hardyCutoffIndex t ↔ hardyCutoff n≤t := by
  rw [hardyCutoffIndex,Nat.le_floor_iff (Real.sqrt_nonneg _),Real.le_sqrt (Nat.cast_nonneg _) (by positivity),
    le_div_iff₀ (by positivity : 0<2*Real.pi)]
  dsimp [hardyCutoff];rw [mul_comm ((n:ℝ)^2)]

private theorem sum_cutoff (f : ℕ→ℝ) {t T : ℝ} (ht : 0≤t) (hT : t≤T) :
    (∑n∈Finset.Icc 1 (hardyCutoffIndex t),f n)=
      ∑n∈Finset.Icc 1 (hardyCutoffIndex T),if hardyCutoff n≤t then f n else 0 := by
  classical
  rw [←sum_filter]
  congr 1;ext n
  simp only [mem_filter,Finset.mem_Icc,←le_hardyCutoffIndex_iff ht]
  constructor
  · intro h;exact ⟨⟨h.1,h.2.trans (hardyCutoffIndex_mono hT)⟩,h.2⟩
  · exact fun h => ⟨h.1.1,h.2⟩

/-- Unequal modes give two oscillatory kernels. Removing the constant
from an equal-mode cosine square leaves only the sum phase. -/
def hardyCosinePair (m n : ℕ) (t : ℝ) :=
  (2/(Real.sqrt m*Real.sqrt n))*(Real.cos (hardyAngle m t+hardyAngle n t)+
    (if m=n then 0 else Real.cos (hardyAngle m t-hardyAngle n t)))

theorem continuous_hardyCosinePair (m n : ℕ) : Continuous (hardyCosinePair m n) := by
  unfold hardyCosinePair
  have h₁ := Real.continuous_cos.comp ((continuous_hardyAngle m).add (continuous_hardyAngle n))
  have h₂ := Real.continuous_cos.comp ((continuous_hardyAngle m).sub (continuous_hardyAngle n))
  split_ifs
  · exact continuous_const.mul (h₁.add continuous_const)
  · exact continuous_const.mul (h₁.add h₂)

private def cosineTerm (n : ℕ) (t : ℝ) := Real.cos (hardyAngle n t)/Real.sqrt n

private theorem cosine_pair_eq (m n : ℕ) (t : ℝ) :
    4*(cosineTerm m t*cosineTerm n t)=(if m=n then 2*(m:ℝ)⁻¹ else 0)+hardyCosinePair m n t := by
  have hc := Real.cos_add_cos (hardyAngle m t+hardyAngle n t) (hardyAngle m t-hardyAngle n t)
  rw [show (hardyAngle m t+hardyAngle n t+(hardyAngle m t-hardyAngle n t))/2=hardyAngle m t by ring,
    show (hardyAngle m t+hardyAngle n t-(hardyAngle m t-hardyAngle n t))/2=hardyAngle n t by ring] at hc
  dsimp only [cosineTerm,hardyCosinePair]
  by_cases h : m=n
  · subst n
    simp only [ite_true,add_zero,sub_self,Real.cos_zero] at hc ⊢
    rw [←sq (Real.sqrt (m:ℝ)),Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [show Real.cos (hardyAngle m t+hardyAngle m t)=2*Real.cos (hardyAngle m t)*Real.cos (hardyAngle m t)-1 by linarith only [hc] ]
    rw [←sq,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  · simp only [h,ite_false,zero_add,hc];ring

/-- Exact finite-pair decomposition, valid at every ordinate in the
integration interval, including the entry heights themselves. -/
theorem hardyCosine_square_sub_diagonal {t T : ℝ} (ht : 0≤t) (hT : t≤T) :
    hardyCosineMain t^2-hardyCosineDiagonal t=
      ∑m∈Finset.Icc 1 (hardyCutoffIndex T),∑n∈Finset.Icc 1 (hardyCutoffIndex T),
        fromHeight (max (hardyCutoff m) (hardyCutoff n)) (hardyCosinePair m n) t := by
  classical
  let S := Finset.Icc 1 (hardyCutoffIndex T)
  let v := fun n : ℕ => if hardyCutoff n≤t then cosineTerm n t else 0
  let P := fun m n : ℕ => fromHeight (max (hardyCutoff m) (hardyCutoff n)) (hardyCosinePair m n) t
  let d := fun m : ℕ => if hardyCutoff m≤t then 2*(m:ℝ)⁻¹ else 0
  have he (m n : ℕ) : 4*(v m*v n)=(if m=n then d m else 0)+P m n := by
    dsimp only [v,P,d];rw [fromHeight_apply]
    by_cases he : m=n
    · subst n
      by_cases hm : hardyCutoff m≤t
      · simpa [hm] using cosine_pair_eq m m t
      · simp [hm]
    · by_cases hm : hardyCutoff m≤t <;> by_cases hn : hardyCutoff n≤t
      · simpa [hm,hn,he,max_le_iff] using cosine_pair_eq m n t
      all_goals simp [hm,hn,he,max_le_iff]
  have hsum : 4*((∑m∈S,v m)*(∑n∈S,v n))=(∑m∈S,d m)+∑m∈S,∑n∈S,P m n := by
    rw [sum_mul,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    rw [mul_sum,mul_sum]
    simp_rw [he]
    rw [sum_add_distrib,sum_ite_eq,if_pos hm]
  have hmain : hardyCosineMain t=2*∑m∈S,v m := by
    change 2*(∑m∈Finset.Icc 1 (hardyCutoffIndex t),cosineTerm m t)=_
    rw [sum_cutoff _ ht hT]
  have hdiag : hardyCosineDiagonal t=∑m∈S,d m := by
    unfold hardyCosineDiagonal
    rw [mul_sum,sum_cutoff _ ht hT]
  change _=∑m∈S,∑n∈S,P m n
  rw [hmain,hdiag]
  linear_combination hsum

private theorem intervalIntegrable_sum_apply {ι : Type*} {s : Finset ι} {a b : ℝ} {f : ι→ℝ→ℝ}
    (H : ∀i∈s,IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun t => ∑i∈s,f i t) volume a b := by
  have he : (fun t => ∑i∈s,f i t)=∑i∈s,f i := by
    classical
    funext t
    clear H
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp only [sum_insert hi,Pi.add_apply,ih]
  rw [he];exact IntervalIntegrable.sum s H

theorem hardyCosineMain_intervalIntegrable {a T : ℝ} (ha : 0≤a) (hT : a≤T) :
    IntervalIntegrable hardyCosineMain volume a T := by
  let F := fun t : ℝ => 2*∑n∈Finset.Icc 1 (hardyCutoffIndex T),fromHeight (hardyCutoff n) (cosineTerm n) t
  have h : IntervalIntegrable F volume a T := (intervalIntegrable_sum_apply fun n _ =>
    fromHeight_intervalIntegrable (hardyCutoff n) ((Real.continuous_cos.comp (continuous_hardyAngle n)).div_const _) a T).const_mul 2
  apply h.congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  dsimp only [F,hardyCosineMain]
  rw [sum_cutoff _ (ha.trans ht.1.le) ht.2];rfl

theorem hardyCosineDiagonal_monotone : Monotone hardyCosineDiagonal := by
  intro t u h
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (hardyCutoffIndex_mono h))
  intro n _ _;positivity

theorem hardyCosineMain_sq_intervalIntegrable {a T : ℝ} (ha : 0≤a) (hT : a≤T) :
    IntervalIntegrable (fun t => hardyCosineMain t^2) volume a T := by
  let S := Finset.Icc 1 (hardyCutoffIndex T)
  have hp := intervalIntegrable_sum_apply (s:=S) (fun m _ => intervalIntegrable_sum_apply (s:=S) (fun n _ =>
    fromHeight_intervalIntegrable (max (hardyCutoff m) (hardyCutoff n)) (continuous_hardyCosinePair m n) a T))
  apply (hp.add (hardyCosineDiagonal_monotone.intervalIntegrable ..)).congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  have h := hardyCosine_square_sub_diagonal (ha.trans ht.1.le) ht.2
  change (∑m∈S,∑n∈S,fromHeight _ (hardyCosinePair m n) t)+hardyCosineDiagonal t=_
  linarith only [h]

end AnalyticNumberTheory.RiemannZeta
