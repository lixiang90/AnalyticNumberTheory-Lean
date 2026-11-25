import AnalyticNumberTheory.AdditiveNumberTheory.WaringBasisParameters
import AnalyticNumberTheory.AdditiveNumberTheory.WaringShiftedTargets
import AnalyticNumberTheory.AdditiveNumberTheory.WaringVinogradovMinorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.WaringBasis

/-!
# Vinogradov's logarithmic bound for Waring's problem

The asymptotic basis order counts the number of powers needed for every
sufficiently large integer. A positive major-arc term persists after averaging
over two independently chosen tuples of diminishing ranges.
-/

open Real Filter Finset
open scoped Topology
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem eventually_power_comparison {a b C D : ℝ} (hab : a<b) (hD : 0<D) :
    ∀ᶠ P : ℕ in atTop, C*(P:ℝ)^a<D*(P:ℝ)^b := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.eventually_gt_atTop (C/D),eventually_ge_atTop 1] with P hp hP
  have hp0 : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  have hp' := (div_lt_iff₀ hD).mp hp
  change C<(P:ℝ)^(b-a)*D at hp'
  rw [show b=(b-a)+a by ring,Real.rpow_add hp0]
  nlinarith only [mul_lt_mul_of_pos_right hp' (Real.rpow_pos_of_pos hp0 a)]

private theorem waring_ambient_scale {k : ℕ} (hk : 0<k) :
    ∃ P : ℕ → ℕ, Tendsto P atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, (P n:ℝ)^k/2 ≤ n ∧ (n:ℝ)≤(P n:ℝ)^k := by
  let u (n : ℕ) := (n:ℝ)^(1/(k:ℝ))
  let P (n : ℕ) := ⌈u n⌉₊
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hu : Tendsto u atTop atTop := (tendsto_rpow_atTop (one_div_pos.mpr hk0)).comp tendsto_natCast_atTop_atTop
  refine ⟨P,tendsto_nat_ceil_atTop.comp hu,?_⟩
  have H := ((tendsto_nat_ceil_div_atTop (R:=ℝ)).comp hu).pow k
  simp only [one_pow] at H
  have he n : (u n)^k=(n:ℝ) := by
    dsimp [u]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),one_div_mul_cancel hk0.ne',Real.rpow_one]
  filter_upwards [H.eventually_le_const (by norm_num : (1:ℝ)<2),eventually_ge_atTop 1] with n hi hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  change ((P n:ℝ)/u n)^k≤2 at hi
  rw [div_pow,he,div_le_iff₀ hn0] at hi
  refine ⟨by linarith,?_⟩
  rw [← he n]
  exact pow_le_pow_left₀ (by dsimp [u]; positivity) (Nat.le_ceil _) _

/-- Four full-length variables per degree together with two sets of
`⌈8k log k⌉` short variables represent every sufficiently large target. -/
theorem eventually_waringCount_pos_logarithmic {k : ℕ} (hk : 3≤k) :
    ∀ᶠ N : ℕ in atTop, 0<waringCount k (4*k+2*waringDiminishingOrder k) N := by
  let m := waringDiminishingOrder k
  let s := 4*k
  let r := 1-1/(1600*(k:ℝ)^2*Real.log k)
  let v := (k:ℝ)*(1-(1-1/(k:ℝ))^m)
  let A (P : ℕ) := waringDiminishingValues k m (waringDiminishingCutoff k P)
  obtain ⟨c,hc,hmajor⟩ := eventually_waringMajorContribution_re_ge (by omega : 2≤k) (show 4*k≤s from le_rfl)
  obtain ⟨C,hC,hminor⟩ := waringSum_vinogradov_fixed_minorArcs hk
  obtain ⟨d,hd,hprod⟩ := waringDiminishingCutoff_product_lower (by omega : 2≤k) m
  have hcard : ∀ᶠ P : ℕ in atTop, d*(P:ℝ)^v≤(A P).card := by
    filter_upwards [eventually_waringDiminishingCutoff_admissible (by omega : 2≤k) m,hprod] with P h hp
    dsimp only [A]
    rw [card_waringDiminishingValues hk _ h.1 h.2, Nat.cast_prod]
    exact hp
  have hrs : r*(s:ℝ)<((s-k:ℕ):ℝ)+v := by
    rw [mul_comm r]
    simpa only [r,s,v,m, Nat.cast_mul,Nat.cast_ofNat] using waringDiminishingOrder_saving hk
  have hcompare := eventually_power_comparison (C:=C^s) hrs (mul_pos hc hd)
  obtain ⟨P,hP,hscale⟩ := waring_ambient_scale (by omega : 0<k)
  filter_upwards [hP.eventually hmajor,hP.eventually hcard,hP.eventually hcompare,hscale,
    hP.eventually (eventually_waringDiminishingValues_small hk m),hP.eventually_ge_atTop 3] with N hmaj ha hcmp hN ht hp
  have hp0 : (0:ℝ)<P N := by exact_mod_cast (by omega : 0<P N)
  have hX : 0<(P N:ℝ)^k := pow_pos hp0 _
  have hn : (A (P N)).Nonempty := card_pos.mp (by
    have : (0:ℝ)<(A (P N)).card := (mul_pos hd (Real.rpow_pos_of_pos hp0 v)).trans_le ha
    exact_mod_cast this)
  have htarget (a : ℕ) (ha : a∈A (P N)) (b : ℕ) (hb : b∈A (P N)) :
      a+b≤N ∧ (P N:ℝ)^k/4≤((N-(a+b):ℕ):ℝ) ∧ ((N-(a+b):ℕ):ℝ)≤(P N:ℝ)^k := by
    have h₁ := ht a ha
    have h₂ := ht b hb
    have hab : a+b≤N := by exact_mod_cast (show (a:ℝ)+b≤N by linarith [hN.1])
    rw [Nat.cast_sub hab,Nat.cast_add]
    exact ⟨hab,by linarith [hN.1],by linarith [hN.2,Nat.cast_nonneg (α:=ℝ) a,Nat.cast_nonneg (α:=ℝ) b]⟩
  apply waringCount_pos_of_shift_set (k:=k) (s:=s) (m:=m) (by omega) hp (A (P N)) hn
    (c:=c) (M:=C*(P N:ℝ)^r)
  · intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact (waringCount_pos_iff (by omega : 0<k)).mpr ⟨x,rfl⟩
  · intro a ha b hb
    obtain ⟨h₁,_,h₂⟩ := htarget a ha b hb
    exact ⟨h₁,(by exact_mod_cast h₂ : N-(a+b)≤P N^k).trans_lt (Nat.pow_lt_pow_left (by omega) (by omega))⟩
  · positivity
  · intro a ha b hb
    exact hmaj _ (htarget a ha b hb).2.1 (htarget a ha b hb).2.2
  · exact fun α hα => hminor (by omega) hα
  · rw [mul_pow,← Real.rpow_mul_natCast hp0.le]
    apply hcmp.trans_le
    rw [Real.rpow_add hp0,Real.rpow_natCast]
    calc
      _ = c*(P N:ℝ)^(s-k)*(d*(P N:ℝ)^v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)

/-- The least number of nonnegative `k`-th powers sufficient for every large integer. -/
noncomputable def waringAsymptoticOrder (k : ℕ) : ℕ :=
  sInf {s : ℕ | ∀ᶠ n : ℕ in atTop, 0<waringCount k s n}

/-- For every positive degree the asymptotic basis order itself is admissible. -/
theorem eventually_waringCount_pos_asymptoticOrder {k : ℕ} (hk : 0<k) :
    ∀ᶠ n : ℕ in atTop, 0<waringCount k (waringAsymptoticOrder k) n := by
  obtain ⟨s,hs⟩ := hilbert_waring hk
  exact Nat.sInf_mem (s:={t : ℕ | ∀ᶠ n : ℕ in atTop, 0<waringCount k t n}) ⟨s,Eventually.of_forall fun n => (waringCount_pos_iff hk).mpr (hs n)⟩

/-- **Vinogradov's bound for Waring's asymptotic basis order**:
`G(k) ≤ 16k log k + 4k + 2` for every positive degree. -/
theorem waringAsymptoticOrder_le_logarithmic {k : ℕ} (hk : 0<k) :
    (waringAsymptoticOrder k:ℝ) ≤ 16*k*Real.log k+4*k+2 := by
  have H : waringAsymptoticOrder k ≤ 4*k+2*waringDiminishingOrder k := by
    apply Nat.sInf_le
    by_cases hk3 : 3≤k
    · exact eventually_waringCount_pos_logarithmic hk3
    · have h : k=1 ∨ k=2 := by omega
      rcases h with rfl|rfl
      · exact .of_forall fun n => waringCount_pos_mono (by decide : 0<1) (by omega : 1≤_) ((waringCount_pos_iff (by decide : 0<1)).mpr ⟨fun _ => n,by simp⟩)
      · exact .of_forall fun n => waringCount_pos_mono (by decide : 0<2) (by omega : 4≤_) (waringCount_four_squares_pos n)
  exact (show (waringAsymptoticOrder k:ℝ)≤((4*k+2*waringDiminishingOrder k:ℕ):ℝ) by exact_mod_cast H).trans (waringDiminishingOrder_total_le k)

end AnalyticNumberTheory.AdditiveNumberTheory
