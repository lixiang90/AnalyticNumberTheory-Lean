import AnalyticNumberTheory.SieveMethods.InfiniteGramSampling
import AnalyticNumberTheory.SieveMethods.CharacterGramEntries
import AnalyticNumberTheory.SieveMethods.CharacterCorrelationFamilies
import AnalyticNumberTheory.PrimeDistribution.InghamKernel

/-!
# Sparse Gram bounds for fixed-modulus and primitive character families

The principal product is confined to the same character. Unit-interval
occupancy and the fourth-order Cauchy kernel bound its contribution,
independently of all the other characters in the family.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate Classical
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

set_option maxHeartbeats 1000000 in
/-- Sparse sampling bound for the smoothly weighted vectors, with any finite choice
of frequencies and complex points in a strip of width one. -/
theorem sparse_character_gram_sampling :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {D L : ℕ},
    CharacterCorrelationFamily F f D → 1≤D → ∀(S : ι→Finset ℂ) {K X : ℝ},0≤K → 1≤X →
    (∀i∈F,∀z∈S i,0≤z.im ∧ z.im<L) →
    (∀i∈F,∀j<L,(((S i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K) →
    ∀(u : ℂ→ℂ),(∀i∈F,∀z∈S i,(u z).re∈Icc (0:ℝ) 1 ∧ (u z).im=z.im) →
    ∀(J : Finset ℕ) (a : ℕ→ℂ),
    let H := (D:ℝ)*((L:ℝ)+2)
    (∑i∈F,∑z∈S i,‖∑n∈J,a n*characterGramVector X (f i) (u z) n‖^2) ≤
      C*(K*X+(∑i∈F,((S i).card:ℝ))*Real.sqrt H*(1+Real.log H))*∑n∈J,‖a n‖^2 := by
  obtain ⟨B,hB,HB⟩ := characterGramEntry_bound
  refine ⟨B*(1+2*π),by positivity,?_⟩
  intro ι F f D L hfamily hD S K X hK hX him hcount u hu J a
  let W := F.sigma S
  let H := (D:ℝ)*((L:ℝ)+2)
  let E := Real.sqrt H*(1+Real.log H)
  let R := ∑i∈F,((S i).card:ℝ)
  have hH : 1≤H := by
    dsimp [H];exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD) (by linarith [Nat.cast_nonneg (α:=ℝ) L])
  have hE : 0≤E := by dsimp [E];have := Real.log_nonneg hH;positivity
  have hR : 0≤R := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hX' := zero_lt_one.trans_le hX
  let g (p : Sigma (fun _ : ι => ℂ)) := characterGramVector X (f p.1) (u p.2)
  let G (p r : Sigma (fun _ : ι => ℂ)) := ∑' n : ℕ,g p n*conj (g r n)
  let V (p r : Sigma (fun _ : ι => ℂ)) := B*(E+(if p.1=r.1 then X/(1+|p.2.im-r.2.im|)^4 else 0))
  have hentry (p) (hp : p∈W) (r) (hr : r∈W) :
      HasSum (fun n : ℕ => g p n*conj (g r n)) (G p r) ∧ ‖G p r‖≤V p r := by
    obtain ⟨hp₁,hp₂⟩ := mem_sigma.mp hp
    obtain ⟨hr₁,hr₂⟩ := mem_sigma.mp hr
    obtain ⟨q,hq,hqD,ψ,hψ,hdiag⟩ := hfamily p.1 hp₁ r.1 hr₁
    letI : NeZero q := ⟨hq.ne'⟩
    obtain ⟨hpr,hpi⟩ := hu _ hp₁ _ hp₂
    obtain ⟨hrr,hri⟩ := hu _ hr₁ _ hr₂
    have hstrip : (u p.2+conj (u r.2)).re∈Icc (0:ℝ) 2 := by
      simp only [add_re,Complex.conj_re];constructor <;> linarith [hpr.1,hpr.2,hrr.1,hrr.2]
    have hh := characterGramVector_hasSum ψ hψ hX' hstrip
    refine ⟨hh.summable.hasSum,?_⟩
    change ‖∑'n:ℕ,characterGramVector X (f p.1) (u p.2) n*conj (characterGramVector X (f r.1) (u r.2) n)‖≤_
    rw [hh.tsum_eq]
    apply (HB ψ hX hstrip).trans
    rw [hpi,hri]
    have htime := him _ hp₁ _ hp₂
    have htime' := him _ hr₁ _ hr₂
    have hdiff : |p.2.im-r.2.im|≤(L:ℝ) := abs_le.mpr ⟨by linarith [htime.1,htime'.2],by linarith [htime.2,htime'.1]⟩
    let H' := (q:ℝ)*(|p.2.im-r.2.im|+2)
    have hH' : 1≤H' := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hq : (1:ℝ)≤q)
      (by linarith [abs_nonneg (p.2.im-r.2.im)])
    have hcomp : H'≤H := by dsimp [H',H];gcongr <;> exact_mod_cast hqD
    have hmain : Real.sqrt H'*(1+Real.log H')≤E := mul_le_mul (Real.sqrt_le_sqrt hcomp)
      (add_le_add_right (Real.log_le_log (zero_lt_one.trans_le hH') hcomp) 1)
      (by linarith [Real.log_nonneg hH']) (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_left (add_le_add hmain ?_) hB.le
    by_cases h : ψ=1
    · simp [h,hdiag h]
    · simp only [if_neg h];split_ifs <;> positivity
  have hsym (p r) : V p r=V r p := by dsimp [V];rw [abs_sub_comm];by_cases h:p.1=r.1 <;> simp [h,eq_comm]
  have hrow (p) (hp : p∈W) : ∑r∈W,V p r≤B*(R*E+2*π*K*X) := by
    obtain ⟨hp₁,hp₂⟩ := mem_sigma.mp hp
    have hker := ingham_kernel_sum_le (S p.1) hK (him _ hp₁) (hcount _ hp₁) p.2.im
    simp only [W,V,←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,Finset.card_sigma,Nat.cast_sum]
    apply mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hB.le
    rw [sum_sigma,Finset.sum_eq_single p.1 (fun i _ hi => by simp [Ne.symm hi]) (fun hn => (hn hp₁).elim)]
    simp only [ite_true]
    calc _ = X*(∑z∈S p.1,1/(1+|p.2.im-z.im|)^4) := by
           rw [mul_sum];apply sum_congr rfl;intro z _;ring
         _ ≤ X*(2*π*K) := mul_le_mul_of_nonneg_left hker hX'.le
         _ = _ := by ring
  have h := sample_of_infinite_gram W J g G (D:=B*(R*E+2*π*K*X)) (mul_nonneg hB.le (add_nonneg (mul_nonneg hR hE)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hK) hX'.le)))
    (fun p hp r hr => (hentry p hp r hr).1)
    (fun p hp => (sum_le_sum fun r hr => (hentry p hp r hr).2).trans (hrow p hp))
    (fun r hr => (sum_le_sum fun p hp => ((hentry p hp r hr).2.trans_eq (hsym p r))).trans (hrow r hr)) a
  rw [show W=F.sigma S by rfl,Finset.sum_sigma] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  change B*(R*E+2*π*K*X) ≤ B*(1+2*π)*(K*X+R*Real.sqrt H*(1+Real.log H))
  rw [show R*Real.sqrt H*(1+Real.log H)=R*E by dsimp [E];ring]
  nlinarith only [mul_nonneg (mul_nonneg hB.le hK) hX'.le,
    mul_nonneg (mul_nonneg (mul_nonneg hB.le Real.pi_pos.le) hR) hE]

end AnalyticNumberTheory.SieveMethods
