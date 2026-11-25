import AnalyticNumberTheory.PrimeDistribution.InghamTypeI
import AnalyticNumberTheory.SieveMethods.HuxleyLargeValues
/-!
# The polynomial alternative in Huxley's density theorem

The quadratic large-value term is largest at the upper cutoff. On the strip
from three quarters to one the sixth-power term is largest at the lower cutoff.
-/
noncomputable section
open Finset Complex Real
open scoped Classical
open AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.PrimeDistribution

private theorem huxley_block_count {K : ℝ} (hK : 0<K) :
    ∃ D > (0:ℝ), ∀ {T X U i : ℕ}, 1≤T → 1≤X → (U:ℝ)≤(T:ℝ)^(3/2:ℝ) →
      i∈Ingham.blocks X U → ∀ {σ : ℝ}, σ∈Set.Icc (3/4:ℝ) 1 →
      ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ n.divisors.card) → ∀ S : Finset ℂ,
      (∀ z∈S, σ ≤ z.re ∧ (T:ℝ)≤z.im ∧ z.im≤2*T) →
      (∀ u : ℝ, ((S.filter (fun z => u≤z.im ∧ z.im≤u+1)).card:ℝ) ≤ K*(1+Real.log T)) →
      (∀ z∈S, 1/(64*(1+Real.log T)) ≤ ‖dirichletPoly (Ingham.blockCoeff a X U i) (2*2^i) z‖) →
      (S.card:ℝ) ≤ D*(1+Real.log T)^20*((U:ℝ)^(2*(1-σ))+(T:ℝ)*(X:ℝ)^(4-6*σ)) := by
  let C := 162*(1+8000*π)
  let D := 512*K*(C*64^2+4*C^3*64^6)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro T X U i hT hX hU hi σ hσ a ha S hS hcell hdet
  let M := 2^i
  let L := 1+Real.log T
  let E := 1-2*σ
  let G := 54*L^3*(M:ℝ)^E
  let B := G*((1+8000*π)*(1+Real.log (2*(M:ℝ))))
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast (Nat.one_le_pow i 2 (by decide))
  have hM0 : 0<(M:ℝ) := by linarith
  have hTr : (1:ℝ)≤T := by exact_mod_cast hT
  have hT0 : 0<(T:ℝ) := by linarith
  have hXr : (1:ℝ)≤X := by exact_mod_cast hX
  have hX0 : 0<(X:ℝ) := by linarith
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg hTr]
  obtain ⟨hXM,hMU⟩ := (mem_filter.mp hi).2
  change X<2*M at hXM
  change M≤U at hMU
  have hMU' : (M:ℝ)≤U := by exact_mod_cast hMU
  have hXlow : (X:ℝ)<2*M := by exact_mod_cast hXM
  have hlog : 1+Real.log (2*(M:ℝ)) ≤ 3*L := by
    rw [Real.log_mul (by norm_num) hM0.ne']
    have hl := Real.log_le_log hM0 (hMU'.trans hU)
    rw [Real.log_rpow hT0] at hl
    dsimp [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),Real.log_nonneg hTr]
  have hlog₀ : 0≤1+Real.log (2*(M:ℝ)) := by linarith [Real.log_nonneg (by linarith : 1≤2*(M:ℝ))]
  have henergy : ∑ n∈Icc 1 (2*M), ‖Ingham.blockCoeff a X U i n‖^2*(n:ℝ)^(-2*σ) ≤ G := by
    apply (Ingham.block_energy (X:=X) (U:=U) (i:=i) ha (by linarith [hσ.1])).trans
    change (2*(M:ℝ))*(1+Real.log (2*(M:ℝ)))^3*(M:ℝ)^(-2*σ) ≤ _
    calc
      _ ≤ (2*(M:ℝ))*(3*L)^3*(M:ℝ)^(-2*σ) := by gcongr
      _ = G := by dsimp only [G,E]; rw [show 1-2*σ=1+(-2)*σ by ring,Real.rpow_add hM0,Real.rpow_one]; ring
  have hm1 : 1 ≤ M := by exact_mod_cast hMr
  have h := huxley_dirichletPoly_large_values S (Ingham.blockCoeff a X U i) (N:=2*M) (by omega)
    id (by positivity : 0 ≤ 1/(64*L)) (by positivity : 0 ≤ K*L) hTr (fun z hz => (hS z hz).1)
    (t₀:=(T:ℝ)) (fun z hz => ⟨(hS z hz).2.1,by change z.im ≤ _; linarith [(hS z hz).2.2]⟩)
    hcell henergy hdet
  push_cast at h
  change (S.card:ℝ)*(1/(64*L))^6 ≤ 128*(K*L)*(2*M)*(1+Real.log (T+1))*(B*(1/(64*L))^4+T*B^3) at h
  have hlogT : 1+Real.log ((T:ℝ)+1) ≤ 2*L := by
    have hh := Real.log_le_log (by linarith) (by linarith : (T:ℝ)+1≤2*T)
    rw [Real.log_mul (by norm_num) hT0.ne'] at hh
    dsimp [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),Real.log_nonneg hTr]
  have hB : B ≤ C*L^4*(M:ℝ)^E := by
    calc
      B ≤ G*((1+8000*π)*(3*L)) := by dsimp only [B,G]; gcongr
      _ = _ := by dsimp only [C,G]; ring
  have hB₀ : 0 ≤ B := by dsimp [B,G]; positivity
  have hc : (S.card:ℝ)*(1/(64*L))^6 ≤ 128*(K*L)*(2*M)*(2*L)*
      ((C*L^4*(M:ℝ)^E)*(1/(64*L))^4+T*(C*L^4*(M:ℝ)^E)^3) := by
    apply h.trans; gcongr
  have hp₁eq : (M:ℝ)*(M:ℝ)^E = (M:ℝ)^(2*(1-σ)) := by
    rw [show 2*(1-σ)=1+E by dsimp [E]; ring,Real.rpow_add hM0,Real.rpow_one]
  have hp₂eq : (M:ℝ)*((M:ℝ)^E)^3 = (M:ℝ)^(4-6*σ) := by
    rw [←Real.rpow_mul_natCast hM0.le,show 4-6*σ=1+E*(3:ℕ) by dsimp [E]; push_cast; ring,Real.rpow_add hM0,Real.rpow_one]
  have hp₂ : (M:ℝ)^(4-6*σ) ≤ 4*(X:ℝ)^(4-6*σ) := by
    have he : 4-6*σ≤0 := by linarith [hσ.1]
    have hh := Real.rpow_le_rpow_of_nonpos (by linarith : 0<(X:ℝ)/2) (by linarith : (X:ℝ)/2≤M) he
    apply hh.trans
    rw [Real.div_rpow hX0.le (by norm_num),div_eq_mul_inv,←Real.rpow_neg (by norm_num : 0≤(2:ℝ))]
    have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (by linarith [hσ.2] : -(4-6*σ)≤2)
    rw [Real.rpow_two] at h2
    calc
      _ ≤ (X:ℝ)^(4-6*σ)*2^2 := by gcongr
      _ = _ := by ring
  let U₁ := (U:ℝ)^(2*(1-σ))
  let X₂ := (X:ℝ)^(4-6*σ)
  have hP₁ : (M:ℝ)*(M:ℝ)^E ≤ U₁ := hp₁eq.le.trans (Real.rpow_le_rpow hM0.le hMU' (by linarith [hσ.2]))
  have hP₂ : (M:ℝ)*((M:ℝ)^E)^3 ≤ 4*X₂ := hp₂eq.le.trans hp₂
  have hh₁ : 0≤U₁ := by dsimp [U₁]; positivity
  have hh₂ : 0≤X₂ := by dsimp [X₂]; positivity
  have hX₂ : 0≤(T:ℝ)*X₂ := by positivity
  have h₀ : L≠0 := by linarith
  rw [div_pow,one_pow,←div_eq_mul_one_div,div_le_iff₀ (by positivity)] at hc
  have hn : (S.card:ℝ) ≤ 512*K*(C*64^2*L^8*((M:ℝ)*(M:ℝ)^E)+
        C^3*64^6*L^20*(T*((M:ℝ)*((M:ℝ)^E)^3))) := by
    apply hc.trans_eq; field_simp; ring
  apply hn.trans
  have hL8 : L^8≤L^20 := pow_le_pow_right₀ hL (by decide)
  calc
    _ ≤ 512*K*(C*64^2*L^20*U₁+C^3*64^6*L^20*((T:ℝ)*(4*X₂))) := by gcongr
    _ ≤ D*L^20*(U₁+T*X₂) := by
      dsimp only [D]
      have h₁ : 0 ≤ K*C*L^20*(T*X₂) := by positivity
      have h₂ : 0 ≤ K*C^3*L^20*U₁ := by positivity
      linarith only [h₁,h₂]

/-- On the strip `3/4 ≤ σ ≤ 1`, a divisor-bounded tail detecting every point
of a height band has at most
`O_K((log T)^21 (U^(2−2σ) + T X^(4−6σ)))` large values. -/
theorem huxley_typeI_count {K : ℝ} (hK : 0<K) :
    ∃ C > (0:ℝ), ∀ {T X U : ℕ}, 1≤T → 1≤X → 1≤U → (U:ℝ)≤(T:ℝ)^(3/2:ℝ) →
      ∀ {σ : ℝ}, σ∈Set.Icc (3/4:ℝ) 1 → ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ n.divisors.card) →
      ∀ S : Finset ℂ, (∀ z∈S, σ ≤ z.re ∧ (T:ℝ)≤z.im ∧ z.im≤2*T) →
      (∀ u : ℝ, ((S.filter (fun z => u≤z.im ∧ z.im≤u+1)).card:ℝ) ≤ K*(1+Real.log T)) →
      (∀ z∈S, 1/8 ≤ ‖∑ n∈Ioc X U, a n*(n:ℂ)^(-z)‖) →
      (S.card:ℝ) ≤ C*(1+Real.log T)^21*((U:ℝ)^(2*(1-σ))+(T:ℝ)*(X:ℝ)^(4-6*σ)) := by
  obtain ⟨D,hD,hd⟩ := huxley_block_count hK
  refine ⟨4*D,by positivity,?_⟩
  intro T X U hT hX hU hUT σ hσ a ha S hS hcell hdet
  let L := 1+Real.log T
  let W := (U:ℝ)^(2*(1-σ))+(T:ℝ)*(X:ℝ)^(4-6*σ)
  let J := Ingham.blocks X U
  let P (i : ℕ) (z : ℂ) := dirichletPoly (Ingham.blockCoeff a X U i) (2*2^i) z
  let F (i : ℕ) := S.filter fun z => 1/(64*L) ≤ ‖P i z‖
  have hTr : (1:ℝ)≤T := by exact_mod_cast hT
  have hT0 : 0<(T:ℝ) := by linarith
  have hUr : (1:ℝ)≤U := by exact_mod_cast hU
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg hTr]
  have hW : 0≤W := by dsimp [W]; positivity
  have hJ : (J.card:ℝ) ≤ 4*L := by
    have hlog := Real.log_le_log (by linarith : 0<(U:ℝ)) hUT
    rw [Real.log_rpow hT0] at hlog
    apply (Ingham.block_count hU).trans
    dsimp [L]; linarith [Real.log_nonneg hTr]
  have hsub : S ⊆ J.biUnion F := by
    intro z hz
    rw [mem_biUnion]; by_contra! h
    have hp (i : ℕ) (hi : i∈J) : ‖P i z‖ ≤ 1/(64*L) := by
      apply le_of_not_ge
      exact fun hn => h i hi (mem_filter.mpr ⟨hz,hn⟩)
    have hv := hdet z hz
    rw [Ingham.tail_by_blocks] at hv
    have hh := (hv.trans (norm_sum_le ..)).trans (sum_le_sum hp)
    simp only [sum_const,nsmul_eq_mul] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hJ (by positivity))
    have hl : 4*L*(1/(64*L)) = (1/16:ℝ) := by field_simp; ring
    linarith only [hh',hl]
  have hb (i : ℕ) (hi : i ∈ J) : ((F i).card:ℝ) ≤ D*L^20*W :=
    hd hT hX hUT hi hσ a ha (F i) (fun z hz => hS z (mem_filter.mp hz).1) (fun u =>
      (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ (filter_subset ..)))).trans (hcell u))
      (fun z hz => (mem_filter.mp hz).2)
  have hc := (card_le_card hsub).trans card_biUnion_le
  have hc' : (S.card:ℝ) ≤ ∑ i∈J, ((F i).card:ℝ) := by exact_mod_cast hc
  have hh := hc'.trans (sum_le_sum hb)
  simp only [sum_const,nsmul_eq_mul] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_right hJ (by positivity))).trans_eq (by dsimp [L,W]; ring)

end AnalyticNumberTheory.PrimeDistribution
