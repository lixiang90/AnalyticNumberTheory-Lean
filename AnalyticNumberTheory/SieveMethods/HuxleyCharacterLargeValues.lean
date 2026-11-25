import AnalyticNumberTheory.SieveMethods.CharacterLargeValues
import AnalyticNumberTheory.SieveMethods.DirichletPolynomialHalfPlaneEnergy

/-!
# Huxley's large-value theorem for character families

The coefficient energy is computed on any real line. Every sample may
lie anywhere to its right. The fixed modulus and primitive family have
the same absolute constants, with correlation conductors q and Q².
-/
noncomputable section
open Real Complex Finset
open scoped Classical
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

/-- Large values on an arbitrary right half-plane, with `δ`-separation of
the ordinates within each character. The sample may lie in any closed
interval of real length `T ≥ 1`. -/
def HalfPlaneCharacterLargeValues {ι : Type*} (F : Finset ι) (f : ι→ℕ→ℂ) (D : ℕ) (c C : ℝ) : Prop :=
  ∀ {N : ℕ},1≤N → ∀(a : ℕ→ℂ) (σ₀ A : ℝ) {T δ V : ℝ},1≤T → 0<δ → 0<V → ∀S : ι→Finset ℂ,
    (∀ i∈F,∀z∈S i,σ₀≤z.re ∧ A≤z.im ∧ z.im≤A+T) →
    (∀ i∈F,∀z∈S i,∀w∈S i,z≠w → δ≤|z.im-w.im|) →
    (∀i∈F,∀z∈S i,V≤‖∑n∈Icc 1 N,a n*f i n*(n:ℂ)^(-z)‖) →
    let G := ∑n∈Icc 1 N,‖a n‖^2*(n:ℝ)^(-2*σ₀)
    c*Real.sqrt (3*D)*(1+Real.log (3*D))^2*G≤V^2 →
    (∑i∈F,((S i).card:ℝ))≤C*(1+δ⁻¹)*(N*G/V^2+N*(D:ℝ)*T*G^3*(1+Real.log ((D:ℝ)*(T+3)))^4/V^6)

private theorem halfPlane_of_strip {ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {D : ℕ} {c C : ℝ}
    (hD : 1≤D) (hc : 0<c) (hC : 0<C) (hf : ∀i∈F,∀n,‖f i n‖≤1)
    (HB : CharacterLargeValueBound F f D c C) :
    HalfPlaneCharacterLargeValues F f D (max c 4) (2*C) := by
  intro N hN a σ₀ A T δ V hT hδ hV S ht hsep hlarge
  let G := ∑n∈Icc 1 N,‖a n‖^2*(n:ℝ)^(-2*σ₀)
  let m := Real.sqrt (3*D)*(1+Real.log (3*D))^2
  change max c 4*Real.sqrt (3*D)*(1+Real.log (3*D))^2*G≤V^2 → _
  intro hth
  have hG : 0≤G := sum_nonneg (fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  let b (n:ℕ) := a n*(n:ℂ)^(-(σ₀:ℂ))
  let τ (z:ℂ) := z-(σ₀:ℂ)
  have hτ : Function.Injective τ := fun _ _ h => sub_left_inj.mp h
  have hr (z:ℂ) : (τ z).re=z.re-σ₀ := by simp [τ]
  have hi (z:ℂ) : (τ z).im=z.im := by simp [τ]
  have he : (∑n∈Icc 1 N,‖b n‖^2)=G := by
    apply sum_congr rfl;intro n hn
    have hn' := (mem_Icc.mp hn).1
    rw [show b n=a n*(n:ℂ)^(-(σ₀:ℂ)) by rfl,norm_mul,mul_pow,
      Complex.norm_natCast_cpow_of_pos (by omega : 0<n),Complex.neg_re,Complex.ofReal_re,
      ←Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    push_cast;ring_nf
  have hpoly (i:ι) (z:ℂ) : (∑n∈Icc 1 N,b n*f i n*(n:ℂ)^(-τ z))=
      ∑n∈Icc 1 N,a n*f i n*(n:ℂ)^(-z) := by
    apply sum_congr rfl;intro n hn
    have hn' := (mem_Icc.mp hn).1
    have hn₀ : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [b,τ];rw [show a n*(n:ℂ)^(-(σ₀:ℂ))*f i n*(n:ℂ)^(-(z-σ₀))=
       a n*f i n*((n:ℂ)^(-(σ₀:ℂ))*(n:ℂ)^(-(z-σ₀))) by ring,
       ←Complex.cpow_add _ _ hn₀,show -(σ₀:ℂ) + -(z-σ₀)= -z by ring]
  have hd := show (1:ℝ)≤D by exact_mod_cast hD
  have hm : 1≤m := one_le_mul_of_one_le_of_one_le ((Real.one_le_sqrt).mpr (by linarith))
    (one_le_pow₀ (by linarith only [Real.log_nonneg (show 1≤3*(D:ℝ) by linarith)]) )
  have hth' : max c 4*m*G≤V^2 := (by simpa only [m,mul_assoc] using hth)
  have hcut (i) (hiF:i∈F) (z) (hz:z∈S i) : (τ z).re≤1 := by
    by_contra! h
    have hh := dirichlet_polynomial_right_energy N b (f i) (hf i hiF) h.le
    rw [he,hpoly] at hh
    have ht' := (pow_le_pow_left₀ hV.le (hlarge i hiF z hz) 2).trans hh
    have hb : 4*G≤V^2 := (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by norm_num : 0≤(4:ℝ)) hm) hG).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right c 4) (by linarith only [hm])) hG).trans hth')
    nlinarith only [hb,ht',sq_pos_of_pos hV]
  let S' (i:ι) := (S i).image τ
  let L := ⌊T⌋₊+1
  have hL : 1≤L := by dsimp [L];omega
  have hTL : T<(L:ℝ) := by dsimp [L];push_cast;exact Nat.lt_floor_add_one T
  have hLT : (L:ℝ)≤T+1 := by dsimp [L];push_cast;linarith only [Nat.floor_le (by linarith : 0≤T)]
  have hs (i) (hiF:i∈F) (w) (hw:w∈S' i) : w.re∈Set.Icc (0:ℝ) 1 ∧ A≤w.im ∧ w.im<A+L := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
    have ht' := ht i hiF z hz
    exact ⟨⟨by rw [hr];linarith only [ht'.1],hcut i hiF z hz⟩,by rw [hi];exact ht'.2.1,by rw [hi];linarith only [hTL,ht'.2.2]⟩
  have hunit : UnitHeightCapacity F S' (1+δ⁻¹) := by
    intro i hiF x
    rw [show S' i=(S i).image τ by rfl,filter_image,card_image_of_injective _ hτ]
    simpa only [hi] using separated_heights_unit_capacity (S i) hδ (hsep i hiF) x
  have hh := HB hN hL A S' (K:=1+δ⁻¹) (by positivity) hs hunit b hV (fun i hiF w hw => by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
    rw [hpoly];exact hlarge i hiF z hz)
  dsimp only at hh
  rw [he] at hh
  have hh' := hh (by
    apply le_trans _ hth
    gcongr;exact le_max_left c 4)
  simp only [S',card_image_of_injective _ hτ] at hh'
  let H := (D:ℝ)*(T+3)
  have hlog : 1+Real.log ((D:ℝ)*(L+2))≤1+Real.log H := by
    have harg : (D:ℝ)*(L+2)≤H := mul_le_mul_of_nonneg_left (by linarith only [hLT] : (L:ℝ)+2≤T+3) (Nat.cast_nonneg D)
    exact add_le_add_right (Real.log_le_log (mul_pos (by linarith only [hd]) (by linarith only [Nat.cast_nonneg (α:=ℝ) L])) harg) 1
  have hl := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd (show 1≤(L:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) L]))
  have ha : 0≤(N:ℝ)*G/V^2 := by positivity
  have haa : (N:ℝ)*D*L*G^3*(1+Real.log ((D:ℝ)*(L+2)))^4/V^6 ≤ (N:ℝ)*D*(2*T)*G^3*(1+Real.log H)^4/V^6 := by
    gcongr <;> linarith
  let Y := (N:ℝ)*D*T*G^3*(1+Real.log H)^4/V^6
  have hay : (N:ℝ)*D*(2*T)*G^3*(1+Real.log H)^4/V^6=2*Y := by dsimp only [Y];ring
  rw [hay] at haa
  apply hh'.trans
  change C*(1+δ⁻¹)*(_+_) ≤ 2*C*(1+δ⁻¹)*(_+Y)
  have hcoef : 0≤C*(1+δ⁻¹) := mul_nonneg hC.le (by positivity)
  calc _ ≤ (C*(1+δ⁻¹))*((N:ℝ)*G/V^2+2*Y) := mul_le_mul_of_nonneg_left (add_le_add le_rfl haa) hcoef
       _ ≤ _ := by nlinarith only [mul_nonneg hcoef ha]

/-- Huxley's estimate for both the full family at one modulus and the
primitive characters of all conductors up to Q, with uniform constants. -/
theorem huxley_character_large_values :
    ∃c C : ℝ,0<c ∧ 0<C ∧
    (∀ q : ℕ, [NeZero q] → HalfPlaneCharacterLargeValues (univ : Finset (DirichletCharacter ℂ q))
      (fun χ n => χ n) q c C) ∧
    (∀ Q : ℕ,1≤Q → HalfPlaneCharacterLargeValues (primitiveCharacterFamily Q) (fun p n => p.2 n) (Q^2) c C) := by
  obtain ⟨c,C,hc,hC,HC⟩ := character_large_values_of_correlation
  refine ⟨max c 4,2*C,lt_of_lt_of_le hc (le_max_left c _),by positivity,?_,?_⟩
  · intro q _ N hN
    have hq : 1≤q := NeZero.one_le
    exact halfPlane_of_strip hq hc hC (fun χ _ n => χ.norm_le_one _) (HC hq (fixed_modulus_correlation_family q)) hN
  · intro Q hQ N hN
    have hD := Nat.one_le_pow 2 Q hQ
    exact halfPlane_of_strip hD hc hC (fun p _ n => p.2.norm_le_one _) (HC hD (primitive_correlation_family Q)) hN

end AnalyticNumberTheory.SieveMethods
