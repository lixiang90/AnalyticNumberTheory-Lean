import AnalyticNumberTheory.SieveMethods.FullCharacterSampling

/-!
# Translation of full character sampling

An arbitrary vertical translation of the sampling interval multiplies
each coefficient by a common phase of modulus one.
-/
noncomputable section
open Real Complex Finset
open scoped Classical
namespace AnalyticNumberTheory.SieveMethods

/-- An upper bound for the number of ordinates of one character in every
half-open interval of length one. -/
def UnitHeightCapacity {ι : Type*} (F : Finset ι) (S : ι→Finset ℂ) (K : ℝ) : Prop :=
  ∀i∈F,∀b : ℝ,(((S i).filter fun z => b≤z.im ∧ z.im<b+1).card:ℝ)≤K

/-- Full character sampling on an arbitrary vertical window. -/
def CharacterWindowMean {ι : Type*} (F : Finset ι) (f : ι→ℕ→ℂ) (D : ℕ) (C : ℝ) : Prop :=
  ∀{L : ℕ} (A : ℝ) (S : ι→Finset ℂ) {K : ℝ},0≤K →
    (∀i∈F,∀z∈S i,z.re∈Set.Icc (0:ℝ) 1 ∧ A≤z.im ∧ z.im<A+L) →
    UnitHeightCapacity F S K → ∀{N : ℕ},1≤N → ∀a : ℕ→ℂ,
    let H := (D:ℝ)*((L:ℝ)+2)
    let R := ∑i∈F,((S i).card:ℝ)
    (∑i∈F,∑z∈S i,‖∑n∈Icc 1 N,a n*f i n*(n:ℂ)^(-z)‖^2) ≤
      C*(K*N+R*Real.sqrt H*(1+Real.log H)^2)*(∑n∈Icc 1 N,‖a n‖^2)

/-- The same window constant works for every translate, support and family. -/
theorem full_character_window_mean :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {D : ℕ},1≤D →
      CharacterCorrelationFamily F f D → CharacterWindowMean F f D C := by
  obtain ⟨C,hC,HC⟩ := full_character_sampling
  refine ⟨C,hC,?_⟩
  intro ι F f D hD hF L A S K hK hz hc N hN a
  let v := (A:ℂ)*I
  let τ (z:ℂ) := z-v
  have hτ : Function.Injective τ := fun _ _ h => sub_left_inj.mp h
  have hr (z:ℂ) : (τ z).re=z.re := by simp [τ,v]
  have hi (z:ℂ) : (τ z).im=z.im-A := by simp [τ,v]
  let S' (i:ι) := (S i).image τ
  let b (n:ℕ) := a n*(n:ℂ)^(-v)
  have hm (i) (hiF:i∈F) (w) (hw:w∈S' i) : 0≤w.im ∧ w.im<L := by
    obtain ⟨z,hz',rfl⟩ := mem_image.mp hw
    have ht := (hz i hiF z hz').2
    rw [hi];constructor <;> linarith [ht.1,ht.2]
  have hcap (i) (hiF:i∈F) (j:ℕ) (_:j<L) :
      (((S' i).filter fun w => ⌊w.im⌋₊=j).card:ℝ)≤K := by
    rw [show S' i=(S i).image τ by rfl,filter_image,card_image_of_injective _ hτ]
    apply le_trans _ (hc i hiF (A+j))
    exact_mod_cast card_le_card (show ((S i).filter fun z => ⌊(τ z).im⌋₊=j) ⊆
        (S i).filter (fun z => A+j≤z.im ∧ z.im<A+j+1) from by
      intro z h
      obtain ⟨h,e⟩ := mem_filter.mp h
      have he := (Nat.floor_eq_iff (hm i hiF _ (mem_image_of_mem τ h)).1).mp e
      rw [hi] at he
      exact mem_filter.mpr ⟨h,by constructor <;> linarith [he.1,he.2]⟩)
  have hu (i) (hiF:i∈F) (w) (hw:w∈S' i) : (id w).re∈Set.Icc (0:ℝ) 1 ∧ (id w).im=w.im := by
    obtain ⟨z,hz',rfl⟩ := mem_image.mp hw
    exact ⟨(hr z) ▸ (hz i hiF z hz').1,rfl⟩
  have hterm (i:ι) (z:ℂ) (n:ℕ) (hn:n∈Icc 1 N) :
      b n*f i n*(n:ℂ)^(-(τ z))=a n*f i n*(n:ℂ)^(-z) := by
    have hn' := (mem_Icc.mp hn).1
    have hn₀ : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [b,τ]
    rw [show a n*(n:ℂ)^(-v)*f i n*(n:ℂ)^(-(z-v))=a n*f i n*((n:ℂ)^(-v)*(n:ℂ)^(-(z-v))) by ring,
      ←Complex.cpow_add _ _ hn₀,show -v + -(z-v)= -z by ring]
  have hsum (i:ι) : (∑w∈S' i,‖∑n∈Icc 1 N,b n*f i n*(n:ℂ)^(-id w)‖^2)=
      ∑z∈S i,‖∑n∈Icc 1 N,a n*f i n*(n:ℂ)^(-z)‖^2 := by
    rw [show S' i=(S i).image τ by rfl,sum_image (fun _ _ _ _ he => hτ he)]
    apply sum_congr rfl;intro z _
    rw [show (∑n∈Icc 1 N,b n*f i n*(n:ℂ)^(-id (τ z)))=
        ∑n∈Icc 1 N,a n*f i n*(n:ℂ)^(-z) by exact sum_congr rfl (hterm i z)]
  have henergy : (∑n∈Icc 1 N,‖b n‖^2)=∑n∈Icc 1 N,‖a n‖^2 := by
    apply sum_congr rfl;intro n hn
    have hn' := (mem_Icc.mp hn).1
    simp [b,norm_mul,Complex.norm_natCast_cpow_of_pos (by omega : 0<n),v]
  have hh := HC hD hF S' hK hm hcap id hu hN b
  dsimp only at hh ⊢
  simpa only [hsum,henergy,S',card_image_of_injective _ hτ] using hh

end AnalyticNumberTheory.SieveMethods
