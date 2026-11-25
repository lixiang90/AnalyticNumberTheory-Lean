import AnalyticNumberTheory.SieveMethods.FullCharacterWindow
import AnalyticNumberTheory.SieveMethods.HeightWindowCover
import AnalyticNumberTheory.SieveMethods.HuxleyWindowLength

/-!
# Large values of character Dirichlet polynomials

A local mean square is applied on height windows whose length is determined
by the coefficient energy and the lower bound at the sample points.
-/
noncomputable section
open Real Complex Finset
open scoped Classical
namespace AnalyticNumberTheory.SieveMethods

/-- The large-value inequality, with the coefficients measured at the left
edge of a strip of width one and with arbitrary height origin. -/
def CharacterLargeValueBound {ι : Type*} (F : Finset ι) (f : ι→ℕ→ℂ) (D : ℕ) (c C : ℝ) : Prop :=
  ∀ {N L : ℕ},1≤N → 1≤L → ∀ (A : ℝ) (S : ι→Finset ℂ) {K : ℝ},0≤K →
    (∀ i∈F,∀z∈S i,z.re∈Set.Icc (0:ℝ) 1 ∧ A≤z.im ∧ z.im<A+L) →
    UnitHeightCapacity F S K → ∀(a : ℕ→ℂ) {V : ℝ},0<V →
    (∀i∈F,∀z∈S i,V≤‖∑n∈Icc 1 N,a n*f i n*(n:ℂ)^(-z)‖) →
    let G := ∑n∈Icc 1 N,‖a n‖^2
    c*Real.sqrt (3*D)*(1+Real.log (3*D))^2*G≤V^2 →
    (∑i∈F,((S i).card:ℝ))≤C*K*(N*G/V^2+N*(D:ℝ)*L*G^3*(1+Real.log ((D:ℝ)*(L+2)))^4/V^6)

private theorem threshold_energy {ι : Type*} (F : Finset ι) (S : ι→Finset ℂ)
    (P : ι→ℂ→ℂ) {V : ℝ} (hV : 0≤V) (hP : ∀i∈F,∀z∈S i,V≤‖P i z‖) :
    (∑i∈F,((S i).card:ℝ))*V^2≤∑i∈F,∑z∈S i,‖P i z‖^2 := by
  rw [sum_mul];apply sum_le_sum;intro i hi
  simpa only [sum_const,nsmul_eq_mul] using sum_le_sum (s:=S i) (fun z hz => pow_le_pow_left₀ hV (hP i hi z hz) 2)

private theorem huxley_balance {C K N D L G V ℓ : ℝ} (hC : 0<C)
    (hK : 0≤K) (hN : 0≤N) (hD : 0≤D) (hL : 0≤L) (hG : 0<G) (hV : 0<V) :
    (2+6*L*D*ℓ^4/(V^2/(2*C*G))^2)*(2*C*K*N*G/V^2)≤
      (4*C+48*C^3)*K*(N*G/V^2+N*D*L*G^3*ℓ^4/V^6) := by
  let X := N*G/V^2
  let Y := N*D*L*G^3*ℓ^4/V^6
  have hX : 0≤X := by dsimp [X];positivity
  have hY : 0≤Y := by dsimp [Y];positivity
  calc _ = 4*C*K*X+48*C^3*K*Y := by dsimp only [X,Y];field_simp;ring
       _ ≤ (4*C+48*C^3)*K*(X+Y) := by
         nlinarith only [mul_nonneg (mul_nonneg hC.le hK) hY,mul_nonneg (mul_nonneg (pow_nonneg hC.le 3) hK) hX]

/-- Huxley's two-term large-value bound with absolute constants for every
family of characters having a common correlation conductor bound. -/
theorem character_large_values_of_correlation :
    ∃c C : ℝ,0<c ∧ 0<C ∧ ∀ {ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {D : ℕ},1≤D →
      CharacterCorrelationFamily F f D → CharacterLargeValueBound F f D c C := by
  obtain ⟨C,hC,HC⟩ := full_character_window_mean
  refine ⟨2*C,4*C+48*C^3,by positivity,by positivity,?_⟩
  intro ι F f D hD hF N L hN hL A S K hK ht hcap a V hV hlarge
  let G := ∑n∈Icc 1 N,‖a n‖^2
  change 2*C*_*_*G ≤ V^2 → _
  intro hmin
  have hG := show 0≤G from sum_nonneg (fun _ _ => sq_nonneg _)
  let ℓ := 1+Real.log ((D:ℝ)*(L+2))
  change (∑i∈F,((S i).card:ℝ))≤(4*C+48*C^3)*K*(N*G/V^2+N*(D:ℝ)*L*G^3*ℓ^4/V^6)
  rcases hG.eq_or_lt with hz|hg
  · have hu := HC hD hF A S hK ht hcap hN a
    have hd := threshold_energy F S _ hV.le hlarge
    change _ ≤ _*G at hu
    rw [←hz,mul_zero] at hu
    have hs := nonpos_of_mul_nonpos_left (hd.trans hu) (sq_pos_of_pos hV)
    simpa [←hz] using hs
  let U := V^2/(2*C*G)
  have hU : Real.sqrt (3*D)*(1+Real.log (3*D))^2≤U := by
    apply (le_div_iff₀ (show 0<2*C*G by positivity)).mpr
    linarith only [hmin]
  obtain ⟨W,hW,_,hcost,hcover⟩ := huxley_window_length hD hL hU
  have hwindow : ∀(S' : ι→Finset ℂ), (∀i∈F,S' i⊆S i) → ∀ b : ℝ,
      (∀i∈F,∀z∈S' i,b≤z.im ∧ z.im<b+W) → (∑i∈F,((S' i).card:ℝ))≤2*C*K*N*G/V^2 := by
    intro S' hsub b hbox
    have hc' : UnitHeightCapacity F S' K := by
      intro i hi b
      apply le_trans _ (hcap i hi b)
      exact_mod_cast card_le_card (filter_subset_filter _ (hsub i hi))
    have hu := HC hD hF b S' hK (fun i hi z hz => ⟨(ht i hi z ((hsub i hi) hz)).1,hbox i hi z hz⟩) hc' hN a
    let R := ∑i∈F,((S' i).card:ℝ)
    have hr : 0≤R := sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hd := threshold_energy F S' _ hV.le (fun i hi z hz => hlarge i hi z ((hsub i hi) hz))
    let B := Real.sqrt ((D:ℝ)*(W+2))*(1+Real.log ((D:ℝ)*(W+2)))^2
    have hh : R*V^2≤C*(K*N+R*B)*G := (hd.trans hu).trans_eq (by dsimp only [R,B,G];ring)
    have ha := (le_div_iff₀ (show 0<2*C*G by positivity)).mp hcost
    change B*(2*C*G)≤V^2 at ha
    apply (le_div_iff₀ (sq_pos_of_pos hV)).mpr
    change R*V^2 ≤ _
    nlinarith only [hh,mul_le_mul_of_nonneg_left ha hr]
  have hb : 0≤2*C*K*N*G/V^2 := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hK) (Nat.cast_nonneg _)) hg.le) (sq_nonneg _)
  have hh := height_window_cover S (Nat.cast_nonneg L) (by exact_mod_cast (Nat.zero_lt_of_lt hW) : 0<(W:ℝ)) hb
    (fun i hi z hz => (ht i hi z hz).2) hwindow
  apply hh.trans ((mul_le_mul_of_nonneg_right hcover hb).trans ?_)
  exact huxley_balance hC hK (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hg hV

end AnalyticNumberTheory.SieveMethods
