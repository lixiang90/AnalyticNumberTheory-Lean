import AnalyticNumberTheory.ExponentialSums.LogPhaseDifferences
import AnalyticNumberTheory.ExponentialSums.DifferencingBounds

/-!
# Cancellation in logarithmic blocks of arbitrary polynomial height

The number of differencing steps depends only on the power relating the
height to the length. All estimates are uniform in the endpoint of the block.
-/

open Real Finset

namespace AnalyticNumberTheory.ExponentialSums

private theorem curvature_scale {A D m h p τ : ℝ} (k : ℕ) (hA : 0<A) (hD : 0<D)
    (hm : 1≤m) (hh : 1≤h) (hp : 1≤p) (hp' : p≤h^k)
    (hh' : h^(k+2)≤D*√m)
    (ht : m^k*√m≤τ) (ht' : τ≤m^(k+1)*√m) :
    let lam := A*p*τ/m^(k+2)
    √lam ≤ √(A*D)/h ∧ (√lam)⁻¹ ≤ √(D/A)*m/h := by
  let lam := A*p*τ/m^(k+2)
  have hm0 : 0<m := by linarith
  have hh0 : 0<h := by linarith
  have hτ : 0<τ := (show 0<m^k*√m by positivity).trans_le ht
  have hp0 : 0<p := by linarith
  have hlam : 0<lam := by dsimp [lam]; positivity
  have hU : lam*h^2 ≤ A*D := by
    calc lam*h^2 = A*p*h^2*τ/m^(k+2) := by dsimp [lam]; ring
         _ ≤ A*h^k*h^2*(m^(k+1)*√m)/m^(k+2) := by gcongr
         _ = A*h^(k+2)*√m/m := by rw [pow_add h k 2,pow_add m k 2,pow_succ]; field_simp; ring
         _ ≤ A*(D*√m)*√m/m := by gcongr
         _ = A*D := by field_simp; nlinarith only [Real.sq_sqrt hm0.le,mul_self_sqrt hm0.le]
  have hL : h^2 ≤ D/A*m^2*lam := by
    calc h^2 ≤ h^(k+2) := pow_le_pow_right₀ hh (by omega)
         _ ≤ D*√m := hh'
         _ = D/A*m^2*(A*1*(m^k*√m)/m^(k+2)) := by rw [pow_add m k 2]; field_simp
         _ ≤ D/A*m^2*lam := by dsimp [lam]; gcongr
  constructor
  · change √lam ≤ _
    rw [le_div_iff₀ hh0]
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow,Real.sq_sqrt hlam.le,Real.sq_sqrt (by positivity : 0≤A*D)]
    exact hU
  · change (√lam)⁻¹ ≤ _
    rw [le_div_iff₀ hh0]
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow,mul_pow,inv_pow,Real.sq_sqrt hlam.le,Real.sq_sqrt (by positivity : 0≤D/A),
      ← div_eq_inv_mul,div_le_iff₀ hlam]
    exact hL

private theorem log_leaf (k : ℕ) :
    ∃ C≥0, ∀ {M H : ℕ} {τ : ℝ}, 1≤M → 1≤H → H≤M →
      (H:ℝ)^(k+2) ≤ (2:ℝ)^(k+2)*√(M:ℝ) →
      (M:ℝ)^k*√(M:ℝ) ≤ |τ| → |τ| ≤ (M:ℝ)^(k+1)*√(M:ℝ) →
      ∀ w : Fin k → ℕ, (∀ i, 1≤w i ∧ w i≤H) → ∀ b : ℕ, b≤2*M →
      ‖∑ n ∈ Ioc M b,e (iterForwardDiff (fun i => (w i:ℝ)) (logPhase τ 0) n)‖ ≤ C*(M:ℝ)/H := by
  let K := (k:ℝ)+3
  let D := (2:ℝ)^(k+2)
  let A := ((k+1).factorial:ℝ)/K^(k+2)
  have hK : 0<K := by dsimp [K]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  let B := 20*K^(k+2)+20
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨B*(√(A*D)+√(D/A)),by positivity,?_⟩
  intro M H τ hm hh hhm hh' ht ht' w hw b hb
  have hm' : (1:ℝ)≤M := by exact_mod_cast hm
  have hh'₁ : (1:ℝ)≤H := by exact_mod_cast hh
  have hτ : 0 < |τ| := (show 0<(M:ℝ)^k*√(M:ℝ) by positivity).trans_le ht
  let p := ∏ i,(w i:ℝ)
  have hp : 1≤p := Finset.one_le_prod₀ (fun i _ => by exact_mod_cast (hw i).1)
  have hp' : p≤(H:ℝ)^k := by
    simpa [p] using Finset.prod_le_prod₀ (s:=univ) (fun i _ => Nat.cast_nonneg (w i))
      (fun i _ => (show (w i:ℝ)≤H by exact_mod_cast (hw i).2))
  let lam := A*p*|τ|/(M:ℝ)^(k+2)
  have ⟨h₁,h₂⟩ := curvature_scale k hA hD hm' hh'₁ hp hp' hh' ht ht'
  by_cases hmb : M<b
  · have hv := iterForwardDiff_logPhase_bound hm hmb hb (fun i => (w i:ℝ))
      (fun i => by exact_mod_cast (hw i).1) (fun i => by exact_mod_cast (hw i).2.trans hhm)
      (a:=0) ⟨le_rfl,zero_le_one⟩ hτ
    have he : p * |τ| * ((k+1).factorial:ℝ)/(K*M)^(k+2) = lam := by
      dsimp [lam,A]; rw [mul_pow]; field_simp <;> ring
    change _ ≤ B*(((b:ℝ)-M)*√(p * |τ| * ((k+1).factorial:ℝ)/(K*M)^(k+2))+
      (√(p * |τ| * ((k+1).factorial:ℝ)/(K*M)^(k+2)))⁻¹) at hv
    rw [he] at hv
    have hd : (b:ℝ)-M≤M := by linarith [show (b:ℝ)≤2*M by exact_mod_cast hb]
    apply hv.trans
    calc B*(((b:ℝ)-M)*√lam+(√lam)⁻¹) ≤ B*((M:ℝ)*(√(A*D)/H)+(√(D/A)*M/H)) := by
              gcongr
         _ = _ := by ring
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty,norm_zero]
    positivity

private theorem log_window (k : ℕ) :
    ∃ κ C : ℝ, 0<κ ∧ 0<C ∧ ∀ {M b : ℕ} {τ : ℝ}, 1≤M → b≤2*M →
      (M:ℝ)^k*√(M:ℝ) ≤ |τ| → |τ| ≤ (M:ℝ)^(k+1)*√(M:ℝ) →
      ‖∑ n ∈ Ioc M b,e (logPhase τ 0 n)‖ ≤ C*(M:ℝ)^(1-κ) := by
  obtain ⟨C,hC,leaf⟩ := log_leaf k
  obtain ⟨D,hD,tree⟩ := iterated_forwardDiff_cancellation k C hC
  let δ := 1/(2*((k:ℝ)+2))
  let κ := δ/((2:ℝ)^k)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ₁ : δ≤1 := by
    dsimp [δ]; apply (div_le_iff₀ (by positivity)).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hκ : 0<κ := by dsimp [κ]; positivity
  refine ⟨κ,D+1,hκ,by linarith,?_⟩
  intro M b τ hm hb ht ht'
  let m := (M:ℝ)
  have hm1 : 1≤m := by dsimp [m]; exact_mod_cast hm
  have hm0 : 0<m := by linarith
  let R := m^δ
  let V := m^κ
  let H := ⌈R⌉₊
  have hR : 1≤R := Real.one_le_rpow hm1 hδ.le
  have hV : 1≤V := Real.one_le_rpow hm1 hκ.le
  have hHR : R≤(H:ℝ) := Nat.le_ceil _
  have hHM : H≤M := Nat.ceil_le.mpr (by
    calc R ≤ m^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 hδ₁
         _ = _ := Real.rpow_one _)
  have hH : 1≤H := by exact_mod_cast hR.trans hHR
  have hHR' : (H:ℝ) ≤ 2*R := by
    have := Nat.ceil_lt_add_one (show 0≤R by linarith)
    change (H:ℝ)<R+1 at this
    linarith
  have hVR : V^(2^k) = R := by
    dsimp [V,R,κ]
    rw [← Real.rpow_natCast,← Real.rpow_mul hm0.le]
    norm_cast
    congr 1
    push_cast
    field_simp
  have hRH : (H:ℝ)^(k+2) ≤ (2:ℝ)^(k+2)*√m := by
    calc (H:ℝ)^(k+2) ≤ (2*R)^(k+2) := pow_le_pow_left₀ (by positivity) hHR' _
         _ = (2:ℝ)^(k+2)*√m := by
           rw [mul_pow]
           congr 1
           dsimp [R,δ]
           rw [← Real.rpow_natCast,← Real.rpow_mul hm0.le,Real.sqrt_eq_rpow]
           congr 1
           push_cast
           field_simp <;> ring
  have hh := tree (logPhase τ 0) M H V hH hHM hV (hVR ▸ hHR)
    (leaf hm hH hHM hRH ht ht') b hb
  apply hh.trans
  have he : m/V = m^(1-κ) := by rw [Real.rpow_sub hm0,Real.rpow_one]
  change D*m/V ≤ (D+1)*m^(1-κ)
  rw [mul_div_assoc,he]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hm0.le _)

private theorem log_height (J : ℕ) :
    ∃ κ C : ℝ, 0<κ ∧ 0<C ∧ ∀ {M b : ℕ} {τ : ℝ}, 1≤M → b≤2*M →
      √(M:ℝ) ≤ |τ| → |τ| ≤ (M:ℝ)^J*√(M:ℝ) →
      ‖∑ n ∈ Ioc M b,e (logPhase τ 0 n)‖ ≤ C*(M:ℝ)^(1-κ) := by
  induction J with
  | zero =>
    obtain ⟨κ,C,hκ,hC,H⟩ := log_window 0
    refine ⟨κ,C,hκ,hC,?_⟩
    intro M b τ hm hb ht ht'
    have hm' : (1:ℝ)≤M := by exact_mod_cast hm
    apply H hm hb (by simpa using ht)
    apply ht'.trans
    gcongr <;> simp [hm']
  | succ J ih =>
    obtain ⟨κ,C,hκ,hC,old⟩ := ih
    obtain ⟨η,D,hη,hD,new⟩ := log_window J
    refine ⟨min κ η,max C D,lt_min hκ hη,hC.trans_le (le_max_left ..),?_⟩
    intro M b τ hm hb ht ht'
    have hm' : (1:ℝ)≤M := by exact_mod_cast hm
    by_cases h : |τ| ≤ (M:ℝ)^J*√(M:ℝ)
    · apply (old hm hb ht h).trans
      exact mul_le_mul (le_max_left ..) (Real.rpow_le_rpow_of_exponent_le hm'
        (sub_le_sub_left (min_le_left ..) _)) (by positivity) (hC.trans_le (le_max_left ..)).le
    · apply (new hm hb (not_le.mp h).le ht').trans
      exact mul_le_mul (le_max_right ..) (Real.rpow_le_rpow_of_exponent_le hm'
        (sub_le_sub_left (min_le_right ..) _)) (by positivity) (hD.trans_le (le_max_right ..)).le

/-- At any fixed polynomial height the logarithmic sums have power cancellation,
uniformly over all incomplete dyadic blocks. -/
theorem logarithmic_block_power_saving (J : ℕ) (_hJ : 1≤J) :
    ∃ κ C : ℝ, 0<κ ∧ 0<C ∧ ∀ {M b : ℕ} {τ : ℝ}, 1≤M → b≤2*M →
      |τ| ≤ (M:ℝ)^J → (M:ℝ) ≤ |τ|^2 →
      ‖∑ n ∈ Ioc M b,e (logPhase τ 0 n)‖ ≤ C*(M:ℝ)^(1-κ) := by
  obtain ⟨κ,C,hκ,hC,H⟩ := log_height J
  refine ⟨κ,C,hκ,hC,?_⟩
  intro M b τ hm hb ht ht'
  have hm' : (1:ℝ)≤M := by exact_mod_cast hm
  apply H hm hb ((Real.sqrt_le_iff).mpr ⟨abs_nonneg _,ht'⟩)
  exact ht.trans (le_mul_of_one_le_right (by positivity) ((Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hm')))


end AnalyticNumberTheory.ExponentialSums
