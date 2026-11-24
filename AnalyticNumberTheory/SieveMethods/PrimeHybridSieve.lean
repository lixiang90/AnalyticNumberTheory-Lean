import AnalyticNumberTheory.SieveMethods.PrimeCharacterSieve
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials

/-!
# The hybrid large sieve for Dirichlet polynomials supported on primes

Gallagher's box kernel restricts the coefficients to a multiplicative short
interval at each Fourier coordinate. Its length is bounded in terms of each
prime in that interval, giving a weighted mean square independent of the
upper endpoint of the polynomial.
-/

noncomputable section
open Complex Real Finset MeasureTheory Filter
open scoped Classical
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

private def logWindow (S : Finset ℕ) (T u : ℝ) : Finset ℕ := S.filter (fun n : ℕ => |u-T*Real.log (n:ℝ)|≤1/2)

private theorem logWindow_span {S : Finset ℕ} (hS : ∀ n ∈ S, 1≤n) {T : ℝ} (hT : 1≤T)
    {u : ℝ} {n m : ℕ} (hn : n∈logWindow S T u) (hm : m∈logWindow S T u) :
    (m:ℝ)-n ≤ 2*n/T := by
  obtain ⟨hn',hn''⟩ := mem_filter.mp hn
  obtain ⟨hm',hm''⟩ := mem_filter.mp hm
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hS n hn'
  have hm0 : 0<(m:ℝ) := by exact_mod_cast hS m hm'
  have hTp : 0<T := by linarith
  have h₁ : Real.log m-Real.log n ≤ 1/T := by
    rw [le_div_iff₀ hTp]
    nlinarith only [(abs_le.mp hn'').2,(abs_le.mp hm'').1]
  have h₂ : (m:ℝ)/n ≤ Real.exp (1/T) := by
    rw [← Real.log_div hm0.ne' hn0.ne'] at h₁
    simpa [Real.exp_log (div_pos hm0 hn0)] using Real.exp_le_exp.mpr h₁
  have hθ : 1/T≤1 := (div_le_one hTp).mpr hT
  have hθ0 : 0≤1/T := by positivity
  have h₃ : Real.exp (1/T) ≤ 1+2*(1/T) := by
    have hh : Real.exp ((1-1/T)*0+(1/T)*1) ≤ (1-1/T)*Real.exp 0+(1/T)*Real.exp 1 :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) hθ0 (by ring)
    simp only [mul_zero,zero_add,mul_one,Real.exp_zero] at hh
    nlinarith [mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hθ0]
  have hh := (div_le_iff₀ hn0).mp (h₂.trans h₃)
  linear_combination hh

private theorem filter_energy_pointwise {S : Finset ℕ} {Q Z : ℕ} (hQ : 1≤Q) (hZ : 1<Z)
    {T : ℝ} (hT : 1≤T) (hS : ∀ n ∈ S, n.Prime ∧ ((Q:ℝ)*Z)^2*T<n) (a : ℕ → ℂ) (u : ℝ) :
    (∑ p ∈ primitiveCharacterFamily Q, ‖∑ n ∈ logWindow S T u,a n*p.2 n‖^2) ≤
      (3/(T*Real.log Z))*∑ n ∈ logWindow S T u,(n:ℝ)*‖a n‖^2 := by
  let W := logWindow S T u
  by_cases hw : W.Nonempty
  · let l := W.min' hw
    let m := W.max' hw
    have hl : l∈W := min'_mem _ _
    have hm : m∈W := max'_mem _ _
    have hl1 : 1≤l := (hS _ (mem_filter.mp hl).1).1.pos
    let M := l-1
    let N := m-l+1
    have hlm : l≤m := min'_le _ _ hm
    have hsub : W ⊆ Ioc M (M+N) := by
      intro n hn
      have h₁ : l≤n := min'_le _ _ hn
      have h₂ : n≤m := le_max' _ _ hn
      apply mem_Ioc.mpr; dsimp [M,N]; omega
    let b := fun n => if n∈W then a n else 0
    have hM (n : ℕ) (hn : n∈W) : (N:ℝ)-1+((Q:ℝ)*Z)^2 ≤ 3*n/T := by
      have hspan := logWindow_span (fun n hn => (hS n hn).1.pos) hT hl hm
      have hn' : l≤n := min'_le _ _ hn
      have hT' : 0<T := by linarith
      have hscale := (hS n (mem_filter.mp hn).1).2
      have he : (N:ℝ)-1 = (m:ℝ)-l := by dsimp [N]; rw [Nat.cast_add,Nat.cast_sub hlm]; ring
      rw [he,le_div_iff₀ hT']
      have hh := (le_div_iff₀ hT').mp hspan
      have hnR : (l:ℝ)≤n := by exact_mod_cast hn'
      nlinarith only [hscale,hh,hnR]
    have hs := sifted_character_large_sieve b M (N:=N) (Q:=Q) (Z:=Z) (by dsimp [N]; omega) hQ hZ.le (fun n _ h r hr => by
      have hw' : n∈W := by by_contra hn; exact h (if_neg hn)
      have hh := hS n (mem_filter.mp hw').1
      have hQZ : (1:ℝ)≤(Q:ℝ)*Z := by exact_mod_cast Nat.mul_pos hQ hZ.le
      have hn : ((Q*Z:ℕ):ℝ)<n := by
        rw [Nat.cast_mul]
        nlinarith [mul_nonneg (sq_nonneg ((Q:ℝ)*Z)) (sub_nonneg.mpr hT),
          mul_nonneg (sub_nonneg.mpr hQZ) (show 0≤(Q:ℝ)*Z by positivity),hh.2]
      exact hh.1.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hr).1
        ((mem_Icc.mp hr).2.trans_lt (by exact_mod_cast hn))))
    have hchar (p : (q : ℕ) × DirichletCharacter ℂ q) :
        (∑ n ∈ Ioc M (M+N), b n*p.2 n) = ∑ n ∈ W,a n*p.2 n := by
      rw [←sum_subset hsub (fun n _ hn => by simp [b,hn])]
      exact sum_congr rfl fun n hn => by simp [b,hn]
    have hsq : (∑ n ∈ Ioc M (M+N),‖b n‖^2) = ∑ n ∈ W,‖a n‖^2 := by
      rw [←sum_subset hsub (fun n _ hn => by simp [b,hn])]
      exact sum_congr rfl fun n hn => by simp [b,hn]
    simp_rw [hchar] at hs
    rw [hsq,mul_sum (s:=W)] at hs
    have hL : 0<Real.log Z := Real.log_pos (by exact_mod_cast hZ)
    have h₁ := hs.trans (sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (hM n hn) (sq_nonneg ‖a n‖)))
    have h₂ : (∑ n ∈ W,3*n/T*‖a n‖^2) = (3/T)*∑ n ∈ W,(n:ℝ)*‖a n‖^2 := by
      rw [mul_sum]; apply sum_congr rfl; intro n _; ring
    rw [h₂] at h₁
    change _ ≤ _ * ∑ n ∈ W,_
    rw [show 3/(T*Real.log Z)=(3/T)/Real.log Z by ring,div_mul_eq_mul_div,le_div_iff₀ hL,mul_comm _ (Real.log _)]
    exact h₁
  · have hh : logWindow S T u=∅ := not_nonempty_iff_eq_empty.mp hw
    simp [hh]

private theorem window_integral (S : Finset ℕ) (T : ℝ) (b : ℕ → ℝ) :
    Integrable (fun u => ∑ n ∈ logWindow S T u,b n) ∧
      (∫ u : ℝ, ∑ n ∈ logWindow S T u,b n)=∑ n ∈ S,b n := by
  let I := fun n : ℕ => Set.Icc (T*Real.log n-1/2) (T*Real.log n+1/2)
  have hf (n : ℕ) : Integrable ( (I n).indicator (fun _ : ℝ => b n)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (hs:=measure_Icc_lt_top.ne))
  have he : (fun u => ∑ n ∈ logWindow S T u,b n) =
      fun u : ℝ => ∑ n ∈ S,(I n).indicator (fun _ => b n) u := by
    ext u
    rw [logWindow,sum_filter]
    apply sum_congr rfl; intro n hn
    rw [Set.indicator_apply]
    congr 1
    apply propext
    change |u-T*Real.log n|≤1/2 ↔ _ ≤ _ ∧ _ ≤ _
    rw [abs_le]; constructor <;> intro hh <;> constructor <;> linarith [hh.1,hh.2]
  rw [he]
  refine ⟨integrable_finsetSum S (fun n _ => hf n),?_⟩
  rw [integral_finsetSum S (fun n _ => hf n)]
  apply sum_congr rfl; intro n hn
  rw [integral_indicator measurableSet_Icc, setIntegral_const,Real.volume_real_Icc,smul_eq_mul,max_eq_left (by linarith)]
  ring

/-- Prime-supported hybrid large sieve with an explicit choice of the
amplifier cutoff Z. Both the primitive principal character of level one
and all other primitive characters enter the sum. -/
theorem prime_hybrid_large_sieve_parameter (S : Finset ℕ) (a : ℕ → ℂ)
    {Q Z : ℕ} (hQ : 1≤Q) (hZ : 1<Z) {T : ℝ} (hT : 1≤T)
    (hS : ∀ n ∈ S, n.Prime ∧ ((Q:ℝ)*Z)^2*T<n) :
    (∑ p ∈ primitiveCharacterFamily Q, ∫ t in (-T)..T,
      ‖∑ n ∈ S,a n*p.2 n*(n:ℂ)^(-(I*(t:ℂ)))‖^2) ≤
      (3*Real.pi^3/(2*Real.log Z))*∑ n ∈ S,(n:ℝ)*‖a n‖^2 := by
  let F := primitiveCharacterFamily Q
  let W := fun u => logWindow S T u
  let G := fun (p : (q : ℕ) × DirichletCharacter ℂ q) (u : ℝ) => ‖∑ n ∈ W u,a n*p.2 n‖^2
  let B := fun u => ∑ n ∈ W u,(n:ℝ)*‖a n‖^2
  let K := 3/(T*Real.log Z)
  have hpt (u : ℝ) : (∑ p ∈ F,G p u) ≤ K*B u := filter_energy_pointwise hQ hZ hT hS a u
  have hB := window_integral S T (fun n => (n:ℝ)*‖a n‖^2)
  have hK : Integrable (fun u => K*B u) := hB.1.const_mul K
  have hg (p : (q : ℕ) × DirichletCharacter ℂ q) (hp : p∈F) : Integrable (G p) := by
    have hm : Measurable (fun u : ℝ => ∑ n ∈ W u,a n*p.2 n) := by
      dsimp only [W,logWindow]
      simp_rw [sum_filter]
      apply Finset.measurable_fun_sum; intro n hn
      exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const measurable_const
    apply hK.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro u
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (Finset.single_le_sum (f:=fun p => G p u) (fun _ _ => sq_nonneg _) hp).trans (hpt u)
  have hTk : 0<T := by linarith
  have hsum := sum_le_sum (s:=F) (fun p _ => tent_gallagher_integral_bound S (fun n hn => (hS n hn).1.pos)
    (fun n => a n*p.2 n) hTk)
  change _ ≤ ∑ p ∈ F, (Real.pi^3/2)*T*(∫ u : ℝ,G p u) at hsum
  rw [←mul_sum,←integral_finsetSum F hg] at hsum
  have hdom := integral_mono (integrable_finsetSum F hg) hK hpt
  rw [integral_const_mul] at hdom
  change _ ≤ K*(∫ u : ℝ, ∑ n ∈ logWindow S T u,(n:ℝ)*‖a n‖^2) at hdom
  rw [hB.2] at hdom
  refine hsum.trans ((mul_le_mul_of_nonneg_left hdom (by positivity)).trans_eq ?_)
  dsimp only [K]; field_simp

/-- **Hybrid large sieve for primes.** If Y≥(Q²(T+2))⁸ and T≥1, the
family mean square on every finite set of primes above Y is at most
6π³/log Y times the weighted coefficient mass. There is no upper
restriction on the primes or on the length of the polynomial. -/
theorem prime_hybrid_large_sieve (S : Finset ℕ) (a : ℕ → ℂ) {Q : ℕ} (hQ : 1≤Q)
    {T Y : ℝ} (hT : 1≤T) (hY : ((Q:ℝ)^2*(T+2))^8≤Y)
    (hS : ∀ p ∈ S, p.Prime ∧ Y<p) :
    (∑ χ ∈ primitiveCharacterFamily Q, ∫ t in (-T)..T,
      ‖∑ p ∈ S,a p*χ.2 p*(p:ℂ)^(-(I*(t:ℂ)))‖^2) ≤
      (6*Real.pi^3/Real.log Y)*∑ p ∈ S,(p:ℝ)*‖a p‖^2 := by
  let B := (Q:ℝ)^2*(T+2)
  have hq : 1≤(Q:ℝ) := by exact_mod_cast hQ
  have hq2 : 1≤(Q:ℝ)^2 := one_le_pow₀ hq
  have hB : 3≤B := by dsimp [B]; nlinarith [mul_nonneg (sub_nonneg.mpr hq2) (show 0≤T+2 by linarith)]
  have hY' : 1<Y := by
    have hh : (3:ℝ)^8≤B^8 := by gcongr
    change B^8≤Y at hY; linarith
  let x := Real.sqrt (Real.sqrt Y)
  have hx : 0<x := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hx4 : x^4=Y := by dsimp [x]; rw [show 4=2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt (by linarith)]
  have hBx : B^2≤x := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg B) hx.le (by decide : 4≠0)).mp
    rw [←pow_mul,hx4]; exact hY
  have hQT : 4*(Q:ℝ)^2*T≤x := by
    have hqB : (Q:ℝ)*(T+2)≤B := by
      dsimp [B]; nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤Q) (sub_nonneg.mpr hq)) (show 0≤T+2 by linarith)]
    have hqB2 := pow_le_pow_left₀ (by positivity) hqB 2
    nlinarith only [hBx,hqB2,mul_nonneg (sq_nonneg (Q:ℝ)) (sq_nonneg T)]
  let Z := ⌈x⌉₊
  have hxZ : x≤Z := Nat.le_ceil _
  have hx1 : 1<x := by nlinarith [hBx,hB,sq_nonneg (B-3)]
  have hZ : 1<Z := by exact_mod_cast (hx1.trans_le hxZ)
  have hZ' : (Z:ℝ)≤2*x := by have hh := Nat.ceil_lt_add_one hx.le; dsimp [Z]; linarith
  have hscale : ((Q:ℝ)*Z)^2*T ≤ Y := by
    calc
      _ ≤ ((Q:ℝ)*(2*x))^2*T := by gcongr
      _ = (4*(Q:ℝ)^2*T)*x^2 := by ring
      _ ≤ x*x^2 := mul_le_mul_of_nonneg_right hQT (sq_nonneg _)
      _ ≤ x^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx1.le) (pow_nonneg hx.le 3)]
      _ = _ := hx4
  have hlog : Real.log Y/4≤Real.log Z := by
    have hh := Real.log_le_log hx hxZ
    dsimp [x] at hh
    rw [Real.log_sqrt (Real.sqrt_nonneg _),Real.log_sqrt (by linarith)] at hh
    linarith
  have base := prime_hybrid_large_sieve_parameter S a hQ hZ hT (fun p hp => ⟨(hS p hp).1,hscale.trans_lt (hS p hp).2⟩)
  refine base.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  rw [div_le_div_iff₀ (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hZ))) (Real.log_pos hY')]
  nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : 0≤12*Real.pi^3)]

/-- Cutoff form used by prime Dirichlet-polynomial zero detectors; all
truncation endpoints u are permitted with the same constant. -/
theorem prime_hybrid_large_sieve_Ioc (a : ℕ → ℂ) {Q : ℕ} (hQ : 1≤Q)
    {T Y u : ℝ} (hT : 1≤T) (hY : ((Q:ℝ)^2*(T+2))^8≤Y) :
    let S := (Ioc ⌊Y⌋₊ ⌊u⌋₊).filter Nat.Prime
    (∑ χ ∈ primitiveCharacterFamily Q, ∫ t in (-T)..T,
      ‖∑ p ∈ S,a p*χ.2 p*(p:ℂ)^(-(I*(t:ℂ)))‖^2) ≤
      (6*Real.pi^3/Real.log Y)*∑ p ∈ S,(p:ℝ)*‖a p‖^2 := by
  intro S
  exact prime_hybrid_large_sieve S a hQ hT hY (fun p hp => ⟨(mem_filter.mp hp).2,
    (Nat.lt_floor_add_one Y).trans_le (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).1)⟩)

end AnalyticNumberTheory.SieveMethods
