import AnalyticNumberTheory.RiemannZeta.HurwitzWavePairs

/-!
# Uniform pair estimates for the shifted critical-line polynomials

Adjacent cells can have arbitrarily small separation as the shift tends to
zero. They are estimated by the square-root height test. The lowest
frequency is kept separate to retain exactly one inverse square root of
the shift.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate Interval
namespace AnalyticNumberTheory.RiemannZeta

private theorem inv_sqrt_frequency_le {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i : Bool×ℕ) (hm : 1≤ i.2) :
    (Real.sqrt (hurwitzWaveFrequency a i))⁻¹≤2*(Real.sqrt (i.2+1:ℕ))⁻¹ := by
  have h₁ : (1:ℝ)≤ i.2 := by exact_mod_cast hm
  have h₂ := (hurwitzWaveFrequency_mem ha i).1
  have h : (↑(i.2+1):ℝ)≤4*hurwitzWaveFrequency a i := by push_cast;linarith
  have H := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at H
  rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀
    (Real.sqrt_pos.mpr (hurwitzWaveFrequency_pos ha.1 _)) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos _)))]
  linarith only [H]

private theorem low_frequency_weight {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i j : Bool×ℕ)
    (hm : i.2=0) (hne : i≠j) :
    (Real.sqrt (hurwitzWaveFrequency a i))⁻¹*(Real.sqrt (hurwitzWaveFrequency a j))⁻¹≤(Real.sqrt a)⁻¹ := by
  rcases eq_or_ne j.2 0 with hj|hj
  · obtain ⟨b,m⟩ := i;obtain ⟨c,n⟩ := j
    change m=0 at hm;change n=0 at hj;subst m;subst n
    cases b <;>cases c <;>simp_all [hurwitzWaveFrequency]
  · have hj' : (1:ℝ)≤j.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have hs : 1≤hurwitzWaveFrequency a j := hj'.trans (hurwitzWaveFrequency_mem ha j).1.le
    have hr : a≤hurwitzWaveFrequency a i := by
      obtain ⟨b,m⟩ := i;cases b <;>simp [hurwitzWaveFrequency] <;>linarith [Nat.cast_nonneg (α:=ℝ) m,ha.2]
    apply (mul_le_mul (inv_anti₀ (Real.sqrt_pos.mpr ha.1) (Real.sqrt_le_sqrt hr))
      (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hs)) (by positivity) (by positivity)).trans_eq
    ring

private theorem separated_frequency_logs {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i j : Bool×ℕ) (hm : i.2+2≤j.2) :
    |Real.log (j.2+1:ℕ)-Real.log (i.2+1:ℕ)|/2≤
      |Real.log (hurwitzWaveFrequency a j)-Real.log (hurwitzWaveFrequency a i)| := by
  let k : ℝ := i.2+1
  let l : ℝ := j.2+1
  let r := hurwitzWaveFrequency a i
  let s := hurwitzWaveFrequency a j
  have hk : 0<k := by dsimp [k];positivity
  have hl : 0<l := by dsimp [l];positivity
  have hkl : k+2≤l := by dsimp [k,l];exact_mod_cast Nat.succ_le_succ hm
  have hr : r≤k := (hurwitzWaveFrequency_mem ha i).2
  have hs : l-1≤s := by dsimp [l];linarith only [(hurwitzWaveFrequency_mem ha j).1]
  have hprod : k*l≤s^2 := by
    have hl' : 0≤l-1 := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right (show k≤l-2 by linarith) hl.le,
      pow_le_pow_left₀ hl' hs 2]
  have H := Real.log_le_log (mul_pos hk hl) hprod
  rw [Real.log_mul hk.ne' hl.ne',Real.log_pow] at H
  change |Real.log (j.2+1:ℕ)-Real.log (i.2+1:ℕ)|/2≤|Real.log s-Real.log r|
  simp only [Nat.cast_add,Nat.cast_one]
  change |Real.log l-Real.log k|/2≤_
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hk (by linarith)))]
  apply le_trans _ (le_abs_self _)
  norm_num at H
  have hr' : Real.log r≤Real.log k := Real.log_le_log (hurwitzWaveFrequency_pos ha.1 i) hr
  linarith only [H,hr']

/-- An ordered majorant with two neighboring diagonals, a separate bottom
row, and the integer logarithmic spacing kernel. -/
def hurwitzWavePairCost (a T : ℝ) (m n : ℕ) : ℝ :=
  (if m=0 then (if n=0 then 8*Real.sqrt T*(Real.sqrt a)⁻¹ else 0)+
    (if n=1 then 8*Real.sqrt T*(Real.sqrt a)⁻¹ else 0)+(4/Real.log 2)*(Real.sqrt a)⁻¹ else 0)+
  (if m=n then 32*Real.sqrt T*((m+1:ℕ):ℝ)⁻¹ else 0)+
  (if m+1=n then 32*Real.sqrt T*((m+1:ℕ):ℝ)⁻¹ else 0)+
  16*criticalCosineGap (m+1) (n+1)

theorem hurwitzWavePairCost_nonneg (a T : ℝ) (m n : ℕ) : 0≤hurwitzWavePairCost a T m n := by
  unfold hurwitzWavePairCost criticalCosineGap;split_ifs <;>positivity

theorem hurwitz_wave_pair_ordered {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i j : Bool×ℕ)
    (hmn : i.2≤j.2) (hne : i≠j) {u v : ℝ} (hu : 0<u) (huv : u≤v)
    (hiu : hurwitzWaveEntry a i≤u) (hju : hurwitzWaveEntry a j≤u) :
    ‖∫t in u..v,hurwitzWave a i t*conj (hurwitzWave a j t)‖≤hurwitzWavePairCost a v i.2 j.2 := by
  let r := hurwitzWaveFrequency a i
  let s := hurwitzWaveFrequency a j
  let w := (Real.sqrt r)⁻¹*(Real.sqrt s)⁻¹
  let k := i.2+1
  let l := j.2+1
  let g := |Real.log l-Real.log k|
  have hgn : 0≤criticalCosineGap k l := by unfold criticalCosineGap;split_ifs <;>positivity
  have hP := hurwitz_wave_pair_sqrt_bound ha i j hne hu huv hiu hju
  change _≤w*(8*Real.sqrt v) at hP
  by_cases hm : i.2=0
  · have hw : w≤(Real.sqrt a)⁻¹ := low_frequency_weight ha i j hm hne
    by_cases hn : j.2≤1
    · have H := hP.trans (mul_le_mul_of_nonneg_right hw (by positivity))
      unfold hurwitzWavePairCost
      rcases (by omega : j.2=0 ∨ j.2=1) with ht|ht <;>simp only [hm,ht,ite_true,
        Nat.zero_add,ite_false,zero_add,add_zero,Nat.zero_ne_one,Nat.one_ne_zero] <;>
        dsimp only [k,l] at hgn <;>rw [hm,ht] at hgn <;>
        linarith [show 0≤4/Real.log 2*(Real.sqrt a)⁻¹ by positivity,
          show 0≤32*Real.sqrt v*(((0+1:ℕ):ℝ))⁻¹ by positivity]
    · have hne' : i.2≠j.2 := by omega
      have hG := hurwitz_wave_pair_log_bound ha i j hne' hu huv hiu hju
      have hr : r≤1 := by have H := (hurwitzWaveFrequency_mem ha i).2;simpa [hm,r] using H
      have hs : 2≤s := (show (2:ℝ)≤j.2 by exact_mod_cast (by omega : 2≤j.2)).trans (hurwitzWaveFrequency_mem ha j).1.le
      have hgap : Real.log 2≤|Real.log s-Real.log r| := by
        apply le_trans _ (le_abs_self _)
        linarith only [Real.log_le_log (by norm_num : (0:ℝ)<2) hs,Real.log_nonpos (hurwitzWaveFrequency_pos ha.1 i).le hr]
      have H := hG.trans (mul_le_mul hw (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4)
        (Real.log_pos (by norm_num : (1:ℝ)<2)) hgap) (by positivity) (by positivity))
      unfold hurwitzWavePairCost
      simp only [if_pos hm,if_neg (by omega : j.2≠0),if_neg (by omega : j.2≠1),
        if_neg hne',if_neg (by omega : i.2+1≠j.2),zero_add,add_zero]
      linarith only [H,hgn]
  · have hm' := Nat.one_le_iff_ne_zero.mpr hm
    have hn' := hm'.trans hmn
    have hw := mul_le_mul (inv_sqrt_frequency_le ha i hm') (inv_sqrt_frequency_le ha j hn') (by positivity) (by positivity)
    change w≤(2*(Real.sqrt k)⁻¹)*(2*(Real.sqrt l)⁻¹) at hw
    by_cases hnear : j.2≤ i.2+1
    · have hkl : Real.sqrt k≤Real.sqrt l := Real.sqrt_le_sqrt (by exact_mod_cast Nat.succ_le_succ hmn)
      have hk : 0<Real.sqrt k := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos _))
      have hw' : w≤4*(k:ℝ)⁻¹ := by
        apply hw.trans
        have H := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (inv_anti₀ hk hkl)
          (show (0:ℝ)≤2 by norm_num)) (show 0≤2*(Real.sqrt k)⁻¹ by positivity)
        apply H.trans_eq
        rw [show (2*(Real.sqrt k)⁻¹)*(2*(Real.sqrt k)⁻¹)=4*((Real.sqrt k)^2)⁻¹ by ring,
          Real.sq_sqrt (Nat.cast_nonneg _)]
      have H := hP.trans (mul_le_mul_of_nonneg_right hw' (by positivity))
      unfold hurwitzWavePairCost
      rcases (by omega : i.2=j.2 ∨ i.2+1=j.2) with e|e <;>
        simp only [if_neg hm,zero_add,if_pos e,add_zero] <;>
        dsimp only [k,l] at H hgn <;>split_ifs <;>first | omega | linarith only [H,hgn]
    · have hfar : i.2+2≤j.2 := by omega
      have he : i.2≠j.2 := by omega
      have hlog := hurwitz_wave_pair_log_bound ha i j he hu huv hiu hju
      have hgap : g/2≤|Real.log s-Real.log r| := separated_frequency_logs ha i j hfar
      have hg : 0<g := by
        apply abs_pos.mpr;apply sub_ne_zero.mpr
        exact ne_of_gt (Real.log_lt_log (Nat.cast_pos.mpr (Nat.succ_pos _)) (Nat.cast_lt.mpr (Nat.succ_lt_succ (by omega : i.2<j.2))))
      have H := hlog.trans (mul_le_mul hw (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4)
        (by positivity : 0<g/2) hgap) (by positivity) (by positivity))
      have hkl : k≠l := by dsimp [k,l];omega
      unfold hurwitzWavePairCost
      simp only [if_neg hm,if_neg he,if_neg (by omega : i.2+1≠j.2),zero_add]
      change _≤16*criticalCosineGap k l
      rw [criticalCosineGap,if_neg hkl,Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_neg (Nat.cast_nonneg _),
        ←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
      apply H.trans_eq;dsimp only [g];ring

end AnalyticNumberTheory.RiemannZeta
