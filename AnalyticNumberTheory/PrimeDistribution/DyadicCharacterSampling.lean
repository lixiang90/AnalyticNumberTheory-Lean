import AnalyticNumberTheory.AnalyticTools.StripSampling
import AnalyticNumberTheory.PrimeDistribution.InghamTypeI

/-!
# Sampling a dyadic character polynomial without logarithmic losses

Centering the frequencies at log M bounds each differentiated coefficient
on M ≤ n ≤ 2M. The same argument works for primitive families and for all
characters of a single modulus, using their respective hybrid mean squares.
-/
noncomputable section
open Real Complex Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

/-- A one-sided hybrid mean square with conductor-height term H. -/
def CharacterHybridMean {ι : Type*} (F : Finset ι) (χ : ι→ℕ→ℂ) (L : ℕ) (H : ℝ) : Prop :=
  ∀ (N : ℕ), 1≤N → ∀ a : ℕ→ℂ,
  (∑p∈F,∫t in (0:ℝ)..L,‖∑n∈Icc 1 N,a n*χ p n*(n:ℂ)^(-(I*(t:ℂ)))‖^2)≤
    π^3*((N:ℝ)+H)*(∑n∈Icc 1 N,‖a n‖^2)

private def freq (M n : ℕ) : ℝ := Real.log M-Real.log n

private def centered (a : ℕ→ℂ) (M N : ℕ) (σ : ℝ) (k : ℕ) (s : ℂ) :=
  ∑n∈Icc 1 N,a n*((freq M n:ℝ):ℂ)^k*cexp ((freq M n:ℂ)*s-((σ*Real.log M:ℝ):ℂ))

private theorem centered_deriv {g : ℝ→ℂ} {x : ℝ} {z : ℂ} (hg : HasDerivAt g z x)
    (a : ℕ→ℂ) (M N : ℕ) (σ : ℝ) (k : ℕ) :
    HasDerivAt (fun t => centered a M N σ k (g t)) (z*centered a M N σ (k+1) (g x)) x := by
  unfold centered
  rw [mul_sum]
  apply HasDerivAt.fun_sum
  intro n hn
  have h := (((hg.const_mul (freq M n:ℂ)).sub_const ((σ*Real.log M:ℝ):ℂ)).cexp).const_mul
    (a n*(freq M n:ℂ)^k)
  convert h using 1 <;> (try dsimp) <;> ring

private theorem cpow_phase (n : ℕ) (hn : 1≤n) (s : ℂ) :
    (n:ℂ)^(-s)=cexp (-s*(Real.log n:ℂ)) := by
  have h : (n:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero h,←Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 1;push_cast;ring

private theorem centered_zero (a : ℕ→ℂ) (M N : ℕ) (σ : ℝ) (s : ℂ) :
    centered a M N σ 0 s = cexp ((Real.log M:ℂ)*(s-σ))*dirichletPoly a N s := by
  simp only [centered,pow_zero,mul_one,dirichletPoly,mul_sum]
  apply sum_congr rfl;intro n hn
  rw [cpow_phase n (mem_Icc.mp hn).1]
  have he : (freq M n:ℂ)*s-((σ*Real.log M:ℝ):ℂ)=
      (Real.log M:ℂ)*(s-σ)+ -s*(Real.log n:ℂ) := by dsimp [freq];push_cast;ring
  rw [he,Complex.exp_add];ring

private def centeredCoeff (a : ℕ→ℂ) (M : ℕ) (σ u : ℝ) (k n : ℕ) : ℂ :=
  a n*(freq M n:ℂ)^k * cexp (((freq M n*u-σ*Real.log M:ℝ):ℂ))

private theorem centered_line (a χ : ℕ→ℂ) (M N : ℕ) (σ u t : ℝ) (k : ℕ) :
    centered (fun n => a n*χ n) M N σ k ((u:ℂ)+(t:ℂ)*I)=
      cexp (I*(t:ℂ)*(Real.log M:ℂ))*
        ∑n∈Icc 1 N,centeredCoeff a M σ u k n*χ n*(n:ℂ)^(-(I*(t:ℂ))) := by
  rw [centered,mul_sum]
  apply sum_congr rfl;intro n hn
  rw [cpow_phase n (mem_Icc.mp hn).1]
  have he : (freq M n:ℂ)*((u:ℂ)+(t:ℂ)*I)-((σ*Real.log M:ℝ):ℂ)=
      I*(t:ℂ)*(Real.log M:ℂ)+((freq M n*u-σ*Real.log M:ℝ):ℂ)+(-(I*(t:ℂ))*(Real.log n:ℂ)) := by
    dsimp [freq];push_cast;ring
  rw [he,Complex.exp_add,Complex.exp_add,centeredCoeff];ring

private theorem norm_centeredCoeff {a : ℕ→ℂ} {M : ℕ} (hM : 1≤M) {σ u : ℝ} (hu : 0≤u)
    (ha : ∀n,a n≠0 → M≤n ∧ n≤2*M) (k n : ℕ) :
    ‖centeredCoeff a M σ u k n‖ ≤ ‖a n‖*(M:ℝ)^(-σ) := by
  by_cases hn : a n=0
  · simp [centeredCoeff,hn]
  obtain ⟨hmn,hnm⟩ := ha n hn
  have h0 : 0<(M:ℝ) := by exact_mod_cast hM
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hM.trans hmn
  have hneg : freq M n≤0 := by dsimp [freq];linarith [Real.log_le_log h0 (by exact_mod_cast hmn : (M:ℝ)≤n)]
  have hlow : -1≤freq M n := by
    have hlog := Real.log_le_log hn0 (by exact_mod_cast hnm : (n:ℝ)≤2*M)
    rw [Real.log_mul (by norm_num) h0.ne'] at hlog
    dsimp only [freq];linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hfreq : ‖(freq M n:ℂ)‖≤1 := by rw [Complex.norm_real,Real.norm_eq_abs];exact abs_le.mpr ⟨hlow,by linarith⟩
  have hpow : ‖(freq M n:ℂ)‖^k≤1 := pow_le_one₀ (norm_nonneg _) hfreq
  rw [centeredCoeff,norm_mul,norm_mul,norm_pow,Complex.norm_exp,Complex.ofReal_re,Real.rpow_def_of_pos h0]
  calc _ ≤ (‖a n‖*1)*Real.exp (Real.log M * -σ) := by
             gcongr
             nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg hu]
       _ = _ := by ring

/-- Square sum of one dyadic block, with no logarithmic loss from sampling.
The tests may have different real parts and may cluster K-fold in height. -/
theorem dyadic_character_sampling {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ} {L M : ℕ} {H K σ : ℝ}
    (hmean : CharacterHybridMean F χ L H) (hH : 0≤H) (hM : 1≤M) (hK : 0≤K) (hσ : 0≤σ)
    (S : ι→Finset ℂ) (hre : ∀p∈F,∀z∈S p,z.re∈Set.Icc σ (σ+1))
    (him : ∀p∈F,∀z∈S p,0≤z.im ∧ z.im<L)
    (hcount : ∀p∈F,∀j<L,(((S p).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K)
    (a : ℕ→ℂ) (ha : ∀n,a n≠0 → M≤n ∧ n≤2*M) :
    (∑p∈F,∑z∈S p,‖dirichletPoly (fun n => a n*χ p n) (2*M) z‖^2) ≤
      9*K*(π^3*(2*(M:ℝ)+H)*((∑n∈Icc 1 (2*M),‖a n‖^2)*(M:ℝ)^(-2*σ))) := by
  let P (p:ι) (k:ℕ) (u t:ℝ) := centered (fun n => a n*χ p n) M (2*M) σ k ((u:ℂ)+(t:ℂ)*I)
  have hR (p:ι) (k:ℕ) (u t:ℝ) : HasDerivAt (fun v => P p k v t) (P p (k+1) u t) u := by
    simpa [P] using centered_deriv ((Complex.ofRealCLM.hasDerivAt (x:=u)).add_const ((t:ℂ)*I))
      (fun n => a n*χ p n) M (2*M) σ k
  have hT (p:ι) (k:ℕ) (u t:ℝ) : HasDerivAt (P p k u) (I*P p (k+1) u t) t := by
    simpa [P] using centered_deriv (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const I).const_add (u:ℂ))
      (fun n => a n*χ p n) M (2*M) σ k
  apply le_trans _ (strip_family_sampling F S P hK hre him hcount
    (fun p k t => continuous_iff_continuousAt.mpr fun u => (hR p k u t).continuousAt)
    (fun p k u => continuous_iff_continuousAt.mpr fun t => (hT p k u t).continuousAt)
    (fun p => hR p 0) hT ?_)
  · apply sum_le_sum;intro p hp;apply sum_le_sum;intro z hz
    dsimp only [P];rw [Complex.re_add_im,centered_zero,norm_mul]
    have hpos : 0≤Real.log M*(z.re-σ) := mul_nonneg
      (Real.log_nonneg (by exact_mod_cast hM)) (sub_nonneg.mpr (hre p hp z hz).1)
    have hn : 1≤‖cexp ((Real.log M:ℂ)*(z-σ))‖ := by
      rw [Complex.norm_exp];apply Real.one_le_exp_iff.mpr
      simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re,zero_mul,sub_zero] using hpos
    gcongr
    exact le_mul_of_one_le_left (norm_nonneg _) hn
  · intro u hu k _
    let b := centeredCoeff a M σ u k
    have he (p : ι) (t : ℝ) : ‖P p k u t‖=‖∑n∈Icc 1 (2*M),b n*χ p n*(n:ℂ)^(-(I*(t:ℂ)))‖ := by
      dsimp only [P];rw [centered_line,norm_mul,Complex.norm_exp];
      simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,sub_zero,Real.exp_zero,one_mul,b]
    simp_rw [he]
    have HH := hmean (2*M) (by omega) b
    push_cast at HH
    apply HH.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [sum_mul];apply sum_le_sum;intro n _
    have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_centeredCoeff (σ:=σ) hM (hσ.trans hu.1) ha k n) 2
    rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _), show -σ*(2:ℕ)= -2*σ by push_cast;ring] at hb
    exact hb

end AnalyticNumberTheory.PrimeDistribution
