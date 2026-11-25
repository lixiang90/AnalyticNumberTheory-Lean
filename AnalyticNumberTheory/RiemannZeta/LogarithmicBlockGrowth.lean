import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import AnalyticNumberTheory.ExponentialSums.LogarithmicPhases
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Growth of zeta near one from logarithmic exponential sums

Dyadic blocks below the oscillatory range cost at most T^(η/J).
On the remaining blocks partial summation transfers cancellation to
the vertical Dirichlet polynomial, with a bounded cost when η≤κ.
-/
noncomputable section
open Finset Real Complex Filter
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.ExponentialSums
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- Power savings on logarithmic phases on each fixed polynomial range
of frequencies. -/
def LogarithmicBlockCancellation : Prop :=
  ∀ J : ℕ, 1≤J → ∃ κ C : ℝ, 0<κ ∧ 0<C ∧ ∀ {M b : ℕ} {τ : ℝ},
    1≤M → b≤2*M → |τ|≤(M:ℝ)^J → (M:ℝ)≤|τ|^2 →
    ‖∑ n∈Ioc M b,e (logPhase τ 0 n)‖ ≤ C*(M:ℝ)^(1-κ)

/-- The vertical phase of a Dirichlet monomial in additive-character notation. -/
theorem vertical_log_term {n : ℕ} (hn : 1≤n) (σ t : ℝ) :
    (n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)) = (((max (n:ℝ) 1)^(-σ):ℝ):ℂ)*e (logPhase (-t/(2*π)) 0 n) := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have hn' := zero_lt_one.trans_le hnr
  rw [max_eq_left hnr,Real.rpow_def_of_pos hn',Complex.ofReal_exp,←Complex.ofReal_natCast,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn'.ne'),←Complex.ofReal_log hn'.le,e,←Complex.exp_add]
  unfold logPhase; push_cast; simp only [add_zero]; congr 1
  have hlog : Complex.log (n:ℂ) = (Real.log (n:ℝ):ℂ) := by rw [←Complex.ofReal_natCast,Complex.ofReal_log hn'.le]
  field_simp [Real.pi_ne_zero]; simp only [hlog]; ring

private theorem strip_block_bound {J M b : ℕ} {T t κ C η σ : ℝ}
    (hJ : 1≤J) (hT : 256≤T) (ht₁ : T≤|t|) (ht₂ : |t|≤3*T)
    (hη : 0<η) (hηκ : η≤κ) (hσ : 0≤σ) (hση : 1-η≤σ) (hC : 0<C)
    (hM : 1≤M) (hb : b≤2*M) (hcut : (M:ℝ)≤4*T)
    (H : ∀ {M b : ℕ} {τ : ℝ}, 1≤M → b≤2*M → |τ|≤(M:ℝ)^J → (M:ℝ)≤|τ|^2 →
      ‖∑ n∈Ioc M b,e (logPhase τ 0 n)‖ ≤ C*(M:ℝ)^(1-κ)) :
    ‖∑ n∈Ioc M b,(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ (1+C)*T^(η/J) := by
  let τ := -t/(2*π)
  have ht : 0<T := by linarith
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hm' := zero_lt_one.trans_le hm
  have hJ' : 0<(J:ℝ) := by exact_mod_cast hJ
  have hτ : |τ|=|t|/(2*π) := by rw [abs_div,abs_neg,abs_of_pos (by positivity : 0<2*π)]
  have hτT : |τ|≤T := by rw [hτ,div_le_iff₀ (by positivity)]; nlinarith only [ht₂,mul_le_mul_of_nonneg_left Real.two_le_pi ht.le,ht]
  have hτsq : (M:ℝ)≤|τ|^2 := by
    have ht8 : T/8 ≤ |τ| := by rw [hτ,le_div_iff₀ (by positivity)]; nlinarith only [ht₁,mul_le_mul_of_nonneg_left Real.pi_le_four ht.le]
    nlinarith only [hcut,sq_nonneg (T-256),mul_nonneg ht.le (show 0≤T-256 by linarith),sq_le_sq₀ (by positivity : 0≤T/8) (abs_nonneg τ) |>.mpr ht8]
  have hTpow := Real.one_le_rpow (show 1≤T by linarith) (div_nonneg hη.le hJ'.le)
  by_cases hmb : M≤b
  · let w (n : ℕ) : ℝ := (max (n:ℝ) 1)^(-σ)
    let z (n : ℕ) : ℂ := e (logPhase τ 0 n)
    have hw0 (n : ℕ) : 0≤w n := Real.rpow_nonneg ((zero_le_one.trans (le_max_right ..))) _
    have hw : Antitone w := fun n m hnm => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (le_max_right ..))
      (max_le_max_right _ (by exact_mod_cast hnm)) (neg_nonpos.mpr hσ)
    have heq : (∑ n∈Ioc M b,(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))=∑ n∈Ioc M b,(w n:ℂ)*z n :=
      sum_congr rfl (fun n hn => vertical_log_term (hM.trans (mem_Ioc.mp hn).1.le) σ t)
    have hwM : w M=(M:ℝ)^(-σ) := by dsimp [w]; rw [max_eq_left hm]
    rw [heq]
    by_cases hlarge : |τ|≤(M:ℝ)^J
    · have hs (k : ℕ) (_ : M≤k) (hk : k≤b) : ‖∑ n∈Ioc M k,z n‖≤C*(M:ℝ)^(1-κ) := H hM (hk.trans hb) hlarge hτsq
      apply (norm_sum_Ioc_antitone_weight w z hw hw0 hmb (by positivity) hs).trans
      rw [hwM,mul_left_comm,←Real.rpow_add hm']
      have hle := Real.rpow_le_one_of_one_le_of_nonpos hm (show -σ+(1-κ)≤0 by linarith)
      nlinarith only [mul_le_mul_of_nonneg_left hle hC.le,mul_le_mul_of_nonneg_left hTpow (show 0≤1+C by linarith),hC]
    · have hs (k : ℕ) (_ : M≤k) (hk : k≤b) : ‖∑ n∈Ioc M k,z n‖≤(M:ℝ) := by
        apply (norm_sum_le ..).trans
        simp only [z,norm_e,sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc]
        exact_mod_cast (by omega : k-M≤M)
      apply (norm_sum_Ioc_antitone_weight w z hw hw0 hmb hm'.le hs).trans
      rw [hwM,show (M:ℝ)^(-σ)*(M:ℝ)=(M:ℝ)^(1-σ) by rw [sub_eq_add_neg,Real.rpow_add hm',Real.rpow_one,mul_comm]]
      have hMJ := (le_of_not_ge hlarge).trans hτT
      have hp := Real.rpow_le_rpow (pow_nonneg hm'.le J) hMJ (div_nonneg hη.le hJ'.le)
      rw [←Real.rpow_natCast (M:ℝ) J,←Real.rpow_mul hm'.le,show (J:ℝ)*(η/J)=η by field_simp] at hp
      exact ((Real.rpow_le_rpow_of_exponent_le hm (by linarith : 1-σ≤η)).trans hp).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg ht.le _) (by linarith))
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hmb),sum_empty,norm_zero]; positivity

/-- For fixed J and a strip no wider than the saving in the order-J block
estimate, zeta is bounded by a power T^(η/J) times a single logarithm. -/
theorem zeta_strip_bound_from_blocks (J : ℕ) (hJ : 1≤J) {κ C η : ℝ}
    (hη : 0<η) (hηκ : η≤κ) (hη' : η≤1/4) (hC : 0<C)
    (H : ∀ {M b : ℕ} {τ : ℝ}, 1≤M → b≤2*M → |τ|≤(M:ℝ)^J → (M:ℝ)≤|τ|^2 →
      ‖∑ n∈Ioc M b,e (logPhase τ 0 n)‖ ≤ C*(M:ℝ)^(1-κ)) :
    ∃ D : ℝ, 0<D ∧ ∀ {T : ℝ}, 256≤T → ∀ z : ℂ, 1-η≤z.re →
      T≤|z.im| → |z.im|≤3*T → ‖riemannZeta z‖ ≤ D*(1+Real.log T)*T^(η/J) := by
  obtain ⟨K,hK,hap⟩ := riemannZeta_approx_dirichletPoly_sub_bound (c:=1) zero_lt_one
    (by linarith [Real.two_le_pi])
  let L := 4+(Real.log 2)⁻¹
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨K+4+L*(1+C),by positivity,fun {T} hT z hz ht₁ ht₂ => ?_⟩
  let N := ⌈|z.im|⌉₊
  have hN : 1≤N := Nat.one_le_ceil_iff.mpr (by linarith : 0 < |z.im|)
  have hN' : (1:ℝ)≤N := by exact_mod_cast hN
  have hnL : |z.im|≤(N:ℝ) := Nat.le_ceil _
  have hnU : (N:ℝ)≤|z.im|+1 := (Nat.ceil_lt_add_one (abs_nonneg z.im)).le
  have hcut : (N:ℝ)≤4*T := by linarith
  have hl := Real.log_nonneg (show 1≤T by linarith)
  have hσ : 0<z.re := by linarith
  have hJ' : 0<(J:ℝ) := by exact_mod_cast hJ
  have hTpow := Real.one_le_rpow (show 1≤T by linarith) (div_nonneg hη.le hJ'.le)
  have herr := hap (N:=N) (σ:=z.re) (t:=z.im) hN hσ (by linarith) (by simpa using hnL)
  rw [Complex.re_add_im] at herr
  have hfrac : (N:ℝ)^(1-z.re)/|z.im|≤2 := by
    rw [div_le_iff₀ (by linarith)]
    have h := Real.rpow_le_rpow_of_exponent_le hN' (show 1-z.re≤1 by linarith)
    rw [Real.rpow_one] at h; linarith
  have htail := Real.rpow_le_one_of_one_le_of_nonpos hN' (neg_nonpos.mpr hσ.le)
  let k := N.log2+1
  have hcutoff : N≤2^k := Nat.lt_log2_self.le
  have hk : (k:ℝ)≤L*(1+Real.log T) := by
    have hp : (2:ℝ)^N.log2≤N := by exact_mod_cast Nat.log2_self_le (n:=N) (by omega)
    have hv := Real.log_le_log (by positivity) (hp.trans hcut)
    rw [Real.log_pow,show (4:ℝ)=2^2 by norm_num,Real.log_mul (by norm_num) (by linarith),Real.log_pow] at hv
    have hquot := (le_div_iff₀ hlog2).mpr hv
    dsimp [k,L]; push_cast; rw [add_div] at hquot; field_simp at hquot ⊢; norm_num at hquot; nlinarith [mul_nonneg hlog2.le hl]
  let B := (1+C)*T^(η/J)
  let f (n : ℕ) := (n:ℂ)^(-z)
  have hpoly : ‖dirichletPoly (fun _ => 1) N z‖≤1+k*B := by
    change ‖∑ n∈Icc 1 N,(1:ℂ)*f n‖≤_; simp only [one_mul]
    rw [sum_Icc_eq_dyadic_blocks f hN hcutoff]
    refine (norm_add_le ..).trans (add_le_add (by simp [f]) ((norm_sum_le ..).trans ?_))
    calc _ ≤ ∑ _j∈range k,B := by
              apply sum_le_sum; intro j _
              by_cases hj : 2^j≤N
              · dsimp only [f,dyadicBlock]
                rw [←Complex.re_add_im z]
                simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero,
                  Complex.add_im,Complex.mul_I_im,zero_add] using strip_block_bound hJ hT ht₁ ht₂ hη hηκ hσ.le hz hC
                    (Nat.one_le_two_pow (n:=j)) (b:=min N (2^(j+1))) ((min_le_right ..).trans (by rw [pow_succ]; omega))
                    ((show (((2:ℕ)^j:ℕ):ℝ)≤N by exact_mod_cast hj).trans hcut) @H
              · simp only [dyadicBlock,Ioc_eq_empty_of_le ((min_le_left ..).trans (le_of_not_ge hj)),sum_empty,norm_zero]
                dsimp [B]; positivity
         _ = _ := by simp
  have htri := norm_add_le (riemannZeta z-dirichletPoly (fun _ => 1) N z) (dirichletPoly (fun _ => 1) N z)
  rw [sub_add_cancel] at htri
  have hkb := mul_le_mul_of_nonneg_right hk (show 0≤B by dsimp [B]; positivity)
  have hone : 1≤(1+Real.log T)*T^(η/J) := one_le_mul_of_one_le_of_one_le (by linarith) hTpow
  dsimp only [B] at hkb hpoly
  nlinarith only [htri,herr,hpoly,hfrac,mul_le_mul_of_nonneg_left htail hK.le,hkb,
    mul_le_mul_of_nonneg_left hone (show 0≤K+4 by linarith),hone]

end AnalyticNumberTheory.RiemannZeta
