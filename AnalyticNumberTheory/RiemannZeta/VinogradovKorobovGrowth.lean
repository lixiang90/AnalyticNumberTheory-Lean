import AnalyticNumberTheory.RiemannZeta.LogarithmicBlockGrowth

/-!
# Vinogradov–Korobov growth of the zeta function

Cubic logarithmic cancellation on dyadic blocks and partial summation lead
to a growth exponent proportional to the three-halves power of the strip width.
-/
noncomputable section
open Real Complex Finset Filter
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- Korobov's exponential sum estimate, with absolute constants and an arbitrary
upper endpoint in the block. -/
def VinogradovKorobovBlockCancellation : Prop :=
  ∃ c>(0:ℝ), ∃ C>(0:ℝ), ∀ (N M : ℕ) (t : ℝ), 1≤N → N≤M → M≤2*N →
    (N:ℝ)≤t → 16≤t → ‖∑ n∈Ioc (N:ℤ) (M:ℤ), e ((t/(2*π))*Real.log n)‖ ≤
      C*N*Real.exp (-c*(Real.log N)^3/(Real.log t)^2)

/-- The classical three-halves exponent, with one logarithmic prefactor. -/
def VinogradovKorobovStripGrowth : Prop :=
  ∃ K>(0:ℝ), ∃ D>(0:ℝ), ∀ (z : ℂ) (η : ℝ), 0≤η → η≤1/4 → 1-η≤z.re →
    16≤|z.im| → ‖riemannZeta z‖ ≤
      D*(1+Real.log |z.im|)*Real.exp (K*η^(3/2:ℝ)*Real.log |z.im|)

/-- Maximizing the cubic cancellation exponent produces the three-halves power of the strip width. -/
theorem vinogradov_cubic_saving {a η c L : ℝ} (ha : 0≤a) (hη : 0≤η) (hc : 0<c) (hL : 0<L) :
    η*a-c*a^3/L^2 ≤ (1/Real.sqrt c)*η^(3/2:ℝ)*L := by
  have hs : 0<Real.sqrt c := Real.sqrt_pos.mpr hc
  have heq : (1/Real.sqrt c)*η^(3/2:ℝ) = η*Real.sqrt (η/c) := by
    by_cases hz : η=0
    · subst η; norm_num
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add (lt_of_le_of_ne hη (Ne.symm hz)),
      Real.rpow_one,←Real.sqrt_eq_rpow,Real.sqrt_div hη]; ring
  rw [heq]
  by_cases h : a≤Real.sqrt (η/c)*L
  · have hh := mul_le_mul_of_nonneg_left h hη
    linarith only [hh,show 0≤c*a^3/L^2 by positivity]
  · have hs' := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hL.le) ha).mpr (le_of_not_ge h)
    rw [mul_pow,Real.sq_sqrt (div_nonneg hη hc.le)] at hs'
    have hh : η*L^2 ≤ c*a^2 := by
      apply (mul_le_mul_of_nonneg_left hs' hc.le).trans_eq'
      field_simp
    have hv : η*a≤c*a^3/L^2 := (le_div_iff₀ (sq_pos_of_pos hL)).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hh ha])
    exact (sub_nonpos.mpr hv).trans (by positivity)

private theorem nat_log_block {c C t : ℝ} {N M : ℕ} (ht : 16≤|t|)
    (hN : 1≤N) (hM : N≤M) (hM' : M≤2*N) (hNt : (N:ℝ)≤|t|)
    (H : ∀ (N M : ℕ) (u : ℝ), 1≤N → N≤M → M≤2*N → (N:ℝ)≤u → 16≤u →
      ‖∑ n∈Ioc (N:ℤ) (M:ℤ), e ((u/(2*π))*Real.log n)‖ ≤
        C*N*Real.exp (-c*(Real.log N)^3/(Real.log u)^2)) :
    ‖∑ n∈Ioc N M,e (logPhase (-t/(2*π)) 0 n)‖ ≤
      C*N*Real.exp (-c*(Real.log N)^3/(Real.log |t|)^2) := by
  have he (u : ℝ) : (∑ n∈Ioc N M,e ((u/(2*π))*Real.log n)) =
      ∑ n∈Ioc (N:ℤ) (M:ℤ),e ((u/(2*π))*Real.log n) := by
    refine sum_bij' (fun n _ => (n:ℤ)) (fun n _ => n.toNat) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [mem_Ioc] at hn ⊢; omega
    · intro n hn; simp only [mem_Ioc] at hn ⊢; omega
    · intro n _; simp
    · intro n hn; simp only [mem_Ioc] at hn; omega
    · intro n _; simp
  have hb := H N M |t| hN hM hM' hNt ht
  rw [←he] at hb
  simp only [logPhase,add_zero]
  rcases le_total 0 t with hp | hn
  · rw [abs_of_nonneg hp] at hb
    rw [show (∑ n∈Ioc N M,e (-t/(2*π)*Real.log n)) =
        star (∑ n∈Ioc N M,e (t/(2*π)*Real.log n)) by
          rw [star_sum]; apply sum_congr rfl; intro n _; rw [star_e]; congr 1; ring,
      norm_star,abs_of_nonneg hp]
    exact hb
  · simpa only [abs_of_nonpos hn] using hb

private theorem vertical_block {c C T η : ℝ} (hc : 0<c) (hC : 0<C) {M b : ℕ}
    (hM : 1≤M) (hmb : M≤b) (hb : b≤2*M) (z : ℂ) (hη : 0≤η)
    (hη' : η≤1/4) (hσ : 1-η≤z.re) (hT : T=|z.im|) (ht : 16≤T) (hMt : (M:ℝ)≤T)
    (H : ∀ (N M : ℕ) (u : ℝ), 1≤N → N≤M → M≤2*N → (N:ℝ)≤u → 16≤u →
      ‖∑ n∈Ioc (N:ℤ) (M:ℤ), e ((u/(2*π))*Real.log n)‖ ≤
        C*N*Real.exp (-c*(Real.log N)^3/(Real.log u)^2)) :
    ‖∑ n∈Ioc M b,(n:ℂ)^(-z)‖ ≤ C*Real.exp ((1/Real.sqrt c)*η^(3/2:ℝ)*Real.log T) := by
  subst T
  let w (n : ℕ) : ℝ := (max (n:ℝ) 1)^(-z.re)
  let f (n : ℕ) : ℂ := e (logPhase (-z.im/(2*π)) 0 n)
  have hMr : (1:ℝ)≤M := by exact_mod_cast hM
  have hm := zero_lt_one.trans_le hMr
  have hw : Antitone w := fun n m hnm => Real.rpow_le_rpow_of_nonpos
    (zero_lt_one.trans_le (le_max_right ..)) (max_le_max_right _ (by exact_mod_cast hnm)) (by linarith)
  have hw0 (n : ℕ) : 0≤w n := Real.rpow_nonneg (zero_le_one.trans (le_max_right ..)) _
  have hh (k : ℕ) (hk : M≤k) (hk' : k≤b) := nat_log_block ht hM hk (hk'.trans hb) hMt H
  have heq (n : ℕ) (hn : n∈Ioc M b) : (n:ℂ)^(-z)=(w n:ℂ)*f n := by
    simpa only [Complex.re_add_im] using vertical_log_term (hM.trans (mem_Ioc.mp hn).1.le) z.re z.im
  rw [sum_congr rfl heq]
  apply (norm_sum_Ioc_antitone_weight w f hw hw0 hmb (by positivity) hh).trans
  have hmul : w M*(C*M*Real.exp (-c*(Real.log M)^3/(Real.log |z.im|)^2)) =
      C*Real.exp ((1-z.re)*Real.log M-c*(Real.log M)^3/(Real.log |z.im|)^2) := by
    dsimp [w]; rw [max_eq_left hMr,Real.rpow_def_of_pos hm,
      show (1-z.re)*Real.log M-c*(Real.log M)^3/(Real.log |z.im|)^2 =
        Real.log M+Real.log M*(-z.re)+(-c*(Real.log M)^3/(Real.log |z.im|)^2) by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hm]; ring
  rw [hmul]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hC.le
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_right (by linarith : 1-z.re≤η) (Real.log_nonneg hMr)) _).trans
    (vinogradov_cubic_saving (Real.log_nonneg hMr) hη hc (Real.log_pos (by linarith)))

/-- Partial summation, dyadic decomposition, and the sharp truncation of zeta
transfer cubic block cancellation to the three-halves strip estimate. -/
theorem vinogradovKorobov_growth_of_blocks (H : VinogradovKorobovBlockCancellation) :
    VinogradovKorobovStripGrowth := by
  obtain ⟨c,hc,C,hC,hblocks⟩ := H
  obtain ⟨A,hA,hap⟩ := riemannZeta_approx_dirichletPoly_sub_bound (c:=2) (by norm_num)
    (by linarith [Real.pi_gt_three])
  refine ⟨1/Real.sqrt c,by positivity,A+3+2*C,by positivity,?_⟩
  intro z η hη hη' hσ ht
  let T := |z.im|
  let N := ⌈T/2⌉₊
  have hT : 16≤T := ht
  have hT0 : 0<T := by linarith
  have hN : 1≤N := Nat.one_le_ceil_iff.mpr (by positivity)
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hlo : T/2≤N := Nat.le_ceil _
  have hhi : (N:ℝ)≤T := (Nat.ceil_lt_add_one (by positivity : 0≤T/2)).le.trans (by linarith)
  have hσp : 0<z.re := by linarith
  have herr := hap (N:=N) (σ:=z.re) (t:=z.im) hN hσp (by linarith) (by change T≤2*N; linarith)
  rw [Complex.re_add_im] at herr
  have hfrac : (N:ℝ)^(1-z.re)/T≤1 := by
    rw [div_le_one hT0]
    exact (Real.rpow_le_rpow_of_exponent_le hn (by linarith : 1-z.re≤1)).trans (by rwa [Real.rpow_one])
  have htail := Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr hσp.le)
  let J := Nat.log 2 N+1
  let L := 1+Real.log T
  let E := Real.exp ((1/Real.sqrt c)*η^(3/2:ℝ)*Real.log T)
  have hlog := Real.log_nonneg (by linarith : 1≤T)
  have hL : 1≤L := by dsimp only [L]; linarith
  have hE : 1≤E := Real.one_le_exp (by positivity)
  have hJN := Nat.pow_log_le_self 2 (by omega : N≠0)
  have hJ : (J:ℝ)≤2*L := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 N))
      ((by exact_mod_cast hJN : (2:ℝ)^Nat.log 2 N≤N).trans hhi)
    rw [Real.log_pow] at h
    dsimp [J,L]; push_cast
    nlinarith only [h,mul_le_mul_of_nonneg_left
      (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2) (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 N))]
  let f (n : ℕ) := (n:ℂ)^(-z)
  have each (j : ℕ) (hj : j∈range J) : ‖∑ n∈dyadicBlock N j,f n‖ ≤ C*E := by
    have hm : 1≤2^j := Nat.one_le_two_pow
    have hmn : 2^j≤N := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt_succ (mem_range.mp hj))).trans hJN
    have hmn' : ((2^j:ℕ):ℝ)≤N := by exact_mod_cast hmn
    exact vertical_block hc hC hm (le_min hmn (Nat.pow_le_pow_right (by decide) (by omega)))
      ((min_le_right N (2^(j+1))).trans_eq (by rw [pow_succ]; ring)) z hη hη' hσ rfl ht (hmn'.trans hhi) hblocks
  have hpoly : ‖dirichletPoly (fun _ => 1) N z‖≤1+J*(C*E) := by
    change ‖∑ n∈Icc 1 N,(1:ℂ)*f n‖≤_
    simp only [one_mul]
    rw [sum_Icc_eq_dyadic_blocks f hN (Nat.lt_pow_succ_log_self one_lt_two N).le]
    apply (norm_add_le ..).trans
    exact add_le_add (by simp [f]) ((norm_sum_le ..).trans ((sum_le_sum each).trans_eq (by simp)))
  have htri := norm_add_le (riemannZeta z-dirichletPoly (fun _ => 1) N z) (dirichletPoly (fun _ => 1) N z)
  rw [sub_add_cancel] at htri
  change ‖riemannZeta z‖ ≤ (A+3+2*C)*L*E
  change ‖riemannZeta z-dirichletPoly (fun _ => 1) N z‖ ≤ (N:ℝ)^(1-z.re)/T+A*(N:ℝ)^(-z.re) at herr
  nlinarith only [htri,herr,hpoly,hfrac,mul_le_mul_of_nonneg_left htail hA.le,
    mul_le_mul_of_nonneg_right hJ (mul_nonneg hC.le (zero_le_one.trans hE)),
    mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hL hE) (show 0≤A+3 by linarith)]

end AnalyticNumberTheory.RiemannZeta
