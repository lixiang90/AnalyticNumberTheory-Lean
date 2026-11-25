import AnalyticNumberTheory.ExponentialSums.MonomialDerivativeTests
import AnalyticNumberTheory.ExponentialSums.LogPhaseCorrelations
import AnalyticNumberTheory.ExponentialSums.ReciprocalRealBlocks

/-!
# Exponent-pair estimates for reciprocal phases

The physical third-derivative test and the fifth-derivative test after
the reciprocal B-process give complementary ranges in the divisor problem.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

local macro "log_powers" : tactic => `(tactic|
  (apply Real.log_injOn_pos
   · simp only [Set.mem_Ioi]; positivity
   · simp only [Set.mem_Ioi]; positivity
   simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow,Real.log_pow,
     Real.log_sqrt,Real.log_inv,Real.log_one]
   <;> ring))

/-- The third-derivative estimate for a reciprocal phase on a dyadic block. -/
theorem reciprocal_third_derivative_block :
    ∃ C≥1, ∀ {A D : ℝ} {a b : ℕ},0<A → 1≤D → D≤a → (b:ℝ)≤2*D →
    ‖∑ n∈Ioc a b,e (A/n)‖≤C*(A^(1/6:ℝ)*D^(1/3:ℝ)+A^(-(1/6):ℝ)*D^(7/6:ℝ)) := by
  obtain ⟨C,hC,H⟩ := vanDerCorput_monomial (k:=3) (s:=-1) (by decide) (by norm_num)
    (by norm_num [fallingPower,Finset.prod_range_succ])
  refine ⟨C,hC,?_⟩
  intro A D a b hA hD ha hb
  have hD' : 0<D := by linarith
  have hh := H hA hD (show D/8≤a by linarith) hb
  simp only [Real.rpow_neg_one,←div_eq_mul_inv] at hh
  apply hh.trans_eq
  congr 1
  apply congrArg₂ (·+·) <;> log_powers

private theorem squareRoot_fifth_derivative_block :
    ∃ C≥1, ∀ {A W : ℝ} {a b : ℕ},0<A → 1≤W → W/8≤a → (b:ℝ)≤2*W →
    ‖∑ n∈Ioc a b,e (2*Real.sqrt (A*n))‖≤C*(W*(A^(1/2:ℝ)*W^(-(9/2):ℝ))^(1/30:ℝ)+
      W^(7/8:ℝ)*(A^(1/2:ℝ)*W^(-(9/2):ℝ))^(-(1/30):ℝ)) := by
  obtain ⟨C,hC,H⟩ := vanDerCorput_monomial (k:=5) (s:=1/2) (by decide) (by norm_num)
    (by norm_num [fallingPower,Finset.prod_range_succ])
  refine ⟨2*C,by linarith,?_⟩
  intro A W a b hA hW ha hb
  have hW' : 0<W := by linarith
  let L := A^(1/2:ℝ)*W^(-(9/2):ℝ)
  have hL : 0<L := by dsimp [L]; positivity
  have H' := H (show 0<2*Real.sqrt A by positivity) hW ha hb
  have he (n : ℕ) : 2*Real.sqrt (A*n)=2*Real.sqrt A*(n:ℝ)^(1/2:ℝ) := by
    rw [Real.sqrt_mul hA.le,Real.sqrt_eq_rpow (x:=(n:ℝ))]; ring
  simp_rw [he]
  apply H'.trans
  change C*(W*(2*Real.sqrt A*W^((1:ℝ)/2-5))^(1/((2:ℝ)^5-2))+
    W^(1-((2:ℝ)⁻¹)^3)*(2*Real.sqrt A*W^((1:ℝ)/2-5))^(-(1/((2:ℝ)^5-2))))≤
    2*C*(W*L^(1/30:ℝ)+W^(7/8:ℝ)*L^(-(1/30):ℝ))
  rw [show 2*Real.sqrt A*W^((1:ℝ)/2-5)=2*L by dsimp [L]; rw [Real.sqrt_eq_rpow]; norm_num; ring,
    show (1:ℝ)/((2:ℝ)^5-2)=1/30 by norm_num,show (1:ℝ)-((2:ℝ)⁻¹)^3=7/8 by norm_num,
    Real.mul_rpow (by norm_num) hL.le,Real.mul_rpow (by norm_num) hL.le]
  have htwo (p : ℝ) (hp : p≤1) : (2:ℝ)^p≤2 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp).trans_eq (Real.rpow_one _)
  have h₁ := htwo (1/30) (by norm_num)
  have h₂ := htwo (-(1/30)) (by norm_num)
  calc
    _ ≤ C*(W*(2*L^(1/30:ℝ))+W^(7/8:ℝ)*(2*L^(-(1/30):ℝ))) := by gcongr
    _ = _ := by ring

/-- A uniform estimate for the square-root saddle terms. The lower
frequency may be zero, and both bounds can be anywhere in the dyadic window. -/
theorem reciprocal_saddle_fifth_derivative :
    ∃ C≥1, ∀ {A W : ℝ} {a b : ℕ},0<A → 1≤W → W/4≤(a:ℝ)+1 → (b:ℝ)≤W →
    ‖∑ n∈Ioc a b,reciprocalSaddleTerm A n‖ ≤ C*A^(1/4:ℝ)*W^(-(3/4):ℝ)*
      (W*(A^(1/2:ℝ)*W^(-(9/2):ℝ))^(1/30:ℝ)+
        W^(7/8:ℝ)*(A^(1/2:ℝ)*W^(-(9/2):ℝ))^(-(1/30):ℝ)) := by
  obtain ⟨C,hC,H⟩ := squareRoot_fifth_derivative_block
  let B := ((4:ℝ)⁻¹)^(-(3/4):ℝ)
  have hB : 1≤B := by
    dsimp [B]; rw [Real.inv_rpow (by norm_num),←Real.rpow_neg (by norm_num),neg_neg]
    exact Real.one_le_rpow (by norm_num) (by norm_num)
  refine ⟨(1+C)*B,one_le_mul_of_one_le_of_one_le (by linarith) hB,?_⟩
  intro A W a b hA hW ha hb
  have hW' : 0<W := by linarith
  let L := A^(1/2:ℝ)*W^(-(9/2):ℝ)
  let S := W*L^(1/30:ℝ)+W^(7/8:ℝ)*L^(-(1/30):ℝ)
  have hL : 0<L := by dsimp [L]; positivity
  have hS : 1≤S := by
    by_cases h : 1≤L
    · exact (one_le_mul_of_one_le_of_one_le hW (Real.one_le_rpow h (by norm_num))).trans
        (le_add_of_nonneg_right (by positivity))
    · exact (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hW (by norm_num : (0:ℝ)≤7/8))
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hL (not_le.mp h).le (by norm_num))).trans
        (le_add_of_nonneg_left (by positivity))
  have hS' : 0≤S := by linarith
  by_cases hab : a<b
  swap
  · rw [Ioc_eq_empty_of_le (not_lt.mp hab),sum_empty,norm_zero]; change 0≤_*S; positivity
  let u := a+1
  have hub : u≤b := hab
  have hu : W/4≤(u:ℝ) := by simpa [u] using ha
  have hup : 0<(u:ℝ) := by linarith
  let f (n : ℕ) := e (2*Real.sqrt (A*n))
  let w (n : ℕ) := (n:ℝ)^(-(3/4):ℝ)
  have hpartial {t : ℕ} (_ : u≤t) (ht : t≤b) : ‖∑ n∈Ioc u t,f n‖≤C*S :=
    H (a:=u) (b:=t) hA hW (by linarith) (by linarith [show (t:ℝ)≤b by exact_mod_cast ht])
  have hw : AntitoneOn w (Set.Icc u b) := by
    intro n hn m _ hnm
    exact Real.rpow_le_rpow_of_nonpos (hup.trans_le (Nat.cast_le.mpr hn.1))
      (Nat.cast_le.mpr hnm) (by norm_num)
  have hsum := norm_sum_Ioc_antitone_weight (c:=f) hub hw (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ ht ht' => hpartial ht ht')
  have hwu : w u≤B*W^(-(3/4):ℝ) := by
    have h := Real.rpow_le_rpow_of_nonpos (show 0<(4:ℝ)⁻¹*W by positivity)
      (show (4:ℝ)⁻¹*W≤u by linarith) (by norm_num : -(3/4:ℝ)≤0)
    rwa [Real.mul_rpow (by norm_num) hW'.le] at h
  let g (n : ℕ) := f n*(w n:ℂ)
  have hboth : ‖∑ n∈Ioc a b,g n‖ ≤ ((1+C)*S)*(B*W^(-(3/4):ℝ)) := by
    rw [←sum_Ioc_consecutive g (Nat.le_succ a) hub]
    have hsub : Ioc a (a+1)={a+1} := by ext i; simp only [mem_Ioc,mem_singleton]; omega
    rw [hsub,sum_singleton]
    apply (norm_add_le ..).trans
    have hfirst : ‖g u‖=w u := by
      dsimp only [g,f]; rw [norm_mul,norm_e,one_mul,Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    change ‖g u‖+_≤_
    rw [hfirst]
    calc
      _ ≤ w u+(C*S)*w u := by gcongr
      _ ≤ ((1+C)*S)*w u := by
        nlinarith only [mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg (Nat.cast_nonneg u) (-(3/4):ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left hwu (by positivity)
  let z : ℂ := ((A^(1/4:ℝ):ℝ):ℂ)*((1+Complex.I)/2)
  have hz : ‖z‖≤A^(1/4:ℝ) := by
    dsimp [z]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity),
      norm_div,Complex.norm_ofNat]
    have ht := norm_add_le (1:ℂ) Complex.I
    simp only [norm_one,Complex.norm_I] at ht
    calc _ ≤ A^(1/4:ℝ)*1 := by gcongr; linarith
         _ = _ := mul_one _
  have he (n : ℕ) : reciprocalSaddleTerm A n=g n*z := by
    dsimp [reciprocalSaddleTerm,g,z,f,w]; push_cast; ring
  simp_rw [he]
  rw [←sum_mul,norm_mul]
  apply (mul_le_mul hboth hz (norm_nonneg _) (by positivity)).trans_eq
  change _=(1+C)*B*A^(1/4:ℝ)*W^(-(3/4):ℝ)*S
  ring

end AnalyticNumberTheory.ExponentialSums
