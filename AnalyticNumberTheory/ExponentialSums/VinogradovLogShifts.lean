import AnalyticNumberTheory.ExponentialSums.VinogradovLogTaylor

/-!
# Shifting a logarithmic exponential sum by products

Averaging the shifts `x y` for `1 ≤ x,y ≤ a` reduces the logarithmic sum
to short polynomial bilinear sums. Both the endpoint error and the
Taylor remainder remain explicit.
-/

open Finset Real Complex
namespace AnalyticNumberTheory.ExponentialSums

private theorem sum_Ioc_append (f : ℤ → ℂ) {a b c : ℤ} (hab : a≤b) (hbc : b≤c) :
    (∑ n∈Ioc a b, f n) + (∑ n∈Ioc b c, f n) = ∑ n∈Ioc a c, f n := by
  rw [←sum_union (Ioc_disjoint_Ioc_of_le le_rfl),Ioc_union_Ioc_eq_Ioc hab hbc]

/-- Translating an interval by a nonnegative integer changes the exponential
sum by at most twice the shift, including when the two intervals are disjoint. -/
theorem norm_sum_Ioc_shift_sub_le (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖≤1)
    {N M h : ℤ} (hNM : N≤M) (hh : 0≤h) :
    ‖(∑ n∈Ioc N M, f n) - ∑ n∈Ioc N M, f (n+h)‖ ≤ 2*(h:ℝ) := by
  have hshift : (∑ n∈Ioc N M, f (n+h)) = ∑ n∈Ioc (N+h) (M+h), f n := by
    apply sum_bij' (fun n _ => n+h) (fun n _ => n-h)
    all_goals simp only [mem_Ioc]
    all_goals intros; first | trivial | omega
  have h1 := sum_Ioc_append f hNM (show M≤M+h by omega)
  have h2 := sum_Ioc_append f (show N≤N+h by omega) (show N+h≤M+h by omega)
  have he : (∑ n∈Ioc N M,f n)-(∑ n∈Ioc (N+h) (M+h),f n) =
      (∑ n∈Ioc N (N+h),f n)-(∑ n∈Ioc M (M+h),f n) := by linear_combination h1-h2
  have hb (A : ℤ) : ‖∑ n∈Ioc A (A+h), f n‖ ≤ h := by
    apply (norm_sum_le ..).trans
    apply (sum_le_sum (fun n _ => hf n)).trans_eq
    simp [Int.card_Ioc]
    exact_mod_cast (Int.toNat_of_nonneg hh)
  rw [hshift,he]
  exact (norm_sub_le ..).trans (by linarith only [hb N,hb M])

private theorem norm_sum_sub_approx {ι : Type*} (S : Finset ι) (f g : ι → ℂ) (E : ℝ)
    (h : ∀ i∈S, ‖f i-g i‖≤E) :
    ‖∑ i∈S,f i‖ ≤ ‖∑ i∈S,g i‖ + S.card*E := by
  have hd : ‖(∑ i∈S,f i)-(∑ i∈S,g i)‖ ≤ S.card*E := by
    rw [←sum_sub_distrib]
    apply (norm_sum_le ..).trans ((sum_le_sum h).trans_eq _)
    simp
  have H := norm_add_le ((∑ i∈S,f i)-(∑ i∈S,g i)) (∑ i∈S,g i)
  rw [sub_add_cancel] at H
  linarith

/-- An average of arbitrary product shifts, with the boundary loss separated
from the central sums. -/
theorem bilinear_shift_average (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖≤1)
    {N M : ℤ} (hNM : N≤M) (a : ℕ) :
    (a:ℝ)^2 * ‖∑ n∈Ioc N M,f n‖ ≤
      (∑ n∈Ioc N M, ‖∑ p∈Icc 1 (a:ℤ) ×ˢ Icc 1 (a:ℤ),f (n+p.1*p.2)‖) + 2*(a:ℝ)^4 := by
  let B := Icc 1 (a:ℤ)
  let P := B ×ˢ B
  let S := ∑ n∈Ioc N M,f n
  have hc : (P.card:ℝ)=(a:ℝ)^2 := by simp [P,B,Int.card_Icc,sq]
  have h (p : ℤ×ℤ) (hp : p∈P) :
      ‖S-∑ n∈Ioc N M,f (n+p.1*p.2)‖≤2*(a:ℝ)^2 := by
    obtain ⟨hx,hy⟩ := mem_product.mp hp
    have hx' := mem_Icc.mp hx
    have hy' := mem_Icc.mp hy
    have hx0 : (0:ℤ)≤p.1 := by omega
    have hy0 : (0:ℤ)≤p.2 := by omega
    apply (norm_sum_Ioc_shift_sub_le f hf hNM (mul_nonneg hx0 hy0)).trans
    have hh := mul_le_mul hx'.2 hy'.2 hy0 (Int.natCast_nonneg _)
    push_cast
    exact_mod_cast (show 2*(p.1*p.2)≤2*(a:ℤ)^2 by linarith only [hh])
  have H := norm_sum_sub_approx P (fun _ => S) (fun p => ∑ n∈Ioc N M,f (n+p.1*p.2)) _ h
  simp only [sum_const,nsmul_eq_mul,norm_mul,Complex.norm_natCast,hc] at H
  rw [sum_comm (s:=P) (t:=Ioc N M)] at H
  apply H.trans
  have ht := norm_sum_le (Ioc N M) (fun n => ∑ p∈P,f (n+p.1*p.2))
  change _ ≤ _ + 2*(a:ℝ)^4
  linarith only [ht]

/-- Uniform reduction of a logarithmic block to polynomial bilinear sums.
The error terms come from the translated endpoints and the Taylor tail. -/
theorem logarithmic_block_bilinear_reduction_shift (k : ℕ) (t θ : ℝ) (hθ : 0≤θ) {N M a : ℕ}
    (hN : 0<N) (hNM : N≤M) (ha : 0<a) (hsmall : (a:ℝ)^2/N ≤ 1/2) :
    ‖∑ n∈Ioc (N:ℤ) M, e ((t/(2*Real.pi))*Real.log ((n:ℝ)+θ))‖ ≤
      (∑ n∈Ioc (N:ℤ) M, ‖vinogradovBilinearSum (Icc 1 (a:ℤ)) (logTaylorCoefficients k t ((n:ℝ)+θ))‖)/(a:ℝ)^2 +
      2*(a:ℝ)^2 + ((M:ℝ)-N)*(2*|t| *((a:ℝ)^2/N)^(k+1)) := by
  let B := Icc 1 (a:ℤ)
  let P := B ×ˢ B
  let E := 2*|t| *((a:ℝ)^2/N)^(k+1)
  let f (n : ℤ) := e ((t/(2*Real.pi))*Real.log ((n:ℝ)+θ))
  have hc : (P.card:ℝ)=(a:ℝ)^2 := by simp [P,B,Int.card_Icc,sq]
  have hcard : ((Ioc (N:ℤ) M).card:ℝ)=(M:ℝ)-N := by
    rw [Int.card_Ioc]
    exact_mod_cast (Int.toNat_of_nonneg (show 0≤(M:ℤ)-N by omega))
  have ht (n : ℤ) (hn : n∈Ioc (N:ℤ) M) :
      ‖∑ p∈P,f (n+p.1*p.2)‖ ≤
      ‖vinogradovBilinearSum B (logTaylorCoefficients k t ((n:ℝ)+θ))‖+(a:ℝ)^2*E := by
    have hnN : (N:ℝ)≤(n:ℝ)+θ := by
      linarith only [hθ,show (N:ℝ)≤n by exact_mod_cast (mem_Ioc.mp hn).1.le]
    have hNr : 0<(N:ℝ) := by exact_mod_cast hN
    have hnr : 0<(n:ℝ)+θ :=  lt_of_lt_of_le hNr hnN
    let g (p : ℤ×ℤ) := e ((t/(2*Real.pi))*Real.log ((n:ℝ)+θ)) *
      diagonalBilinearChar (logTaylorCoefficients k t ((n:ℝ)+θ)) (vinogradovCurve k p.2) (vinogradovCurve k p.1)
    have happrox (p : ℤ×ℤ) (hp : p∈P) : ‖f (n+p.1*p.2)-g p‖≤E := by
      obtain ⟨hx,hy⟩ := mem_product.mp hp
      have hx' := mem_Icc.mp hx
      have hy' := mem_Icc.mp hy
      have hx0 : 0≤p.1 := by omega
      have hy0 : 0≤p.2 := by omega
      have hxy : 0≤(p.2:ℝ)*p.1 := by exact_mod_cast mul_nonneg hy0 hx0
      have hxy' : (p.2:ℝ)*p.1≤(a:ℝ)^2 := by
        rw [sq]; exact_mod_cast mul_le_mul hy'.2 hx'.2 hx0 (Int.natCast_nonneg _)
      have hb : (p.2:ℝ)*p.1/((n:ℝ)+θ) ≤ (a:ℝ)^2/N := div_le_div₀ (sq_nonneg _) hxy' hNr hnN
      have hlog : Real.log (((n:ℝ)+(p.1:ℝ)*p.2)+θ) = Real.log ((n:ℝ)+θ)+Real.log (1+(p.2:ℝ)*p.1/((n:ℝ)+θ)) := by
        rw [←Real.log_mul hnr.ne' (by positivity)]
        congr 1; field_simp [hnr.ne']; ring
      dsimp only [f,g]; push_cast; rw [hlog,mul_add,e_add,←mul_sub,norm_mul,norm_e,one_mul]
      apply (logTaylor_character_error k t hnr hxy (hb.trans hsmall)).trans
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hxy hnr.le) hb _) (by positivity)
    have H := norm_sum_sub_approx P (fun p => f (n+p.1*p.2)) g E happrox
    have hg : (∑ p∈P,g p) = e ((t/(2*Real.pi))*Real.log ((n:ℝ)+θ))*
        vinogradovBilinearSum B (logTaylorCoefficients k t ((n:ℝ)+θ)) := by
      simp only [P,g,←mul_sum,sum_product,vinogradovBilinearSum,vinogradovTorusSum,
        torusCharSum,diagonalBilinearChar]
    simpa only [hg,norm_mul,norm_e,one_mul,hc] using H
  have A := bilinear_shift_average f (fun n => (norm_e _).le) (by exact_mod_cast hNM : (N:ℤ)≤M) a
  have H := sum_le_sum ht
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,hcard] at H
  let W := ∑ n∈Ioc (N:ℤ) M, ‖vinogradovBilinearSum B (logTaylorCoefficients k t ((n:ℝ)+θ))‖
  change _ ≤ W/(a:ℝ)^2 + 2*(a:ℝ)^2 + ((M:ℝ)-N)*E
  have ha0 : 0<(a:ℝ) := by exact_mod_cast ha
  have H' : (a:ℝ)^2*‖∑ n∈Ioc (N:ℤ) M, f n‖ ≤ W+((M:ℝ)-N)*((a:ℝ)^2*E)+2*(a:ℝ)^4 :=
    A.trans (add_le_add_left H _)
  rw [←le_div_iff₀' (sq_pos_of_pos ha0)] at H'
  apply H'.trans_eq
  field_simp; ring

/-- Uniform reduction of a logarithmic block to polynomial bilinear sums.
The error terms come from the translated endpoints and the Taylor tail. -/
theorem logarithmic_block_bilinear_reduction (k : ℕ) (t : ℝ) {N M a : ℕ}
    (hN : 0<N) (hNM : N≤M) (ha : 0<a) (hsmall : (a:ℝ)^2/N ≤ 1/2) :
    ‖∑ n∈Ioc (N:ℤ) M, e ((t/(2*Real.pi))*Real.log n)‖ ≤
      (∑ n∈Ioc (N:ℤ) M, ‖vinogradovBilinearSum (Icc 1 (a:ℤ)) (logTaylorCoefficients k t n)‖)/(a:ℝ)^2 +
      2*(a:ℝ)^2 + ((M:ℝ)-N)*(2*|t| *((a:ℝ)^2/N)^(k+1)) := by
  simpa only [add_zero] using logarithmic_block_bilinear_reduction_shift k t 0 le_rfl hN hNM ha hsmall

end AnalyticNumberTheory.ExponentialSums
