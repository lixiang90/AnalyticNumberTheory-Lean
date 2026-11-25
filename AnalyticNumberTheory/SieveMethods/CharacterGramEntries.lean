import AnalyticNumberTheory.SieveMethods.SmoothedCharacterKernel

/-!
# Gram entries for character sums on a dyadic interval

The vector indexed by (χ,u) contains frequencies from all positive
integers. Its absolute smoothing factor is (n/X)^(3/2) exp(−n/(2X)).
On the dyadic interval this factor is bounded away from zero.
-/
noncomputable section
open Complex Real Set
open scoped ComplexConjugate Classical
namespace AnalyticNumberTheory.SieveMethods

/-- A centered and exponentially smoothed vector for a character sample. -/
def characterGramVector (X : ℝ) (f : ℕ→ℂ) (u : ℂ) (n : ℕ) : ℂ :=
  if n=0 then 0 else f n*(X:ℂ)^(u-3/2)*(n:ℂ)^(3/2-u)*(Real.exp (-(n:ℝ)/(2*X)):ℂ)

/-- Pointwise correlation of two smoothed vectors. The character ψ accounts
for both twists, including zeros at integers sharing factors with either level. -/
theorem characterGramVector_hasSum {q : ℕ} [NeZero q] {f g : ℕ→ℂ} (ψ : DirichletCharacter ℂ q)
    (hψ : ∀n : ℕ,ψ n=f n*conj (g n)) {X : ℝ} (hX : 0<X) {u v : ℂ}
    (h : (u+conj v).re∈Icc (0:ℝ) 2) :
    HasSum (fun n : ℕ => characterGramVector X f u n*conj (characterGramVector X g v n))
      ((X:ℂ)^(u+conj v-3)*smoothedCharacterKernel ψ X (u+conj v)) := by
  apply ((smoothedCharacterKernel_hasSum ψ hX h).mul_left _).congr_fun
  intro n
  rcases eq_or_ne n 0 with rfl|hn
  · simp [characterGramVector,LSeries.term_zero]
  have hn' : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  have hX' := Complex.ofReal_ne_zero.mpr hX.ne'
  have hargX : ((X:ℂ)).arg≠π := by simp [Complex.arg_ofReal_of_nonneg hX.le,Real.pi_ne_zero.symm]
  have hargn : (n:ℂ).arg≠π := by simpa using Real.pi_ne_zero.symm
  have hcX := Complex.cpow_conj (X:ℂ) (v-3/2) hargX
  have hcn := Complex.cpow_conj (n:ℂ) (3/2-v) hargn
  simp only [Complex.conj_ofReal,map_natCast,map_sub,map_div₀,map_ofNat] at hcX hcn
  simp only [characterGramVector,if_neg hn,map_mul,Complex.conj_ofReal,LSeries.term_of_ne_zero hn,hψ n]
  symm
  rw [←hcX,←hcn,div_eq_mul_inv (f n*conj (g n)),←Complex.cpow_neg]
  have he : (Real.exp (-(n:ℝ)/(2*X)):ℂ)*(Real.exp (-(n:ℝ)/(2*X)):ℂ)
        =(Real.exp (-(n:ℝ)/X):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.exp_add];congr 2;ring
  calc _ = (f n*conj (g n))*((X:ℂ)^(u+conj v-3)*(n:ℂ)^(-(u+conj v-3)))*
           (Real.exp (-(n:ℝ)/X):ℂ) := by ring
       _ = (f n*conj (g n))*(((X:ℂ)^(u-3/2)*(X:ℂ)^(conj v-3/2))*
          ((n:ℂ)^(3/2-u)*(n:ℂ)^(3/2-conj v)))*((Real.exp (-(n:ℝ)/(2*X)):ℂ)*
            (Real.exp (-(n:ℝ)/(2*X)):ℂ)) := by
         rw [he,←Complex.cpow_add _ _ hX',←Complex.cpow_add _ _ hn']
         rw [show u-3/2+(conj v-3/2)=u+conj v-3 by ring,
           show 3/2-u+(3/2-conj v)= -(u+conj v-3) by ring]
       _ = _ := by ring

/-- Uniform off-diagonal part and rapidly decreasing principal-character part
of the Gram kernel. -/
theorem characterGramEntry_bound :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {X : ℝ},1≤X →
    ∀{u v : ℂ}, (u+conj v).re∈Icc (0:ℝ) 2 →
    let H := (q:ℝ)*(|u.im-v.im|+2)
    ‖(X:ℂ)^(u+conj v-3)*smoothedCharacterKernel ψ X (u+conj v)‖ ≤
      C*(Real.sqrt H*(1+Real.log H)+(if ψ=1 then X/(1+|u.im-v.im|)^4 else 0)) := by
  obtain ⟨C,hC,h⟩ := smoothedCharacterKernel_bound
  refine ⟨C,hC,?_⟩
  intro q _ ψ X hX u v hs
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hX)]
  convert h ψ hs hX using 1 <;> simp [sub_eq_add_neg]

end AnalyticNumberTheory.SieveMethods
