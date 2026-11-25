import AnalyticNumberTheory.RiemannZeta.RiemannSharpApproximation
import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximation

/-!
# Sharp approximate functional equation for periodic L-functions

Grouping positive integers by their residues produces the direct polynomial
of length qx. On the reciprocal side the finite Fourier transform of the
periodic coefficients multiplies the gamma modes at ±2πn, with n≤y.
-/
noncomputable section
open Real Complex Finset
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Evaluation of the finite Fourier transform using the representatives
1,…,q and the unnormalized angular frequency ω. -/
def periodicFourierCoeff {q : ℕ} (Φ : ZMod q → ℂ) (ω : ℝ) :=
  ∑ r∈range q,Φ ((r+1:ℕ):ZMod q)*hurwitzShift (((r+1:ℕ):ℝ)/q) ω

/-- Reciprocal Dirichlet polynomial for a periodic coefficient function. -/
def periodicDualSum {q : ℕ} (Φ : ZMod q → ℂ) (y : ℝ) (s : ℂ) :=
  (q:ℂ)^(-s)*∑ m∈range ⌊y⌋₊,(
    periodicFourierCoeff Φ (hurwitzOmega m)*hurwitzDualMode s (hurwitzOmega m)+
    periodicFourierCoeff Φ (-hurwitzOmega m)*hurwitzDualMode s (-hurwitzOmega m))

private theorem reindex {q : ℕ} [NeZero q] {x : ℝ} (hx : 1≤x) (g : ℕ → ℂ) :
    (∑ r∈range q,∑ m∈Icc 0 ⌊x-((r+1:ℕ):ℝ)/q⌋₊,g (q*m+r+1)) =
    ∑ n∈Icc 1 ⌊(q:ℝ)*x⌋₊,g n := by
  have hq := NeZero.pos q
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq
  have hqx : 0≤(q:ℝ)*x := mul_nonneg hq'.le (by linarith)
  have H (r m : ℕ) (hr : r<q) : m≤⌊x-((r+1:ℕ):ℝ)/q⌋₊ ↔ q*m+r+1≤⌊(q:ℝ)*x⌋₊ := by
    have ha : ((r+1:ℕ):ℝ)/q≤1 := (div_le_one hq').mpr (by exact_mod_cast hr)
    rw [Nat.le_floor_iff (by linarith),Nat.le_floor_iff hqx,le_sub_iff_add_le,←mul_le_mul_iff_right₀ hq']
    push_cast
    field_simp
    constructor <;> intro hh <;> nlinarith
  rw [sum_sigma']
  refine sum_bij (fun p _ => q*p.2+p.1+1) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨r,m⟩ hp
    obtain ⟨hr,hm⟩ := mem_sigma.mp hp
    exact mem_Icc.mpr ⟨by omega,(H r m (mem_range.mp hr)).mp (mem_Icc.mp hm).2⟩
  · rintro ⟨r,m⟩ hp ⟨v,j⟩ hj he
    have hr := mem_range.mp (mem_sigma.mp hp).1
    have hv := mem_range.mp (mem_sigma.mp hj).1
    change q*m+r+1=q*j+v+1 at he
    have h : q*m+r=q*j+v := by omega
    have h₁ := congrArg (· % q) h
    have h₂ := congrArg (· / q) h
    simp [Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hv] at h₁
    simp [Nat.mul_add_div hq,Nat.div_eq_of_lt hr,Nat.div_eq_of_lt hv] at h₂
    congr
  · intro n hn
    let r := (n-1)%q
    let m := (n-1)/q
    have hr : r<q := Nat.mod_lt _ hq
    have he : q*m+r+1=n := by dsimp [m,r];rw [Nat.div_add_mod]; have := (mem_Icc.mp hn).1;omega
    exact ⟨⟨r,m⟩,mem_sigma.mpr ⟨mem_range.mpr hr,mem_Icc.mpr ⟨by omega,(H r m hr).mpr (he ▸ (mem_Icc.mp hn).2)⟩⟩,he⟩

/-- Splitting an arbitrary sharp direct polynomial into residue classes. -/
theorem periodic_directSum {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) {x : ℝ} (hx : 1≤x) (s : ℂ) :
    dirichletPoly (fun n : ℕ => Φ n) ⌊(q:ℝ)*x⌋₊ s =
    (q:ℂ)^(-s)*∑ r∈range q,Φ ((r+1:ℕ):ZMod q)*hurwitzDirectSum (((r+1:ℕ):ℝ)/q) x s := by
  rw [dirichletPoly,←reindex hx,mul_sum]
  apply sum_congr rfl
  intro r hr
  rw [hurwitzDirectSum,←mul_assoc,mul_sum]
  apply sum_congr rfl
  intro m hm
  have hq := NeZero.pos q
  have he : ((q*m+r+1:ℕ):ℝ)=(q:ℝ)*((m:ℝ)+((r+1:ℕ):ℝ)/q) := by push_cast; field_simp; ring
  have hw := Complex.mul_cpow_ofReal_nonneg (by positivity : 0≤(q:ℝ))
    (by positivity : 0≤(m:ℝ)+((r+1:ℕ):ℝ)/q) (-s)
  rw [←Complex.ofReal_mul,←he] at hw
  simp only [Complex.ofReal_natCast,Complex.ofReal_add] at hw
  rw [show (((q*m+r+1:ℕ):ZMod q))=((r+1:ℕ):ZMod q) by simp,hw];ring

theorem periodic_dualSum {q : ℕ} (Φ : ZMod q → ℂ) (y : ℝ) (s : ℂ) :
    periodicDualSum Φ y s=(q:ℂ)^(-s)*∑ r∈range q,Φ ((r+1:ℕ):ZMod q)*hurwitzDualSum (((r+1:ℕ):ℝ)/q) y s := by
  rw [periodicDualSum]
  congr 1
  simp only [periodicFourierCoeff,sum_mul,←sum_add_distrib,hurwitzDualSum,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro m hm
  dsimp only [hurwitzPair];ring

/-- Sharp two-sided periodic approximate functional equation, uniform in q
and in coefficient functions bounded by one. The direct cutoff is qx,
the reciprocal cutoff is y, and their product is q|Im s|/(2π). -/
theorem periodicLFunction_sharp_afe {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (hΦ : ∀ j, ‖Φ j‖≤1)
    {x y : ℝ} (hx : 2≤x) (hy : 2≤y) {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖ZMod.LFunction Φ s-dirichletPoly (fun n : ℕ => Φ n) ⌊(q:ℝ)*x⌋₊ s-periodicDualSum Φ y s‖ ≤
      (q:ℝ)^(1-s.re)*(256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt |s.im|)) := by
  let E := 256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt |s.im|)
  have hq : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  rw [ZMod.LFunction,sum_residues_succ,periodic_directSum Φ (by linarith) s,periodic_dualSum,
    ←mul_sub,←mul_sub,←sum_sub_distrib,←sum_sub_distrib,norm_mul,Complex.norm_natCast_cpow_of_pos (NeZero.pos q),neg_re]
  calc
    _ ≤ (q:ℝ)^(-s.re)*(∑ r∈range q,E) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro r hr
      rw [←mul_sub,←mul_sub,norm_mul,ZMod.toAddCircle_natCast]
      have H := hurwitzZeta_rational_sharp_afe (j:=r+1) (by omega) (mem_range.mp hr) hx hy hσ hσ' hxy
      exact (mul_le_mul (hΦ _) H (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by
      rw [sum_const,card_range,nsmul_eq_mul,show 1-s.re= -s.re+1 by ring,Real.rpow_add hq,Real.rpow_one]
      dsimp [E];ring

/-- Every Dirichlet character, including imprimitive characters, specializes
the periodic equation with the same period-uniform error. -/
theorem dirichletLFunction_sharp_afe {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x y : ℝ} (hx : 2≤x) (hy : 2≤y) {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖χ.LFunction s-dirichletPoly (fun n : ℕ => χ n) ⌊(q:ℝ)*x⌋₊ s-periodicDualSum χ y s‖ ≤
      (q:ℝ)^(1-s.re)*(256*(1+1/(1-s.re))*(x^(-s.re)*(1+Real.log (y+2))+x^(1-s.re)/Real.sqrt |s.im|)) :=
  periodicLFunction_sharp_afe χ χ.norm_le_one hx hy hσ hσ' hxy

end AnalyticNumberTheory.DirichletLFunctions
