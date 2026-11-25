import AnalyticNumberTheory.SieveMethods.RosserFundamentalLemma

/-!
# The fundamental lemma for the sifted set

The sieve-dimension hypothesis is imposed on the densities of the sifting
primes. The sifting remainder consists only of the divisors below the level.
-/
noncomputable section
open Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- Sieve-dimension bound for an arithmetic sieve datum at z. -/
def SieveData.hasDimensionAt (s : SieveData) (z A κ : ℝ) : Prop :=
  ∀ w : ℝ, 2≤w → w≤z →
    (∏ p∈(s.prodPrimes z).primeFactors.filter (fun p : ℕ => w≤p), (1-s.density p)⁻¹) ≤
      A*(log z/log w)^κ

private theorem model_bound {A κ : ℝ} (hA : 1≤A) (hκ : 0≤κ) :
    ∃ u₀ : ℝ, ∀ {u z : ℝ}, u₀≤u → 2≤z → ∀ (s : SieveData) (b : Bool),
      (∀p∈(s.prodPrimes z).primeFactors,(p:ℝ)≤z) → s.hasDimensionAt z A κ →
      rosserRemainder s.density (fun l => rosserTruncationFactor (1+u/3) l<z^u) b
        (descPrimeList (s.prodPrimes z)) ≤ 2*A*s.eulerProd z*exp (-(u/2)*log u) := by
  obtain ⟨u₀,h₀⟩ := rosser_fundamental_lemma hA hκ
  refine ⟨u₀,?_⟩
  intro u z hu hz s b hpz hd
  let L := descPrimeList (s.prodPrimes z)
  let g := fun p : ℕ => max 0 (s.density p)
  let C := fun l => rosserTruncationFactor (1+u/3) l<z^u
  have hp (p : ℕ) (hpL : p∈L) : p.Prime := Nat.prime_of_mem_primeFactors (mem_descPrimeList_iff.mp hpL)
  have hg (p : ℕ) (hpL : p∈L) : g p=s.density p := max_eq_right (s.density_nonneg_of_prime (hp p hpL))
  have hprod (f : ℕ → ℝ) : (L.map f).prod=∏ p∈(s.prodPrimes z).primeFactors,f p := by
    have hL : L.toFinset=(s.prodPrimes z).primeFactors := by ext p; simp [L,mem_descPrimeList_iff]
    rw [←List.prod_toFinset f (descPrimeList_nodup _),hL]
  have hV : (L.map (fun p => 1-g p)).prod=s.eulerProd z := by
    rw [show L.map (fun p => 1-g p)=L.map (fun p => 1-s.density p) from
      List.map_congr_left (fun p h => by rw [hg p h]),hprod]; rfl
  have hD : SieveDimensionBound L z g A κ := by
    intro w hw hwz
    rw [sieveWindowFactor,show L.map (fun p : ℕ => if w≤(p:ℝ) then (1-g p)⁻¹ else 1)=
      L.map (fun p : ℕ => if w≤(p:ℝ) then (1-s.density p)⁻¹ else 1) from
      List.map_congr_left (fun p h => by rw [hg p h]),hprod,←Finset.prod_filter]
    exact hd w hw hwz
  have hr : rosserRemainder s.density C b L=rosserRemainder g C b L := by
    unfold rosserRemainder; congr 1
    apply List.map_congr_left
    intro e he
    obtain ⟨h₁,h₂,_⟩ := rosserFirstFailures_spec he
    change (e.1.map s.density).prod*(e.2.map (fun p => 1-s.density p)).prod=
      (e.1.map g).prod*(e.2.map (fun p => 1-g p)).prod
    rw [show e.1.map g=e.1.map s.density from List.map_congr_left (fun p h => hg p (h₁.subset h)),
      show e.2.map (fun p => 1-g p)=e.2.map (fun p => 1-s.density p) from
      List.map_congr_left (fun p h => by rw [hg p (h₂.subset h)])]
  have h := h₀ hu hz L g b (descPrimeList_pairwise_gt _) hp (fun p h => hpz p (mem_descPrimeList_iff.mp h))
    (fun _ => le_max_left ..) (fun p h => (hg p h).trans_lt (s.density_lt_one_of_prime (hp p h))) hD
  rw [hV] at h
  exact hr.le.trans h

/-- The upper and lower Rosser model sums approximate the Euler product with
relative error at most 2 A exp(−u log(u)/2), uniformly over all sieve data. -/
theorem betaSieve_fundamental_main_terms {A κ : ℝ} (hA : 1≤A) (hκ : 0≤κ) :
    ∃ u₀ : ℝ, ∀ {u z : ℝ}, u₀≤u → 2≤z → ∀ (s : SieveData),
      (∀p∈(s.prodPrimes z).primeFactors,(p:ℝ)≤z) → s.hasDimensionAt z A κ →
      let V := s.eulerProd z
      let E := 2*A*V*exp (-(u/2)*log u)
      (∑d∈(s.prodPrimes z).divisors, betaSieveUpper (1+u/3) (z^u) d*s.density d)≤V+E ∧
      V-E≤(∑d∈(s.prodPrimes z).divisors, betaSieveLower (1+u/3) (z^u) d*s.density d) := by
  obtain ⟨u₀,h₀⟩ := model_bound hA hκ
  refine ⟨u₀,?_⟩
  intro u z hu hz s hpz hd
  obtain ⟨hplus,hminus⟩ := betaSieve_main_terms s z (1+u/3) (z^u)
  dsimp only
  rw [hplus,hminus]
  exact ⟨add_le_add_right (h₀ hu hz s true hpz hd) _,sub_le_sub_left (h₀ hu hz s false hpz hd) _⟩

/-- The fundamental lemma of the sieve for a finite arithmetic set.
The unconditional combinatorial error only involves divisors below z^u. -/
theorem siftedCount_fundamental_lemma {A κ : ℝ} (hA : 1≤A) (hκ : 0≤κ) :
    ∃ u₀ : ℝ, ∀ {u z : ℝ}, u₀≤u → 2≤z → ∀ (s : SieveData), 0≤s.X →
      (∀p∈(s.prodPrimes z).primeFactors,(p:ℝ)≤z) → s.hasDimensionAt z A κ →
      |(siftedCount s.A s.prodPrimes z : ℝ)-s.X*s.eulerProd z| ≤
        s.X*(2*A*s.eulerProd z*exp (-(u/2)*log u))+
          ∑d∈(s.prodPrimes z).divisors.filter (fun d : ℕ => (d:ℝ)<z^u), |s.rem d| := by
  obtain ⟨u₀,h₀⟩ := betaSieve_fundamental_main_terms hA hκ
  refine ⟨max 12 u₀,?_⟩
  intro u z hu hz s hX hpz hd
  have hu₁ := (max_le_iff.mp hu).1
  have hu₂ := (max_le_iff.mp hu).2
  let β := 1+u/3
  let y := z^u
  have hβ : 1≤β := by dsimp [β]; linarith
  have hzy : z<y := by
    calc z = z^(1:ℝ) := (Real.rpow_one z).symm
         _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have hy : 1<y := by linarith
  have hp' (p : ℕ) (h : p∈(s.prodPrimes z).primeFactors) : (p:ℝ)<y := (hpz p h).trans_lt hzy
  let P := s.prodPrimes z
  have hsum (F : ℕ → ℝ) (hF : ∀d∈P.divisors, y≤d → F d=0) :
      (∑d∈P.divisors.filter (fun d : ℕ => (d:ℝ)<y), F d*s.density d)=
      ∑d∈P.divisors,F d*s.density d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases h : (d:ℝ)<y <;> simp [h]
    exact Or.inl (hF _ hd (not_lt.mp h))
  have hup := betaSieve_upper_bound s z hβ hy
  have hlo := betaSieve_lower_bound s z hβ hy hp'
  rw [hsum _ (fun d _ h => betaSieveUpper_eq_zero_of_le hβ hy h)] at hup
  rw [hsum _ (fun d hd h => betaSieveLower_eq_zero_of_le hβ hy (fun p hp =>
    hp' _ (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (s.prodPrimes_ne_zero z) hp)) h)] at hlo
  obtain ⟨hup',hlo'⟩ := h₀ hu₂ hz s hpz hd
  have h1 := mul_le_mul_of_nonneg_left hup' hX
  have h2 := mul_le_mul_of_nonneg_left hlo' hX
  dsimp only [P,y,β] at hup hlo h1 h2
  rw [abs_le]
  constructor <;> linarith only [hup,hlo,h1,h2]

end AnalyticNumberTheory.SieveMethods
