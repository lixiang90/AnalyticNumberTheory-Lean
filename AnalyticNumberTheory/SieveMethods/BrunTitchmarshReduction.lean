import AnalyticNumberTheory.SieveMethods.SelbergMonotonicity
import AnalyticNumberTheory.SieveMethods.CombinatorialSieve

/-! # Translation from prime progressions to rough intervals

Small primes contribute at most π(z). Translating the remaining progression
indices and averaging over units accounts for the factor q/φ(q).
-/
open Real Finset
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

/-- Transfer any uniform estimate for rough numbers in real intervals to a
prime-progression bound with the exact small-prime error π(z). -/
theorem brun_titchmarsh_of_rough_interval {x y : ℝ} {q a : ℕ} (hx : 0≤x) (hy : 0<y)
    (hq : 1≤q) (z M : ℝ) (H : ∀ t : ℝ, 0≤t → ∀ T : Finset ℕ,
      T⊆Ioc ⌊t⌋₊ ⌊t+y/q⌋₊ → (∀ m∈T, ∀ d : ℕ, 1<d → (d:ℝ)≤z → ¬d∣m) → (T.card:ℝ)≤M) :
    (piAP (x+y) q a-piAP x q a)*(q.totient:ℝ) ≤ q*(M+(primeFinset z).card) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let C := (Ioc ⌊x⌋₊ ⌊x+y⌋₊).filter (fun n : ℕ => n.Prime ∧ n ≡ a [MOD q])
  let Sm := C.filter (fun n : ℕ => (n:ℝ)≤z)
  let Lg := C.filter (fun n : ℕ => z<(n:ℝ))
  let b := a%q
  let A := Lg.image (fun n => n/q)
  let w := (x-(b:ℝ))/q
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hbr : (b:ℝ)<q := by exact_mod_cast Nat.mod_lt a hq
  have hrec (n : ℕ) (hn : n∈Lg) : q*(n/q)+b=n := by
    have h := (mem_filter.mp (mem_filter.mp hn).1).2.2
    rw [show b=n%q from h.symm,add_comm,Nat.mod_add_div]
  have hcard : A.card=Lg.card := by
    dsimp only [A]
    apply card_image_of_injOn
    intro m hm n hn h
    simpa only [hrec m hm,hrec n hn] using congrArg (fun k => q*k+b) h
  have hsplit : C.card=Sm.card+Lg.card := by
    simpa only [Sm,Lg,not_le] using (C.card_filter_add_card_filter_not (fun n : ℕ => (n:ℝ)≤z)).symm
  have hsm : Sm.card≤(primeFinset z).card := card_le_card (fun n hn =>
    mem_primeFinset_iff.mpr ⟨(mem_filter.mp (mem_filter.mp hn).1).2.1,(mem_filter.mp hn).2⟩)
  have hI (k : ℕ) (hk : k∈A) : w<k ∧ (k:ℝ)≤w+y/q := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hn).1).1
    have hr : (q:ℝ)*(↑(n/q):ℝ)+b=n := by exact_mod_cast hrec n hn
    have hnl := (Nat.floor_lt hx).mp hl
    have hnu := (Nat.le_floor_iff (by linarith : 0≤x+y)).mp hu
    dsimp [w]
    constructor
    · rw [div_lt_iff₀ hqr]; linarith
    · rw [←add_div,le_div_iff₀ hqr]; linarith
  have hp (k : ℕ) (hk : k∈A) : (q*k+b).Prime ∧ z<(q*k+b:ℕ) := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    rw [hrec n hn]
    exact ⟨(mem_filter.mp (mem_filter.mp hn).1).2.1,(mem_filter.mp hn).2⟩
  obtain ⟨r,T,hr,hs,hc,hrough⟩ := selberg_progression_to_rough A z hp
  have hw : -1≤w := by dsimp [w]; rw [le_div_iff₀ hqr]; linarith
  have hwr : 0≤w+r := by linarith [show (1:ℝ)≤r by exact_mod_cast hr]
  have hsub : T⊆Ioc ⌊w+r⌋₊ ⌊w+r+y/q⌋₊ := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := mem_image.mp (hs hn)
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt hwr).mpr
      push_cast; linarith [(hI k hk).1]
    · apply Nat.le_floor
      push_cast; linarith [(hI k hk).2]
  have HB := H _ hwr T hsub hrough
  rw [hcard] at hc
  have HL : (Lg.card:ℝ)*q.totient ≤ (q:ℝ)*T.card := by exact_mod_cast hc
  have Hs := mul_le_mul (show (Sm.card:ℝ)≤(primeFinset z).card by exact_mod_cast hsm)
    (show (q.totient:ℝ)≤q by exact_mod_cast Nat.totient_le q) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [piAP_sub_eq_card_interval q a hy.le]
  change (C.card:ℝ)*q.totient≤_
  rw [hsplit,Nat.cast_add]
  linarith only [HL.trans (mul_le_mul_of_nonneg_left HB hqr.le),Hs]

/-- Natural block version of the translation principle. The block length
is the ceiling of the real ratio y/q. -/
theorem brun_titchmarsh_of_rough_block {x y : ℝ} {q a : ℕ} (hx : 0≤x) (hy : 0<y)
    (hq : 1≤q) (z M : ℝ) (H : ∀ (n : ℕ) (T : Finset ℕ),
      T⊆Ioc n (n+⌈y/(q:ℝ)⌉₊) → (∀ m∈T, ∀ d : ℕ, 1<d → (d:ℝ)≤z → ¬d∣m) → (T.card:ℝ)≤M) :
    (piAP (x+y) q a-piAP x q a)*(q.totient:ℝ) ≤ q*(M+(primeFinset z).card) := by
  apply brun_titchmarsh_of_rough_interval hx hy hq z M
  intro t ht T hI hr
  apply H ⌊t⌋₊ T _ hr
  intro m hm
  obtain ⟨hl,hu⟩ := mem_Ioc.mp (hI hm)
  apply mem_Ioc.mpr ⟨hl,hu.trans ?_⟩
  have h := Nat.floor_mono (a:=t+y/(q:ℝ)) (show t+y/(q:ℝ) ≤ t+(⌈y/(q:ℝ)⌉₊:ℕ) by
    linarith only [Nat.le_ceil (y/(q:ℝ))])
  simpa [Nat.floor_add_natCast ht] using h

end AnalyticNumberTheory.SieveMethods
