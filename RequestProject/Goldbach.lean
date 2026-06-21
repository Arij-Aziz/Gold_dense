import Mathlib
import RequestProject.Blueprint

/-!
# The Goldbach reduction (Section 5 of the blueprint)

This file formalises the **reduction** of the (binary) Goldbach conjecture to the
"covering" statement of the blueprint, in the precise form
`HmissZero : ∀ i ≥ 1, miss i = 0` — i.e. *every* even integer in the interval
`[P i + 4, P i + 2·P(i+1) − 5]` is a sum `a + b` with `a ∈ A i`, `b ∈ B i`.

## What is proved here (unconditionally, no `sorry`, no extra axioms)

* `goldbach_of_interval` — if `miss i = 0` (for `i ≥ 1`) and an *even* `N` lies strictly
  between the consecutive "even anchors" `2·P i` and `2·P (i+1)`, then `N` is a sum of two
  primes.
* `exists_consecutive_primes` — every `M ≥ 6` that is **not** prime lies strictly between two
  consecutive primes `P i < M < P (i+1)` with `i ≥ 1`.
* `goldbach_of_cover` — **the reduction**: from `HmissZero` it follows that *every* even
  `N ≥ 4` is a sum of two primes.  The argument is the elementary tiling of the even numbers
  by the intervals `(2·P i, 2·P (i+1))` together with the trivial representation
  `2p = p + p` at the anchors, plus a finite check for the few small cases.

## The genuinely open step

`HmissZero` is *exactly* the content of binary Goldbach for the relevant ranges, so it is
**not** assumed as an axiom; it appears only as an explicit hypothesis of `goldbach_of_cover`.
The blueprint proposes deriving it from the Hardy–Littlewood circle method together with the
spectral large sieve (Deshouillers–Iwaniec 1982), the Kuznetsov trace formula and the
Siegel–Walfisz theorem.  None of that machinery is available in Mathlib, and binary Goldbach
is an open problem; the corresponding derivation `cover_of_circle_method` is therefore left as
`sorry` and clearly marked as the single open step.  Every other result in this file is fully
proved.
-/

open Filter Topology

namespace BlueprintH

/-! ### Small values of `P` -/

lemma P_zero : P 0 = 2 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rw [hc] at h
  exact h

/-- For `i ≥ 1`, the prime `P i` is at least `3` (it is an odd prime). -/
lemma three_le_P {i : ℕ} (hi : 1 ≤ i) : 3 ≤ P i := by
  have h2 : P 0 < P i := P_strictMono (lt_of_lt_of_le Nat.zero_lt_one hi)
  rw [P_zero] at h2
  omega

/-! ### `miss i = 0` collapses `evenInterval` onto `C` -/

/-- If `miss i = 0`, then every even integer of the interval is realised as a sum: the
inclusion `C i ⊆ evenInterval i` becomes an equality. -/
lemma evenInterval_eq_C_of_miss_zero {i : ℕ} (h : miss i = 0) :
    evenInterval i = C i := by
  have hsub := C_subset_evenInterval i
  have hle : (evenInterval i).card ≤ (C i).card := by
    have hcle := C_card_le_evenInterval i
    have : (evenInterval i).card - (C i).card = 0 := h
    omega
  exact (Finset.eq_of_subset_of_card_le hsub hle).symm

/-- Membership criterion for `evenInterval` (just unfolding the definition). -/
lemma mem_evenInterval_iff {i n : ℕ} :
    n ∈ evenInterval i ↔ (P i + 4 ≤ n ∧ n ≤ P i + 2 * P (i + 1) - 5) ∧ Even n := by
  simp [evenInterval, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-! ### From an interval hit to a Goldbach representation -/

/-- If `miss i = 0` (with `i ≥ 1`) and `N` is even with `2·P i < N < 2·P (i+1)`, then `N` is a
sum of two primes. -/
lemma goldbach_of_interval {i N : ℕ} (hi : 1 ≤ i) (h : miss i = 0)
    (hlo : 2 * P i < N) (hhi : N < 2 * P (i + 1)) (hN : Even N) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  have hP3 : 3 ≤ P i := three_le_P hi
  have hPsucc : P i < P (i + 1) := P_lt_succ i
  -- `N` lies in `evenInterval i`.
  have hmemEI : N ∈ evenInterval i := by
    rw [mem_evenInterval_iff]
    refine ⟨⟨?_, ?_⟩, hN⟩
    · -- `P i + 4 ≤ N`
      obtain ⟨k, hk⟩ := hN
      omega
    · -- `N ≤ P i + 2 * P (i+1) - 5`
      obtain ⟨k, hk⟩ := hN
      have : 5 ≤ 2 * P (i + 1) := by omega
      omega
  -- hence `N ∈ C i`
  have hmemC : N ∈ C i := by
    rw [evenInterval_eq_C_of_miss_zero h] at hmemEI; exact hmemEI
  rw [mem_C] at hmemC
  obtain ⟨a, ha, b, hb, hab⟩ := hmemC
  rw [mem_A] at ha; rw [mem_B] at hb
  exact ⟨a, b, ha.2, hb.2, hab⟩

/-! ### Tiling the even numbers by consecutive primes -/

/-- Every `M ≥ 6` that is not prime lies strictly between two consecutive primes
`P i < M < P (i+1)` with `i ≥ 1`. -/
lemma exists_consecutive_primes {M : ℕ} (hM : 6 ≤ M) (hMp : ¬ Nat.Prime M) :
    ∃ i : ℕ, 1 ≤ i ∧ P i < M ∧ M < P (i + 1) := by
  classical
  -- the set of primes below `M` is a nonempty finite set; take its greatest element
  set S : Finset ℕ := (Finset.range M).filter (fun n => Nat.Prime n) with hS
  have h5S : 5 ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by norm_num⟩
  have hSne : S.Nonempty := ⟨5, h5S⟩
  obtain ⟨pmax, hpmaxS, hpmax_max⟩ := S.exists_max_image id hSne
  rw [hS] at hpmaxS
  simp only [Finset.mem_filter, Finset.mem_range] at hpmaxS
  obtain ⟨hpmax_lt, hpmax_prime⟩ := hpmaxS
  -- `pmax = P i` where `i = count of primes below pmax`
  set i := Nat.count Nat.Prime pmax with hi_def
  have hPi : P i = pmax := by
    rw [hi_def]; simpa [P] using Nat.nth_count (p := Nat.Prime) hpmax_prime
  -- `5 ≤ pmax`, so `i ≥ 1` (actually `i ≥ 2`)
  have h5le : (5 : ℕ) ≤ pmax := by
    have := hpmax_max 5 h5S; simpa using this
  have hi1 : 1 ≤ i := by
    -- `count Nat.Prime pmax ≥ count Nat.Prime 5 = 2`
    have hmono : Nat.count Nat.Prime 5 ≤ Nat.count Nat.Prime pmax :=
      Nat.count_monotone _ h5le
    have : Nat.count Nat.Prime 5 = 2 := by decide
    rw [hi_def]; omega
  -- `P (i+1) > M`: the next prime after `pmax` is `≥ M`, and `≠ M` since `M` not prime
  have hPi_lt_M : P i < M := by rw [hPi]; exact hpmax_lt
  have hM_le_Pnext : M ≤ P (i + 1) := by
    by_contra hcon
    push_neg at hcon
    -- `P (i+1)` is a prime `< M`, hence in `S`, hence `≤ pmax = P i < P (i+1)`, contradiction
    have hmem : P (i + 1) ∈ S := by
      rw [hS]; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hcon, P_prime (i + 1)⟩
    have := hpmax_max (P (i + 1)) hmem
    simp only [id] at this
    have : P (i + 1) ≤ pmax := this
    rw [← hPi] at this
    exact absurd this (not_le.mpr (P_lt_succ i))
  have hMne : M ≠ P (i + 1) := fun h => hMp (h ▸ P_prime (i + 1))
  exact ⟨i, hi1, hPi_lt_M, lt_of_le_of_ne hM_le_Pnext (Ne.symm (fun h => hMne h.symm))⟩

/-! ### The reduction -/

/-- **The covering hypothesis** (`HmissZero`): for every `i ≥ 1`, every even integer in the
interval `[P i + 4, P i + 2·P(i+1) − 5]` is a sum `a + b` with `a ∈ A i`, `b ∈ B i`.

This is the genuinely open input — it is the content of binary Goldbach in the relevant
ranges — and is therefore taken as a hypothesis, **not** an axiom. -/
abbrev HmissZero : Prop := ∀ i : ℕ, 1 ≤ i → miss i = 0

/-- **The Goldbach reduction.**  From the covering hypothesis `HmissZero`, every even
`N ≥ 4` is a sum of two primes.

Proof outline.  Write `N = 2 * M` with `M ≥ 2`.
* If `M` is prime, then `N = M + M` is a sum of two primes.
* Otherwise `M` is not prime; the small case `M = 4` (`N = 8 = 3 + 5`) is checked directly,
  and for `M ≥ 6` we use `exists_consecutive_primes` to find `i ≥ 1` with
  `P i < M < P (i+1)`, i.e. `2·P i < N < 2·P (i+1)`, and then `goldbach_of_interval`. -/
theorem goldbach_of_cover (hcov : HmissZero) :
    ∀ N : ℕ, 4 ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  intro N hN4 hNeven
  obtain ⟨M, hM⟩ := hNeven
  -- `N = 2 * M`
  have hN2M : N = 2 * M := by omega
  have hM2 : 2 ≤ M := by omega
  by_cases hMp : Nat.Prime M
  · -- `N = M + M`
    exact ⟨M, M, hMp, hMp, by omega⟩
  · -- `M` not prime, so `M ≥ 4`
    have hM4 : 4 ≤ M := by
      rcases Nat.lt_or_ge M 4 with h | h
      · interval_cases M <;> simp_all (config := {decide := true})
      · exact h
    rcases Nat.lt_or_ge M 6 with hlt | hge
    · -- `M ∈ {4, 5}`; `5` is prime so `M = 4`, `N = 8 = 3 + 5`
      interval_cases M
      · exact ⟨3, 5, by norm_num, by norm_num, by omega⟩
      · exact absurd (by norm_num : Nat.Prime 5) hMp
    · -- `M ≥ 6`
      obtain ⟨i, hi1, hPiM, hMPnext⟩ := exists_consecutive_primes hge hMp
      have hlo : 2 * P i < N := by omega
      have hhi : N < 2 * P (i + 1) := by omega
      exact goldbach_of_interval hi1 (hcov i hi1) hlo hhi ⟨M, hM⟩

/-! ### The open step (circle method) -/

/-- **The single open step.**  The blueprint derives the covering hypothesis `HmissZero`
from the Hardy–Littlewood circle method (major-arc evaluation à la Vaughan, with the
singular-series lower bound), the spectral large sieve of Deshouillers–Iwaniec (Invent.
Math. **70**, 1982), the Kuznetsov trace formula and the Siegel–Walfisz theorem, together
with Dusart's explicit prime-gap bound (`HDusart`).

None of this analytic machinery is available in Mathlib, and binary Goldbach is an open
problem; this derivation is therefore left as `sorry`.  It is the *only* unproved step: every
other declaration in this file is fully proved, and `goldbach_of_cover` reduces Goldbach to
exactly this statement. -/
theorem cover_of_circle_method : HmissZero := by
  sorry

/-- **Binary Goldbach**, modulo the single open circle-method step `cover_of_circle_method`:
every even `N ≥ 4` is a sum of two primes. -/
theorem goldbach (N : ℕ) (hN4 : 4 ≤ N) (hNeven : Even N) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N :=
  goldbach_of_cover cover_of_circle_method N hN4 hNeven

end BlueprintH
