import RequestProject.AdditiveEnergy

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# Module 1 — `PrimeSumset.Definitions`

Definitions of the prime sumset problem (blueprint §2 and Module 1):

* `primeIdx i` — the `i`-th prime `p_i` (using `Nat.nth Nat.Prime`).
* `Aset x`     — `A = {p prime : 3 ≤ p ≤ x}` as a `Finset ℤ`.
* `Bset x`     — `B = {p prime : x < p ≤ 2x}` as a `Finset ℤ`.
* The trigger threshold `i > 10^15` and basic positivity / nonemptiness facts.

The sumset `C = A + B`, mass `M = |A|·|B|`, representation functions and the
additive energy `E` are the *general* notions developed in
`RequestProject.AdditiveEnergy` (`sumset`, `mass`, `rAdd`, `rSub`, `energy`),
applied to `Aset x` and `Bset x`.
-/

namespace PrimeSumset

open Finset

/-- The trigger threshold of the blueprint: `i > 10^15`. -/
def trigger : ℕ := 10 ^ 15

/-- The `i`-th prime `p_i` (0-indexed: `primeIdx 0 = 2`, `primeIdx 1 = 3`, …). -/
noncomputable def primeIdx (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- `A = {p prime : 3 ≤ p ≤ x}`, as a finite set of integers. -/
noncomputable def Aset (x : ℕ) : Finset ℤ :=
  (((Finset.Icc 3 x).filter (fun n => Nat.Prime n)).image (fun n => (n : ℤ)))

/-- `B = {p prime : x < p ≤ 2x}`, as a finite set of integers. -/
noncomputable def Bset (x : ℕ) : Finset ℤ :=
  (((Finset.Ioc x (2 * x)).filter (fun n => Nat.Prime n)).image (fun n => (n : ℤ)))

/-- The `i`-th prime is at least `i`. -/
lemma le_primeIdx (i : ℕ) : i ≤ primeIdx i := by
  have hmono : StrictMono (Nat.nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime
  exact hmono.le_apply

/-- Above the trigger, the prime `x = p_i` is at least `3`. -/
lemma three_le_primeIdx_of_trigger {i : ℕ} (hi : i > trigger) : 3 ≤ primeIdx i := by
  have h1 : i ≤ primeIdx i := le_primeIdx i
  have h2 : (3 : ℕ) ≤ i := by
    have : (3 : ℕ) ≤ trigger := by norm_num [trigger]
    omega
  omega

/-
`3` is an element of `A` once `3 ≤ x` (so `A` is nonempty).
-/
lemma three_mem_Aset {x : ℕ} (hx : 3 ≤ x) : (3 : ℤ) ∈ Aset x := by
  -- By definition of `Aset`, we need to show that `3 ∈ Aset x`.
  unfold Aset
  simp
  exact ⟨ 3, ⟨ ⟨ by norm_num, hx ⟩, by norm_num ⟩, by norm_num ⟩

/-- `A` is nonempty once `3 ≤ x`. -/
lemma Aset_nonempty {x : ℕ} (hx : 3 ≤ x) : (Aset x).Nonempty :=
  ⟨3, three_mem_Aset hx⟩

/-
By Bertrand's postulate there is a prime in `(x, 2x]`, so `B` is nonempty.
-/
lemma Bset_nonempty {x : ℕ} (hx : 0 < x) : (Bset x).Nonempty := by
  obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ x < p ∧ p ≤ 2 * x := by
    exact Nat.exists_prime_lt_and_le_two_mul x hx.ne'
  use p
  simp [Bset, hp]

/-
The mass `M = |A|·|B|` is positive once `3 ≤ x` (`A` and `B` are nonempty).
-/
lemma mass_pos {x : ℕ} (hx : 3 ≤ x) : 0 < mass (Aset x) (Bset x) := by
  exact mul_pos ( Finset.card_pos.mpr ( Aset_nonempty hx ) ) ( Finset.card_pos.mpr ( Bset_nonempty ( by linarith ) ) )

end PrimeSumset