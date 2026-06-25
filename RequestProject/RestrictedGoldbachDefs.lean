import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions

/-!
# RestrictedGoldbach — Definitions

Per `sup` blueprint §1.  1‑indexed primes via the existing 0‑indexed `primeIdx`.
**A** = primes in [3, pᵢ],  **B** = primes in (pᵢ, 2pᵢ]
-/

open scoped BigOperators

namespace RestrictedGoldbach

open Finset

/-- The i‑th prime, 1‑indexed: p₁ = 2, p₂ = 3, … -/
noncomputable def primeIdx1 (i : ℕ) : ℕ := PrimeSumset.primeIdx (i - 1)

lemma primeIdx1_pos {i : ℕ} (hi : 2 ≤ i) : 0 < primeIdx1 i := by
  have h_one_le : 1 ≤ i - 1 := by omega
  have hle : i - 1 ≤ PrimeSumset.primeIdx (i - 1) := PrimeSumset.le_primeIdx (i - 1)
  unfold primeIdx1
  omega

/-- A = {p prime : 3 ≤ p ≤ pᵢ} -/
noncomputable def Aset (i : ℕ) : Finset ℤ := PrimeSumset.Aset (primeIdx1 i)

/-- B = {p prime : pᵢ < p ≤ 2pᵢ} -/
noncomputable def Bset (i : ℕ) : Finset ℤ := PrimeSumset.Bset (primeIdx1 i)

/-- Membership lemma: a ∈ Aset i iff a = (n : ℤ) for some n with 3 ≤ n ≤ pᵢ and n prime. -/
lemma mem_Aset_iff {i a : ℕ} : (a : ℤ) ∈ Aset i ↔ 3 ≤ a ∧ a ≤ primeIdx1 i ∧ Nat.Prime a := by
  unfold Aset
  rw [PrimeSumset.Aset]
  simp; tauto

lemma Aset_mem {i a : ℕ} (hlo : 3 ≤ a) (hhi : a ≤ primeIdx1 i) (hp : Nat.Prime a) : (a : ℤ) ∈ Aset i := by
  rw [mem_Aset_iff]; exact ⟨hlo, hhi, hp⟩

/-- Membership lemma: b ∈ Bset i iff b = (n : ℤ) for some n with pᵢ < n ≤ 2pᵢ and n prime. -/
lemma mem_Bset_iff {i b : ℕ} : (b : ℤ) ∈ Bset i ↔ primeIdx1 i < b ∧ b ≤ 2 * primeIdx1 i ∧ Nat.Prime b := by
  unfold Bset
  rw [PrimeSumset.Bset]
  simp; tauto

lemma Bset_mem {i b : ℕ} (hlo : primeIdx1 i < b) (hhi : b ≤ 2 * primeIdx1 i) (hp : Nat.Prime b) : (b : ℤ) ∈ Bset i := by
  rw [mem_Bset_iff]; exact ⟨hlo, hhi, hp⟩

lemma rAdd_pos_iff {i N : ℕ} : 0 < PrimeSumset.rAdd (Aset i) (Bset i) (N : ℤ) ↔ (N : ℤ) ∈ PrimeSumset.sumset (Aset i) (Bset i) := by
  constructor
  · intro hpos
    have h_nonempty : ((Aset i ×ˢ Bset i).filter fun p => p.1 + p.2 = (N : ℤ)).Nonempty :=
      Finset.card_pos.mp hpos
    rcases h_nonempty with ⟨⟨a, b⟩, hp⟩
    rcases Finset.mem_filter.mp hp with ⟨hp_prod, hp_eq⟩
    rcases Finset.mem_product.mp hp_prod with ⟨ha, hb⟩
    apply Finset.mem_add.mpr
    exact ⟨a, ha, b, hb, hp_eq⟩
  · intro hmem
    rcases Finset.mem_add.mp hmem with ⟨a, ha, b, hb, heq⟩
    unfold PrimeSumset.rAdd
    have hcard : ((Aset i ×ˢ Bset i).filter fun p => p.1 + p.2 = (N : ℤ)).Nonempty := by
      refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, heq⟩⟩
    exact Finset.card_pos.mpr hcard

/-- r_{A,B}(N) = #{(a,b) ∈ A×B : a+b = N} -/
noncomputable def restricted_repr (i N : ℕ) : ℕ :=
  PrimeSumset.rAdd (Aset i) (Bset i) (N : ℤ)

/-- E_x = {even N ∈ (x, 3x] : r_{A,B}(N) = 0} -/
noncomputable def ExceptionalSet (i : ℕ) : Finset ℕ :=
  let pi := primeIdx1 i
  filter (fun n : ℕ =>
    n % 2 = 0 ∧ pi < n ∧ n ≤ 3 * pi ∧ restricted_repr i n = 0)
    (Ico (pi + 1) (3 * pi + 1))

end RestrictedGoldbach
