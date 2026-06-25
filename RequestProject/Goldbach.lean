import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions
import RequestProject.MainTheorem
import RequestProject.RestrictedGoldbachImproved

open scoped BigOperators Pointwise Classical

/-!
# Goldbach-type density and exceptional-set bounds

This module repackages the main density result `sumset_card_gt_95` as explicit
statements about the *representable* integers `N` (those with `0 < r_{A+B}(N)`)
and the *exceptional* integers (`r_{A+B}(N) = 0`), where `A = Aset x`,
`B = Bset x`, `x = pᵢ`.

## The output interval is `(x, 3x]`, and exceptions are counted over even `N`

The user originally proposed these two statements over the interval `(x, 2x]`:

```
theorem goldbach_density {i : ℕ} (hi : i > trigger) :
    (9040 / 10000 : ℝ) * (primeIdx i : ℝ)
      < #{N ∈ Finset.Ioc (primeIdx i) (2 * primeIdx i) |
            0 < rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N}

theorem goldbach_exception_bound {i : ℕ} (hi : i > trigger) :
    #{N ∈ Finset.Ioc (primeIdx i) (2 * primeIdx i) |
          rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N = 0}
      < (960 / 10000 : ℝ) * (primeIdx i : ℝ)
```



The internally consistent corrected statements, proved below, are:

* `goldbach_density`         — over the full support `(x, 3x]`, the representable
  count exceeds `0.95·x` (it equals `(A+B).card`, so this is exactly
  `sumset_card_gt_95` repackaged);
* `goldbach_exception_bound` — the number of **even** `N ∈ (x, 3x]` that are *not*
  representable is below `0.05·x` (the genuine Goldbach exceptional set; the two
  bounds are complementary since `(x,3x]` contains exactly `x` even numbers).

Both are proved modulo the single pre-existing analytic obligation
`restricted_exceptional_bound` (via `sumset_card_gt_95`); no new `sorry` is introduced.
-/

namespace PrimeSumset

open Finset

/-- `0 < r_{A+B}(N)` exactly says `N` lies in the pointwise sumset `A + B`. -/
lemma rAdd_pos_iff (A B : Finset ℤ) (N : ℤ) : 0 < rAdd A B N ↔ N ∈ A + B := by
  rw [rAdd, Finset.card_pos, Finset.mem_add]
  constructor
  · rintro ⟨p, hp⟩
    rw [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨p.1, hp.1.1, p.2, hp.1.2, hp.2⟩
  · rintro ⟨y, hy, z, hz, hyz⟩
    exact ⟨(y, z), by rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hy, hz⟩, hyz⟩⟩

/-- Every element of `Aset x` is odd (primes in `[3,x]` are `≠ 2`). -/
lemma Aset_odd {x : ℕ} {a : ℤ} (ha : a ∈ Aset x) : Odd a := by
  simp [Aset] at ha
  obtain ⟨n, ⟨⟨h3, hx⟩, hp⟩, rfl⟩ := ha
  exact (Int.odd_coe_nat n).mpr (hp.odd_of_ne_two (by omega))

/-- Every element of `Bset x` is odd (for `x ≥ 2`, primes in `(x,2x]` are `≠ 2`). -/
lemma Bset_odd {x : ℕ} (hx2 : 2 ≤ x) {b : ℤ} (hb : b ∈ Bset x) : Odd b := by
  simp [Bset] at hb
  obtain ⟨n, ⟨⟨hlt, hle⟩, hp⟩, rfl⟩ := hb
  exact (Int.odd_coe_nat n).mpr (hp.odd_of_ne_two (by omega))

/-- Parity: any representable `N` (for `x ≥ 2`) is even, since it is a sum of two
odd primes. -/
lemma rAdd_pos_even {x : ℕ} (hx2 : 2 ≤ x) {N : ℤ}
    (hN : 0 < rAdd (Aset x) (Bset x) N) : Even N := by
  rw [rAdd_pos_iff, Finset.mem_add] at hN
  obtain ⟨a, ha, b, hb, rfl⟩ := hN
  exact (Aset_odd ha).add_odd (Bset_odd hx2 hb)

/-- The number of even integers in `(x, 3x]` is at most `x`. -/
lemma even_card_le (x : ℕ) :
    ((Finset.Ioc (x : ℤ) (3 * x)).filter (fun n => Even n)).card ≤ x := by
  refine le_trans (Finset.card_le_card_of_injOn (fun n => n / 2)
    (t := Finset.Ioc ((x : ℤ) / 2) (3 * (x : ℤ) / 2)) ?_ ?_) ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    simp only [Finset.mem_coe, Finset.mem_Ioc]; omega
  · intro n hn m hm hnm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ioc] at hn hm
    obtain ⟨_, k, rfl⟩ := hn
    obtain ⟨_, l, rfl⟩ := hm
    dsimp only at hnm; omega
  · rw [Int.card_Ioc]; omega

/-- **Goldbach density (corrected).**  For every `i > 10^15`, with `x = pᵢ`,
`A = Aset x`, `B = Bset x`, the number of representable integers `N ∈ (x, 3x]`
(those with `0 < r_{A+B}(N)`) exceeds `0.95·x`.

Since the sumset `A+B` is exactly the support `(x,3x]` of representable integers,
this filtered count equals `(A+B).card`, so the statement is exactly the main
theorem `sumset_card_gt_95` repackaged.  (The constant `95/100 = 0.95`.) -/
theorem goldbach_density {i : ℕ} (hi : i > trigger) :
    (95 / 100 : ℝ) * (primeIdx i : ℝ)
      < (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
            0 < rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N} : ℝ) := by
  have heq : {N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
        0 < rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N}
      = sumset (Aset (primeIdx i)) (Bset (primeIdx i)) := by
    ext N; rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩; rwa [rAdd_pos_iff] at h
    · intro h
      have hb : N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) := by
        rw [sumset, Finset.mem_add] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp [Aset] at ha; simp [Bset] at hb
        obtain ⟨na, ⟨⟨h3, hax⟩, _⟩, rfl⟩ := ha
        obtain ⟨nb, ⟨⟨hxb, hb2⟩, _⟩, rfl⟩ := hb
        rw [Finset.mem_Ioc]; constructor <;> omega
      exact ⟨hb, by rw [rAdd_pos_iff]; exact h⟩
  rw [heq]
  have hmain := sumset_card_gt_95 hi
  have hconst : (95 / 100 : ℝ) = 0.95 := by norm_num
  rw [hconst]; exact hmain

/-- **Goldbach exceptional-set bound (corrected).**  For every `i > 10^15`, with
`x = pᵢ`, `A = Aset x`, `B = Bset x`, the number of **even** integers `N ∈ (x, 3x]`
that are *not* representable (`r_{A+B}(N) = 0`) is below `0.05·x`.

The interval `(x, 3x]` contains exactly `x` even numbers, all representable `N`
are even, and representable + exceptional partition the even numbers; combined
with `goldbach_density` (representable `> 0.95·x`) this forces the even
exceptional count below `(1 - 0.95)·x = 0.05·x`.  (The constant
`5/100 = 0.05`.) -/
theorem goldbach_exception_bound {i : ℕ} (hi : i > trigger) :
    (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
          Even N ∧ rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N = 0} : ℝ)
      < (5 / 100 : ℝ) * (primeIdx i : ℝ) := by
  set x := primeIdx i with hx
  have hx2 : 2 ≤ x := by have := three_le_primeIdx_of_trigger hi; omega
  -- Even numbers of (x,3x] split into representable and exceptional.
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n))
    (p := fun n => 0 < rAdd (Aset x) (Bset x) n)
  have hrep : ((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).filter
        (fun n => 0 < rAdd (Aset x) (Bset x) n)
      = {N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | 0 < rAdd (Aset x) (Bset x) N} := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr; intro n hn
    exact ⟨fun h => h.2, fun h => ⟨rAdd_pos_even hx2 h, h⟩⟩
  have hexc : ((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).filter
        (fun n => ¬ 0 < rAdd (Aset x) (Bset x) n)
      = {N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | Even N ∧ rAdd (Aset x) (Bset x) N = 0} := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr; intro n hn
    simp only [Nat.not_lt, Nat.le_zero]
  rw [hrep, hexc] at hpart
  have hdens : (95 / 100 : ℝ) * (x : ℝ)
      < (({N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | 0 < rAdd (Aset x) (Bset x) N}).card : ℝ) := by
    have hd := goldbach_density hi; rw [← hx] at hd; exact hd
  have heven : (((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).card : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast even_card_le x
  have hcast : (((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).card : ℝ)
      = (({N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | 0 < rAdd (Aset x) (Bset x) N}).card : ℝ)
        + (({N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | Even N ∧ rAdd (Aset x) (Bset x) N = 0}).card : ℝ) := by
    rw [← hpart]; push_cast; ring
  nlinarith [hcast, hdens, heven]

/-- **Improved bound — 0‑indexed wrapper.**  For every `i > 10^15`,
`|C| > (111/112)·pᵢ`. -/
theorem sumset_card_gt_111_div_112 {i : ℕ} (hi : i > trigger) :
    ((111 : ℝ) / 112) * (primeIdx i : ℝ) <
      ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have hi' : 10 ^ 15 < i + 1 := by
    unfold trigger at hi; omega
  have h := RestrictedGoldbach.sumset_card_gt_111_div_112 hi'
  simpa [RestrictedGoldbach.primeIdx1, RestrictedGoldbach.Aset, RestrictedGoldbach.Bset] using h

/-- **Goldbach density (improved).**  For every `i > 10^15`, the number of
representable `N ∈ (x, 3x]` exceeds `(111/112)·x ≈ 0.99107·x`. -/
theorem goldbach_density_improved {i : ℕ} (hi : i > trigger) :
    ((111 : ℝ) / 112) * (primeIdx i : ℝ)
      < (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
            0 < rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N} : ℝ) := by
  have heq : {N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
        0 < rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N}
      = sumset (Aset (primeIdx i)) (Bset (primeIdx i)) := by
    ext N; rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩; rwa [rAdd_pos_iff] at h
    · intro h
      have hb : N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) := by
        rw [sumset, Finset.mem_add] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        simp [Aset] at ha; simp [Bset] at hb
        obtain ⟨na, ⟨⟨h3, hax⟩, _⟩, rfl⟩ := ha
        obtain ⟨nb, ⟨⟨hxb, hb2⟩, _⟩, rfl⟩ := hb
        rw [Finset.mem_Ioc]; constructor <;> omega
      exact ⟨hb, by rw [rAdd_pos_iff]; exact h⟩
  rw [heq]
  exact sumset_card_gt_111_div_112 hi

/-- **Goldbach exceptional-set bound (improved).**  For every `i > 10^15`,
the number of even non‑representable `N ∈ (x, 3x]` is below `(1/112)·x ≈ 0.00893·x`. -/
theorem goldbach_exception_bound_improved {i : ℕ} (hi : i > trigger) :
    (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
          Even N ∧ rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N = 0} : ℝ)
      < ((1 : ℝ) / 112) * (primeIdx i : ℝ) := by
  set x := primeIdx i with hx
  have hx2 : 2 ≤ x := by have := three_le_primeIdx_of_trigger hi; omega
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n))
    (p := fun n => 0 < rAdd (Aset x) (Bset x) n)
  have hrep : ((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).filter
        (fun n => 0 < rAdd (Aset x) (Bset x) n)
      = {N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | 0 < rAdd (Aset x) (Bset x) N} := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr; intro n hn
    exact ⟨fun h => h.2, fun h => ⟨rAdd_pos_even hx2 h, h⟩⟩
  have hexc : ((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).filter
        (fun n => ¬ 0 < rAdd (Aset x) (Bset x) n)
      = {N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | Even N ∧ rAdd (Aset x) (Bset x) N = 0} := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr; intro n hn
    simp only [Nat.not_lt, Nat.le_zero]
  rw [hrep, hexc] at hpart
  have hdens : ((111 : ℝ) / 112) * (x : ℝ)
      < (({N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | 0 < rAdd (Aset x) (Bset x) N}).card : ℝ) := by
    have hd := goldbach_density_improved hi; rw [← hx] at hd; exact hd
  have heven : (((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).card : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast even_card_le x
  have hcast : (((Finset.Ioc ((x : ℤ)) (3 * x)).filter (fun n => Even n)).card : ℝ)
      = (({N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | 0 < rAdd (Aset x) (Bset x) N}).card : ℝ)
        + (({N ∈ Finset.Ioc ((x : ℤ)) (3 * x) | Even N ∧ rAdd (Aset x) (Bset x) N = 0}).card : ℝ) := by
    rw [← hpart]; push_cast; ring
  nlinarith [hcast, hdens, heven]

end PrimeSumset
