import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# Module 8 — `PrimeSumset.KappaFactory` (Factory 1: per-difference sieve ⇒ explicit `κ₀`)

This module realises **Factory 1** of the κ-Factory blueprint ("Direct
upper-bound sieve on differences", §5.1).  It is the layer *below* the research
ladder: instead of assuming the energy ceiling `E ≤ κ·M²/x` as a black box, we
**derive** it — with an *explicit* constant `κ₀ = 1 + 3c²` — from the more
primitive **per-difference sieve bound**

  `r_{A-A}(h) ≤ c · |A|² / x`   and   `r_{B-B}(h) ≤ c · |B|² / x`   (for `h ≠ 0`),

which is the shape of a Brun / Selberg upper-bound sieve on prime pairs
(unconditional in the literature, with an explicit `c`; e.g. `c` of size a few
units for prime pairs, by Selberg's sieve / Brun–Titchmarsh).  This is exactly
the blueprint's §5.1.1 Step 4 ("a crude uniform bound `|A_h| ≤ c_A·|A|²/x` …
yields `E ≤ c_A c_B · M²/x`"), made fully rigorous including the `h`-range and
the diagonal `h = 0` term.

## What is fully proven here (sorry-free, general combinatorics)

* `rSub_zero`            : `r_{A-A}(0) = |A|`  (the diagonal count).
* `sum_ite_zero_le`      : `∑_{h∈s} (if h=0 then a else b) ≤ a + b·|s|` (`a,b ≥ 0`).
* `energy_le_of_pair_bounds` : the **Factory-1 core** — for arbitrary finite
  `A,B ⊆ ℤ`, per-difference bounds `r_{A-A}(h) ≤ c_A`, `r_{B-B}(h) ≤ c_B`
  (`h ≠ 0`) and a range bound `A - A ⊆ [-D, D]` give

      `E(A,B) ≤ |A|·|B| + (2D+1)·c_A·c_B`.

## The prime instance (Factory-1 output)

`energy_ceiling_of_sieve` turns the citable prime-pair sieve hypotheses (with
explicit constant `c`) and a mass lower bound `x ≤ M` (citable Chebyshev / PNT)
into the explicit energy ceiling

  `E(A,B) ≤ (1 + 3c²) · M² / x`,

hence — via the proven research-ladder reduction — the explicit positive density

  `|C| ≥ x / (1 + 3c²)`   and   `|C| > h·x`  for every `h < 1/(1+3c²)`.

So `κ₀ = 1 + 3c²` and `h₀ = 1/(1+3c²) > 0`: a *first explicit positive
constant*, conditional only on the citable explicit upper-bound sieve
(blueprint Success criterion #2, with the analytic hypothesis cleanly
separated).  Improving `c` (better sieve weights / Brun–Titchmarsh constants)
directly improves `κ₀` and `h₀` — the blueprint's research ladder, §6.
-/

namespace PrimeSumset

open Finset

/-
**Diagonal count.** `r_{A-A}(0) = |A|`: the difference-zero pairs are exactly
the diagonal `{(a,a) : a ∈ A}`.
-/
lemma rSub_zero (A : Finset ℤ) : rSub A 0 = A.card := by
  convert Finset.card_image_of_injective _ ( show Function.Injective ( fun x : ℤ => ( x, x ) ) from fun x y hxy => by injection hxy ) using 2;
  convert congr_arg Finset.card ( show ( A ×ˢ A |> Finset.filter fun p => p.1 - p.2 = 0 ) = Finset.image ( fun x => ( x, x ) ) A from ?_ ) using 1;
  grind

/-
Elementary inequality: for nonnegative `a, b`,
`∑_{h∈s} (if h=0 then a else b) ≤ a + b·|s|`.  (The `h=0` term contributes at
most `a`; every term contributes at most `b` on top of the `0`-term, giving the
crude `a + b·|s|`.)
-/
lemma sum_ite_zero_le {s : Finset ℤ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∑ h ∈ s, (if h = 0 then a else b) ≤ a + b * (s.card : ℝ) := by
  by_cases h : 0 ∈ s <;> simp_all +decide [ mul_comm, Finset.sum_ite ];
  · simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ];
    exact mul_le_mul_of_nonneg_left ( mod_cast Nat.pred_le _ ) hb;
  · simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ]

/-
**Factory-1 core (general additive combinatorics).**

For arbitrary finite `A, B ⊆ ℤ`, suppose:
* `A - A ⊆ [-D, D]` (the difference support is contained in a window of radius `D`);
* `r_{A-A}(h) ≤ c_A` for every `h ≠ 0`;
* `r_{B-B}(h) ≤ c_B` for every `h ≠ 0`;
* `c_A, c_B ≥ 0`.

Then the additive energy satisfies

  `E(A,B) ≤ |A|·|B| + (2D+1)·c_A·c_B`.

This is the rigorous form of the blueprint's §5.1.1 Step 4 uniform bound,
including the diagonal `h = 0` term (`|A|·|B|`) and the `h`-range factor
`(2D+1)`.
-/
lemma energy_le_of_pair_bounds (A B : Finset ℤ) (cA cB : ℝ) (D : ℕ)
    (hAsub : A - A ⊆ Finset.Icc (-(D : ℤ)) (D : ℤ))
    (hA : ∀ h : ℤ, h ≠ 0 → (rSub A h : ℝ) ≤ cA)
    (hB : ∀ h : ℤ, h ≠ 0 → (rSub B h : ℝ) ≤ cB)
    (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    (energy A B : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) + (2 * (D : ℝ) + 1) * (cA * cB) := by
  rw [ PrimeSumset.energy_eq_diff_corr ];
  -- Apply the termwise bound to each term in the sum.
  have h_termwise : ∀ h ∈ A - A, (rSub A h : ℝ) * (rSub B (-h) : ℝ) ≤ (if h = 0 then (A.card : ℝ) * (B.card : ℝ) else cA * cB) := by
    intro h hh; split_ifs <;> simp_all +decide [ rSub_zero ] ;
    exact mul_le_mul ( hA h ‹_› ) ( hB ( -h ) ( neg_ne_zero.mpr ‹_› ) ) ( by positivity ) ( by positivity );
  refine' le_trans _ ( le_trans ( Finset.sum_le_sum h_termwise ) _ );
  · norm_cast;
  · refine' le_trans ( sum_ite_zero_le _ _ ) _;
    · positivity;
    · positivity;
    · have := Finset.card_le_card hAsub; simp_all +decide [ mul_comm ] ;
      exact mul_le_mul_of_nonneg_left ( mod_cast by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ ( D : ℤ ) + 1 + D ) ] ) ( mul_nonneg hcA hcB )

/-
The difference set of `Aset x` lies in the window `[-x, x]`: all elements are
integers in `[3, x]`, so all differences are in `[3-x, x-3] ⊆ [-x, x]`.
-/
lemma Aset_diff_subset (x : ℕ) :
    Aset x - Aset x ⊆ Finset.Icc (-(x : ℤ)) (x : ℤ) := by
  intro y hy; rw [ Finset.mem_sub ] at hy; obtain ⟨ a, ha, b, hb, rfl ⟩ := hy; simp_all +decide [ Aset ] ;
  grind

/-
**Factory-1 prime instance — explicit energy ceiling from a sieve constant.**

Let `i > 10^15`, `x = pᵢ`, `A = {p prime : 3 ≤ p ≤ x}`, `B = {p prime : x < p ≤ 2x}`.
Assume the citable **per-difference sieve bounds** with an explicit constant `c ≥ 0`:

  `r_{A-A}(h) ≤ c·|A|²/x`  and  `r_{B-B}(h) ≤ c·|B|²/x`   for every `h ≠ 0`,

and the citable **mass lower bound** `x ≤ M = |A|·|B|` (Chebyshev / PNT-strength).
Then the additive energy obeys the explicit ceiling

  `E(A,B) ≤ (1 + 3c²) · M² / x`,

i.e. an explicit `κ₀ = 1 + 3c²`.  (The analytic inputs are the hypotheses
`hA`, `hB`, `hmass`; everything else is proven.)
-/
theorem energy_ceiling_of_sieve {i : ℕ} (hi : i > trigger) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ h : ℤ, h ≠ 0 →
        (rSub (Aset (primeIdx i)) h : ℝ)
          ≤ c * ((Aset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ))
    (hB : ∀ h : ℤ, h ≠ 0 →
        (rSub (Bset (primeIdx i)) h : ℝ)
          ≤ c * ((Bset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)
      ≤ (1 + 3 * c ^ 2)
          * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
          / (primeIdx i : ℝ) := by
  -- Apply the energy_le_of_pair_bounds lemma with the given bounds.
  have h_apply : energy (Aset (primeIdx i)) (Bset (primeIdx i)) ≤ (Aset (primeIdx i)).card * (Bset (primeIdx i)).card + (2 * (primeIdx i : ℝ) + 1) * (c * (Aset (primeIdx i)).card ^ 2 / (primeIdx i : ℝ)) * (c * (Bset (primeIdx i)).card ^ 2 / (primeIdx i : ℝ)) := by
    convert energy_le_of_pair_bounds ( Aset ( primeIdx i ) ) ( Bset ( primeIdx i ) ) ( c * ( Aset ( primeIdx i ) |> Finset.card ) ^ 2 / ( primeIdx i : ℝ ) ) ( c * ( Bset ( primeIdx i ) |> Finset.card ) ^ 2 / ( primeIdx i : ℝ ) ) ( primeIdx i ) ( Aset_diff_subset ( primeIdx i ) ) hA hB _ _ using 1 <;> ring_nf; all_goals positivity
  refine le_trans h_apply ?_;
  norm_num [ PrimeSumset.mass ] at *;
  rw [ le_div_iff₀ ];
  · field_simp;
    rw [ add_div', mul_div_assoc', div_le_iff₀ ];
    · have := three_le_primeIdx_of_trigger hi;
      nlinarith [ ( by norm_cast : ( 3 : ℝ ) ≤ primeIdx i ), mul_le_mul_of_nonneg_left ( by norm_cast : ( 3 : ℝ ) ≤ primeIdx i ) ( sq_nonneg c ), mul_le_mul_of_nonneg_left ( by norm_cast : ( 3 : ℝ ) ≤ primeIdx i ) ( sq_nonneg ( ( Aset ( primeIdx i ) |> Finset.card : ℝ ) * ( Bset ( primeIdx i ) |> Finset.card : ℝ ) ) ), mul_le_mul_of_nonneg_left hmass ( sq_nonneg c ), mul_le_mul_of_nonneg_left hmass ( sq_nonneg ( primeIdx i : ℝ ) ) ];
    · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( by unfold primeIdx; exact Nat.prime_nth_prime i ) ) );
    · exact ne_of_gt ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( by exact Nat.prime_nth_prime i ) ) ) );
  · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( by exact Nat.prime_nth_prime i ) )

/-- **Factory-1 output (lower-bound form).**  Under the citable sieve constant
`c ≥ 0` and mass lower bound `x ≤ M`, the distinct sumset satisfies

  `|C| ≥ x / (1 + 3c²)`,

an explicit positive lower bound with `κ₀ = 1 + 3c²`. -/
theorem sumset_card_ge_explicit_of_sieve {i : ℕ} (hi : i > trigger) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ h : ℤ, h ≠ 0 →
        (rSub (Aset (primeIdx i)) h : ℝ)
          ≤ c * ((Aset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ))
    (hB : ∀ h : ℤ, h ≠ 0 →
        (rSub (Bset (primeIdx i)) h : ℝ)
          ≤ c * ((Bset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    (primeIdx i : ℝ) / (1 + 3 * c ^ 2)
      ≤ ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by omega
    exact_mod_cast this
  have hMpos : 0 < (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) := by
    exact_mod_cast mass_pos h3
  have hκpos : 0 < (1 + 3 * c ^ 2) := by positivity
  have hceil := energy_ceiling_of_sieve hi c hc hA hB hmass
  exact sumset_card_ge_of_energy_ceiling _ _ _ _ hxpos hκpos hMpos hceil

/-- **Factory-1 output (explicit density form / first explicit `h₀ > 0`).**

Under the citable sieve constant `c ≥ 0` and mass lower bound `x ≤ M`, for every
`h < 1/(1+3c²)` the distinct sumset satisfies

  `|C| > h·x`.

In particular `h₀ = 1/(1+3c²) > 0` is a first explicit positive density
constant, conditional only on the explicit upper-bound sieve (Brun / Selberg)
and Chebyshev mass bound. -/
theorem sumset_card_gt_explicit_of_sieve {i : ℕ} (hi : i > trigger)
    (c h : ℝ) (hc : 0 ≤ c) (hh : h < 1 / (1 + 3 * c ^ 2))
    (hA : ∀ k : ℤ, k ≠ 0 →
        (rSub (Aset (primeIdx i)) k : ℝ)
          ≤ c * ((Aset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ))
    (hB : ∀ k : ℤ, k ≠ 0 →
        (rSub (Bset (primeIdx i)) k : ℝ)
          ≤ c * ((Bset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    h * (primeIdx i : ℝ)
      < ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by omega
    exact_mod_cast this
  have hMpos : 0 < (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) := by
    exact_mod_cast mass_pos h3
  have hκpos : 0 < (1 + 3 * c ^ 2) := by positivity
  have hceil := energy_ceiling_of_sieve hi c hc hA hB hmass
  exact sumset_card_gt_of_energy_ceiling _ _ _ _ _ hxpos hκpos hMpos hceil hh

end PrimeSumset
