import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions
import RequestProject.KappaFactory

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# Module 9 — `PrimeSumset.DifferenceSieve` (extracting the per-difference constant `c`)

This module realises the **Difference-Sieve Program**: it goes one layer below
`RequestProject.KappaFactory`.  `KappaFactory` *assumed* the per-difference
sieve bound

  `r_{A-A}(h) ≤ c · |A|² / x`,  `r_{B-B}(h) ≤ c · |B|² / x`  (`h ≠ 0`)

as a black box with an explicit constant `c`.  Here we **derive that bound**,
with an explicit formula `c = C_pair · κ_A²`, from two strictly more *citable*
unconditional analytic inputs:

* a **raw Selberg/Brun prime-pair upper bound** (Factory D1, §4.1):
  `r_{A-A}(h) ≤ C_pair · x / (log x)²`  for every `h ≠ 0`
  (the number of `p ≤ x` with `p, p+h` both prime is `≪ x/log²x`, with an
  explicit `C_pair`, e.g. via Selberg's sieve / Brun–Titchmarsh);
* a **Chebyshev / PNT lower bound** on the prime count
  `|A| ≥ x / (κ_A · log x)`  (and similarly for `B`).

The elementary algebraic identity `|A|²/x ≥ x/(κ_A² log²x)` then converts the
raw `x/log²x`-shaped pair bound into the per-difference `|A|²/x`-shaped bound
with the **explicit transfer constant**

  `c₀ = C_pair · κ_A²`.

Feeding `c₀` into `KappaFactory.energy_ceiling_of_sieve` produces the explicit
energy ceiling `κ₀ = 1 + 3 c₀²` and hence the first explicit positive density
`h₀ = 1/(1 + 3 c₀²)`.

## What is fully proven here (sorry-free)

* `per_diff_of_pair_bound` — the **core transfer lemma** (pure real algebra):
  raw pair bound `r ≤ C_pair·x/lx²` plus Chebyshev lower bound
  `x/(κ_A·lx) ≤ |A|` give `r ≤ (C_pair·κ_A²)·|A|²/x`.
* `energy_ceiling_of_prime_pair_sieve` — the prime instance: from the raw pair
  bounds and Chebyshev lower bounds (plus the mass bound `x ≤ M`), the energy
  ceiling `E ≤ (1 + 3 c₀²)·M²/x` holds with `c₀ = C_pair·κ_A²`.
* `sumset_card_ge_of_prime_pair_sieve` : `|C| ≥ x/(1 + 3 c₀²)`.
* `sumset_card_gt_of_prime_pair_sieve` : `|C| > h·x` for every
  `h < 1/(1 + 3 c₀²)`.
* `sumset_card_gt_of_prime_pair_sieve_concrete` — a concrete numeric
  illustration: with `C_pair = 16`, `κ_A = 2` (so `c₀ = 64`, `κ₀ = 12289`),
  the density `h₀ = 1/12289` is realised.

## Honest scope (singular-series obstruction)

A genuinely *uniform-in-`x`* constant `C_pair` (and hence `c₀`) does **not**
exist for the sharp sieve: the Selberg main term carries the singular series
`𝔖(h) = ∏_{p∣h, p>2}(p-1)/(p-2)`, whose supremum over even `h ≤ x` grows like
`≍ log log x`.  For our setup `x = p_i` is a *single fixed* (astronomically
large) value, so `sup_{h} 𝔖(h)` is a finite constant and the finite `C_pair`
(hence finite `c₀`) exists for that `x`; the theorems below take `C_pair` and
`κ_A` as parameters supplied per `x`, which is exactly what the literature
provides.  Driving `c₀` down to the regime `κ₀ < 10/9` (to recover `|C| > 0.9x`)
still requires averaging the singular series — the Hardy–Littlewood main term —
which is the single documented gap elsewhere in the project.
-/

namespace PrimeSumset

open Finset

/-- **Core transfer lemma (pure real algebra).**

Given a raw prime-pair upper bound `r ≤ C_pair · x / lx²` (with `lx = log x`)
and a Chebyshev lower bound on the prime count `x / (κ_A · lx) ≤ L` (with
`L = |A|`), the per-difference bound

  `r ≤ (C_pair · κ_A²) · L² / x`

follows.  This is the algebraic engine that converts the citable `x/log²x`-shaped
sieve bound into the `|A|²/x`-shaped per-difference bound required by
`KappaFactory`, with the explicit transfer constant `c₀ = C_pair · κ_A²`. -/
lemma per_diff_of_pair_bound
    (r Cpair kA L x lx : ℝ)
    (hx : 0 < x) (hlx : 0 < lx) (hkA : 0 < kA)
    (hCpair : 0 ≤ Cpair)
    (hpair : r ≤ Cpair * x / lx ^ 2)
    (hlow : x / (kA * lx) ≤ L) :
    r ≤ (Cpair * kA ^ 2) * L ^ 2 / x := by
  have hden : 0 < kA * lx := by positivity
  have hL : x ≤ L * (kA * lx) := by
    rw [div_le_iff₀ hden] at hlow; linarith
  have hLpos : 0 ≤ L := by nlinarith [mul_pos hkA hlx]
  have key : Cpair * x / lx ^ 2 ≤ (Cpair * kA ^ 2) * L ^ 2 / x := by
    rw [div_le_div_iff₀ (by positivity) hx]
    nlinarith [mul_le_mul hL hL (le_of_lt hx) (by positivity : (0:ℝ) ≤ L * (kA*lx)),
               mul_nonneg hCpair (sq_nonneg lx), hCpair]
  linarith

/-- Positivity of `log (p_i)` above the trigger (`p_i ≥ 3 > 1`). -/
lemma log_primeIdx_pos {i : ℕ} (hi : i > trigger) : 0 < Real.log (primeIdx i) := by
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  apply Real.log_pos
  have : (3 : ℝ) ≤ (primeIdx i : ℝ) := by exact_mod_cast h3
  linarith

/-- **Difference-Sieve prime instance — explicit energy ceiling from raw pair
bounds.**

For `i > 10^15`, `x = p_i`, `A = {p prime : 3 ≤ p ≤ x}`,
`B = {p prime : x < p ≤ 2x}`.  Assume the citable raw prime-pair upper bounds
with explicit constant `C_pair ≥ 0`:

  `r_{A-A}(h) ≤ C_pair · x / (log x)²`,  `r_{B-B}(h) ≤ C_pair · x / (log x)²`  (`h ≠ 0`),

the citable Chebyshev lower bounds with explicit constant `κ_A > 0`:

  `x / (κ_A · log x) ≤ |A|`,  `x / (κ_A · log x) ≤ |B|`,

and the mass lower bound `x ≤ M`.  Then with `c₀ = C_pair · κ_A²` the additive
energy obeys

  `E(A,B) ≤ (1 + 3 c₀²) · M² / x`. -/
theorem energy_ceiling_of_prime_pair_sieve {i : ℕ} (hi : i > trigger)
    (Cpair kA : ℝ) (hCpair : 0 ≤ Cpair) (hkA : 0 < kA)
    (hpairA : ∀ h : ℤ, h ≠ 0 →
        (rSub (Aset (primeIdx i)) h : ℝ)
          ≤ Cpair * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hpairB : ∀ h : ℤ, h ≠ 0 →
        (rSub (Bset (primeIdx i)) h : ℝ)
          ≤ Cpair * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hlowA : (primeIdx i : ℝ) / (kA * Real.log (primeIdx i))
          ≤ ((Aset (primeIdx i)).card : ℝ))
    (hlowB : (primeIdx i : ℝ) / (kA * Real.log (primeIdx i))
          ≤ ((Bset (primeIdx i)).card : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)
      ≤ (1 + 3 * (Cpair * kA ^ 2) ^ 2)
          * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
          / (primeIdx i : ℝ) := by
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by
      have := three_le_primeIdx_of_trigger hi; omega
    exact_mod_cast this
  have hlx : 0 < Real.log (primeIdx i) := log_primeIdx_pos hi
  have hc : 0 ≤ Cpair * kA ^ 2 := by positivity
  -- Transfer the raw pair bounds to per-difference bounds with c₀ = Cpair·κ_A².
  have hA : ∀ h : ℤ, h ≠ 0 →
      (rSub (Aset (primeIdx i)) h : ℝ)
        ≤ (Cpair * kA ^ 2) * ((Aset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ) := by
    intro h hh
    exact per_diff_of_pair_bound _ Cpair kA _ _ _ hxpos hlx hkA hCpair (hpairA h hh) hlowA
  have hB : ∀ h : ℤ, h ≠ 0 →
      (rSub (Bset (primeIdx i)) h : ℝ)
        ≤ (Cpair * kA ^ 2) * ((Bset (primeIdx i)).card : ℝ) ^ 2 / (primeIdx i : ℝ) := by
    intro h hh
    exact per_diff_of_pair_bound _ Cpair kA _ _ _ hxpos hlx hkA hCpair (hpairB h hh) hlowB
  exact energy_ceiling_of_sieve hi (Cpair * kA ^ 2) hc hA hB hmass

/-- **Difference-Sieve output (lower-bound form).**  Under the raw pair bounds
(constant `C_pair`), Chebyshev lower bounds (constant `κ_A`) and the mass bound,
with `c₀ = C_pair·κ_A²` the distinct sumset satisfies `|C| ≥ x/(1 + 3 c₀²)`. -/
theorem sumset_card_ge_of_prime_pair_sieve {i : ℕ} (hi : i > trigger)
    (Cpair kA : ℝ) (hCpair : 0 ≤ Cpair) (hkA : 0 < kA)
    (hpairA : ∀ h : ℤ, h ≠ 0 →
        (rSub (Aset (primeIdx i)) h : ℝ)
          ≤ Cpair * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hpairB : ∀ h : ℤ, h ≠ 0 →
        (rSub (Bset (primeIdx i)) h : ℝ)
          ≤ Cpair * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hlowA : (primeIdx i : ℝ) / (kA * Real.log (primeIdx i))
          ≤ ((Aset (primeIdx i)).card : ℝ))
    (hlowB : (primeIdx i : ℝ) / (kA * Real.log (primeIdx i))
          ≤ ((Bset (primeIdx i)).card : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    (primeIdx i : ℝ) / (1 + 3 * (Cpair * kA ^ 2) ^ 2)
      ≤ ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by omega
    exact_mod_cast this
  have hMpos : 0 < (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) := by
    exact_mod_cast mass_pos h3
  have hκpos : 0 < (1 + 3 * (Cpair * kA ^ 2) ^ 2) := by positivity
  have hceil := energy_ceiling_of_prime_pair_sieve hi Cpair kA hCpair hkA
    hpairA hpairB hlowA hlowB hmass
  exact sumset_card_ge_of_energy_ceiling _ _ _ _ hxpos hκpos hMpos hceil

/-- **Difference-Sieve output (explicit density form).**  Under the raw pair
bounds (constant `C_pair`), Chebyshev lower bounds (constant `κ_A`) and the mass
bound, with `c₀ = C_pair·κ_A²` the distinct sumset satisfies `|C| > h·x` for
every `h < 1/(1 + 3 c₀²)`.  Thus `h₀ = 1/(1 + 3 c₀²) > 0` is a first explicit
positive density extracted from the raw (citable) prime-pair upper bound. -/
theorem sumset_card_gt_of_prime_pair_sieve {i : ℕ} (hi : i > trigger)
    (Cpair kA h : ℝ) (hCpair : 0 ≤ Cpair) (hkA : 0 < kA)
    (hh : h < 1 / (1 + 3 * (Cpair * kA ^ 2) ^ 2))
    (hpairA : ∀ k : ℤ, k ≠ 0 →
        (rSub (Aset (primeIdx i)) k : ℝ)
          ≤ Cpair * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hpairB : ∀ k : ℤ, k ≠ 0 →
        (rSub (Bset (primeIdx i)) k : ℝ)
          ≤ Cpair * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hlowA : (primeIdx i : ℝ) / (kA * Real.log (primeIdx i))
          ≤ ((Aset (primeIdx i)).card : ℝ))
    (hlowB : (primeIdx i : ℝ) / (kA * Real.log (primeIdx i))
          ≤ ((Bset (primeIdx i)).card : ℝ))
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
  have hκpos : 0 < (1 + 3 * (Cpair * kA ^ 2) ^ 2) := by positivity
  have hceil := energy_ceiling_of_prime_pair_sieve hi Cpair kA hCpair hkA
    hpairA hpairB hlowA hlowB hmass
  exact sumset_card_gt_of_energy_ceiling _ _ _ _ _ hxpos hκpos hMpos hceil hh

/-- **Concrete numeric illustration.**  Taking the (illustrative) explicit
constants `C_pair = 16` and `κ_A = 2`, the transfer constant is `c₀ = 64`, the
energy constant is `κ₀ = 1 + 3·64² = 12289`, and the realised explicit positive
density is `h₀ = 1/12289`: `|C| ≥ (1/12289)·x`.  (The numbers are placeholders
for whatever explicit Selberg/Brun and Chebyshev constants one cites; the point
is that any finite pair `(C_pair, κ_A)` yields a concrete finite `h₀ > 0`.) -/
theorem sumset_card_gt_of_prime_pair_sieve_concrete {i : ℕ} (hi : i > trigger)
    (hpairA : ∀ k : ℤ, k ≠ 0 →
        (rSub (Aset (primeIdx i)) k : ℝ)
          ≤ 16 * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hpairB : ∀ k : ℤ, k ≠ 0 →
        (rSub (Bset (primeIdx i)) k : ℝ)
          ≤ 16 * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hlowA : (primeIdx i : ℝ) / (2 * Real.log (primeIdx i))
          ≤ ((Aset (primeIdx i)).card : ℝ))
    (hlowB : (primeIdx i : ℝ) / (2 * Real.log (primeIdx i))
          ≤ ((Bset (primeIdx i)).card : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    (1 / 12289 : ℝ) * (primeIdx i : ℝ)
      ≤ ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by
      have := three_le_primeIdx_of_trigger hi; omega
    exact_mod_cast this
  have hge := sumset_card_ge_of_prime_pair_sieve hi 16 2
    (by norm_num) (by norm_num) hpairA hpairB hlowA hlowB hmass
  have heq : (1 + 3 * ((16 : ℝ) * (2 : ℝ) ^ 2) ^ 2) = 12289 := by norm_num
  rw [heq] at hge
  rw [div_eq_mul_one_div, mul_comm] at hge
  linarith

end PrimeSumset
