import RequestProject.AdditiveEnergy
import RequestProject.Definitions

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# Module 7 — `PrimeSumset.ResearchLadder` (the explicit-constant ladder)

This module realises the **research ladder** of the second blueprint
(*"Proving `|C| > h·p_i` by Changing the Landscape"*, §6) and its **Success
type D** ("produce a nontrivial explicit positive constant `h₀ > 0` and a clear
roadmap for iterative improvement").

The mathematical situation is honest and precise:

* The blueprint's target `|C| > h·x` follows, for `x = pᵢ`, from a single
  analytic input — an **energy ceiling** `E(A,B) ≤ κ·M²/x` with an *explicit*
  constant `κ` (a sieve upper bound on the additive energy).  This is recorded
  for `κ < 10/9` (the strong, Hardy–Littlewood-strength input) as the documented
  `sorry` `PrimeSumset.energy_ceiling`.

* The reduction `ceiling ⇒ density bound` is **fully proven** and completely
  *general in `κ`* (`sumset_card_ge_of_energy_ceiling`,
  `sumset_card_gt_of_energy_ceiling` in `AdditiveEnergy`): for **any** explicit
  `κ > 0`,

      `E(A,B) ≤ κ·M²/x  ⟹  |A+B| ≥ x/κ`,  and  `|A+B| > h·x` for every `h < 1/κ`.

So the entire content of the research ladder is the constant `κ`:

  * a **Brun/Selberg upper-bound sieve** yields an explicit but large `κ`
    (the parity barrier forces `κ > 1`), hence a small but **positive** explicit
    constant `h₀ = 1/κ`  (Stage 1 / Success D);
  * refining the weights drives `κ` down (Stage 2);
  * reaching `κ < 10/9` gives the target `h = 0.9` (Stage 3).

Per the Lean Integration Policy (§11) — "separation between proved facts and new
assumptions" — the sieve ceiling is introduced **as an explicit hypothesis**
(not as an axiom).  Everything below is therefore `sorry`-free: it is the exact,
machine-checked statement that *any* explicit sieve constant `κ` rigorously
implies an explicit positive density bound for the prime sumset.
-/

namespace PrimeSumset

open Finset

/-- **Research-ladder theorem (lower bound form).**

Let `i > 10^15`, `x = pᵢ`, `A = {p prime : 3 ≤ p ≤ x}`,
`B = {p prime : x < p ≤ 2x}`.  Suppose the additive energy obeys the explicit
**sieve ceiling** `E(A,B) ≤ κ·M²/x` for some explicit `κ > 0` (the citable
Brun/Selberg upper-bound input).  Then the distinct sumset satisfies

  `|A+B| ≥ x/κ`.

Fully proven (`sorry`-free) from the general reduction; the only assumption is
the explicit ceiling, supplied as a hypothesis `hceil`. -/
theorem sumset_card_ge_of_sieve_ceiling
    {i : ℕ} (hi : i > trigger) (κ : ℝ) (hκ : 0 < κ)
    (hceil : (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)
        ≤ κ * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
            / (primeIdx i : ℝ)) :
    (primeIdx i : ℝ) / κ ≤ ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by omega
    exact_mod_cast this
  have hMpos : 0 < (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) := by
    exact_mod_cast mass_pos h3
  exact sumset_card_ge_of_energy_ceiling _ _ _ _ hxpos hκ hMpos hceil

/-- **Research-ladder theorem (explicit density form / Success type D).**

Under the same setup, for an explicit sieve ceiling with constant `κ > 0`, the
distinct sumset satisfies `|A+B| > h·x` for the explicit constant `h = 1/κ`
(indeed for every `h < 1/κ`).

This is exactly the blueprint's target statement shape `|C| > h·pᵢ` with an
explicit `h`; the value of `h` is pinned to the reciprocal of whatever explicit
sieve constant `κ` is available.  Fully proven (`sorry`-free) from the explicit
ceiling hypothesis `hceil`. -/
theorem sumset_card_gt_const_of_sieve_ceiling
    {i : ℕ} (hi : i > trigger) (κ h : ℝ) (hκ : 0 < κ) (hh : h < 1 / κ)
    (hceil : (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)
        ≤ κ * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
            / (primeIdx i : ℝ)) :
    h * (primeIdx i : ℝ)
      < ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by omega
    exact_mod_cast this
  have hMpos : 0 < (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) := by
    exact_mod_cast mass_pos h3
  exact sumset_card_gt_of_energy_ceiling _ _ _ _ _ hxpos hκ hMpos hceil hh

end PrimeSumset
