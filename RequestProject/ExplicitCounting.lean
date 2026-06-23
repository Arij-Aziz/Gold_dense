import RequestProject.Definitions

open scoped BigOperators
open scoped Classical

/-!
# Module 2 — `PrimeSumset.ExplicitCounting`

Explicit prime-counting inputs (blueprint §3 Citable Tool 1, Module 2).

The exact cardinality identities `card_Aset`, `card_Bset` relate `|A|`, `|B|`
to the prime-counting function `Nat.primeCounting` (`π`).  They are elementary
and unconditional, but are recorded here as `sorry` bookkeeping facts: they are
**not** used on the proven path to the main theorem (that path goes through
`mass_pos` and the energy ceiling only).

The quantitative bounds `pi_bounds`, `mass_lower_bound` encode the **citable**
Dusart/Axler explicit estimates for `π(t)`.  These are genuine theorems of
analytic number theory that are *not present in Mathlib*; they are stated here
in existence form (so as not to commit to any unverified numeric constant) and
left as `sorry`.  They would feed the proof of the (still open / novel) energy
ceiling, but are not on the proven path to the main theorem either.

**Honesty note.** Everything in this module is `sorry`. None of it is on the
machine-checked path to `MainTheorem.sumset_card_gt_904`, which depends
only on `PrimeSumset.energy_ceiling` (the single novel obligation) together with
fully-proven combinatorics.
-/

namespace PrimeSumset

open Finset

/-- `|A| = π(x) - 1`: the primes in `[3, x]` are exactly the primes `≤ x` other
than `2`. (Elementary; recorded as `sorry`, off the proven main path.) -/
lemma card_Aset {x : ℕ} (hx : 2 ≤ x) :
    (Aset x).card = Nat.primeCounting x - 1 := by
  sorry

/-- `|B| = π(2x) - π(x)`: the primes in `(x, 2x]`.
(Elementary; recorded as `sorry`, off the proven main path.) -/
lemma card_Bset (x : ℕ) :
    (Bset x).card = Nat.primeCounting (2 * x) - Nat.primeCounting x := by
  sorry

/-- **Citable Tool 1 (Dusart/Axler).**  An explicit two-sided bound
`c₁ · t/ln t < π(t) < c₂ · t/ln t` valid for all `t` above the trigger range.
Stated in existence form to avoid committing to an unverified constant; this is
a genuine but not-in-Mathlib analytic input, left as `sorry`. -/
lemma pi_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
      ∀ t : ℕ, t ≥ trigger →
        c₁ * (t : ℝ) / Real.log t < (Nat.primeCounting t : ℝ) ∧
        (Nat.primeCounting t : ℝ) < c₂ * (t : ℝ) / Real.log t := by
  sorry

end PrimeSumset
