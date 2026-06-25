import RequestProject.AdditiveEnergy
import RequestProject.Definitions
import RequestProject.RestrictedGoldbachMain

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# PrimeSumset — Main Theorem

For every `i > 10^15` with `x = pᵢ`, the distinct sumset
`C = A + B` of `A = primes∩[3,x]` and `B = primes∩(x,2x]`
satisfies `|C| > 0.95·x`.

This wraps `RestrictedGoldbach.sumset_card_gt_95` (1‑indexed primes)
into the 0‑indexed `PrimeSumset` framing.
-/

namespace PrimeSumset

open Finset

/-- **Main Theorem (0.95 constant).**  For every `i > 10^15`,
`|C| > 0.95·pᵢ`.

Wraps `RestrictedGoldbach.sumset_card_gt_95` (1‑indexed) into
the 0‑indexed `PrimeSumset` framing. -/
theorem sumset_card_gt_95 {i : ℕ} (hi : i > trigger) :
    0.95 * (primeIdx i : ℝ)
      < ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have hi' : 10 ^ 15 < i + 1 := by
    unfold trigger at hi; omega
  have h := RestrictedGoldbach.sumset_card_gt_95 hi'
  simpa [RestrictedGoldbach.primeIdx1, RestrictedGoldbach.Aset, RestrictedGoldbach.Bset] using h

end PrimeSumset
