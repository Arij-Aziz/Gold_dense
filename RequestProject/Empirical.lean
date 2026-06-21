import Mathlib

/-!
# Empirical motivation (computable mirrors)

Computable mirrors of the blueprint definitions.  They make the *empirical motivation* of
the blueprint reproducible if desired, but the heavy `native_decide` evaluations are **not**
run as part of the build (they slow every compile down).  Instead, the values they produce
are recorded as comments below.  To re-check any of them, turn the corresponding comment
back into an `example ... := by native_decide`.

* `ppC i`  — the `i`-th odd prime (1-indexed), `ppC 1 = 3`.
* `AsetC`, `BsetC`, `CsetC` — computable versions of `A`, `B`, `C`.

The corrected definition of `B` (lower bound `pᵢ`, exclusive) reproduces the blueprint's
empirical data (`n(C₁₀₀) = 542`, `h(100) ≈ 0.99`).
-/

namespace BlueprintH.Empirical

/-- Odd primes up to `b`. -/
def oddPrimesUpTo (b : Nat) : List Nat :=
  (List.range (b + 1)).filter (fun n => Nat.Prime n && n != 2)

/-- Precomputed odd-prime list (enough for the sample indices below). -/
def plist : List Nat := oddPrimesUpTo 3000

/-- The `i`-th odd prime, 1-indexed (`ppC 1 = 3`). -/
def ppC (i : Nat) : Nat := (plist[i - 1]?).getD 0

/-- Computable `A i`. -/
def AsetC (i : Nat) : List Nat := (oddPrimesUpTo (ppC i)).filter (fun q => 3 ≤ q)

/-- Computable `B i` (corrected: lower bound `pᵢ`, exclusive). -/
def BsetC (i : Nat) : List Nat :=
  (oddPrimesUpTo (2 * ppC (i + 1) - 5)).filter (fun q => ppC i < q)

/-- Computable `C i` (distinct sums). -/
def CsetC (i : Nat) : List Nat :=
  ((AsetC i).flatMap (fun a => (BsetC i).map (fun b => a + b))).eraseDups

/-- `n(C i)` = number of distinct prime sums. -/
def CcardC (i : Nat) : Nat := (CsetC i).length

/-! ### Verified empirical values (recorded, not re-run on build)

The following equalities were machine-checked with `native_decide`.  They are kept here as
comments so the build stays fast; re-enable any of them as an `example` to re-verify.

* `ppC 100 = 547`           -- the 100-th odd prime is 547
* `CcardC 100 = 542`        -- `n(C₁₀₀) = 542`, i.e. `h(100) = 542/547 ≈ 0.99`
* `(BsetC 100).length = 85` -- the corrected `B₁₀₀` has 85 elements (nonempty)
* `(BsetC 200).length ≠ 0`  -- the corrected `B₂₀₀` is nonempty
-/

/-! ### Numerical check of Dusart's prime-gap bound `g_n < p_n/(5000·ln² p_n)`

The project's gap input is supplied by Dusart, P. *Explicit estimates of some functions over
primes*, Ramanujan J **45**, 227–251 (2018), https://doi.org/10.1007/s11139-016-9839-4: for
`x ≥ 468 991 632` there is a prime in `(x, x·(1 + 1/(5000·ln²x))]`, i.e.
`g_n < p_n/(5000·ln² p_n)`.  This is a genuine **unconditional** estimate and is taken as the
cited hypothesis `HDusart` in `RequestProject.Blueprint`.

`dusartGapOK p` decides `g < p/(5000·ln² p)` for the prime `p` with next prime `p + g`, using
`Float` (a floating-point sanity check; the formal proof of Theorem H does not depend on it,
it relies on the cited hypothesis `HDusart`). -/

/-- Next prime strictly above `n`. -/
partial def nextPrime (n : Nat) : Nat :=
  let m := n + 1
  if Nat.Prime m then m else nextPrime m

/-- Floating-point check of Dusart's bound `g < p/(5000·ln² p)` at a prime `p`. -/
def dusartGapOK (p : Nat) : Bool :=
  let g := nextPrime p - p
  (Float.ofNat g) < (Float.ofNat p) / (5000.0 * (Float.log (Float.ofNat p)) ^ 2)

end BlueprintH.Empirical
