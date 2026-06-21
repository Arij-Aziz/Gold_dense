import Mathlib
import RequestProject.Blueprint
import RequestProject.Empirical
import RequestProject.Goldbach
import RequestProject.Supplement
import RequestProject.Theorem42

/-!
# Theorem H — entry point

* `RequestProject.Blueprint` — definitions of `A`, `B`, `C`, `h` and the main results:
  - `BlueprintH.tendsto_h_one : h i → 1` from the analytic hypotheses `Hgap`, `Hcover`;
  - `BlueprintH.tendsto_h_one_of_dusart : h i → 1` — the headline result, built from the
    cited literature: the prime-gap input `Hgap` is *derived* (`Hgap_of_dusart`) from
    Dusart, P. *Explicit estimates of some functions over primes*, Ramanujan J **45**,
    227–251 (2018), https://doi.org/10.1007/s11139-016-9839-4 (`HDusart`): the genuine
    **unconditional** estimate `g_n < p_n/(5000·ln² p_n)` for `p_n ≥ 468 991 632`, and
    `Hcover` is Aziz (2025, untitled-2.pdf) Theorem 4.2.
  The Prime Number Theorem and Chebyshev's theorem, where invoked in the blueprint, are
  cited as classical results.
* `RequestProject.Empirical` — computable mirrors of the definitions (e.g. `n(C₁₀₀) = 542`,
  recorded as comments), plus a reproducible floating-point check of Dusart's gap bound
  (`dusartGapOK`).
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
