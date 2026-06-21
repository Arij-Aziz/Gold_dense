import Mathlib
import RequestProject.Blueprint
import RequestProject.Goldbach

/-!
# Blueprint supplement: the explicit-threshold reduction

This file formalises the reduction described in `Blueprint supplement.txt`
("Conditional Goldbach via Analytic + Empirical Methods").

The supplement organises the proof of binary Goldbach into **two** complementary inputs:

* **Empirical input** (cited): Goldbach's conjecture has been verified for every even
  `N ≤ 4·10¹⁸` by Oliveira e Silva, Herzog & Pardi, *Empirical verification of the even
  Goldbach conjecture and computation of prime gaps up to 4·10¹⁸*, Math. Comp. **83**
  (2014), 2033–2060.  This is recorded here as the hypothesis `GoldbachEmpirical`.

* **Analytic input** (this project): every even `N > N₀` is a sum of two primes, where `N₀`
  is the explicit threshold of Theorem 4.2 (`N₀ = max(N₁, N₂)`, with `N₁` the major-arc
  threshold and `N₂` the minor-arc threshold).  This is recorded here as the hypothesis
  `GoldbachAnalytic N₀`.

The supplement's key observation (Section 2) is that once the explicit threshold satisfies
`N₀ < 4·10¹⁸`, the two inputs **tile** the even integers and full binary Goldbach follows.
That tiling argument is the content of `goldbach_of_empirical_analytic`, which is proved
unconditionally here (it is pure case analysis on `N ≤ 4·10¹⁸` vs. `N > 4·10¹⁸`).

We also connect the supplement's framing to the reduction already established in
`RequestProject.Goldbach`: the covering hypothesis `HmissZero` (every even integer in each
band `[P i + 4, …]` is a sum of two primes) implies the analytic input `GoldbachAnalytic N₀`
for any `N₀ ≥ 3` (`analytic_of_cover`).

## Soundness note

The supplement proposes recording the empirical verification and the circle-method machinery
as `axiom`s.  To keep the development sound we instead state every cited / open input as an
ordinary `Prop`-valued **hypothesis**; the genuinely open analytic step is still the
circle-method covering `cover_of_circle_method` of `RequestProject.Goldbach`.  No new axioms
are introduced.
-/

namespace BlueprintH.Supplement

open BlueprintH

/-- The empirical bound up to which binary Goldbach has been verified
(Oliveira e Silva, Herzog & Pardi, Math. Comp. **83** (2014)): `4·10¹⁸`. -/
def empiricalBound : ℕ := 4 * 10 ^ 18

/-- **Empirical Goldbach** (cited literature, Oliveira e Silva et al. 2014):
every even `N` with `4 ≤ N ≤ 4·10¹⁸` is a sum of two primes.  Taken as a hypothesis
referencing the published computation, not an axiom. -/
abbrev GoldbachEmpirical : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → N ≤ empiricalBound →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- **Analytic Goldbach above the explicit threshold `N₀`** (this project, Theorem 4.2):
every even `N > N₀` is a sum of two primes.  The supplement's task (Sections 1–2) is to make
`N₀` explicit and confirm `N₀ < 4·10¹⁸`; here `N₀` is kept as a parameter. -/
abbrev GoldbachAnalytic (N₀ : ℕ) : Prop :=
  ∀ N : ℕ, Even N → N₀ < N →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- **The supplement's tiling reduction (Section 2).**  If the explicit analytic threshold
`N₀` lies below the empirical bound `4·10¹⁸`, then the empirical input (for `N ≤ 4·10¹⁸`) and
the analytic input (for `N > N₀`, hence in particular for `N > 4·10¹⁸`) together cover every
even `N ≥ 4`: full binary Goldbach.

This is proved unconditionally — it is just the case split on `N ≤ 4·10¹⁸`. -/
theorem goldbach_of_empirical_analytic {N₀ : ℕ}
    (hN₀ : N₀ < empiricalBound)
    (hemp : GoldbachEmpirical) (hana : GoldbachAnalytic N₀) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  intro N hN h4
  by_cases h : N ≤ empiricalBound
  · exact hemp N hN h4 h
  · exact hana N hN (lt_trans hN₀ (not_le.mp h))

/-- **Connecting the supplement to the band-covering reduction.**  The covering hypothesis
`HmissZero` of `RequestProject.Goldbach` (every even integer in each band is a sum of two
primes) already yields binary Goldbach for *all* even `N ≥ 4` via `goldbach_of_cover`; in
particular it yields the analytic input `GoldbachAnalytic N₀` for any threshold `N₀ ≥ 3`. -/
theorem analytic_of_cover {N₀ : ℕ} (hN₀ : 3 ≤ N₀) (hcov : HmissZero) :
    GoldbachAnalytic N₀ := by
  intro N hN hlt
  exact goldbach_of_cover hcov N (by omega) hN

/-- `N₀ = 10¹⁰` is the value the supplement expects for the explicit threshold
(Section 2 / Hurdle: "the expected outcome is `N₀ ≪ 10¹⁰`").  Recorded here as a concrete
candidate; the exact value awaits the explicit constant computation of Theorem 4.2. -/
def N₀candidate : ℕ := 10 ^ 10

/-- The candidate threshold lies below the empirical bound, as the supplement requires
(`N₀ < 4·10¹⁸`). -/
theorem N₀candidate_lt_empiricalBound : N₀candidate < empiricalBound := by
  unfold N₀candidate empiricalBound; norm_num

/-- **Full binary Goldbach from the two supplement inputs at the candidate threshold.**
Combining the empirical verification with the analytic argument at `N₀ = 10¹⁰` gives every
even `N ≥ 4` as a sum of two primes. -/
theorem goldbach_of_inputs
    (hemp : GoldbachEmpirical) (hana : GoldbachAnalytic N₀candidate) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N :=
  goldbach_of_empirical_analytic N₀candidate_lt_empiricalBound hemp hana

end BlueprintH.Supplement
