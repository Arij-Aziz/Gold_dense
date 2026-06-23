/-
  Challenge.lean
  ==============
  Auditable statement file for the PrimeSumset project
  ("A new explicit positive density for the prime sumset").

  ── HOW TO USE ──────────────────────────────────────────────────────────────
  This file has ONE import: `import Mathlib`.
  No `RequestProject.*` imports appear anywhere.

  Every theorem is stated with its verbatim signature from the source files,
  with `sorry` as the proof body. All project-internal definitions are
  reproduced inline below using only Mathlib primitives, so a reviewer can
  verify every statement is well-typed without building the project.

  To check: `lake build RequestProject.Challenge`
  Expected: zero errors; only `declaration uses sorry` warnings (intended).

  ── SCOPE ────────────────────────────────────────────────────────────────────
  15 critical theorems from the active dependency tree of the PrimeSumset
  project, matching `RequestProject.Audit.lean` exactly.

  ── CONTENTS ─────────────────────────────────────────────────────────────────
  §0.  Inline definitions (Mathlib-only reproductions)
  §1.  Phase I : Target main results (conditional on energy_ceiling)
  §2.  Phase II: The analytic formalization gap
  §3.  Phase III: Research ladder (unconditional reductions)
  §4.  Phase IV: Unconditional difference sieve application
  §5.  Phase V : Unconditional explicit densities (literature constants)
  §6.  Phase VI: Minor-arc integration (circle method)

  Total: 15 theorems/lemmas (matching Audit.lean exactly).
  Axiom footprint for each: [propext, Classical.choice, Quot.sound, sorryAx].
  ─────────────────────────────────────────────────────────────────────────────
-/
import Mathlib

open scoped BigOperators
open scoped Pointwise
open scoped Classical
open scoped Real
open Complex

noncomputable section

-- ════════════════════════════════════════════════════════════════════════════
-- §0.  Inline definitions (Mathlib primitives only)
-- ════════════════════════════════════════════════════════════════════════════

namespace PrimeSumset

open Finset

-- ── From AdditiveEnergy.lean ────────────────────────────────────────────────

/-- The representation function `r_{A+B}(n) = #{(a,b) ∈ A×B : a+b = n}`. -/
def rAdd (A B : Finset ℤ) (n : ℤ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = n)).card

/-- The (self) difference representation function
    `r_{A-A}(h) = #{(a,a') ∈ A×A : a-a' = h}`. -/
def rSub (A : Finset ℤ) (h : ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 - p.2 = h)).card

/-- The additive energy `E(A,B)`, as the exact count of quadruples
    `(a₁,b₁,a₂,b₂) ∈ A×B×A×B` with `a₁+b₁ = a₂+b₂`. -/
def energy (A B : Finset ℤ) : ℕ :=
  (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter
    (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card

/-- The distinct sumset `C = A + B` (pointwise addition). -/
def sumset (A B : Finset ℤ) : Finset ℤ := A + B

/-- The mass `M = |A|·|B|`. -/
def mass (A B : Finset ℤ) : ℕ := A.card * B.card

-- ── From Definitions.lean ───────────────────────────────────────────────────

/-- The trigger threshold of the blueprint: `i > 10^15`. -/
def trigger : ℕ := 10 ^ 15

/-- The `i`-th prime `p_i` (0-indexed: `primeIdx 0 = 2`, `primeIdx 1 = 3`, …). -/
noncomputable def primeIdx (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- `A = {p prime : 3 ≤ p ≤ x}`, as a finite set of integers. -/
noncomputable def Aset (x : ℕ) : Finset ℤ :=
  (((Finset.Icc 3 x).filter (fun n => Nat.Prime n)).image (fun n => (n : ℤ)))

/-- `B = {p prime : x < p ≤ 2x}`, as a finite set of integers. -/
noncomputable def Bset (x : ℕ) : Finset ℤ :=
  (((Finset.Ioc x (2 * x)).filter (fun n => Nat.Prime n)).image (fun n => (n : ℤ)))

-- ── From MinorArc.lean ──────────────────────────────────────────────────────

/-- The exponential sum `S A α = ∑_{a∈A} e(aα)` with `e(t) = exp(2π i t)`. -/
noncomputable def S (A : Finset ℤ) (α : ℝ) : ℂ :=
  ∑ a ∈ A, Complex.exp (((2 * Real.pi * (a : ℝ) * α)) * Complex.I)

/-- The exponential sum `T B α = ∑_{b∈B} e(bα)`; defined identically to `S`. -/
noncomputable def T (B : Finset ℤ) (α : ℝ) : ℂ :=
  ∑ b ∈ B, Complex.exp (((2 * Real.pi * (b : ℝ) * α)) * Complex.I)

-- ── From ConcreteConstants.lean ─────────────────────────────────────────────

/-- The literature-derived prime-pair upper-bound constant.
    Source: Selberg sieve, C_sieve = 8 (Montgomery–Vaughan);
    sup 𝔖(h) ≈ 8.33 for x = 10^15.  C_pair = C_sieve · sup 𝔖(h) ≈ 67. -/
def C_pair_lit : ℝ := 67

/-- The literature-derived Chebyshev lower-bound constant.
    Source: Dusart 2010, Theorem 1: π(x) > x/(log x - 1) for x ≥ 5393.
    For x ≥ 10^15, |A| = π(x)-1 > x/log x, so κ_A = 1 suffices. -/
def kA_lit : ℝ := 1

/-- Transfer constant c₀ = C_pair · κ_A². -/
def c0_lit : ℝ := C_pair_lit * kA_lit ^ 2

/-- Energy constant κ₀ = 1 + 3c₀². -/
def kappa0_lit : ℝ := 1 + 3 * c0_lit ^ 2

/-- First explicit cited positive density h₀ = 1/κ₀. -/
noncomputable def h0_lit : ℝ := 1 / kappa0_lit

-- ════════════════════════════════════════════════════════════════════════════
-- §1.  Phase I — Target Main Results (conditional on energy_ceiling)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Main Theorem (sumset_card_gt_904).**
    For every `i > 10^15`, with `x = pᵢ`,
    `A = {p prime : 3 ≤ p ≤ x}` and `B = {p prime : x < p ≤ 2x}`,
    the distinct sumset `C = A + B` satisfies `|C| > 0.904·x`.

    The constant `0.904` is sharp for the available reproducing-kernel value
    `κ = 1.1053`: `1/κ = 10000/11053 = 0.90473… > 0.904`.

    Proven modulo the single novel obligation `energy_ceiling`; all other steps
    are machine-checked. -/
theorem sumset_card_gt_904 {i : ℕ} (hi : i > trigger) :
    0.904 * (primeIdx i : ℝ)
      < ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  sorry

/-- **Overlap (high-multiplicity) bound.**
    For every `i > 10^15`, with `x = pᵢ`, `A = primes∩[3,x]`,
    `B = primes∩(x,2x]`, and any `k ≥ 1`, the number of sums `n ∈ C = A+B`
    represented at least `k` times satisfies
    `#{n ∈ C : k ≤ r_{A+B}(n)} ≤ (10/9)·M²/(k²·x)`, where `M = |A|·|B|`.

    This is the energy level-set (Chebyshev) bound: from Identity 1,
    `#{…}·k² ≤ E(A,B)`, and the energy ceiling gives
    `E ≤ 1.1053·M²/x ≤ (10/9)·M²/x`.
    Proven modulo the single novel obligation `energy_ceiling`. -/
theorem overlap_bound {i : ℕ} (hi : i > trigger) (k : ℕ) (hk : 0 < k) :
    (#{n ∈ sumset (Aset (primeIdx i)) (Bset (primeIdx i)) |
        k ≤ rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) n} : ℝ)
      ≤ (10/9 : ℝ) * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
          / ((k : ℝ) ^ 2 * (primeIdx i : ℝ)) := by
  sorry

/-- **Goldbach density.**
    For every `i > 10^15`, with `x = pᵢ`, `A = Aset x`, `B = Bset x`,
    the number of representable integers `N ∈ (x, 3x]`
    (those with `0 < r_{A+B}(N)`) exceeds `0.904·x`.

    Since the sumset `A+B` is exactly the support `(x,3x]` of representable
    integers, this filtered count equals `(A+B).card`, so the statement is
    exactly the main theorem `sumset_card_gt_904` repackaged.
    (The constant `9040/10000 = 0.904`.) -/
theorem goldbach_density {i : ℕ} (hi : i > trigger) :
    (9040 / 10000 : ℝ) * (primeIdx i : ℝ)
      < (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
            0 < rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N} : ℝ) := by
  sorry

/-- **Goldbach exceptional-set bound.**
    For every `i > 10^15`, with `x = pᵢ`, `A = Aset x`, `B = Bset x`,
    the number of **even** integers `N ∈ (x, 3x]` that are *not* representable
    (`r_{A+B}(N) = 0`) is below `0.096·x`.

    The interval `(x, 3x]` contains exactly `x` even numbers, all representable
    `N` are even, and representable + exceptional partition the even numbers;
    combined with `goldbach_density` (representable `> 0.904·x`) this forces the
    even exceptional count below `(1 - 0.904)·x = 0.096·x`.
    (The constant `960/10000 = 0.096`.) -/
theorem goldbach_exception_bound {i : ℕ} (hi : i > trigger) :
    (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
          Even N ∧ rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N = 0} : ℝ)
      < (960 / 10000 : ℝ) * (primeIdx i : ℝ) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §2.  Phase II — The Analytic Formalization Gap
-- ════════════════════════════════════════════════════════════════════════════

/-- **Energy Ceiling (the single novel obligation, `sorry`).**
    For every `i > 10^15`, the additive energy of the prime sets
    `A = primes∩[3,pᵢ]` and `B = primes∩(pᵢ,2pᵢ]` obeys
    `E(A,B) ≤ (1.1053)·M²/pᵢ`, where `M = |A|·|B|`.

    The constant `1.1053` is the reproducing-kernel value `1/K_ν(0,0)` for the
    limiting measure `dν = δ + (1/3)|α|dα`; since `1/1.1053 > 0.904`, this
    ceiling yields the main theorem `|C| > 0.904·pᵢ`.

    Discharging this ceiling requires two ingredients absent from Mathlib:
    1. the Goldston–Montgomery bridge linking `E(A,B)` to Montgomery's pair
       correlation `F(α, T)`, and
    2. the D-I-R reproducing-kernel extremal bound `C_ν ≤ 1/K_ν(0,0)`.

    It is therefore left as one honest `sorry`. The reduction
    `ceiling ⇒ |C| > 0.904·pᵢ` is fully machine-checked. -/
theorem energy_ceiling {i : ℕ} (hi : i > trigger) :
    (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)
      ≤ (11053 / 10000 : ℝ)
          * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
          / (primeIdx i : ℝ) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §3.  Phase III — Research Ladder (Unconditional Reductions)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Research-ladder theorem (lower bound form).**
    Let `i > 10^15`, `x = pᵢ`, `A = {p prime : 3 ≤ p ≤ x}`,
    `B = {p prime : x < p ≤ 2x}`.  Suppose the additive energy obeys the
    explicit **sieve ceiling** `E(A,B) ≤ κ·M²/x` for some explicit `κ > 0`
    (the citable Brun/Selberg upper-bound input).  Then the distinct sumset
    satisfies `|A+B| ≥ x/κ`.

    Fully proven (`sorry`-free) from the general reduction; the only assumption
    is the explicit ceiling, supplied as a hypothesis `hceil`. -/
theorem sumset_card_ge_of_sieve_ceiling
    {i : ℕ} (hi : i > trigger) (κ : ℝ) (hκ : 0 < κ)
    (hceil : (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)
        ≤ κ * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
            / (primeIdx i : ℝ)) :
    (primeIdx i : ℝ) / κ ≤
      ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  sorry

/-- **Research-ladder theorem (explicit density form / Success type D).**
    Under the same setup, for an explicit sieve ceiling with constant `κ > 0`,
    the distinct sumset satisfies `|A+B| > h·x` for every `h < 1/κ`.

    This is exactly the blueprint's target statement shape `|C| > h·pᵢ` with an
    explicit `h`; the value of `h` is pinned to the reciprocal of whatever
    explicit sieve constant `κ` is available.  Fully proven (`sorry`-free) from
    the explicit ceiling hypothesis `hceil`. -/
theorem sumset_card_gt_const_of_sieve_ceiling
    {i : ℕ} (hi : i > trigger) (κ h : ℝ) (hκ : 0 < κ) (hh : h < 1 / κ)
    (hceil : (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)
        ≤ κ * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
            / (primeIdx i : ℝ)) :
    h * (primeIdx i : ℝ)
      < ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §4.  Phase IV — Unconditional Difference Sieve Application
-- ════════════════════════════════════════════════════════════════════════════

/-- **Core transfer lemma (pure real algebra).**
    Given a raw prime-pair upper bound `r ≤ C_pair · x / lx²` (with `lx = log x`)
    and a Chebyshev lower bound on the prime count `x / (κ_A · lx) ≤ L`
    (with `L = |A|`), the per-difference bound

      `r ≤ (C_pair · κ_A²) · L² / x`

    follows.  This is the algebraic engine that converts the citable
    `x/log²x`-shaped sieve bound into the `|A|²/x`-shaped per-difference bound
    required by `KappaFactory`, with the explicit transfer constant
    `c₀ = C_pair · κ_A²`. -/
lemma per_diff_of_pair_bound
    (r Cpair kA L x lx : ℝ)
    (hx : 0 < x) (hlx : 0 < lx) (hkA : 0 < kA)
    (hCpair : 0 ≤ Cpair)
    (hpair : r ≤ Cpair * x / lx ^ 2)
    (hlow : x / (kA * lx) ≤ L) :
    r ≤ (Cpair * kA ^ 2) * L ^ 2 / x := by
  sorry

/-- **Difference-Sieve prime instance — explicit energy ceiling from raw pair
    bounds.**
    For `i > 10^15`, `x = p_i`, `A = {p prime : 3 ≤ p ≤ x}`,
    `B = {p prime : x < p ≤ 2x}`.  Assume the citable raw prime-pair upper
    bounds with explicit constant `C_pair ≥ 0`:

      `r_{A-A}(h) ≤ C_pair · x / (log x)²`,
      `r_{B-B}(h) ≤ C_pair · x / (log x)²`  (`h ≠ 0`),

    the citable Chebyshev lower bounds with explicit constant `κ_A > 0`:

      `x / (κ_A · log x) ≤ |A|`,  `x / (κ_A · log x) ≤ |B|`,

    and the mass lower bound `x ≤ M`.  Then with `c₀ = C_pair · κ_A²` the
    additive energy obeys `E(A,B) ≤ (1 + 3 c₀²) · M² / x`. -/
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
  sorry

/-- **Difference-Sieve output (lower-bound form).**
    Under the raw pair bounds (constant `C_pair`), Chebyshev lower bounds
    (constant `κ_A`) and the mass bound, with `c₀ = C_pair·κ_A²` the distinct
    sumset satisfies `|C| ≥ x/(1 + 3 c₀²)`. -/
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
  sorry

/-- **Difference-Sieve output (explicit density form).**
    Under the raw pair bounds (constant `C_pair`), Chebyshev lower bounds
    (constant `κ_A`) and the mass bound, with `c₀ = C_pair·κ_A²` the distinct
    sumset satisfies `|C| > h·x` for every `h < 1/(1 + 3 c₀²)`.  Thus
    `h₀ = 1/(1 + 3 c₀²) > 0` is a first explicit positive density extracted
    from the raw (citable) prime-pair upper bound. -/
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
  sorry

/-- **Concrete numeric illustration.**
    Taking the (illustrative) explicit constants `C_pair = 16` and `κ_A = 2`,
    the transfer constant is `c₀ = 64`, the energy constant is
    `κ₀ = 1 + 3·64² = 12289`, and the realised explicit positive density is
    `h₀ = 1/12289`: `|C| ≥ (1/12289)·x`.  The numbers are placeholders for
    whatever explicit Selberg/Brun and Chebyshev constants one cites; the point
    is that any finite pair `(C_pair, κ_A)` yields a concrete finite `h₀ > 0`. -/
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
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §5.  Phase V — Unconditional Explicit Densities (Literature Constants)
-- ════════════════════════════════════════════════════════════════════════════

/-- **First fully-cited positive density theorem.**
    Under the raw prime-pair upper bound with constant C_pair_lit (cited:
    Selberg sieve, C_sieve=8, Montgomery–Vaughan Ch. 7; sup 𝔖(h) for x=10^15)
    and Chebyshev lower bound with constant kA_lit (cited: Dusart 2010,
    Theorem 1: π(x) > x/(log x - 1) for x ≥ 5393),
    the distinct sumset satisfies `|C| ≥ h₀_lit · x`, where
    `C_pair_lit = 67`, `kA_lit = 1`, `c₀ = 67`, `κ₀ = 13468`,
    `h₀ = 1/13468`. -/
theorem sumset_ge_cited_density {i : ℕ} (hi : i > trigger)
    (hpairA : ∀ h : ℤ, h ≠ 0 →
        (rSub (Aset (primeIdx i)) h : ℝ)
          ≤ C_pair_lit * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hpairB : ∀ h : ℤ, h ≠ 0 →
        (rSub (Bset (primeIdx i)) h : ℝ)
          ≤ C_pair_lit * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hlowA : (primeIdx i : ℝ) / (kA_lit * Real.log (primeIdx i))
          ≤ ((Aset (primeIdx i)).card : ℝ))
    (hlowB : (primeIdx i : ℝ) / (kA_lit * Real.log (primeIdx i))
          ≤ ((Bset (primeIdx i)).card : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    h0_lit * (primeIdx i : ℝ)
      ≤ ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §6.  Phase VI — Minor-Arc Integration (Circle Method)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Minor-arc energy identity (general form).**
    For arbitrary finite `A B : Finset ℤ`,
    `∫₀¹ ‖S A α‖² · ‖T B α‖² dα = E(A,B)`.

    This is the standard Parseval/orthogonality identity behind the circle
    method: expanding `‖S‖²‖T‖²` into a quadruple sum and using
    `∫₀¹ e(mα) dα = [m = 0]` collapses it to the count of additive quadruples
    `a₁+b₁ = a₂+b₂`, which is exactly `energy A B`.

    The identity is *unconditional* and holds for arbitrary finite
    `A B : Finset ℤ` (it does not use the trigger hypothesis). -/
theorem energy_eq_minor_arc_integral (A B : Finset ℤ) :
    (∫ α in (0:ℝ)..1, ‖S A α‖ ^ 2 * ‖T B α‖ ^ 2) = (energy A B : ℝ) := by
  sorry

/-- **Minor-arc energy bound (prime instance).**
    For every `i > 10^15`, with `x = pᵢ`, `A = Aset x`, `B = Bset x`,
    the additive energy equals the minor-arc `L²`-integral of the power spectra:

      `∫₀¹ ‖S A α‖² · ‖T B α‖² dα = E(A,B)`.

    This is the exact Parseval/orthogonality identity of the circle method; it
    holds unconditionally for all finite `A, B`, so the hypothesis
    `hi : i > trigger` (included as requested) is not used by the proof. -/
theorem minor_arc_energy_bound {i : ℕ} (hi : i > trigger) :
    ∫ α in (0:ℝ)..1,
        ‖S (Aset (primeIdx i)) α‖ ^ 2 * ‖T (Bset (primeIdx i)) α‖ ^ 2
      = (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) := by
  sorry

end PrimeSumset
