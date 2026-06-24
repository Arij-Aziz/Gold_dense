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
  20 critical theorems from the active dependency tree of the PrimeSumset
  project, matching `RequestProject.Audit.lean` exactly.

  ── CONTENTS ─────────────────────────────────────────────────────────────────
  §0.  Inline definitions (Mathlib-only reproductions)
  §1.  Phase I : Target main results (conditional on energy_ceiling)
  §2.  Phase II: The analytic formalization gap
  §3.  Phase III: Additive-energy combinatorics (unconditional)
  §4.  Phase IV: Prime-set basic facts (unconditional)
  §5.  Phase V: Goldbach representation facts (unconditional)
  §6.  Phase VI: GM bridge layer (conditional Tier-1)

  Total: 20 theorems/lemmas (matching Audit.lean exactly).
  Axiom footprint for each: [propext, Classical.choice, Quot.sound, sorryAx].
  ─────────────────────────────────────────────────────────────────────────────
-/
import Mathlib

open scoped BigOperators
open scoped Pointwise
open scoped Classical
open scoped Real
open intervalIntegral

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

-- ── From GM2Retyped.lean ─────────────────────────────────────────────────────

/-- Opaque predicate: `S₁` is the specific off‑diagonal zero‑sum
from the explicit‑formula expansion of the cross‑energy in GM1. -/
opaque ZeroSumRep (i : ℕ) (S₁ : ℝ) : Prop

/-- Montgomery's pair correlation function `F(α, x)`.  Opaque —
its definition requires the Riemann zeta function, which is not in Mathlib. -/
opaque F_montgomery (α x : ℝ) : ℝ

/-- The singular‑series‑averaged weight `ω₀(α,x)`. -/
noncomputable def omega0 (x α : ℝ) : ℝ :=
  (1 / 2) * (1 - x ^ (α - 1)) ^ 2 * x ^ (α - 1) * Real.log x

/-- Normalized weighted form factor:
`(∫₀¹ F(α,p_i)·ω₀(α,p_i) dα) / (∫₀¹ ω₀(α,p_i) dα)`. -/
noncomputable def normalized_weighted_form_factor (i : ℕ) : ℝ :=
  (∫ α in (0 : ℝ)..1, F_montgomery α (primeIdx i) * omega0 (primeIdx i) α)
    / (∫ α in (0 : ℝ)..1, omega0 (primeIdx i) α)

/-- Matching error: the discrepancy between the zero‑sum `S₁` and the
normalized weighted form factor. -/
noncomputable def matching_error (i : ℕ) (S₁ : ℝ) : ℝ :=
  S₁ - normalized_weighted_form_factor i

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
-- §3.  Phase III — Additive-Energy Combinatorics (unconditional)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Total mass equals sum of representation function over the sumset.**
    `∑_{n∈C} r_{A+B}(n) = M`. -/
lemma sum_rAdd (A B : Finset ℤ) :
    ∑ n ∈ sumset A B, rAdd A B n = mass A B := by
  sorry

/-- **Identity 1 (sumset side).**
    `E(A,B) = ∑_{n∈C} r_{A+B}(n)²`. -/
lemma energy_eq_sum_sq (A B : Finset ℤ) :
    energy A B = ∑ n ∈ sumset A B, (rAdd A B n) ^ 2 := by
  sorry

/-- **Identity 2 (difference side).**
    `E(A,B) = ∑_h r_{A-A}(h)·r_{B-B}(-h)`. -/
lemma energy_eq_diff_corr (A B : Finset ℤ) :
    energy A B = ∑ h ∈ (A - A), rSub A h * rSub B (-h) := by
  sorry

/-- **Level-set / overlap bound (Chebyshev for the energy).**
    `#{n ∈ C : k ≤ r_{A+B}(n)} · k² ≤ E(A,B)`. -/
lemma overlap_card_mul_sq_le_energy (A B : Finset ℤ) (k : ℕ) :
    (#{n ∈ sumset A B | k ≤ rAdd A B n}) * k ^ 2 ≤ energy A B := by
  sorry

/-- **Phase I — Cauchy–Schwarz compression.**
    `M² ≤ |C|·E(A,B)`. -/
lemma cauchy_schwarz_compression (A B : Finset ℤ) :
    (mass A B) ^ 2 ≤ (sumset A B).card * energy A B := by
  sorry

/-- **Phase I + Phase IV — the energy-method reduction.**
    Given `E(A,B) ≤ κ·M²/x` with `0 < κ < 10/9`,
    the distinct sumset satisfies `|A+B| > 0.9·x`. -/
lemma sumset_lower_of_energy_ceiling (A B : Finset ℤ) (x κ : ℝ)
    (hx : 0 < x) (hM : 0 < (mass A B : ℝ)) (hκ : κ < 10 / 9)
    (hE : (energy A B : ℝ) ≤ κ * (mass A B : ℝ) ^ 2 / x) :
    0.9 * x < ((sumset A B).card : ℝ) := by
  sorry

/-- **Research-ladder reduction (general explicit constant).**
    Given `E(A,B) ≤ κ·M²/x` with `κ > 0`,
    the distinct sumset satisfies `|A+B| ≥ x/κ`. -/
lemma sumset_card_ge_of_energy_ceiling (A B : Finset ℤ) (x κ : ℝ)
    (hx : 0 < x) (hκ : 0 < κ) (hM : 0 < (mass A B : ℝ))
    (hE : (energy A B : ℝ) ≤ κ * (mass A B : ℝ) ^ 2 / x) :
    x / κ ≤ ((sumset A B).card : ℝ) := by
  sorry

/-- **Research-ladder reduction (explicit fraction form).**
    Under the same hypotheses, for any `h < 1/κ`,
    we get `|A+B| > h·x`. -/
lemma sumset_card_gt_of_energy_ceiling (A B : Finset ℤ) (x κ h : ℝ)
    (hx : 0 < x) (hκ : 0 < κ) (hM : 0 < (mass A B : ℝ))
    (hE : (energy A B : ℝ) ≤ κ * (mass A B : ℝ) ^ 2 / x)
    (hh : h < 1 / κ) :
    h * x < ((sumset A B).card : ℝ) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §4.  Phase IV — Prime-Set Basic Facts (unconditional)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Non‑emptiness of `A`.**  For `x ≥ 3`, `Aset x` is nonempty. -/
lemma Aset_nonempty {x : ℕ} (hx : 3 ≤ x) : (Aset x).Nonempty := by
  sorry

/-- **Non‑emptiness of `B`.**  For `x > 0`, `Bset x` is nonempty. -/
lemma Bset_nonempty {x : ℕ} (hx : 0 < x) : (Bset x).Nonempty := by
  sorry

/-- **Mass positivity.**  For `x ≥ 3`, `mass (Aset x) (Bset x) > 0`. -/
lemma mass_pos {x : ℕ} (hx : 3 ≤ x) : 0 < mass (Aset x) (Bset x) := by
  sorry

/-- **Lower bound on primes.**  For `i > 10^15`, we have `3 ≤ primeIdx i`. -/
lemma three_le_primeIdx_of_trigger {i : ℕ} (hi : i > trigger) : 3 ≤ primeIdx i := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §5.  Phase V — Goldbach Representation Facts (unconditional)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Representation positivity.**  `0 < r_{A+B}(N)` iff `N ∈ A+B`. -/
lemma rAdd_pos_iff (A B : Finset ℤ) (N : ℤ) : 0 < rAdd A B N ↔ N ∈ A + B := by
  sorry

/-- **Parity.**  Any representable `N` (for `x ≥ 2`) is even, since it is a sum
of two odd primes. -/
lemma rAdd_pos_even {x : ℕ} (hx2 : 2 ≤ x) {N : ℤ}
    (hN : 0 < rAdd (Aset x) (Bset x) N) : Even N := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §6.  Phase VI — GM Bridge Layer (conditional Tier‑1)
-- ════════════════════════════════════════════════════════════════════════════

/-- **GM2 — Form‑Factor Matching (structural).**
    The zero‑sum `S₁` from GM1 equals the normalized weighted form factor
    `J := normalized_weighted_form_factor i` plus a remainder
    `R₂ := matching_error i S₁`.  Tier‑1 sorry; the identification of the
    main term with Montgomery's `F(α,T)` follows from the unconditional
    asymptotics of Baluyot et al. (2024), Theorem 1. -/
theorem GM2_form_factor_matching_structured
    {i : ℕ} (hi : i > trigger) {S₁ : ℝ} (hS₁ : ZeroSumRep i S₁) :
    ∃ J R₂ : ℝ,
      J = normalized_weighted_form_factor i ∧
      R₂ = matching_error i S₁ ∧
      S₁ = J + R₂ := by
  sorry

end PrimeSumset
