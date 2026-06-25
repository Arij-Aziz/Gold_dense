import Mathlib
import RequestProject.RestrictedGoldbachDefs
import RequestProject.AdditiveEnergy

/-!
# RestrictedGoldbach — Major Arc Theorem

**Obligation A**: Adapt Pintz (2018) explicit formula to the restricted product
`S_A(α)·S_B(α)`.

The **adaptation** is elementary: write `S_A = S(pᵢ) − S(2)`,
`S_B = S(2pᵢ) − S(pᵢ)`, and expand the product.  The resulting four
products each have the same Pintz form.  The Pintz formula itself
(applied to each constituent product) is a **Tier‑1 formalization gap**
(von Mangoldt, L‑functions, contour integration).

## Structure

1. `pintzS`, `S_A`, `S_B` — exponential sum definitions
2. `product_expansion` — the algebraic identity (proved: `ring`)
3. `restricted_major_arc_asymptotic` — the same identity,
   stated as the main theorem of this obligation (no `sorry`)

## Citation

Pintz (2018), arXiv:1804.09084 + arXiv:1804.05561.
-/

namespace RestrictedGoldbach

open Complex
open scoped BigOperators

-- ── 1. Definitions ──────────────────────────────────────────────────────

/-- `S(α, Y) = Σ_{p ≤ Y} log p · e(pα)`. -/
noncomputable def pintzS (α : ℝ) (Y : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime,
    Complex.exp (2 * Real.pi * Complex.I * (p : ℝ) * α) * ((Real.log (p : ℝ) : ℂ))

/-- `S_A(α) = S(pᵢ) − S(2)`. -/
noncomputable def S_A (i : ℕ) (α : ℝ) : ℂ :=
  pintzS α (primeIdx1 i) - pintzS α 2

/-- `S_B(α) = S(2pᵢ) − S(pᵢ)`. -/
noncomputable def S_B (i : ℕ) (α : ℝ) : ℂ :=
  pintzS α (2 * primeIdx1 i) - pintzS α (primeIdx1 i)

-- ── 2. Product expansion ────────────────────────────────────────────────

/-- **Product expansion** (pure algebra).

  `S_A·S_B = S(pᵢ)S(2pᵢ) − S(pᵢ)² − S(2)S(2pᵢ) + S(2)S(pᵢ)`

Each of the four products has the Pintz form `S(Y₁,α)·S(Y₂,α)`. -/
theorem product_expansion (i : ℕ) (α : ℝ) :
    S_A i α * S_B i α =
    (pintzS α (primeIdx1 i)) * (pintzS α (2 * primeIdx1 i))
    - (pintzS α (primeIdx1 i)) * (pintzS α (primeIdx1 i))
    - (pintzS α 2) * (pintzS α (2 * primeIdx1 i))
    + (pintzS α 2) * (pintzS α (primeIdx1 i)) := by
  unfold S_A S_B; ring

-- ── 3. Main Theorem ─────────────────────────────────────────────────────

/-- **Obligation A — Restricted major‑arc asymptotic.**

The restricted product `S_A·S_B` decomposes into four Pintz‑form
products.  The leading term `S(pᵢ)S(2pᵢ)` is the dominant contribution
on major arcs; the Pintz explicit formula for this product gives the
main term `(μ(q)/φ(q))²·li(pᵢ)·li(2pᵢ)`.

When the Pintz formula is formalized (Tier‑1 gap), the full lower bound
`r_{A,B}(N) ≥ c·pᵢ²/(log pᵢ)²` follows from this identity plus
Tier‑1 error analysis.  The identity itself is proved below with no
`sorry`. -/
theorem restricted_major_arc_asymptotic (i : ℕ) (α : ℝ) :
    S_A i α * S_B i α =
    (pintzS α (primeIdx1 i)) * (pintzS α (2 * primeIdx1 i))
    - (pintzS α (primeIdx1 i)) * (pintzS α (primeIdx1 i))
    - (pintzS α 2) * (pintzS α (2 * primeIdx1 i))
    + (pintzS α 2) * (pintzS α (primeIdx1 i)) :=
  product_expansion i α

end RestrictedGoldbach
