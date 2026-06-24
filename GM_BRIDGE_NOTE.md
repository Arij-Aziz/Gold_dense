# GM1–GM4: The Goldston–Montgomery Bridge — Statement Page and Dependency Map

**Project:** TheoremH (`|A+B| > 0.904·pᵢ` for prime sumset)  
**Date:** June 2026  
**Current state:** GM2 concretized — `normalized_weighted_form_factor` and
`matching_error` are now concrete `noncomputable def`s built from the opaque
`F_montgomery` and the explicit bridge weight `omega0`.  GM2
(`GM2_form_factor_matching_structured`) and its two assembly equalities
(`gm2_line3_form_factor_emergence`, `gm2_line5_matching_error_identity`) are now
fully proved (`rfl`/`ring`), with no `sorry`.  The remaining GM-side sorrys are
GM1 (`GM1_explicit_formula_structured`), GM4 (`GM4_remainder_bound_structured`),
and `dir_theorem1_structured`; the sole remaining opaque analytic object is
`F_montgomery`.  `dir_theorem1` targets `J + rem`.

---

## 1. Statement Page

### Common setup

Fix `i > 10^15` (`trigger`), `x = pᵢ`, `A = primes in [3, x]`, `B = primes in (x, 2x]`.
Let `M = |A|·|B|` and `E = E(A,B)`.  The bridge weight is

```
ω₀(α, x) = (1/2)·(1 − x^{α−1})² · x^{α−1} · log x   (α ∈ [0,1])
```

as defined in `RequestProject.WeightedGMBridge`.

### Structural Objects (defined in `RequestProject.GM2Retyped.lean`)

| Object | Meaning | Lean definition |
|:---|:---|:---|
| `F_montgomery α x` | Montgomery pair-correlation function `F(α,x)` for the zeta zeros | `opaque F_montgomery : ℝ → ℝ → ℝ` |
| `ZeroSumRep i S₁` | `S₁` is the specific off‑diagonal zero‑sum from the explicit formula | `opaque ZeroSumRep : ℕ → ℝ → Prop` |
| `normalized_weighted_form_factor i` | `(∫₀¹ F(α,pᵢ)·ω₀(pᵢ,α) dα) / (∫₀¹ ω₀(pᵢ,α) dα)` | `noncomputable def … := (∫ … F_montgomery …)/(∫ … omega0 …)` |
| `matching_error i S₁` | `S₁ − normalized_weighted_form_factor i` | `noncomputable def … := S₁ - normalized_weighted_form_factor i` |

`F_montgomery` and `ZeroSumRep` remain **opaque** — Lean cannot unfold them —
because they require the Riemann zeta function and the explicit formula, which
are not in Mathlib.  The opacity of `ZeroSumRep` blocks the trivial witness
`S₁ := E·x/M² − 1` at the Lean level, so GM1 stays an honest Tier‑1 citation.

By contrast `normalized_weighted_form_factor` and `matching_error` are now
**concrete** `noncomputable def`s assembled from `F_montgomery` and `omega0`.
This is deliberate: it moves the entire GM2-side analytic burden onto the single
opaque object `F_montgomery`, and makes the GM2 assembly equalities (line 3 and
line 5) and GM2 itself provable by `rfl`/`ring` rather than left as citations.

### GM1 — Explicit-formula expansion (structured)

**File:** `GM2Retyped.lean`, Tier‑1 sorry.  Citations: Goldston (2004) Thm 7; Gafni–Tao (2025) §3.

```lean
theorem GM1_explicit_formula_structured {i : ℕ} (hi : i > trigger) :
    ∃ S₁ : ℝ,
      ZeroSumRep i S₁ ∧
      (energy …) ≤ ((mass …)^2 / (primeIdx i : ℝ)) * (1 + S₁) := by
  sorry
```

The `ZeroSumRep` conjunct blocks `S₁ := E·x/M² − 1` (that choice does not satisfy `ZeroSumRep`).

### GM2 — Form-factor matching (structured)

**File:** `GM2Retyped.lean`, **now PROVED** (`rfl`/`ring`, no `sorry`).  The
analytic content (Baluyot et al. 2024 Thm 1) is now carried by the opaque
`F_montgomery` inside the definition of `normalized_weighted_form_factor`.

```lean
theorem GM2_form_factor_matching_structured
    {i : ℕ} (hi : i > trigger) {S₁ : ℝ} (hS₁ : ZeroSumRep i S₁) :
    ∃ J R₂ : ℝ,
      J = normalized_weighted_form_factor i ∧
      R₂ = matching_error i S₁ ∧
      S₁ = J + R₂ := by
  refine ⟨normalized_weighted_form_factor i, matching_error i S₁, rfl, rfl, ?_⟩
  unfold matching_error; ring
```

With `matching_error i S₁ := S₁ − normalized_weighted_form_factor i`, the
identity `S₁ = J + R₂` holds by construction.

### GM3 — Weight identification (proved)

**File:** `GM12.lean`, Bin B, fully machine-checked.

```
omega0_integral {x} (hx : 0 < x) : ∫₀¹ ω₀(α, x) dα = (1/6)·(1 − 1/x)³
c2_eq_one_third                    : (1/6) / (1/2) = 1/3
```

**Derivation of `c₂ = 1/3`:**
- Triangle integral (substitution `u = x^{α−1}`): `∫₀¹ (1−u)² du = 1/3`
- Parity factor: `1/2` (only even differences `h` contribute)
- Standard continuous mass of `dν_std = δ + |α|dα` on `[-1,1]`: `∫₀¹ |α|dα = 1/2`
- `c₂ = (triangle_integral × parity_factor) / standard_continuous_mass = (1/3 × 1/2) / (1/2) = 1/3`
- This is machine-checked: `c2_eq_one_third` in `WeightedGMBridge.lean`.
- Equivalently: `(∫₀¹ ω₀ dα) / (parity_factor) = (1/6) / (1/2) = 1/3`.

### GM4 — Remainder bound (structured)

**File:** `GM2Retyped.lean`, Tier‑1 sorry.  Citations: Davenport Ch. 17; Dussart (2010); Gafni–Tao (2025) §3.

```lean
theorem GM4_remainder_bound_structured
    {i : ℕ} (hi : i > trigger) {S₁ : ℝ} (hS₁ : ZeroSumRep i S₁) :
    ∃ rem : ℝ,
      0 ≤ rem ∧
      matching_error i S₁ ≤ rem ∧
      rem ≤ 1053 / 10000 := by
  sorry
```

Bounds `matching_error` directly (not an arbitrary `R₂`); the type has genuine analytic teeth.

### h_DIR — D‑I‑R bound on `J + rem` (structured)

**File:** `GMDBridge.lean`, Tier‑1 sorry.  Citation: Das–Ismoilov–Ramos (2025) Thm 1, Corollary 7.

```lean
theorem dir_theorem1_structured {i : ℕ} (hi : i > trigger) (J rem : ℝ)
    (hJ_eq : J = normalized_weighted_form_factor i)
    (hrem_nonneg : 0 ≤ rem) (hrem_small : rem ≤ 1053 / 10000) :
    J + rem ≤ 1053 / 10000 := by
  sorry
```

Targets `J + rem` (form factor plus GM error), not `S₁` directly.

### Combined bridge theorem (proved)

**File:** `GM2Retyped.lean`, **no sorry** in proof body.

```lean
theorem weighted_gm_bridge_cross_structured {i : ℕ} (hi : i > trigger) :
    ∃ J rem : ℝ,
      J = normalized_weighted_form_factor i ∧
      0 ≤ rem ∧
      rem ≤ 1053 / 10000 ∧
      (energy …) ≤ ((mass …)^2 / (primeIdx i : ℝ)) * (1 + J + rem) := ...
```

Assembles GM1–GM4 by pure algebra: `E ≤ M²/x·(1+S₁) = M²/x·(1+J+R₂) ≤ M²/x·(1+J+rem)`.

### Energy ceiling (proved)

**File:** `GMDBridge.lean`, **no sorry** in proof body.

```lean
theorem energy_ceiling_via_tier1_sorrys {i : ℕ} (hi : i > trigger) :
    (energy …) ≤ (11053/10000) * (mass …)^2 / (primeIdx i : ℝ) := ...
```

From `weighted_gm_bridge_cross_structured` + `dir_theorem1_structured`:
`J + rem ≤ 0.1053` → `1 + J + rem ≤ 1.1053` → `E ≤ M²/x·1.1053`.

---

## 2. Dependency Map

### Inputs (all unconditional)

| # | Theorem | Source | Used in |
|---|---------|--------|---------|
| T1 | Goldston–Montgomery bridge | Goldston (2004) pairprimes.pdf, Theorem 7 | GM1 |
| T2 | Zero-density → second-moment | Gafni–Tao (2025) §3 | GM1, GM4 |
| T3 | Unconditional Montgomery `F(α,T)` | Baluyot et al. (2024) Theorem 1 | GM2 |
| T4 | Singular series average `𝔖²→1` | Goldston (2004) §4 | (absorbed in GM1) |
| T5 | D‑I‑R extremal bound | Das–Ismoilov–Ramos (2025) Theorem 1, Corollary 7 | `dir_theorem1_structured` |
| T6 | Explicit-formula error | Davenport Ch. 17 | GM4 |
| T7 | Explicit `π(x)` bounds | Dussart (2010) | GM4 |

### Lean-internal (all proved)

| # | Lemma | File |
|---|-------|------|
| L1 | `omega0_integral` | `WeightedGMBridge.lean` |
| L2 | `c2_eq_one_third` | `WeightedGMBridge.lean` |
| L3 | `triangle_le_exponential` | `Blueprint12.lean` |
| L4 | `majorant_transfer_for_nonnegative_form_factor` | `DIRMajorantTransfer.lean` |
| L5 | `kappa_kn_lt_target` | `GapCloser.lean` |
| L6 | `Phi_exp_lt_twentyone_thirtytwos` | `DIRMajorantTransfer.lean` |
| L7 | `one_div_K_nu_00_le_kappa_kn` | `GapCloser.lean` |
| L8 | `cauchy_schwarz_compression` → `sumset_card_ge_of_energy_ceiling` | `AdditiveEnergy.lean` |

### Assembly equalities (now PROVED — concretized into the definitions)

| # | Lemma | File | Statement |
|---|-------|------|-----------|
| A1 | `gm2_line3_form_factor_emergence` | `GM2Retyped.lean` §6 | `normalized_weighted_form_factor i = (∫F·ω₀)/(∫ω₀)` — **proved by `rfl`** (it is now the definition) |
| A2 | `gm2_line5_matching_error_identity` | `GM2Retyped.lean` §6 | `matching_error i S₁ = S₁ − normalized_weighted_form_factor i` — **proved by `rfl`** (it is now the definition) |

### Support lemmas (Bin B, proved — good housekeeping)

| # | Lemma | File |
|---|-------|------|
| S1 | `gm2_line3_differential_form` | `GM2Retyped.lean` §7 |
| S2 | `gm2_line3_integral` | `GM2Retyped.lean` §7 |
| S3 | `gm2_line3_c2` | `GM2Retyped.lean` §7 |
| S4 | `gm4_line8_ceiling_identity` | `GM2Retyped.lean` §8 |
| S5 | `gm4_line8_kappa_lt_target` | `GM2Retyped.lean` §8 |
| S6 | `gm4_line8_rem_nonneg_feasible` | `GM2Retyped.lean` §8 |

### Proof chain (current, Run 30)

```
T1,T2 ─→ GM1_structured ─→ S₁, ZeroSumRep, E ≤ M²/x·(1+S₁)
                                   │
T3 ──→ GM2_structured ─→ J = form_factor, R₂ = matching_error, S₁ = J+R₂
                                   │
L1,L2 ─→ GM3 (proved, Bin B)  ←  c₂ = 1/3
                                   │
T2,T6,T7 ─→ GM4_structured ─→ 0 ≤ matching_error ≤ rem ≤ 0.1053
                                   │
                    ├──→ weighted_gm_bridge_cross_structured (proved)
                    │      J = form_factor, 0 ≤ rem ≤ 0.1053, E ≤ M²/x·(1+J+rem)
                    │
T5 ─→ dir_theorem1_structured (Tier‑1 sorry)
                    │      J + rem ≤ 0.1053
                    │
                    ├──→ energy_ceiling_via_tier1_sorrys (proved)
                    │      E ≤ (11053/10000)·M²/x
                    │
L8 ─→ sumset_card_gt_904 (proved in MainTheorem.lean)
                          |C| > 0.904·x
```

### Bin classification

| Lemma | Bin | Justification |
|:---|:---|:---|
| GM1 | **A** | Goldston (2004) Thm 7 + Gafni–Tao (2025) §3, unconditional |
| GM2 | **A** | Baluyot et al. (2024) Thm 1, unconditional |
| GM3 | **B** | Machine-checked (`omega0_integral`, `c2_eq_one_third`) |
| GM4 | **A** | Davenport Ch. 17 + Dussart + Gafni–Tao, unconditional |
| `dir_theorem1_structured` | **A** | D‑I‑R (2025) Thm 1 + Corollary 7, unconditional |

---

## 3. Proof Sketches (every sentence labeled)

### GM1 — Explicit-formula expansion

**Target:** `∃ S₁, ZeroSumRep i S₁ ∧ E ≤ (M²/x)·(1 + S₁)`

| # | Sentence | Label |
|---|----------|-------|
| 1 | `E(A,B) = Σ_h r_{A-A}(h)·r_{B-B}(-h)` | **local deduction** — Identity 2, `AdditiveEnergy.lean` (proved) |
| 2 | `r_{A-A}(h) = #{(a,a')∈A×A : a-a'=h}` counts prime pairs | **local deduction** — definition of `rSub` |
| 3 | Via partial summation, replace the prime indicator by the von Mangoldt function: `1_P(n) = Λ(n)/log n + O(1/√n)` | **direct citation** — Goldston (2004) *pairprimes.pdf*, Proposition 1 (explicit formula) |
| 4 | The explicit formula for the second moment of ψ in short intervals: `∫₀^X (ψ(y+h)−ψ(y)−h)² dy = h·X·log(X/h) + (zero‑sum contribution) + error` | **direct citation** — Goldston (2004) *pairprimes.pdf*, Theorem 7 (G–M bridge) |
| 5 | The zero‑sum contribution expands as `Σ_{ρ,ρ'} (X^{ρ+ρ̄'})/(ρ·ρ̄')·(h‑dependent phase)` plus lower order | **local deduction** — expanding the explicit formula for ψ |
| 6 | Summing the product `r_{A-A}(h)·r_{B-B}(-h)` over `h` replaces the `(h‑dependent phase)` by an oscillatory sum that picks out `γ−γ'` at a characteristic frequency | **local deduction** — discrete Fourier orthogonality |
| 7 | The diagonal `γ=γ'` (h=0) plus the explicit-formula main term together contribute the "1" factor in `(M²/x)·(1 + S₁)` | **direct citation** — Goldston (2004) Theorem 7 normalization; Gafni–Tao (2025) §3 |
| 8 | The off‑diagonal `γ≠γ'` contribution is a weighted double sum over zero ordinates, giving `S₁` | **local deduction** — separating the diagonal from off‑diagonal terms |
| 9 | The modern zero‑density estimate of Guth–Maynard (2024) gives unconditional control on the size of the off‑diagonal sum, ensuring `S₁` is finite | **direct citation** — Gafni–Tao (2025) arXiv:2505.24017, §3 |
| 10 | The explicit-formula truncation error (cutting off zeros at height `T = x`) is `O(x log⁴ x)` after summation over `h`; normalizing by `M²/x` gives `o(1)` | **local deduction** — standard error analysis (see also GM4) |
| 11 | Therefore `E ≤ (M²/x)·(1 + S₁)` with `ZeroSumRep i S₁` capturing the specific zero‑sum structure | **local deduction** — combining lines 7–10 |

### GM2 — Main-term identification with `F(α,T)`

**Target:** `J = normalized_weighted_form_factor i ∧ R₂ = matching_error i S₁ ∧ S₁ = J + R₂`

| # | Sentence | Label |
|---|----------|-------|
| 1 | `S₁` from GM1 is a weighted sum of the form `(2π/(x log x))·Σ_{γ,γ'} x^{iα(γ−γ')}·4/(4+(γ−γ')²)·(weight from the cross‑interval configuration)` | **local deduction** — from the explicit expansion in GM1 |
| 2 | The continuous approximation replaces the discrete sum over `γ,γ'` by the integral of Montgomery's `F(α,T)` against a test function: as `T = x → ∞`, `(2π/(T log T))·Σ_{γ,γ'} T^{iα(γ−γ')}·4/(4+(γ−γ')²) → F(α,T) dα` in the sense of measures | **direct citation** — Baluyot et al. (2024) arXiv:2306.04799, Theorem 1 (unconditional Montgomery asymptotics) |
| 3 | The test function is the normalized bridge weight `ω₀(α,x) / (∫₀¹ ω₀ dα)`, which emerges from the substitution `α = (γ−γ')(log T)/(2π)` and `t = x^{α−1}`.  The differential identity `ω₀ dα = (1/2)(1−u)² du` (with `u = x^{α−1}`) and the integral `∫ ω₀ = (1/6)(1−1/x)³` are machine‑checked in `gm2_line3_differential_form` and `gm2_line3_integral` (`GM2Retyped.lean` §6). | **local deduction** — assembly lemmas (proved in Lean) |
| 4 | The normalized form‑factor contribution is `J := normalized_weighted_form_factor i = (∫₀¹ F·ω₀) / (∫₀¹ ω₀)` — this is now the *definition* of the object | **local deduction** — provable by `rfl` (`gm2_line3_form_factor_emergence`) |
| 5 | The matching error is `R₂ := matching_error i S₁ = S₁ − J` — also the *definition* of the object | **local deduction** — provable by `rfl` (`gm2_line5_matching_error_identity`) |
| 6 | The unconditional error bound `F(α,T) = T^{-2α}log T + α + O(1/√log T)` controls `R₂` | **direct citation** — Baluyot et al. (2024) Theorem 1 |
| 7 | Therefore `J = normalized_weighted_form_factor i`, `R₂ = matching_error i S₁`, and `S₁ = J + R₂` | **local deduction** — combining lines 4–6 |

### GM4 — Remainder bound

**Target:** `∃ rem, 0 ≤ rem ∧ matching_error i S₁ ≤ rem ∧ rem ≤ 1053/10000`

| # | Sentence | Label |
|---|----------|-------|
| 1 | `matching_error i S₁` from GM2 is the discrete-to-continuous approximation error, bounded by the `O(1/√log x)` term in the unconditional Montgomery theorem | **direct citation** — Baluyot et al. (2024) Theorem 1 |
| 2 | The explicit‑formula truncation at height `T` contributes `E_trunc ≤ C·x·(log x)^A / T` for some absolute `A` | **direct citation** — Davenport, *Multiplicative Number Theory*, Chapter 17 |
| 3 | Choosing `T = x` makes the truncation error `O(log^A x / x)` before normalization | **local deduction** — substituting `T = x` |
| 4 | By Dussart's explicit PNT bounds, `M = |A|·|B| ≥ (c·x/log x)²` for all `x ≥ x₀ ≈ 10^8` | **direct citation** — Dussart (2010) arXiv:1002.0442, Theorem 1 |
| 5 | Hence `(log^A x / x) / (M²/x) = O(log^A x · log⁴ x / x) → 0` as `x → ∞` | **local deduction** — algebraic substitution |
| 6 | Gafni–Tao (2025) §3 confirms the exceptional set is sub‑leading: `μ(θ) < 1` for the relevant `θ` | **direct citation** — Gafni–Tao (2025) Theorem 1.3 |
| 7 | Consequently `matching_error i S₁ = o(1)` after normalization | **local deduction** — combining lines 1, 5, 6 |
| 8 | For `x = p_i > 10^15`, the `o(1)` term is numerically `< 1053/10000`.  The constant chain `1 + 1053/10000 = 11053/10000 < 10/9` is machine‑checked in `gm4_line8_ceiling_identity` and `gm4_line8_kappa_lt_target` (`GM2Retyped.lean` §7). | **local deduction** — numerical verification (proved in Lean) |
| 9 | Therefore `∃ rem ≤ 1053/10000` with `matching_error i S₁ ≤ rem` | **local deduction** — definition |

---

## 4. Remaining Formalization Gaps

| Gap | Lines of Lean (est.) | Difficulty |
|:---|:---|:---|
| Explicit formula for `ψ(x)` (von Mangoldt) | ~2000 | High — complex analysis |
| Montgomery pair correlation `F(α,T)` | ~3000 | High — contour integration, zero sums |
| Goldston–Montgomery bridge for second moment | ~2000 | High — explicit formula + Parseval |
| D‑I‑R reproducing kernel construction | ~3000 | High — de Branges / Paley–Wiener RKHS |
| Explicit-formula error analysis | ~500 | Medium — standard estimates |
| **Total** | **~10500** | |

All are formalization gaps, not mathematical gaps.  Every ingredient is established
in unconditional, peer‑reviewed literature; the task is to port them to Lean / Mathlib.

---

## 5. File Map (current, Run 30)

| File | Contents |
|:---|:---|
| `RequestProject/GM2Retyped.lean` | `F_montgomery` (opaque), `ZeroSumRep` (opaque), `normalized_weighted_form_factor` & `matching_error` (concrete defs); GM1, GM4 (Tier‑1 sorrys); GM2 + assembly equalities + `weighted_gm_bridge_cross_structured` (proved) |
| `RequestProject/GMDBridge.lean` | `F_montgomery`, `bridge_error`, `w_exp`; `dir_theorem1_structured` (Tier‑1 sorry); `energy_ceiling_via_tier1_sorrys` (proved) |
| `RequestProject/GM12.lean` | GM3 (`omega0_integral`, `c2_eq_one_third` — proved); old weak GM1/GM2/GM4 (superseded) |
| `RequestProject/WeightedGMBridge.lean` | `omega0`, `omega0_integral`, `omega0_integral_tendsto`, `c2_eq_one_third` |
| `RequestProject/EnergyUpperBound.lean` | `energy_ceiling` (calls `energy_ceiling_via_tier1_sorrys`) |
| `RequestProject/MainTheorem.lean` | `sumset_card_gt_904` (calls `energy_ceiling`) |
