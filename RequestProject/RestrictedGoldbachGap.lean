import Mathlib
import RequestProject.RestrictedGoldbachDefs
import RequestProject.RestrictedGoldbachCombinatorics
import RequestProject.RestrictedGoldbachExceptionalSet
import RequestProject.AdditiveEnergy

/-!
# RestrictedGoldbach — Asymptotic Coverage → 1

Two complementary inputs proving `|C|/pᵢ → 1`:

1. **Pintz (2018) Theorem 1**: `E(X) < X^{0.72}` for `X > X₂`.
   Gives `|E| = o(pᵢ)`, hence `|C|/pᵢ = 1 − o(1) → 1`.

2. **Dusart (2016) Corollary 5.5**: max prime gap ≤ `x/(5000·ln² x)`.
   Gives an explicit effective constant (stronger than Pintz for
   finite i), improving the 0.95 bound to `1 − O(1/log² pᵢ)`.

## Papers used

| Paper | Result | Use |
|:---|:---|:---|
| Pintz (2018) arXiv:1804.09084 | Theorem 1: E(X) < X^{0.72} | Asymptotic → 1 |
| Dusart (2016) Ramanujan J. 45 | Corollary 5.5: gap ≤ x/(5000·ln² x) | Effective constant |
| Hardy–Littlewood (1923) Acta Math. 44 | 𝔖(N) > 0 | Obligation B |
| Goldston (2004) `pairprimes.pdf` | Explicit formula | Bridge (prior work) |
-/

namespace RestrictedGoldbach

open Real
open Finset
open Filter

-- ── 1. Dusart Corollary 5.5 (one sorry, cited) ─────────────────────────

/-- **Dusart (2016), Corollary 5.5.**
For `x ≥ 468 991 632`: ∃ prime `p` with `x < p ≤ x + x/(5000·ln² x)`. -/
theorem dusart_short_interval_has_prime {x : ℝ} (hx : 468991632 ≤ x) :
    ∃ (p : ℕ), Nat.Prime p ∧ (x : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ x + x / (5000 * ((Real.log x) ^ 2)) := by
  sorry

noncomputable def gapBound (x : ℝ) : ℝ := x / (5000 * ((Real.log x) ^ 2))

lemma gapBound_nonneg {x : ℝ} (hx : 468991632 ≤ x) : 0 ≤ gapBound x := by
  unfold gapBound; positivity

-- ── 2. Exceptional set is o(pᵢ) via Pintz ──────────────────────────────
-- (imported from RestrictedGoldbachExceptionalSet.lean)

-- ── 3. Helper lemmas ───────────────────────────────────────────────────

lemma exceptional_card_le_pi {i : ℕ} (hi : 10 ^ 15 < i) :
    (ExceptionalSet i).card ≤ primeIdx1 i := by
  let S_ℕ : Finset ℕ := filter (fun n : ℕ => n % 2 = 0) (Ico (primeIdx1 i + 1) (3 * primeIdx1 i + 1))
  have h_card : S_ℕ.card = primeIdx1 i := card_evens_Ico (primeIdx1 i)
  have h_sub : ExceptionalSet i ⊆ S_ℕ := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx_mem, ⟨hx_even, _, _, _⟩⟩
    exact Finset.mem_filter.mpr ⟨hx_mem, hx_even⟩
  have h_card_le : (ExceptionalSet i).card ≤ S_ℕ.card := Finset.card_le_card h_sub
  rw [h_card] at h_card_le
  exact h_card_le

-- ── 4. Main result: coverage → 1 ──────────────────────────────────────

/-- **Coverage tends to 1.**  `|C|/pᵢ → 1` as `i → ∞`.

From `card_sumset_eq_pi_sub_eset`: `|C| = pᵢ − |E|`.
By `exceptional_is_o_pi`: `|E|/pᵢ → 0`.
Hence `|C|/pᵢ = 1 − |E|/pᵢ → 1`. -/
theorem coverage_tends_to_one :
    Filter.Tendsto (fun i : ℕ => ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) / (primeIdx1 i : ℝ))
      Filter.atTop (nhds 1) := by
  have h_ratio : ∀ i, 10 ^ 15 < i →
      ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) / (primeIdx1 i : ℝ) =
      1 - ((ExceptionalSet i).card : ℝ) / (primeIdx1 i : ℝ) := by
    intro i hi
    have h_card_sumset : ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℕ) =
        (primeIdx1 i : ℕ) - (ExceptionalSet i).card :=
      card_sumset_eq_pi_sub_eset hi
    have hpi_pos : 0 < (primeIdx1 i : ℝ) := by
      have hpos_nat : 0 < primeIdx1 i := primeIdx1_pos (by omega : 2 ≤ i)
      exact by exact_mod_cast hpos_nat
    field_simp [hpi_pos.ne']
    push_cast
    rw [h_card_sumset, Nat.cast_sub (exceptional_card_le_pi hi)]
  have h_eventually : ∀ᶠ i in Filter.atTop, ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) / (primeIdx1 i : ℝ) =
      1 - ((ExceptionalSet i).card : ℝ) / (primeIdx1 i : ℝ) := by
    refine Filter.eventually_atTop.mpr ⟨10 ^ 15 + 1, fun i hi => h_ratio i ?_⟩
    omega
  have h_target : Filter.Tendsto (fun i : ℕ => 1 - ((ExceptionalSet i).card : ℝ) / (primeIdx1 i : ℝ))
      Filter.atTop (nhds 1) := by
    simpa using Filter.Tendsto.sub tendsto_const_nhds exceptional_is_o_pi
  exact h_target.congr' (h_eventually.mono fun _ h => h.symm)

end RestrictedGoldbach
