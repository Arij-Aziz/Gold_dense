/-
  Challenge.lean
  ===============
  Auditable statement file for the RequestProject.

  ── HOW TO USE ─────────────────────────────────────────────────────────────
  This file has ONE import: `import Mathlib`.
  No `RequestProject.*` imports appear anywhere.

  Every theorem is stated with its verbatim signature from the source file,
  with `sorry` as the proof body. All project-internal definitions are
  reproduced inline below using only Mathlib primitives, so a reviewer can
  verify every statement is well-typed without building the project.

  To check: `lake build Challenge`
  Expected: zero errors; only `declaration uses sorry` warnings (intended).

  ── SCOPE ──────────────────────────────────────────────────────────────────
  20 theorems matching `Audit.lean` exactly (ordered by importance).

  ── CONTENTS ───────────────────────────────────────────────────────────────
  §0.  Inline definitions (Mathlib-only reproductions)
  §1.  Best result: 0.99107 density                  (4 theorems)
  §2.  Original 0.95 density                          (2 theorems)
  §3.  Tier‑1 analytic gap                            (1 theorem)
  §4.  Combinatorial backbone                         (2 theorems)
  §5.  Additive-energy combinatorics                  (5 theorems)
  §6.  Set combinatorics                              (3 theorems)
  §7.  Obligation A                                   (1 theorem)
  §8.  Basic membership / positivity                  (2 theorems)

  Total: 20 theorems (matching Audit.lean exactly).
  ───────────────────────────────────────────────────────────────────────────
-/
import Mathlib

open scoped BigOperators
open scoped Pointwise
open scoped Classical

noncomputable section

-- ══════════════════════════════════════════════════════════════════════════
-- §0.  Inline definitions (Mathlib primitives only)
-- ══════════════════════════════════════════════════════════════════════════

-- ── Shared namespace: PrimeSumset  ───────────────────────────────────────

namespace PrimeSumset

open Finset

/- The representation function r_{A+B}(n) = #{(a,b) ∈ A×B : a+b=n}. -/
def rAdd (A B : Finset ℤ) (n : ℤ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = n)).card

/- The difference representation function r_{A-A}(h) = #{(a,a') ∈ A×A : a-a'=h}. -/
def rSub (A : Finset ℤ) (h : ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 - p.2 = h)).card

/- The additive energy E(A,B), counting quadruples (a₁,b₁,a₂,b₂) with a₁+b₁ = a₂+b₂. -/
def energy (A B : Finset ℤ) : ℕ :=
  (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card

/- The distinct sumset C = A + B. -/
def sumset (A B : Finset ℤ) : Finset ℤ := A + B

/- The mass M = |A|·|B|. -/
def mass (A B : Finset ℤ) : ℕ := A.card * B.card

/- The trigger threshold of the blueprint: i > 10^15. -/
def trigger : ℕ := 10 ^ 15

/- The i‑th prime pᵢ (0‑indexed: primeIdx 0 = 2, primeIdx 1 = 3, …). -/
noncomputable def primeIdx (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/- A = {p prime : 3 ≤ p ≤ x}, as a finite set of integers. -/
noncomputable def Aset (x : ℕ) : Finset ℤ :=
  (((Finset.Icc 3 x).filter (fun n => Nat.Prime n)).image (fun n => (n : ℤ)))

/- B = {p prime : x < p ≤ 2x}, as a finite set of integers. -/
noncomputable def Bset (x : ℕ) : Finset ℤ :=
  (((Finset.Ioc x (2 * x)).filter (fun n => Nat.Prime n)).image (fun n => (n : ℤ)))

end PrimeSumset

-- ── Shared namespace: RestrictedGoldbach  ─────────────────────────────────

namespace RestrictedGoldbach

open Finset

/- The i‑th prime, 1‑indexed: p₁ = 2, p₂ = 3, … -/
noncomputable def primeIdx1 (i : ℕ) : ℕ := PrimeSumset.primeIdx (i - 1)

/- A = {p prime : 3 ≤ p ≤ pᵢ}, using PrimeSumset.Aset. -/
noncomputable def Aset (i : ℕ) : Finset ℤ := PrimeSumset.Aset (primeIdx1 i)

/- B = {p prime : pᵢ < p ≤ 2pᵢ}, using PrimeSumset.Bset. -/
noncomputable def Bset (i : ℕ) : Finset ℤ := PrimeSumset.Bset (primeIdx1 i)

/- r_{A,B}(N) = #{(a,b) ∈ A×B : a+b = N} -/
noncomputable def restricted_repr (i N : ℕ) : ℕ :=
  PrimeSumset.rAdd (Aset i) (Bset i) (N : ℤ)

/- Eₓ = {even N ∈ (pᵢ, 3pᵢ] : r_{A,B}(N) = 0}. -/
noncomputable def ExceptionalSet (i : ℕ) : Finset ℕ :=
  let pi := primeIdx1 i
  filter (fun n : ℕ =>
    n % 2 = 0 ∧ pi < n ∧ n ≤ 3 * pi ∧ restricted_repr i n = 0)
    (Ico (pi + 1) (3 * pi + 1))

/- Pintz exponential sum: S(α, Y) = Σ_{p ≤ Y} log p · e(pα). -/
noncomputable def pintzS (α : ℝ) (Y : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime,
    Complex.exp (2 * Real.pi * Complex.I * (p : ℝ) * α) * ((Real.log (p : ℝ) : ℂ))

/- Restricted sum: S_A(α) = S(pᵢ) − S(2). -/
noncomputable def S_A (i : ℕ) (α : ℝ) : ℂ :=
  pintzS α (primeIdx1 i) - pintzS α 2

/- Restricted sum: S_B(α) = S(2pᵢ) − S(pᵢ). -/
noncomputable def S_B (i : ℕ) (α : ℝ) : ℂ :=
  pintzS α (2 * primeIdx1 i) - pintzS α (primeIdx1 i)

end RestrictedGoldbach

-- ══════════════════════════════════════════════════════════════════════════
-- §1.  Best result: 0.99107 density  (most important)
--      Sources: RestrictedGoldbachImproved.lean, Goldbach.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace RestrictedGoldbach

open Finset

/- **sumset_card_gt_111_div_112** (1‑indexed, strongest constant)
   For i > 10^15, |C| > (111/112)·pᵢ ≈ 0.99107·pᵢ. -/
theorem sumset_card_gt_111_div_112 {i : ℕ} (hi : 10 ^ 15 < i) :
    ((111 : ℝ) / 112) * (primeIdx1 i : ℝ) <
    ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) := by
  sorry

end RestrictedGoldbach

namespace PrimeSumset

open Finset

/- **sumset_card_gt_111_div_112** (0‑indexed framing)
   For i > 10^15, |sumset(Aset(pᵢ), Bset(pᵢ))| > (111/112)·pᵢ. -/
theorem sumset_card_gt_111_div_112 {i : ℕ} (hi : i > trigger) :
    ((111 : ℝ) / 112) * (primeIdx i : ℝ) <
    ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  sorry

/- **goldbach_density_improved**
   For i > 10^15, the number of representable N ∈ (pᵢ, 3pᵢ] exceeds (111/112)·pᵢ. -/
theorem goldbach_density_improved {i : ℕ} (hi : i > trigger) :
    ((111 : ℝ) / 112) * (primeIdx i : ℝ) <
    (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
       0 < rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N} : ℝ) := by
  sorry

/- **goldbach_exception_bound_improved**
   For i > 10^15, even non‑representable N ∈ (pᵢ, 3pᵢ] count < (1/112)·pᵢ. -/
theorem goldbach_exception_bound_improved {i : ℕ} (hi : i > trigger) :
    (#{N ∈ Finset.Ioc ((primeIdx i : ℤ)) (3 * primeIdx i) |
       Even N ∧ rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) N = 0} : ℝ) <
    ((1 : ℝ) / 112) * (primeIdx i : ℝ) := by
  sorry

end PrimeSumset

-- ══════════════════════════════════════════════════════════════════════════
-- §2.  Original 0.95 density
--      Sources: RestrictedGoldbachMain.lean, MainTheorem.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace RestrictedGoldbach

open Finset

/- **sumset_card_gt_95** (1‑indexed, original constant)
   Conditional on `restricted_exceptional_bound`. -/
theorem sumset_card_gt_95 {i : ℕ} (hi : 10 ^ 15 < i) :
    (0.95 : ℝ) * (primeIdx1 i : ℝ) <
    ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) := by
  sorry

end RestrictedGoldbach

namespace PrimeSumset

open Finset

/- **sumset_card_gt_95** (0‑indexed framing)
   Wraps `RestrictedGoldbach.sumset_card_gt_95` into 0‑indexed framing. -/
theorem sumset_card_gt_95 {i : ℕ} (hi : i > trigger) :
    0.95 * (primeIdx i : ℝ) <
    ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  sorry

end PrimeSumset

-- ══════════════════════════════════════════════════════════════════════════
-- §3.  Tier‑1 analytic gap
--      Source: RestrictedGoldbachExceptionalSet.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace RestrictedGoldbach

open Finset

/- **restricted_exceptional_bound** (Tier‑1 gap)
   The exceptional set cardinality is below pᵢ/20.
   Depends on Pintz circle method + Obligations A,B. -/
theorem restricted_exceptional_bound {i : ℕ} (hi : 10 ^ 15 < i) :
    (ExceptionalSet i).card < (1/20 : ℝ) * (primeIdx1 i : ℝ) := by
  sorry

end RestrictedGoldbach

-- ══════════════════════════════════════════════════════════════════════════
-- §4.  Combinatorial backbone
--      Source: RestrictedGoldbachCombinatorics.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace RestrictedGoldbach

open Finset

/- **card_sumset_eq_pi_sub_eset**
   |C| = pᵢ − |Eₓ| (equality in ℕ). -/
theorem card_sumset_eq_pi_sub_eset {i : ℕ} (hi : 10 ^ 15 < i) :
    ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℕ) =
    (primeIdx1 i : ℕ) - (ExceptionalSet i).card := by
  sorry

/- **sumset_card_ge_pi_sub_eset**
   |C| ≥ pᵢ − |Eₓ| (inequality in ℝ). -/
theorem sumset_card_ge_pi_sub_eset {i : ℕ} (hi : 10 ^ 15 < i) :
    (primeIdx1 i : ℝ) - ((ExceptionalSet i).card : ℝ) ≤
    ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) := by
  sorry

end RestrictedGoldbach

-- ══════════════════════════════════════════════════════════════════════════
-- §5.  Additive-energy combinatorics
--      Source: AdditiveEnergy.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace PrimeSumset

open Finset

/- **cauchy_schwarz_compression**  (Phase I)
   M² ≤ |C|·E(A,B). -/
lemma cauchy_schwarz_compression (A B : Finset ℤ) :
    (mass A B) ^ 2 ≤ (sumset A B).card * energy A B := by
  sorry

/- **sumset_card_ge_of_energy_ceiling**  (Research-ladder reduction)
   Given x > 0, κ > 0, and energy ceiling E ≤ κ·M²/x,
   the distinct sumset satisfies |A+B| ≥ x/κ. -/
lemma sumset_card_ge_of_energy_ceiling (A B : Finset ℤ) (x κ : ℝ)
    (hx : 0 < x) (hκ : 0 < κ) (hM : 0 < (mass A B : ℝ))
    (hE : (energy A B : ℝ) ≤ κ * (mass A B : ℝ) ^ 2 / x) :
    x / κ ≤ ((sumset A B).card : ℝ) := by
  sorry

/- **energy_eq_sum_sq**  (Identity 1)
   E(A,B) = ∑_{n∈C} r_{A+B}(n)². -/
lemma energy_eq_sum_sq (A B : Finset ℤ) :
    energy A B = ∑ n ∈ sumset A B, (rAdd A B n) ^ 2 := by
  sorry

/- **energy_eq_diff_corr**  (Identity 2)
   E(A,B) = ∑_{h} r_{A-A}(h)·r_{B-B}(-h). -/
lemma energy_eq_diff_corr (A B : Finset ℤ) :
    energy A B = ∑ h ∈ (A - A), rSub A h * rSub B (-h) := by
  sorry

/- **sum_rAdd**
   The total mass equals the sum of the representation function over the sumset:
   ∑_{n∈C} r_{A+B}(n) = M. -/
lemma sum_rAdd (A B : Finset ℤ) :
    ∑ n ∈ sumset A B, rAdd A B n = mass A B := by
  sorry

end PrimeSumset

-- ══════════════════════════════════════════════════════════════════════════
-- §6.  Set combinatorics
--      Source: RestrictedGoldbachCombinatorics.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace RestrictedGoldbach

open Finset

/- **add_Aset_Bset_even**
   Every sum a+b with a∈Aset, b∈Bset is even. -/
lemma add_Aset_Bset_even {i : ℕ} {a b : ℤ}
    (ha : a ∈ Aset i) (hb : b ∈ Bset i) : (a + b) % 2 = (0 : ℤ) := by
  sorry

/- **add_Aset_Bset_range**
   Every sum a+b with a∈Aset, b∈Bset lies in (pᵢ, 3pᵢ]. -/
lemma add_Aset_Bset_range {i : ℕ} {a b : ℤ}
    (ha : a ∈ Aset i) (hb : b ∈ Bset i) :
    (primeIdx1 i : ℤ) < a + b ∧ a + b ≤ (3 : ℤ) * (primeIdx1 i : ℤ) := by
  sorry

/- **card_evens_Ico**
   The number of even integers in Ico(pᵢ+1, 3pᵢ+1) is exactly pᵢ. -/
lemma card_evens_Ico (pi : ℕ) :
    ((Ico (pi + 1) (3 * pi + 1)).filter (fun n : ℕ => n % 2 = 0)).card = pi := by
  sorry

end RestrictedGoldbach

-- ══════════════════════════════════════════════════════════════════════════
-- §7.  Obligation A — major‑arc asymptotic
--      Source: RestrictedGoldbachMajorArc.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace RestrictedGoldbach

open Finset

/- **restricted_major_arc_asymptotic**  (Obligation A)
   The restricted product decomposes into four Pintz‑form products:
   S_A·S_B = S(pᵢ)S(2pᵢ) − S(pᵢ)² − S(2)S(2pᵢ) + S(2)S(pᵢ).
   Each product has the same Pintz explicit formula structure. -/
theorem restricted_major_arc_asymptotic (i : ℕ) (α : ℝ) :
    S_A i α * S_B i α =
    (pintzS α (primeIdx1 i)) * (pintzS α (2 * primeIdx1 i))
    - (pintzS α (primeIdx1 i)) * (pintzS α (primeIdx1 i))
    - (pintzS α 2) * (pintzS α (2 * primeIdx1 i))
    + (pintzS α 2) * (pintzS α (primeIdx1 i)) := by
  sorry

end RestrictedGoldbach

-- ══════════════════════════════════════════════════════════════════════════
-- §8.  Basic membership / positivity
--      Sources: RestrictedGoldbachDefs.lean
-- ══════════════════════════════════════════════════════════════════════════

namespace RestrictedGoldbach

open Finset

/- **rAdd_pos_iff**
   0 < r_{A,B}(N) exactly when N lies in the pointwise sumset. -/
lemma rAdd_pos_iff {i N : ℕ} :
    0 < PrimeSumset.rAdd (Aset i) (Bset i) (N : ℤ) ↔
    (N : ℤ) ∈ PrimeSumset.sumset (Aset i) (Bset i) := by
  sorry

/- **primeIdx1_pos**
   The 1‑indexed prime pᵢ is positive for i ≥ 2. -/
lemma primeIdx1_pos {i : ℕ} (hi : 2 ≤ i) : 0 < primeIdx1 i := by
  sorry

end RestrictedGoldbach
