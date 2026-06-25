import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions
import RequestProject.RestrictedGoldbachDefs
import RequestProject.RestrictedGoldbachCombinatorics
import RequestProject.RestrictedGoldbachMajorArc
import RequestProject.RestrictedGoldbachSingularSeries
import RequestProject.RestrictedGoldbachExceptionalSet
import RequestProject.RestrictedGoldbachMain
import RequestProject.MainTheorem
import RequestProject.Goldbach
import RequestProject.RestrictedGoldbachImproved

/-!
# Axiom audit

This module imports every file directly needed by the twenty most important
theorems of the development and runs `#print axioms` on each.
Running this file prints, for each theorem, the exact set of axioms it
transitively depends on.

Reading the output:

* Theorems depending only on `propext`, `Classical.choice`, `Quot.sound`
  are fully machine-checked.
* Theorems whose dependency list contains `sorryAx` rest on the project's
  remaining Tier-1 analytic citation burden (`restricted_exceptional_bound`).
-/

-- ## §1 — Main results: strongest density (0.99107 = 111/112)

-- Strongest bound, 1‑indexed
#check RestrictedGoldbach.sumset_card_gt_111_div_112
#print axioms RestrictedGoldbach.sumset_card_gt_111_div_112

-- Strongest bound, 0‑indexed
#check PrimeSumset.sumset_card_gt_111_div_112
#print axioms PrimeSumset.sumset_card_gt_111_div_112

-- Goldbach density (111/112)
#check PrimeSumset.goldbach_density_improved
#print axioms PrimeSumset.goldbach_density_improved

-- Goldbach exceptional-set bound (1/112)
#check PrimeSumset.goldbach_exception_bound_improved
#print axioms PrimeSumset.goldbach_exception_bound_improved

-- ## §2 — Main results: original density (0.95)

-- Original bound, 1‑indexed
#check RestrictedGoldbach.sumset_card_gt_95
#print axioms RestrictedGoldbach.sumset_card_gt_95

-- Original bound, 0‑indexed
#check PrimeSumset.sumset_card_gt_95
#print axioms PrimeSumset.sumset_card_gt_95

-- ## §3 — Tier‑1 analytic gap (Pintz circle method, cited)

#check RestrictedGoldbach.restricted_exceptional_bound
#print axioms RestrictedGoldbach.restricted_exceptional_bound

-- ## §4 — Combinatorial backbone

-- Main combinatorial identity: |C| = pᵢ − |Eₓ|
#check RestrictedGoldbach.card_sumset_eq_pi_sub_eset
#print axioms RestrictedGoldbach.card_sumset_eq_pi_sub_eset

-- Inequality form in ℝ
#check RestrictedGoldbach.sumset_card_ge_pi_sub_eset
#print axioms RestrictedGoldbach.sumset_card_ge_pi_sub_eset

-- ## §5 — Additive-energy combinatorics

-- Cauchy–Schwarz compression: M² ≤ |C|·E
#check PrimeSumset.cauchy_schwarz_compression
#print axioms PrimeSumset.cauchy_schwarz_compression

-- Research‑ladder reduction: |C| ≥ x/κ
#check PrimeSumset.sumset_card_ge_of_energy_ceiling
#print axioms PrimeSumset.sumset_card_ge_of_energy_ceiling

-- Identity 1: E = Σ r²
#check PrimeSumset.energy_eq_sum_sq
#print axioms PrimeSumset.energy_eq_sum_sq

-- Identity 2: E = Σ r_A·r_B
#check PrimeSumset.energy_eq_diff_corr
#print axioms PrimeSumset.energy_eq_diff_corr

-- Fundamental sum identity: Σ r = M
#check PrimeSumset.sum_rAdd
#print axioms PrimeSumset.sum_rAdd

-- ## §6 — Set combinatorics

-- Parity: every sum a+b is even
#check RestrictedGoldbach.add_Aset_Bset_even
#print axioms RestrictedGoldbach.add_Aset_Bset_even

-- Range: a+b ∈ (pᵢ, 3pᵢ]
#check RestrictedGoldbach.add_Aset_Bset_range
#print axioms RestrictedGoldbach.add_Aset_Bset_range

-- Even count in the target interval
#check RestrictedGoldbach.card_evens_Ico
#print axioms RestrictedGoldbach.card_evens_Ico

-- ## §7 — Obligation A: major‑arc asymptotic

#check RestrictedGoldbach.restricted_major_arc_asymptotic
#print axioms RestrictedGoldbach.restricted_major_arc_asymptotic

-- ## §8 — Basic membership / positivity

-- Membership: 0 < r_{A+B}(N) ↔ N ∈ A+B
#check RestrictedGoldbach.rAdd_pos_iff
#print axioms RestrictedGoldbach.rAdd_pos_iff

-- Positivity of 1‑indexed prime
#check RestrictedGoldbach.primeIdx1_pos
#print axioms RestrictedGoldbach.primeIdx1_pos
