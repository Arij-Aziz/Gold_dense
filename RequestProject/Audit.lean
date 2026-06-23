import Mathlib
import RequestProject.MainTheorem
import RequestProject.Goldbach
import RequestProject.EnergyUpperBound
import RequestProject.ResearchLadder
import RequestProject.DifferenceSieve
import RequestProject.ConcreteConstants
import RequestProject.MinorArc

/-!
# Project Audit File

This file isolates the 15 most critical theorems of the active dependency tree
for the PrimeSumset project.

By checking the axioms of each theorem, you can verify exactly which results
are strictly machine-checked and which results currently depend on the isolated
formalization gap (`energy_ceiling` / `sorryAx`).
-/

namespace PrimeSumset

/-!
## Phase I: The Target Main Results (Conditional on Formalization Gap)
These theorems establish the > 0.904 density and the Goldbach bounds.
Because they depend on `energy_ceiling`, `#print axioms` will output `sorryAx`.
-/

#print axioms sumset_card_gt_904

#print axioms overlap_bound

#print axioms goldbach_exception_bound

#print axioms goldbach_density

/-!
## Phase II: The Analytic Formalization Gap
This is the single isolated assumption driving the main results above.
It encodes the D-I-R (2025) reproducing-kernel bound.
`#print axioms` will output `sorryAx`.
-/

#print axioms energy_ceiling


/-!
## Phase III: The Research Ladder (Unconditional Reductions)
These theorems strictly prove that *any* sieve ceiling bounds the additive energy.
They are completely isolated from the formalization gap.
`#print axioms` will be clean (no `sorryAx`).
-/

#print axioms sumset_card_ge_of_sieve_ceiling

#print axioms sumset_card_gt_const_of_sieve_ceiling


/-!
## Phase IV: Unconditional Difference Sieve Application
These theorems prove the algebraic transfer from raw prime-pair bounds
(Selberg/Brun) into the exact per-difference energy bounds required.
`#print axioms` will be entirely clean (no `sorryAx`).
-/

#print axioms per_diff_of_pair_bound

#print axioms energy_ceiling_of_prime_pair_sieve

#print axioms sumset_card_ge_of_prime_pair_sieve

#print axioms sumset_card_gt_of_prime_pair_sieve

#print axioms sumset_card_gt_of_prime_pair_sieve_concrete


/-!
## Phase V: Unconditional Explicit Densities (Literature Constants)
These theorems plug literature-derived constants (e.g., C_pair = 67, kA = 1)
into the difference sieve to extract a genuine, unconditionally verified positive density.
`#print axioms` will be entirely clean (no `sorryAx`).
-/

#print axioms sumset_ge_cited_density


/-!
## Phase VI: Minor-Arc Integration (Circle Method)
These theorems prove the exact Parseval/orthogonality identity equating the
additive energy to the minor-arc integral.
`#print axioms` will be completely clean (no `sorryAx`).
-/

#print axioms energy_eq_minor_arc_integral

#print axioms minor_arc_energy_bound

end PrimeSumset
