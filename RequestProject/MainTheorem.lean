import RequestProject.AdditiveEnergy
import RequestProject.Definitions
import RequestProject.ExplicitCounting
import RequestProject.ShortInterval
import RequestProject.EnergyUpperBound

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# Module 6 — `PrimeSumset.MainTheorem`

The main theorem of the blueprint (§1, Phase IV).  For every `i > 10^15` with
`x = pᵢ`, the distinct sumset `C = A + B` of `A = primes∩[3,x]` and
`B = primes∩(x,2x]` satisfies `|C| > 0.904·x`.

The proof assembles three ingredients:

* `mass_pos`                        — `M = |A|·|B| > 0`               (proved);
* `energy_ceiling`                  — `E ≤ κ·M²/x` with `κ = 1.1053`  (the single
                                       novel obligation, `sorry`);
* `sumset_card_ge_of_energy_ceiling`— Cauchy–Schwarz compression `M² ≤ |C|·E`
                                       turned into `|C| ≥ x/κ`        (proved).

Since `1/κ = 10000/11053 > 0.904`, the energy ceiling gives `|C| > 0.904·x`.
-/

namespace PrimeSumset

open Finset

/-- **Main Theorem.**  For every `i > 10^15`, with `x = pᵢ`,
`A = {p prime : 3 ≤ p ≤ x}` and `B = {p prime : x < p ≤ 2x}`, the distinct
sumset `C = A + B` satisfies `|C| > 0.904·x`.

The constant `0.904` is sharp for the available reproducing-kernel value
`κ = 1.1053`: `1/κ = 10000/11053 = 0.90473… > 0.904`.

Proven modulo the single novel obligation `energy_ceiling` (see
`RequestProject.EnergyUpperBound`); all other steps are machine-checked. -/
theorem sumset_card_gt_904 {i : ℕ} (hi : i > trigger) :
    0.904 * (primeIdx i : ℝ)
      < ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by omega
    exact_mod_cast this
  have hMpos : 0 < (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) := by
    exact_mod_cast mass_pos h3
  -- `|C| ≥ x/κ` with `κ = 1.1053`.
  have hge : (primeIdx i : ℝ) / (11053 / 10000)
      ≤ ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) :=
    sumset_card_ge_of_energy_ceiling _ _ _ _ hxpos (by norm_num) hMpos (energy_ceiling hi)
  -- `0.904·x < x/κ` since `0.904 < 1/κ = 10000/11053`.
  have hlt : 0.904 * (primeIdx i : ℝ) < (primeIdx i : ℝ) / (11053 / 10000) := by
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith [hxpos]
  linarith

/-- **Overlap (high-multiplicity) bound.**  For every `i > 10^15`, with
`x = pᵢ`, `A = primes∩[3,x]`, `B = primes∩(x,2x]`, and any `k ≥ 1`, the number
of sums `n ∈ C = A+B` represented at least `k` times satisfies
`#{n ∈ C : k ≤ r_{A+B}(n)} ≤ (10/9)·M²/(k²·x)`, where `M = |A|·|B|`.

This is the energy level-set (Chebyshev) bound: from Identity 1,
`#{…}·k² ≤ E(A,B)`, and the energy ceiling gives `E ≤ (1.1053)·M²/x ≤ (10/9)·M²/x`.
Proven modulo the single novel obligation `energy_ceiling`. -/
theorem overlap_bound {i : ℕ} (hi : i > trigger) (k : ℕ) (hk : 0 < k) :
    (#{n ∈ sumset (Aset (primeIdx i)) (Bset (primeIdx i)) |
        k ≤ rAdd (Aset (primeIdx i)) (Bset (primeIdx i)) n} : ℝ)
      ≤ (10/9 : ℝ) * (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) ^ 2
          / ((k : ℝ) ^ 2 * (primeIdx i : ℝ)) := by
  set A := Aset (primeIdx i)
  set B := Bset (primeIdx i)
  have h3 : 3 ≤ primeIdx i := three_le_primeIdx_of_trigger hi
  have hxpos : 0 < (primeIdx i : ℝ) := by
    have : 0 < primeIdx i := by omega
    exact_mod_cast this
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  -- Overlap count times k² bounded by the energy (cast to ℝ).
  have hcount : ((#{n ∈ sumset A B | k ≤ rAdd A B n} : ℕ) : ℝ) * (k : ℝ) ^ 2
      ≤ (energy A B : ℝ) := by
    have := overlap_card_mul_sq_le_energy A B k
    calc ((#{n ∈ sumset A B | k ≤ rAdd A B n} : ℕ) : ℝ) * (k : ℝ) ^ 2
        = (((#{n ∈ sumset A B | k ≤ rAdd A B n}) * k ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (energy A B : ℝ) := by exact_mod_cast this
  -- Energy ceiling, relaxed from 1.1053 to 10/9.
  have hE : (energy A B : ℝ)
      ≤ (10/9 : ℝ) * (mass A B : ℝ) ^ 2 / (primeIdx i : ℝ) := by
    have hceil := energy_ceiling hi
    have hMsq : 0 ≤ (mass A B : ℝ) ^ 2 := by positivity
    calc (energy A B : ℝ)
        ≤ (11053 / 10000 : ℝ) * (mass A B : ℝ) ^ 2 / (primeIdx i : ℝ) := hceil
      _ ≤ (10/9 : ℝ) * (mass A B : ℝ) ^ 2 / (primeIdx i : ℝ) := by
          apply div_le_div_of_nonneg_right ?_ hxpos.le
          nlinarith [hMsq]
  -- Combine: count·k² ≤ (10/9)·M²/x.
  have key : ((#{n ∈ sumset A B | k ≤ rAdd A B n} : ℕ) : ℝ) * (k : ℝ) ^ 2
      ≤ (10/9 : ℝ) * (mass A B : ℝ) ^ 2 / (primeIdx i : ℝ) := le_trans hcount hE
  rw [le_div_iff₀ hxpos] at key
  -- Conclude by dividing by k²·x > 0.
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (k : ℝ) ^ 2 * (primeIdx i : ℝ))]
  nlinarith [key]

end PrimeSumset
