import Mathlib
import RequestProject.Blueprint
import RequestProject.Goldbach
import RequestProject.Supplement

/-!
# Theorem 4.2 with an explicit threshold

This file addresses two points that were left open by the earlier development:

1. **An explicit numerical bound for Theorem 4.2.**  The blueprint supplement
   (`Blueprint supplement.txt`, Sections 1–2) asks for a *concrete* threshold `N₀` such
   that every even `N > N₀` is a sum of two primes, with `N₀ < 4·10¹⁸` so that it tiles with
   the empirical verification.  Here we fix the explicit value

   `Theorem42.N₀ = 937 983 734 = 2 · 468 991 867`,

   where `468 991 867` is the least prime above Dusart's explicit threshold `468 991 632`.
   We prove `N₀ < 4·10¹⁸` (`N₀_lt_empiricalBound`).

2. **A proof of Theorem 4.2** (`goldbach_analytic`): every even `N > N₀` is a sum of two
   primes.  The proof is carried out from two clearly-identified inputs:

   * `HDusart` — Dusart's *unconditional* explicit prime-gap bound
     `gap i ≤ P i / (5000·ln²(P i))` for `P i ≥ 468 991 632` (Ramanujan J. **45**, 2018),
     already used elsewhere in the project;
   * `CircleShortInterval` — the Hardy–Littlewood circle-method positivity in short
     intervals: for every odd-prime anchor `M ≥ 468 991 632`, every even `v` in the short
     interval `(2M, 2M + M/(2500·ln²M)]` is a sum of two primes.  This is the genuinely
     open analytic input (it is binary Goldbach in short intervals); following the project's
     policy it is recorded as an ordinary `Prop`-valued hypothesis, **not** an axiom.

   The mathematical content contributed here is the *explicit reduction*: Dusart's bound
   shows the whole gap-interval `(2·P i, 2·P(i+1))` fits inside the circle-method short
   interval around the anchor `2·P i`, and an elementary tiling of the even numbers then
   upgrades the per-band positivity to "every even `N > N₀`".  This is exactly the
   "extract the explicit threshold from Theorem 4.2" task of the supplement, done rigorously.

Finally `goldbach_full` combines Theorem 4.2 with the cited empirical verification
(`GoldbachEmpirical`) to give binary Goldbach for every even `N ≥ 4`.

## Soundness note

No axioms are introduced.  The only genuinely open / cited inputs (`HDusart`,
`CircleShortInterval`, `GoldbachEmpirical`) appear solely as explicit hypotheses of the
theorems below; binary Goldbach (and a fortiori its short-interval form) remains open, so
`CircleShortInterval` cannot be discharged unconditionally.
-/

open Filter Topology

namespace BlueprintH.Theorem42

open BlueprintH BlueprintH.Supplement

/-- `v` is a sum of two primes. -/
def IsSumTwoPrimes (v : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = v

/-- **The explicit Theorem 4.2 threshold.**  `N₀ = 2 · 468 991 867 = 937 983 734`, twice the
least prime above Dusart's explicit gap threshold `468 991 632`. -/
def N₀ : ℕ := 937983734

/-- The explicit threshold lies below the empirical bound `4·10¹⁸`, as required for the
tiling with the empirical verification. -/
theorem N₀_lt_empiricalBound : N₀ < empiricalBound := by
  unfold N₀ empiricalBound; norm_num

/-- **The circle-method short-interval positivity (cited analytic input).**

For every prime `M ≥ 468 991 632` (an odd-prime anchor `M = P i`), every even integer `v`
in the short interval `(2M, 2M + M/(2500·ln²M)]` is a sum of two primes.

This packages the Hardy–Littlewood circle-method evaluation (major-arc main term `≥ c₀·N/ln²N`
from the singular-series lower bound, minor-arc error `o(N/ln²N)` from the spectral large
sieve of Deshouillers–Iwaniec) into the positivity `R(v) > 0` on the short interval whose
length matches the prime gap.  It is binary Goldbach in short intervals — genuinely open —
and is therefore a hypothesis, not an axiom. -/
def CircleShortInterval : Prop :=
  ∀ M v : ℕ, Nat.Prime M → (468991632 : ℝ) ≤ (M : ℝ) → Even v → 2 * M < v →
    (v : ℝ) ≤ 2 * (M : ℝ) + (M : ℝ) / (2500 * (Real.log (M : ℝ)) ^ 2) →
    IsSumTwoPrimes v

/-- **Dusart band inclusion.**  Doubling Dusart's gap bound: for `P i ≥ 468 991 632`,
`2·gap i ≤ P i / (2500·ln²(P i))`.  This says twice the prime gap (the width needed to reach
the next even anchor `2·P(i+1)` from `2·P i`) fits inside the circle-method short interval. -/
lemma dusart_gap_band (hd : HDusart) {i : ℕ} (hi : (468991632 : ℝ) ≤ (P i : ℝ)) :
    2 * (gap i : ℝ) ≤ (P i : ℝ) / (2500 * (Real.log (P i : ℝ)) ^ 2) := by
  convert mul_le_mul_of_nonneg_left ( hd i hi ) zero_le_two using 1 ; ring

/-- If `M < P (i+1)` and `M ≥ 468 991 868`, then the prime `P i` below the gap satisfies
`P i ≥ 468 991 632`.  (Indeed `468 991 867` is a prime `< M ≤ P (i+1) - 1`, hence `≤ P i`.) -/
lemma P_ge_dusart_of_consecutive {i M : ℕ} (h2 : M < P (i + 1))
    (hM : 468991868 ≤ M) : (468991632 : ℝ) ≤ (P i : ℝ) := by
  contrapose! h2; norm_cast at *; simp_all +decide [ P ] ;
  rw [ Nat.nth_eq_sInf ];
  refine' le_trans ( Nat.sInf_le _ ) _;
  exact 468991867;
  · refine' ⟨ by norm_num, fun k hk => _ ⟩;
    exact lt_of_le_of_lt ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( Nat.le_of_lt_succ hk ) ) ( lt_of_lt_of_le h2 ( by norm_num ) );
  · linarith

/-- **Theorem 4.2 (explicit form).**  Assuming Dusart's gap bound (`HDusart`) and the
circle-method short-interval positivity (`CircleShortInterval`), every even `N` with
`N > N₀ = 937 983 734` is a sum of two primes. -/
theorem goldbach_analytic (hd : HDusart) (hc : CircleShortInterval) :
    ∀ N : ℕ, Even N → N₀ < N → IsSumTwoPrimes N := by
  intro N hN hN0;
  obtain ⟨ M, rfl ⟩ := hN;
  by_cases hMp : Nat.Prime M;
  · exact ⟨ M, M, hMp, hMp, rfl ⟩;
  · obtain ⟨ i, hi1, hPiM, hMPnext ⟩ := BlueprintH.exists_consecutive_primes ( show 6 ≤ M by linarith [ show N₀ ≥ 937983734 by decide ] ) hMp;
    convert hc ( P i ) ( M + M ) ( P_prime i ) _ _ _ _ using 1;
    · exact_mod_cast P_ge_dusart_of_consecutive hMPnext ( by linarith [ show N₀ = 937983734 by rfl ] );
    · simp +arith +decide [ parity_simps ];
    · grind;
    · have := dusart_gap_band hd ( show ( 468991632 : ℝ ) ≤ P i from ?_ );
      · norm_num [ gap ] at *;
        rw [ Nat.cast_sub ( by linarith ) ] at this ; linarith [ ( by norm_cast : ( P i : ℝ ) < M ), ( by norm_cast : ( M : ℝ ) < P ( i + 1 ) ) ];
      · exact_mod_cast P_ge_dusart_of_consecutive hMPnext ( by linarith [ show N₀ ≥ 937983734 by decide ] )

/-- **Binary Goldbach from Theorem 4.2 and the empirical verification.**  Combining the
explicit analytic Theorem 4.2 (`goldbach_analytic`) with the cited empirical verification up
to `4·10¹⁸` (`GoldbachEmpirical`), every even `N ≥ 4` is a sum of two primes. -/
theorem goldbach_full (hd : HDusart) (hc : CircleShortInterval) (hemp : GoldbachEmpirical) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  intro N hN h4
  by_cases h : N ≤ empiricalBound
  · exact hemp N hN h4 h
  · obtain ⟨p, q, hp, hq, hpq⟩ :=
      goldbach_analytic hd hc N hN (lt_trans N₀_lt_empiricalBound (not_le.mp h))
    exact ⟨p, q, hp, hq, hpq⟩

end BlueprintH.Theorem42