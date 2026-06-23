import Mathlib

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# General additive energy combinatorics

This module develops the *general*, exact combinatorial identities and
inequalities behind the additive energy method, for arbitrary finite subsets
`A B : Finset ℤ`.  Nothing here uses primes or analytic number theory; these
are the "provable now" tools (Phase I / Phase II of the blueprint, Module 4
`PrimeSumset.AdditiveEnergy`).

* `rAdd A B n` — the representation function `r_{A+B}(n)`.
* `rSub A h`   — the representation function `r_{A-A}(h)`.
* `energy A B` — the additive energy `E(A,B)` as a count of quadruples.
* `sumset A B` — the distinct sumset `C = A + B` (pointwise).
* `mass A B`   — `M = |A|·|B|`.

Main results:

* `sum_rAdd`           : `∑_{n∈C} r_{A+B}(n) = M`.
* `energy_eq_sum_sq`   : `E(A,B) = ∑_{n∈C} r_{A+B}(n)²`            (Identity 1).
* `energy_eq_diff_corr`: `E(A,B) = ∑_{h} r_{A-A}(h)·r_{B-B}(-h)`  (Identity 2).
* `cauchy_schwarz_compression` : `M² ≤ |C|·E(A,B)`               (Phase I).
-/

namespace PrimeSumset

open Finset

/-- The representation function `r_{A+B}(n) = #{(a,b) ∈ A×B : a+b=n}`. -/
def rAdd (A B : Finset ℤ) (n : ℤ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = n)).card

/-- The (self) difference representation function `r_{A-A}(h) = #{(a,a') ∈ A×A : a-a'=h}`. -/
def rSub (A : Finset ℤ) (h : ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 - p.2 = h)).card

/-- The additive energy `E(A,B)`, as the exact count of quadruples
`(a₁,b₁,a₂,b₂) ∈ A×B×A×B` with `a₁+b₁=a₂+b₂`. -/
def energy (A B : Finset ℤ) : ℕ :=
  (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card

/-- The distinct sumset `C = A + B`. -/
def sumset (A B : Finset ℤ) : Finset ℤ := A + B

/-- The mass `M = |A|·|B|`. -/
def mass (A B : Finset ℤ) : ℕ := A.card * B.card

/-
The total mass is the sum of the representation function over the sumset:
`∑_{n∈C} r_{A+B}(n) = M`.
-/
lemma sum_rAdd (A B : Finset ℤ) :
    ∑ n ∈ sumset A B, rAdd A B n = mass A B := by
  unfold rAdd mass sumset;
  rw [ ← Finset.card_eq_sum_card_fiberwise ];
  · exact Finset.card_product _ _;
  · exact fun p hp => Finset.add_mem_add ( Finset.mem_product.mp hp |>.1 ) ( Finset.mem_product.mp hp |>.2 )

/-
**Identity 1 (sumset side).**  The additive energy equals the sum of squares
of the sumset representation function.
-/
lemma energy_eq_sum_sq (A B : Finset ℤ) :
    energy A B = ∑ n ∈ sumset A B, (rAdd A B n) ^ 2 := by
  unfold rAdd energy;
  -- By definition of sumset, we can rewrite the left-hand side as a sum over n in sumset A B.
  have h_sumset : {q ∈ (A ×ˢ B) ×ˢ A ×ˢ B | q.1.1 + q.1.2 = q.2.1 + q.2.2} = Finset.biUnion (sumset A B) (fun n => Finset.image (fun (p : (ℤ × ℤ) × (ℤ × ℤ)) => (p.1, p.2)) (Finset.filter (fun p => p.1 + p.2 = n) (A ×ˢ B) ×ˢ Finset.filter (fun p => p.1 + p.2 = n) (A ×ˢ B))) := by
    ext ⟨x, y⟩; simp [sumset];
    rw [ Finset.mem_add ] ; aesop;
  rw [ h_sumset, Finset.card_biUnion ];
  · simp +decide [ sq ];
  · intro n hn m hm hnm; simp_all +decide [ Finset.disjoint_left ] ;

/-- **Identity 2 (difference side).**  The additive energy equals the
difference correlation `∑_h r_{A-A}(h)·r_{B-B}(-h)`. -/
lemma energy_eq_diff_corr (A B : Finset ℤ) :
    energy A B = ∑ h ∈ (A - A), rSub A h * rSub B (-h) := by
  have hgroup : energy A B = ∑ h ∈ (A - A), (Finset.filter (fun q => q.1.1 - q.2.1 = h ∧ q.1.1 + q.1.2 = q.2.1 + q.2.2) ((A ×ˢ B) ×ˢ (A ×ˢ B))).card := by
    rw [ ← Finset.card_biUnion ];
    · convert rfl;
      congr with q;
      simp +decide [ Finset.mem_sub ];
      exact ⟨ fun ⟨ a, ha, b, hb, h, h', h'' ⟩ => ⟨ h, h'' ⟩, fun h => ⟨ q.1.1, h.1.1.1, q.2.1, h.1.2.1, h.1, rfl, h.2 ⟩ ⟩;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun q hq hq' => hxy <| by aesop;
  convert hgroup using 2;
  rw [ show { q ∈ ( A ×ˢ B ) ×ˢ A ×ˢ B | q.1.1 - q.2.1 = _ ∧ q.1.1 + q.1.2 = q.2.1 + q.2.2 } = ( Finset.filter ( fun p : ℤ × ℤ => p.1 - p.2 = ‹ℤ› ) ( A ×ˢ A ) ×ˢ Finset.filter ( fun p : ℤ × ℤ => p.1 - p.2 = -‹ℤ› ) ( B ×ˢ B ) ).image ( fun p : ( ℤ × ℤ ) × ℤ × ℤ => ( ( p.1.1, p.2.1 ), ( p.1.2, p.2.2 ) ) ) from ?_ ];
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    · rfl;
    · aesop;
  · ext ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩; simp [Finset.mem_image];
    grind

/-
**Level-set / overlap bound (Chebyshev for the energy).**

The number of sums `n ∈ C = A+B` with high multiplicity `r_{A+B}(n) ≥ k`
times `k²` never exceeds the additive energy:
`#{n ∈ C : k ≤ r_{A+B}(n)} · k² ≤ E(A,B)`.

This is immediate from Identity 1 `E = ∑_{n∈C} r_{A+B}(n)²`: each of the
counted `n` contributes at least `k²` to the energy.
-/
lemma overlap_card_mul_sq_le_energy (A B : Finset ℤ) (k : ℕ) :
    (#{n ∈ sumset A B | k ≤ rAdd A B n}) * k ^ 2 ≤ energy A B := by
  rw [energy_eq_sum_sq]
  calc
    (#{n ∈ sumset A B | k ≤ rAdd A B n}) * k ^ 2
        = ∑ _n ∈ {n ∈ sumset A B | k ≤ rAdd A B n}, k ^ 2 := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ n ∈ {n ∈ sumset A B | k ≤ rAdd A B n}, (rAdd A B n) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hk : k ≤ rAdd A B n := (Finset.mem_filter.mp hn).2
          exact Nat.pow_le_pow_left hk 2
    _ ≤ ∑ n ∈ sumset A B, (rAdd A B n) ^ 2 :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-
**Phase I — Cauchy–Schwarz compression.**  `M² ≤ |C|·E(A,B)`.
-/
lemma cauchy_schwarz_compression (A B : Finset ℤ) :
    (mass A B) ^ 2 ≤ (sumset A B).card * energy A B := by
  rw [ energy_eq_sum_sq A B ];
  have h_cauchy_schwarz : ∀ (s : Finset ℤ) (f : ℤ → ℕ), (∑ n ∈ s, f n : ℚ) ^ 2 ≤ (s.card : ℚ) * ∑ n ∈ s, f n ^ 2 := by
    intro s f; have := Finset.sum_le_sum fun i ( hi : i ∈ s ) => pow_two_nonneg ( f i - ( ∑ j ∈ s, f j : ℚ ) / s.card ) ; by_cases hs : s = ∅ <;> simp_all +decide [ sub_sq ] ;
    norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] at this;
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *; nlinarith [ mul_div_cancel₀ ( ∑ j ∈ s, ( f j : ℚ ) ) ( Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <| Classical.choose_spec <| Finset.nonempty_of_ne_empty hs ) ] ;
  convert h_cauchy_schwarz ( sumset A B ) ( fun n => rAdd A B n ) using 1 ; norm_cast;
  rw [ ← sum_rAdd ]

/-
**Phase I + Phase IV — the energy-method reduction.**

Given a real `x > 0`, positive mass `M = |A|·|B| > 0`, and an *energy ceiling*
`E(A,B) ≤ κ·M²/x` with `0 < κ < 10/9`, the distinct sumset satisfies
`|A+B| > 0.9·x`.

This is the purely logical heart of the blueprint: combine the Cauchy–Schwarz
compression `M² ≤ |C|·E` with the ceiling to get `|C| ≥ x/κ > (9/10)·x`.
-/
lemma sumset_lower_of_energy_ceiling (A B : Finset ℤ) (x κ : ℝ)
    (hx : 0 < x) (hM : 0 < (mass A B : ℝ)) (hκ : κ < 10 / 9)
    (hE : (energy A B : ℝ) ≤ κ * (mass A B : ℝ) ^ 2 / x) :
    0.9 * x < ((sumset A B).card : ℝ) := by
  -- From `cauchy_schwarz_compression A B` cast to ℝ we get `M^2 ≤ C * E`.
  have h1 : (mass A B : ℝ) ^ 2 ≤ (sumset A B).card * (energy A B : ℝ) := by
    exact_mod_cast cauchy_schwarz_compression A B;
  rw [ le_div_iff₀ hx ] at hE;
  nlinarith [ mul_lt_mul_of_pos_left hκ hM ]

/-
**Research-ladder reduction (general explicit constant).**

Given `x > 0`, positive mass `M = |A|·|B| > 0`, and an energy ceiling
`E(A,B) ≤ κ·M²/x` with *any* explicit `κ > 0`, the distinct sumset satisfies
`|A+B| ≥ x/κ`.

This is the parametric heart of the blueprint's research ladder (§6).  *Any*
explicit sieve constant `κ` immediately yields the explicit positive lower
bound `x/κ` (Success type D / Stage 1).  Driving `κ` downward improves the
constant; once `κ < 10/9` one recovers `|C| > 0.9·x`
(`sumset_lower_of_energy_ceiling`).
-/
lemma sumset_card_ge_of_energy_ceiling (A B : Finset ℤ) (x κ : ℝ)
    (hx : 0 < x) (hκ : 0 < κ) (hM : 0 < (mass A B : ℝ))
    (hE : (energy A B : ℝ) ≤ κ * (mass A B : ℝ) ^ 2 / x) :
    x / κ ≤ ((sumset A B).card : ℝ) := by
  have h1 : (mass A B : ℝ) ^ 2 ≤ (sumset A B).card * (energy A B : ℝ) := by
    exact_mod_cast cauchy_schwarz_compression A B
  have hC : 0 ≤ ((sumset A B).card : ℝ) := by positivity
  rw [ le_div_iff₀ hx ] at hE
  rw [ div_le_iff₀ hκ ]
  nlinarith [ mul_le_mul_of_nonneg_left hE hC, mul_le_mul_of_nonneg_left h1 hx.le,
              mul_pos hM hM ]

/-
**Research-ladder reduction (explicit fraction form).**

Under the same hypotheses, for any `h < 1/κ` we get the explicit density bound
`|A+B| > h·x`.  This is the exact statement shape the new blueprint targets
(`|C| > h·x` for an explicit constant `h`): an explicit sieve constant `κ`
produces the explicit constant `h = 1/κ` (any value strictly below it).
-/
lemma sumset_card_gt_of_energy_ceiling (A B : Finset ℤ) (x κ h : ℝ)
    (hx : 0 < x) (hκ : 0 < κ) (hM : 0 < (mass A B : ℝ))
    (hE : (energy A B : ℝ) ≤ κ * (mass A B : ℝ) ^ 2 / x)
    (hh : h < 1 / κ) :
    h * x < ((sumset A B).card : ℝ) := by
  have hge : x / κ ≤ ((sumset A B).card : ℝ) :=
    sumset_card_ge_of_energy_ceiling A B x κ hx hκ hM hE
  have hlt : h * x < x / κ := by
    rw [ div_eq_mul_one_div, mul_comm x (1 / κ) ]
    exact mul_lt_mul_of_pos_right hh hx
  linarith

end PrimeSumset