import Mathlib

/-!
# Theorem H : `h(i) = n(Cᵢ)/p'ᵢ → 1`

This file formalizes the blueprint *"h(i) → 1 as p'ᵢ → ∞"*.

## Definitions (corrected per the author's clarification)

Let `p'₁ < p'₂ < …` be the odd primes (`p'₁ = 3`).  We index by `Nat.nth Nat.Prime`,
so `P i = Nat.nth Nat.Prime i` gives `P 0 = 2`, `P 1 = 3 = p'₁`, `P 2 = 5 = p'₂`, …;
for `i ≥ 1`, `P i = p'ᵢ`.

* `A i = { p prime | 3 ≤ p ≤ P i }`
* `B i = { p prime | P i < p ≤ 2·P(i+1) − 5 }`     (lower bound `P i`, **exclusive**)
* `C i = { a + b | a ∈ A i, b ∈ B i }`              (distinct sums)
* `h i = (C i).card / P i`

NOTE.  An earlier draft of the blueprint wrote the lower bound of `B` as `2·P i + 2`,
which makes `B` empty for every twin-prime pair and gives `h(i) = 0` infinitely often
(machine-checked: `B 200 = ∅`).  The intended, and here used, lower bound is `P i`
(exclusive); with it the empirical data of the blueprint is reproduced (`h(100) ≈ 0.99`).

## Proof architecture

`C i` consists of even numbers lying in the interval `[P i + 4, P i + 2·P(i+1) − 5]`.
Writing `E i` for the number of even integers in that interval and
`miss i = E i − (C i).card` for the count of even integers there **not** represented as
`a + b`, we have the exact identity

  `h i = (E i)/(P i) − (miss i)/(P i)`.

The two analytic inputs, which are **not** available in Mathlib and are therefore taken as
hypotheses (cited, not assumed as axioms):

* `HDusart` — Dusart, P. *Explicit estimates of some functions over primes.*
            Ramanujan J **45**, 227–251 (2018), https://doi.org/10.1007/s11139-016-9839-4.
            This paper gives, for every real `x ≥ 468 991 632`, a prime in
            `(x, x·(1 + 1/(5000·ln²x))]`.  Applied at `x = P i` this gives the explicit
            prime-gap bound `gap i ≤ P i / (5000·ln²(P i))` for `P i ≥ 468 991 632`.
            This is a genuine *unconditional* result (it rests only on a numerical zero
            verification and an explicit zero-free region — i.e. on classical results of
            prime-number theory, no RH/GRH).  Mathlib has neither the full Prime Number
            Theorem nor Dusart's explicit estimates, so it is taken as a cited hypothesis.
            From `HDusart` we *derive* the relative-gap limit `Hgap` (`gap i / P i → 0`),
            so the project rests on Dusart, not on a free PNT assumption.
* `Hcover` — the Goldbach-covering input (Aziz 2025, untitled-2.pdf, Theorem 4.2):
            `(miss i)/(P i) → 0`,  i.e. almost every even integer in the interval is a sum.

From these, `E i / P i → 1` (elementary, using `Hgap`, which is derived from `HDusart`)
and the identity above give `h i → 1`.

The classical Prime Number Theorem and Chebyshev's theorem, where the blueprint invokes
them, are cited as standard results.
-/

open Filter Topology

namespace BlueprintH

/-- `P i` is the `i`-th prime (`0`-indexed): `P 0 = 2`, `P 1 = 3`, …  For `i ≥ 1` these
are the odd primes `p'ᵢ` of the blueprint. -/
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime i

lemma P_prime (i : ℕ) : Nat.Prime (P i) := Nat.prime_nth_prime i

lemma P_strictMono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOf_prime

lemma P_pos (i : ℕ) : 0 < P i := (P_prime i).pos

lemma P_lt_succ (i : ℕ) : P i < P (i + 1) := P_strictMono (Nat.lt_succ_self i)

lemma two_le_P (i : ℕ) : 2 ≤ P i := (P_prime i).two_le

/-- `A i = { p prime | 3 ≤ p ≤ P i }`. -/
noncomputable def A (i : ℕ) : Finset ℕ := (Finset.Icc 3 (P i)).filter (fun n => Nat.Prime n)

/-- `B i = { p prime | P i < p ≤ 2·P(i+1) − 5 }`. -/
noncomputable def B (i : ℕ) : Finset ℕ :=
  (Finset.Ioc (P i) (2 * P (i + 1) - 5)).filter (fun n => Nat.Prime n)

/-- `C i = { a + b | a ∈ A i, b ∈ B i }`, the set of distinct prime sums. -/
noncomputable def C (i : ℕ) : Finset ℕ := (A i ×ˢ B i).image (fun p => p.1 + p.2)

/-- The even integers in the interval `[P i + 4, P i + 2·P(i+1) − 5]` containing `C i`. -/
noncomputable def evenInterval (i : ℕ) : Finset ℕ :=
  (Finset.Icc (P i + 4) (P i + 2 * P (i + 1) - 5)).filter (fun n => Even n)

/-- The prime gap `P(i+1) − P i`. -/
noncomputable def gap (i : ℕ) : ℕ := P (i + 1) - P i

/-- `miss i` = number of even integers in `[P i + 4, P i + 2·P(i+1) − 5]` *not* of the
form `a + b` with `a ∈ A i`, `b ∈ B i`. -/
noncomputable def miss (i : ℕ) : ℕ := (evenInterval i).card - (C i).card

/-- `h i = n(Cᵢ)/p'ᵢ`. -/
noncomputable def h (i : ℕ) : ℝ := (C i).card / (P i : ℝ)

/-! ### Elementary structural lemmas -/

lemma mem_A {i x : ℕ} : x ∈ A i ↔ (3 ≤ x ∧ x ≤ P i) ∧ Nat.Prime x := by
  simp [A, Finset.mem_filter, Finset.mem_Icc, and_assoc]

lemma mem_B {i x : ℕ} : x ∈ B i ↔ (P i < x ∧ x ≤ 2 * P (i + 1) - 5) ∧ Nat.Prime x := by
  simp [B, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

lemma mem_C {i x : ℕ} : x ∈ C i ↔ ∃ a ∈ A i, ∃ b ∈ B i, a + b = x := by
  classical
  simp only [C, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

/-- Every element of `A i` is odd (it is a prime `≥ 3`). -/
lemma odd_of_mem_A {i a : ℕ} (ha : a ∈ A i) : Odd a := by
  rw [mem_A] at ha
  exact ha.2.odd_of_ne_two (by omega)

/-- Every element of `B i` is odd (it is a prime `> P i ≥ 2`). -/
lemma odd_of_mem_B {i b : ℕ} (hb : b ∈ B i) : Odd b := by
  rw [mem_B] at hb
  have : b ≠ 2 := by have := two_le_P i; omega
  exact hb.2.odd_of_ne_two this

/-- Every element of `C i` is even. -/
lemma even_of_mem_C {i x : ℕ} (hx : x ∈ C i) : Even x := by
  rw [mem_C] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact (odd_of_mem_A ha).add_odd (odd_of_mem_B hb)

/-- Every element of `C i` lies in `[P i + 4, P i + 2·P(i+1) − 5]`. -/
lemma mem_C_bounds {i x : ℕ} (hx : x ∈ C i) :
    P i + 4 ≤ x ∧ x ≤ P i + 2 * P (i + 1) - 5 := by
  rw [mem_C] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [mem_A] at ha; rw [mem_B] at hb
  obtain ⟨⟨ha3, haP⟩, _⟩ := ha
  obtain ⟨⟨hbP, hbU⟩, _⟩ := hb
  constructor
  · omega
  · have : 5 ≤ 2 * P (i + 1) := by have := two_le_P (i + 1); omega
    omega

/-- `C i ⊆ evenInterval i`. -/
lemma C_subset_evenInterval (i : ℕ) : C i ⊆ evenInterval i := by
  intro x hx
  rw [evenInterval, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨mem_C_bounds hx, even_of_mem_C hx⟩

lemma C_card_le_evenInterval (i : ℕ) : (C i).card ≤ (evenInterval i).card :=
  Finset.card_le_card (C_subset_evenInterval i)

/-- The defining identity `(C i).card = (evenInterval i).card − miss i` over `ℝ`. -/
lemma C_card_eq (i : ℕ) :
    ((C i).card : ℝ) = (evenInterval i).card - (miss i : ℝ) := by
  have hle := C_card_le_evenInterval i
  rw [miss, Nat.cast_sub hle]; ring

/-! ### Counting the even integers in an interval -/

/-
The number of even integers in `Finset.Icc l u` is at most `(u + 1 - l)/2 + 1`.
-/
lemma card_filter_even_Icc_le (l u : ℕ) :
    ((Finset.Icc l u).filter (fun n => Even n)).card ≤ (u + 1 - l) / 2 + 1 := by
  -- Let's map the even numbers in `[l, u]` injectively to the interval `[⌈l/2⌉, u/2]`.
  have h_map : ((Finset.Icc l u).filter (fun n => Even n)) ⊆ Finset.image (fun k => 2 * k) (Finset.Icc ((l + 1) / 2) (u / 2)) := by
    intro n hn; simp_all +decide [ Nat.even_iff ];
    exact ⟨ n / 2, ⟨ by omega, by omega ⟩, by linarith [ Nat.mod_add_div n 2 ] ⟩;
  refine le_trans ( Finset.card_le_card h_map ) ?_;
  rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ; omega;

/-
The number of even integers in `Finset.Icc l u` is at least `(u + 1 - l)/2` when `l ≤ u`.
-/
lemma card_filter_even_Icc_ge (l u : ℕ) (hlu : l ≤ u) :
    (u + 1 - l) / 2 ≤ ((Finset.Icc l u).filter (fun n => Even n)).card := by
  -- Consider the set of even numbers in the interval $[l, u]$. This set is in bijection with the set of integers in the interval $[(l + 1) / 2, u / 2]$.
  have h_bij : Finset.image (fun k => 2 * k) (Finset.Icc ((l + 1) / 2) (u / 2)) ⊆ Finset.filter (fun n => Even n) (Finset.Icc l u) := by
    grind;
  exact le_trans ( by erw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ; omega ) ( Finset.card_mono h_bij )

/-! ### The two analytic inputs (cited literature, taken as hypotheses) -/

/-- **Hypothesis HDusart** (Dusart, P. *Explicit estimates of some functions over primes.*
Ramanujan J **45**, 227–251 (2018), https://doi.org/10.1007/s11139-016-9839-4).

This paper gives: for all real `x ≥ 468 991 632` there is a prime `p` with
`x < p ≤ x·(1 + 1/(5000·ln²x))`.  Specialising to `x = P i` (an actual prime once
`P i ≥ 468 991 632`), the next prime `P (i+1)` lies in that interval, so
`P (i+1) - P i ≤ (P i)/(5000·ln²(P i))`, i.e. the explicit gap bound below.

This is the form of Dusart's result we use.  It is a genuinely *unconditional* estimate
(no RH/GRH); it rests only on the numerical verification of zeros of ζ and an explicit
zero-free region, both classical.  Mathlib has neither the full PNT nor Dusart's explicit
bounds, so this is taken as a cited hypothesis (not an axiom).  From it we derive `Hgap`. -/
abbrev HDusart : Prop :=
  ∀ i : ℕ, (468991632 : ℝ) ≤ (P i : ℝ) →
    (gap i : ℝ) ≤ (P i : ℝ) / (5000 * (Real.log (P i : ℝ)) ^ 2)

/-- **Hypothesis Hgap.**  The relative prime gap tends to `0`, i.e. `p_{i+1}/p_i → 1`.

It is **derived** from `HDusart` (see `Hgap_of_dusart`): once `P i ≥ 468 991 632`,
`gap i / P i ≤ 1/(5000·ln²(P i)) → 0`.  Equivalently this is a standard consequence of the
Prime Number Theorem, but here we tie it to Dusart's explicit estimate rather than assume
it freely.  (For context: Mathlib has only the Chebyshev *upper* bound
`π(x) ≤ (log 4 + ε)·x/log x`; one-sided Chebyshev bounds give only a *bounded* ratio, not
the limit `1`.) -/
abbrev Hgap : Prop := Tendsto (fun i => (gap i : ℝ) / (P i : ℝ)) atTop (𝓝 0)

/-- `P i → ∞` (as a real sequence). -/
lemma tendsto_P_atTop : Tendsto (fun i => (P i : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp P_strictMono.tendsto_atTop

/-
`1/(5000·ln²(P i)) → 0`.
-/
lemma tendsto_inv_log_sq_P : Tendsto (fun i => 1 / (5000 * (Real.log (P i : ℝ)) ^ 2))
    atTop (𝓝 0) := by
  -- Since $P i \to \infty$, we have $\log(P i) \to \infty$.
  have h_log_inf : Filter.Tendsto (fun i => Real.log (P i)) Filter.atTop Filter.atTop := by
    exact Real.tendsto_log_atTop.comp <| tendsto_P_atTop;
  exact tendsto_const_nhds.div_atTop ( Filter.Tendsto.const_mul_atTop ( by norm_num ) ( Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| h_log_inf ) )

/-
**`Hgap` is derived from Dusart's explicit gap bound.**
-/
lemma Hgap_of_dusart (hd : HDusart) : Hgap := by
  refine' squeeze_zero_norm' _ tendsto_inv_log_sq_P;
  simp +zetaDelta at *;
  obtain ⟨ a, ha ⟩ := Filter.eventually_atTop.mp ( tendsto_P_atTop.eventually_ge_atTop 468991632 );
  exact ⟨ a, fun b hb => by have := hd b ( ha b hb ) ; rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| P_pos b ) ] ; ring_nf at *; linarith ⟩

/-- **Hypothesis Hcover** (Aziz 2025, Goldbach-on-bands style).  The fraction of even
integers in `[P i + 4, P i + 2·P(i+1) − 5]` not represented as `a + b` tends to `0`.  Not
available in Mathlib; taken as a hypothesis.

(Remark: the blueprint's Lemma 3 only covers the central `√p`-band `(2p'ᵢ, 2p'_{i+1})`; the
covering needed for `h → 1` is over the full interval of width `≈ 2p'ᵢ`, which is what this
hypothesis encodes.) -/
abbrev Hcover : Prop := Tendsto (fun i => (miss i : ℝ) / (P i : ℝ)) atTop (𝓝 0)

/-
`P(i+1)/P i → 1`, derived from `Hgap`.
-/
lemma P_ratio_tendsto_one (hgap : Hgap) :
    Tendsto (fun i => (P (i + 1) : ℝ) / (P i : ℝ)) atTop (𝓝 1) := by
  have h : (fun i => (P (i + 1) : ℝ) / (P i : ℝ))
      = (fun i => (gap i : ℝ) / (P i : ℝ) + 1) := by
    funext i
    have hpi : (P i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (P_pos i).ne'
    rw [gap, Nat.cast_sub (P_lt_succ i).le]
    field_simp
    ring
  rw [h]
  simpa using hgap.add_const 1

/-
`E i / P i → 1`, where `E i = (evenInterval i).card`.  Elementary squeeze using `Hgap`
and the even-count bounds.
-/
lemma evenInterval_card_div_tendsto_one (hgap : Hgap) :
    Tendsto (fun i => ((evenInterval i).card : ℝ) / (P i : ℝ)) atTop (𝓝 1) := by
  -- Let l = P i + 4 and u = P i + 2*P(i+1) - 5 so evenInterval i = (Finset.Icc l u).filter Even and E i := (evenInterval i).card.
  set E := fun i : ℕ => (evenInterval i).card
  have h_bounds : ∀ i ≥ 1, (P (i + 1) - 4 : ℝ) ≤ E i ∧ E i ≤ (P (i + 1) - 3 : ℝ) := by
    intro i hi
    have h_bounds : (P (i + 1) - 4 : ℕ) ≤ E i ∧ E i ≤ (P (i + 1) - 3 : ℕ) := by
      have h_bounds : (P i + 4 ≤ P i + 2 * P (i + 1) - 5) ∧ ((P i + 2 * P (i + 1) - 5 + 1 - (P i + 4)) / 2 ≤ E i ∧ E i ≤ (P i + 2 * P (i + 1) - 5 + 1 - (P i + 4)) / 2 + 1) := by
        refine' ⟨ Nat.le_sub_of_add_le _, _, _ ⟩;
        · rcases i with ( _ | _ | i ) <;> simp +arith +decide [ P ] at *;
          linarith [ Nat.Prime.two_le ( Nat.prime_nth_prime ( i + 3 ) ), show Nat.nth Nat.Prime ( i + 3 ) ≥ 5 by exact le_trans ( by norm_num ) ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( show i + 3 ≥ 2 by linarith ) ) ];
        · convert card_filter_even_Icc_ge ( P i + 4 ) ( P i + 2 * P ( i + 1 ) - 5 ) _ using 1;
          exact le_tsub_of_add_le_left ( by linarith [ show P ( i + 1 ) ≥ 5 by exact le_trans ( by norm_num ) ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( show i + 1 ≥ 2 by linarith ) ) ] );
        · convert card_filter_even_Icc_le ( P i + 4 ) ( P i + 2 * P ( i + 1 ) - 5 ) using 1;
      omega;
    norm_cast;
    rw [ Int.subNatNat_of_le, Int.subNatNat_of_le ] <;> norm_cast;
    · exact Nat.succ_le_of_lt ( lt_of_le_of_lt ( Nat.Prime.two_le ( P_prime _ ) ) ( P_lt_succ _ ) );
    · refine' Nat.le_trans _ ( Nat.nth_monotone _ <| Nat.succ_le_succ hi ) ; norm_num [ P ];
      exact Nat.infinite_setOf_prime;
  -- Dividing by P i > 0 and using the fact that P(i+1)/(P i) → 1, we get the desired result.
  have h_div : Tendsto (fun i => ((P (i + 1) : ℝ) - 4) / (P i : ℝ)) atTop (𝓝 1) ∧ Tendsto (fun i => ((P (i + 1) : ℝ) - 3) / (P i : ℝ)) atTop (𝓝 1) := by
    have h_div : Tendsto (fun i => ((P (i + 1) : ℝ) / (P i : ℝ)) - 4 / (P i : ℝ)) atTop (𝓝 1) ∧ Tendsto (fun i => ((P (i + 1) : ℝ) / (P i : ℝ)) - 3 / (P i : ℝ)) atTop (𝓝 1) := by
      exact ⟨ by simpa using Filter.Tendsto.sub ( P_ratio_tendsto_one hgap ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( tendsto_natCast_atTop_atTop.comp ( P_strictMono.tendsto_atTop ) ) ) ), by simpa using Filter.Tendsto.sub ( P_ratio_tendsto_one hgap ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( tendsto_natCast_atTop_atTop.comp ( P_strictMono.tendsto_atTop ) ) ) ) ⟩;
    simpa only [ sub_div ] using h_div;
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_div.1 h_div.2 ( Filter.eventually_atTop.mpr ⟨ 1, fun i hi => by simpa using div_le_div_of_nonneg_right ( h_bounds i hi |>.1 ) ( Nat.cast_nonneg _ ) ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 1, fun i hi => by simpa using div_le_div_of_nonneg_right ( h_bounds i hi |>.2 ) ( Nat.cast_nonneg _ ) ⟩ )

/-- **Theorem H.**  `h i = n(Cᵢ)/p'ᵢ → 1` as `i → ∞`. -/
theorem tendsto_h_one (hgap : Hgap) (hcover : Hcover) :
    Tendsto (fun i => h i) atTop (𝓝 1) := by
  have key : (fun i => h i)
      = (fun i => ((evenInterval i).card : ℝ) / (P i : ℝ)
                    - (miss i : ℝ) / (P i : ℝ)) := by
    funext i
    rw [h, C_card_eq i, sub_div]
  rw [key]
  have := (evenInterval_card_div_tendsto_one hgap).sub hcover
  simpa using this

/-- **Theorem H, from the cited literature.**  Using Dusart (2018, Ramanujan J **45**,
227–251, https://doi.org/10.1007/s11139-016-9839-4) `HDusart` for the prime-gap input
and Aziz (2025) Thm. 4.2 (`Hcover`) for the Goldbach covering,
`h i = n(Cᵢ)/p'ᵢ → 1`.  This is the project's headline result: it rests on Dusart's genuine
unconditional gap estimate `g_n < p_n/(5000·ln² p_n)` for `p_n ≥ 468 991 632`. -/
theorem tendsto_h_one_of_dusart (hd : HDusart) (hcover : Hcover) :
    Tendsto (fun i => h i) atTop (𝓝 1) :=
  tendsto_h_one (Hgap_of_dusart hd) hcover

end BlueprintH