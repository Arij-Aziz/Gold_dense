import RequestProject.DifferenceSieve
import RequestProject.Definitions

open scoped BigOperators
open scoped Pointwise
open scoped Classical

/-!
# Module 10 — `PrimeSumset.ConcreteConstants`

Plugs literature-derived explicit constants into `DifferenceSieve`:

  C_pair = 67   (cite: Selberg sieve upper bound for prime pairs,
                 C_sieve = 8, Montgomery–Vaughan, *Multiplicative Number
                 Theory I*, Ch. 7; singular series supremum
                 sup_{|h|≤x} 𝔖(h) ≈ 2C₂·e^γ·log log x ≈ 8.33;
                 see CONSTANTS_MINING.md §3)

  κ_A    = 1    (cite: Dusart 2010, "Estimates of Some Functions Over
                 Primes without R.H.", arXiv:1002.0442, Theorem 1:
                 π(x) > x/(log x - 1) for x ≥ 5393, hence
                 |A| = π(x)-1 > x/log x for x ≥ 10^15;
                 see CONSTANTS_MINING.md §2)

giving the first fully-cited explicit positive density h₀ = 1/κ₀.
-/

namespace PrimeSumset

open Finset

/-- The literature-derived prime-pair upper-bound constant.
  Source: Selberg sieve. C_sieve = 8 (Montgomery–Vaughan); sup 𝔖(h) ≈ 8.33
  for x=10^15. C_pair = C_sieve · sup 𝔖(h) ≈ 67. -/
def C_pair_lit : ℝ := 67

/-- The literature-derived Chebyshev lower-bound constant.
  Source: Dusart 2010, Theorem 1: π(x) > x/(log x - 1) for x ≥ 5393.
  For x ≥ 10^15, |A| = π(x)-1 > x/log x, so κ_A = 1 suffices. -/
def kA_lit : ℝ := 1

/-- Transfer constant c₀ = C_pair · κ_A². -/
def c0_lit : ℝ := C_pair_lit * kA_lit ^ 2

/-- Energy constant κ₀ = 1 + 3c₀². -/
def kappa0_lit : ℝ := 1 + 3 * c0_lit ^ 2

/-- First explicit cited positive density h₀ = 1/κ₀. -/
noncomputable def h0_lit : ℝ := 1 / kappa0_lit

/-- Numeric check: κ₀ = 13468. -/
lemma kappa0_lit_val : kappa0_lit = 13468 := by
  unfold kappa0_lit c0_lit C_pair_lit kA_lit
  norm_num

/-- Numeric check: c₀ = 67. -/
lemma c0_lit_val : c0_lit = 67 := by
  unfold c0_lit C_pair_lit kA_lit
  norm_num

/-- Numeric check: h₀ · 13468 = 1. -/
lemma h0_lit_val : h0_lit * 13468 = 1 := by
  unfold h0_lit kappa0_lit c0_lit C_pair_lit kA_lit
  norm_num

/-- **First fully-cited positive density theorem.**
  Under the raw prime-pair upper bound with constant C_pair_lit (cited:
  Selberg sieve, C_sieve=8, Montgomery–Vaughan Ch. 7; sup 𝔖(h) for x=10^15)
  and Chebyshev lower bound with constant kA_lit (cited: Dusart 2010,
  Theorem 1: π(x) > x/(log x - 1) for x ≥ 5393),
  the distinct sumset satisfies |C| ≥ h₀_lit · x. -/
theorem sumset_ge_cited_density {i : ℕ} (hi : i > trigger)
    (hpairA : ∀ h : ℤ, h ≠ 0 →
        (rSub (Aset (primeIdx i)) h : ℝ)
          ≤ C_pair_lit * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hpairB : ∀ h : ℤ, h ≠ 0 →
        (rSub (Bset (primeIdx i)) h : ℝ)
          ≤ C_pair_lit * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hlowA : (primeIdx i : ℝ) / (kA_lit * Real.log (primeIdx i))
          ≤ ((Aset (primeIdx i)).card : ℝ))
    (hlowB : (primeIdx i : ℝ) / (kA_lit * Real.log (primeIdx i))
          ≤ ((Bset (primeIdx i)).card : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    h0_lit * (primeIdx i : ℝ)
      ≤ ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have hCpair : 0 ≤ C_pair_lit := by unfold C_pair_lit; norm_num
  have hkApos : 0 < kA_lit := by unfold kA_lit; norm_num
  have hge := sumset_card_ge_of_prime_pair_sieve hi C_pair_lit kA_lit
    hCpair hkApos hpairA hpairB hlowA hlowB hmass
  unfold h0_lit kappa0_lit c0_lit
  have hden : (1 + 3 * (C_pair_lit * kA_lit ^ 2) ^ 2) = (13468 : ℝ) := by
    unfold C_pair_lit kA_lit; norm_num
  rw [hden]
  have h_eq : (1 / (13468 : ℝ)) * (primeIdx i : ℝ) = (primeIdx i : ℝ) / (13468 : ℝ) := by
    ring
  rw [h_eq]
  rw [hden] at hge
  exact hge

/-- **Density form.** Under the same hypotheses, for every `h < h₀_lit`
  the distinct sumset satisfies `|C| > h · x`. -/
theorem sumset_gt_cited_density {i : ℕ} (hi : i > trigger)
    (h : ℝ) (hh : h < h0_lit)
    (hpairA : ∀ k : ℤ, k ≠ 0 →
        (rSub (Aset (primeIdx i)) k : ℝ)
          ≤ C_pair_lit * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hpairB : ∀ k : ℤ, k ≠ 0 →
        (rSub (Bset (primeIdx i)) k : ℝ)
          ≤ C_pair_lit * (primeIdx i : ℝ) / (Real.log (primeIdx i)) ^ 2)
    (hlowA : (primeIdx i : ℝ) / (kA_lit * Real.log (primeIdx i))
          ≤ ((Aset (primeIdx i)).card : ℝ))
    (hlowB : (primeIdx i : ℝ) / (kA_lit * Real.log (primeIdx i))
          ≤ ((Bset (primeIdx i)).card : ℝ))
    (hmass : (primeIdx i : ℝ)
        ≤ (mass (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ)) :
    h * (primeIdx i : ℝ)
      < ((sumset (Aset (primeIdx i)) (Bset (primeIdx i))).card : ℝ) := by
  have hCpair : 0 ≤ C_pair_lit := by unfold C_pair_lit; norm_num
  have hkApos : 0 < kA_lit := by unfold kA_lit; norm_num
  have hh_inv : h < 1 / (1 + 3 * (C_pair_lit * kA_lit ^ 2) ^ 2) := by
    unfold h0_lit kappa0_lit c0_lit at hh
    exact hh
  exact sumset_card_gt_of_prime_pair_sieve hi C_pair_lit kA_lit h hCpair hkApos hh_inv
    hpairA hpairB hlowA hlowB hmass

end PrimeSumset
