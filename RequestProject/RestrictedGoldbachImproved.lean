import Mathlib
import RequestProject.RestrictedGoldbachExceptionalSet
import RequestProject.RestrictedGoldbachCombinatorics
import RequestProject.RestrictedGoldbachDefs

/-!
# RestrictedGoldbach — Improved Bound: `|C| > (111/112)·pᵢ`

Reuses the same `pintz_exceptional_bound` (Tier-1 sorry).
No new `sorry` declarations.
-/

namespace RestrictedGoldbach

open Real

-- ── 1. Improved numerical inequality: 64·(3p)^{18/25} < p/112 ─────
-- Proof follows the same 25th-power method as the /20 version.

lemma inequality_64_3p_pow_18_25_lt_p_div_112 {p : ℝ}
    (hp : (10 : ℝ) ^ (15 : ℕ) ≤ p) (hp_pos : 0 < p) :
    64 * ((3 * p) ^ ((18/25 : ℝ))) < p / 112 := by
  have hp_nonneg : 0 ≤ p := by linarith
  have h3p_nonneg : 0 ≤ 3 * p := by nlinarith
  -- Compute LHS^25
  have h_inner : ((3 * p : ℝ) ^ ((18/25 : ℝ))) ^ (25 : ℕ) = (3 * p : ℝ) ^ ((18 : ℕ) : ℝ) := by
    calc
      ((3 * p : ℝ) ^ ((18/25 : ℝ))) ^ (25 : ℕ)
          = ((3 * p : ℝ) ^ ((18/25 : ℝ))) ^ ((25 : ℕ) : ℝ) := by
            rw [← Real.rpow_natCast]
      _ = (3 * p : ℝ) ^ (((18/25 : ℝ)) * ((25 : ℕ) : ℝ)) := by
        rw [Real.rpow_mul h3p_nonneg (18/25 : ℝ) ((25 : ℕ) : ℝ)]
      _ = (3 * p : ℝ) ^ ((18 : ℕ) : ℝ) := by
        have hexp : ((18/25 : ℝ)) * ((25 : ℕ) : ℝ) = (18 : ℝ) := by
          push_cast; ring
        rw [hexp]; norm_num
  have hL_pow : (64 * ((3 * p) ^ ((18/25 : ℝ)))) ^ (25 : ℕ) =
      (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * p ^ (18 : ℕ) := by
    calc
      (64 * ((3 * p) ^ ((18/25 : ℝ)))) ^ (25 : ℕ)
          = (64 : ℝ) ^ (25 : ℕ) * (((3 * p) ^ ((18/25 : ℝ))) ^ (25 : ℕ)) := by
            rw [mul_pow]
      _ = (64 : ℝ) ^ (25 : ℕ) * ((3 * p : ℝ) ^ ((18 : ℕ) : ℝ)) :=
        congrArg (fun t => (64 : ℝ) ^ (25 : ℕ) * t) h_inner
      _ = (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * p ^ (18 : ℕ) := by
        have htemp : ((3 * p : ℝ) ^ ((18 : ℕ) : ℝ)) = (3 : ℝ) ^ (18 : ℕ) * p ^ (18 : ℕ) := by
          rw [Real.rpow_natCast, mul_pow]
        calc
          (64 : ℝ) ^ (25 : ℕ) * ((3 * p : ℝ) ^ ((18 : ℕ) : ℝ))
              = (64 : ℝ) ^ (25 : ℕ) * ((3 : ℝ) ^ (18 : ℕ) * p ^ (18 : ℕ)) := by rw [htemp]
          _ = (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * p ^ (18 : ℕ) := by ring
  have hR_pow : (p / 112) ^ (25 : ℕ) = p ^ (25 : ℕ) / (112 : ℝ) ^ (25 : ℕ) := by rw [div_pow]
  -- Show LHS^25 < RHS^25
  have h_pow_lt : (64 * ((3 * p) ^ ((18/25 : ℝ)))) ^ (25 : ℕ) < (p / 112) ^ (25 : ℕ) := by
    rw [hL_pow, hR_pow]
    have h112_25_pos : 0 < (112 : ℝ) ^ (25 : ℕ) := pow_pos (by norm_num) 25
    rw [lt_div_iff₀ h112_25_pos]
    have hp25 : p ^ (25 : ℕ) = p ^ (18 : ℕ) * p ^ (7 : ℕ) := by
      rw [← pow_add, show (18 : ℕ) + (7 : ℕ) = (25 : ℕ) by omega]
    rw [hp25]
    have hp18_pos : 0 < p ^ (18 : ℕ) := pow_pos hp_pos 18
    have h_const : (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * (112 : ℝ) ^ (25 : ℕ) <
        ((10 : ℝ) ^ (15 : ℕ)) ^ (7 : ℕ) := by norm_num
    have hp7 : ((10 : ℝ) ^ (15 : ℕ)) ^ (7 : ℕ) ≤ p ^ (7 : ℕ) := by
      have h_base_nonneg : 0 ≤ (10 : ℝ) ^ (15 : ℕ) := pow_nonneg (by norm_num) 15
      gcongr
    have h_total : (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * (112 : ℝ) ^ (25 : ℕ) < p ^ (7 : ℕ) := by
      linarith
    calc
      (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * p ^ (18 : ℕ) * (112 : ℝ) ^ (25 : ℕ)
          = ((64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * (112 : ℝ) ^ (25 : ℕ)) * p ^ (18 : ℕ) := by ring
      _ < p ^ (7 : ℕ) * p ^ (18 : ℕ) := mul_lt_mul_of_pos_right h_total hp18_pos
      _ = p ^ (18 : ℕ) * p ^ (7 : ℕ) := mul_comm _ _
  by_contra! H
  have h_pow_le : (p / 112) ^ (25 : ℕ) ≤ (64 * ((3 * p) ^ ((18/25 : ℝ)))) ^ (25 : ℕ) := by
    gcongr
  linarith

-- ── 2. Improved exceptional bound: |E| < pᵢ/112 ───────────────────

theorem restricted_exceptional_bound_improved {i : ℕ} (hi : 10 ^ 15 < i) :
    (ExceptionalSet i).card < (1/112 : ℝ) * (primeIdx1 i : ℝ) := by
  have h_pintz : (ExceptionalSet i).card ≤ 64 * ((3 * (primeIdx1 i : ℝ)) ^ ((18/25 : ℝ))) :=
    pintz_exceptional_bound hi
  have hp_pos : 0 < (primeIdx1 i : ℝ) := by
    have hpos_nat : 0 < primeIdx1 i := primeIdx1_pos (by omega : 2 ≤ i)
    exact_mod_cast hpos_nat
  have hp_real : (10 : ℝ) ^ (15 : ℕ) ≤ (primeIdx1 i : ℝ) := by
    have h_nat : (10 : ℕ) ^ (15 : ℕ) < i := by omega
    have h_nat' : (10 : ℕ) ^ (15 : ℕ) ≤ i - 1 := by omega
    have h_le_nat : i - 1 ≤ PrimeSumset.primeIdx (i - 1) := PrimeSumset.le_primeIdx _
    have : (10 : ℕ) ^ (15 : ℕ) ≤ primeIdx1 i := by
      calc
        (10 : ℕ) ^ (15 : ℕ) ≤ i - 1 := h_nat'
        _ ≤ PrimeSumset.primeIdx (i - 1) := h_le_nat
        _ = primeIdx1 i := by rw [primeIdx1]
    exact_mod_cast this
  have h_ineq : 64 * ((3 * (primeIdx1 i : ℝ)) ^ ((18/25 : ℝ))) < (1/112 : ℝ) * (primeIdx1 i : ℝ) := by
    have h := inequality_64_3p_pow_18_25_lt_p_div_112 hp_real hp_pos
    simpa [div_eq_inv_mul, mul_comm] using h
  linarith

-- ── 3. Main improved theorem: |C| > (111/112)·pᵢ ≈ 0.99107·pᵢ ──

theorem sumset_card_gt_111_div_112 {i : ℕ} (hi : 10 ^ 15 < i) :
    ((111 : ℝ) / 112) * (primeIdx1 i : ℝ) <
      ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) := by
  have hE : (ExceptionalSet i).card < (1/112 : ℝ) * (primeIdx1 i : ℝ) :=
    restricted_exceptional_bound_improved hi
  have hcard := sumset_card_ge_pi_sub_eset hi
  have hpos : 0 < primeIdx1 i := primeIdx1_pos (by omega)
  have hp_pos : (0 : ℝ) < (primeIdx1 i : ℝ) := Nat.cast_pos.mpr hpos
  nlinarith

end RestrictedGoldbach
