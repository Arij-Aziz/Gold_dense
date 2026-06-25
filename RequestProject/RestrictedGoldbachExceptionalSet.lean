import Mathlib
import RequestProject.RestrictedGoldbachDefs

/-!
# RestrictedGoldbach — Exceptional Set Bound

**ONE `sorry`**: `pintz_exceptional_bound` (Pintz 2018).
Everything else proved from it.
-/

namespace RestrictedGoldbach

open Real
open Filter

lemma primeIdx_ge_add_two (n : ℕ) : n + 2 ≤ PrimeSumset.primeIdx n := by
  induction' n with k ih
  · have hp : Nat.Prime (Nat.nth Nat.Prime 0) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 0
    have hgt : 1 < Nat.nth Nat.Prime 0 := Nat.Prime.one_lt hp
    simpa [PrimeSumset.primeIdx] using hgt
  · have hmono : StrictMono (Nat.nth Nat.Prime) :=
      Nat.nth_strictMono Nat.infinite_setOf_prime
    have hlt : PrimeSumset.primeIdx k < PrimeSumset.primeIdx (Nat.succ k) := by
      simpa [PrimeSumset.primeIdx] using hmono (Nat.lt_succ_self k)
    have hle' : PrimeSumset.primeIdx k + 1 ≤ PrimeSumset.primeIdx (Nat.succ k) :=
      Nat.succ_le_of_lt hlt
    have h_sum : k + 3 ≤ PrimeSumset.primeIdx k + 1 := by omega
    have h_target : k + 3 ≤ PrimeSumset.primeIdx (Nat.succ k) := le_trans h_sum hle'
    have : k.succ + 2 = k + 3 := by omega
    rw [this]
    exact h_target

lemma primeIdx_strict_gt (n : ℕ) : n < PrimeSumset.primeIdx n := by
  have h := primeIdx_ge_add_two n
  omega

lemma primeIdx1_ge_i {i : ℕ} (hi : 1 ≤ i) : i ≤ primeIdx1 i := by
  unfold primeIdx1
  have h := primeIdx_strict_gt (i - 1)
  omega

-- ── 1. Pintz (THE ONLY SORRY) ──────────────────────────────────────

/-- Pintz (2018) Theorem 1: `|E| ≤ 64·(3pᵢ)^{18/25}`. -/
theorem pintz_exceptional_bound {i : ℕ} (hi : 10 ^ 15 < i) :
    (ExceptionalSet i).card ≤ 64 * ((3 * (primeIdx1 i : ℝ)) ^ ((18/25 : ℝ))) := by
  sorry

-- ── 2. Numerical inequality ─────────────────────────────────────────

lemma inequality_64_3p_pow_18_25_lt_p_div_20 {p : ℝ}
    (hp : (10 : ℝ) ^ (15 : ℕ) ≤ p) (hp_pos : 0 < p) :
    64 * ((3 * p) ^ ((18/25 : ℝ))) < p / 20 := by
  have hp_nonneg : 0 ≤ p := by linarith
  have h3p_nonneg : 0 ≤ 3 * p := by nlinarith
  have hL_nonneg : 0 ≤ 64 * ((3 * p) ^ ((18/25 : ℝ))) := by positivity
  have hR_nonneg : 0 ≤ p / 20 := by nlinarith
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
  have hR_pow : (p / 20) ^ (25 : ℕ) = p ^ (25 : ℕ) / (20 : ℝ) ^ (25 : ℕ) := by rw [div_pow]
  -- Show LHS^25 < RHS^25
  have h_pow_lt : (64 * ((3 * p) ^ ((18/25 : ℝ)))) ^ (25 : ℕ) < (p / 20) ^ (25 : ℕ) := by
    rw [hL_pow, hR_pow]
    have h20_25_pos : 0 < (20 : ℝ) ^ (25 : ℕ) := pow_pos (by norm_num) 25
    rw [lt_div_iff₀ h20_25_pos]
    have hp25 : p ^ (25 : ℕ) = p ^ (18 : ℕ) * p ^ (7 : ℕ) := by
      rw [← pow_add, show (18 : ℕ) + (7 : ℕ) = (25 : ℕ) by omega]
    rw [hp25]
    have hp18_pos : 0 < p ^ (18 : ℕ) := pow_pos hp_pos 18
    have h_const : (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * (20 : ℝ) ^ (25 : ℕ) <
        ((10 : ℝ) ^ (15 : ℕ)) ^ (7 : ℕ) := by norm_num
    have hp7 : ((10 : ℝ) ^ (15 : ℕ)) ^ (7 : ℕ) ≤ p ^ (7 : ℕ) := by
      have h_base_nonneg : 0 ≤ (10 : ℝ) ^ (15 : ℕ) := pow_nonneg (by norm_num) 15
      gcongr
    have h_total : (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * (20 : ℝ) ^ (25 : ℕ) < p ^ (7 : ℕ) := by
      linarith
    calc
      (64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * p ^ (18 : ℕ) * (20 : ℝ) ^ (25 : ℕ)
          = ((64 : ℝ) ^ (25 : ℕ) * (3 : ℝ) ^ (18 : ℕ) * (20 : ℝ) ^ (25 : ℕ)) * p ^ (18 : ℕ) := by ring
      _ < p ^ (7 : ℕ) * p ^ (18 : ℕ) := mul_lt_mul_of_pos_right h_total hp18_pos
      _ = p ^ (18 : ℕ) * p ^ (7 : ℕ) := mul_comm _ _
  by_contra! H
  have h_pow_le : (p / 20) ^ (25 : ℕ) ≤ (64 * ((3 * p) ^ ((18/25 : ℝ)))) ^ (25 : ℕ) := by
    gcongr
  linarith

-- ── 3. Restricted exceptional bound ─────────────────────────────────

theorem restricted_exceptional_bound {i : ℕ} (hi : 10 ^ 15 < i) :
    (ExceptionalSet i).card < (1/20 : ℝ) * (primeIdx1 i : ℝ) := by
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
  have h_ineq : 64 * ((3 * (primeIdx1 i : ℝ)) ^ ((18/25 : ℝ))) < (1/20 : ℝ) * (primeIdx1 i : ℝ) := by
    have h := inequality_64_3p_pow_18_25_lt_p_div_20 hp_real hp_pos
    simpa [div_eq_inv_mul, mul_comm] using h
  linarith

-- ── 4. Asymptotic ──────────────────────────────────────────────────

theorem exceptional_is_o_pi :
    Filter.Tendsto (fun i : ℕ => ((ExceptionalSet i).card : ℝ) / (primeIdx1 i : ℝ))
      Filter.atTop (nhds 0) := by
  have h_bound : ∀ᶠ i in Filter.atTop,
      ((ExceptionalSet i).card : ℝ) / (primeIdx1 i : ℝ) ≤
      64 * (3 : ℝ) ^ ((18/25 : ℝ)) * ((primeIdx1 i : ℝ) ^ ((-7/25 : ℝ))) := by
    refine Filter.eventually_atTop.mpr ⟨10 ^ 15 + 1, fun i hi => ?_⟩
    have hi' : 10 ^ 15 < i := by omega
    have h_pintz : (ExceptionalSet i).card ≤ 64 * ((3 * (primeIdx1 i : ℝ)) ^ ((18/25 : ℝ))) :=
      pintz_exceptional_bound hi'
    set p := (primeIdx1 i : ℝ) with hp
    have hp_pos : 0 < p := by
      have hpos_nat : 0 < primeIdx1 i := primeIdx1_pos (by omega : 2 ≤ i)
      dsimp [p]
      exact_mod_cast hpos_nat
    have h_div : ((ExceptionalSet i).card : ℝ) / p ≤ 64 * ((3 * p) ^ ((18/25 : ℝ))) / p :=
      (div_le_div_of_nonneg_right h_pintz (by linarith))
    have h_div_eq : p ^ ((18/25 : ℝ)) / p = p ^ (((18/25 : ℝ)) - (1 : ℝ)) := by
      calc
        p ^ ((18/25 : ℝ)) / p = p ^ ((18/25 : ℝ)) / (p ^ (1 : ℝ)) := by rw [Real.rpow_one p]
        _ = p ^ (((18/25 : ℝ)) - (1 : ℝ)) := by
          rw [← Real.rpow_sub (by linarith : 0 < p) ((18/25 : ℝ)) (1 : ℝ)]
    have h_mul_rpow : (3 * p : ℝ) ^ ((18/25 : ℝ)) = (3 : ℝ) ^ ((18/25 : ℝ)) * p ^ ((18/25 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) (by linarith : 0 ≤ p)]
    have h_simp : 64 * ((3 * p) ^ ((18/25 : ℝ))) / p =
        64 * (3 : ℝ) ^ ((18/25 : ℝ)) * (p ^ ((-7/25 : ℝ))) := by
      calc
        64 * ((3 * p) ^ ((18/25 : ℝ))) / p
            = 64 * (((3 : ℝ) ^ ((18/25 : ℝ)) * p ^ ((18/25 : ℝ))) / p) := by
              rw [h_mul_rpow, mul_div_assoc]
        _ = 64 * (3 : ℝ) ^ ((18/25 : ℝ)) * (p ^ ((18/25 : ℝ)) / p) := by
          calc
            64 * (((3 : ℝ) ^ ((18/25 : ℝ)) * p ^ ((18/25 : ℝ))) / p)
                = 64 * ((3 : ℝ) ^ ((18/25 : ℝ)) * (p ^ ((18/25 : ℝ)) / p)) := by rw [mul_div_assoc]
            _ = 64 * (3 : ℝ) ^ ((18/25 : ℝ)) * (p ^ ((18/25 : ℝ)) / p) := by rw [← mul_assoc]
        _ = 64 * (3 : ℝ) ^ ((18/25 : ℝ)) * (p ^ (((18/25 : ℝ)) - (1 : ℝ))) := by rw [h_div_eq]
        _ = 64 * (3 : ℝ) ^ ((18/25 : ℝ)) * (p ^ ((-7/25 : ℝ))) := by
          congr 2; ring
    rw [h_simp] at h_div
    exact h_div
  have h_nonneg : ∀ᶠ i in Filter.atTop, 0 ≤ ((ExceptionalSet i).card : ℝ) / (primeIdx1 i : ℝ) := by
    refine Filter.eventually_atTop.mpr ⟨0, fun i _ => ?_⟩
    exact div_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast Nat.zero_le _)
  have h_pi_tendsto : Filter.Tendsto (fun i : ℕ => (primeIdx1 i : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun i => ?_) tendsto_natCast_atTop_atTop
    by_cases hi : 1 ≤ i
    · have hge : i ≤ primeIdx1 i := primeIdx1_ge_i hi
      exact_mod_cast hge
    · have hi0 : i = 0 := by omega
      subst hi0
      exact by exact_mod_cast Nat.zero_le _
  have h7pos : 0 < (7/25 : ℝ) := by norm_num
  have h_pos_pow : Filter.Tendsto (fun i : ℕ => ((primeIdx1 i : ℝ) ^ (7/25 : ℝ)))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop h7pos).comp h_pi_tendsto
  have h_pow_tendsto : Filter.Tendsto (fun i : ℕ => ((primeIdx1 i : ℝ) ^ ((-7/25 : ℝ))))
      Filter.atTop (nhds 0) := by
    have h_eq : (fun i : ℕ => ((primeIdx1 i : ℝ) ^ ((-7/25 : ℝ)))) =
        (fun x : ℝ => x⁻¹) ∘ (fun i : ℕ => ((primeIdx1 i : ℝ) ^ (7/25 : ℝ))) := by
      ext i
      have h_nonneg_i : 0 ≤ (primeIdx1 i : ℝ) := by exact_mod_cast Nat.zero_le _
      simp [Real.rpow_neg h_nonneg_i, show (-7/25 : ℝ) = -(7/25 : ℝ) by ring]
    rw [h_eq]
    exact tendsto_inv_atTop_zero.comp h_pos_pow
  have h_upper_tendsto : Filter.Tendsto (fun i : ℕ =>
      64 * (3 : ℝ) ^ ((18/25 : ℝ)) * ((primeIdx1 i : ℝ) ^ ((-7/25 : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa [mul_assoc] using
      Filter.Tendsto.const_mul (64 * (3 : ℝ) ^ ((18/25 : ℝ))) h_pow_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ h_upper_tendsto h_nonneg ?_
  · exact tendsto_const_nhds
  · exact h_bound

end RestrictedGoldbach
