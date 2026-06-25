import Mathlib
import RequestProject.RestrictedGoldbachDefs
import RequestProject.RestrictedGoldbachCombinatorics
import RequestProject.RestrictedGoldbachExceptionalSet

/-!
# RestrictedGoldbach — Main Theorem

`sumset_card_gt_95`: `|A+B| > 0.95·pᵢ` (strongest achieved constant).
-/

namespace RestrictedGoldbach

theorem sumset_card_gt_95 {i : ℕ} (hi : 10 ^ 15 < i) :
    (0.95 : ℝ) * (primeIdx1 i : ℝ) < ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) := by
  have hE : (ExceptionalSet i).card < (1/20 : ℝ) * (primeIdx1 i : ℝ) :=
    restricted_exceptional_bound hi
  have hcard := sumset_card_ge_pi_sub_eset hi
  have hpos : 0 < primeIdx1 i := primeIdx1_pos (by omega)
  have hp_pos : (0 : ℝ) < (primeIdx1 i : ℝ) := Nat.cast_pos.mpr hpos
  nlinarith

end RestrictedGoldbach
