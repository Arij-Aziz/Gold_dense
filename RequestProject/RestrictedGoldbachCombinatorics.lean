import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.RestrictedGoldbachDefs

open scoped BigOperators

namespace RestrictedGoldbach

open Finset

set_option maxHeartbeats 8000000

/-! ### Counting evens in Ico(pi+1, 3pi+1) -/

lemma card_evens_Ico_two (a : ℕ) : ((Ico a (a + 2)).filter (fun n : ℕ => n % 2 = 0)).card = 1 := by
  have hset : Ico a (a + 2) = {a, a + 1} := by
    ext x; simp [mem_Ico]; omega
  rw [hset]
  by_cases ha : a % 2 = 0
  · have h_filter : ({a, a + 1} : Finset ℕ).filter (fun n => n % 2 = 0) = {a} := by
      ext x; simp [ha]; omega
    simp [h_filter]
  · have ha_mod_one : a % 2 = 1 := by
      have hlt : a % 2 < 2 := Nat.mod_lt a (by norm_num)
      omega
    have h_even : (a + 1) % 2 = 0 := by
      calc
        (a + 1) % 2 = ((a % 2) + 1) % 2 := by simpa using Nat.add_mod_right a 1
        _ = (1 + 1) % 2 := by rw [ha_mod_one]
        _ = 0 := by norm_num
    have h_filter : ({a, a + 1} : Finset ℕ).filter (fun n => n % 2 = 0) = {a + 1} := by
      ext x; simp [ha_mod_one, h_even]; omega
    simp [h_filter]

lemma card_evens_Ico (pi : ℕ) :
    ((Ico (pi + 1) (3 * pi + 1)).filter (fun n : ℕ => n % 2 = 0)).card = pi := by
  have h_target : 3 * pi + 1 = (pi + 1) + 2 * pi := by omega
  rw [h_target]
  have h_general (a k : ℕ) : ((Ico a (a + 2 * k)).filter (fun n : ℕ => n % 2 = 0)).card = k := by
    induction' k with k ih
    · simp
    · have : a + 2 * (k + 1) = (a + 2 * k) + 2 := by omega
      rw [this]
      have h_union : Ico a ((a + 2 * k) + 2) = Ico a (a + 2 * k) ∪ Ico (a + 2 * k) ((a + 2 * k) + 2) := by
        rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      have h_disjoint : Disjoint (Ico a (a + 2 * k)) (Ico (a + 2 * k) ((a + 2 * k) + 2)) := by
        apply Finset.disjoint_left.mpr
        intro x hx1 hx2
        rcases mem_Ico.mp hx1 with ⟨hlo, hhi⟩
        rcases mem_Ico.mp hx2 with ⟨hlo', hhi'⟩
        omega
      rw [h_union, filter_union]
      rw [card_union_of_disjoint]
      · rw [ih, card_evens_Ico_two (a + 2 * k)]
      · apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        apply Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        exact h_disjoint
  exact h_general (pi + 1) pi

/-! ### Membership extraction for Aset/Bset -/

private lemma mem_Aset_extract {i : ℕ} {a : ℤ} (ha : a ∈ Aset i) :
    ∃ na : ℕ, (na : ℤ) = a ∧ 3 ≤ na ∧ na ≤ primeIdx1 i ∧ Nat.Prime na := by
  unfold Aset at ha
  -- ha : a ∈ PrimeSumset.Aset (primeIdx1 i)
  -- Now we need to see what PrimeSumset.Aset is
  have hmem : a ∈ (((Finset.Icc 3 (primeIdx1 i)).filter (fun n => Nat.Prime n)).image (fun n : ℕ => (n : ℤ))) := by
    -- ha is already of this type by definition; need to unfold PrimeSumset.Aset
    simpa [PrimeSumset.Aset] using ha
  rcases Finset.mem_image.mp hmem with ⟨na, hna, rfl⟩
  rcases Finset.mem_filter.mp hna with ⟨hna_range, hna_prime⟩
  rcases Finset.mem_Icc.mp hna_range with ⟨hna_lo, hna_hi⟩
  exact ⟨na, rfl, hna_lo, hna_hi, hna_prime⟩

private lemma mem_Bset_extract {i : ℕ} {b : ℤ} (hb : b ∈ Bset i) :
    ∃ nb : ℕ, (nb : ℤ) = b ∧ primeIdx1 i < nb ∧ nb ≤ 2 * primeIdx1 i ∧ Nat.Prime nb := by
  unfold Bset at hb
  have hmem : b ∈ (((Finset.Ioc (primeIdx1 i) (2 * primeIdx1 i)).filter (fun n => Nat.Prime n)).image (fun n : ℕ => (n : ℤ))) := by
    simpa [PrimeSumset.Bset] using hb
  rcases Finset.mem_image.mp hmem with ⟨nb, hnb, rfl⟩
  rcases Finset.mem_filter.mp hnb with ⟨hnb_range, hnb_prime⟩
  rcases Finset.mem_Ioc.mp hnb_range with ⟨hnb_lo, hnb_hi⟩
  exact ⟨nb, rfl, hnb_lo, hnb_hi, hnb_prime⟩

/-- Elements of Aset pi are positive ℤ. -/
lemma mem_Aset_pos {pi : ℕ} {a : ℤ} (ha : a ∈ PrimeSumset.Aset pi) : 0 ≤ a := by
  have hmem : a ∈ (((Finset.Icc 3 pi).filter (fun n => Nat.Prime n)).image (fun n : ℕ => (n : ℤ))) := by
    simpa [PrimeSumset.Aset] using ha
  rcases Finset.mem_image.mp hmem with ⟨n, hn, rfl⟩
  rcases Finset.mem_filter.mp hn with ⟨hn_range, hn_prime⟩
  have : 3 ≤ n := (Finset.mem_Icc.mp hn_range).1
  omega

lemma mem_Bset_pos {pi : ℕ} {b : ℤ} (hb : b ∈ PrimeSumset.Bset pi) : 0 ≤ b := by
  have hmem : b ∈ (((Finset.Ioc pi (2 * pi)).filter (fun n => Nat.Prime n)).image (fun n : ℕ => (n : ℤ))) := by
    simpa [PrimeSumset.Bset] using hb
  rcases Finset.mem_image.mp hmem with ⟨n, hn, rfl⟩
  rcases Finset.mem_filter.mp hn with ⟨hn_range, hn_prime⟩
  have : pi < n := (Finset.mem_Ioc.mp hn_range).1
  omega

/-- Elements of Aset i are odd primes (as ℤ), hence even when added to another odd. -/
lemma add_Aset_Bset_even {i : ℕ} {a b : ℤ}
    (ha : a ∈ Aset i) (hb : b ∈ Bset i) : (a + b) % 2 = (0 : ℤ) := by
  rcases mem_Aset_extract ha with ⟨na, rfl, hna_lo, hna_hi, hna_prime⟩
  rcases mem_Bset_extract hb with ⟨nb, rfl, hnb_lo, hnb_hi, hnb_prime⟩
  have hna_odd : na % 2 = 1 := by
    have h_not_two : na ≠ 2 := by omega
    have h := hna_prime.eq_two_or_odd
    rcases h with (h_eq | h_mod)
    · exact (h_not_two h_eq).elim
    · exact h_mod
  have hnb_odd : nb % 2 = 1 := by
    have h_not_two : nb ≠ 2 := by omega
    have h := hnb_prime.eq_two_or_odd
    rcases h with (h_eq | h_mod)
    · exact (h_not_two h_eq).elim
    · exact h_mod
  push_cast
  have h1 : (na : ℤ) % 2 = (1 : ℤ) := by exact_mod_cast hna_odd
  have h2 : (nb : ℤ) % 2 = (1 : ℤ) := by exact_mod_cast hnb_odd
  calc
    ((na : ℤ) + (nb : ℤ)) % 2 = (((na : ℤ) % 2) + ((nb : ℤ) % 2)) % 2 := by rw [Int.add_emod]
    _ = ((1 : ℤ) + 1) % 2 := by rw [h1, h2]
    _ = 0 := by norm_num

/-- Elements of Aset i + Bset i are in the range (pᵢ, 3pᵢ]. -/
lemma add_Aset_Bset_range {i : ℕ} {a b : ℤ}
    (ha : a ∈ Aset i) (hb : b ∈ Bset i) :
    (primeIdx1 i : ℤ) < a + b ∧ a + b ≤ (3 : ℤ) * (primeIdx1 i : ℤ) := by
  rcases mem_Aset_extract ha with ⟨na, rfl, hna_lo, hna_hi, hna_prime⟩
  rcases mem_Bset_extract hb with ⟨nb, rfl, hnb_lo, hnb_hi, hnb_prime⟩
  constructor
  · push_cast; omega
  · push_cast; omega

/-- C ⊆ S_ℤ (range inclusion): every a+b is even and in (pᵢ, 3pᵢ]. -/
lemma sumset_sub_evens_ℤ {i : ℕ} (hi : 10 ^ 15 < i) :
    PrimeSumset.sumset (Aset i) (Bset i) ⊆
    ((filter (fun n : ℕ => n % 2 = 0) (Ico ((primeIdx1 i : ℕ) + 1) (3 * primeIdx1 i + 1))).image
      (fun n : ℕ => (n : ℤ))) := by
  intro z hz
  rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, rfl⟩
  have h_even : (a + b) % 2 = (0 : ℤ) := add_Aset_Bset_even ha hb
  have h_range := add_Aset_Bset_range ha hb
  set pi : ℕ := primeIdx1 i
  have ha_pos : 0 ≤ a := by
    have ha' : a ∈ PrimeSumset.Aset (primeIdx1 i) := by
      unfold Aset at ha; exact ha
    exact mem_Aset_pos ha'
  have hb_pos : 0 ≤ b := by
    have hb' : b ∈ PrimeSumset.Bset (primeIdx1 i) := by
      unfold Bset at hb; exact hb
    exact mem_Bset_pos hb'
  have h_nonneg : 0 ≤ a + b := by nlinarith
  let k : ℕ := (a + b).toNat
  have hk_cast : (k : ℤ) = a + b := Int.toNat_of_nonneg h_nonneg
  have hk_even : k % 2 = 0 := by
    -- (k : ℤ) % 2 = 0, and k % 2 is either 0 or 1, so it must be 0
    have hz : (k : ℤ) % 2 = (0 : ℤ) := by
      rw [hk_cast, h_even]
    have h_cases : k % 2 = 0 ∨ k % 2 = 1 := by
      have hlt : k % 2 < 2 := Nat.mod_lt k (by norm_num)
      omega
    rcases h_cases with (h | h)
    · exact h
    · have hz' : (k : ℤ) % 2 = (1 : ℤ) := by exact_mod_cast h
      rw [hz] at hz'
      norm_num at hz'
  have hk_lo : (pi : ℕ) < k := by
    rw [← Nat.cast_lt (α := ℤ), hk_cast]
    exact_mod_cast h_range.1
  have hk_hi : k ≤ 3 * pi := by
    rw [← Nat.cast_le (α := ℤ), hk_cast]
    exact_mod_cast h_range.2
  apply Finset.mem_image.mpr
  refine ⟨k, mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hk_even⟩, ?_⟩
  rw [hk_cast]

/-- E as ℤ equals S \ C (where S is evens in range cast to ℤ). -/
lemma eset_eq_sdiff_ℤ {i : ℕ} (hi : 10 ^ 15 < i) :
    let pi : ℕ := primeIdx1 i
    let S_ℕ : Finset ℕ := filter (fun n : ℕ => n % 2 = 0) (Ico (pi + 1) (3 * pi + 1))
    let S : Finset ℤ := S_ℕ.image (fun n : ℕ => (n : ℤ))
    let E_ℕ : Finset ℕ := ExceptionalSet i
    let E_ℤ : Finset ℤ := E_ℕ.image (fun n : ℕ => (n : ℤ))
    E_ℤ = S \ (PrimeSumset.sumset (Aset i) (Bset i)) := by
  intro pi S_ℕ S E_ℕ E_ℤ
  set C := PrimeSumset.sumset (Aset i) (Bset i)
  apply Finset.Subset.antisymm
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    rcases mem_filter.mp hm with ⟨hm_range, ⟨hm_even, hm_lo, hm_hi, hm_zero⟩⟩
    have hmS : (m : ℤ) ∈ S := Finset.mem_image.mpr ⟨m, mem_filter.mpr ⟨hm_range, hm_even⟩, rfl⟩
    refine Finset.mem_sdiff.mpr ⟨hmS, ?_⟩
    intro hmC
    have hpos : 0 < PrimeSumset.rAdd (Aset i) (Bset i) (m : ℤ) :=
      (rAdd_pos_iff.mpr hmC)
    have h_zero : restricted_repr i m = 0 := hm_zero
    rw [restricted_repr] at h_zero
    exact hpos.ne' h_zero
  · intro n hn
    rcases Finset.mem_sdiff.mp hn with ⟨hnS, hn_notC⟩
    rcases Finset.mem_image.mp hnS with ⟨m, hm, rfl⟩
    rcases mem_filter.mp hm with ⟨hm_range, hm_even⟩
    rcases Finset.mem_Ico.mp hm_range with ⟨hlo, hhi⟩
    have hm_lo : pi < m := by omega
    have hm_hi : m ≤ 3 * pi := by omega
    apply Finset.mem_image.mpr
    refine ⟨m, ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨hm_range, hm_even, hm_lo, hm_hi, ?_⟩
    unfold restricted_repr
    by_contra! h_not_zero
    have hpos : 0 < PrimeSumset.rAdd (Aset i) (Bset i) (m : ℤ) := by
      -- h_not_zero : rAdd ... ≠ 0
      apply Nat.pos_of_ne_zero h_not_zero
    have : (m : ℤ) ∈ C := (rAdd_pos_iff.mp hpos)
    exact hn_notC this

/-! ## Main theorem -/

theorem card_sumset_eq_pi_sub_eset {i : ℕ} (hi : 10 ^ 15 < i) :
    ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℕ) = (primeIdx1 i : ℕ) - (ExceptionalSet i).card := by
  set pi : ℕ := primeIdx1 i
  set C : Finset ℤ := PrimeSumset.sumset (Aset i) (Bset i)
  set E : Finset ℕ := ExceptionalSet i

  let S_ℕ : Finset ℕ := filter (fun n : ℕ => n % 2 = 0) (Ico (pi + 1) (3 * pi + 1))
  have hS_nat : S_ℕ.card = pi := card_evens_Ico pi

  let S : Finset ℤ := S_ℕ.image (fun n : ℕ => (n : ℤ))
  have hS_card : S.card = pi := by
    have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
    rw [Finset.card_image_of_injective S_ℕ hinj, hS_nat]

  have hC_sub_S : C ⊆ S := sumset_sub_evens_ℤ hi

  let E_ℤ : Finset ℤ := E.image (fun n : ℕ => (n : ℤ))
  have hE_card_eq : E_ℤ.card = E.card := by
    have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
    apply Finset.card_image_of_injective E hinj

  have hE_eq_sdiff : E_ℤ = S \ C := eset_eq_sdiff_ℤ hi

  have h_disjoint : Disjoint C E_ℤ := by
    rw [hE_eq_sdiff]
    exact Finset.disjoint_sdiff

  have h_union : C ∪ E_ℤ = S := by
    rw [hE_eq_sdiff, Finset.union_sdiff_of_subset hC_sub_S]

  have h_card_union : (C ∪ E_ℤ).card = C.card + E_ℤ.card :=
    Finset.card_union_of_disjoint h_disjoint

  rw [h_union, hS_card, h_card_union, hE_card_eq] at *
  omega

theorem sumset_card_ge_pi_sub_eset {i : ℕ} (hi : 10 ^ 15 < i) :
    (primeIdx1 i : ℝ) - ((ExceptionalSet i).card : ℝ) ≤
    ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) := by
  have h_nat := card_sumset_eq_pi_sub_eset hi
  have hE_le : (ExceptionalSet i).card ≤ primeIdx1 i := by
    let S_ℕ : Finset ℕ := filter (fun n : ℕ => n % 2 = 0) (Ico (primeIdx1 i + 1) (3 * primeIdx1 i + 1))
    have h_card : S_ℕ.card = primeIdx1 i := card_evens_Ico (primeIdx1 i)
    have h_sub : ExceptionalSet i ⊆ S_ℕ := by
      intro x hx
      rcases mem_filter.mp hx with ⟨hx_range, ⟨hx_even, hx_lo, hx_hi, hx_zero⟩⟩
      exact mem_filter.mpr ⟨hx_range, hx_even⟩
    have h_card_le : (ExceptionalSet i).card ≤ S_ℕ.card := Finset.card_le_card h_sub
    rw [h_card] at h_card_le
    exact h_card_le
  have h_real : ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) =
               (primeIdx1 i : ℝ) - ((ExceptionalSet i).card : ℝ) := by
    calc
      ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) =
          (((PrimeSumset.sumset (Aset i) (Bset i)).card : ℕ) : ℝ) := rfl
      _ = (((primeIdx1 i : ℕ) - (ExceptionalSet i).card : ℕ) : ℝ) := by push_cast; rw [h_nat]
      _ = (primeIdx1 i : ℝ) - ((ExceptionalSet i).card : ℝ) := Nat.cast_sub hE_le
  rw [h_real]

theorem sumset_card_gt_904_of_exceptional_bound {i : ℕ} (hi : 10 ^ 15 < i) (η : ℝ) (hη : η < 0.096)
    (hE : (ExceptionalSet i).card < η * (primeIdx1 i : ℝ)) :
    (0.9 : ℝ) * (primeIdx1 i : ℝ) < ((PrimeSumset.sumset (Aset i) (Bset i)).card : ℝ) := by
  have h := sumset_card_ge_pi_sub_eset hi
  have hpos : 0 < primeIdx1 i := primeIdx1_pos (by omega)
  have hp_pos : (0 : ℝ) < (primeIdx1 i : ℝ) := Nat.cast_pos.mpr hpos
  nlinarith

end RestrictedGoldbach
