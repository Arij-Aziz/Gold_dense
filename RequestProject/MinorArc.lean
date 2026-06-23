import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions

open scoped BigOperators Pointwise Classical

/-!
# Minor-arc energy identity (Parseval / orthogonality)

This module introduces the exponential sums

* `S A α = ∑_{a∈A} e(aα)` and `T B α = ∑_{b∈B} e(bα)`  (with `e(t) = exp(2π i t)`),

and proves the exact circle-method identity

* `minor_arc_energy_bound` :
    `∫₀¹ ‖S A α‖² · ‖T B α‖² dα = E(A,B)`,

i.e. the additive energy `E(A,B)` equals the `L²`-integral of the product of the
power spectra of `A` and `B`.  This is the standard Parseval/orthogonality
identity behind the circle method: expanding `‖S‖²‖T‖²` into a quadruple sum and
using `∫₀¹ e(mα) dα = [m = 0]` collapses it to the count of additive quadruples
`a₁+b₁ = a₂+b₂`, which is exactly `energy A B`.

The identity is *unconditional* and holds for arbitrary finite `A B : Finset ℤ`
(it does not use the trigger hypothesis).  The prime instance
`minor_arc_energy_bound` is the requested specialization to `A = Aset (pᵢ)`,
`B = Bset (pᵢ)`; the hypothesis `hi : i > trigger`, included as requested, is not
needed by the proof.
-/

namespace PrimeSumset

open Finset

/-- The exponential sum `S A α = ∑_{a∈A} e(aα)` with `e(t) = exp(2π i t)`. -/
noncomputable def S (A : Finset ℤ) (α : ℝ) : ℂ :=
  ∑ a ∈ A, Complex.exp (((2 * Real.pi * (a : ℝ) * α)) * Complex.I)

/-- The exponential sum `T B α = ∑_{b∈B} e(bα)`; defined identically to `S`. -/
noncomputable def T (B : Finset ℤ) (α : ℝ) : ℂ :=
  ∑ b ∈ B, Complex.exp (((2 * Real.pi * (b : ℝ) * α)) * Complex.I)

/-- `‖S A α‖²` (complexified) expands as the difference exponential sum
`∑_{(a,a')∈A×A} e((a-a')α)`. -/
theorem normSq_S (A : Finset ℤ) (α : ℝ) :
    ((‖S A α‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ A ×ˢ A, Complex.exp (((2 * Real.pi * ((p.1 : ℝ) - p.2) * α)) * Complex.I) := by
  have h0 : ((‖S A α‖ ^ 2 : ℝ) : ℂ) = S A α * (starRingEnd ℂ) (S A α) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h0, S, map_sum, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [← Complex.exp_conj, ← Complex.exp_add]; congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; push_cast; ring

/-- `T` is definitionally the same sum as `S`, so its power spectrum has the same
expansion. -/
theorem normSq_T (B : Finset ℤ) (α : ℝ) :
    ((‖T B α‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ B ×ˢ B, Complex.exp (((2 * Real.pi * ((p.1 : ℝ) - p.2) * α)) * Complex.I) :=
  normSq_S B α

/-- Pointwise: the (real) integrand `‖S A α‖²·‖T B α‖²`, complexified, equals a
single sum over `(A×A)×(B×B)` of `e(((a-a')+(b-b'))α)`. -/
theorem integrand_expand (A B : Finset ℤ) (α : ℝ) :
    ((‖S A α‖ ^ 2 * ‖T B α‖ ^ 2 : ℝ) : ℂ)
      = ∑ r ∈ (A ×ˢ A) ×ˢ (B ×ˢ B),
          Complex.exp ((2 * Real.pi * (((r.1.1 : ℝ) - r.1.2) + ((r.2.1 : ℝ) - r.2.2)) * α)
            * Complex.I) := by
  rw [Complex.ofReal_mul, normSq_S A α, normSq_T B α, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_product]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro q hq
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Orthogonality: `∫₀¹ e(mα) dα = [m = 0]` for integer `m`. -/
theorem integral_exp_int (m : ℤ) :
    (∫ α in (0:ℝ)..1, Complex.exp (((2 * Real.pi * (m : ℝ)) * Complex.I) * (α : ℂ)))
      = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hc : ((2 * Real.pi * (m : ℝ)) * Complex.I) ≠ 0 := by
      push_cast; simp [Complex.I_ne_zero, hpi, hm']
    rw [integral_exp_mul_complex hc, if_neg hm]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, mul_one, Complex.exp_zero]
    have h1 : Complex.exp (((2 * Real.pi * (m : ℝ)) * Complex.I)) = 1 := by
      rw [show ((2 * Real.pi * (m : ℝ)) * Complex.I)
            = ((m : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h1]; simp

/-- The integral of a single quadruple's exponential term, via orthogonality. -/
theorem term_integral (r : (ℤ × ℤ) × (ℤ × ℤ)) :
    (∫ α in (0:ℝ)..1,
        Complex.exp ((2 * Real.pi * (((r.1.1 : ℝ) - r.1.2) + ((r.2.1 : ℝ) - r.2.2)) * α)
          * Complex.I))
      = if ((r.1.1 - r.1.2) + (r.2.1 - r.2.2) : ℤ) = 0 then 1 else 0 := by
  have h : (fun α : ℝ => Complex.exp ((2 * Real.pi
            * (((r.1.1 : ℝ) - r.1.2) + ((r.2.1 : ℝ) - r.2.2)) * α) * Complex.I))
        = (fun α : ℝ => Complex.exp (((2 * Real.pi
            * (((r.1.1 - r.1.2) + (r.2.1 - r.2.2) : ℤ) : ℝ)) * Complex.I) * (α : ℂ))) := by
    funext α; congr 1; push_cast; ring
  rw [h, integral_exp_int]

/-- Each quadruple's exponential term is interval-integrable on `[0,1]`. -/
theorem term_intervalIntegrable (r : (ℤ × ℤ) × (ℤ × ℤ)) :
    IntervalIntegrable
      (fun α : ℝ => Complex.exp ((2 * Real.pi * (((r.1.1 : ℝ) - r.1.2) + ((r.2.1 : ℝ) - r.2.2)) * α)
        * Complex.I)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  apply Complex.continuous_exp.comp; continuity

/-- The quadruple-count bijection: the number of `((a,a'),(b,b')) ∈ (A×A)×(B×B)`
with `(a-a')+(b-b') = 0` equals `energy A B`. -/
theorem card_diff_eq_energy (A B : Finset ℤ) :
    (((A ×ˢ A) ×ˢ (B ×ˢ B)).filter
        (fun r : (ℤ × ℤ) × (ℤ × ℤ) => (r.1.1 - r.1.2) + (r.2.1 - r.2.2) = 0)).card
      = energy A B := by
  rw [energy]
  refine Finset.card_bij'
    (fun r _ => ((r.1.1, r.2.1), (r.1.2, r.2.2)))
    (fun q _ => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ hr
    simp only [Finset.mem_filter, Finset.mem_product] at hr ⊢
    refine ⟨⟨⟨hr.1.1.1, hr.1.2.1⟩, hr.1.1.2, hr.1.2.2⟩, ?_⟩; omega
  · rintro ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
    refine ⟨⟨⟨hq.1.1.1, hq.1.2.1⟩, hq.1.1.2, hq.1.2.2⟩, ?_⟩; omega
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ hr; rfl
  · rintro ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ hq; rfl

/-- **Minor-arc energy identity (general form).**  For arbitrary finite
`A B : Finset ℤ`, `∫₀¹ ‖S A α‖² · ‖T B α‖² dα = E(A,B)`. -/
theorem energy_eq_minor_arc_integral (A B : Finset ℤ) :
    (∫ α in (0:ℝ)..1, ‖S A α‖ ^ 2 * ‖T B α‖ ^ 2) = (energy A B : ℝ) := by
  have key : ((∫ α in (0:ℝ)..1, ‖S A α‖ ^ 2 * ‖T B α‖ ^ 2 : ℝ) : ℂ) = (energy A B : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [integrand_expand A B]
    rw [intervalIntegral.integral_finset_sum (fun r _ => term_intervalIntegrable r)]
    simp_rw [term_integral]
    rw [Finset.sum_boole, card_diff_eq_energy A B]
  exact_mod_cast key

/-- **Minor-arc energy bound (prime instance).**  For every `i > 10^15`, with
`x = pᵢ`, `A = Aset x`, `B = Bset x`, the additive energy equals the minor-arc
`L²`-integral of the power spectra:
`∫₀¹ ‖S A α‖² · ‖T B α‖² dα = E(A,B)`.

This is the exact Parseval/orthogonality identity of the circle method; it holds
unconditionally for all finite `A, B`, so the hypothesis `hi : i > trigger`
(included as requested) is not used by the proof. -/
theorem minor_arc_energy_bound {i : ℕ} (hi : i > trigger) :
    ∫ α in (0:ℝ)..1,
        ‖S (Aset (primeIdx i)) α‖ ^ 2 * ‖T (Bset (primeIdx i)) α‖ ^ 2
      = (energy (Aset (primeIdx i)) (Bset (primeIdx i)) : ℝ) :=
  energy_eq_minor_arc_integral (Aset (primeIdx i)) (Bset (primeIdx i))

end PrimeSumset
