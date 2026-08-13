import DelPezzoBlekherman.Fiber.ComplexBlock
import DelPezzoBlekherman.Fiber.RealFamily

noncomputable section

universe u v

namespace RealFiberFamily

variable {Y : Type u} (A : Y → Type v)
variable [∀ y, CommRing (A y)] [∀ y, Algebra ℝ (A y)]
variable [∀ y, Fintype (QuadraticClosedPoint ℝ (A y))]
variable [∀ y, DecidableEq (QuadraticClosedPoint ℝ (A y))]

/-- The normalized complex-block argument supplies the at-most-one-quadratic-point condition
uniformly over a reduced locus in a finite real-algebra family. -/
theorem pairCount_le_one_of_normalizedComplexBlocks
    (Omega : Set Y)
    (coeff : ∀ y, QuadraticClosedPoint ℝ (A y) → ℂ)
    (hnonneg : ∀ y ∈ Omega, ∀ z,
      QuadraticForm.NonrealPairNegativeDirections.complexRelationOne z = 0 →
      0 ≤ QuadraticForm.NonrealPairNegativeDirections.complexBlockForm (coeff y) z)
    (hnonisotropic : ∀ y ∈ Omega, ∀ p,
      QuadraticForm.NonrealPairNegativeDirections.complexBlockForm (coeff y)
        (Pi.single p Complex.I) ≠ 0) :
    ∀ y ∈ Omega, pairCount A y ≤ 1 := by
  intro y hy
  exact QuadraticForm.NonrealPairNegativeDirections.card_le_one_of_nonnegative_relationOne
    (coeff y) (hnonneg y hy) (hnonisotropic y hy)

end RealFiberFamily
