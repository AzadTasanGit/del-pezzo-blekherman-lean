import DelPezzoBlekherman.Fiber.ReducedAlgebra
import DelPezzoBlekherman.LinearAlgebra.NonrealPairInertia

noncomputable section

universe u v

namespace IsArtinianRing

/-- The real-fiber count theorem with the at-most-one-pair hypothesis discharged by the inertia
argument: independent negative directions contributed by the quadratic closed points inside an
index-one form force at most one such point. -/
theorem real_reduced_fiber_rational_point_dichotomy_of_inertia
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V)
    (hpairs : QuadraticForm.NonrealPairNegativeDirections Q
      (QuadraticClosedPoint ℝ A))
    (hindex : sigNeg Q ≤ 1)
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) :=
  real_reduced_fiber_rational_point_dichotomy hrank (hpairs.card_le_one hindex)

/-- Restriction version matching the paper's hyperplane setup: if the fiber relation lives on a
subspace of an ambient Lorentzian space, negative index monotonicity still gives the result. -/
theorem real_reduced_fiber_rational_point_dichotomy_of_restricted_inertia
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (W : Submodule ℝ V)
    (hpairs : QuadraticForm.NonrealPairNegativeDirections (Q.restrict W)
      (QuadraticClosedPoint ℝ A))
    (hindex : sigNeg Q ≤ 1)
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) :=
  real_reduced_fiber_rational_point_dichotomy hrank
    (hpairs.card_le_one_of_restrict hindex)

/-- Hyperplane formulation: nonnegativity on a codimension-one subspace plus the independent
negative directions contributed by nonreal pairs directly yields the real-fiber dichotomy. -/
theorem real_reduced_fiber_rational_point_dichotomy_of_nonneg_hyperplane
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V)
    (hpairs : QuadraticForm.NonrealPairNegativeDirections Q
      (QuadraticClosedPoint ℝ A))
    (W : Submodule ℝ V)
    (hcodim : Module.finrank ℝ V = Module.finrank ℝ W + 1)
    (hnonneg : ∀ x ∈ W, 0 ≤ Q x)
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) :=
  real_reduced_fiber_rational_point_dichotomy hrank
    (hpairs.card_le_one_of_nonneg_hyperplane W hcodim hnonneg)

/-- Evaluation-relation formulation: if the relation is a nonzero functional and the ambient
quadratic form is nonnegative on its kernel, the same conclusion follows. -/
theorem real_reduced_fiber_rational_point_dichotomy_of_nonneg_relationKernel
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V)
    (hpairs : QuadraticForm.NonrealPairNegativeDirections Q
      (QuadraticClosedPoint ℝ A))
    (relation : Module.Dual ℝ V) (hrelation : relation ≠ 0)
    (hnonneg : ∀ x, relation x = 0 → 0 ≤ Q x)
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) :=
  real_reduced_fiber_rational_point_dichotomy hrank
    (hpairs.card_le_one_of_nonneg_ker relation hrelation hnonneg)

end IsArtinianRing
