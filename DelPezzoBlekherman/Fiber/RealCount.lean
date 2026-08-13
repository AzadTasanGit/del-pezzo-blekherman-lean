import DelPezzoBlekherman.Fiber.ReducedAlgebra

noncomputable section

universe u

namespace IsArtinianRing

/-- A reduced finite real algebra has length equal to its number of real rational closed points
plus twice its number of quadratic (complex-conjugate-pair) closed points. -/
theorem real_finrank_eq_rationalClosedPoint_add_two_mul_quadraticClosedPoint
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A] :
    Module.finrank ℝ A =
      Nat.card (RationalClosedPoint ℝ A) +
        2 * Nat.card (QuadraticClosedPoint ℝ A) := by
  have hlength := real_finrank_eq_natCard_add_natCard_quadraticClosedPoint (A := A)
  have hclosed := MaximalSpectrum.natCard_eq_natCard_rationalClosedPoint_add_quadraticClosedPoint
    (F := ℝ) (F' := ℂ) (A := A) Complex.finrank_real_complex
  omega

/-- Fiber-rank form of the exact count equation used in the perturbation proof. -/
theorem add_two_eq_rationalClosedPoint_add_two_mul_quadraticClosedPoint
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2) :
    c + 2 = Nat.card (RationalClosedPoint ℝ A) +
      2 * Nat.card (QuadraticClosedPoint ℝ A) := by
  rw [← hrank]
  exact real_finrank_eq_rationalClosedPoint_add_two_mul_quadraticClosedPoint

/-- If a reduced fiber has no real rational closed point, size `c+2`, and at most one quadratic
point, then `c≥1` is impossible. This is the exact terminal contradiction of Theorem 8.3. -/
theorem exists_rationalClosedPoint_of_finrank_add_two_of_pair_le_one
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {c : ℕ} (hc : 1 ≤ c) (hrank : Module.finrank ℝ A = c + 2)
    (hpairs : Nat.card (QuadraticClosedPoint ℝ A) ≤ 1) :
    0 < Nat.card (RationalClosedPoint ℝ A) := by
  have hcount :=
    add_two_eq_rationalClosedPoint_add_two_mul_quadraticClosedPoint (A := A) hrank
  omega

end IsArtinianRing
