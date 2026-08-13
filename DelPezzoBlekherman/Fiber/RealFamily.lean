import DelPezzoBlekherman.Fiber.RealCount

noncomputable section

universe u v

namespace RealFiberFamily

variable {Y : Type v} (A : Y → Type u)
variable [∀ y, CommRing (A y)] [∀ y, Algebra ℝ (A y)] [∀ y, Module.Finite ℝ (A y)]

/-- Number of real rational closed points in a member of a real finite-algebra family. -/
def realCount (y : Y) : ℕ := Nat.card (RationalClosedPoint ℝ (A y))

/-- Number of quadratic closed points, equivalently complex-conjugate pairs, in a family member. -/
def pairCount (y : Y) : ℕ := Nat.card (QuadraticClosedPoint ℝ (A y))

/-- Reducedness and constant rank `c+2` supply the exact count equation pointwise on a locus. -/
theorem count_eq_add_two_on
    {Omega : Set Y} {c : ℕ}
    (hReduced : ∀ y ∈ Omega, IsReduced (A y))
    (hRank : ∀ y ∈ Omega, Module.finrank ℝ (A y) = c + 2) :
    ∀ y ∈ Omega, c + 2 = realCount A y + 2 * pairCount A y := by
  intro y hy
  let _ : IsReduced (A y) := hReduced y hy
  exact IsArtinianRing.add_two_eq_rationalClosedPoint_add_two_mul_quadraticClosedPoint
    (hRank y hy)

omit [∀ y, Module.Finite ℝ (A y)] in
/-- A pointwise at-most-one-quadratic-point theorem is exactly the pair-count hypothesis consumed
by the SOS perturbation theorem. -/
theorem pairCount_le_one_on
    {Omega : Set Y}
    (hpairs : ∀ y ∈ Omega, Nat.card (QuadraticClosedPoint ℝ (A y)) ≤ 1) :
    ∀ y ∈ Omega, pairCount A y ≤ 1 := hpairs

omit [∀ y, Module.Finite ℝ (A y)] in
/-- Absence of real rational points is the zero value of the family real-count function. -/
theorem realCount_eq_zero
    (y : Y) (hzero : Nat.card (RationalClosedPoint ℝ (A y)) = 0) :
    realCount A y = 0 := hzero

omit [∀ y, Module.Finite ℝ (A y)] in
/-- If every rational closed point of a fiber lifts to a real source point over the same target,
then a target outside the real map image has real fiber count zero. -/
theorem realCount_eq_zero_of_not_mem_range_of_lift
    {X : Type*} (phi : X → Y) (Omega : Set Y)
    (lift : ∀ y, y ∈ Omega → RationalClosedPoint ℝ (A y) → X)
    (hlift : ∀ y hy q, phi (lift y hy q) = y)
    (y : Y) (hyOmega : y ∈ Omega) (hy : y ∉ Set.range phi) :
    realCount A y = 0 := by
  have hempty : IsEmpty (RationalClosedPoint ℝ (A y)) :=
    ⟨fun q ↦ hy ⟨lift y hyOmega q, hlift y hyOmega q⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl hempty)

end RealFiberFamily
