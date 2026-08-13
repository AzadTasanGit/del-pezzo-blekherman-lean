import DelPezzoBlekherman.Geometry.RealProjective.HVectorRationalLift
import DelPezzoBlekherman.Fiber.RealFamily

noncomputable section

universe u v

namespace RealProjectiveCoordinateFiber

variable {C I : Type} {W : Type u} [Fintype I]
variable [CommRing C] [IsDomain C] [Algebra ℝ C]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Real algebra points whose chosen degree-one generator values define a projective direction. -/
abbrev NonzeroGeneratorRealPoint (b : Module.Basis I ℝ W) (g : I → C) :=
  {a : C →ₐ[ℝ] ℝ //
    RealProjectiveTopology.basisContinuousLinearEquiv b (fun i ↦ a (g i)) ≠ 0}

/-- The canonical projective direction of a real algebra point with nonzero generator vector. -/
def generatorDirection (b : Module.Basis I ℝ W) (g : I → C) :
    NonzeroGeneratorRealPoint b g → RealProjectiveTopology.Direction W :=
  fun a ↦ RealProjectiveTopology.directionOf W
    ⟨RealProjectiveTopology.basisContinuousLinearEquiv b
      (fun i ↦ (a.1 : C →ₐ[ℝ] ℝ) (g i)), a.2⟩

/-- Rational points of the concrete good fibers force the real-fiber count to vanish outside
the projective image. It is enough to realize real algebra points of `C` in the source and to
identify their generator-value directions with the projective map. -/
theorem hVectorGoodFiber_realCount_eq_zero_outside_range
    {X : Type v} (phi : X → RealProjectiveTopology.Direction W)
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    (realize : NonzeroGeneratorRealPoint b g → X)
    (hrealize : ∀ a : NonzeroGeneratorRealPoint b g,
      phi (realize a) = RealProjectiveTopology.directionOf W
        ⟨RealProjectiveTopology.basisContinuousLinearEquiv b
          (fun i ↦ (a.1 : C →ₐ[ℝ] ℝ) (g i)), a.2⟩) :
    ∀ y ∈ hVectorGoodOmega b CC g hg h, y ∉ Set.range phi →
      RealFiberFamily.realCount (hVectorGoodFiber b CC g hg h) y = 0 := by
  let lift : ∀ y, y ∈ hVectorGoodOmega b CC g hg h →
      RationalClosedPoint ℝ (hVectorGoodFiber b CC g hg h y) → X :=
    fun y hy q ↦ realize
      ⟨hVectorSourceAlgHomOfRationalFiberPoint b CC g hg h y q,
        hVectorSourceAlgHomOfRationalFiberPoint_generator_ne_zero b CC g hg h hy q⟩
  have hlift : ∀ y hy q, phi (lift y hy q) = y := by
    intro y hy q
    dsimp only [lift]
    rw [hrealize]
    exact directionOf_hVectorSourceAlgHomOfRationalFiberPoint_generators
      b CC g hg h hy q
  intro y hyOmega hy
  exact RealFiberFamily.realCount_eq_zero_of_not_mem_range_of_lift
    (hVectorGoodFiber b CC g hg h) phi (hVectorGoodOmega b CC g hg h)
    lift hlift y hyOmega hy

/-- In the canonical source consisting of nonzero real algebra points, the outside-image
zero-count theorem has no remaining lift or realization assumption. -/
theorem hVectorGoodFiber_realCount_eq_zero_outside_generatorDirection
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c) :
    ∀ y ∈ hVectorGoodOmega b CC g hg h,
      y ∉ Set.range (generatorDirection b g) →
        RealFiberFamily.realCount (hVectorGoodFiber b CC g hg h) y = 0 := by
  apply hVectorGoodFiber_realCount_eq_zero_outside_range
    (generatorDirection b g) b CC g hg h (fun a ↦ a)
  intro a
  rfl

end RealProjectiveCoordinateFiber
