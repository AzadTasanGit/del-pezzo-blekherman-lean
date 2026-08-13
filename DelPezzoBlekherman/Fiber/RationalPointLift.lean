import DelPezzoBlekherman.Fiber.ReducedAlgebra

noncomputable section

universe u v

namespace RationalClosedPoint

variable {F : Type u} {A : Type v}
variable [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]

/-- The residue field of a rational closed point is canonically (up to the chosen inverse) an
`F`-algebra isomorphic to `F`. -/
noncomputable def residueAlgEquiv (p : RationalClosedPoint F A) :
    (A ⧸ p.1.asIdeal) ≃ₐ[F] F := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite F A
  letI : Field (A ⧸ p.1.asIdeal) :=
    IsArtinianRing.fieldOfSubtypeIsMaximal (R := A) p.1
  apply (AlgEquiv.ofBijective (Algebra.ofId F (A ⧸ p.1.asIdeal)) ?_).symm
  constructor
  · exact FaithfulSMul.algebraMap_injective F (A ⧸ p.1.asIdeal)
  · exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (Algebra.ofId F (A ⧸ p.1.asIdeal)).toLinearMap)
      (by simpa only [Module.finrank_self] using p.2.symm)).mp
        (FaithfulSMul.algebraMap_injective F (A ⧸ p.1.asIdeal))

/-- A rational closed point of a finite `F`-algebra induces an actual `F`-algebra-valued point. -/
noncomputable def algHom (p : RationalClosedPoint F A) : A →ₐ[F] F :=
  (residueAlgEquiv p).toAlgHom.comp (Ideal.Quotient.mkₐ F p.1.asIdeal)

end RationalClosedPoint
