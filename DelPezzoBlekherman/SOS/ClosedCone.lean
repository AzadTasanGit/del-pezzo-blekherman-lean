/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Convexity.GramCone
import DelPezzoBlekherman.SOS.DualCone

/-!
# Closed Gram-represented SOS cones

This module transfers the closedness theorem for finite sums of squares to the
convex-cone realization used by `SOSConeDual`.
-/

namespace SOSConeDual

noncomputable section

/-- A Gram representation with no nonzero positive semidefinite kernel element
makes the corresponding SOS convex cone closed. -/
theorem sosCone_isClosed_of_gram
    {n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (DelPezzoBlekherman.rankOneGram q) = sq q)
    (hker : ∀ A ∈ DelPezzoBlekherman.realGramCone n, T A = 0 → A = 0) :
    IsClosed (sosCone sq : Set W) := by
  rw [sosCone_eq_finiteSumCone sq]
  · exact DelPezzoBlekherman.finiteSumCone_isClosed_of_gram sq T hgram hker
  · intro a ha q
    refine ⟨Real.sqrt a • q, ?_⟩
    rw [← hgram, DelPezzoBlekherman.rankOneGram_smul, map_smul,
      Real.sq_sqrt ha, hgram]

end

end SOSConeDual
