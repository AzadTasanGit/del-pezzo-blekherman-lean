import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.RankNullity

noncomputable section

universe u v w

open LinearMap

namespace LinearMap.BilinForm

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Pull a bilinear form on `V/W` back to `V`. -/
def pullbackQuotient (W : Submodule K V)
    (B : LinearMap.BilinForm K (V ⧸ W)) : LinearMap.BilinForm K V :=
  B.comp W.mkQ W.mkQ

@[simp]
theorem pullbackQuotient_apply (W : Submodule K V) (B : LinearMap.BilinForm K (V ⧸ W))
    (x y : V) : pullbackQuotient W B x y = B (W.mkQ x) (W.mkQ y) :=
  rfl

/-- Pulling a nondegenerate form back from a quotient makes the quotient submodule exactly its
left radical.  This is the linear-algebra heart of the Artinian Gorenstein kernel argument. -/
theorem ker_pullbackQuotient_eq (W : Submodule K V)
    (B : LinearMap.BilinForm K (V ⧸ W))
    (hB : B.Nondegenerate) : LinearMap.ker (pullbackQuotient W B) = W := by
  apply le_antisymm
  · intro x hx
    have hx' : pullbackQuotient W B x = 0 := LinearMap.mem_ker.mp hx
    have hqx : W.mkQ x = 0 := hB.1 _ fun z ↦ by
      obtain ⟨y, rfl⟩ := W.mkQ_surjective z
      have hy := LinearMap.congr_fun hx' y
      simpa only [pullbackQuotient_apply, LinearMap.zero_apply] using hy
    rw [← Submodule.ker_mkQ W, LinearMap.mem_ker]
    exact hqx
  · intro x hx
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    have hqx : W.mkQ x = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hx
    simp [pullbackQuotient, hqx]

/-- The finite rank of a bilinear form, defined as the dimension of the range of its associated
map to the dual. -/
def finiteRank [Module.Finite K V] (B : LinearMap.BilinForm K V) : ℕ :=
  Module.finrank K B.range

/-- A nondegenerate form on `V/W`, pulled back to `V`, has rank `dim(V/W)`. -/
theorem finiteRank_pullbackQuotient_eq [Module.Finite K V]
    (W : Submodule K V) (B : LinearMap.BilinForm K (V ⧸ W)) (hB : B.Nondegenerate) :
    finiteRank (pullbackQuotient W B) = Module.finrank K (V ⧸ W) := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (pullbackQuotient W B)
  rw [ker_pullbackQuotient_eq W B hB] at hrank
  have hquot := W.finrank_quotient_add_finrank
  unfold finiteRank
  omega

end LinearMap.BilinForm

/-- The special Artinian Gorenstein datum used in the paper: multiplication in degree one,
followed by an identification of the one-dimensional socle with the base field, is a perfect
pairing.  This avoids assuming any kernel or rank conclusion. -/
structure ArtinianGorensteinDegreeOneCertificate
    (K : Type u) (Q : Type v) (S : Type w)
    [Field K] [AddCommGroup Q] [Module K Q]
    [AddCommGroup S] [Module K S] where
  mul11 : Q →ₗ[K] Q →ₗ[K] S
  socleEquiv : S ≃ₗ[K] K
  perfect : (mul11.compr₂ socleEquiv.toLinearMap).Nondegenerate

namespace ArtinianGorensteinDegreeOneCertificate

variable {K : Type u} {V : Type v} {S : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup S] [Module K S]

/-- A one-dimensional socle is (noncanonically) linearly equivalent to the base field. -/
noncomputable def socleEquivOfFinrankEqOne [Module.Free K S]
  (hS : Module.finrank K S = 1) : S ≃ₗ[K] K :=
  (Module.nonempty_linearEquiv_of_finrank_eq_one hS).some.symm

/-- Build the degree-one Gorenstein certificate directly from multiplication, the Hilbert
function value `dim S = 1`, and nondegeneracy of the induced scalar pairing. -/
noncomputable def ofMulOfSocleFinrankOne [Module.Free K S]
    (mul11 : (V →ₗ[K] V →ₗ[K] S))
    (hS : Module.finrank K S = 1)
    (hperfect : (mul11.compr₂ (socleEquivOfFinrankEqOne hS).toLinearMap).Nondegenerate) :
    ArtinianGorensteinDegreeOneCertificate K V S where
  mul11 := mul11
  socleEquiv := socleEquivOfFinrankEqOne hS
  perfect := hperfect

/-- The scalar-valued perfect degree-one multiplication form. -/
def socleForm (W : Submodule K V)
    (h : ArtinianGorensteinDegreeOneCertificate K (V ⧸ W) S) :
    LinearMap.BilinForm K (V ⧸ W) :=
  h.mul11.compr₂ h.socleEquiv.toLinearMap

/-- The Hankel form on the original degree-one space obtained from the Artinian quotient. -/
def hankelForm (W : Submodule K V)
    (h : ArtinianGorensteinDegreeOneCertificate K (V ⧸ W) S) :
    LinearMap.BilinForm K V :=
  LinearMap.BilinForm.pullbackQuotient W (socleForm W h)

/-- The radical of the induced Hankel form is exactly the parameter space `W`. -/
theorem ker_hankelForm_eq (W : Submodule K V)
    (h : ArtinianGorensteinDegreeOneCertificate K (V ⧸ W) S) :
    LinearMap.ker (hankelForm W h) = W :=
  LinearMap.BilinForm.ker_pullbackQuotient_eq W (socleForm W h) h.perfect

/-- Consequently the Hankel rank is the degree-one dimension of the Artinian quotient. -/
theorem finiteRank_hankelForm_eq [Module.Finite K V] (W : Submodule K V)
    (h : ArtinianGorensteinDegreeOneCertificate K (V ⧸ W) S) :
    LinearMap.BilinForm.finiteRank (hankelForm W h) = Module.finrank K (V ⧸ W) :=
  LinearMap.BilinForm.finiteRank_pullbackQuotient_eq W (socleForm W h) h.perfect

/-- If `dim V = m + c + 1` and the Artinian degree-one quotient has dimension `c`, then the
parameter space has dimension `m + 1`. -/
theorem finrank_parameterSpace_eq_add_one [Module.Finite K V]
    (W : Submodule K V) {m c : ℕ}
    (hV : Module.finrank K V = m + c + 1)
    (hQ : Module.finrank K (V ⧸ W) = c) :
    Module.finrank K W = m + 1 := by
  have hdim := W.finrank_quotient_add_finrank
  omega

/-- Conversely, if the ambient degree-one space has dimension `m+c+1` and the chosen
parameter space has dimension `m+1`, then its degree-one quotient has dimension `c`.  This is
the direction used after choosing the homogeneous parameters in PDF Theorem 4.3. -/
theorem finrank_quotient_eq_of_parameterSpace_finrank [Module.Finite K V]
    (W : Submodule K V) {m c : ℕ}
    (hV : Module.finrank K V = m + c + 1)
    (hW : Module.finrank K W = m + 1) :
    Module.finrank K (V ⧸ W) = c := by
  have hdim := W.finrank_quotient_add_finrank
  omega

/-- The precise dimension/rank conclusion used in Theorem 4.3: perfect Artinian Gorenstein
degree-one pairing plus the two Hilbert-function dimensions forces `dim W = m+1` and Hankel
rank `c`. -/
theorem parameterSpace_finrank_and_hankelRank [Module.Finite K V]
    (W : Submodule K V)
    (h : ArtinianGorensteinDegreeOneCertificate K (V ⧸ W) S)
    {m c : ℕ}
    (hV : Module.finrank K V = m + c + 1)
    (hQ : Module.finrank K (V ⧸ W) = c) :
    Module.finrank K W = m + 1 ∧
      LinearMap.BilinForm.finiteRank (hankelForm W h) = c := by
  exact ⟨finrank_parameterSpace_eq_add_one W hV hQ,
    (finiteRank_hankelForm_eq W h).trans hQ⟩

end ArtinianGorensteinDegreeOneCertificate
