import DeJongAlterations.Algebra.NodeFittingGeometricNodeSupport
import DeJongAlterations.Algebra.NodeFittingGeometricIdealSheaf

/-! # The SAME actual lift of an original Fitting-support point is nonsmooth

The generic support transfer uses the ENTIRE native stalk ideal and native local
stalk map. No chosen residue identification or geometric-point certificate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingSupportPullback

open NodeFittingIdealSheaf NodeFittingGeometricNodeSupport
  Geometry.NodeCompletedLocalGeometricChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y S : Scheme.{u}}

/-- The ENTIRE original stalk ideal and actual local stalk map transfer support to the SAME actual point. -/
theorem mem_comap_support_of_mem_support (I : X.IdealSheafData) (g : Y ⟶ X) (y : Y)
    (hy : g y ∈ I.support) : y ∈ (I.comap g).support := by
  apply (mem_support_iff_stalkIdeal_le_maximalIdeal (I.comap g) y).mpr
  rw [stalkIdeal_comap]
  exact (Ideal.map_mono ((mem_support_iff_stalkIdeal_le_maximalIdeal I (g y)).mp hy)).trans
    (map_maximalIdeal_le (g.stalkMap y).hom)

/-- Any prescribed actual lift retains the original closed support, without a residue-field isomorphism input. -/
theorem mem_comap_support_of_image_eq (I : X.IdealSheafData) (g : Y ⟶ X)
    (x : X) (y : Y) (hy : g y = x) (hx : x ∈ I.support) : y ∈ (I.comap g).support := by
  apply mem_comap_support_of_mem_support I g y
  simpa only [hy] using hx

variable (f : X ⟶ S) [LocallyOfFinitePresentation f] (s : S)
  (K : Type u) [Field K] [Algebra (S.residueField s) K] [PerfectField K]

local notation "Z" => OriginalGeometricScheme f s K
local notation "π" => pullback.fst f (originalFieldMap s K)
local notation "q" => pullback.snd f (originalFieldMap s K)

/-- The SAME actual geometric lift of an original Sing point cannot be in the actual geometric smooth locus. -/
theorem geometric_not_smooth_of_original_mem_support (hdim : topologicalKrullDim Z ≤ 1)
    (y : Z) (hy : π y ∈ (NodeFittingOmegaGluing.idealSheaf f 1).support) :
    y ∉ (q).smoothLocus := by
  intro hs
  exact NodeFittingGeometricIdealSheaf.not_mem_originalPullback_support_of_mem_smoothLocus
    f s K hdim y hs
    (mem_comap_support_of_mem_support (NodeFittingOmegaGluing.idealSheaf f 1) π y hy)

end DeJongAlterations.Algebra.NodeFittingSupportPullback
