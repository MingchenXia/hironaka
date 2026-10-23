import DeJongAlterations.Algebra.NodeFittingOriginalGeometricStalk
import DeJongAlterations.Algebra.NodeFittingExternalBaseStalk
import DeJongAlterations.Algebra.NodeFittingSmoothScheme

/-! # ENTIRE actual geometric Fitting ideal sheaf and ORIGINAL-family smooth-point deletion -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Algebra.NodeFittingGeometricIdealSheaf

open NodeFittingIdealSheaf Geometry.NodeCompletedLocalGeometricChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K]

local notation "Y" => OriginalGeometricScheme f s K
local notation "π" => pullback.fst f (originalFieldMap s K)
local notation "q" => pullback.snd f (originalFieldMap s K)

/-- ENTIRE idealSheafData equality for the actual ORIGINAL geometric base change, every Fitting index. -/
theorem originalPullback_eq_geometricIdealSheaf (i : ℕ) :
    (NodeFittingOmegaGluing.idealSheaf f i).comap π = NodeFittingOmegaGluing.idealSheaf q i := by
  apply ext_stalkIdeal
  intro y
  exact (NodeFittingOriginalGeometricStalk.originalFittingStalkIdeal_eq_nativeOmega f s K y i).trans
    ((NodeFittingOmegaGluing.idealSheaf_stalk q i y).trans
      (NodeFittingExternalBaseStalk.stalkFittingIdeal_eq_nativeOmega K q y i)).symm

/-- EVERY actual geometric smooth point avoids the support of the ENTIRE pulled ORIGINAL family ideal. -/
theorem not_mem_originalPullback_support_of_mem_smoothLocus [PerfectField K]
    (hdim : topologicalKrullDim (Y) ≤ 1) (y : Y) (hy : y ∈ (q).smoothLocus) :
    y ∉ ((NodeFittingOmegaGluing.idealSheaf f 1).comap π).support := by
  rw [originalPullback_eq_geometricIdealSheaf]
  let B := Γ(Spec (.of K), ⊤)
  let e : B ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have hField : IsField B := e.toMulEquiv.isField (Field.toIsField K)
  let : Field B := hField.toField
  let : PerfectField B := PerfectField.of_ringEquiv e.symm
  exact NodeFittingSmoothScheme.not_mem_support_of_mem_smoothLocus q hField inferInstance hdim y hy

/-- The ACTUAL pulled ORIGINAL singular closed-subscheme inclusion has no smooth geometric image point. -/
theorem originalPullback_subscheme_image_not_mem_smoothLocus [PerfectField K]
    (hdim : topologicalKrullDim (Y) ≤ 1)
    (z : ((NodeFittingOmegaGluing.idealSheaf f 1).comap π).subscheme) :
    ((NodeFittingOmegaGluing.idealSheaf f 1).comap π).subschemeι z ∉ (q).smoothLocus := by
  intro hz
  apply not_mem_originalPullback_support_of_mem_smoothLocus f s K hdim _ hz
  have hmem : ((NodeFittingOmegaGluing.idealSheaf f 1).comap π).subschemeι z ∈
      Set.range ((NodeFittingOmegaGluing.idealSheaf f 1).comap π).subschemeι := ⟨z, rfl⟩
  rw [((NodeFittingOmegaGluing.idealSheaf f 1).comap π).range_subschemeι] at hmem
  exact hmem

end DeJongAlterations.Algebra.NodeFittingGeometricIdealSheaf
