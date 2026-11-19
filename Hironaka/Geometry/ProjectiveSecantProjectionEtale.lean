import Hironaka.Geometry.ProjectiveSecantProjectionDominant
import Hironaka.Geometry.ProjectiveSecantProjectionGenericEtale

/-!
# Genuine generic etaleness of the same original codimension-one projective projection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveProjectionPoint ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X = n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
  (hout : pointImage k n p ∉ Set.range i)
  (hc : pointImage k n p ∈ originalTangentOpen k n i s hs hdim.le hx)

include s hs hdim hx hc

/-- Original geometric dimension, actual rational smooth point and actual tangent avoidance internally produce native generic etaleness of the SAME frozen original finite projection. No dominance, flatness, unramifiedness or generic-etaleness certificate is supplied. -/
theorem originalProjection_isGenericallyEtale :
    IsGenericallyEtale (projectionFromPoint k n p hp i hout) := by
  let f := projectionFromPoint k n p hp i hout
  let : IsFinite f := projectionFromPoint_isFinite k n p hp i hout
  let : IsDominant f := originalProjection_isDominant_of_dimension_eq k n i p hp hout hdim
  let : IsLocallyNoetherian (projectiveSpace k n) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceStructure k n)
  exact genericallyEtale_of_formallyUnramified_stalk f (s (⊥ : PrimeSpectrum k))
    (projectionFromPoint_stalkMap_formallyUnramified k n i p hp s hs hdim.le hx hout hc)

/-- The SAME original transverse codimension-one projection is actually etale over an internally produced dense original target open containing its original generic point. -/
theorem exists_originalProjection_dense_target_etale_open :
    ∃ V : (projectiveSpace k n).Opens, genericPoint (projectiveSpace k n) ∈ V ∧
      Dense (V : Set (projectiveSpace k n)) ∧ Etale (projectionFromPoint k n p hp i hout ∣_ V) := by
  let f := projectionFromPoint k n p hp i hout
  let : IsFinite f := projectionFromPoint_isFinite k n p hp i hout
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (i ≫ projectiveSpaceStructure k (n + 1))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (i ≫ projectiveSpaceStructure k (n + 1))
  let : IsNoetherian X := .mk
  exact FiniteGenericallyEtaleOpen.exists_dense_target_etale_open f
    (originalProjection_isGenericallyEtale k n i p hp s hs hdim hx hout hc)

end Hironaka.Geometry.ProjectiveSecant
