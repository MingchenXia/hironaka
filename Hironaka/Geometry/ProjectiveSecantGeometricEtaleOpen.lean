import Hironaka.Geometry.ProjectiveSecantProjectionTangentFamilyOpen
import Hironaka.Geometry.ProjectiveSecantGeometricComponentPoints
import Hironaka.Geometry.FiberDimensionUpperSemicontinuityClosedCover

/-!
# Genuine original generic-etale centre open from the paper's original pure-dimensional geometric hypotheses
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveRationalPointCoordinates ProjectiveProjectionPoint

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The paper's actual original pure-dimensional closed source and dense geometric open internally construct a nonempty original centre open with native GE of EVERY same original finite rational-centre projection, over separably closed original fields which may be imperfect. -/
theorem exists_original_genericallyEtale_center_open_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (U : X.Opens) (hU : Dense (U : Set X))
    [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k (n + 1)))]
    (hpure : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n) :
    ∃ O : (projectiveSpace k (n + 1)).Opens, (O : Set (projectiveSpace k (n + 1))).Nonempty ∧
      ∀ (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
        (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _), pointImage k n p ∈ O →
        ∃ hout : pointImage k n p ∉ Set.range i,
          IsFinite (projectionFromPoint k n p hp i hout) ∧
          projectionFromPoint k n p hp i hout ≫ projectiveSpaceStructure k n =
            i ≫ projectiveSpaceStructure k (n + 1) ∧
          IsGenericallyEtale (projectionFromPoint k n p hp i hout) := by
  have hdim : topologicalKrullDim X ≤ n := by
    rw [FiberDimensionUpperSemicontinuityClosedCover.topologicalKrullDim_eq_iSup_componentDimension]
    exact iSup_le fun C : irreducibleComponents X => (hpure C.1 C.2).le
  let : IsNoetherian X := originalProjectiveSource_isNoetherian k (n + 1) i
  let : Finite (irreducibleComponents X) := finite_irreducibleComponents_of_isNoetherian
  choose s hsC _ hs hsx using (fun C : irreducibleComponents X =>
    exists_original_rational_smooth_component_point k (n + 1) i U hU C.1 C.2)
  have hcover : ∀ C ∈ irreducibleComponents X, ∃ a, s a (⊥ : PrimeSpectrum k) ∈ C := by
    intro C hC
    exact ⟨⟨C, hC⟩, hsC ⟨C, hC⟩⟩
  let O := tangentPointFamilyCenterOpen k n i s hs hsx hdim
  refine ⟨O, tangentPointFamilyCenterOpen_nonempty k n i s hs hsx hdim, ?_⟩
  intro p hp hc
  refine ⟨hc.2, projectionFromPoint_isFinite k n p hp i hc.2,
    projectionFromPoint_structure k n p hp i hc.2, ?_⟩
  exact projectionFromTangentPointFamilyOpen_isGenericallyEtale k n i s hs hsx hdim hpure hcover p hp hc

end Hironaka.Geometry.ProjectiveSecant
