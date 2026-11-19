import Hironaka.Geometry.ProjectiveSecantOriginalBirationalParameter
import Hironaka.Geometry.ProjectiveSecantOriginalEtaleParameter
import Hironaka.Geometry.ProjectiveSecantSeparableProjectionDescent

/-!
# The actual original general-position open works over EVERY finite separable field

These are the genuine original-source two conclusions of de Jong Lemma 2.11:
finite and birational onto the entire native image in small dimension, and
finite and generically etale for the actual pure codimension-one original source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveRationalPointCoordinates ProjectiveProjectionPoint BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (U : X.Opens) (hU : Dense (U : Set X))
  [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k (n + 1)))]

include hU

/-- The actual nonempty ORIGINAL parameter open produces the SAME finite projection birational onto its ENTIRE native image for EVERY finite separable original extension and actual centre. No scalar source, open, geometric point, coordinate, image or birationality certificate is supplied. -/
theorem exists_original_birational_parameter_open (hdim : topologicalKrullDim X < n) :
    ∃ O : (projectiveSpace k (n + 1)).Opens, (O : Set (projectiveSpace k (n + 1))).Nonempty ∧
      (O : Set (projectiveSpace k (n + 1))) ⊆ (Set.range i)ᶜ ∧
      ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
        (p : Spec (.of L) ⟶ projectiveSpace L (n + 1))
        (hp : p ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _),
        projectiveCoefficientMap (algebraMap k L) (n + 1) (pointImage L n p) ∈ O →
        ∃ hout : pointImage L n p ∉ Set.range (scalarClosedInclusion k L (algebraMap k L) n i),
          let f := projectionFromPoint L n p hp (scalarClosedInclusion k L (algebraMap k L) n i) hout
          IsFinite f ∧ f ≫ projectiveSpaceStructure L n =
            scalarClosedInclusion k L (algebraMap k L) n i ≫ projectiveSpaceStructure L (n + 1) ∧
          Scheme.BirationalOver f.toImage (𝟙 f.image) := by
  obtain ⟨O, hO, houtO, hgood⟩ :=
    exists_original_birational_parameter_open_over_separableClosure k n i U hU hdim
  refine ⟨O, hO, houtO, ?_⟩
  intro L _ _ _ _ p hp hpO
  let hout := scalarCenter_outside_of_original_image k L n i p (houtO hpO)
  obtain ⟨_, _, _, hBR⟩ := hgood (separableClosureCenter k L n p hp)
    (separableClosureCenter_structure k L n p hp)
    (separableClosureCenter_mem_original_open k L n p hp O hpO)
  refine ⟨hout, projectionFromPoint_isFinite L n p hp _ hout,
    projectionFromPoint_structure L n p hp _ hout, ?_⟩
  exact projectionFromPoint_toImage_birationalOver_of_separableClosure k L n i p hp hout hBR

/-- Actual pure original codimension-one geometry internally gives a nonempty ORIGINAL open whose EVERY finite separable actual centre yields the SAME actual finite generically etale projection. No scalar purity, perfectness, transversality, flatness, or etaleness certificate is supplied. -/
theorem exists_original_genericallyEtale_parameter_open
    (hpure : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n) :
    ∃ O : (projectiveSpace k (n + 1)).Opens, (O : Set (projectiveSpace k (n + 1))).Nonempty ∧
      (O : Set (projectiveSpace k (n + 1))) ⊆ (Set.range i)ᶜ ∧
      ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
        (p : Spec (.of L) ⟶ projectiveSpace L (n + 1))
        (hp : p ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _),
        projectiveCoefficientMap (algebraMap k L) (n + 1) (pointImage L n p) ∈ O →
        ∃ hout : pointImage L n p ∉ Set.range (scalarClosedInclusion k L (algebraMap k L) n i),
          let f := projectionFromPoint L n p hp (scalarClosedInclusion k L (algebraMap k L) n i) hout
          IsFinite f ∧ f ≫ projectiveSpaceStructure L n =
            scalarClosedInclusion k L (algebraMap k L) n i ≫ projectiveSpaceStructure L (n + 1) ∧
          IsGenericallyEtale f := by
  obtain ⟨O, hO, houtO, hgood⟩ :=
    exists_original_genericallyEtale_parameter_open_over_separableClosure k n i U hU hpure
  refine ⟨O, hO, houtO, ?_⟩
  intro L _ _ _ _ p hp hpO
  let hout := scalarCenter_outside_of_original_image k L n i p (houtO hpO)
  obtain ⟨_, _, _, hGE⟩ := hgood (separableClosureCenter k L n p hp)
    (separableClosureCenter_structure k L n p hp)
    (separableClosureCenter_mem_original_open k L n p hp O hpO)
  refine ⟨hout, projectionFromPoint_isFinite L n p hp _ hout,
    projectionFromPoint_structure L n p hp _ hout, ?_⟩
  exact projectionFromPoint_genericallyEtale_of_separableClosure k L n i p hp hout hGE

end Hironaka.Geometry.ProjectiveSecant
