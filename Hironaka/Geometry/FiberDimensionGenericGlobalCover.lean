import Hironaka.Geometry.FiberDimensionGenericFinite
import Hironaka.Geometry.RationalCoordinateMapGenericFiberDimension
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Actual source-open fiber covers and finite maxima of fiber dimension

The source cover is pulled back along the literal scheme-theoretic fiber
inclusion. Native Cartesian comparisons identify its charts with actual
composite fibers. Their finite maximum computes the original fiber dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionGenericGlobalCover

open FiberDimension FiberDimensionGenericFinite

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- An actual source-open fiber-cover chart is the actual fiber of the original composite. -/
def fiberCoverChartIso (f : X ⟶ Y) (𝒰 : X.OpenCover.{v}) (s : Y) (i : 𝒰.I₀) :
    (𝒰.pullback₁ (f.fiberι s)).X i ≅ (𝒰.f i ≫ f).fiber s :=
  (fiberProjection_isPullback (𝒰.f i) f s).isoPullback.symm

/-- The native pullback cover computes the actual composite fiber dimensions. -/
theorem fiberCoverChart_dimension (f : X ⟶ Y) (𝒰 : X.OpenCover.{v}) (s : Y) (i : 𝒰.I₀) :
    topologicalKrullDim ((𝒰.pullback₁ (f.fiberι s)).X i) =
      fiberDimension (𝒰.f i ≫ f) s :=
  IsHomeomorph.topologicalKrullDim_eq _ (fiberCoverChartIso f 𝒰 s i).hom.homeomorph.isHomeomorph

/-- Dimensions of finitely many actual source-open fibers compute the full actual fiber dimension. -/
theorem fiberDimension_eq_finset_sup_of_openCover (f : X ⟶ Y)
    (𝒰 : X.OpenCover.{v}) [Fintype 𝒰.I₀] [Nonempty 𝒰.I₀]
    (s : Y) (n : 𝒰.I₀ → ℕ) (hdim : ∀ i, fiberDimension (𝒰.f i ≫ f) s = n i) :
    fiberDimension f s = (Finset.univ.sup n : ℕ) := by
  let 𝒱 := 𝒰.pullback₁ (f.fiberι s)
  apply le_antisymm
  · apply FunctionFieldDimension.topologicalKrullDim_le_of_openCover _ (Finset.univ.sup n) 𝒱
    intro i
    change 𝒰.I₀ at i
    rw [fiberCoverChart_dimension f 𝒰 s i, hdim i]
    exact_mod_cast (Finset.le_sup (f := n) (Finset.mem_univ i))
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty n
    have hle := (𝒱.f i).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    rw [fiberCoverChart_dimension f 𝒰 s i, hdim i, ← heq] at hle
    exact hle

end Hironaka.Geometry.FiberDimensionGenericGlobalCover
