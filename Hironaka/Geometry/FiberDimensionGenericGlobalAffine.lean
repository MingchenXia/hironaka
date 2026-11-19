import Hironaka.Geometry.FiberDimensionGenericGlobalCover
import Hironaka.Geometry.FiberDimensionGenericAffine

/-!
# Actual generic constancy over an affine integral base

The native finite affine source cover is chosen internally. Each selected
chart contains its original indexing point and is therefore nonempty,
integral and dominant. Actual affine relative normalization on these charts
and their literal source-open fiber cover compute a finite constant dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionGenericGlobalAffine

open FiberDimension FiberDimensionGenericGlobalCover

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- An actual dominant finite-type map over an affine integral base has constant actual
fiber dimension on an internally constructed nonempty dense base open. -/
theorem exists_nonempty_dense_constant_fiberDimension
    [IsIntegral X] [IsIntegral Y] [IsAffine Y] [CompactSpace X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    ∃ U : Y.Opens, Nonempty U ∧ Dense (U : Set Y) ∧ ∃ n : ℕ,
      ∀ s : U, fiberDimension f s.val = n := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  have hne (i : 𝒰.I₀) : Nonempty (𝒰.X i) := by
    change Nonempty (X.affineCover.X (X.affineCover.idx i.val))
    obtain ⟨x, hx⟩ := X.affineCover.covers i.val
    exact ⟨x⟩
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    dsimp [𝒰, Scheme.OpenCover.finiteSubcover]
    infer_instance
  have (i : 𝒰.I₀) : IsIntegral (𝒰.X i) := by
    let := hne i
    exact isIntegral_of_isOpenImmersion (𝒰.f i)
  have (i : 𝒰.I₀) : IsDominant (𝒰.f i) := by
    constructor
    exact (IsOpenImmersion.isOpen_range (𝒰.f i)).dense
      ⟨𝒰.f i (Classical.choice (hne i)), ⟨_, rfl⟩⟩
  have hlocal (i : 𝒰.I₀) : ∃ U : Y.Opens, Nonempty U ∧ ∃ n : ℕ,
      ∀ s : U, fiberDimension (𝒰.f i ≫ f) s.val = n := by
    obtain ⟨U, hU, hdense, n, hfull, hrestricted⟩ :=
      FiberDimensionGenericAffine.exists_nonempty_dense_constant_fiberDimension (𝒰.f i ≫ f)
    exact ⟨U, hU, n, hfull⟩
  choose U hU n hdim using hlocal
  let V : Y.Opens := ⨅ i, U i
  have hη : genericPoint Y ∈ V := by
    change genericPoint Y ∈ ((⨅ i, U i : Y.Opens) : Set Y)
    rw [Opens.coe_iInf, Set.mem_iInter]
    intro i
    exact ((genericPoint_spec Y).mem_open_set_iff (U i).isOpen).mpr (by simpa using hU i)
  refine ⟨V, ⟨⟨genericPoint Y, hη⟩⟩, V.isOpen.dense ⟨genericPoint Y, hη⟩,
    Finset.univ.sup n, ?_⟩
  intro s
  apply fiberDimension_eq_finset_sup_of_openCover f 𝒰 s.val n
  intro i
  exact hdim i ⟨s.val, (iInf_le U i) s.property⟩

end Hironaka.Geometry.FiberDimensionGenericGlobalAffine
