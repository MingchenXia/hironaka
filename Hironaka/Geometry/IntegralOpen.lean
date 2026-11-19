import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.NoetherianSpace

/-!
# Integral open subsets of reduced Noetherian schemes

Every nonempty open of a reduced scheme with Noetherian underlying space contains a
nonempty integral open, which can moreover be chosen affine. The construction isolates
an open part of an actual irreducible component, using finiteness of the components.
-/

open AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.IntegralOpen

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A nonempty open in a Noetherian space contains a nonempty irreducible open. -/
theorem exists_nonempty_irreducible_open_le (T : Type u) [TopologicalSpace T]
    [NoetherianSpace T] (V : Opens T) (hV : Nonempty V) :
    ∃ W : Opens T, W ≤ V ∧ Nonempty W ∧ IrreducibleSpace W := by
  obtain ⟨⟨x, hx⟩⟩ := hV
  obtain ⟨O, hO, hOn, hOZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  have hWn : (O ∩ (V : Set T)).Nonempty := by
    obtain ⟨y, _, hy⟩ := isIrreducible_irreducibleComponent.isPreirreducible
      O V hO V.isOpen (hOn.mono fun y hy => ⟨hOZ hy, hy⟩)
      ⟨x, mem_irreducibleComponent, hx⟩
    exact ⟨y, hy⟩
  refine ⟨⟨O ∩ V, hO.inter V.isOpen⟩, Set.inter_subset_right, hWn.to_subtype, ?_⟩
  exact Subtype.irreducibleSpace ⟨hWn,
    isIrreducible_irreducibleComponent.isPreirreducible.open_subset
      (hO.inter V.isOpen) (Set.inter_subset_left.trans hOZ)⟩

/-- Every nonempty open of a reduced topologically Noetherian scheme contains an integral open. -/
theorem exists_nonempty_integral_open_le (Y : Scheme.{u}) [NoetherianSpace Y]
    [IsReduced Y] (V : Y.Opens) (hV : Nonempty V) :
    ∃ W : Y.Opens, W ≤ V ∧ Nonempty W ∧ IsIntegral W.toScheme := by
  obtain ⟨W, hWV, hWn, hWi⟩ := exists_nonempty_irreducible_open_le Y V hV
  let : IrreducibleSpace W := hWi
  exact ⟨W, hWV, hWn, isIntegral_of_irreducibleSpace_of_isReduced (show Y.Opens from W).toScheme⟩

/-- The integral open can be chosen affine, without strengthening topological Noetherianity. -/
theorem exists_nonempty_integral_affine_open_le (Y : Scheme.{u}) [NoetherianSpace Y]
    [IsReduced Y] (V : Y.Opens) (hV : Nonempty V) :
    ∃ W : Y.Opens, W ≤ V ∧ Nonempty W ∧ IsIntegral W.toScheme ∧ IsAffine W.toScheme := by
  obtain ⟨U, hUV, hUn, hUi⟩ := exists_nonempty_integral_open_le Y V hV
  obtain ⟨⟨x, hx⟩⟩ := hUn
  obtain ⟨W, hWa, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
  let : IsIntegral U.toScheme := hUi
  let : Nonempty W.toScheme := ⟨⟨x, hxW⟩⟩
  exact ⟨W, hWU.trans hUV, inferInstance,
    isIntegral_of_isOpenImmersion (Y.homOfLE (U := W) (V := U) hWU), hWa⟩

end Hironaka.Geometry.IntegralOpen
