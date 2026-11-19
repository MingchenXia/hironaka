import Hironaka.Resolution.HironakaOriginalOldBranchThroughPoint
import Hironaka.Resolution.HironakaNormalCrossingsSNCBlockCarrier
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation

set_option autoImplicit false

/-!
# A highest old-stratum phase tests every original local branch list

The through-point producer is applied to an arbitrary original joint SNC
presentation. Its finite through-index count is identified with the actual
intrinsic NC multiplicity. Actual centre containment in the highest stratum
then produces augmented testness for that SAME original branch list.
No local augmented test history or chart-matching certificate is assumed.

Blueprint: `hir:original-old-branch-highest-phase-universal-history`.
The pinned `HironakaNormalCrossingsSNCBlockCarrier` source has been added
without replacing existing sources; its actual import objects are required
before this module can receive a faithful kernel check.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalOldBranchOpenHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings
  HomogenizedGlueingTower BoundaryCount HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsMultiplicityStrata HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSNCBlockCarrier
  CoefficientIdealRestriction

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

private theorem branchMultiplicity_congr_of_eq {A : Type u} [TopologicalSpace A]
    [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A]
    {H K : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hK : IsNormalCrossingsCarrier (n := n) K) (hHK : H = K) (x : A) :
    branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

/-- The actual original highest-stratum condition produces the universal test property
for every original joint SNC branch presentation, on the SAME tower and original ideal. -/
theorem isOriginalBranchTestTower_of_centresIn_highest_stratum
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ} (_hr : 0 < r)
    (hbound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn
      {x : X | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} T) :
    IsOriginalBranchTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) H T := by
  classical
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x : X | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  intro W B hSNC hUnion
  let MU := MarkedIdeal.pullback (Subtype.val : W → X) M
  let EU := MU.E
  let SW := (Subtype.val : W → X) ⁻¹' Z
  let hBU := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_union_of_snc_append B EU hSNC)
  have hHW : IsNormalCrossingsCarrier (n := n) ((Subtype.val : W → X) ⁻¹' H) :=
    hUnion.symm ▸ hBU
  have hCount (x : W) : boundaryCount B x = branchMultiplicity hH x.val := by
    have hRaw := (branchMultiplicity_union_eq_count B EU hSNC x).1
    change branchMultiplicity hBU x = boundaryCount B x at hRaw
    calc
      boundaryCount B x = branchMultiplicity hBU x := hRaw.symm
      _ = branchMultiplicity hHW x := (branchMultiplicity_congr_of_eq hHW hBU hUnion x).symm
      _ = branchMultiplicity hH x.val := branchMultiplicity_open W hH hHW x
  have hBoundB : ∀ x : W, boundaryCount B x ≤ r := by
    intro x
    rw [hCount]
    exact hbound x.val
  have hClosedSW : IsClosed SW :=
    (isClosed_branchMultiplicity_superlevel hH r).preimage continuous_subtype_val
  have hScount : ∀ x ∈ SW, r ≤ boundaryCount B x := by
    intro x hx
    rw [hCount]
    exact hx
  have hWF : ({ MU with E := B ++ MU.E } : MarkedIdeal n W).IsWellFormed := by
    refine ⟨?_, GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,
      hSNC, ?_⟩
    · change IsClosedSubmanifold n ((Subtype.val : W → X) ⁻¹' (univ : Set X))
      rw [preimage_univ]
      exact isClosedSubmanifold_univ
    · change IsTransverse n ((Subtype.val : W → X) ⁻¹' (univ : Set X)) (B ++ MU.E)
      rw [preimage_univ]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  have hTW : IsGeoTestTower MU (restrict W T) :=
    isGeoTestTower_restrict (𝔪 := M) W isClosedSubmanifold_univ hI T hT
  have hTZW : CentresIn SW (restrict W T) := centresIn_restrict_original W T hTZ
  exact isGeoTestTower_add_snc_branches_of_centresIn_maxcount
    (X := CMfd.of (n := n) W) MU B hWF r hBoundB
    hClosedSW hScount (restrict W T) hTW hTZW

end

end Hironaka.HironakaOriginalOldBranchOpenHistory
