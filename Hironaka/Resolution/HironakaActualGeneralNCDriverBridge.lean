import Hironaka.Invariant.DropMembers
import Hironaka.Resolution.HironakaCanonicalPrincipalization

set_option autoImplicit false

/-!
# An actual SNC tail with the retained original marked datum

Deleting initial boundary members preserves a geometric test tower in one
direction, without a containment or disjointness condition on those members.
The submanifold, controlled ideal, marking and cosupport remain unchanged.
The entire ordered list of born boundary members is literally the same.

For a coherent original ideal, positive marking and compact cosupport, an
augmented SNC boundary internally produces a canonical resolving tail. The
same actual tower resolves the retained-boundary datum. Both resolutions
are retained in the conclusion; canonicality concerns the augmented datum.

This is a consumer for the SNC end of a general NC prephase. It does not
produce the all-prefix original old-branch histories through that prephase
or identify a canonical general-NC driver.

Blueprint: `hironaka-actual-general-nc-driver-bridge-extension.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualGeneralNCDriverBridge

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison DropMembers DivisorExponentAlong
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (IsCanonicalSegment)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- Deleting initial boundary slots preserves their order at every stage of the same tower. -/
theorem boundary_sublist_geoTransformAlong (M : MarkedIdeal n X) (E' : List (Set X))
    (hsub : E'.Sublist M.E) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (geoTransformAlong ({ M with E := E' } : MarkedIdeal n X) T).E.Sublist
        (geoTransformAlong M T).E
  | _, .refl => hsub
  | _, .step T C π _hπ =>
    sublist_transformE π C (boundary_sublist_geoTransformAlong M E' hsub T)

/-- The boundary members of a smaller initial boundary remain available along the same tower. -/
theorem boundary_members_geoTransformAlong (M : MarkedIdeal n X) (E' : List (Set X))
    (hsub : ∀ H ∈ E', H ∈ M.E) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      ∀ H ∈ (geoTransformAlong ({ M with E := E' } : MarkedIdeal n X) T).E,
        H ∈ (geoTransformAlong M T).E
  | _, .refl => hsub
  | _, .step T C π _hπ =>
    forall_mem_transformE π C (boundary_members_geoTransformAlong M E' hsub T)

/-- Replacing only the initial boundary changes no born slot, repetition or birth order. -/
theorem born_boundary_geoTransformAlong_withE (M : MarkedIdeal n X) (E' : List (Set X)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (geoTransformAlong ({ M with E := E' } : MarkedIdeal n X) T).E.drop E'.length =
        (geoTransformAlong M T).E.drop M.E.length
  | _, .refl => by
    change E'.drop E'.length = M.E.drop M.E.length
    rw [List.drop_length, List.drop_length]
  | _, .step T C π hπ => by
    have hsmall : E'.length ≤
        ((geoTransformAlong ({ M with E := E' } : MarkedIdeal n X) T).E.map
          (geoStrictTransform π C)).length := by
      rw [List.length_map, length_E_geoTransformAlong]
      exact Nat.le_add_right E'.length T.length
    have hlarge : M.E.length ≤
        ((geoTransformAlong M T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, length_E_geoTransformAlong]
      exact Nat.le_add_right M.E.length T.length
    simp only [geoTransformAlong_step, geoTransform_E]
    rw [List.drop_append_of_le_length hsmall, List.drop_append_of_le_length hlarge]
    simp only [← List.map_drop, born_boundary_geoTransformAlong_withE M E' T]

/-- Forgetting initial boundary members preserves every centre's admissibility on the same tower.
No disjointness or containment condition on the deleted members is needed in this direction. -/
theorem isGeoTestTower_forget_boundary (M : MarkedIdeal n X) (E' : List (Set X))
    (hsub : ∀ H ∈ E', H ∈ M.E) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
      IsGeoTestTower ({ M with E := E' } : MarkedIdeal n X) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    refine ⟨isGeoTestTower_forget_boundary M E' hsub T hT.1,
      (isAdmissibleCentre_geoTransformAlong_withE_iff M E' T C).mpr ?_⟩
    exact ⟨hT.2.1, hT.2.2.1,
      hasNormalCrossings_of_forall_mem hT.2.2.2
        (boundary_members_geoTransformAlong M E' hsub T)⟩

/-- Forgetting initial boundary members preserves resolution of the same controlled ideal and mark. -/
theorem isGeoResolution_forget_boundary (M : MarkedIdeal n X) (E' : List (Set X))
    (hsub : ∀ H ∈ E', H ∈ M.E) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoResolution M T) :
    IsGeoResolution ({ M with E := E' } : MarkedIdeal n X) T :=
  ⟨isGeoTestTower_forget_boundary M E' hsub T hT.1,
    (cosupp_geoTransformAlong_withE M E' T).trans hT.2⟩

/-- Original ideal data internally produce one actual resolving canonical SNC tail for the
augmented boundary. The same tower resolves the retained boundary, with exactly the same born
boundary history. Canonicality is asserted only for the augmented SNC datum. -/
theorem exists_original_snc_tail_with_retained_boundary (I : GermIdeal n X)
    (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hne : ∀ x, IsNonzeroAlongAt univ I x)
    (hK : IsCompact (GermIdealOrder.cosupport n univ I d))
    (E F : List (Set X)) (hEF : IsSNCDivisor n (E ++ F)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution (⟨univ, E, I, d⟩ : MarkedIdeal n X) T ∧
      IsGeoResolution (⟨univ, E ++ F, I, d⟩ : MarkedIdeal n X) T ∧
      IsCanonicalSegment (⟨univ, E ++ F, I, d⟩ : MarkedIdeal n X)
        ((CanonicalCentres.canonicalInvariant n).inv
          (⟨univ, E ++ F, I, d⟩ : MarkedIdeal n X)) T ∧
      (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).E.drop E.length =
        (geoTransformAlong (⟨univ, E ++ F, I, d⟩ : MarkedIdeal n X) T).E.drop
          (E ++ F).length := by
  let P : MarkedIdeal n X := ⟨univ, E ++ F, I, d⟩
  have hdom : IsInvDomain n P := by
    refine ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hI, hEF,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hEF⟩, ?_, hd, ?_⟩
    · intro x _
      exact ⟨n, le_rfl, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
    · intro x _
      exact hne x
  obtain ⟨Y, T, hseg, hres⟩ :=
    HironakaCanonicalPrincipalization.exists_canonical_segment_of_isCompact
      (CanonicalCentres.canonicalInvariant.{u} n) hdom hK
  refine ⟨Y, T, ?_, hres, hseg, ?_⟩
  · exact isGeoResolution_forget_boundary P E (fun H hH => List.mem_append_left F hH) T hres
  · exact born_boundary_geoTransformAlong_withE P E T

end

end Hironaka.HironakaActualGeneralNCDriverBridge
