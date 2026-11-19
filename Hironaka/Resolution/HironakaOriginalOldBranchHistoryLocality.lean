import Hironaka.Invariant.DropMembers
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Blowup.BlowupTowerSplit

set_option autoImplicit false

/-!
# Locality of original old-branch test histories

The universal initial-branch predicate, reflection from an open covering the
whole cosupport, and exact prefix history use only existing low-level geometry.
Reflection fixes the actual ambient tower and needs no compact branch chart.
The prescribed ambient extension consumer is in
`HironakaOriginalOldBranchOpenHistory`; the strengthened finite-prephase
producer itself remains an unformalized blueprint theorem.

Blueprint: `hironaka-original-old-branch-open-history-extension.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalOldBranchOpenHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings DropMembers
  GermIdealPullbackCalculus HomogenizedGlueingTower

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

private theorem hasNormalCrossings_image_val {A : CMfd.{u} n}
    {U : Opens A} {C : Set U} {E : List (Set A)}
    (hC : HasNormalCrossings n C (E.map ((Subtype.val : U → A) ⁻¹' ·))) :
    HasNormalCrossings n ((Subtype.val : U → A) '' C) E := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨S₀, S, hcoord, hcard⟩ := hC c hc
  let k : Fin E.length → Fin (E.map ((Subtype.val : U → A) ⁻¹' ·)).length :=
    Fin.cast (List.length_map _).symm
  refine ⟨S₀, fun i => S (k i), ?_, ?_⟩
  · apply NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff.mp
    refine NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hcoord (Option.map k) ?_ ?_
    · rintro (_ | i)
      · exact Subtype.val_injective.preimage_image C
      · simp [k]
    · rintro (_ | i) <;> rfl
  · intro i hi
    apply hcard (k i)
    simpa [NormalCrossingsInvariance.get_map_preimage, k] using hi

/-- The complete literal original-old block precedes the entire retained and born boundary.
The identity holds along every geometric tower, without testness or removed empty slots. -/
theorem entire_original_old_retained_boundary (M : MarkedIdeal n X) (B : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong ({ M with E := B ++ M.E } : MarkedIdeal n X) T).E =
        B.map (strictAlong T) ++ (geoTransformAlong M T).E
  | _, .refl => by
    change B ++ M.E = B.map (fun A => A) ++ M.E
    exact congrArg (fun L : List (Set X) => L ++ M.E) (List.map_id B).symm
  | _, .step T C π hπ => by
    rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E,
      entire_original_old_retained_boundary M B T, List.map_append, List.map_map, List.append_assoc]
    rfl

/-- Every original joint SNC branch presentation tests the same restricted tower.
The universal quantification permits later phases to retain the literal strict
transforms of the original branches, including all empty historical entries. -/
def IsOriginalBranchTestTower (M : MarkedIdeal n X) (H : Set X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  ∀ (U : Opens X) (B : List (Set U)),
    IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E) →
    (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
    IsGeoTestTower
      ({ MarkedIdeal.pullback (Subtype.val : U → X) M with
        E := B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E } : MarkedIdeal n U)
      (restrict U T)

/-- Boundary-test histories reflect from an initial open containing the entire cosupport.
The ambient tower is fixed, and no compactness of the branch chart is needed. -/
theorem isGeoTestTower_of_restrict_cosupport_cover (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (E' : List (Set X)) (U : Opens X) (hU : M.cosupp ⊆ U) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X)
        ({ M with E := E' } : MarkedIdeal n X)) (restrict U T) →
      IsGeoTestTower ({ M with E := E' } : MarkedIdeal n X) T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hT, hTU => by
    have hAugT := isGeoTestTower_of_restrict_cosupport_cover M hN hI E' U hU T hT.1 hTU.1
    have hLocal := hTU.2
    rw [geoTransformAlong_restrict (𝔪 := ({ M with E := E' } : MarkedIdeal n X))
      U hN hI T hAugT] at hLocal
    let V := openPreimage T U
    have hInside : C ⊆ (V : Set _) := by
      intro x hx
      exact hU (TransformOffCentre.cosupp_geoTransformAlong_subset M hN hI T hT.1
        (hT.2.2.1 hx))
    have hImage : (Subtype.val : V → _) '' ((Subtype.val : V → _) ⁻¹' C) = C := by
      rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hInside]
    have hNC := hasNormalCrossings_image_val hLocal.2.2
    rw [hImage] at hNC
    refine ⟨hAugT, hT.2.1, ?_, hNC⟩
    rw [cosupp_geoTransformAlong_withE M E' T]
    exact hT.2.2.1

/-- Every original joint branch presentation has actual testness and well-formedness
at every prefix, with the literal original-old block followed by the entire retained/born block. -/
theorem original_branch_prefix_histories (M : MarkedIdeal n X) (hN : M.N = univ)
    (hI : M.ideal.IsCoherent) {H : Set X} {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hHistory : IsOriginalBranchTestTower M H T) (U : Opens X) (B : List (Set U))
    (hSNC : IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E))
    (hUnion : (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A)) :
    let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
    let MB : MarkedIdeal n U := { MU with E := B ++ MU.E }
    ∀ j : ℕ, IsGeoTestTower MB (head (restrict U T) j) ∧
      (geoTransformAlong MB (head (restrict U T) j)).IsWellFormed ∧
      (geoTransformAlong MB (head (restrict U T) j)).E =
        B.map (strictAlong (head (restrict U T) j)) ++
          (geoTransformAlong MU (head (restrict U T) j)).E := by
  dsimp only
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let MB : MarkedIdeal n U := { MU with E := B ++ MU.E }
  have hTest : IsGeoTestTower MB (restrict U T) := hHistory U B hSNC hUnion
  have hWF : MB.IsWellFormed := by
    refine ⟨?_, isCoherent_pullback contMDiff_subtype_val hI, hSNC, ?_⟩
    · change IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' M.N)
      rw [hN, preimage_univ]
      exact HomogenizedGlueingTower.isClosedSubmanifold_univ
    · change IsTransverse n ((Subtype.val : U → X) ⁻¹' M.N) (B ++ MU.E)
      rw [hN, preimage_univ]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  intro j
  have hHead := ((isGeoTestTower_iff_head_tail MB (restrict U T) j).mp hTest).1
  exact ⟨hHead, MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF _ hHead,
    entire_original_old_retained_boundary MU B (head (restrict U T) j)⟩

end

end Hironaka.HironakaOriginalOldBranchOpenHistory
