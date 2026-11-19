import Hironaka.Resolution.HironakaDisjointBlowupCommutation
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Resolution.HironakaStageCenters
import Hironaka.Resolution.HironakaEmbeddedAnalytic
import Hironaka.Resolution.HironakaSingularSubspaceBlowupLift

/-! Independent marked centres can be executed in either order. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointMarkedSwap

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaAdmissibleSequence HironakaAdmissibleCalculus HironakaDisjointBlowupCommutation
  HomogenizedGlueingTower HironakaLocalPrincipalization RestrictEmptyTower
  TransformOffCentre NormalCrossings MarkedIdealOperationsAlong.MarkedIdeal
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaSingularSubspaceBlowupLift
  NormalCrossingsInvariance MarkedIdealTowerTransport BlowupStrictSubmanifold

variable {n : ℕ} {X Y W Z Q : CMfd.{0} n}

/-- A centre disjoint from an admissible blowup remains admissible when
pulled to the transformed record, with the newly born boundary included. -/
theorem admissible_preimage_of_disjoint
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C D : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hC : M.IsAdmissibleCentre C) (hD : M.IsAdmissibleCentre D) (hCD : Disjoint C D)
    {q : Z → Y} (hq : IsBlowupAlong n (π ⁻¹' D) q) :
    (M.geoTransform C π).IsAdmissibleCentre (π ⁻¹' D) := by
  let T : BlowupTower X Y := .step .refl C π hπ
  have hT : IsGeoTestTower M T := (isGeoTestTower_step_iff M .refl C π hπ).mpr
    ⟨trivial,hC⟩
  have hOver : CentresOver C T := ⟨trivial,fun _ hx => hx⟩
  have hA := isAdmissibleBlowupSequence_proj M C T hT hOver
  refine ⟨hq.1,?_,?_⟩
  · intro x hx
    have hOut : π x ∉ C := fun hxC => disjoint_left.mp hCD hxC hx
    exact (mem_cosupp_geoTransform_iff M hM.isClosedSubmanifold_N.1
      (hol_of_isCoherent hM.isCoherent) hπ hOut).mpr (hD.2.1 hx)
  · exact HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint hA hM.isSNCDivisor.1 hπ.1.1 hCD.symm hD.2.2

/-- For disjoint centres admissible at the same stage, both genuine
ordered two-step towers test the original record. Their total
projections have the physical commutation biholomorphism. -/
theorem exists_disjoint_marked_swap
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C D : Set X} {π : Y → X} {ρ : W → X}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ)
    (hC : M.IsAdmissibleCentre C) (hD : M.IsAdmissibleCentre D) (hCD : Disjoint C D) :
    ∃ (Z Q : CMfd.{0} n) (q : Z → Y) (r : Q → W)
      (hq : IsBlowupAlong n (π ⁻¹' D) q) (hr : IsBlowupAlong n (ρ ⁻¹' C) r),
      IsGeoTestTower M (.step (.step .refl C π hπ) (π ⁻¹' D) q hq) ∧
      IsGeoTestTower M (.step (.step .refl D ρ hρ) (ρ ⁻¹' C) r hr) ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q,
        (ρ ∘ r) ∘ e = π ∘ q := by
  obtain ⟨Z,Q,q,r,hq,hr,e,he⟩ := exists_disjoint_double_blowups hπ hρ hCD
  refine ⟨Z,Q,q,r,hq,hr,?_,?_,e,he⟩
  · exact (isGeoTestTower_step_iff M _ _ _ hq).mpr
      ⟨(isGeoTestTower_step_iff M _ _ _ hπ).mpr ⟨trivial,hC⟩,
        admissible_preimage_of_disjoint M hM hπ hC hD hCD hq⟩
  · exact (isGeoTestTower_step_iff M _ _ _ hr).mpr
      ⟨(isGeoTestTower_step_iff M _ _ _ hρ).mpr ⟨trivial,hD⟩,
        admissible_preimage_of_disjoint M hM hρ hD hC hCD.symm hr⟩

/-- Singularity agrees with the original carrier along a disjoint second
centre. This also identifies original singularity from the tested lift. -/
theorem singularSet_at_disjoint_second_centre
    {C D A : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hA : IsClosed A) (hCD : Disjoint C D) {y : Y} (hy : y ∈ π ⁻¹' D) :
    y ∈ singularSet (n := n) (strictTransform n π A) ↔ π y ∈ singularSet (n := n) A := by
  have hexc : y ∉ exceptionalLocus n π := fun he =>
    disjoint_left.mp hCD (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ he) hy
  simp only [mem_singularSet_iff]
  rw [mem_strictTransform_iff_of_notMem hπ.contMDiff.continuous hA hexc]
  exact and_congr_right fun _ => forall_congr' fun d => not_congr
    (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus hπ.contMDiff hA hexc d)

private theorem normalCrossings_of_contained_open
    {D : Set X} {E : List (Set X)} (U : Opens X) (hDU : D ⊆ U)
    (h : HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' D)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))) : HasNormalCrossings n D E := by
  intro x hx
  obtain ⟨S₀,S,hCoord,hCard⟩ := h ⟨x,hDU hx⟩ hx
  let k : Fin E.length → Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length :=
    Fin.cast (List.length_map _).symm
  refine ⟨S₀,fun i => S (k i),?_,?_⟩
  · apply (isCoordinateFamilyAt_preimage_val_iff (x := (⟨x,hDU hx⟩ : U))).mp
    refine IsCoordinateFamilyAt.reindex hCoord (Option.map k) ?_ ?_
    · rintro (_ | i)
      · rfl
      · simp [k]
    · rintro (_ | i) <;> rfl
  · intro i hi
    apply hCard (k i)
    simpa [get_map_preimage,k] using hi

/-- Smoothness and closedness of a disjoint pulled-back centre descend
to the original base. -/
theorem closedSubmanifold_of_disjoint_preimage {C D : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hCD : Disjoint C D)
    (h : IsClosedSubmanifold n (π ⁻¹' D)) : IsClosedSubmanifold n D := by
  let U := centreComplement hπ
  let V := centreComplementPreimage hπ
  let e := offCentreBiholomorphism hπ
  have hIso : IsProperMap π := isProperMap_of_isBlowupAlong hπ
  have hs := surjective_of_isBlowupAlong hπ
  have hLoc := BlowupRestrictOpen.isClosedSubmanifold_preimage_val h V
  have hLoc' : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' D) :=
    (isClosedSubmanifold_preimage_iff e).mp hLoc
  refine ⟨?_,?_⟩
  · rw [← image_preimage_eq D hs]
    exact hIso.isClosedMap _ h.1
  · intro x hx
    have hxU : x ∈ U := fun hxC => disjoint_left.mp hCD hxC hx
    obtain ⟨k,hk⟩ := hLoc'.2 ⟨x,hxU⟩ hx
    exact ⟨k, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hk⟩

/-- An admissible lifted second centre disjoint from the first centre was
already admissible on the original stage. -/
theorem admissible_of_disjoint_preimage
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C D : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCD : Disjoint C D)
    (hLift : (M.geoTransform C π).IsAdmissibleCentre (π ⁻¹' D)) :
    M.IsAdmissibleCentre D := by
  let U := centreComplement hπ
  let V := centreComplementPreimage hπ
  let e := offCentreBiholomorphism hπ
  refine ⟨closedSubmanifold_of_disjoint_preimage hπ hCD hLift.1,?_,?_⟩
  · intro x hx
    obtain ⟨y,rfl⟩ := surjective_of_isBlowupAlong hπ x
    have hOut : π y ∉ C := fun hC => disjoint_left.mp hCD hC hx
    exact (mem_cosupp_geoTransform_iff M hM.isClosedSubmanifold_N.1
      (hol_of_isCoherent hM.isCoherent) hπ hOut).mp (hLift.2.1 hx)
  · apply normalCrossings_of_contained_open U (fun _ hx hC => disjoint_left.mp hCD hC hx)
    apply (hasNormalCrossings_preimage_iff e).mp
    have hLocal := hasNormalCrossings_preimage (pullsBackCoordinates_val V) hLift.2.2
    rw [geoTransform_E,List.map_append] at hLocal
    have hOld : HasNormalCrossings n ((Subtype.val : V → Y) ⁻¹' (π ⁻¹' D))
        ((M.E.map (geoStrictTransform π C)).map ((Subtype.val : V → Y) ⁻¹' ·)) :=
      NormalCrossingsComparison.hasNormalCrossings_of_forall_mem hLocal
        (fun _ hH => List.mem_append.mpr (Or.inl hH))
    have hSlots : (M.E.map (geoStrictTransform π C)).map ((Subtype.val : V → Y) ⁻¹' ·) =
        (M.E.map ((Subtype.val : U → X) ⁻¹' ·)).map (e ⁻¹' ·) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro H hH
      ext y
      exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
        (hM.isSNCDivisor.1 H hH) y.property
    rw [hSlots] at hOld
    exact hOld

/-- Commute an actual two-step singular-centred TEST when the second
base centre is disjoint from the first and has an original blowup.
The output is physically over the very same base projection. -/
theorem swap_actual_two_singular_steps
    (A : Set X) (hA : IsClosed A) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : W → X}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hCD : Disjoint C D)
    (hTest : IsGeoTestTower M (.step (.step .refl C π hπ) (π ⁻¹' D) q hq))
    (hCSing : C ⊆ singularSet (n := n) A)
    (hDSing : π ⁻¹' D ⊆ singularSet (n := n) (strictTransform n π A)) :
    ∃ (Q : CMfd.{0} n) (r : Q → W) (hr : IsBlowupAlong n (ρ ⁻¹' C) r),
      IsGeoTestTower M (.step (.step .refl D ρ hρ) (ρ ⁻¹' C) r hr) ∧
      D ⊆ singularSet (n := n) A ∧
      ρ ⁻¹' C ⊆ singularSet (n := n) (strictTransform n ρ A) ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q,
        (ρ ∘ r) ∘ e = π ∘ q := by
  obtain ⟨hFirst,hSecond⟩ := (isGeoTestTower_step_iff M _ _ _ hq).mp hTest
  have hD := admissible_of_disjoint_preimage M hM hπ hCD hSecond
  have hC := ((isGeoTestTower_step_iff M _ _ _ hπ).mp hFirst).2
  have hDa : D ⊆ singularSet (n := n) A := by
    intro x hx
    obtain ⟨y,rfl⟩ := surjective_of_isBlowupAlong hπ x
    exact (singularSet_at_disjoint_second_centre hπ hA hCD hx).mp (hDSing hx)
  obtain ⟨Z', Q', q', r, hq', hr, _, hSwapped, _⟩ := exists_disjoint_marked_swap M hM hπ hρ hC hD hCD
  refine ⟨Q',r,hr,hSwapped,hDa,?_,disjoint_double_blowup_comparison hπ hρ hCD hq hr⟩
  intro y hy
  exact (singularSet_at_disjoint_second_centre hρ hA hCD.symm hy).mpr (hCSing hy)

/-- A second physical centre whose base footprint misses the first
centre is the entire preimage of its own projected footprint. -/
theorem preimage_image_eq_of_disjoint_centre
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (D : Set Y) (hCD : Disjoint C (π '' D)) : π ⁻¹' (π '' D) = D := by
  let e := offCentreBiholomorphism hπ
  apply Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro y ⟨z,hz,he⟩
  have hzOut : π z ∉ C := fun hzC => disjoint_left.mp hCD hzC ⟨z,hz,rfl⟩
  have hyOut : π y ∉ C := he ▸ hzOut
  have hEq : e ⟨z,hzOut⟩ = e ⟨y,hyOut⟩ := Subtype.ext he
  have hzy : z = y := congrArg Subtype.val (e.injective hEq)
  rwa [← hzy]

/-- An actual pair of consecutive TEST/singular steps can be swapped
whenever their footprints on their common source are disjoint. The other
two literal blowups and their endpoint comparison are constructed. -/
theorem swap_actual_steps_of_disjoint_projected_footprints
    (A : Set X) (hA : IsClosed A) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C : Set X} {D : Set Y} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q)
    (hCD : Disjoint C (π '' D))
    (hTest : IsGeoTestTower M (.step (.step .refl C π hπ) D q hq))
    (hCSing : C ⊆ singularSet (n := n) A)
    (hDSing : D ⊆ singularSet (n := n) (strictTransform n π A)) :
    ∃ (B Q : CMfd.{0} n) (ρ : B → X) (r : Q → B)
      (hρ : IsBlowupAlong n (π '' D) ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r),
      IsGeoTestTower M (.step (.step .refl (π '' D) ρ hρ) (ρ ⁻¹' C) r hr) ∧
      π '' D ⊆ singularSet (n := n) A ∧
      ρ ⁻¹' C ⊆ singularSet (n := n) (strictTransform n ρ A) ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q,
        (ρ ∘ r) ∘ e = π ∘ q := by
  let F := π '' D
  have hF : π ⁻¹' F = D := preimage_image_eq_of_disjoint_centre hπ D hCD
  have hSmooth := closedSubmanifold_of_disjoint_preimage hπ hCD
    (show IsClosedSubmanifold n (π ⁻¹' F) by rw [hF]; exact hq.1)
  have hInterior : interior F = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y,rfl⟩ := surjective_of_isBlowupAlong hπ x
    have hOpen : IsOpen (π ⁻¹' interior F) := isOpen_interior.preimage hπ.contMDiff.continuous
    have hSub : π ⁻¹' interior F ⊆ D := (preimage_mono interior_subset).trans hF.subset
    have hy := (interior_maximal hSub hOpen) hx
    rw [hq.2.1] at hy
    exact hy
  obtain ⟨B,tB,cB,mB,ρ,hρ⟩ := BlowupExistence.exists_isBlowupAlong F hSmooth hInterior
  let : TopologicalSpace B := tB
  let : ChartedSpace (ComplexModel n) B := cB
  let : IsComplexManifold n B := mB
  let B₀ : CMfd.{0} n := ⟨B⟩
  have hq' : IsBlowupAlong n (π ⁻¹' F) q := hF.symm ▸ hq
  have hTest' : IsGeoTestTower M (.step (.step .refl C π hπ) (π ⁻¹' F) q hq') := by
    rw [isGeoTestTower_step_iff] at hTest ⊢
    rwa [hF]
  obtain ⟨Q,r,hr,hS⟩ := swap_actual_two_singular_steps (W := B₀)
    A hA M hM hπ hq' hρ hCD hTest' hCSing (by rwa [hF])
  exact ⟨B₀,Q,ρ,r,hρ,hr,hS⟩

end Hironaka.HironakaG8DisjointMarkedSwap
