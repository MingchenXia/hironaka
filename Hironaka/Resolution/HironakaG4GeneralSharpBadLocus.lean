import Hironaka.Resolution.HironakaG4SharpBadLocusAnalytic

set_option autoImplicit false

/-!
# The entire sharp bad locus for a general closed smooth carrier

Actual smooth flattening windows supply the local dimension. The full literal
original sharp bad locus is analytic without a global purity or positive
ambient-dimension hypothesis. Zero-dimensional carriers have no bad points.
Blueprint: `hironaka-g4-general-sharp-bad-locus.tex`.
This is static geometry, with no sharp-driver termination claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4GeneralSharpBadLocus

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.RegularLocusDense BlowupTowers NormalCrossings NormalCrossingsInvariance
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4SharpBadLocusAnalytic BlowupFlatCoordinates AnalyticDimensionBasics
  AnalyticSubsetOpens BlowupRestrictOpen

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual smooth flattening itself supplies a genuinely pure open window. -/
theorem exists_actual_locally_pure_window {W : Set X} (hW : IsClosedSubmanifold n W)
    {x : X} (hxW : x ∈ W) :
    ∃ (U : Opens X) (q : ℕ), x ∈ U ∧
      ∀ y ∈ (Subtype.val : U → X) ⁻¹' W,
        RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' W) y q := by
  obtain ⟨q,hqn,_hx,Φ,_hsrc,_h0,hflat⟩ := hW.2 x hxW
  let U : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  refine ⟨U,q,mem_flatDomain_self Φ,?_⟩
  intro y hy
  exact regularAtDim_preimage_val_iff.mpr
    (regularAtDim_of_flattening_of_mem hqn Φ hflat hy y.property.1 y.property.2)

private theorem density_preimage_val {W : Set X} {E : List (Set X)}
    (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A)) (U : Opens X) :
    (Subtype.val : U → X) ⁻¹' W ⊆ closure
      ((Subtype.val : U → X) ⁻¹' W \ ⋃ A ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), A) := by
  have htotal : (Subtype.val : U → X) ⁻¹' (⋃ A ∈ E, A) =
      ⋃ A ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), A := by
    ext y
    constructor
    · intro hy
      obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨(Subtype.val : U → X) ⁻¹' A,
        List.mem_map.mpr ⟨A,hA,rfl⟩,hyA⟩
    · intro hy
      obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp hy
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
      exact mem_iUnion₂.mpr ⟨B,hB,hyA⟩
  intro y hy
  have hcl : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ A ∈ E, A) := hdense hy
  have he := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (W \ ⋃ A ∈ E, A)
  have hlocal := (Set.ext_iff.mp he y).mp hcl
  rw [preimage_sdiff] at hlocal
  change y ∈ closure ((Subtype.val : U → X) ⁻¹' W \ (Subtype.val : U → X) ⁻¹' (⋃ A ∈ E, A)) at hlocal
  rw [htotal] at hlocal
  exact hlocal

private theorem sharpBad_empty_of_ambient_zero {W : Set X} {E : List (Set X)}
    (hn : n = 0) (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    originalSharpBadLocus (n := n) W E = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hboundary := (originalSharpBadLocus_subset_boundary hW hx).2
  obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hboundary
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
  obtain ⟨S,_hcoord,hcard,_hinj⟩ := hE.2 x
  have h1 := hcard i hxH
  have hle := Finset.card_le_univ (s := S i)
  simp only [Fintype.card_fin] at hle
  omega

/-- The full literal original sharp bad locus is analytic for every closed smooth
carrier: no artificial global pure dimension and no positive ambient dimension. -/
theorem isComplexAnalyticSubset_originalSharpBadLocus
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A)) :
    IsComplexAnalyticSubset (n := n) (originalSharpBadLocus (n := n) W E) := by
  classical
  by_cases hn : 0 < n
  · apply isComplexAnalyticSubset_of_forall_opens
    intro x
    by_cases hxW : x ∈ W
    · obtain ⟨U,q,hxU,hReg⟩ := exists_actual_locally_pure_window hW hxW
      have hWU := isClosedSubmanifold_preimage_val hW U
      have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U)
        continuous_subtype_val hE
      have ha := HironakaG4SharpBadLocusAnalytic.isComplexAnalyticSubset_originalSharpBadLocus
        (X := CMfd.of (n := n) U) hn hWU hEU (density_preimage_val hdense U) q hReg
      have heq : originalSharpBadLocus (n := n) ((Subtype.val : U → X) ⁻¹' W)
          (E.map ((Subtype.val : U → X) ⁻¹' ·)) =
          (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E := by
        ext y
        exact and_congr Iff.rfl
          (not_congr HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff)
      exact ⟨U,hxU,heq ▸ ha⟩
    · let U : Opens X := ⟨Wᶜ,hW.1.isOpen_compl⟩
      refine ⟨U,hxW,?_⟩
      have heq : (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact y.property hy.1
      rw [heq]
      exact isComplexAnalyticSubset_empty
  · have hn0 : n = 0 := by omega
    rw [sharpBad_empty_of_ambient_zero hn0 hW hE]
    exact isComplexAnalyticSubset_empty

/-- Actual density off the whole boundary makes the entire literal sharp bad
locus thin in the actual smooth carrier, without SNC or purity assumptions. -/
theorem originalSharpBadLocus_thin
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A)) :
    ∀ O : Set X, IsOpen O → O ∩ W ⊆ originalSharpBadLocus (n := n) W E →
      O ∩ W = ∅ := by
  have hsub := originalSharpBadLocus_subset_boundary (E := E) hW
  intro O hO hOW
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxO,hxW⟩
  obtain ⟨y,hyO,hyW,hyE⟩ := mem_closure_iff.mp (hdense hxW) O hO hxO
  exact hyE (hsub (hOW ⟨hyO,hyW⟩)).2

/-- Actual zero-dimensional carriers have an empty literal bad locus, rather
than only a truncated natural-number dimension bound. -/
theorem originalSharpBadLocus_eq_empty_of_regular_zero
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A))
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x 0) :
    originalSharpBadLocus (n := n) W E = ∅ := by
  have hbad := isComplexAnalyticSubset_originalSharpBadLocus hW hE hdense
  have hsub := originalSharpBadLocus_subset_boundary (E := E) hW
  have hthin := originalSharpBadLocus_thin hW hdense
  have hdim : DimLE (n := n) W 0 := fun x k hx =>
    (RegularPointDimension.eq_of_regularAtDim hx (hreg x hx.2.1)).le
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y,_hy,k,hyk⟩ := exists_regularAtDim_mem_nhds hbad hx univ_mem
  have hlt := ThinDimensionDrop.lt_of_regularAtDim_of_thin
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW)
    (hsub.trans inter_subset_left) hthin hdim hyk
  omega

end

end Hironaka.HironakaG4GeneralSharpBadLocus
