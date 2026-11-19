import Hironaka.Resolution.HironakaG8ClosedNativeTestGlobalization
import Hironaka.Resolution.HironakaSharpActualCurveOriginalGrowingHistory
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixLocalHistories

/-! Rank and closed-support obligations in serializing finite local histories. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8StageRankCoherence

/-- A chain of dependencies of the indicated length ending at a stage. -/
inductive DependencyPath {ι : Type*} (before : ι → ι → Prop) : ℕ → ι → Prop
  | nil (i : ι) : DependencyPath before 0 i
  | step {a b : ι} {k : ℕ} (h : before a b) (p : DependencyPath before k a) :
      DependencyPath before (k+1) b

/-- A common serial rank exists exactly when each stage has a finite bound
on the lengths of its preceding dependency paths. Independent stages can
share a rank. -/
theorem exists_natural_rank_iff {ι : Type*} (before : ι → ι → Prop) :
    (∃ r : ι → ℕ, ∀ ⦃a b⦄, before a b → r a < r b) ↔
      ∀ i, ∃ k, ∀ l, DependencyPath before l i → l ≤ k := by
  constructor
  · rintro ⟨r,hr⟩ i
    refine ⟨r i,fun l p => ?_⟩
    induction p with
    | nil i => exact Nat.zero_le _
    | step h p ih => exact Nat.succ_le_of_lt (ih.trans_lt (hr h))
  · intro h
    classical
    let r (i : ι) := Nat.find (h i)
    refine ⟨r, ?_⟩
    intro a b hab
    have hBound : ∀ l, DependencyPath before l a → l ≤ r b - 1 := by
      intro l p
      have := Nat.find_spec (h b) (l+1) (.step hab p)
      change l+1 ≤ r b at this
      omega
    have hle : r a ≤ r b - 1 := Nat.find_min' (h a) hBound
    have hpos : 0 < r b := Nat.find_spec (h b) 1 (.step hab (.nil a))
    omega

/-- The pairwise dependency test can be locally finite and acyclic without
a natural serial rank. The windows can see just a two-element link, with
any overlap of successive links seeing the same singleton. -/
theorem no_natural_rank_for_reverse_links :
    ¬ ∃ r : ℕ → ℕ, ∀ k, r (k+1) < r k := by
  rintro ⟨r,hr⟩
  have hPred : ∀ k, r k + k ≤ r 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k =>
      have h := hr k
      omega
  have := hPred (r 0 + 1)
  omega

/-- Relative closedness and equality of full traces on an open cover
are sufficient to glue globally closed support. In particular no compactness
or separate closedness of a chart's ambient image is needed. -/
theorem exists_closed_support_of_open_compatible_traces
    {X ι : Type*} [TopologicalSpace X] (U : ι → Opens X) (F : ι → Set X)
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hSub : ∀ i, F i ⊆ U i)
    (hClosed : ∀ i, IsClosed ((Subtype.val : U i → X) ⁻¹' F i))
    (hAgree : ∀ i j, F i ∩ (U j : Set X) = F j ∩ (U i : Set X)) :
    ∃ S : Set X, IsClosed S ∧ ∀ i, S ∩ (U i : Set X) = F i := by
  let S := ⋃ i, F i
  have hTrace (i : ι) : S ∩ (U i : Set X) = F i := by
    ext x
    constructor
    · rintro ⟨hxS,hxi⟩
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hxS
      have hh : x ∈ F j ∩ (U i : Set X) := ⟨hxj,hxi⟩
      rw [hAgree j i] at hh
      exact hh.1
    · exact fun hx => ⟨mem_iUnion.mpr ⟨i,hx⟩,hSub i hx⟩
  refine ⟨S, ?_, hTrace⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i,hi⟩ := hCover x
  let C : Set (U i) := (Subtype.val ⁻¹' F i)ᶜ
  refine ⟨Subtype.val '' C, ?_, (U i).isOpen.isOpenMap_subtype_val _ (hClosed i).isOpen_compl,
    ⟨⟨x,hi⟩, ?_, rfl⟩⟩
  · rintro _ ⟨z,hz,rfl⟩ hS
    exact hz (by rw [← hTrace i]; exact ⟨hS,z.property⟩)
  · exact fun h => hx (mem_iUnion.mpr ⟨i,h⟩)

/-- A rank-indexed family of compatible actual traces gives closed
global supports and local finiteness from finitely many active ranks per window. -/
theorem exists_locally_finite_closed_stage_supports
    {X ι κ : Type*} [TopologicalSpace X] (U : ι → Opens X) (F : κ → ι → Set X)
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hSub : ∀ k i, F k i ⊆ U i)
    (hClosed : ∀ k i, IsClosed ((Subtype.val : U i → X) ⁻¹' F k i))
    (hAgree : ∀ k i j, F k i ∩ (U j : Set X) = F k j ∩ (U i : Set X))
    (hFinite : ∀ i, {k | (F k i).Nonempty}.Finite) :
    ∃ S : κ → Set X, (∀ k, IsClosed (S k)) ∧ LocallyFinite S ∧
      ∀ k i, S k ∩ (U i : Set X) = F k i := by
  choose S hS hTrace using fun k =>
    exists_closed_support_of_open_compatible_traces U (F k) hCover (hSub k) (hClosed k) (hAgree k)
  refine ⟨S,hS,?_,hTrace⟩
  intro x
  obtain ⟨i,hi⟩ := hCover x
  refine ⟨U i,(U i).isOpen.mem_nhds hi,(hFinite i).subset ?_⟩
  intro k hk
  change (F k i).Nonempty
  rw [← hTrace k i]
  exact hk

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8ClosedNativeTestGlobalization HironakaG3EmptyAwareHistory

/-- The full projected centre footprint of an actual finite tower is closed. -/
theorem isClosed_baseCentreFootprint {n : ℕ} {X Y : CMfd.{0} (n+1)}
    (T : BlowupTower X Y) : IsClosed (baseCentreFootprint T) := by
  induction T with
  | refl => exact isClosed_empty
  | step T C π hπ ih =>
    exact ih.union ((HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ hπ.1.1)

/-- Restriction to a literal open retains precisely the trace of the
original footprint, including when it erases centre occurrences. -/
theorem baseCentreFootprint_restrict {n : ℕ} {X Y : CMfd.{0} (n+1)}
    (O : Opens X) (T : BlowupTower X Y) :
    baseCentreFootprint (restrict O T) = (Subtype.val : O → X) ⁻¹' baseCentreFootprint T := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    change baseCentreFootprint (restrict O T) ∪
      (restrict O T).proj '' ((Subtype.val : openPreimage T O → _) ⁻¹' C) =
      (Subtype.val : O → X) ⁻¹' (baseCentreFootprint T ∪ T.proj '' C)
    rw [preimage_union, ih]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.val,hy,(proj_restrict O T y).symm⟩
    · rintro ⟨y,hy,he⟩
      have hyO : y ∈ openPreimage T O := by
        change T.proj y ∈ O
        rw [he]
        exact x.property
      refine ⟨⟨y,hyO⟩,hy,Subtype.ext ?_⟩
      rw [proj_restrict]
      exact he

/-- Empty-aware comparisons preserve the exact union of projected centres,
even when their literal rank numbers differ across the comparison. -/
theorem baseCentreFootprint_emptyAware
    {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} (n+1)}
    {φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ Y₂}
    (h : EmptyAwareTowerIso φ T₁ T₂ ψ) :
    baseCentreFootprint T₁ = φ ⁻¹' baseCentreFootprint T₂ := by
  induction h with
  | refl => exact preimage_empty.symm
  | @step A B C D R S θ h K π hπ L ρ hρ χ hχ hEq ih =>
    rw [baseCentreFootprint,baseCentreFootprint,preimage_union,ih]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨θ y,?_,(emptyAware_proj_comm h y)⟩
      change y ∈ θ ⁻¹' L
      rwa [hEq]
    · rintro ⟨y,hy,he⟩
      refine ⟨θ.symm y,?_,φ.injective ?_⟩
      · rw [← hEq]
        change θ (θ.symm y) ∈ L
        rwa [θ.apply_symm_apply]
      · change φ (R.proj (θ.symm y)) = φ x
        rw [← emptyAware_proj_comm h, θ.apply_symm_apply]
        exact he
  | leftEmpty h hρ χ hχ ih =>
    rw [baseCentreFootprint, image_empty, union_empty, ih]
  | rightEmpty h hρ χ hχ ih =>
    rw [baseCentreFootprint, image_empty, union_empty, ih]

open HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal

/-- The total (unranked) footprint of a physically compatible chart cover
is a single closed subset of the original ambient manifold. -/
theorem exists_closed_total_footprint_of_physical_charts
    {n : ℕ} {X Z : CMfd.{0} (n+1)} {κ : Type*} {K : LocalTowerClass X} {P : Z → X}
    (cmp : HasPhysicalComparisons K) (c : κ → TowerChart K Z P)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) :
    ∃ F : Set X, IsClosed F ∧
      ∀ i, F ∩ ((c i).U : Set X) = (Subtype.val : (c i).U → X) '' baseCentreFootprint (c i).T := by
  let U (i : κ) := (c i).U
  let A (i : κ) := (Subtype.val : (c i).U → X) '' baseCentreFootprint (c i).T
  have hSub (i : κ) : A i ⊆ U i := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hClosed (i : κ) : IsClosed ((Subtype.val : U i → X) ⁻¹' A i) := by
    change IsClosed ((Subtype.val : U i → X) ⁻¹'
      ((Subtype.val : U i → X) '' baseCentreFootprint (c i).T))
    rw [preimage_image_eq _ Subtype.val_injective]
    exact isClosed_baseCentreFootprint (c i).T
  have hDirection (i j : κ) : A i ∩ (U j : Set X) ⊆ A j ∩ (U i : Set X) := by
    obtain ⟨β,hβ⟩ := cmp (c i).U (c j).U _ _ (c i).T (c j).T (c i).mem (c j).mem
    let O := U i ⊓ U j
    let Oi := nestedOpens (U i) O
    let Oj := nestedOpens (U j) O
    let α := overlapBaseEquiv (n := n+1) (show O ≤ U i from inf_le_left) (show O ≤ U j from inf_le_right)
    have hEq := baseCentreFootprint_emptyAware hβ
    rw [baseCentreFootprint_restrict, baseCentreFootprint_restrict] at hEq
    rintro _ ⟨⟨x,hx,rfl⟩,hj⟩
    let a : Oi := ⟨x,⟨x.property,hj⟩⟩
    have ha : a ∈ (Subtype.val : Oi → U i) ⁻¹' baseCentreFootprint (c i).T := hx
    rw [hEq] at ha
    change (α a).val ∈ baseCentreFootprint (c j).T at ha
    refine ⟨⟨(α a).val,ha,?_⟩,x.property⟩
    exact overlapBaseEquiv_point (show O ≤ U i from inf_le_left) (show O ≤ U j from inf_le_right) a
  exact exists_closed_support_of_open_compatible_traces U A hCover hSub hClosed
    (fun i j => Subset.antisymm (hDirection i j) (hDirection j i))

open HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGlobalPrefixTowers
  HironakaSharpActualCurveOriginalGrowingHistory HironakaSharpActualCurveLocalStationaryCentres
  HironakaSharpActualCurveGlobalSuccessorCentre HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveGluedProjection HironakaLocallyFiniteResolutionSequence
  HironakaSharpActualCurveGlobalPrefixLocalHistories HironakaSharpActualCurveGlobalPrefixTests
  HironakaSharpActualCurveUniformPrefixes MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealTowerTransport
  Hironaka.HolomorphicIdealSheaves HomogenizedGlueingTower GermIdealPullbackCalculus
  BlowupTowerIsomorphism BlowupRestrictOpen HironakaSharpActualCurveEmptyPadding
  BlowupTowerSplit ResolutionInvariantExt

/-- Rank-synchronized actual finite histories already have a physical
global sequence with locally finite actual centre images. -/
theorem uniform_growing_seq_locally_finite
    {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (A : ActualEndpointHistories X ι) (hc : ∀ x : X, ∃ i, x ∈ A.openSet i) :
    LocallyFinite (centreImage (uniformGrowingSeq A hc)) := by
  intro x
  obtain ⟨i,hi⟩ := hc x
  let L := ((A.prefixTower i).append (A.tail i)).length
  refine ⟨A.openSet i,(A.openSet i).isOpen.mem_nhds hi,(Set.finite_Iio L).subset ?_⟩
  intro k hk
  change k < L
  by_contra hn
  obtain ⟨z,hz,hzU⟩ := hk
  rw [centreImage_uniformGrowingSeq A hc k] at hz
  obtain ⟨y,hy,rfl⟩ := hz
  exact disjoint_left.mp (globalUniformCentre_disjoint_preimage_open A k i (le_of_not_gt hn))
    hy hzU

/-- The glued global sequence tests the same record whenever each literal
rank-synchronized full local tower tests its actual pullback. -/
theorem uniform_growing_seq_original_test
    {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (A : ActualEndpointHistories X ι) (hc : ∀ x : X, ∃ i, x ∈ A.openSet i)
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hLocal : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : A.openSet i → X) M)
      ((A.prefixTower i).append (A.tail i))) :
    ∀ k, IsGeoTestTower M ((uniformGrowingSeq A hc).stage k).2 := by
  intro k
  cases k with
  | zero => trivial
  | succ k =>
    change IsGeoTestTower M (uniformOriginalPositiveTower A hc k)
    apply isGeoTestTower_of_open_cover M hN hI A.openSet hc
    intro i
    let Mi := MarkedIdeal.pullback (Subtype.val : A.openSet i → X) M
    have hNi := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN (A.openSet i)
    have hMi : Mi.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
    have hIso := localOriginalPrefix_isTowerIso A hc k i
    have hId : MarkedIdeal.pullback
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (A.openSet i)) ∞) Mi = Mi :=
      ContactCanonicalAlong.pullback_id Mi hMi
    have hTests := IsTowerIso.isGeoTestTower_iff (𝔪 := Mi) _ hNi hMi hIso
    rw [hId] at hTests
    apply hTests.mp
    let T := (A.prefixTower i).append (A.tail i)
    let E := identityEmptyTail (A.finalSpace i) (k+1)
    have hPadded : IsGeoTestTower Mi (T.append E) :=
      (isGeoTestTower_append_iff (𝔪 := Mi) T E).mpr ⟨hLocal i,
        isGeoTestTower_of_isEmptyTower _ E (identityEmptyTail_isEmptyTower _ _)⟩
    exact ((isGeoTestTower_iff_head_tail Mi (T.append E) T.length).mp hPadded).1

end Hironaka.HironakaG8StageRankCoherence
