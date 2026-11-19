import Hironaka.Resolution.HironakaSharpActualEmptyChronologicalDefect
import Hironaka.Resolution.HironakaSharpActualOriginalDynamicStep
import Hironaka.Resolution.HironakaSharpOriginalRestrictedDistinctDefectCentre
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-! Genuine finite dynamic FIRST-Z histories from only original compact-pure
geometry. Every original ideal position and every actual empty default is kept.
No full modified-invariant decrease, termination or fair scheduling is asserted.
The full mathematics precedes this source in
`hironaka-sharp-original-dynamic-good-prefixes-extension.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalDynamicGoodPrefixes
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupRestrictOpen
  HironakaSharpActualEmptyChronologicalDefect HironakaSharpActualFamilyDefectOpenNaturality
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualOriginalDynamicStep
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualDynamicDistinctCentre
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalRestrictedDistinctDefectCentre
  HironakaCoherentTransformExtension RelativePrincipalizationSpan RestrictedIdealExtension
  NormalCrossings NormalCrossingsInvariance MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder DivisorExponentAlong NonmonomialOrderLocal IdealWeightPowers
  RestrictEmptyTower CanonicalCentres ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem initial_actual_relation_iff (W : Set X) (E : List (Set X))
    (x : X) (i j : Fin E.length) :
    (actualIdealGermSetoid (fun a : Fin E.length =>
      (originalRelativeMemberMarked W (E.get a)).ideal) x).r i j ↔
      (traceGermSetoid (n := n) W E x).r i j := by
  constructor
  · intro h g hg
    have hh := h g
    change (HolomorphicAt n g x ∧ traceSpan (n := n) W (E.get i) x g) ↔
      (HolomorphicAt n g x ∧ traceSpan (n := n) W (E.get j) x g) at hh
    exact ⟨fun hi => (hh.mp ⟨hg,hi⟩).2,fun hj => (hh.mpr ⟨hg,hj⟩).2⟩
  · intro h g
    change (HolomorphicAt n g x ∧ traceSpan (n := n) W (E.get i) x g) ↔
      (HolomorphicAt n g x ∧ traceSpan (n := n) W (E.get j) x g)
    exact ⟨fun hi => ⟨hi.1,(h g hi.1).mp hi.2⟩,
      fun hj => ⟨hj.1,(h g hj.1).mpr hj.2⟩⟩

private theorem initial_actual_distinct_count_eq (W : Set X) (E : List (Set X))
    (x : X) :
    actualDistinctProperCount (fun a : Fin E.length =>
      (originalRelativeMemberMarked W (E.get a)).ideal) x=
        distinctProperTraceGermCount (n := n) W E x := by
  let F := fun a : Fin E.length => (originalRelativeMemberMarked W (E.get a)).ideal
  have hRel : ∀ i j,(traceGermSetoid (n := n) W E x).r i j ↔
      (actualIdealGermSetoid F x).r i j :=
    fun i j => (initial_actual_relation_iff W E x i j).symm
  let eQ := Quotient.congr (Equiv.refl (Fin E.length)) hRel
  have hProper : actualProperPositions F x=properTraceMembers (n := n) W E x := by
    ext i
    simp only [actualProperPositions,properTraceMembers,Finset.mem_filter,
      Finset.mem_univ,true_and]
    change (¬(HolomorphicAt n (1 : X → ℂ) x ∧
      traceSpan (n := n) W (E.get i) x (1 : X → ℂ))) ↔ _
    constructor
    · intro h hs
      exact h ⟨holomorphicAt_const 1,hs⟩
    · intro h hs
      exact h hs.2
  have hmk : Quotient.mk (actualIdealGermSetoid F x)=
      eQ ∘ Quotient.mk (traceGermSetoid (n := n) W E x) := by
    funext i
    exact (Quotient.congr_mk (Equiv.refl (Fin E.length)) hRel i).symm
  change ((actualProperPositions F x).image (Quotient.mk (actualIdealGermSetoid F x))).card=_
  rw [hProper,hmk,←Finset.image_image,Finset.card_image_of_injective _ eQ.injective]
  rfl

/-- The actual identity-stage indexed quotient defect is the literal original FIRST defect. -/
theorem chronologicalDistinctDefect_refl (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W⊆closure (W \ ⋃ H∈E,H)) :
    chronologicalDistinctDefect W E (.refl : BlowupTower X X)=originalDistinctDefectPhase W E := by
  ext x
  let F := fun i : Fin E.length => (originalRelativeMemberMarked W (E.get i)).ideal
  have he := (original_product_nmOrd_eq_current hn hW hE hdense 1
    (.refl : BlowupTower X X) trivial x).trans
    (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense
      (.refl : BlowupTower X X) trivial x)
  have hp := chronological_product_eq_actual_family_product W E (.refl : BlowupTower X X)
  change chronologicalMemberProduct W E (.refl : BlowupTower X X)=
    relativeIdealListProduct W (List.ofFn F) at hp
  have hord : ordinaryTraceOrder W (originalMemberProduct (n := n) E) x=
      ordinaryTraceOrder W (relativeIdealListProduct W (List.ofFn F)) x := by
    rw [←hp]
    exact he
  change (x∈W ∧ actualDistinctProperCount F x<
    ordinaryTraceOrder W (relativeIdealListProduct W (List.ofFn F)) x) ↔
      (x∈W ∧ distinctProperTraceGermCount (n := n) W E x<
        ordinaryTraceOrder W (originalMemberProduct (n := n) E) x)
  rw [initial_actual_distinct_count_eq,hord]

/-- Centre support is used as an induction invariant here; the final producer
below creates it internally from the original data. -/
theorem chronologicalDistinctDefect_subset_originalBad_of_centresOver (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    (hOver : CentresOver (originalSharpBadLocus (n := n) W E) T) :
    chronologicalDistinctDefect W E T⊆T.proj ⁻¹' originalSharpBadLocus (n := n) W E := by
  let U : Opens X := ⟨originalGoodLocus (n := n) W E,isOpen_originalGoodLocus hW.1 hE.1⟩
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  have hWU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hDenseU : WU⊆closure (WU \ ⋃ H∈EU,H) := by
    intro y hy
    have hp : y∈(Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H∈E,H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H∈E,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp [WU,EU]
  have hDisj : Disjoint (U : Set X) (originalSharpBadLocus (n := n) W E) := by
    rw [originalSharpBadLocus_eq_compl_good]
    exact disjoint_compl_right
  have hEmpty := isEmptyTower_restrict_of_centresOver U hDisj T hOver
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template _ hwM T hT
  have hOpen := chronologicalDistinctDefect_open hn hW hE hdense T hGeom U
  have hLocal := chronologicalDistinctDefect_empty hn hWU hEU hDenseU (restrict U T) hEmpty
  have hInitialOpen := chronologicalDistinctDefect_open hn hW hE hdense
    (.refl : BlowupTower X X) trivial U
  change chronologicalDistinctDefect (X := CMfd.of (n := n) U) WU EU
    (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))=
      (Subtype.val : U → X) ⁻¹' chronologicalDistinctDefect W E (.refl : BlowupTower X X) at hInitialOpen
  have hInitialEmpty : chronologicalDistinctDefect (X := CMfd.of (n := n) U) WU EU
      (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))=∅ := by
    rw [hInitialOpen,chronologicalDistinctDefect_refl hn hW hE hdense]
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact disjoint_left.mp (originalDistinctDefectPhase_disjoint_good hn hW hE hdense) hy y.property
  rw [hInitialEmpty,preimage_empty] at hLocal
  intro y hy
  rw [originalSharpBadLocus_eq_compl_good]
  intro hyGood
  let z : openPreimage T U := ⟨y,hyGood⟩
  have hz : z∈chronologicalDistinctDefect (X := CMfd.of (n := n) U) WU EU (restrict U T) := by
    rw [hOpen]
    exact hy
  rw [hLocal] at hz
  exact hz

/-- The actual FIRST rule resets the current whole product invariant at its
actual current stage; no historical full-value equality is asserted. -/
def IsDynamicFirstPrefix (hn : 0<n) (W : Set X) (E : List (Set X)) :
    {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _,.refl => True
  | _,.step T C _ _ => IsDynamicFirstPrefix hn W E T ∧
      if chronologicalDistinctDefect W E T=∅ then C=∅ else
        C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T)
          (.refl : BlowupTower _ _)) (chronologicalDistinctDefect W E T)

/-- Every actual head inherits the same genuine dynamic rule. -/
theorem isDynamicFirstPrefix_head (hn : 0<n) (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsDynamicFirstPrefix hn W E T →
      ∀ j,IsDynamicFirstPrefix hn W E (head T j)
  | _,.refl,_,0 => trivial
  | _,.refl,_,_+1 => trivial
  | _,.step _T _C _π _hπ,h,0 => h
  | _,.step T _C _π _hπ,h,j+1 => isDynamicFirstPrefix_head hn W E T h.1 j

/-- A genuine supported tower is an isomorphism over the entire complement. -/
theorem isIsomorphismOver_proj_of_centresOver (B : Set X) (T : BlowupTower X Y)
    (hOver : CentresOver B T) : IsIsomorphismOver n T.proj Bᶜ := by
  have hSupp := HironakaEmbeddedBoundary.support_exceptionalDivisor_subset_of_centresOver B T hOver
  have hExc := HironakaPrincipalization.exceptionalLocus_subset_support T
  have hImage : T.proj '' exceptionalLocus n T.proj⊆B := by
    rintro x ⟨y,hy,rfl⟩
    exact hSupp (hExc hy)
  exact HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    T.isBlowupSequence hImage

/-- ONLY original compact-pure geometry produces an actual FIRST-Z tower of
every finite length, all centre supports, and whole-good isomorphisms at every head. -/
theorem exists_original_dynamic_first_prefix (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (hK : IsCompact W) {d : ℕ} (hd : d+1≤n)
    (hr : ∀ x∈W,RegularAtDim (n := n) W x (d+1)) (a : ℕ) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),T.length=a ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) T ∧
      IsDynamicFirstPrefix hn W E T ∧ CentresOver (originalSharpBadLocus (n := n) W E) T ∧
      IsIsomorphismOver n T.proj (originalGoodLocus (n := n) W E) ∧
      ∀ j,IsGeoTestTower (originalMemberProductMarked W E 1) (head T j) ∧
        IsDynamicFirstPrefix hn W E (head T j) ∧
        CentresOver (originalSharpBadLocus (n := n) W E) (head T j) ∧
        IsIsomorphismOver n (head T j).proj (originalGoodLocus (n := n) W E) := by
  have hCore : ∀ a : ℕ,∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),T.length=a ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) T ∧
      IsDynamicFirstPrefix hn W E T ∧ CentresOver (originalSharpBadLocus (n := n) W E) T := by
    intro k
    induction k with
    | zero => exact ⟨X,.refl,rfl,trivial,trivial,trivial⟩
    | succ k ih =>
      obtain ⟨Y,T,hLen,hTest,hRule,hOver⟩ := ih
      by_cases hZ : chronologicalDistinctDefect W E T=∅
      · let hπ := BlowupExistenceCodimOne.isBlowupAlong_id_empty (n := n) (X := Y)
        refine ⟨Y,.step T ∅ id hπ,?_,⟨hTest,isAdmissibleCentre_empty _⟩,?_,?_⟩
        · simp only [BlowupTower.length_step,hLen]
        · exact ⟨hRule,by simp only [hZ,ite_true]⟩
        · exact ⟨hOver,empty_subset _⟩
      · have hne : (chronologicalDistinctDefect W E T).Nonempty := Set.nonempty_iff_ne_empty.mpr hZ
        obtain ⟨C,_hneC,hCZ,hAdm,_hLevel,hCeq⟩ :=
          exists_original_dynamic_distinct_centre hn hW hE hdense hK hd hr T hTest hne
        have hDom := originalMemberProductMarked_isInvDomain hn hW hE hd hr hdense le_rfl
        have hDomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom T hTest
        have hint : interior C=∅ := eq_empty_of_subset_empty
          ((interior_mono hAdm.2.1).trans
            (ResolutionInvariantDriver.interior_cosupp_eq_empty hDomT).subset)
        obtain ⟨Z,π,hπ⟩ := exists_blowup C hAdm.1 hint
        refine ⟨Z,.step T C π hπ,?_,⟨hTest,hAdm⟩,?_,?_⟩
        · simp only [BlowupTower.length_step,hLen]
        · exact ⟨hRule,by simpa only [hZ,ite_false] using hCeq⟩
        · exact ⟨hOver,hCZ.trans
            (chronologicalDistinctDefect_subset_originalBad_of_centresOver hn hW hE hdense T hTest hOver)⟩
  obtain ⟨Y,T,hLen,hTest,hRule,hOver⟩ := hCore a
  have hGood (Z : CMfd.{u} n) (S : BlowupTower X Z)
      (hS : CentresOver (originalSharpBadLocus (n := n) W E) S) :
      IsIsomorphismOver n S.proj (originalGoodLocus (n := n) W E) := by
    simpa only [originalSharpBadLocus_eq_compl_good,compl_compl] using
      isIsomorphismOver_proj_of_centresOver (originalSharpBadLocus (n := n) W E) S hS
  refine ⟨Y,T,hLen,hTest,hRule,hOver,hGood Y T hOver,?_⟩
  intro j
  have hHead := centresOver_head (originalSharpBadLocus (n := n) W E) T j hOver
  exact ⟨((isGeoTestTower_iff_head_tail _ T j).mp hTest).1,
    isDynamicFirstPrefix_head hn W E T hRule j,hHead,hGood _ _ hHead⟩

end
end Hironaka.HironakaSharpOriginalDynamicGoodPrefixes
