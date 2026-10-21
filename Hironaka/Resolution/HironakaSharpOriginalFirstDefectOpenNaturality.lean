/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalRestrictedDistinctDefectCentre
import Hironaka.Invariant.ResolutionInvariantSegments
/-! Genuine FIRST-Z open naturality in arbitrary carrier dimension.
The original quotient is preserved, never replaced by incidence count. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalFirstDefectOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpOriginalRestrictedDistinctDefectCentre HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalAllBoundaryCentre HironakaSharpOriginalDeepProductBlowup
  RelativePrincipalizationSpan RestrictedIdealExtension MarkedIdealRestrictOpen
  GermIdealOrder DivisorExponentAlong NormalCrossings NormalCrossingsInvariance
  MarkedIdealBiholomorphism NonmonomialOrderLocal ResolutionInvariantDriver ResolutionDriver
  ResolutionInvariantSegments CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

private theorem traceSpan_comp_val_iff (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (U : Opens X) (x : U) (i : Fin E.length)
    (g : X → ℂ) (hg : HolomorphicAt n g x.val) :
    traceSpan (n := n) ((Subtype.val : U → X) ⁻¹' W)
      ((E.map ((Subtype.val : U → X) ⁻¹' ·)).get (Fin.cast (List.length_map _).symm i))
      x (g ∘ Subtype.val) ↔ traceSpan (n := n) W (E.get i) x.val g := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hU := (holomorphicAt_comp_val_iff U).mpr hg
  have hExt := (holomorphicAt_iff_extendOpens U).mp hU
  have heq : extendOpens U (g ∘ Subtype.val)=ᶠ[𝓝 x.val] g :=
    (eventually_nhds_val_iff U).mpr (Eventually.of_forall fun y => by simp)
  have hdict := restrictOn_pullback_val_iff U (W := W) (x := x) (F := g ∘ Subtype.val) hI
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal] at hdict
  change (HolomorphicAt n (g ∘ Subtype.val) x ∧
    traceSpan (n := n) ((Subtype.val : U → X) ⁻¹' W)
      ((Subtype.val : U → X) ⁻¹' E.get i) x (g ∘ Subtype.val)) ↔
    (HolomorphicAt n (extendOpens U (g ∘ Subtype.val)) x.val ∧
      traceSpan (n := n) W (E.get i) x.val (extendOpens U (g ∘ Subtype.val))) at hdict
  have hSpan : traceSpan (n := n) ((Subtype.val : U → X) ⁻¹' W)
      ((Subtype.val : U → X) ⁻¹' E.get i) x (g ∘ Subtype.val) ↔
      traceSpan (n := n) W (E.get i) x.val g := by
    constructor
    · intro h
      exact IsInSpanOnAt.congr_right (hdict.mp ⟨hU,h⟩).2 (heq.mono fun _ hy _ => hy.symm)
    · intro h
      exact (hdict.mpr ⟨hExt,IsInSpanOnAt.congr_right h (heq.mono fun _ hy _ => hy)⟩).2
  simpa [get_map_preimage] using hSpan

/-- BOTH directions for the SAME entire original trace germ relation. -/
theorem original_traceGerm_rel_open_iff (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (U : Opens X) (x : U) (i j : Fin E.length) :
    (traceGermSetoid (n := n) ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) x).r
        (Fin.cast (List.length_map _).symm i) (Fin.cast (List.length_map _).symm j) ↔
      (traceGermSetoid (n := n) W E x.val).r i j := by
  refine ⟨?_,original_traceGerm_rel_preimage_val hn hE U i j⟩
  intro h g hg
  have hh := h (g ∘ Subtype.val) ((holomorphicAt_comp_val_iff U).mpr hg)
  exact (traceSpan_comp_val_iff hn hE U x i g hg).symm.trans
    (hh.trans (traceSpan_comp_val_iff hn hE U x j g hg))

/-- A genuine quotient equivalence preserves the finite image of proper classes. -/
theorem original_distinct_count_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (U : Opens X) (x : U) (hx : x.val∈W) :
    distinctProperTraceGermCount (n := n) ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) x=
        distinctProperTraceGermCount (n := n) W E x.val := by
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let eFin : Fin E.length ≃ Fin EU.length := finCongr (List.length_map _).symm
  have hRel : ∀ i j,(traceGermSetoid (n := n) W E x.val).r i j ↔
      (traceGermSetoid (n := n) WU EU x).r (eFin i) (eFin j) :=
    fun i j => (original_traceGerm_rel_open_iff hn hE U x i j).symm
  let eQ := Quotient.congr eFin hRel
  have hEU : IsSNCDivisor n EU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hProper (i : Fin E.length) : i∈properTraceMembers (n := n) W E x.val ↔
      eFin i∈properTraceMembers (n := n) WU EU x := by
    rw [properTraceMembers_eq_incident hE.1 hx,properTraceMembers_eq_incident (X := CMfd.of (n := n) U) hEU.1 hx]
    simp [eFin,EU]
  have hImage : (properTraceMembers (n := n) WU EU x).image
      (Quotient.mk (traceGermSetoid (n := n) WU EU x))=
      ((properTraceMembers (n := n) W E x.val).image
        (Quotient.mk (traceGermSetoid (n := n) W E x.val))).image eQ := by
    ext q
    constructor
    · intro hq
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
      let i := eFin.symm j
      have he : eFin i=j := eFin.apply_symm_apply j
      refine Finset.mem_image.mpr ⟨Quotient.mk _ i,
        Finset.mem_image.mpr ⟨i,(hProper i).mpr (he ▸ hj),rfl⟩,?_⟩
      exact (Quotient.congr_mk eFin hRel i).trans (congrArg (Quotient.mk _) he)
    · intro hq
      obtain ⟨q₀,hq₀,hqe⟩ := Finset.mem_image.mp hq
      obtain ⟨i,hi,hie⟩ := Finset.mem_image.mp hq₀
      refine Finset.mem_image.mpr ⟨eFin i,(hProper i).mp hi,?_⟩
      exact (Quotient.congr_mk eFin hRel i).symm.trans ((congrArg eQ hie).trans hqe)
  unfold distinctProperTraceGermCount
  change ((properTraceMembers (n := n) WU EU x).image _).card=_
  rw [hImage,Finset.card_image_of_injective _ eQ.injective]

/-- Genuine original product order, with no carrier-dimension-one shortcut. -/
theorem original_product_order_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (U : Opens X) (x : U) :
    ordinaryTraceOrder (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
      (originalMemberProduct (M := U) (n := n) (E.map ((Subtype.val : U → X) ⁻¹' ·))) x=
        ordinaryTraceOrder W (originalMemberProduct (n := n) E) x.val := by
  have hw : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have h := nmOrd_pullback_val hn hw
    (fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy) U x
  rw [pullback_val_originalMemberProductMarked hn W hE 1 U] at h
  simpa only [nmOrd_originalMemberProductMarked] using h

/-- The literal entire FIRST-Z commutes with actual open restriction in ALL dimensions. -/
theorem original_first_defect_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (U : Opens X) :
    originalDistinctDefectPhase (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))=
        (Subtype.val : U → X) ⁻¹' originalDistinctDefectPhase W E := by
  ext x
  by_cases hx : x.val∈W
  · change (x.val∈W ∧ _ < _) ↔ (x.val∈W ∧ _ < _)
    rw [original_product_order_open hn hW hE hdense U x,original_distinct_count_open hn hE U x hx]
  · exact ⟨fun h => (hx h.1).elim,fun h => (hx h.1).elim⟩

private theorem product_domain (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1≤n) (hreg : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) : IsInvDomain (n+1) (originalMemberProductMarked W E 1) := by
  have h := originalMemberProductMarked_isInvDomain hn hW hE hd hreg hdense le_rfl
  exact ⟨h.isWellFormed,fun x hx => by
    obtain ⟨j,hj,hjreg⟩ := h.dimLE x hx
    exact ⟨j,hj.trans (Nat.le_succ n),hjreg⟩,h.one_le_d,h.isNonzeroAlongAt⟩

private theorem first_value_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1≤n) (hreg : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (U : Opens X) (x : U)
    (hx : x.val∈originalDistinctDefectPhase W E) :
    (invFamily hn (n+1)).inv (originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) .refl x=
      (invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl x.val := by
  have hcos : x.val∈(originalMemberProductMarked W E 1).cosupp :=
    (ordinaryTraceOrder_cosupport_iff hW (isCoherent_originalMemberProduct hn hE)
      (fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy) hx.1 1).mpr (by
        have hlt : distinctProperTraceGermCount (n := n) W E x.val <
            ordinaryTraceOrder W (originalMemberProduct (n := n) E) x.val := hx.2
        omega)
  have h := (invFamily hn (n+1)).isInvValue.restrictOpen _
    (product_domain hn hW hE hd hreg hdense) U .refl trivial x hcos
  rwa [pullback_val_originalMemberProductMarked hn W hE 1 U] at h

/-- A TRUE meeting of the original maximum, not arbitrary local-max equality. -/
theorem original_first_maximum_open_of_meeting (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1≤n) (hreg : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (U : Opens X)
    (hne : ((Subtype.val : U → X) ⁻¹' maxLocus
      ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
      (originalDistinctDefectPhase W E)).Nonempty) :
    maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) .refl)
      (originalDistinctDefectPhase (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)))=
        (Subtype.val : U → X) ⁻¹' maxLocus
          ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
          (originalDistinctDefectPhase W E) := by
  rw [original_first_defect_open hn hW hE hdense U]
  exact maxLocus_preimage _ (fun x hx => first_value_open hn hW hE hd hreg hdense U x hx) hne

/-- Missing the actual original maximum gives EMPTY trace and STRICTLY smaller values. -/
theorem original_first_value_lt_of_maximum_trace_empty (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1≤n) (hreg : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (U : Opens X) {a : X}
    (ha : a∈maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
      (originalDistinctDefectPhase W E))
    (hempty : (Subtype.val : U → X) ⁻¹' maxLocus
      ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
      (originalDistinctDefectPhase W E)=∅) (x : U)
    (hx : x∈originalDistinctDefectPhase (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))) :
    (invFamily hn (n+1)).inv (originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) .refl x<
      (invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl a := by
  rw [original_first_defect_open hn hW hE hdense U] at hx
  rw [first_value_open hn hW hE hd hreg hdense U x hx]
  apply lt_of_le_of_ne (ha.2 x.val hx)
  intro heq
  have hmax : x.val∈maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
      (originalDistinctDefectPhase W E) :=
    ⟨hx,fun y hy => (ha.2 y hy).trans_eq heq.symm⟩
  have : x∈(Subtype.val : U → X) ⁻¹' maxLocus
      ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) .refl)
      (originalDistinctDefectPhase W E) := hmax
  rw [hempty] at this
  exact this
end
end Hironaka.HironakaSharpOriginalFirstDefectOpenNaturality
