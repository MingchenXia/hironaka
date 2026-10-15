/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstGoodTraceRestrictionNonzero

/-! Actual lower normalized open member ideals and their entire remaining
product/domain. The auxiliary boundary is EMPTY; no joint exceptional SNC. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstGoodLowerProduct
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFirstGoodTraceRestrictionNonzero HironakaSharpActualFirstGoodReducedTraces
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteMemberProduct
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers
  InvertibleIdealQuotient MonomialPartAlong MarkedIdealRestrictOpen
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem span_on_subcarrier {N S : Set Y} (hSN : S ⊆ N)
    {K : (Y → ℂ) → Prop} {x : Y} {g : Y → ℂ}
    (h : IsInSpanOnAt (n := n) N K x g) : IsInSpanOnAt (n := n) S K x g := by
  obtain ⟨m,s,a,hs,ha,hrel⟩ := h
  exact ⟨m,s,a,hs,ha,hrel.mono fun y hy hyS => hy (hSN hyS)⟩

/-- BOTH true normalized relative-generator directions survive a genuine
subcarrier and an actual open pullback, retaining the SAME generator. -/
theorem actual_subcarrier_open_relative_generator {N S : Set Y} (hSN : S ⊆ N)
    {I : GermIdeal n Y} (hI : I.IsCoherent) (O : Opens Y) (x : O)
    (f : Y → ℂ) (hf : HolomorphicAt n f (x : Y))
    (hgen : ∀ g,I.mem (x : Y) g ↔ HolomorphicAt n g (x : Y) ∧
      IsInSpanOnAt (n := n) N (·=f) (x : Y) g) :
    ∀ g,(restrictOn n ((Subtype.val : O → Y) ⁻¹' S)
      (GermIdeal.pullback (m := n) (Subtype.val : O → Y) I)).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) ((Subtype.val : O → Y) ⁻¹' S)
        (·=f ∘ Subtype.val) x g := by
  have hfI : I.mem (x : Y) f := (hgen f).mpr
    ⟨hf,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hgenS : ∀ a,(restrictOn n S I).mem (x : Y) a ↔
      HolomorphicAt n a (x : Y) ∧ IsInSpanOnAt (n := n) S (·=f) (x : Y) a := by
    intro a
    constructor
    · intro ha
      exact ⟨ha.1,IsInSpanOnAt.trans (fun b hb => span_on_subcarrier hSN ((hgen b).mp hb).2) ha.2⟩
    · rintro ⟨ha,hspan⟩
      exact ⟨ha,IsInSpanOnAt.mono (S := (·=f)) (fun b hb => hb ▸ hfI) hspan⟩
  intro g
  rw [restrictOn_pullback_val_iff O hI,hgenS]
  constructor
  · rintro ⟨hg,hspan⟩
    obtain ⟨c,hc,hrel⟩ := isInSpanOnAt_eq_iff.mp hspan
    refine ⟨(holomorphicAt_iff_extendOpens O).mpr hg,
      isInSpanOnAt_eq_iff.mpr ⟨c ∘ Subtype.val,(holomorphicAt_comp_val_iff O).mpr hc,?_⟩⟩
    have hh := (eventually_nhds_val_iff O).mp hrel
    filter_upwards [hh] with y hy hyS
    simpa only [extendOpens_val,Function.comp_apply] using hy hyS
  · rintro ⟨hg,hspan⟩
    obtain ⟨c,hc,hrel⟩ := isInSpanOnAt_eq_iff.mp hspan
    refine ⟨(holomorphicAt_iff_extendOpens O).mp hg,
      isInSpanOnAt_eq_iff.mpr ⟨extendOpens O c,(holomorphicAt_iff_extendOpens O).mp hc,?_⟩⟩
    apply (eventually_nhds_val_iff O).mpr
    filter_upwards [hrel] with y hy hyS
    simpa only [extendOpens_val,Function.comp_apply] using hy hyS

/-- The literal normalized open pullback on the SAME actual lower trace. -/
def actualLowerTraceMember (W : Set X) (E : List (Set X)) (i j : Fin E.length)
    (T : BlowupTower X Y) (O : Opens Y) : GermIdeal n O :=
  restrictOn n ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T)
    (GermIdeal.pullback (m := n) (Subtype.val : O → Y)
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal)

/-- ONLY original geometry supplies EACH real remaining lower normalized
member's coherence/nonzero/BOTH relative-generator directions on computed good. -/
theorem exists_original_first_good_lower_members (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      ∀ i : Fin E.length,
        IsClosedSubmanifold n ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T) ∧
        ∀ j : Fin E.length,j ≠ i →
          (actualLowerTraceMember W E i j T O).IsCoherent ∧
          (∀ x ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T,
            IsNonzeroAlongAt ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T)
              (actualLowerTraceMember W E i j T O) x) ∧
          ∀ x ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T,
            ∃ f : O → ℂ,HolomorphicAt n f x ∧ ∀ g,(actualLowerTraceMember W E i j T O).mem x g ↔
              HolomorphicAt n g x ∧ IsInSpanOnAt (n := n)
                ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T) (·=f) x g := by
  obtain ⟨O,hO,hTraces⟩ := exists_actual_first_good_open_reduced_traces hn hW hE hdense d hr T hT
  refine ⟨O,hO,?_⟩
  intro i
  have hS := (hTraces i).1
  refine ⟨hS,?_⟩
  intro j hji
  obtain ⟨hNj,_hEj,_hmj,hwj,hnzj,hprj⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  have hI := hwj.isCoherent
  have hop := GermIdealPullbackCalculus.isCoherent_pullback (f := (Subtype.val : O → Y)) contMDiff_subtype_val hI
  have hLow := isCoherent_restrictOn hop (VanishingIdealCoherent.isCoherent_vanishingIdeal hS)
  refine ⟨hLow,?_,?_⟩
  · intro x hx
    have hxGood : (x : Y) ∉ chronologicalDistinctDefect W E T := by
      change (x : Y) ∈ (chronologicalDistinctDefect W E T)ᶜ
      rw [←hO]
      exact x.property
    have hnz := original_first_good_other_member_nonzero hn hW hE hdense T hT i j hji.symm hx hxGood
    obtain ⟨g,hg,hfreq⟩ := hnz
    refine ⟨g ∘ Subtype.val,le_restrictOn hop x _ (comp_val_mem_pullback_val O hI hg),?_⟩
    rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x] at hfreq
    exact Filter.frequently_map.mp hfreq
  · intro x hx
    rw [hNj] at hprj
    obtain ⟨f,hf,hgen⟩ := hprj x hx.1
    exact ⟨f ∘ Subtype.val,(holomorphicAt_comp_val_iff O).mpr hf,
      actual_subcarrier_open_relative_generator (fun y hy => hy.1) hI O x f hf hgen⟩

/-- TRUE ordered product of ALL other actual positions, including unit factors. -/
def actualRemainingLowerProduct (W : Set X) (E : List (Set X)) (i : Fin E.length)
    (T : BlowupTower X Y) (O : Opens Y) : GermIdeal n O :=
  relativeIdealListProduct (X := CMfd.of O) ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T)
    (((List.finRange E.length).filter (fun j => j ≠ i)).map fun j => actualLowerTraceMember W E i j T O)

/-- The SAME actual remaining lower product geometry/order sum is built BEFORE
its real EMPTY-boundary mark-one invariant-domain input. -/
theorem exists_original_first_good_lower_product_domain (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      ∀ i : Fin E.length,
        let S := (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T
        let L := ((List.finRange E.length).filter (fun j => j ≠ i)).map fun j => actualLowerTraceMember W E i j T O
        let P := actualRemainingLowerProduct W E i T O
        P.IsCoherent ∧ (∀ x ∈ S,IsNonzeroAlongAt S P x) ∧
        (∀ x ∈ S,∃ f : O → ℂ,HolomorphicAt n f x ∧ ∀ g,P.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) S (·=f) x g) ∧
        (∀ x ∈ S,ordinaryTraceOrder (X := CMfd.of O) S P x=(L.map fun I => ordinaryTraceOrder (X := CMfd.of O) S I x).sum) ∧
        IsInvDomain n (⟨S,[],P,1⟩ : MarkedIdeal n O) := by
  obtain ⟨O,hO,hMembers⟩ := exists_original_first_good_lower_members hn hW hE hdense d hr T hT
  refine ⟨O,hO,?_⟩
  intro i
  let S := (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T
  let L := ((List.finRange E.length).filter (fun j => j ≠ i)).map fun j => actualLowerTraceMember W E i j T O
  have hS := (hMembers i).1
  have hL : ∀ I ∈ L,I.IsCoherent ∧ (∀ x ∈ S,IsNonzeroAlongAt S I x) ∧
      ∀ x ∈ S,∃ f : O → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) S (·=f) x g := by
    intro I hIL
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hIL
    exact (hMembers i).2 j (of_decide_eq_true (List.mem_filter.mp hj).2)
  obtain ⟨hc,hnz,hpr,hOrd⟩ := relativeIdealListProduct_actual_geometry (X := CMfd.of O) hS L
    (fun I hI => (hL I hI).1) (fun I hI => (hL I hI).2.1) (fun I hI => (hL I hI).2.2)
  refine ⟨hc,hnz,hpr,hOrd,?_⟩
  refine ⟨⟨hS,hc,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hS⟩,?_,le_rfl,hnz⟩
  intro x hx
  obtain ⟨k,hk⟩ := hS.2 x hx
  exact ⟨k,hk.1,hk⟩

end
end Hironaka.HironakaSharpActualFirstGoodLowerProduct
