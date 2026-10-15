/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.ColonUnitIdealExact
import Hironaka.Resolution.HironakaSharpActualChronologicalNoOldFactor

/-! Genuine no-common-member witnesses force actual divExp zero by coherent
continuation, then whole monomial unit and actual carrier-normalized residual.
Composite original raw-TOTAL factor transport and sharp driver remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualChronologicalResidualDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualChronologicalNoOldFactor HironakaSharpActualFiniteChronologicalHistory
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers MemberTraceIdealAlong
variable {n : ℕ} {X : CMfd.{u} n}

/-- Real maximal-divisibility neighborhoods and true coherent persistence
force the ACTUAL incident exponent zero, without an exponent certificate. -/
theorem divExpAlong_eq_zero_of_no_member_factor {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {I : GermIdeal n X} (hI : I.IsCoherent)
    (hnd : ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a)
    {x : X} (hx : x ∈ N) (i : Fin E.length) (hxi : x ∈ E.get i) :
    divExpAlong n N I (E.get i) x=0 := by
  by_contra hne
  have hpos : 1 ≤ divExpAlong n N I (E.get i) x := Nat.one_le_iff_ne_zero.mpr hne
  have hhol := fun y g (hg : I.mem y g) => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  have hdiv := (isDivNearAlong_divExpAlong hhol x).mono hpos
  obtain ⟨a,ha,hna⟩ := hnd x hx i hxi
  apply hna
  apply (isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx i (hhol x a ha)).mpr
  refine ⟨hhol x a ha,?_⟩
  filter_upwards [hdiv,HadamardBridge.eventually_mem_of_isCoherent hI ha] with y hy hya hyNH
  exact (vanishesToOrderOn_one_iff hyNH.1 (hhol y a hya)).mp ((hy hyNH.1 hyNH.2).2 a hya)

/-- Genuine exponent0 implies BOTH WHOLE monomial membership directions,
at EVERY ambient point, including outside the actual carrier. -/
theorem monomialPartAlong_eq_unit_of_no_member_factor {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {I : GermIdeal n X} (hI : I.IsCoherent)
    (hnd : ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a) :
    monomialPartAlong n N I E=unitIdeal n X := by
  ext x g
  change (HolomorphicAt n g x ∧ _) ↔ HolomorphicAt n g x
  refine ⟨fun hg => hg.1,fun hg => ⟨hg,?_⟩⟩
  intro i hxN hxH
  rw [divExpAlong_eq_zero_of_no_member_factor hE hT hI hnd hxN i hxH,idealPow_zero]
  exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hg hg)

/-- The actual whole nonmonomial colon is precisely true carrier normalization;
its WHOLE unit denominator was independently proved first. -/
theorem nonmonomialPartAlong_eq_restrictOn_of_no_member_factor {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent)
    (hnd : ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a) :
    nonmonomialPartAlong n N I E=restrictOn n N I := by
  change InvertibleIdealQuotient.colon (restrictOn n N I) (monomialPartAlong n N I E)=_
  rw [monomialPartAlong_eq_unit_of_no_member_factor hE hT hI hnd,
    BlowupControlledTransform.colon_unitIdeal (isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN))]

/-- ONLY original data internally supply actual nofactor/principal geometry
before real all-prefix exponents and SAME actual residual dictionaries. -/
theorem original_members_actual_chronological_residual_dictionary (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    (∀ y ∈ A.N,∀ j : Fin A.E.length,y ∈ A.E.get j → divExpAlong n A.N A.ideal (A.E.get j) y=0) ∧
      monomialPartAlong n A.N A.ideal A.E=unitIdeal n Y ∧
      nonmonomialPartAlong n A.N A.ideal A.E=restrictOn n A.N A.ideal ∧
      ∀ y ∈ A.N,∀ g, (nonmonomialPartAlong n A.N A.ideal A.E).mem y g ↔ A.ideal.mem y g := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  obtain ⟨_hN,_hE,_hm,hwA,_hnzA,hprA⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  have hnd := original_members_actual_finite_chronological_no_exceptional_factor hn hW hE hdense i T hT
  have hM := monomialPartAlong_eq_unit_of_no_member_factor hwA.isSNCDivisor hwA.isTransverse hwA.isCoherent hnd
  have hNm := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hwA.isClosedSubmanifold_N
    hwA.isSNCDivisor hwA.isTransverse hwA.isCoherent hnd
  refine ⟨fun y hy j hyj => divExpAlong_eq_zero_of_no_member_factor hwA.isSNCDivisor hwA.isTransverse hwA.isCoherent hnd hy j hyj,hM,hNm,?_⟩
  intro y hy g
  rw [hNm]
  obtain ⟨f,_hf,hgen⟩ := hprA y hy
  constructor
  · intro hg
    exact (hgen g).mpr ⟨hg.1,IsInSpanOnAt.trans (fun s hs => ((hgen s).mp hs).2) hg.2⟩
  · exact fun hg => le_restrictOn hwA.isCoherent y g hg

end
end Hironaka.HironakaSharpActualChronologicalResidualDictionary
