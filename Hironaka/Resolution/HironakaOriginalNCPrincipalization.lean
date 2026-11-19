import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCompactDriver
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumLocalDriver
import Hironaka.Resolution.HironakaPrincipalizationBoundary

/-!
# Principalization retaining a prescribed genuine NC carrier

The ideal is coherent and pointwise nonzero. The original marked datum
is (X,X,[],I,1); the empty RETAINED list does not remove prescribed H.
ONE actual tower carries whole ideal/support/off-zero conclusions,
SAME NEW raw canonicality, ALL original local-branch tests and genuine
NC of the strict prescribed H together with ALL born boundary entries.

The exact-open and precompact-neighbourhood forms add no compactness
of the whole original or restricted zero locus. Every open carries the
literal pulled-back ideal and H. No global SNC labelling of H is used.

Mathematics/API precede source in
work/hironaka-g9-general-nc-public-principalization-20261024/.
SOURCE ONLY. LocalDriver5dcb is narrow-clean but full final/root actual
pending at creation. No formal readiness, Blueprint credit, embedded
first-good-open producer, G8 OR or full original G9 closure is asserted.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCPrincipalization

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupFlatCoordinates NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  GermIdealTotalTransform DivisorExponentAlong
  HironakaAdmissibleSequence HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCOldStratumStrictEquality
  HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCMarkedStratumCompactDriver HironakaOriginalNCMarkedStratumLocalDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ}

/-- Genuine common pair coordinates give NC of the entire old/born union.
Finite avoidance removes every closed born member missing the basepoint. -/
private theorem union_isNormalCrossingsCarrier {X : CMfd.{u} n}
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E) :
    IsNormalCrossingsCarrier (n := n) (H ∪ ⋃ A ∈ E, A) := by
  refine ⟨h.1.union ((List.finite_toSet E).isClosed_biUnion (fun A hA => h.2.1 A hA)), fun x => ?_⟩
  obtain ⟨Φ, S, B, hsrc, h0, hH, hcard, _hinj, hEq⟩ := h.2.2 x
  let P := Finset.univ.filter (fun i : Fin E.length => x ∈ E.get i)
  let S' := S ∪ P.biUnion B
  let W : Set X := ⋂ i : Fin E.length, if x ∈ E.get i then univ else (E.get i)ᶜ
  have hWo : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact isOpen_univ
    · exact (h.2.1 _ (List.get_mem _ _)).isOpen_compl
  have hxW : x ∈ W := by
    apply mem_iInter.mpr
    intro i
    split_ifs with hi
    · exact mem_univ _
    · exact hi
  let e := chartAt (ComplexModel n) x
  let V := e.target ∩ e.symm ⁻¹' W
  have hVo : IsOpen V := e.isOpen_inter_preimage_symm hWo
  have hxV : e x ∈ V := ⟨e.map_source (mem_chart_source _ x), by
    change e.symm (e x) ∈ W
    rwa [e.left_inv (mem_chart_source _ x)]⟩
  let Θ := Φ.restrict V hVo (e x) ⟨Φ.center_mem_source, hxV⟩
  have hflat (y : X) (hy : y ∈ flatDomain Θ) : y ∈ flatDomain Φ ∧ y ∈ W := by
    refine ⟨⟨hy.1, hy.2.1⟩, ?_⟩
    have hh : e.symm (e y) ∈ W := hy.2.2.2
    rwa [e.left_inv hy.1] at hh
  refine ⟨Θ, (fun _ hz => hsrc hz.1), h0, S', fun y hy => ?_⟩
  constructor
  · rintro (hyH | hyE)
    · obtain ⟨j, hj, hz⟩ := (hH y (hflat y hy).1).mp hyH
      exact ⟨j, Finset.mem_union.mpr (Or.inl hj), hz⟩
    · obtain ⟨A, hyA'⟩ := mem_iUnion.mp hyE
      obtain ⟨hA, hyA⟩ := mem_iUnion.mp hyA'
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hA
      have hxi : x ∈ E.get i := by
        by_contra hxi
        have hh := mem_iInter.mp (hflat y hy).2 i
        rw [if_neg hxi] at hh
        exact hh hyA
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard i hxi).1
      have hz := (hEq i hxi y (hflat y hy).1).mp hyA
      refine ⟨a, Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, by simp [ha]⟩)), ?_⟩
      exact hz a (by simp [ha])
  · rintro ⟨a, ha, hya⟩
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Or.inl ((hH y (hflat y hy).1).mpr ⟨a, ha, hya⟩)
    · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
      have hxi : x ∈ E.get i := (Finset.mem_filter.mp hi).2
      have hz : Φ.toFun (e y) ∈ coordSubspace (B i) := by
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hcard i hxi).1
        have hab : a = b := by simpa only [hb, Finset.mem_singleton] using hai
        intro k hk
        have hkb : k = b := by simpa only [hb, Finset.mem_singleton] using hk
        change Φ.toFun (e y) a = 0 at hya
        simpa only [hab, hkb] using hya
      exact Or.inr (mem_iUnion.mpr ⟨E.get i,
        mem_iUnion.mpr ⟨List.get_mem _ _, (hEq i hxi y (hflat y hy).1).mpr hz⟩⟩)

/-- The SAME actual resolving mark-one whole-carrier tower has the entire
principalization geometry. All inputs here are produced internally by
the public driver calls below; this helper is not a separate BP node. -/
private theorem principalization_geometry {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hN : M.N = univ) (hd : M.d = 1) (hE : M.E = [])
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hRes : IsGeoResolution M T)
    (hHistory : IsOriginalBranchTestTower M H T) :
    let E := (geoTransformAlong M T).E
    let D := exceptionalDivisor T
    IsAdmissibleBlowupSequence n X [] M.ideal.zeroLocus Y T.proj E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) T.proj M.ideal = D.ideal ∧
      D.support = (⋃ A ∈ E, A) ∧
      D.support = T.proj ⁻¹' M.ideal.zeroLocus ∧
      IsIsomorphismOver n T.proj M.ideal.zeroLocusᶜ ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
      IsNormalCrossingsCarrier (n := n) (strictAlong T H ∪ ⋃ A ∈ E, A) := by
  have hI := hM.isWellFormed.isCoherent
  have hcos : M.cosupp = M.ideal.zeroLocus := by
    show GermIdealOrder.cosupport n M.N M.ideal M.d = _
    rw [hN, hd, GermIdealOrder.cosupport_one
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg), univ_inter]
  have hpb := pullback_eq_exceptionalDivisor_of_isGeoResolution M hN hI hd T hRes
  have hsuppZ : (exceptionalDivisor T).support = T.proj ⁻¹' M.ideal.zeroLocus := by
    rw [EffectiveDivisor.support, ← hpb, BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj hI]
  have hadm := isAdmissibleBlowupSequence_proj M _ T hRes.1
    (centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hI T hRes.1)
  rw [hcos, hE] at hadm
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop
    M hM.isWellFormed.isSNCDivisor.1 T
  rw [hE] at hsupp
  simp only [List.length_nil, List.drop_zero] at hsupp
  have hIso : IsIsomorphismOver n T.proj M.ideal.zeroLocusᶜ := by
    refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence ?_
    rintro x ⟨y, hy, rfl⟩
    have hy' := HironakaPrincipalization.exceptionalLocus_subset_support T hy
    rw [hsuppZ] at hy'
    exact hy'
  have hPair := (current_old_strata_eq_strict M h T hRes.1 hHistory).1
  exact ⟨hadm,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hRes.1).isWellFormed.isSNCDivisor,
    hpb, hsupp, hsuppZ, hIso, hPair, union_isNormalCrossingsCarrier hPair⟩

/-- Compact-zero-locus principalization with prescribed genuine NC H.
The SAME actual tower supplies every geometry, canonical and branch output. -/
theorem exists_generalNC_principalization_of_isCompact {X : CMfd.{u} n}
    {I : GermIdeal n X} (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (hZ : IsCompact I.zeroLocus) :
    let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      let E := (geoTransformAlong M T).E
      let D := exceptionalDivisor T
      IsGeoResolution M T ∧ IsCanonical M (markedStratumHistoryValue M H) T ∧
      IsOriginalBranchTestTower M H T ∧
      IsAdmissibleBlowupSequence n X [] I.zeroLocus Y T.proj E ∧
      IsSNCDivisor n E ∧ GermIdeal.pullback (m := n) T.proj I = D.ideal ∧
      D.support = (⋃ A ∈ E, A) ∧ D.support = T.proj ⁻¹' I.zeroLocus ∧
      IsIsomorphismOver n T.proj I.zeroLocusᶜ ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
      IsNormalCrossingsCarrier (n := n) (strictAlong T H ∪ ⋃ A ∈ E, A) := by
  let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
  have hM : IsInvDomain n M :=
    HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne isSNCDivisor_nil
  have h : IsBoundaryAdaptedCarrier (n := n) H M.E := boundaryAdapted_nil hH
  have hK : IsCompact M.cosupp := by
    change IsCompact (⟨univ, [], I, 1⟩ : MarkedIdeal n X).cosupp
    rw [cosupp_univ_one hI]
    exact hZ
  obtain ⟨Y, T, hRes, hCan, hHistory⟩ := exists_markedStratum_canonical_resolving_tower M hM hK h
  exact ⟨Y, T, hRes, hCan, hHistory, principalization_geometry M hM rfl rfl rfl h T hRes hHistory⟩

/-- Principalization on the EXACT given open U contained in a compact K.
No compactness of Z(I), or of its trace inside U, is a premise. -/
theorem exists_generalNC_principalization_of_subset_isCompact {X : CMfd.{u} n}
    {I : GermIdeal n X} (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
    let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
    let HU := (Subtype.val : U → X) ⁻¹' H
    ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      let E := (geoTransformAlong MU T).E
      let D := exceptionalDivisor T
      IsGeoResolution MU T ∧ IsCanonical MU (markedStratumHistoryValue MU HU) T ∧
      IsOriginalBranchTestTower MU HU T ∧
      IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' I.zeroLocus) Y T.proj E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) T.proj (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) = D.ideal ∧
      D.support = (⋃ A ∈ E, A) ∧ D.support = T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' I.zeroLocus) ∧
      IsIsomorphismOver n T.proj ((Subtype.val : U → X) ⁻¹' I.zeroLocus)ᶜ ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T HU) E ∧
      IsNormalCrossingsCarrier (n := n) (strictAlong T HU ∪ ⋃ A ∈ E, A) := by
  let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
  have hM : IsInvDomain n M :=
    HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne isSNCDivisor_nil
  have h : IsBoundaryAdaptedCarrier (n := n) H M.E := boundaryAdapted_nil hH
  obtain ⟨Y, T, hRes, hCan, hHistory, _hPair⟩ :=
    exists_markedStratum_resolution_of_subset_isCompact M hM h K hK U hUK
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hMU : IsInvDomain n MU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hGeom := principalization_geometry MU hMU rfl rfl rfl (boundaryAdapted_open U h) T hRes hHistory
  have hZ : (GermIdeal.pullback (m := n) (Subtype.val : U → X) I).zeroLocus =
      (Subtype.val : U → X) ⁻¹' I.zeroLocus :=
    BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hI
  refine ⟨Y, T, hRes, hCan, hHistory, ?_⟩
  simpa only [hZ, MU, M, MarkedIdeal.pullback] using hGeom

/-- One precompact U containing the given compact K, and one tower on U
with all the SAME prescribed-H principalization conclusions. -/
theorem exists_generalNC_principalization_local {X : CMfd.{u} n}
    {I : GermIdeal n X} (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (K : Set X) (hK : IsCompact K) :
    let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
      let HU := (Subtype.val : U → X) ⁻¹' H
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        let E := (geoTransformAlong MU T).E
        let D := exceptionalDivisor T
        IsGeoResolution MU T ∧ IsCanonical MU (markedStratumHistoryValue MU HU) T ∧
        IsOriginalBranchTestTower MU HU T ∧
        IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' I.zeroLocus) Y T.proj E ∧
        IsSNCDivisor n E ∧
        GermIdeal.pullback (m := n) T.proj (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) = D.ideal ∧
        D.support = (⋃ A ∈ E, A) ∧ D.support = T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' I.zeroLocus) ∧
        IsIsomorphismOver n T.proj ((Subtype.val : U → X) ⁻¹' I.zeroLocus)ᶜ ∧
        IsBoundaryAdaptedCarrier (n := n) (strictAlong T HU) E ∧
        IsNormalCrossingsCarrier (n := n) (strictAlong T HU ∪ ⋃ A ∈ E, A) := by
  let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
  have hM : IsInvDomain n M :=
    HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne isSNCDivisor_nil
  have h : IsBoundaryAdaptedCarrier (n := n) H M.E := boundaryAdapted_nil hH
  obtain ⟨U, hKU, hUc, Y, T, hRes, hCan, hHistory, _hPair⟩ :=
    exists_markedStratum_relativelyCompact_local_resolution M hM h K hK
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hMU : IsInvDomain n MU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hGeom := principalization_geometry MU hMU rfl rfl rfl (boundaryAdapted_open U h) T hRes hHistory
  have hZ : (GermIdeal.pullback (m := n) (Subtype.val : U → X) I).zeroLocus =
      (Subtype.val : U → X) ⁻¹' I.zeroLocus :=
    BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hI
  refine ⟨U, hKU, hUc, Y, T, hRes, hCan, hHistory, ?_⟩
  simpa only [hZ, MU, M, MarkedIdeal.pullback] using hGeom

end
end Hironaka.HironakaOriginalNCPrincipalization
