import Hironaka.Resolution.HironakaG4IncidentOldBornStratumCentre
import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Resolution.HironakaG4DisjointOldStrictTrace
import Hironaka.Resolution.HironakaG4SelectedBornCanonicalColumns
import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler
import Hironaka.Resolution.HironakaG4ActiveMonomialSharpBad
import Hironaka.Resolution.HironakaG4CanonicalZeroRowUnit

/-! Genuine compact-support WHOLE-monomial cleanup by general coherent SUM mask resolution.
Only the actual old-incidence support must be compact; the carrier may be noncompact.
Complete source-first chapter: hironaka-g4-compact-whole-monomial-mask-phase.tex.
Current sharp centres, all actual old positions and original footprints are retained.
No D-factor/nonunit-residual preparation or original canonicality is inferred. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4CompactWholeMonomialMaskPhase

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MemberInterTowerAlong MemberInterLocusAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealOperationsTransform
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualOriginalControlledHistory HironakaCoherentTransformExtension
  HironakaG4RecordedTowerResidualCompatibility HironakaG4DisjointOldStrictTrace
  HironakaG4SelectedBornCanonicalColumns HironakaG4ActiveMonomialSharpBad
  HironakaG4CanonicalZeroRowUnit HironakaSharpActualCurveWholeBoundaryTransversality
  HironakaG4IncidentOldBornStratumCentre HironakaSharpActualFirstAmbientStrictTraceFactor
  HironakaSharpActualCompositeTotalResidual HironakaSharpNormalCrossingsOpenLocus
  RelativePrincipalizationSpan RestrictedIdealExtension IdealWeightPowers InvertibleIdealQuotient
  RestrictEmptyTower HironakaAdmissibleSequence
  DivisorExponentAlong GermIdealOrder MonomialPartAlong MonomialPart NormalCrossings
  NormalCrossingsComparison SimultaneousNormalCrossings BlowupStrictSubmanifold BlowupSNCTransform

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Every literal actual next centre avoids the ENTIRE current NC region,
read on the true strict carrier and full ordered ambient boundary. -/
def CurrentSharpCentres (N : Set X) (E : List (Set X)) :
    {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CurrentSharpCentres N E T ∧
      C ⊆ originalSharpBadLocus (n := n) (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E

private def oldRow (N : Set X) (B : List (Set X)) (I : GermIdeal n X) : MarkedIdeal n X :=
  ⟨N,B,I,1⟩

private def sumMarked {ι : Type} (N : Set X) (B : List (Set X))
    (I : ι → GermIdeal n X) (first : ι) : List ι → MarkedIdeal n X
  | [] => oldRow N B (I first)
  | j :: tail => MarkedIdealOperationsTransform.MarkedIdeal.add
      (oldRow N B (I j)) (sumMarked N B I first tail)

@[simp] private theorem sumMarked_N {ι : Type} (N : Set X) (B : List (Set X))
    (I : ι → GermIdeal n X) (i : ι) (L : List ι) : (sumMarked N B I i L).N=N := by
  cases L <;> rfl

@[simp] private theorem sumMarked_E {ι : Type} (N : Set X) (B : List (Set X))
    (I : ι → GermIdeal n X) (i : ι) (L : List ι) : (sumMarked N B I i L).E=B := by
  cases L <;> rfl

@[simp] private theorem sumMarked_d {ι : Type} (N : Set X) (B : List (Set X))
    (I : ι → GermIdeal n X) (i : ι) (L : List ι) : (sumMarked N B I i L).d=1 := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    change 1 * (sumMarked N B I i L).d=1
    rw [ih]

private theorem sumMarked_coherent {ι : Type} (N : Set X) (B : List (Set X))
    (I : ι → GermIdeal n X) (hI : ∀ i,(I i).IsCoherent) (i : ι) (L : List ι) :
    (sumMarked N B I i L).ideal.IsCoherent := by
  induction L with
  | nil => exact hI i
  | cons j L ih =>
    exact isCoherent_sumIdeal (GermIdealPullbackCalculus.isCoherent_idealPow (hI j) _)
      (GermIdealPullbackCalculus.isCoherent_idealPow ih _)

private theorem sumMarked_pair {ι : Type} {N : Set X} (hN : IsClosedSubmanifold n N)
    (B : List (Set X)) (I : ι → GermIdeal n X) (hI : ∀ i,(I i).IsCoherent)
    (i j : ι) (L : List ι) :
    IsSubmanifoldPair (oldRow N B (I j)) (sumMarked N B I i L) := by
  exact ⟨(sumMarked_N N B I i L).symm,(sumMarked_E N B I i L).symm,
    hN,hI j,sumMarked_coherent N B I hI i L⟩

private theorem sumMarked_nonzero {ι : Type} (N : Set X) (B : List (Set X))
    (I : ι → GermIdeal n X) (hI : ∀ i,(I i).IsCoherent)
    (hne : ∀ i,∀ x ∈ N,IsNonzeroAlongAt N (I i) x) (i : ι) (L : List ι)
    {x : X} (hx : x ∈ N) : IsNonzeroAlongAt N (sumMarked N B I i L).ideal x := by
  cases L with
  | nil => exact hne i x hx
  | cons j L =>
    apply InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
    exact InvDomainCompanion.isNonzeroAlongAt_idealPow
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hI j) hg) (hne j x hx) _

private theorem sumMarked_test_iff {ι : Type} {N : Set X} (hN : IsClosedSubmanifold n N)
    (B : List (Set X)) (I : ι → GermIdeal n X) (hI : ∀ i,(I i).IsCoherent)
    (i : ι) (L : List ι) (T : BlowupTower X Y) :
    IsGeoTestTower (sumMarked N B I i L) T ↔
      IsGeoTestTower (oldRow N B (I i)) T ∧
        ∀ j ∈ L,IsGeoTestTower (oldRow N B (I j)) T := by
  induction L with
  | nil => simp [sumMarked]
  | cons j L ih =>
    rw [sumMarked,(geoTransformAlong_add_along (oldRow N B (I j))
      (sumMarked N B I i L) (sumMarked_pair hN B I hI i j L) (by rfl)
        (by rw [sumMarked_d]) T).1,ih]
    simp only [List.mem_cons,forall_eq_or_imp]
    tauto

private theorem sumMarked_cosupp_iff {ι : Type} {N : Set X} (hN : IsClosedSubmanifold n N)
    (B : List (Set X)) (I : ι → GermIdeal n X) (hI : ∀ i,(I i).IsCoherent)
    (i : ι) (L : List ι) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (sumMarked N B I i L) T) (y : Y) :
    y ∈ (geoTransformAlong (sumMarked N B I i L) T).cosupp ↔
      y ∈ (geoTransformAlong (oldRow N B (I i)) T).cosupp ∧
        ∀ j ∈ L,y ∈ (geoTransformAlong (oldRow N B (I j)) T).cosupp := by
  induction L with
  | nil => simp [sumMarked]
  | cons j L ih =>
    have hAdd := geoTransformAlong_add_along (oldRow N B (I j))
      (sumMarked N B I i L) (sumMarked_pair hN B I hI i j L)
      (by rfl) (by rw [sumMarked_d]) T
    obtain ⟨hj,hTail⟩ := hAdd.1.mp hT
    obtain ⟨hEq,hPair,_hc⟩ := hAdd.2 hj hTail
    change y ∈ (geoTransformAlong
      (MarkedIdealOperationsTransform.MarkedIdeal.add (oldRow N B (I j))
        (sumMarked N B I i L)) T).cosupp ↔ _
    rw [hEq.cosupp_eq,cosupp_add_along hPair
      (by rw [d_geoTransformAlong];rfl)
      (by rw [d_geoTransformAlong,sumMarked_d]),Set.mem_inter_iff,ih hTail]
    simp only [List.mem_cons,forall_eq_or_imp]
    tauto

private abbrev rowIdeal {r : ℕ} (N : Set X) (H : Fin r → Set X) (i : Fin r) :
    GermIdeal n X := restrictOn n N (vanishingIdeal (n := n) (H i))

def incidentOld {r : ℕ} (H : Fin r → Set X) (x : X) : Finset (Fin r) :=
  Finset.univ.filter (fun i => x ∈ H i)

structure Region {r : ℕ} (N : Set X) (H : Fin r → Set X) (B : List (Set X)) : Prop where
  smooth : IsClosedSubmanifold n N
  /-- Compactness of the actual old-incidence support; no compact-carrier premise. -/
  compact : IsCompact (N ∩ ⋃ i : Fin r,H i)
  full : IsSNCDivisor n (List.ofFn H ++ B)
  transverse : IsTransverse n N B
  dense : N ⊆ closure (N \ ⋃ A ∈ List.ofFn H ++ B,A)
  monomial : ∀ i,IsMonomialAlong n N (rowIdeal N H i) B

private theorem Region.member_mem {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (_hR : Region N H B) (i : Fin r) : H i ∈ List.ofFn H ++ B :=
  List.mem_append_left B (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem Region.member_smooth {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (i : Fin r) : IsClosedSubmanifold n (H i) := by
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (hR.member_mem i)
  rw [←hj]
  exact MonomialPart.isClosedSubmanifold_get hn hR.full j

private theorem Region.row_coherent {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (i : Fin r) : (rowIdeal N H i).IsCoherent :=
  isCoherent_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal (hR.member_smooth hn i))
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hR.smooth)

private theorem Region.row_nonzero {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (i : Fin r) (x : X) (hx : x ∈ N) :
    IsNonzeroAlongAt N (rowIdeal N H i) x := by
  obtain ⟨g,hg,hfreq⟩ := HironakaSharpOriginalMemberProductDomain.originalMemberIdeal_isNonzeroAlongAt
    hR.full hR.dense (hR.member_mem i) hx
  exact ⟨g,le_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal
    (hR.member_smooth hn i)) x g hg,hfreq⟩

private theorem row_cosupp {N A : Set X} (hA : IsClosedSubmanifold n A) (B : List (Set X)) :
    (oldRow N B (restrictOn n N (vanishingIdeal (n := n) A))).cosupp=N ∩ A := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal hA
  have hEq : RestrictEquiv (oldRow N B (restrictOn n N (vanishingIdeal (n := n) A)))
      (oldRow N B (vanishingIdeal (n := n) A)) :=
    ⟨rfl,rfl,rfl,restrictLe_restrictOn,restrictLe_self_restrictOn hI⟩
  rw [hEq.cosupp_eq]
  exact SmoothCentreLocus.cosupport_vanishingIdeal_one hA.1

private theorem contained_old_whole_trace {N A C : Set X}
    (hN : IsClosedSubmanifold n N) (hA : IsClosedSubmanifold n A)
    (B : List (Set X)) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ N) (hCA : C ⊆ A) :
    ((oldRow N B (restrictOn n N (vanishingIdeal (n := n) A))).geoTransform C π).ideal=
      restrictOn n (geoStrictTransform π C N) (vanishingIdeal (n := n) (geoStrictTransform π C A)) := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal hA
  have hcI := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  have hEq : RestrictEquiv (oldRow N B (restrictOn n N (vanishingIdeal (n := n) A)))
      (oldRow N B (vanishingIdeal (n := n) A)) :=
    ⟨rfl,rfl,rfl,restrictLe_restrictOn,restrictLe_self_restrictOn hI⟩
  have hWhole := congrArg MarkedIdeal.ideal (hEq.geoTransform_eq hN.1 hcI hI hπ.contMDiff (C := C))
  rw [hWhole]
  exact actual_first_controlled_ambient_strict_trace hN hA hπ hCN hCA

private theorem Region.row_wellFormed {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (i : Fin r) (d : ℕ) :
    (⟨N,B,rowIdeal N H i,d⟩ : MarkedIdeal n X).IsWellFormed :=
  ⟨hR.smooth,hR.row_coherent hn i,
    isSNCDivisor_of_sublist hR.full (List.sublist_append_right _ _),hR.transverse⟩

private theorem Region.sum_domain {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (i : Fin r) (L : List (Fin r)) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (sumMarked N B (rowIdeal N H) i L) where
  isWellFormed := by
    refine ⟨?_,sumMarked_coherent N B (rowIdeal N H) (hR.row_coherent hn) i L,?_,?_⟩
    · simpa only [sumMarked_N] using hR.smooth
    · simpa only [sumMarked_E] using
        isSNCDivisor_of_sublist hR.full (List.sublist_append_right _ _)
    · simpa only [sumMarked_N,sumMarked_E] using hR.transverse
  dimLE := by
    intro x hx
    rw [sumMarked_N] at hx ⊢
    obtain ⟨k,hk⟩ := hR.smooth.2 x hx
    exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩
  one_le_d := by rw [sumMarked_d]
  isNonzeroAlongAt := by
    intro x hx
    rw [sumMarked_N] at hx ⊢
    exact sumMarked_nonzero N B (rowIdeal N H) (hR.row_coherent hn) (hR.row_nonzero hn) i L hx

theorem Region.old_incident_bad {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) {x : X} (hx : x ∈ N) (i : Fin r) (hxi : x ∈ H i) :
    x ∈ originalSharpBadLocus (n := n) N (List.ofFn H ++ B) := by
  refine ⟨hx,?_⟩
  intro hNC
  let oi : Fin (List.ofFn H ++ B).length := ⟨i.val,by simp only [List.length_append,List.length_ofFn];omega⟩
  have hOld : (List.ofFn H ++ B).get oi=H i := by
    simp [oi,List.get_eq_getElem ]
  have hD : (monomialPartAlong n N (rowIdeal N H i) B).mem x 1 := by
    apply (HironakaSharpActualTraceIncidence.one_mem_monomialPartAlong_iff (rowIdeal N H i) B hx).mpr
    intro j hxj
    let bj : Fin (List.ofFn H ++ B).length :=
      ⟨r+j.val,by simp only [List.length_append,List.length_ofFn];omega⟩
    have hBorn : (List.ofFn H ++ B).get bj=B.get j := by
      simp [bj,List.get_eq_getElem ]
    have hne : oi≠bj := by
      intro he
      have := congrArg Fin.val he
      dsimp [oi,bj] at this
      omega
    have hz := divExpAlong_restricted_member_eq_zero_at_normalCrossings hn hR.smooth hR.full
      hR.dense hx hNC oi bj hne (by rwa [hBorn])
    simpa only [hOld,hBorn] using hz
  have hOne := one_mem_of_restricted_span_one (hR.row_coherent hn i) hx
    (hR.monomial i x hx 1 hD)
  exact ((HironakaSharpActualCurveExceptionalDifference.actual_normalized_vanishing_unit_iff
    (hR.member_smooth hn i).1 hx).mp hOne) hxi

private theorem incident_strict_subset {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (T : BlowupTower X Y) (y : Y) :
    incidentOld (fun i => strictAlong T (H i)) y ⊆ incidentOld H (T.proj y) := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    strictAlong_subset_preimage T (hR.member_smooth hn i).1 (Finset.mem_filter.mp hi).2⟩

theorem incident_strict_bound {r q : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (hbound : ∀ x ∈ N,(incidentOld H x).card≤q)
    (T : BlowupTower X Y) {y : Y} (hy : y ∈ strictAlong T N) :
    (incidentOld (fun i => strictAlong T (H i)) y).card≤q :=
  (Finset.card_le_card (incident_strict_subset hn hR T y)).trans
    (hbound _ (strictAlong_subset_preimage T hR.smooth.1 hy))

private theorem outside_mask_disjoint {r : ℕ} {N C : Set X} {H : Fin r → Set X}
    (P : Finset (Fin r)) (hbound : ∀ x ∈ N,(incidentOld H x).card≤P.card)
    (hCN : C ⊆ N) (hCP : ∀ i ∈ P,C ⊆ H i) (i : Fin r) (hi : i ∉ P) :
    Disjoint C (H i) := by
  apply Set.disjoint_left.mpr
  intro x hxC hxi
  have hsub : P ⊆ incidentOld H x := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hCP j hj hxC⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (hbound x (hCN hxC))
  apply hi
  rw [heq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxi⟩

private theorem born_ordered (N : Set X) (B : List (Set X)) (T : BlowupTower X Y) :
    (geoTransformAlong (geometricTemplate N B) T).E=
      B.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N []) T).E := by
  rw [←geoTransformAlong_E_eq_of_E_eq (𝔍 := geometricTemplate (univ : Set X) B)
    (𝔪 := geometricTemplate N B) rfl T]
  exact actual_whole_ambient_boundary_ordered_dictionary N B T

theorem full_ordered {r : ℕ} (N : Set X) (H : Fin r → Set X) (B : List (Set X))
    (T : BlowupTower X Y) :
    (geoTransformAlong (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) T).E=
      List.ofFn (fun i => strictAlong T (H i)) ++ (geoTransformAlong (geometricTemplate N B) T).E := by
  rw [actual_whole_ambient_boundary_ordered_dictionary N (List.ofFn H ++ B) T,born_ordered N B T]
  simp only [List.map_append,List.map_ofFn,List.append_assoc]
  rfl

private theorem empty_born_test {N : Set X} (hN : IsClosedSubmanifold n N) (B : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate N B) T →
      IsGeoTestTower (geometricTemplate N []) T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hT => by
    have hPrev := empty_born_test hN B T hT.1
    have hw0 : (geometricTemplate N []).IsWellFormed :=
      ⟨hN,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
    have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hPrev
    have hNC : HasNormalCrossings n C (geoTransformAlong (geometricTemplate N []) T).E :=
      hasNormalCrossings_of_forall_mem hT.2.2.2 (by
        intro A hA
        rw [born_ordered N B T]
        exact List.mem_append_right _ hA)
    refine ⟨hPrev,⟨hT.2.1,?_,hNC⟩⟩
    change C ⊆ cosupport n _ _ (geoTransformAlong (geometricTemplate N []) T).d
    rw [d_geoTransformAlong]
    change C ⊆ cosupport n _ _ 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hw.isCoherent hg)]
    rw [←geoTransformAlong_N_eq_of_N_eq (𝔍 := geometricTemplate N B)
      (𝔪 := geometricTemplate N []) rfl T]
    exact hT.2.subset_N

private theorem Region.after_tests {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate N B) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) T)
    (hMono : ∀ i,IsMonomialAlong n (strictAlong T N)
      (rowIdeal (strictAlong T N) (fun j => strictAlong T (H j)) i)
      (geoTransformAlong (geometricTemplate N B) T).E) :
    Region (strictAlong T N) (fun i => strictAlong T (H i))
      (geoTransformAlong (geometricTemplate N B) T).E := by
  have hBorn := isSNCDivisor_of_sublist hR.full (List.sublist_append_right _ _)
  have hw0 : (geometricTemplate N B).IsWellFormed :=
    ⟨hR.smooth,isCoherent_unitIdeal,hBorn,hR.transverse⟩
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT
  have hwF0 : (geometricTemplate (univ : Set X) (List.ofFn H ++ B)).IsWellFormed :=
    ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
      isCoherent_unitIdeal,hR.full,isTransverse_univ_of_isSNCDivisor hR.full⟩
  have hwF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwF0 T hFull
  have hD := (actual_recorded_tower_residual_dictionary hn hR.smooth hR.full hR.dense T
    (empty_born_test hR.smooth B T hT) hFull).2.2.2.1
  rw [N_geoTransformAlong] at hD
  rw [←actual_whole_ambient_boundary_ordered_dictionary N (List.ofFn H ++ B) T,
    full_ordered N H B T] at hD
  refine ⟨?_,?_,?_,?_,hD,hMono⟩
  · simpa only [N_geoTransformAlong,geometricTemplate] using hw.isClosedSubmanifold_N
  · have hClosedOld : IsClosed (⋃ i : Fin r,strictAlong T (H i)) :=
      isClosed_iUnion_of_finite (fun i => isClosed_strictAlong T (hR.member_smooth hn i).1)
    refine ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hR.compact).of_isClosed_subset
      ((isClosed_strictAlong T hR.smooth.1).inter hClosedOld) ?_
    rintro y ⟨hyN,hyH⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hyH
    exact ⟨strictAlong_subset_preimage T hR.smooth.1 hyN,
      mem_iUnion.mpr ⟨i,strictAlong_subset_preimage T (hR.member_smooth hn i).1 hi⟩⟩
  · have hs := hwF.isSNCDivisor
    rwa [full_ordered N H B T] at hs
  · simpa only [N_geoTransformAlong,geometricTemplate] using hw.isTransverse

private theorem template_ideal (N : Set X) (B : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate N B) T).ideal=unitIdeal n Y
  | _,.refl => rfl
  | _,.step T C π _ => by
    ext y g
    change ((geoTransformAlong (geometricTemplate N B) T).geoTransform C π).ideal.mem y g ↔
      HolomorphicAt n g y
    apply HironakaG4UnitRowGeoTransform.geoTransform_mem_iff_holomorphic_of_one_mem
    rw [template_ideal N B T]
    exact holomorphicAt_const 1

theorem template_current (N : Set X) (B : List (Set X)) (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate N B) T=
      geometricTemplate (strictAlong T N) (geoTransformAlong (geometricTemplate N B) T).E := by
  change (⟨(geoTransformAlong (geometricTemplate N B) T).N,
      (geoTransformAlong (geometricTemplate N B) T).E,
      (geoTransformAlong (geometricTemplate N B) T).ideal,
      (geoTransformAlong (geometricTemplate N B) T).d⟩ : MarkedIdeal n Y)=_
  rw [N_geoTransformAlong,template_ideal,d_geoTransformAlong]
  rfl

theorem strict_univ : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    strictAlong T (univ : Set X)=univ
  | _,.refl => rfl
  | _,.step T C π hπ => by
    change geoStrictTransform π C (strictAlong T (univ : Set X))=univ
    rw [strict_univ T]
    exact geoStrictTransform_univ hπ

theorem currentSharp_append (N : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (hT : CurrentSharpCentres N E T)
    (hS : CurrentSharpCentres (strictAlong T N)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E S) :
    CurrentSharpCentres N E (T.append S) := by
  induction S with
  | refl => exact hT
  | step S C π hπ ih =>
    refine ⟨ih hS.1,?_⟩
    rw [strictAlong_append T N S,geoTransformAlong_append,
      template_current (univ : Set X) E T,strict_univ T]
    exact hS.2

private theorem row_current {r : ℕ} (N : Set X) (H : Fin r → Set X) (B : List (Set X))
    (i : Fin r) (T : BlowupTower X Y)
    (hI : (geoTransformAlong (oldRow N B (rowIdeal N H i)) T).ideal=
      rowIdeal (strictAlong T N) (fun j => strictAlong T (H j)) i) :
    geoTransformAlong (oldRow N B (rowIdeal N H i)) T=
      oldRow (strictAlong T N) (geoTransformAlong (geometricTemplate N B) T).E
        (rowIdeal (strictAlong T N) (fun j => strictAlong T (H j)) i) := by
  change (⟨(geoTransformAlong (oldRow N B (rowIdeal N H i)) T).N,
    (geoTransformAlong (oldRow N B (rowIdeal N H i)) T).E,
    (geoTransformAlong (oldRow N B (rowIdeal N H i)) T).ideal,
    (geoTransformAlong (oldRow N B (rowIdeal N H i)) T).d⟩ : MarkedIdeal n Y)=_
  rw [N_geoTransformAlong,geoTransformAlong_E_eq_of_E_eq
    (𝔍 := oldRow N B (rowIdeal N H i)) (𝔪 := geometricTemplate N B) rfl T,
    hI,d_geoTransformAlong]
  rfl

private theorem mask_prefix {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (P : Finset (Fin r)) (hP : P.Nonempty)
    (hbound : ∀ x ∈ N,(incidentOld H x).card≤P.card) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (∀ i ∈ P,IsGeoTestTower (oldRow N B (rowIdeal N H i)) T) →
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) T ∧
      CurrentSharpCentres N (List.ofFn H ++ B) T ∧
      Region (strictAlong T N) (fun i => strictAlong T (H i))
        (geoTransformAlong (geometricTemplate N B) T).E ∧
      ∀ i ∈ P,(geoTransformAlong (oldRow N B (rowIdeal N H i)) T).ideal=
        rowIdeal (strictAlong T N) (fun j => strictAlong T (H j)) i
  | _,.refl,_hTests => ⟨trivial,trivial,trivial,hR,fun _ _ => rfl⟩
  | _,.step T C π hπ,hTests => by
    obtain ⟨hBorn,hFull,hSharp,hPrev,hRows⟩ :=
      mask_prefix hn hR P hP hbound T (fun i hi => (hTests i hi).1)
    let NT := strictAlong T N
    let HT := fun i => strictAlong T (H i)
    let BT := (geoTransformAlong (geometricTemplate N B) T).E
    obtain ⟨i0,hi0⟩ := hP
    have hCurrent : ∀ i ∈ P,(oldRow NT BT (rowIdeal NT HT i)).IsAdmissibleCentre C := by
      intro i hi
      have hc := (hTests i hi).2
      rwa [row_current N H B i T (hRows i hi)] at hc
    have hCN : C ⊆ NT := (hCurrent i0 hi0).subset_N
    have hCB : HasNormalCrossings n C BT := (hCurrent i0 hi0).2.2
    have hCP : ∀ i ∈ P,C ⊆ HT i := by
      intro i hi
      have hc := (hCurrent i hi).2.1
      rw [row_cosupp (hPrev.member_smooth hn i) BT] at hc
      exact hc.trans inter_subset_right
    have hOutside : ∀ i ∉ P,Disjoint C (HT i) := by
      intro i hi
      exact outside_mask_disjoint P
        (fun x hx => incident_strict_bound hn hR hbound T hx) hCN hCP i hi
    have hCFull : HasNormalCrossings n C (List.ofFn HT ++ BT) := by
      intro x hx
      apply actual_incident_old_normalCrossingsAt hPrev.full hCB hx
      intro j hxj
      let i : Fin r := ⟨j.val,by simpa only [List.length_ofFn] using j.isLt⟩
      have hj : (List.ofFn HT).get j=HT i := by simp [List.get_eq_getElem,i]
      have hxi : x ∈ HT i := by rwa [←hj]
      have hi : i ∈ P := by
        by_contra hi
        exact Set.disjoint_left.mp (hOutside i hi) hx hxi
      exact Eventually.of_forall (fun y hy => by rw [hj];exact hCP i hi hy)
    have hBad : C ⊆ originalSharpBadLocus (n := n) (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) T).E := by
      rw [full_ordered N H B T]
      intro x hx
      exact hPrev.old_incident_bad hn (hCN hx) i0 (hCP i0 hi0 hx)
    have hBornNext : IsGeoTestTower (geometricTemplate N B) (.step T C π hπ) :=
      actual_original_test_history_template (oldRow N B (rowIdeal N H i0))
        (hR.row_wellFormed hn i0 1) (.step T C π hπ) (hTests i0 hi0)
    have hwF0 : (geometricTemplate (univ : Set X) (List.ofFn H ++ B)).IsWellFormed :=
      ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
        isCoherent_unitIdeal,hR.full,isTransverse_univ_of_isSNCDivisor hR.full⟩
    have hwF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwF0 T hFull
    have hFullNext : IsGeoTestTower
        (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) (.step T C π hπ) := by
      refine ⟨hFull,⟨hπ.1,?_,?_⟩⟩
      · change C ⊆ cosupport n _ _
          (geoTransformAlong (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) T).d
        rw [d_geoTransformAlong]
        change C ⊆ cosupport n _ _ 0
        rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hwF.isCoherent hg),
          N_geoTransformAlong]
        change C ⊆ strictAlong T (univ : Set X)
        rw [strict_univ T]
        exact subset_univ C
      · rw [full_ordered N H B T]
        exact hCFull
    let d : Fin r → ℕ := fun i => if i ∈ P then 1 else 0
    let M : Fin r → MarkedIdeal n _ := fun i => ⟨NT,BT,rowIdeal NT HT i,d i⟩
    have hAdm : ∀ i,(M i).IsAdmissibleCentre C := by
      intro i
      by_cases hi : i ∈ P
      · simpa only [M,d,if_pos hi,oldRow] using hCurrent i hi
      · refine ⟨hπ.1,?_,hCB⟩
        change C ⊆ cosupport n NT (rowIdeal NT HT i) (d i)
        rw [show d i=0 from if_neg hi,
          cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hPrev.row_coherent hn i) hg)]
        exact hCN
    have hWhole : ∀ i,((M i).geoTransform C π).ideal=
        rowIdeal (geoStrictTransform π C NT) (fun j => geoStrictTransform π C (HT j)) i := by
      intro i
      by_cases hi : i ∈ P
      · simpa only [M,d,if_pos hi,oldRow] using
          contained_old_whole_trace hPrev.smooth (hPrev.member_smooth hn i) BT hπ hCN (hCP i hi)
      · simpa only [M,d,if_neg hi] using
          actual_disjoint_old_zero_mark_trace hPrev.smooth (hPrev.member_smooth hn i) hπ hCN (hOutside i hi)
    have hMonomialNext : ∀ i,IsMonomialAlong n (strictAlong (.step T C π hπ) N)
        (rowIdeal (strictAlong (.step T C π hπ) N) (fun j => strictAlong (.step T C π hπ) (H j)) i)
        (geoTransformAlong (geometricTemplate N B) (.step T C π hπ)).E := by
      intro i
      have hInputs := geoTransform_monomial_inputs hn (hPrev.row_wellFormed hn i (d i))
        (hPrev.row_nonzero hn i) (hPrev.monomial i) (hAdm i) hπ
      change IsMonomialAlong n (geoStrictTransform π C NT)
        (rowIdeal (geoStrictTransform π C NT) (fun j => geoStrictTransform π C (HT j)) i)
        (BT.map (geoStrictTransform π C) ++ [π ⁻¹' C])
      have hm := hInputs.2.2
      change IsMonomialAlong n (geoStrictTransform π C NT) ((M i).geoTransform C π).ideal
        (BT.map (geoStrictTransform π C) ++ [π ⁻¹' C]) at hm
      rwa [hWhole i] at hm
    refine ⟨hBornNext,hFullNext,⟨hSharp,hBad⟩,
      hR.after_tests hn (.step T C π hπ) hBornNext hFullNext hMonomialNext,?_⟩
    intro i hi
    change ((geoTransformAlong (oldRow N B (rowIdeal N H i)) T).geoTransform C π).ideal=_
    rw [row_current N H B i T (hRows i hi),
      contained_old_whole_trace hPrev.smooth (hPrev.member_smooth hn i) BT hπ hCN (hCP i hi)]
    rfl

def maskEmpty {r : ℕ} (N : Set X) (H : Fin r → Set X) (P : Finset (Fin r)) : Prop :=
  ∀ x ∈ N,¬∀ i ∈ P,x ∈ H i

theorem maskEmpty_strict {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) {P : Finset (Fin r)} (hEmpty : maskEmpty N H P)
    (T : BlowupTower X Y) : maskEmpty (strictAlong T N) (fun i => strictAlong T (H i)) P := by
  intro y hy hall
  apply hEmpty (T.proj y) (strictAlong_subset_preimage T hR.smooth.1 hy)
  intro i hi
  exact strictAlong_subset_preimage T (hR.member_smooth hn i).1 (hall i hi)

theorem remove_mask {r : ℕ} {N : Set X} {H : Fin r → Set X} {B : List (Set X)}
    (hn : 0 < n) (hR : Region N H B) (P : Finset (Fin r)) (hP : P.Nonempty)
    (hbound : ∀ x ∈ N,(incidentOld H x).card≤P.card) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) T ∧
      CurrentSharpCentres N (List.ofFn H ++ B) T ∧
      Region (strictAlong T N) (fun i => strictAlong T (H i))
        (geoTransformAlong (geometricTemplate N B) T).E ∧
      CentresOver (N ∩ ⋃ i,H i) T ∧
      maskEmpty (strictAlong T N) (fun i => strictAlong T (H i)) P := by
  obtain ⟨i0,hi0⟩ := hP
  let L := (P.erase i0).toList
  let M := sumMarked N B (rowIdeal N H) i0 L
  have hDom : ResolutionInvariantSpec.IsInvDomain (n+1) M := hR.sum_domain hn i0 L
  have hSub : M.cosupp ⊆ N ∩ ⋃ i,H i := by
    intro x hx
    have hi := ((sumMarked_cosupp_iff hR.smooth B (rowIdeal N H) (hR.row_coherent hn)
      i0 L (.refl : BlowupTower X X) trivial x).mp hx).1
    rw [geoTransformAlong_refl,row_cosupp (hR.member_smooth hn i0) B] at hi
    exact ⟨hi.1,mem_iUnion.mpr ⟨i0,hi.2⟩⟩
  have hCompact : IsCompact M.cosupp := hR.compact.of_isClosed_subset
    (GiraudAlong.isClosed_cosupport_along hDom.isWellFormed.isCoherent
      hDom.isWellFormed.isClosedSubmanifold_N M.d) hSub
  obtain ⟨Y,T,_hCan,hResolution⟩ :=
    HironakaOriginalCompactCosupportGlobalScheduler.exists_original_compact_cosupport_terminal_tower
      hn (n+1) M hDom hCompact
  have hSource := (sumMarked_test_iff hR.smooth B (rowIdeal N H) (hR.row_coherent hn) i0 L T).mp
    hResolution.1
  have hTests : ∀ i ∈ P,IsGeoTestTower (oldRow N B (rowIdeal N H i)) T := by
    intro i hi
    by_cases he : i=i0
    · simpa only [he] using hSource.1
    · exact hSource.2 i (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨he,hi⟩))
  obtain ⟨hBorn,hFull,hSharp,hNext,hRows⟩ := mask_prefix hn hR P ⟨i0,hi0⟩ hbound T hTests
  have hOverSum := centresOver_cosupp M hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent T hResolution.1
  have hOver : CentresOver (N ∩ ⋃ i,H i) T :=
    HironakaEmbeddedBoundary.centresOver_of_inter_subset (fun _ hx => hSub hx.1) T hOverSum hOverSum
  refine ⟨Y,T,hBorn,hFull,hSharp,hNext,hOver,?_⟩
  intro y hy hall
  have hAll : ∀ i ∈ P,y ∈ (geoTransformAlong (oldRow N B (rowIdeal N H i)) T).cosupp := by
    intro i hi
    rw [row_current N H B i T (hRows i hi),
      row_cosupp (hNext.member_smooth hn i) (geoTransformAlong (geometricTemplate N B) T).E]
    exact ⟨hy,hall i hi⟩
  have hySum := (sumMarked_cosupp_iff hR.smooth B (rowIdeal N H) (hR.row_coherent hn)
    i0 L T hResolution.1 y).mpr ⟨hAll i0 hi0,fun j hj =>
      hAll j (Finset.mem_erase.mp (Finset.mem_toList.mp hj)).2⟩
  rw [hResolution.2] at hySum
  exact hySum


/-- The born boundary after concatenation is the actual current born template transform. -/
theorem born_append (N : Set X) (B : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    (geoTransformAlong (geometricTemplate N B) (T.append S)).E=
      (geoTransformAlong (geometricTemplate (strictAlong T N)
        (geoTransformAlong (geometricTemplate N B) T).E) S).E := by
  rw [geoTransformAlong_append]
  exact congrArg (fun M : MarkedIdeal n Y => (geoTransformAlong M S).E)
    (template_current N B T)

/-- Exact full current ordered ambient template, retaining every original old slot. -/
theorem full_template_current {r : ℕ} (N : Set X) (H : Fin r → Set X)
    (B : List (Set X)) (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate (univ : Set X) (List.ofFn H ++ B)) T=
      geometricTemplate (univ : Set Y)
        (List.ofFn (fun i => strictAlong T (H i)) ++
          (geoTransformAlong (geometricTemplate N B) T).E) := by
  rw [template_current (univ : Set X) (List.ofFn H ++ B) T,
    strict_univ T,full_ordered N H B T]


end
end Hironaka.HironakaG4CompactWholeMonomialMaskPhase
