import Hironaka.Resolution.HironakaG4RetainedFactorOpenComparison
import Hironaka.Resolution.HironakaActualGlobalDefectProfileBlock
import Hironaka.Resolution.HironakaG4JointProfileSupport

/-! Physical open comparisons carry the true chronological profile, actual
inactive labels and retained defect rank after the native sharp block. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedRankOpenComparison
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism NormalCrossings NormalCrossingsInvariance
  MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBoundaryMaskBlock HironakaSharpOriginalProductTraceOrder
  HironakaActualGlobalDefectProfileBlock HironakaG4RetainedFactorOpenComparison
  HironakaActualRetainedBoundaryJointStep HironakaG4PreparedCentreCoordinates HironakaG4JointProfileSupport

variable {n : ℕ} {X Y Z : CMfd.{u} n}

def retainedProfileAlong (N : Set X) (old born : List (Set X))
    (S : BlowupTower X Y) (z : Y) (i : Fin old.length) : ℕ :=
  ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) S).N
    (chronologicalMarked (retainedResidualMarked N old born i) S).ideal z

def retainedDefectRankAlong (N : Set X) (old born : List (Set X))
    (S : BlowupTower X Y) (z : Y) : ℕ ×ₗ ℕ :=
  let r := retainedProfileAlong N old born S z
  toLex (∑ i,r i,(retainedInactiveRows N old born r S z).card)


/-- Ordered comparison of actual row orders and factor units preserves the
entire labelled inactive set and the numerical rank. -/
theorem inactive_mask_and_rank_eq_of_ordered_comparison
    {X' : CMfd.{u} n} {N : Set X} {N' : Set X'}
    {old born : List (Set X)} {old' born' : List (Set X')}
    (S : BlowupTower X Y) (R : BlowupTower X' Z) (x : Y) (z : Z)
    (ι : Fin old.length ≃ Fin old'.length)
    (hOrd : ∀ i,retainedProfileAlong N' old' born' R z (ι i)=retainedProfileAlong N old born S x i)
    (hUnit : ∀ i,(retainedFactorMarked N' old' born' R (ι i)).ideal.mem z 1 ↔
      (retainedFactorMarked N old born S i).ideal.mem x 1) :
    let rS := retainedProfileAlong N old born S x
    let rR := retainedProfileAlong N' old' born' R z
    retainedInactiveRows N' old' born' rR R z =
      (retainedInactiveRows N old born rS S x).map ι.toEmbedding ∧
      retainedDefectRankAlong N' old' born' R z = retainedDefectRankAlong N old born S x := by
  classical
  intro rS rR
  have hMask : retainedInactiveRows N' old' born' rR R z =
      (retainedInactiveRows N old born rS S x).map ι.toEmbedding := by
    ext j
    obtain ⟨i,rfl⟩ := ι.surjective j
    rw [Finset.mem_map_equiv,ι.symm_apply_apply]
    simp only [retainedInactiveRows,Finset.mem_filter,Finset.mem_univ,true_and,
      show rR (ι i) = rS i from hOrd i,hUnit i]
  have hSum : ∑ i,rR i = ∑ i,rS i :=
    (ι.sum_comp rR).symm.trans (Finset.sum_congr rfl (fun i _ => hOrd i))
  refine ⟨hMask,?_⟩
  change toLex ((∑ i,rR i),(retainedInactiveRows N' old' born' rR R z).card) =
    toLex ((∑ i,rS i),(retainedInactiveRows N old born rS S x).card)
  rw [hSum,hMask,Finset.card_map]

/-- Under exact open tower comparison, the actual transformed rank and all
its ordered labels are exactly unchanged at corresponding physical points. -/
theorem actual_retained_rank_open_tower_iso (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (hR : IsGeoTestTower (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
      (born.map ((Subtype.val : U → X) ⁻¹' ·))) R)
    (hFullR : IsGeoTestTower (geometricTemplate (univ : Set U)
      ((old.map ((Subtype.val : U → X) ⁻¹' ·)) ++ (born.map ((Subtype.val : U → X) ⁻¹' ·)))) R)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e)
    (z : Z) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let ι : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    let rS := retainedProfileAlong N old born S (e z).val
    let rR := retainedProfileAlong NU OU BU R z
    (∀ i,rR (ι i)=rS i) ∧
      retainedInactiveRows NU OU BU rR R z =
        (retainedInactiveRows N old born rS S (e z).val).map ι.toEmbedding ∧
      retainedDefectRankAlong NU OU BU R z = retainedDefectRankAlong N old born S (e z).val := by
  classical
  intro NU OU BU ι rS rR
  have hOrd (i : Fin old.length) : rR (ι i)=rS i :=
    (actual_retained_orders_and_count_open_tower_iso hn hN hE hTr hdense
      U S hS hFullS R hR hFullR e he z).1 i

  have hUnit (i : Fin old.length) : (retainedFactorMarked NU OU BU R (ι i)).ideal.mem z 1 ↔
      (retainedFactorMarked N old born S i).ideal.mem (e z).val 1 :=
    actual_retained_factor_unit_open_tower_iso_iff hn hN hE hTr hdense U S hS hFullS R e he i z
  exact ⟨hOrd,inactive_mask_and_rank_eq_of_ordered_comparison S R (e z).val z ι hOrd hUnit⟩


/-- Strict decrease of the actual residual lexicographic rank over the
selected native joint cosupport. -/
theorem retained_defect_rank_decrease_of_native_joint_mask (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card)
    (R : BlowupTower X Y) (hRead : RetainedJointMaskResult N old born profile q P R)
    (z : Y) (hz : z ∈ (geoTransformAlong (geometricTemplate N born) R).N)
    (hFoot : R.proj z ∈ (jointProfileMarked N old born q P).cosupp) :
    retainedDefectRankAlong N old born R z < toLex (q,P.card) := by
  have hProgress := retained_joint_mask_progress_over_cosupp hn hN hE hTr hdense
    profile q hq hsum hOrd P hP hBound R hRead z hz hFoot
  let r := retainedProfileAlong N old born R z
  change (∑ i,r i) < q ∨ r = profile ∧ retainedInactiveRows N old born r R z ⊂ P at hProgress
  change toLex ((∑ i,r i),(retainedInactiveRows N old born r R z).card) < toLex (q,P.card)
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases hProgress with hLt | ⟨hOrdEq,hSsub⟩
  · exact Or.inl hLt
  · exact Or.inr ⟨hOrdEq ▸ hsum,Finset.card_lt_card hSsub⟩

/-- The actual strict mask progress is a strict lexicographic rank drop on
the original physical carrier of an open comparison. -/
theorem retained_defect_rank_decrease_of_actual_open_joint_mask (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFullS : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e)
    (q : ℕ) (hq : 1 ≤ q) :
    let XU := CMfd.of (n := n) U
    let NU := (Subtype.val : U → X) ⁻¹' N
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    ∀ (profile : Fin OU.length → ℕ), (∑ i,profile i=q) →
      (∀ x ∈ NU,∀ i,ordinaryTraceOrder NU (oldResidualPart (X := XU) NU OU BU i) x ≤ profile i) →
      ∀ (P : Finset (Fin OU.length)), (∀ i ∈ P,profile i=0) →
        (∀ x ∈ NU,ordinaryTraceOrder NU (canonicalProductMarked (X := XU) NU OU BU q).ideal x=q →
          (inactiveCanonicalRows (X := XU) NU OU BU profile x).card ≤ P.card) →
        RetainedJointMaskResult NU OU BU profile q P R →
        ∀ z ∈ (geoTransformAlong (geometricTemplate NU BU) R).N,
          R.proj z ∈ (jointProfileMarked NU OU BU q P).cosupp →
          retainedDefectRankAlong N old born S (e z).val < toLex (q,P.card) := by
  intro XU NU OU BU profile hsum hOrd P hP hBound hRead z hz hFoot
  obtain ⟨hR,hFullR⟩ : IsGeoTestTower (geometricTemplate NU BU) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) R := by
    cases R <;>
      exact ⟨(hRead.2.2.1 0).1,(hRead.2.2.1 0).2.1⟩
  have hOpen := (actual_retained_rank_open_tower_iso hn hN hE hTr hdense U S hS hFullS R hR hFullR e he z).2.2
  rw [←hOpen]
  have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hEU : IsSNCDivisor n (OU ++ BU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTU : IsTransverse n NU BU := isTransverse_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ OU ++ BU,H) := by
    simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hdense U
  exact retained_defect_rank_decrease_of_native_joint_mask hn hNU hEU hTU hDenseU
    profile q hq hsum hOrd P hP hBound R hRead z hz hFoot

end
end Hironaka.HironakaG4RetainedRankOpenComparison
