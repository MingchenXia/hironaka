import Hironaka.Resolution.HironakaActualRetainedBoundaryMaskBlock
import Hironaka.Resolution.HironakaOriginalCrossingLowerHistory
import Hironaka.MarkedIdeal.MarkedIdealEquivalence

/-! Actual all-original-mask folding, downward inactive-count cleaning and
an actual product-order exit on ONE genuine compact defect-profile window.
The source true distinct-count cut is essential.  The original-profile
global fold and dimension/finite-row processed-state induction are separate.
Source-first proof: `hironaka-actual-retained-boundary-profile-exit-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualRetainedBoundaryProfileExit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  NormalCrossings NormalCrossingsComparison RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBornResidualHistory HironakaActualRetainedBoundaryMaskBlock
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaG4PreparedCentreCoordinates
  HironakaSharpOriginalProductTraceOrder HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus MonomialPartAlong GermIdealOrder DivisorExponentAlong
  MemberInterLocusAlong HironakaG4SharpBadFootprint

variable {n : ℕ} {X Y Z V : CMfd.{u} n}

private def currentIndex (old : List (Set X)) (T : BlowupTower X Y) :
    Fin old.length ≃ Fin (old.map (strictAlong T)).length :=
  (finCongr (List.length_map _)).symm

private theorem currentIndex_get (old : List (Set X)) (T : BlowupTower X Y) (i : Fin old.length) :
    (old.map (strictAlong T)).get (currentIndex old T i)=strictAlong T (old.get i) := by
  simp [currentIndex]

private theorem current_geometry_append (N : Set X) (born : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    geoTransformAlong (geometricTemplate
      (geoTransformAlong (geometricTemplate N born) T).N
      (geoTransformAlong (geometricTemplate N born) T).E) S=
        geoTransformAlong (geometricTemplate N born) (T.append S) := by
  rw [geoTransformAlong_append]
  apply congrArg (fun M : MarkedIdeal n Y => geoTransformAlong M S)
  simpa only [N_geoTransformAlong,geometricTemplate] using (template_current N born T).symm

private theorem row_append (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (S : BlowupTower Y Z) (i : Fin old.length) :
    let A := geoTransformAlong (geometricTemplate N born) T
    chronologicalMarked (retainedResidualMarked A.N (old.map (strictAlong T)) A.E (currentIndex old T i)) S=
      chronologicalMarked (retainedResidualMarked N old born i) (T.append S) := by
  dsimp only
  rw [HironakaG4OriginalSelectedResidualTail.chronological_append_native]
  apply congrArg (fun M : MarkedIdeal n Y => chronologicalMarked M S)
  have hCast : currentIndex old T i=Fin.cast (List.length_map _).symm i := by
    apply Fin.ext
    rfl
  rw [hCast]
  exact retained_seed_eq_chronological_current hn hN hE hTr hdense T hT hFull i

private theorem factor_append (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (i : Fin old.length) :
    let A := geoTransformAlong (geometricTemplate N born) T
    retainedFactorMarked A.N (old.map (strictAlong T)) A.E S (currentIndex old T i)=
      retainedFactorMarked N old born (T.append S) i := by
  unfold retainedFactorMarked
  dsimp only
  rw [current_geometry_append,currentIndex_get,strictAlong_append]

private theorem product_ideal (N : Set X) (old born : List (Set X))
    (q : ℕ) (T : BlowupTower X Y) :
    (retainedProductMarked N old born q T).ideal=
      relativeIdealListProduct (geoTransformAlong (geometricTemplate N born) T).N
        (List.ofFn fun i : Fin old.length =>
          (chronologicalMarked (retainedResidualMarked N old born i) T).ideal) := by
  unfold retainedProductMarked
  dsimp only
  congr 1
  conv_lhs => rw [←List.ofFn_get old,List.map_ofFn]
  rfl

private theorem product_append (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (q : ℕ) (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (S : BlowupTower Y Z) :
    let A := geoTransformAlong (geometricTemplate N born) T
    retainedProductMarked A.N (old.map (strictAlong T)) A.E q S=
      retainedProductMarked N old born q (T.append S) := by
  have hGeom := current_geometry_append N born T S
  dsimp only
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · change (geoTransformAlong (geometricTemplate
      (geoTransformAlong (geometricTemplate N born) T).N
      (geoTransformAlong (geometricTemplate N born) T).E) S).N=
        (geoTransformAlong (geometricTemplate N born) (T.append S)).N
    exact congrArg (fun M : MarkedIdeal n Z => M.N) hGeom
  · change (geoTransformAlong (geometricTemplate
      (geoTransformAlong (geometricTemplate N born) T).N
      (geoTransformAlong (geometricTemplate N born) T).E) S).E=
        (geoTransformAlong (geometricTemplate N born) (T.append S)).E
    exact congrArg (fun M : MarkedIdeal n Z => M.E) hGeom
  · rw [product_ideal,product_ideal,hGeom]
    congr 1
    apply List.ext_get
    · simp
    · intro j hj hj'
      have hRow := congrArg (fun M : MarkedIdeal n Z => M.ideal)
        (row_append hn hN hE hTr hdense T hT hFull S ⟨j,by simpa using hj'⟩)
      have hIndex : currentIndex old T ⟨j,by simpa using hj'⟩=⟨j,by simpa using hj⟩ := by
        apply Fin.ext
        rfl
      rw [hIndex] at hRow
      simpa only [List.get_ofFn,Fin.cast_mk] using hRow

private theorem count_reindex {a b : ℕ} (e : Fin a ≃ Fin b)
    (F : Fin a → GermIdeal n X) (G : Fin b → GermIdeal n X)
    (h : ∀ i,G (e i)=F i) (x : X) :
    actualDistinctProperCount F x=actualDistinctProperCount G x := by
  classical
  have hRel : ∀ i j,(actualIdealGermSetoid F x) i j ↔ (actualIdealGermSetoid G x) (e i) (e j) := by
    intro i j
    change (∀ g,(F i).mem x g ↔ (F j).mem x g) ↔
      (∀ g,(G (e i)).mem x g ↔ (G (e j)).mem x g)
    rw [h i,h j]
  let eqQ := Quotient.congr e hRel
  have hProper (i : Fin a) : e i ∈ actualProperPositions G x ↔ i ∈ actualProperPositions F x := by
    simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and,h i]
  have hImage :
      Finset.map eqQ.toEmbedding ((actualProperPositions F x).image (Quotient.mk (actualIdealGermSetoid F x)))=
        (actualProperPositions G x).image (Quotient.mk (actualIdealGermSetoid G x)) := by
    ext c
    constructor
    · intro hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp hc
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_image.mpr ⟨e i,(hProper i).mpr hi,rfl⟩
    · intro hc
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hc
      refine Finset.mem_map.mpr ⟨Quotient.mk _ (e.symm j),?_,?_⟩
      · exact Finset.mem_image.mpr ⟨e.symm j,(hProper _).mp (by simpa using hj),rfl⟩
      · change Quotient.mk _ (e (e.symm j))=Quotient.mk _ j
        rw [e.apply_symm_apply]
  simpa only [actualDistinctProperCount,Finset.card_map] using congrArg Finset.card hImage

private theorem count_nonincrease (N : Set X) (old born : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (z : Y),
      actualDistinctProperCount (fun i : Fin old.length =>
        (chronologicalMarked (retainedResidualMarked N old born i) T).ideal) z ≤
          actualDistinctProperCount (oldResidualPart N old born) (T.proj z)
  | _,.refl,_ => le_rfl
  | _,.step T C π hπ,z => by
    let A := geoTransformAlong (geometricTemplate N born) T
    let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal
    have hCurrentN (i : Fin old.length) :
        (chronologicalMarked (retainedResidualMarked N old born i) T).N=A.N :=
      (chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) T).1
    have hFamily : (fun i : Fin old.length =>
        (chronologicalMarked (retainedResidualMarked N old born i) (.step T C π hπ)).ideal)=
          (fun i => HironakaSharpActualChronologicalStrictStep.nextRelativeStrict A.N (F i) C π) := by
      funext i
      change HironakaSharpActualChronologicalStrictStep.nextRelativeStrict
        (chronologicalMarked (retainedResidualMarked N old born i) T).N (F i) C π=_
      rw [hCurrentN]
    rw [hFamily]
    exact (HironakaG4DistinctResidualCountTransform.actual_distinct_proper_count_nextRelativeStrict_le
      A.N C π F z).trans (count_nonincrease N old born T (π z))

private theorem family_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S) :
    let A := geoTransformAlong (geometricTemplate N born) S
    ∀ i : Fin old.length,
      let J := (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
      J.IsCoherent ∧ (∀ x ∈ A.N,IsNonzeroAlongAt A.N J x) ∧
        ∀ x ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f x ∧ ∀ g,J.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) A.N (·=f) x g := by
  dsimp only
  intro i
  have hSeed := retainedResidualMarked_geometry hn hN hE hTr hdense i
  obtain ⟨hw,hnz,hpr⟩ := chronologicalMarked_actual_geometry hn
    (retainedResidualMarked N old born i) hSeed.1 rfl hSeed.2.1 hSeed.2.2 S hS
  have hCurrentN := (chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) S).1
  rw [hCurrentN] at hnz hpr
  exact ⟨hw.isCoherent,hnz,hpr⟩

private theorem product_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S) :
    let A := geoTransformAlong (geometricTemplate N born) S
    (retainedProductMarked N old born q S).ideal.IsCoherent ∧
      (∀ y ∈ A.N,IsNonzeroAlongAt A.N (retainedProductMarked N old born q S).ideal y) ∧
      (∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,(retainedProductMarked N old born q S).ideal.mem y g ↔
          HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g) ∧
      ∀ y ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q S).ideal y=
        ∑ i : Fin old.length,ordinaryTraceOrder A.N
          (chronologicalMarked (retainedResidualMarked N old born i) S).ideal y := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hWF : (geometricTemplate N born).IsWellFormed := ⟨hN,IdealWeightPowers.isCoherent_unitIdeal,hBorn,hTr⟩
  have hCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF S hS
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
  have hFam := family_geometry hn hN hE hTr hdense S hS
  have hList : ∀ I ∈ List.ofFn F,I.IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate N born) S).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate N born) S).N I y) ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate N born) S).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,I.mem y g ↔ HolomorphicAt n g y ∧
          IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate N born) S).N (·=f) y g := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact hFam i
  have hp := relativeIdealListProduct_actual_geometry hCurrent.isClosedSubmanifold_N (List.ofFn F)
    (fun I hI => (hList I hI).1) (fun I hI => (hList I hI).2.1) (fun I hI => (hList I hI).2.2)
  dsimp only
  rw [product_ideal]
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  intro y hy
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hp.2.2.2 y hy


private theorem current_row (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T) (i : Fin old.length) :
    let A := geoTransformAlong (geometricTemplate N born) T
    oldResidualPart A.N (old.map (strictAlong T)) A.E (currentIndex old T i)=
      (chronologicalMarked (retainedResidualMarked N old born i) T).ideal := by
  exact congrArg (fun M : MarkedIdeal n Y => M.ideal)
    (row_append hn hN hE hTr hdense T hT hFull (.refl : BlowupTower Y Y) i)

private theorem inactive_append (N : Set X) (old born : List (Set X))
    (profile : Fin old.length → ℕ) (T : BlowupTower X Y) (S : BlowupTower Y Z) (z : Z) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let e := currentIndex old T
    (retainedInactiveRows N old born profile (T.append S) z).map e.toEmbedding=
      retainedInactiveRows A.N (old.map (strictAlong T)) A.E (fun j => profile (e.symm j)) S z := by
  classical
  dsimp only
  let e := currentIndex old T
  ext j
  constructor
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    simp only [retainedInactiveRows,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    change profile (e.symm (e i))=0 ∧ _
    rw [e.symm_apply_apply]
    change profile i=0 ∧ ¬(retainedFactorMarked
      (geoTransformAlong (geometricTemplate N born) T).N (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E S (e i)).ideal.mem z 1
    rw [factor_append]
    exact hi
  · intro hj
    simp only [retainedInactiveRows,Finset.mem_filter,Finset.mem_univ,true_and] at hj
    refine Finset.mem_map.mpr ⟨e.symm j,?_,?_⟩
    · simp only [retainedInactiveRows,Finset.mem_filter,Finset.mem_univ,true_and]
      have hD := factor_append N old born T S (e.symm j)
      change retainedFactorMarked _ _ _ S (e (e.symm j))=_ at hD
      rw [e.apply_symm_apply] at hD
      rw [←hD]
      exact hj
    · change e (e.symm j)=j
      exact e.apply_symm_apply j

private def At (N : Set X) (old born : List (Set X)) (profile : Fin old.length → ℕ)
    (q t : ℕ) (T : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate N born) T
  IsGeoTestTower (geometricTemplate N born) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
    CurrentSharpCentres N (old ++ born) T ∧
    (∀ z ∈ A.N,∀ i,ordinaryTraceOrder A.N
      (chronologicalMarked (retainedResidualMarked N old born i) T).ideal z ≤
        ordinaryTraceOrder N (oldResidualPart N old born i) (T.proj z)) ∧
    IsRetainedProductEquimultiple N old born q T ∧
    IsGeoTestTower (canonicalProductMarked N old born q) T ∧
    MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) T)
      (retainedProductMarked N old born q T) ∧
    ∀ z ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q T).ideal z=q →
      (retainedInactiveRows N old born profile T z).card ≤ t

private def Forward (N : Set X) (old born : List (Set X)) (profile : Fin old.length → ℕ)
    (q t : ℕ) (T : BlowupTower X Y) (R : BlowupTower Y Z) : Prop :=
  At N old born profile q t (T.append R) ∧
    (∀ z ∈ (geoTransformAlong (geometricTemplate N born) (T.append R)).N,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) (T.append R)).N
        (retainedProductMarked N old born q (T.append R)).ideal z=q →
      R.proj z ∈ (geoTransformAlong (geometricTemplate N born) T).N ∧
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) T).N
          (retainedProductMarked N old born q T).ideal (R.proj z)=q) ∧
    ∀ z ∈ (geoTransformAlong (geometricTemplate N born) (T.append R)).N,
      retainedInactiveRows N old born profile (T.append R) z ⊆
        retainedInactiveRows N old born profile T (R.proj z)

private theorem at_refl (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q t : ℕ)
    (hBound : ∀ z ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal z=q →
      (inactiveCanonicalRows N old born profile z).card ≤ t) :
    At N old born profile q t (.refl : BlowupTower X X) := by
  refine ⟨trivial,trivial,trivial,(fun _ _ _ => le_rfl),trivial,trivial,?_,hBound⟩
  exact MarkedIdeal.RestrictEquiv.refl (product_geometry hn hN hE hTr hdense q .refl trivial).1

private theorem forward_refl {N : Set X} {old born : List (Set X)}
    {profile : Fin old.length → ℕ} {q t : ℕ} (T : BlowupTower X Y)
    (h : At N old born profile q t T) : Forward N old born profile q t T (.refl : BlowupTower Y Y) := by
  exact ⟨h,(fun _ hz hzq => ⟨hz,hzq⟩),fun _ _ => Finset.Subset.refl _⟩

private theorem at_mono {N : Set X} {old born : List (Set X)}
    {profile : Fin old.length → ℕ} {q a b : ℕ} {T : BlowupTower X Y}
    (h : At N old born profile q a T) (hab : a ≤ b) : At N old born profile q b T := by
  rcases h with ⟨hT,hFull,hSharp,hRows,hEqui,hProd,hEq,hCap⟩
  exact ⟨hT,hFull,hSharp,hRows,hEqui,hProd,hEq,fun z hz hzq => (hCap z hz hzq).trans hab⟩

private theorem forward_mono {N : Set X} {old born : List (Set X)}
    {profile : Fin old.length → ℕ} {q a b : ℕ} {T : BlowupTower X Y} {R : BlowupTower Y Z}
    (h : Forward N old born profile q a T R) (hab : a ≤ b) : Forward N old born profile q b T R :=
  ⟨at_mono h.1 hab,h.2⟩

private theorem carrier_projects {N : Set X} (hN : IsClosed N) (born : List (Set X))
    (T : BlowupTower X Y) :
    (geoTransformAlong (geometricTemplate N born) T).N ⊆ T.proj ⁻¹' N := by
  rw [N_geoTransformAlong]
  exact MemberInterTowerAlong.strictAlong_subset_preimage T hN

private theorem carrier_append_maps {N : Set X} {born : List (Set X)}
    (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (hClosed : IsClosed (geoTransformAlong (geometricTemplate N born) T).N) :
    (geoTransformAlong (geometricTemplate N born) (T.append R)).N ⊆
      R.proj ⁻¹' (geoTransformAlong (geometricTemplate N born) T).N := by
  rw [←current_geometry_append N born T R]
  exact carrier_projects hClosed _ R

private theorem product_footprint (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {profile : Fin old.length → ℕ} {q t : ℕ}
    (T : BlowupTower X Y) (h : At N old born profile q t T) :
    (retainedProductMarked N old born q T).cosupp ⊆
      T.proj ⁻¹' (canonicalProductMarked N old born q).cosupp := by
  rcases h with ⟨_hT,_hFull,_hSharp,_hRows,_hEqui,hProd,hEq,_hCap⟩
  have hp := product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  intro z hz
  have hzNative := hEq.cosupp_eq.symm ▸ hz
  exact TransformOffCentre.cosupp_geoTransformAlong_subset
    (canonicalProductMarked N old born q) hN hp.1 T hProd hzNative

private theorem top_initial (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q t : ℕ) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (T : BlowupTower X Y) (h : At N old born profile q t T)
    {z : Y} (hz : z ∈ (geoTransformAlong (geometricTemplate N born) T).N)
    (hzq : ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) T).N
      (retainedProductMarked N old born q T).ideal z=q) :
    T.proj z ∈ N ∧ ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (T.proj z)=q := by
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense T h.1 h.2.1
  have hp := product_geometry hn hN hE hTr hdense q T h.1
  have hp0 := product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hzCos : z ∈ (retainedProductMarked N old born q T).cosupp :=
    (ordinaryTraceOrder_cosupport_iff hRec.1 hp.1 hp.2.1 hz q).mpr hzq.ge
  have hCos := product_footprint hn hN hE hTr hdense T h hzCos
  have hxN : T.proj z ∈ N := (canonicalProductMarked N old born q).cosupp_subset_N hCos
  have hGe := (ordinaryTraceOrder_cosupport_iff hN hp0.1 hp0.2.1 hxN q).mp hCos
  have hLe : ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (T.proj z) ≤ q := by
    have hSum : ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (T.proj z)=
        ∑ i,ordinaryTraceOrder N (oldResidualPart N old born i) (T.proj z) := hp0.2.2.2 _ hxN
    rw [hSum,←hsum]
    exact Finset.sum_le_sum (fun i _ => hOrd _ hxN i)
  exact ⟨hxN,hLe.antisymm hGe⟩

private theorem current_inputs (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q t : ℕ) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (T : BlowupTower X Y) (h : At N old born profile q t T) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let O := old.map (strictAlong T)
    let e := currentIndex old T
    (∀ z ∈ A.N,∀ j,ordinaryTraceOrder A.N (oldResidualPart A.N O A.E j) z ≤ profile (e.symm j)) ∧
      IsCompact (canonicalProductMarked A.N O A.E q).cosupp ∧
      ∀ z ∈ A.N,ordinaryTraceOrder A.N (canonicalProductMarked A.N O A.E q).ideal z=q →
        actualDistinctProperCount (oldResidualPart A.N O A.E) z < q := by
  let A := geoTransformAlong (geometricTemplate N born) T
  let O := old.map (strictAlong T)
  let e := currentIndex old T
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense T h.1 h.2.1
  have hp := product_geometry hn hN hE hTr hdense q T h.1
  have hProduct := retainedProductMarked_eq_canonical hn hN hE hTr hdense q T h.1 h.2.1
  refine ⟨?_,?_,?_⟩
  · intro z hz j
    have hRow := current_row hn hN hE hTr hdense T h.1 h.2.1 (e.symm j)
    change oldResidualPart A.N O A.E (e (e.symm j))=_ at hRow
    rw [e.apply_symm_apply] at hRow
    rw [hRow]
    exact (h.2.2.2.1 z hz (e.symm j)).trans
      (hOrd _ (carrier_projects hN.1 born T hz) (e.symm j))
  · have hClosed : IsClosed (retainedProductMarked N old born q T).cosupp :=
      GiraudAlong.isClosed_cosupport_along hp.1 hRec.1 _
    have hK := ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hCompact).of_isClosed_subset
      hClosed (product_footprint hn hN hE hTr hdense T h)
    rw [hProduct] at hK
    exact hK
  · intro z hz hzq
    have hzq' : ordinaryTraceOrder A.N (retainedProductMarked N old born q T).ideal z=q := by
      rw [hProduct]
      exact hzq
    have hTop := top_initial hn hN hE hTr hdense profile q t hsum hOrd T h hz hzq'
    have hEq := count_reindex e
      (fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal)
      (oldResidualPart A.N O A.E) (fun i => current_row hn hN hE hTr hdense T h.1 h.2.1 i) z
    rw [←hEq]
    exact (count_nonincrease N old born T z).trans_lt (hCount _ hTop.1 hTop.2)

private theorem equimultiple_append (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (q : ℕ) (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (S : BlowupTower Y Z) (hEquiT : IsRetainedProductEquimultiple N old born q T)
    (hEquiS : IsRetainedProductEquimultiple
      (geoTransformAlong (geometricTemplate N born) T).N (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E q S) :
    IsRetainedProductEquimultiple N old born q (T.append S) := by
  induction S with
  | refl => exact hEquiT
  | step S C π hπ ih =>
    refine ⟨ih hEquiS.1,?_⟩
    have h := hEquiS.2
    rw [current_geometry_append,product_append hn hN hE hTr hdense q T hT hFull S] at h
    exact h

private theorem restrict_equiv_trans {M L K : MarkedIdeal n X}
    (h : MarkedIdeal.RestrictEquiv M L) (h' : MarkedIdeal.RestrictEquiv L K) :
    MarkedIdeal.RestrictEquiv M K := by
  refine ⟨h.N_eq.trans h'.N_eq,h.E_eq.trans h'.E_eq,h.d_eq.trans h'.d_eq,?_,?_⟩
  · exact RestrictLeCalculus.RestrictLe.trans h.le (h.N_eq.symm ▸ h'.le)
  · exact RestrictLeCalculus.RestrictLe.trans (h.N_eq.symm ▸ h'.ge) h.ge

private theorem restrict_equiv_history {M L : MarkedIdeal n X}
    (hM : M.IsWellFormed) (hL : L.IsWellFormed) (h : MarkedIdeal.RestrictEquiv M L)
    (S : BlowupTower X Y) (hS : IsGeoTestTower L S) :
    IsGeoTestTower M S ∧ MarkedIdeal.RestrictEquiv (geoTransformAlong M S) (geoTransformAlong L S) := by
  have hTest := ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv h
    hM.isClosedSubmanifold_N.1 hM.isCoherent hL.isCoherent).2 S).1.mpr hS
  refine ⟨hTest,?_⟩
  cases S with
  | refl => exact h
  | step S C π hπ =>
    have hEq := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq
      h hM.isClosedSubmanifold_N.1 hM.isCoherent hL.isCoherent S C π hπ
    rw [←hEq]
    exact MarkedIdeal.RestrictEquiv.refl
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (.step S C π hπ) hTest).isCoherent

private theorem forward_append (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {profile : Fin old.length → ℕ} {q t : ℕ}
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (S : BlowupTower Z V)
    (hR : Forward N old born profile q t T R)
    (hS : Forward N old born profile q t (T.append R) S) :
    Forward N old born profile q t T (R.append S) := by
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense
    (T.append R) hR.1.1 hR.1.2.1
  refine ⟨?_,?_,?_⟩
  · rw [←BlowupTower.append_assoc]
    exact hS.1
  · intro z hz hzq
    rw [←BlowupTower.append_assoc] at hz hzq
    have hTopS := hS.2.1 z hz hzq
    have hTopR := hR.2.1 (S.proj z) hTopS.1 hTopS.2
    rw [BlowupTower.proj_append]
    exact hTopR
  · intro z hz
    rw [←BlowupTower.append_assoc] at hz ⊢
    rw [BlowupTower.proj_append]
    exact (hS.2.2 z hz).trans
      (hR.2.2 (S.proj z) (carrier_append_maps (T.append R) S hRec.1.1 hz))

private theorem forward_end {N : Set X} {old born : List (Set X)}
    {profile : Fin old.length → ℕ} {q t : ℕ} (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (h : ∀ k : ℕ,Forward N old born profile q t T (BlowupTowerSplit.head R k)) :
    Forward N old born profile q t T R := by
  have he := h 0
  change Forward N old born profile q t T (BlowupTowerSplit.split R 0).2.1 at he
  rw [StepOneEmptyPrefix.split_zero R] at he
  exact he

private theorem prefix_forward_append (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {profile : Fin old.length → ℕ} {q t : ℕ}
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (S : BlowupTower Z V)
    (hR : ∀ k : ℕ,Forward N old born profile q t T (BlowupTowerSplit.head R k))
    (hS : ∀ k : ℕ,Forward N old born profile q t (T.append R) (BlowupTowerSplit.head S k)) :
    ∀ k : ℕ,Forward N old born profile q t T (BlowupTowerSplit.head (R.append S) k) := by
  intro k
  by_cases hk : k ≤ S.length
  · have hs := StepOneEmptyPrefix.split_append_of_le R S k hk
    change Forward N old born profile q t T (BlowupTowerSplit.split (R.append S) k).2.1
    rw [hs]
    exact forward_append hn hN hE hTr hdense T R (BlowupTowerSplit.head S k)
      (forward_end T R hR) (hS k)
  · have hs := HironakaOriginalCrossingLowerHistory.split_append_above_tail R S k (by omega)
    change Forward N old born profile q t T (BlowupTowerSplit.split (R.append S) k).2.1
    rw [hs]
    exact hR (k-S.length)

private def inactiveIndices {r : ℕ} (profile : Fin r → ℕ) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter fun i => profile i=0

private theorem inactive_subset_indices (N : Set X) (old born : List (Set X))
    (profile : Fin old.length → ℕ) (T : BlowupTower X Y) (z : Y) :
    retainedInactiveRows N old born profile T z ⊆ inactiveIndices profile := by
  classical
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1⟩

private def Erased (N : Set X) (old born : List (Set X)) (profile : Fin old.length → ℕ)
    (q : ℕ) (T : BlowupTower X Y) (P : Finset (Fin old.length)) : Prop :=
  ∀ z ∈ (geoTransformAlong (geometricTemplate N born) T).N,
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) T).N
      (retainedProductMarked N old born q T).ideal z=q →
    ¬P ⊆ retainedInactiveRows N old born profile T z

private theorem erased_forward {N : Set X} {old born : List (Set X)}
    {profile : Fin old.length → ℕ} {q t : ℕ} (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (hR : Forward N old born profile q t T R) {P : Finset (Fin old.length)}
    (hErased : Erased N old born profile q T P) : Erased N old born profile q (T.append R) P := by
  intro z hz hzq hMask
  have hTop := hR.2.1 z hz hzq
  exact hErased _ hTop.1 hTop.2 (hMask.trans (hR.2.2 z hz))

private def Folded (N : Set X) (old born : List (Set X)) (profile : Fin old.length → ℕ)
    (q t : ℕ) (T : BlowupTower X Y) (F : Finset (Finset (Fin old.length))) (R : BlowupTower Y Z) : Prop :=
  (∀ k : ℕ,Forward N old born profile q t T (BlowupTowerSplit.head R k)) ∧
    ∀ P ∈ F,Erased N old born profile q (T.append R) P

private theorem folded_insert (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {profile : Fin old.length → ℕ} {q t : ℕ}
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (S : BlowupTower Z V)
    {F : Finset (Finset (Fin old.length))} {P : Finset (Fin old.length)}
    (hR : Folded N old born profile q t T F R)
    (hS : ∀ k : ℕ,Forward N old born profile q t (T.append R) (BlowupTowerSplit.head S k))
    (hErased : Erased N old born profile q ((T.append R).append S) P) :
    Folded N old born profile q t T (insert P F) (R.append S) := by
  refine ⟨prefix_forward_append hn hN hE hTr hdense T R S hR.1 hS,?_⟩
  intro P0 hP0
  rcases Finset.mem_insert.mp hP0 with hEq | hOld
  · rw [hEq,←BlowupTower.append_assoc]
    exact hErased
  · rw [←BlowupTower.append_assoc]
    exact erased_forward (T.append R) S (forward_end (T.append R) S hS) (hR.2 P0 hOld)

private theorem mask_block_at (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q t : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (T : BlowupTower X Y) (hStart : At N old born profile q t T)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0) (hCard : P.card=t) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (∀ k : ℕ,Forward N old born profile q t T (BlowupTowerSplit.head R k)) ∧
      Erased N old born profile q (T.append R) P := by
  classical
  let A := geoTransformAlong (geometricTemplate N born) T
  let O := old.map (strictAlong T)
  let e := currentIndex old T
  let pCur : Fin O.length → ℕ := fun j => profile (e.symm j)
  let PCur := P.map e.toEmbedding
  rcases hStart with ⟨hT,hFull,hSharp,hRowsT,hEquiT,hProdT,hProdEqT,hCapT⟩
  have hStart : At N old born profile q t T := ⟨hT,hFull,hSharp,hRowsT,hEquiT,hProdT,hProdEqT,hCapT⟩
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense T hT hFull
  have hInputs := current_inputs hn hN hE hTr hdense profile q t hsum hOrd hCompact hCount T hStart
  have hSumCur : ∑ j,pCur j=q := (Fintype.sum_equiv e.symm pCur profile (fun _ => rfl)).trans hsum
  have hPCur : ∀ j ∈ PCur,pCur j=0 := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    change profile (e.symm (e i))=0
    rw [e.symm_apply_apply]
    exact hP i hi
  have hCanonT : retainedProductMarked N old born q T=canonicalProductMarked A.N O A.E q :=
    retainedProductMarked_eq_canonical hn hN hE hTr hdense q T hT hFull
  have hInactiveT (z : Y) : inactiveCanonicalRows A.N O A.E pCur z=
      (retainedInactiveRows N old born profile T z).map e.toEmbedding :=
    (inactive_append N old born profile T (.refl : BlowupTower Y Y) z).symm
  have hBoundCur : ∀ z ∈ A.N,ordinaryTraceOrder A.N (canonicalProductMarked A.N O A.E q).ideal z=q →
      (inactiveCanonicalRows A.N O A.E pCur z).card ≤ PCur.card := by
    intro z hz hzq
    have hzq' : ordinaryTraceOrder A.N (retainedProductMarked N old born q T).ideal z=q := by
      rw [hCanonT]
      exact hzq
    change (inactiveCanonicalRows A.N O A.E pCur z).card ≤ (P.map e.toEmbedding).card
    rw [hInactiveT,Finset.card_map,Finset.card_map,hCard]
    exact hCapT z hz hzq'
  obtain ⟨Z,R,_hCanonical,_hResolution,_hEquiR,_hFootprint,hHeads,hErase⟩ :=
    exists_actual_retained_boundary_joint_mask_block hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1
      pCur q hq hSumCur hInputs.1 hInputs.2.1 hInputs.2.2 PCur hPCur hBoundCur
  have hTemplate : A=geometricTemplate A.N A.E :=
    (current_geometry_append N born T (.refl : BlowupTower Y Y)).symm
  have hFullTemplate : geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) T=
      geometricTemplate (univ : Set Y) (O ++ A.E) := by
    rw [template_current,strict_univ,retained_born_full_boundary_ordered_dictionary N old born T]
  have hp0 := product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hpT := product_geometry hn hN hE hTr hdense q T hT
  have hWF0 : (canonicalProductMarked N old born q).IsWellFormed :=
    ⟨hN,hp0.1,isSNCDivisor_of_sublist hE (List.sublist_append_right _ _),hTr⟩
  have hWFT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF0 T hProdT
  have hcCur : (canonicalProductMarked A.N O A.E q).ideal.IsCoherent := by
    rw [←hCanonT]
    exact hpT.1
  have hWFCur : (canonicalProductMarked A.N O A.E q).IsWellFormed :=
    ⟨hRec.1,hcCur,isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_right _ _),hRec.2.2.1⟩
  have hEqCur : MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) T)
      (canonicalProductMarked A.N O A.E q) := by
    rw [←hCanonT]
    exact hProdEqT
  refine ⟨Z,R,?_,?_⟩
  · intro k
    let S := BlowupTowerSplit.head R k
    obtain ⟨hCarrierS,hFullS,hSharpS,_hOverS,hRowsS,_hCountS,hEquiS,hProdS,hProdEqS,_hFactorsS,hTopS,hActS⟩ := hHeads k
    have hGeomS := current_geometry_append N born T S
    have hCarrierTS : IsGeoTestTower (geometricTemplate N born) (T.append S) := by
      apply (isGeoTestTower_append_iff _ T S).mpr
      refine ⟨hT,?_⟩
      change IsGeoTestTower A S
      rw [hTemplate]
      exact hCarrierS
    have hFullTS : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) (T.append S) := by
      apply (isGeoTestTower_append_iff _ T S).mpr
      exact ⟨hFull,hFullTemplate.symm ▸ hFullS⟩
    have hSharpTS : CurrentSharpCentres N (old ++ born) (T.append S) := by
      apply currentSharp_append N (old ++ born) T S hSharp
      rw [retained_born_full_boundary_ordered_dictionary N old born T]
      simpa only [N_geoTransformAlong,geometricTemplate] using hSharpS
    have hRowsTS : ∀ z ∈ (geoTransformAlong (geometricTemplate N born) (T.append S)).N,
        ∀ i,ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) (T.append S)).N
          (chronologicalMarked (retainedResidualMarked N old born i) (T.append S)).ideal z ≤
            ordinaryTraceOrder N (oldResidualPart N old born i) ((T.append S).proj z) := by
      intro z hz i
      have hzLocal : z ∈ (geoTransformAlong (geometricTemplate A.N A.E) S).N := by
        rw [hGeomS]
        exact hz
      have h := hRowsS z hzLocal (e i)
      rw [row_append hn hN hE hTr hdense T hT hFull S i,
        current_row hn hN hE hTr hdense T hT hFull i,hGeomS] at h
      rw [BlowupTower.proj_append]
      exact h.trans (hRowsT _ (carrier_append_maps T S hRec.1.1 hz) i)
    obtain ⟨hNativeS,hEqNativeS⟩ := restrict_equiv_history hWFT hWFCur hEqCur S hProdS
    have hProdTS : IsGeoTestTower (canonicalProductMarked N old born q) (T.append S) :=
      (isGeoTestTower_append_iff _ T S).mpr ⟨hProdT,hNativeS⟩
    have hEqTS : MarkedIdeal.RestrictEquiv
        (geoTransformAlong (canonicalProductMarked N old born q) (T.append S))
        (retainedProductMarked N old born q (T.append S)) := by
      rw [geoTransformAlong_append]
      have h := restrict_equiv_trans hEqNativeS hProdEqS
      rw [product_append hn hN hE hTr hdense q T hT hFull S] at h
      exact h
    have hLocalTop {z : _} (hz : z ∈ (geoTransformAlong (geometricTemplate N born) (T.append S)).N)
        (hzq : ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) (T.append S)).N
          (retainedProductMarked N old born q (T.append S)).ideal z=q) :
        z ∈ (geoTransformAlong (geometricTemplate A.N A.E) S).N ∧
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate A.N A.E) S).N
            (retainedProductMarked A.N O A.E q S).ideal z=q := by
      rw [hGeomS,product_append hn hN hE hTr hdense q T hT hFull S]
      exact ⟨hz,hzq⟩
    refine ⟨⟨hCarrierTS,hFullTS,hSharpTS,hRowsTS,
      equimultiple_append hn hN hE hTr hdense q T hT hFull S hEquiT hEquiS,hProdTS,hEqTS,?_⟩,?_,?_⟩
    · intro z hz hzq
      have hLocal := hLocalTop hz hzq
      have hCap := (hTopS z hLocal.1 hLocal.2).2.2.2
      have hMap := congrArg Finset.card (inactive_append N old born profile T S z)
      simpa only [Finset.card_map] using hMap.trans_le (hCap.trans_eq (by simp only [PCur,Finset.card_map,hCard]))
    · intro z hz hzq
      have hLocal := hLocalTop hz hzq
      have hTop := hTopS z hLocal.1 hLocal.2
      have hqSource := hTop.2.1
      rw [←hCanonT] at hqSource
      exact ⟨hTop.1,hqSource⟩
    · intro z hz i hi
      have hzLocal : z ∈ (geoTransformAlong (geometricTemplate A.N A.E) S).N := by rw [hGeomS];exact hz
      have hiLocal : e i ∈ retainedInactiveRows A.N O A.E pCur S z := by
        rw [←inactive_append N old born profile T S z]
        exact Finset.mem_map.mpr ⟨i,hi,rfl⟩
      have hiSource := hActS z hzLocal hiLocal
      rw [hInactiveT] at hiSource
      obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hiSource
      have hji' : j=i := e.injective hji
      rwa [hji'] at hj
  · intro z hz hzq hMask
    have hzLocal : z ∈ (geoTransformAlong (geometricTemplate A.N A.E) R).N := by
      rw [current_geometry_append]
      exact hz
    have hzqLocal : ordinaryTraceOrder (geoTransformAlong (geometricTemplate A.N A.E) R).N
        (retainedProductMarked A.N O A.E q R).ideal z=q := by
      rw [current_geometry_append,product_append hn hN hE hTr hdense q T hT hFull R]
      exact hzq
    obtain ⟨j,hj,hUnit⟩ := hErase z hzLocal hzqLocal
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    change (retainedFactorMarked A.N O A.E R (e i)).ideal.mem z 1 at hUnit
    rw [factor_append] at hUnit
    exact (Finset.mem_filter.mp (hMask hi)).2.2 hUnit

private theorem all_masks_drop (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q t : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (T : BlowupTower X Y) (hStart : At N old born profile q t T) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (∀ k : ℕ,Forward N old born profile q t T (BlowupTowerSplit.head R k)) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate N born) (T.append R)).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) (T.append R)).N
          (retainedProductMarked N old born q (T.append R)).ideal z=q →
        (retainedInactiveRows N old born profile (T.append R) z).card < t := by
  classical
  have fold (F : Finset (Finset (Fin old.length))) :
      (∀ P ∈ F,P ⊆ inactiveIndices profile ∧ P.card=t) →
      ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),Folded N old born profile q t T F R := by
    induction F using Finset.induction_on with
    | empty =>
      intro _hF
      refine ⟨Y,.refl,?_,?_⟩
      · intro k
        cases k <;> exact forward_refl T hStart
      · intro P hP
        exact (Finset.notMem_empty P hP).elim
    | @insert P F _hPF ih =>
      intro hF
      obtain ⟨Z,R,hR⟩ := ih (fun P0 hP0 => hF P0 (Finset.mem_insert_of_mem hP0))
      obtain ⟨hPsub,hCard⟩ := hF P (Finset.mem_insert_self P F)
      have hPzero : ∀ i ∈ P,profile i=0 := fun i hi => (Finset.mem_filter.mp (hPsub hi)).2
      have hREnd := forward_end T R hR.1
      obtain ⟨V,S,hS,hErase⟩ := mask_block_at hn hN hE hTr hdense profile q t hq hsum
        hOrd hCompact hCount (T.append R) hREnd.1 P hPzero hCard
      exact ⟨V,R.append S,folded_insert hn hN hE hTr hdense T R S hR hS hErase⟩
  let All := (inactiveIndices profile).powersetCard t
  obtain ⟨Z,R,hR⟩ := fold All (fun P hP => Finset.mem_powersetCard.mp hP)
  have hEnd := forward_end T R hR.1
  rcases hEnd.1 with ⟨_hT,_hFull,_hSharp,_hRows,_hEqui,_hProd,_hEq,hCap⟩
  refine ⟨Z,R,hR.1,?_⟩
  intro z hz hzq
  apply lt_of_le_of_ne (hCap z hz hzq)
  intro hEq
  have hMem : retainedInactiveRows N old born profile (T.append R) z ∈ All :=
    Finset.mem_powersetCard.mpr ⟨inactive_subset_indices N old born profile (T.append R) z,hEq⟩
  exact hR.2 _ hMem z hz hzq (Finset.Subset.refl _)

private theorem descend_inactive_count (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q) (t : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),At N old born profile q t T →
      ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
        (∀ k : ℕ,Forward N old born profile q t T (BlowupTowerSplit.head R k)) ∧
        At N old born profile q 0 (T.append R) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro Y T hAt
    by_cases hLow : t=0
    · subst t
      refine ⟨Y,.refl,?_,hAt⟩
      intro k
      cases k <;> exact forward_refl T hAt
    · obtain ⟨Z,R,hR,hDrop⟩ := all_masks_drop hn hN hE hTr hdense profile q t hq hsum
        hOrd hCompact hCount T hAt
      rcases (forward_end T R hR).1 with ⟨hT,hFull,hSharp,hRows,hEqui,hProd,hEq,_hCap⟩
      have hLower : At N old born profile q (t-1) (T.append R) := by
        refine ⟨hT,hFull,hSharp,hRows,hEqui,hProd,hEq,?_⟩
        intro z hz hzq
        have h := hDrop z hz hzq
        omega
      obtain ⟨V,S,hS,hEnd⟩ := ih (t-1) (by omega) (T.append R) hLower
      refine ⟨V,R.append S,?_,?_⟩
      · exact prefix_forward_append hn hN hE hTr hdense T R S hR
          (fun k => forward_mono (hS k) (Nat.sub_le t 1))
      · rw [←BlowupTower.append_assoc]
        exact hEnd

private theorem profile_exit (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower X Z),
      (∀ k : ℕ,Forward N old born profile q (inactiveIndices profile).card
        (.refl : BlowupTower X X) (BlowupTowerSplit.head R k)) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate N born) R).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) R).N
          (retainedProductMarked N old born q R).ideal z < q := by
  classical
  let t := (inactiveIndices profile).card
  have hAuto : ∀ z ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal z=q →
      (inactiveCanonicalRows N old born profile z).card ≤ t := by
    intro z _hz _hzq
    exact Finset.card_le_card (inactive_subset_indices N old born profile (.refl : BlowupTower X X) z)
  have hInitial := at_refl hn hN hE hTr hdense profile q t hAuto
  obtain ⟨Y,R,hR,hZero⟩ := descend_inactive_count hn hN hE hTr hdense profile q hq hsum
    hOrd hCompact hCount t (.refl : BlowupTower X X) hInitial
  have hZero' : At N old born profile q 0 R := by simpa only [BlowupTower.refl_append] using hZero
  obtain ⟨Z,S,hS,hErased⟩ := mask_block_at hn hN hE hTr hdense profile q 0 hq hsum
    hOrd hCompact hCount R hZero' ∅ (fun i hi => (Finset.notMem_empty i hi).elim) rfl
  have hR' : ∀ k : ℕ,Forward N old born profile q t (.refl : BlowupTower X X) (BlowupTowerSplit.head R k) := hR
  have hS' : ∀ k : ℕ,Forward N old born profile q t
      ((.refl : BlowupTower X X).append R) (BlowupTowerSplit.head S k) := by
    intro k
    simpa only [BlowupTower.refl_append] using forward_mono (hS k) (Nat.zero_le t)
  have hHeads := prefix_forward_append hn hN hE hTr hdense (.refl : BlowupTower X X) R S hR' hS'
  have hEnd : At N old born profile q t (R.append S) := by
    simpa only [BlowupTower.refl_append] using (forward_end (.refl : BlowupTower X X) (R.append S) hHeads).1
  have hp := product_geometry hn hN hE hTr hdense q (R.append S) hEnd.1
  refine ⟨Z,R.append S,hHeads,?_⟩
  intro z hz
  have hLe : ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) (R.append S)).N
      (retainedProductMarked N old born q (R.append S)).ideal z ≤ q := by
    rw [hp.2.2.2 z hz,←hsum]
    apply Finset.sum_le_sum
    intro i _hi
    exact (hEnd.2.2.2.1 z hz i).trans (hOrd _ (carrier_projects hN.1 born (R.append S) hz) i)
  apply lt_of_le_of_ne hLe
  intro hzq
  exact hErased z hz hzq (Finset.empty_subset _)

/-- ALL original inactive masks are actually folded.  Persistence uses the
derived genuine q-top projection AND original-index inactive activity.
The same actual chronological rows and entire retained born list survive. -/
theorem exists_actual_retained_boundary_all_masks_drop (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (t : ℕ) (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ t) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower X Z),
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let A := geoTransformAlong (geometricTemplate N born) Q
        IsGeoTestTower (geometricTemplate N born) Q ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) Q ∧
        CurrentSharpCentres N (old ++ born) Q ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) N (old ++ born)) Q ∧
        (∀ z ∈ A.N,∀ i,ordinaryTraceOrder A.N
          (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal z ≤
            ordinaryTraceOrder N (oldResidualPart N old born i) (Q.proj z)) ∧
        (∀ z,actualDistinctProperCount (fun i : Fin old.length =>
          (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal) z ≤
            actualDistinctProperCount (oldResidualPart N old born) (Q.proj z)) ∧
        IsRetainedProductEquimultiple N old born q Q ∧
        IsGeoTestTower (canonicalProductMarked N old born q) Q ∧
        MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) Q)
          (retainedProductMarked N old born q Q) ∧
        (∀ z ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q Q).ideal z=q →
          Q.proj z ∈ N ∧ ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (Q.proj z)=q) ∧
        ∀ z ∈ A.N,retainedInactiveRows N old born profile Q z ⊆
          inactiveCanonicalRows N old born profile (Q.proj z)) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate N born) R).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) R).N
          (retainedProductMarked N old born q R).ideal z=q →
        (retainedInactiveRows N old born profile R z).card < t := by
  have hStart := at_refl hn hN hE hTr hdense profile q t hBound
  obtain ⟨Z,R,hHeads,hDrop⟩ := all_masks_drop hn hN hE hTr hdense profile q t hq hsum
    hOrd hCompact hCount (.refl : BlowupTower X X) hStart
  refine ⟨Z,R,?_,?_⟩
  · intro k
    let Q := BlowupTowerSplit.head R k
    have hF := hHeads k
    simp only [Forward,BlowupTower.refl_append] at hF
    rcases hF with ⟨⟨hCarrier,hFull,hSharp,hRows,hEqui,hProd,hEq,_hCap⟩,hTop,hActivity⟩
    refine ⟨hCarrier,hFull,hSharp,(currentSharpCentres_original_footprint hN.1 hE.1 Q hSharp).2,
      hRows,(fun z => count_nonincrease N old born Q z),hEqui,hProd,hEq,hTop,hActivity⟩
  · simpa only [BlowupTower.refl_append] using hDrop

/-- A genuine compact TRUE-defect profile window is resolved by internally
folding every original inactive mask, descending its actual count to zero,
then taking the actual empty-mask q-exit block.  No initial count bound,
future state, terminal tower or descending measure is supplied. -/
theorem exists_actual_retained_boundary_profile_q_exit (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower X Z),
      IsGeoTestTower (geometricTemplate N born) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R ∧
      CurrentSharpCentres N (old ++ born) R ∧
      IsGeoResolution (canonicalProductMarked N old born q) R ∧
      RestrictEmptyTower.CentresOver (canonicalProductMarked N old born q).cosupp R ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let A := geoTransformAlong (geometricTemplate N born) Q
        IsGeoTestTower (geometricTemplate N born) Q ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) Q ∧
        CurrentSharpCentres N (old ++ born) Q ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) N (old ++ born)) Q ∧
        (∀ z ∈ A.N,∀ i,ordinaryTraceOrder A.N
          (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal z ≤
            ordinaryTraceOrder N (oldResidualPart N old born i) (Q.proj z)) ∧
        (∀ z,actualDistinctProperCount (fun i : Fin old.length =>
          (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal) z ≤
            actualDistinctProperCount (oldResidualPart N old born) (Q.proj z)) ∧
        IsRetainedProductEquimultiple N old born q Q ∧
        IsGeoTestTower (canonicalProductMarked N old born q) Q ∧
        MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) Q)
          (retainedProductMarked N old born q Q) ∧
        (∀ z ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q Q).ideal z=q →
          Q.proj z ∈ N ∧ ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (Q.proj z)=q) ∧
        ∀ z ∈ A.N,retainedInactiveRows N old born profile Q z ⊆
          inactiveCanonicalRows N old born profile (Q.proj z)) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate N born) R).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) R).N
          (retainedProductMarked N old born q R).ideal z < q := by
  obtain ⟨Z,R,hHeads,hExit⟩ := profile_exit hn hN hE hTr hdense profile q hq hsum hOrd hCompact hCount
  have hEnd : At N old born profile q (inactiveIndices profile).card R := by
    simpa only [BlowupTower.refl_append] using (forward_end (.refl : BlowupTower X X) R hHeads).1
  rcases hEnd with ⟨hCarrierR,hFullR,hSharpR,_hRowsR,_hEquiR,hProdR,hEqR,_hCapR⟩
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense R hCarrierR hFullR
  have hp := product_geometry hn hN hE hTr hdense q R hCarrierR
  have hp0 := product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hEmpty : (geoTransformAlong (canonicalProductMarked N old born q) R).cosupp=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rw [hEqR.cosupp_eq] at hz
    have hzN := (retainedProductMarked N old born q R).cosupp_subset_N hz
    have hGe := (ordinaryTraceOrder_cosupport_iff hRec.1 hp.1 hp.2.1 hzN q).mp hz
    exact (not_le_of_gt (hExit z hzN)) hGe
  have hOver := HironakaAdmissibleSequence.centresOver_cosupp
    (canonicalProductMarked N old born q) hN hp0.1 R hProdR
  refine ⟨Z,R,hCarrierR,hFullR,hSharpR,⟨hProdR,hEmpty⟩,hOver,?_,hExit⟩
  intro k
  let Q := BlowupTowerSplit.head R k
  have hF := hHeads k
  simp only [Forward,BlowupTower.refl_append] at hF
  rcases hF with ⟨⟨hCarrier,hFull,hSharp,hRows,hEqui,hProd,hEq,_hCap⟩,hTop,hActivity⟩
  exact ⟨hCarrier,hFull,hSharp,(currentSharpCentres_original_footprint hN.1 hE.1 Q hSharp).2,
    hRows,(fun z => count_nonincrease N old born Q z),hEqui,hProd,hEq,hTop,hActivity⟩

end
end Hironaka.HironakaActualRetainedBoundaryProfileExit
