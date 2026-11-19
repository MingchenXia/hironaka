import Hironaka.Resolution.HironakaG3BoundaryContainedOriginalGlobalLift
import Hironaka.Resolution.HironakaDisjointEmbeddedBoundaryLift
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CoupledNativeGeometry
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsInvariance SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3ControlledHistorySubsetTransport
  HironakaDisjointEmbeddedBoundaryLift
  HironakaActualNativeSectionRegularity

/-- Native normal crossings with the whole transformed boundary lift through
an actual coupled endpoint to the whole ambient transformed boundary. -/
theorem coupled_endpoint_native_normalCrossings {d t : ℕ} (hn : 0 < d+t)
    {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {U : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T U η)
    (D : Set Q) (hD : HasNormalCrossings d D (geoTransformAlong M T).E) :
    HasNormalCrossings (d+t) (η '' D) (geoTransformAlong (fullMarked B J) U).E := by
  obtain ⟨_hc,hr,_hI,_hNorm,hE,hTrans,F,hF,_hProj,_hIdeal,hBoundary⟩ := endpoint_of_coupledHistory h
  let := chartedSpace (Nat.le_add_right d t) hr
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
  have hMap : (geoTransformAlong (fullMarked B J) U).E.map
      (fun H => (Subtype.val : contactAlong N U → Y) ⁻¹' H) =
      (geoTransformAlong M T).E.map (F.symm ⁻¹' ·) := by
    rw [← hBoundary,List.map_map]
    apply List.map_congr_left
    intro H _hH
    ext p
    change p.val ∈ H ↔ η (F.symm p) ∈ H
    rw [← congrFun hF, F.apply_symm_apply]
  have hPre : HasNormalCrossings d (F.symm ⁻¹' D)
      ((geoTransformAlong M T).E.map (F.symm ⁻¹' ·)) := by
    exact hasNormalCrossings_preimage (MarkedIdealTowerTransport.pullsBackCoordinates F.symm) hD
  rw [← hMap] at hPre
  have hImg : (Subtype.val : contactAlong N U → Y) '' (F.symm ⁻¹' D) = η '' D := by
    rw [← hF]
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      refine ⟨F.symm p,hp,?_⟩
      exact congrArg Subtype.val (F.apply_symm_apply p)
    · rintro ⟨q,hq,rfl⟩
      refine ⟨F q,?_,rfl⟩
      change F.symm (F q) ∈ D
      rwa [F.symm_apply_apply]
  rw [← hImg]
  exact hasNormalCrossings_native_image hr hn hE hTrans _ hPre

/-- A closed smooth native subset has a closed smooth image under the
actual coupled endpoint embedding. -/
theorem coupled_endpoint_native_closedSubmanifold {d t : ℕ}
    {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {U : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T U η)
    (D : Set Q) (hD : IsClosedSubmanifold d D) :
    IsClosedSubmanifold (d+t) (η '' D) := by
  have hEnd := endpoint_of_coupledHistory h
  obtain ⟨hEmb,_hRange⟩ := endpoint_closedEmbedding_range hEnd
  obtain ⟨_hc,hr,_hI,_hNorm,_hE,_hTrans,F,hF,_hProj,_hIdeal,_hBoundary⟩ := hEnd
  let := chartedSpace (Nat.le_add_right d t) hr
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
  let D' : Set (contactAlong N U) := F.symm ⁻¹' D
  have hD' : IsClosedSubmanifold d D' :=
    (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff F.symm).mpr hD
  have hImg : (Subtype.val : contactAlong N U → Y) '' D' = η '' D := by
    rw [← hF]
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨F.symm p,hp,congrArg Subtype.val (F.apply_symm_apply p)⟩
    · rintro ⟨q,hq,rfl⟩
      refine ⟨F q,?_,rfl⟩
      change F.symm (F q) ∈ D
      rwa [F.symm_apply_apply]
  refine ⟨hEmb.isClosedMap D hD.1,?_⟩
  intro y hy
  rw [← hImg] at hy
  obtain ⟨p,hp,rfl⟩ := hy
  obtain ⟨r,hrp⟩ := hD'.2 p hp
  refine ⟨r,?_⟩
  rw [← hImg]
  exact (regularAtDim_native_image_iff (Nat.le_add_right d t) hr D' p r).mpr hrp

/-- The native dimension is unchanged by the actual coupled endpoint
embedding. -/
theorem coupled_endpoint_native_regularAtDim {d t : ℕ}
    {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {U : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T U η)
    (D : Set Q) (q : Q) (r : ℕ) (hq : RegularAtDim (n := d) D q r) :
    RegularAtDim (n := d+t) (η '' D) (η q) r := by
  obtain ⟨_hc,hr,_hI,_hNorm,_hE,_hTrans,F,hF,_hProj,_hIdeal,_hBoundary⟩ := endpoint_of_coupledHistory h
  let := chartedSpace (Nat.le_add_right d t) hr
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
  let D' : Set (contactAlong N U) := F.symm ⁻¹' D
  have hD' : RegularAtDim (n := d) D' (F q) r := by
    apply RegularAtDimTransport.regularAtDim_of_preimage (A := D) (A' := D') (z := F q) (O := Set.univ) F.symm.contMDiff
      (MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse F.symm.contMDiff F.contMDiff
        F.symm_apply_apply F.apply_symm_apply (F q)) isOpen_univ (mem_univ _) (fun _ _ => Iff.rfl)
    simpa only [F.symm_apply_apply] using hq
  have hImg : (Subtype.val : contactAlong N U → Y) '' D' = η '' D := by
    rw [← hF]
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨F.symm p,hp,congrArg Subtype.val (F.apply_symm_apply p)⟩
    · rintro ⟨p,hp,rfl⟩
      refine ⟨F p,?_,rfl⟩
      change F.symm (F p) ∈ D
      rwa [F.symm_apply_apply]
  rw [← hImg, ← congrFun hF q]
  exact (regularAtDim_native_image_iff (Nat.le_add_right d t) hr D' (F q) r).mpr hD'

/-- Smoothness and normal crossings of an intrinsic iterated strict
transform pass to the actual ambient iterated strict transform. -/
theorem coupled_strictAlong_geometry {d t : ℕ} (hn : 0 < d+t)
    {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {U : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T U η) (V : Set P)
    (hSmooth : IsClosedSubmanifold d (strictAlong T V))
    (hNC : HasNormalCrossings d (strictAlong T V) (geoTransformAlong M T).E) :
    IsClosedSubmanifold (d+t) (strictAlong U (ι '' V)) ∧
      HasNormalCrossings (d+t) (strictAlong U (ι '' V)) (geoTransformAlong (fullMarked B J) U).E := by
  rw [← strictAlong_image_of_coupledHistory h V]
  exact ⟨coupled_endpoint_native_closedSubmanifold h _ hSmooth,
    coupled_endpoint_native_normalCrossings hn h _ hNC⟩

/-- The dimension of the intrinsic iterated strict transform is retained
on every point of the ambient iterated strict transform. -/
theorem coupled_strictAlong_regularAtDim {d t : ℕ}
    {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {U : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T U η) (V : Set P) (r : ℕ)
    (hDim : ∀ q ∈ strictAlong T V, RegularAtDim (n := d) (strictAlong T V) q r) :
    ∀ y ∈ strictAlong U (ι '' V), RegularAtDim (n := d+t) (strictAlong U (ι '' V)) y r := by
  intro y hy
  have hImage := strictAlong_image_of_coupledHistory h V
  rw [← hImage] at hy ⊢
  obtain ⟨q,hq,rfl⟩ := hy
  exact coupled_endpoint_native_regularAtDim h _ q r (hDim q hq)

end
end Hironaka.HironakaG3CoupledNativeGeometry
