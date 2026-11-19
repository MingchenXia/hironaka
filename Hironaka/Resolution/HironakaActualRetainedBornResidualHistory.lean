import Hironaka.Resolution.HironakaActualRetainedBornResidualSeed
import Hironaka.Resolution.HironakaActualCleanupDensityCompactness

/-! The canonical whole old residual on a genuine recorded history, retaining
the ENTIRE INITIAL born list and every subsequent born position. The actual
mixed residual step supplies the induction; principality and next-comparison
certificates are not premises.

Blueprint: `hironaka-actual-retained-born-residual-history-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualRetainedBornResidualHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  HironakaG4PreparedCentreCoordinates HironakaG4MixedOldResidualStep
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaActualRetainedBornResidualSeed HironakaActualCleanupDensityCompactness
  IdealWeightPowers
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Literal full boundary order retains the initial born entries inside the
carrier template's own list, followed by every true later birth. -/
theorem retained_born_full_boundary_ordered_dictionary (N : Set X)
    (old born : List (Set X)) :
    ∀{Y : CMfd.{u} n}(S : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate (univ : Set X) (old++born)) S).E=
        old.map (strictAlong S)++(geoTransformAlong (geometricTemplate N born) S).E
  | _,.refl => by
    change old++born=old.map (fun H : Set X=>H)++born
    simp
  | _,.step S C π hπ => by
    change (geoTransformAlong (geometricTemplate (univ : Set X) (old++born)) S).E.map
      (geoStrictTransform π C)++[π ⁻¹' C]=_
    rw [retained_born_full_boundary_ordered_dictionary N old born S,
      List.map_append,List.map_map,List.append_assoc]
    rfl

private theorem recorded_geometry {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (S : BlowupTower X Y)
    (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old++born)) S) :
    let A:=geoTransformAlong (geometricTemplate N born) S
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n (old.map (strictAlong S)++A.E) ∧
      IsTransverse n A.N A.E := by
  have hBorn:=isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hw : (geometricTemplate N born).IsWellFormed:=⟨hN,isCoherent_unitIdeal,hBorn,hTr⟩
  have hwS:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw S hS
  have hwFull : (geometricTemplate (univ : Set X) (old++born)).IsWellFormed:=
    ⟨⟨isClosed_univ,fun x _=>⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
      isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hSNC:=(MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwFull S hFull).isSNCDivisor
  rw [retained_born_full_boundary_ordered_dictionary N old born S] at hSNC
  exact ⟨hwS.isClosedSubmanifold_N,hSNC,hwS.isTransverse⟩

private theorem dense_diff_union {Z : Type*} [TopologicalSpace Z] {N D F : Set Z}
    (hD : IsClosed D) (hd : N⊆closure (N\D)) (hf : N⊆closure (N\F)) :
    N⊆closure (N\(D∪F)) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro U hU hxU
  obtain ⟨y,hyU,hyN,hyD⟩:=mem_closure_iff.mp (hd hx) U hU hxU
  obtain ⟨z,⟨hzU,hzD⟩,hzN,hzF⟩:=mem_closure_iff.mp (hf hyN)
    (U∩Dᶜ) (hU.inter hD.isOpen_compl) ⟨hyU,hyD⟩
  exact ⟨z,hzU,hzN,fun h=>h.elim hzD hzF⟩

private theorem dense_diff_list {Z : Type*} [TopologicalSpace Z] {N : Set Z}
    (L : List (Set Z)) (hC : ∀H∈L,IsClosed H)
    (hD : ∀H∈L,N⊆closure (N\H)) : N⊆closure (N\⋃H∈L,H) := by
  induction L with
  | nil => simpa using (subset_closure : N⊆closure N)
  | cons H L ih =>
    have hTail:=ih (fun K hK=>hC K (List.mem_cons_of_mem H hK))
      (fun K hK=>hD K (List.mem_cons_of_mem H hK))
    simpa only [List.mem_cons,Set.iUnion_iUnion_eq_or_left] using
      dense_diff_union (hC H (by simp)) (hD H (by simp)) hTail

private theorem full_density_of_actual_old_nonzero (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (S : BlowupTower X Y)
    (hN : IsClosedSubmanifold n (geoTransformAlong (geometricTemplate N born) S).N)
    (hSNC : IsSNCDivisor n
      (old.map (strictAlong S)++(geoTransformAlong (geometricTemplate N born) S).E))
    (hTr : IsTransverse n (geoTransformAlong (geometricTemplate N born) S).N
      (geoTransformAlong (geometricTemplate N born) S).E)
    (hnz : ∀i : Fin old.length,∀y∈(geoTransformAlong (geometricTemplate N born) S).N,
      IsNonzeroAlongAt (geoTransformAlong (geometricTemplate N born) S).N
        (restrictOn n (geoTransformAlong (geometricTemplate N born) S).N
          (vanishingIdeal (n:=n) (strictAlong S (old.get i)))) y) :
    let A:=geoTransformAlong (geometricTemplate N born) S
    A.N⊆closure (A.N\⋃H∈old.map (strictAlong S)++A.E,H) := by
  apply actual_cleanup_source_full_density hn hN hSNC hTr
  apply dense_diff_list (old.map (strictAlong S))
    (fun H hH=>hSNC.1 H (List.mem_append_left _ hH))
  intro H hH
  obtain ⟨H₀,hH₀,rfl⟩:=List.mem_map.mp hH
  obtain ⟨i,rfl⟩:=List.mem_iff_get.mp hH₀
  exact actual_density_of_nonzero_normalized_vanishing (hnz i)

private theorem recorded_density_and_residuals (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N⊆closure (N\⋃H∈old++born,H)) :
    ∀{Y : CMfd.{u} n}(S : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N born) S →
      IsGeoTestTower (geometricTemplate (univ : Set X) (old++born)) S →
      let A:=geoTransformAlong (geometricTemplate N born) S
      A.N⊆closure (A.N\⋃H∈old.map (strictAlong S)++A.E,H) ∧
        ∀i : Fin old.length,
          let I:=restrictOn n A.N (vanishingIdeal (n:=n) (strictAlong S (old.get i)))
          I.IsCoherent ∧ (∀y∈A.N,IsNonzeroAlongAt A.N I y) ∧
            nonmonomialPartAlong n A.N I A.E=
              (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
  | _,.refl,_hS,_hFull => by
    refine ⟨?_,fun i=>?_⟩
    · simpa [geometricTemplate,geoTransformAlong,strictAlong] using hdense
    · change (oldTraceIdeal N old i).IsCoherent ∧
        (∀y∈N,IsNonzeroAlongAt N (oldTraceIdeal N old i) y) ∧
        oldResidualPart N old born i=(retainedResidualMarked N old born i).ideal
      have hParts:=actual_old_parts_geometry hn hN hE hTr hdense i
      exact ⟨hParts.1,hParts.2.1,rfl⟩
  | _,.step S C π hπ,hS,hFull => by
    let A:=geoTransformAlong (geometricTemplate N born) S
    let O:=old.map (strictAlong S)
    let A':=geoTransformAlong (geometricTemplate N born) (.step S C π hπ)
    obtain ⟨hDense,hRows⟩:=recorded_density_and_residuals hn hN hE hTr hdense S hS.1 hFull.1
    obtain ⟨hNCur,hSNC,hTrCur⟩:=recorded_geometry hN hE hTr S hS.1 hFull.1
    have hCN : C⊆A.N:=hS.2.subset_N
    have hCNC : HasNormalCrossings n C (O++A.E):=by
      rw [←retained_born_full_boundary_ordered_dictionary N old born S]
      exact hFull.2.2.2
    have hRowsNew : ∀i : Fin old.length,
        let I:=restrictOn n A'.N
          (vanishingIdeal (n:=n) (strictAlong (.step S C π hπ) (old.get i)))
        I.IsCoherent ∧ (∀y∈A'.N,IsNonzeroAlongAt A'.N I y) ∧
          nonmonomialPartAlong n A'.N I A'.E=
            (chronologicalMarked (retainedResidualMarked N old born i) (.step S C π hπ)).ideal:=by
      intro i
      let j : Fin O.length:=⟨i.val,by simpa only [O,List.length_map] using i.isLt⟩
      have hGet : O.get j=strictAlong S (old.get i):=by simp [O,j]
      have hStep:=actual_mixed_old_residual_step hn hNCur hSNC hTrCur hDense j hπ hCN hCNC
      dsimp only at hStep
      simp only [oldResidualPart,oldTraceIdeal] at hStep
      rw [hGet,(hRows i).2.2] at hStep
      have hChronoN:=(chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) S).1
      change (chronologicalMarked (retainedResidualMarked N old born i) S).N=A.N at hChronoN
      have hChronoStep :
          (chronologicalMarked (retainedResidualMarked N old born i) (.step S C π hπ)).ideal=
            nextRelativeStrict A.N
              (chronologicalMarked (retainedResidualMarked N old born i) S).ideal C π:=by
        change nextRelativeStrict (chronologicalMarked (retainedResidualMarked N old born i) S).N
          (chronologicalMarked (retainedResidualMarked N old born i) S).ideal C π=_
        rw [hChronoN]
      rw [hChronoStep]
      exact hStep
    obtain ⟨hN',hSNC',hTr'⟩:=recorded_geometry hN hE hTr (.step S C π hπ) hS hFull
    have hDense':=full_density_of_actual_old_nonzero hn (.step S C π hπ)
      hN' hSNC' hTr' (fun i=>(hRowsNew i).2.1)
    exact ⟨hDense',hRowsNew⟩

/-- ONLY original geometry and two actual geometric tests produce the full
current geometry/density and WHOLE canonical-residual historical dictionary.
Every INITIAL born entry and every new born entry remains in the same A.E. -/
theorem actual_retained_born_recorded_residual_dictionary (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N⊆closure (N\⋃H∈old++born,H)) (S : BlowupTower X Y)
    (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old++born)) S) :
    let A:=geoTransformAlong (geometricTemplate N born) S
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n (old.map (strictAlong S)++A.E) ∧
      IsTransverse n A.N A.E ∧ A.N⊆closure (A.N\⋃H∈old.map (strictAlong S)++A.E,H) ∧
      ∀i : Fin old.length,
        let I:=restrictOn n A.N (vanishingIdeal (n:=n) (strictAlong S (old.get i)))
        let J:=(chronologicalMarked (retainedResidualMarked N old born i) S).ideal
        I.IsCoherent ∧ (∀y∈A.N,IsNonzeroAlongAt A.N I y) ∧
          nonmonomialPartAlong n A.N I A.E=J ∧
          I=restrictOn n A.N ((monomialPartAlong n A.N I A.E).mul J) := by
  let A:=geoTransformAlong (geometricTemplate N born) S
  obtain ⟨hNCur,hSNC,hTrCur⟩:=recorded_geometry hN hE hTr S hS hFull
  obtain ⟨hDense,hRows⟩:=recorded_density_and_residuals hn hN hE hTr hdense S hS hFull
  refine ⟨hNCur,hSNC,hTrCur,hDense,fun i=>?_⟩
  obtain ⟨hcI,hnzI,hNm⟩:=hRows i
  let j : Fin (old.map (strictAlong S)).length:=⟨i.val,by simpa only [List.length_map] using i.isLt⟩
  have hGet : (old.map (strictAlong S)).get j=strictAlong S (old.get i):=by simp [j]
  have hParts:=actual_old_parts_geometry hn hNCur hSNC hTrCur hDense j
  simp only [oldTraceIdeal,oldResidualPart,oldMonomialPart,hGet] at hParts
  obtain ⟨_hcI,_hnzI,_hcJ,_hnzJ,_hcD,_hnzD,_hMon,hFactor⟩:=hParts
  rw [hNm] at hFactor
  exact ⟨hcI,hnzI,hNm,hFactor⟩

end
end Hironaka.HironakaActualRetainedBornResidualHistory
