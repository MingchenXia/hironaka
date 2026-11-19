import Hironaka.Resolution.HironakaG34ProcessedMaskEquivariance
import Hironaka.Resolution.HironakaG4RecordedPartsOpen
import Hironaka.Resolution.HironakaActualProcessedSharpCleanup
import Hironaka.Resolution.HironakaG34NonPureLowDim

/-! The actual processed mask and its entire matrix on a restricted original
tower. Every row and born slot retains its chronological index. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ProcessedMaskRestriction

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings NormalCrossingsComparison HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedTowerResidualCompatibility HironakaG4RecordedPartsOpen
  HironakaActualProcessedMaskControlledSum HironakaActualProcessedMaskFiniteBlock
  HironakaG34ProcessedMaskEquivariance HironakaG4MonomialFamilyInvariant
  HironakaG4ZeroMaskGammaStep HironakaActualProcessedSharpCleanup
  HomogenizedGlueingTower RestrictEmptyTower RelativePrincipalizationSpan
  DivisorExponentAlong MonomialPartAlong RestrictedIdealExtension InvertibleIdealQuotient
  HironakaSharpActualFiniteChronologicalHistory

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The restricted literal tower retains the carrier and its full ordered
born list by preimage of the endpoint inclusion. -/
theorem original_carrier_template_restrict {W : Set X} (hW : IsClosedSubmanifold n W)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) :
    geoTransformAlong (geometricTemplate ((Subtype.val : U → X) ⁻¹' W) []) (restrict U T) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
        (geoTransformAlong (geometricTemplate W []) T) := by
  have h := geoTransformAlong_restrict U hW IdealWeightPowers.isCoherent_unitIdeal T hT
  rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := CMfd.of (n := n) U),
    List.map_nil] at h
  exact h

private theorem factor_pullback (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (U : Opens X) (i : Fin E.length) :
    let v := (Subtype.val : U → X)
    let EU := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EU.length := finCongr (List.length_map _).symm
    oldFactor (v ⁻¹' W) EU (restrict U T) (e i) =
      GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y) (oldFactor W E T i) := by
  intro v EU e
  let A := geoTransformAlong (geometricTemplate W []) T
  let O := E.map (strictAlong T)
  let j : Fin O.length := Fin.cast (List.length_map _).symm i
  have hGet : (E.map (strictAlong T)).get j = strictAlong T (E.get i) := by simp [O,j]
  have hGetU : EU.get (e i) = v ⁻¹' E.get i := by simp [EU,e]
  have hGeom := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hParts := (actual_old_parts_pullback_open hn hGeom.1 hGeom.2.1 hGeom.2.2.1
    hGeom.2.2.2.1 (openPreimage T U) j).1
  unfold oldFactor
  rw [original_carrier_template_restrict hW T hT U,hGetU,strictAlong_restrict]
  simpa only [oldMonomialPart,oldTraceIdeal,hGet,MarkedIdeal.pullback] using hParts

private theorem original_factor_coherent (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (i : Fin E.length) :
    (oldFactor W E T i).IsCoherent := by
  have hGeom := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  let oi : Fin (E.map (strictAlong T)).length := Fin.cast (List.length_map _).symm i
  have hGet : (E.map (strictAlong T)).get oi = strictAlong T (E.get i) := by simp [oi]
  have h := (actual_old_parts_geometry hn hGeom.1 hGeom.2.1 hGeom.2.2.1
    hGeom.2.2.2.1 oi).2.2.2.2.1
  simpa only [oldMonomialPart,oldTraceIdeal,hGet,oldFactor] using h

/-- Every literal old row and born column of the restricted factor
matrix comes from the identical chronological position in the original. -/
theorem processed_matrix_entries_restrict (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (U : Opens X) :
    let v := (Subtype.val : U → X)
    let EU := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EU.length := finCongr (List.length_map _).symm
    let R := restrict U T
    let A := geoTransformAlong (geometricTemplate W []) T
    let AU := geoTransformAlong (geometricTemplate (v ⁻¹' W) []) R
    ∃ c : Fin AU.E.length ≃ Fin A.E.length,
      (∀ j,(c j).val = j.val) ∧
      ∀ (z : openPreimage T U) i j,
        factorMatrix (v ⁻¹' W) EU R z (e i) j = factorMatrix W E T z.val i (c j) := by
  intro v EU e R
  let u := (Subtype.val : openPreimage T U → Y)
  let A := geoTransformAlong (geometricTemplate W []) T
  let AU := geoTransformAlong (geometricTemplate (v ⁻¹' W) []) R
  have hAU : AU = MarkedIdeal.pullback u A := original_carrier_template_restrict hW T hT U
  have hN : AU.N = u ⁻¹' A.N := congrArg MarkedIdeal.N hAU
  have hB : AU.E = A.E.map (u ⁻¹' ·) := congrArg MarkedIdeal.E hAU
  have hLen : AU.E.length = A.E.length := by rw [hB,List.length_map]
  let c : Fin AU.E.length ≃ Fin A.E.length := finCongr hLen
  have hFactor (i : Fin E.length) : oldFactor (v ⁻¹' W) EU R (e i) =
      GermIdeal.pullback (m := n) u (oldFactor W E T i) :=
    factor_pullback hn hW hE hdense T hT hFull U i
  have hc := original_factor_coherent hn hW hE hdense T hT hFull
  refine ⟨c,fun _ => rfl,?_⟩
  intro z i j
  let F := factorMatrix W E T z.val
  let FU := factorMatrix (v ⁻¹' W) EU R z
  change FU (e i) j = F i (c j)
  let M : MarkedIdeal n Y := ⟨A.N,A.E,oldFactor W E T i,1⟩
  have hj : j.val < (MarkedIdeal.pullback u M).E.length := by
    simpa [M,MarkedIdeal.pullback,c] using (c j).isLt
  have h := HironakaMonomialBlowup.divExpAlong_pullback_val_get M (hc i)
    (openPreimage T U) z hj (c j).isLt
  have hGet : AU.E.get j = u ⁻¹' A.E.get (c j) := by
    rw [List.get_of_eq hB]
    simp [c,List.get_eq_getElem]
  change divExpAlong n AU.N (oldFactor (v ⁻¹' W) EU R (e i)) (AU.E.get j) z =
    divExpAlong n A.N (oldFactor W E T i) (A.E.get (c j)) z.val
  rw [hN,hFactor,hGet]
  simpa [M,MarkedIdeal.pullback,u,c,List.get_eq_getElem] using h

/-- Reindex a finite span sum by the literal row bijection. -/
theorem mask_sum_map {ι κ : Type*} {D : ι → GermIdeal n Y} {D' : κ → GermIdeal n Y}
    (e : ι ↪ κ) (P : Finset ι) (hFactor : ∀ i,D' (e i) = D i) :
    maskSum D' (P.map e) = maskSum D P := by
  ext x f
  have hGen : (fun g => ∃ i ∈ P.map e,(D' i).mem x g) =
      (fun g => ∃ i ∈ P,(D i).mem x g) := by
    funext g
    apply propext
    constructor
    · rintro ⟨i,hi,hg⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      exact ⟨j,hj,(hFactor j) ▸ hg⟩
    · rintro ⟨i,hi,hg⟩
      exact ⟨e i,Finset.mem_map.mpr ⟨i,hi,rfl⟩,(hFactor i).symm ▸ hg⟩
  change IsInSpanAt (n := n) (fun g => ∃ i ∈ P.map e,(D' i).mem x g) x f ↔
    IsInSpanAt (n := n) (fun g => ∃ i ∈ P,(D i).mem x g) x f
  rw [hGen]

/-- Reindex a finite span along a literal equivalence. -/
theorem mask_sum_reindex {ι κ : Type*} {D : ι → GermIdeal n Y} {D' : κ → GermIdeal n Y}
    (e : ι ≃ κ) (P : Finset ι) (hFactor : ∀ i,D' (e i) = D i) :
    maskSum D' (P.map e.toEmbedding) = maskSum D P :=
  mask_sum_map e.toEmbedding P hFactor

/-- The actual mask and all canonical born exponents on the restricted
prefix. The old position bijection is exactly the literal list-map index. -/
theorem processed_mask_matrix_restrict (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (U : Opens X) :
    let v := (Subtype.val : U → X)
    let u := (Subtype.val : openPreimage T U → Y)
    let EU := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EU.length := finCongr (List.length_map _).symm
    let R := restrict U T
    (∀ P : Finset (Fin E.length),
      processedMaskMarked (v ⁻¹' W) EU R (P.map e.toEmbedding) =
        MarkedIdeal.pullback u (processedMaskMarked W E T P)) ∧
    ∀ z : openPreimage T U,
      (properRows (factorMatrix (v ⁻¹' W) EU R z)).map e.symm.toEmbedding =
        properRows (factorMatrix W E T z.val) ∧
      tauD (factorMatrix (v ⁻¹' W) EU R z) = tauD (factorMatrix W E T z.val) ∧
      nuOne (fun i => factorMatrix (v ⁻¹' W) EU R z (e i)) = nuOne (factorMatrix W E T z.val) := by
  intro v u EU e R
  let A := geoTransformAlong (geometricTemplate W []) T
  let AU := geoTransformAlong (geometricTemplate (v ⁻¹' W) []) R
  have hAU : AU = MarkedIdeal.pullback u A := original_carrier_template_restrict hW T hT U
  have hN : AU.N = u ⁻¹' A.N := congrArg MarkedIdeal.N hAU
  have hB : AU.E = A.E.map (u ⁻¹' ·) := congrArg MarkedIdeal.E hAU
  have hFactor (i : Fin E.length) : oldFactor (v ⁻¹' W) EU R (e i) =
      GermIdeal.pullback (m := n) u (oldFactor W E T i) :=
    factor_pullback hn hW hE hdense T hT hFull U i
  have hc := original_factor_coherent hn hW hE hdense T hT hFull
  obtain ⟨c,_hChronology,hEntry⟩ :=
    processed_matrix_entries_restrict hn hW hE hdense T hT hFull U
  constructor
  · intro P
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪 := processedMaskMarked (X := CMfd.of (n := n) U) (v ⁻¹' W) EU R (P.map e.toEmbedding))
      (𝔫 := MarkedIdeal.pullback u (processedMaskMarked W E T P)) ?_ ?_ ?_ rfl
    · exact hN
    · exact hB
    · let D := fun i : Fin E.length => oldFactor W E T i
      let DU := fun i : Fin EU.length => oldFactor (v ⁻¹' W) EU R i
      change maskSum DU (P.map e.toEmbedding) = GermIdeal.pullback (m := n) u (maskSum D P)
      have hu : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ u := contMDiff_subtype_val
      rw [pullback_maskSum (Y := CMfd.of (n := n) (openPreimage T U)) hu D
        (fun i _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)]
      exact mask_sum_reindex e P hFactor
  · intro z
    let F := factorMatrix W E T z.val
    let FU := factorMatrix (v ⁻¹' W) EU R z
    obtain ⟨hRows,hCount,hNu⟩ := column_equiv_invariants F (fun i => FU (e i)) c (hEntry z)
    have hRowsCast : (properRows FU).map e.symm.toEmbedding = properRows (fun i => FU (e i)) := by
      ext i
      constructor
      · intro hi
        obtain ⟨j,hj,hj'⟩ := Finset.mem_map.mp hi
        have he : j = e i := by simpa using congrArg e hj'
        subst j
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
      · intro hi
        refine Finset.mem_map.mpr ⟨e i,?_,e.symm_apply_apply i⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    exact ⟨hRowsCast.trans hRows,(tauD_row_equiv e FU).symm.trans hCount,hNu⟩

end
end Hironaka.HironakaG4ProcessedMaskRestriction
