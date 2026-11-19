import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Invariant.RestrictEmptyTower

/-! Genuine one-step and recorded-history footprints of literal sharp bad
loci. Complete source-first proof: hironaka-g4-sharp-bad-footprint.tex.
No monomial hypothesis, future selector or original footprint is supplied. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SharpBadFootprint

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings NormalCrossingsInvariance
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualFiniteChronologicalHistory
  HironakaG4CompactWholeMonomialMaskPhase HomogenizedGlueingTower MemberInterTowerAlong
  RestrictEmptyTower MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem normalCrossingsAt_strict_of_notMem {N : Set X} {E : List (Set X)}
    (hN : IsClosed N) (hE : ∀ H ∈ E,IsClosed H) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) {y : Y} (hy : π y ∉ C)
    (hNC : normalCrossingsAt (n := n) N E (π y)) :
    normalCrossingsAt (n := n) (geoStrictTransform π C N)
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) y := by
  let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hflat⟩,hcard⟩ := hNC
  let A : Option (Fin E'.length) → Set X := fun o =>
    o.elim N (fun i => if hi : i.val<E.length then E.get ⟨i.val,hi⟩ else C)
  let J : Option (Fin E'.length) → Finset (Fin n) := fun o =>
    o.elim S₀ (fun i => if hi : i.val<E.length then S ⟨i.val,hi⟩ else ∅)
  have hOld : IsCoordinateFamilyAt n A J (π y) := by
    refine ⟨Φ,hsrc,hzero,?_⟩
    rintro (_ | i) hi u hu huΦ
    · exact hflat none hi hu huΦ
    · by_cases hidx : i.val<E.length
      · simpa only [A,J,Option.elim,dif_pos hidx] using
          hflat (some ⟨i.val,hidx⟩)
            (by simpa only [A,Option.elim,dif_pos hidx] using hi) hu huΦ
      · exact False.elim (hy (by simpa only [A,Option.elim,dif_neg hidx] using hi))
  have hGetOld (i : Fin E'.length) (hi : i.val<E.length) :
      E'.get i=geoStrictTransform π C (E.get ⟨i.val,hi⟩) := by
    simp only [E',List.get_eq_getElem]
    rw [List.getElem_append_left (by simpa only [List.length_map] using hi)]
    simp only [List.getElem_map]
  have hGetLast (i : Fin E'.length) (hi : ¬i.val<E.length) : E'.get i=π ⁻¹' C := by
    have hlt : i.val<E.length+1 := by simpa [E'] using i.isLt
    have hv : i.val=E.length := by omega
    simp [E',List.get_eq_getElem,hv]
  have hOpen : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  have hDictionary : ∀ o : Option (Fin E'.length),∀ u ∈ π ⁻¹' Cᶜ,
      u ∈ o.elim (geoStrictTransform π C N) E'.get ↔ π u ∈ A o := by
    rintro (_ | i) u hu
    · exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN hu
    · change u ∈ E'.get i ↔ π u ∈ A (some i)
      by_cases hidx : i.val<E.length
      · rw [hGetOld i hidx]
        simpa only [A,Option.elim,dif_pos hidx] using
          mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
            (hE _ (List.get_mem E ⟨i.val,hidx⟩)) hu
      · rw [hGetLast i hidx]
        simp only [A,Option.elim,dif_neg hidx,Set.mem_preimage]
  have hNonexc : y ∉ exceptionalLocus n π :=
    fun h => hy (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  have hNew := isCoordinateFamilyAt_of_preimage hπ.contMDiff hNonexc hOpen hy hDictionary hOld
  refine ⟨S₀,fun i => if hi : i.val<E.length then S ⟨i.val,hi⟩ else ∅,hNew,?_⟩
  intro i hi
  by_cases hidx : i.val<E.length
  · have hi' : y ∈ geoStrictTransform π C (E.get ⟨i.val,hidx⟩) := by
      rwa [hGetOld i hidx] at hi
    have hOldMem := (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
      (hE _ (List.get_mem E ⟨i.val,hidx⟩)) hy).mp hi'
    simpa only [dif_pos hidx] using hcard ⟨i.val,hidx⟩ hOldMem
  · have hyC : π y ∈ C := by rwa [hGetLast i hidx] at hi
    exact False.elim (hy hyC)

/-- Genuine strict carrier/full boundary bad points lie over old bad points
or the actual centre, using only closed initial sets. -/
theorem originalSharpBadLocus_strict_subset_preimage_union {N : Set X} {E : List (Set X)}
    (hN : IsClosed N) (hE : ∀ H ∈ E,IsClosed H) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) :
    originalSharpBadLocus (n := n) (geoStrictTransform π C N)
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) ⊆
        π ⁻¹' (originalSharpBadLocus (n := n) N E ∪ C) := by
  intro y hy
  by_cases hyC : π y ∈ C
  · exact Or.inr hyC
  · refine Or.inl ⟨geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN hy.1,?_⟩
    intro hNC
    exact hy.2 (normalCrossingsAt_strict_of_notMem hN hE hπ hyC hNC)

private theorem boundary_closed_along (M : MarkedIdeal n X) (hE : ∀ H ∈ M.E,IsClosed H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),∀ H ∈ (geoTransformAlong M T).E,IsClosed H
  | _,.refl => hE
  | _,.step T C π hπ => by
    intro H hH
    change H ∈ (geoTransformAlong M T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
    rcases List.mem_append.mp hH with hOld | hBorn
    · obtain ⟨K,_hK,rfl⟩ := List.mem_map.mp hOld
      exact isClosed_closure
    · rw [List.mem_singleton.mp hBorn]
      exact hπ.1.1.preimage hπ.contMDiff.continuous

/-- The actual CURRENT condition on a fixed real history internally gives
both its current bad pullback and native INITIAL centre footprint. -/
theorem currentSharpCentres_original_footprint {N : Set X} {E : List (Set X)}
    (hN : IsClosed N) (hE : ∀ H ∈ E,IsClosed H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CurrentSharpCentres N E T →
      originalSharpBadLocus (n := n) (strictAlong T N)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E ⊆
            T.proj ⁻¹' originalSharpBadLocus (n := n) N E ∧
        CentresOver (originalSharpBadLocus (n := n) N E) T
  | _,.refl,_hSharp => ⟨fun _ h => h,trivial⟩
  | _,.step T C π hπ,hSharp => by
    obtain ⟨hBad,hOver⟩ := currentSharpCentres_original_footprint hN hE T hSharp.1
    have hCOver : C ⊆ T.proj ⁻¹' originalSharpBadLocus (n := n) N E := hSharp.2.trans hBad
    refine ⟨?_,⟨hOver,hCOver⟩⟩
    have hStep := originalSharpBadLocus_strict_subset_preimage_union
      (isClosed_strictAlong T hN)
      (boundary_closed_along (geometricTemplate (univ : Set X) E) hE T) hπ
    intro y hy
    have hUnion := hStep hy
    exact hBad (hUnion.elim id (fun hc => hSharp.2 hc))

end
end Hironaka.HironakaG4SharpBadFootprint
