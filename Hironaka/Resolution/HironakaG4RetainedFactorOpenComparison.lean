import Hironaka.Resolution.HironakaG34NonPureLowDim
import Hironaka.Resolution.HironakaG34JointMaskEquivariance
import Hironaka.Resolution.HironakaActualRetainedBornResidualHistory

/-! The actual normalized old monomial factors and their unit germs
are invariant under the physical comparison with a literal open restriction. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedFactorOpenComparison
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison
  HironakaSharpActualFiniteChronologicalHistory HironakaActualRetainedBornResidualHistory
  HironakaActualRetainedBoundaryMaskBlock HironakaG34NonPureLowDim
  HironakaG34JointMaskEquivariance HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalDistinctDefect RelativePrincipalizationSpan
  HironakaG4CompactWholeMonomialMaskPhase GermIdealOrder

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The whole actual factor of each old position pulls back under the same
open tower comparison that carries the actual residual and product. -/
theorem actual_retained_factor_open_tower_iso (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e)
    (i : Fin old.length) :
    let f := (Subtype.val : openPreimage S U → Y) ∘ e
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let iU : Fin OU.length := Fin.cast (List.length_map _).symm i
    MarkedIdeal.pullback f (retainedFactorMarked N old born S i) =
      retainedFactorMarked ((Subtype.val : U → X) ⁻¹' N) OU BU R iU := by
  intro f OU BU iU
  let A := geoTransformAlong (geometricTemplate N born) S
  let AR := geoTransformAlong (geometricTemplate ((Subtype.val : U → X) ⁻¹' N) BU) R
  let O := old.map (strictAlong S)
  let j : Fin O.length := Fin.cast (List.length_map _).symm i
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  have hH := MonomialPart.isClosedSubmanifold_get hn
    (isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_left O A.E)) j
  have hGet : O.get j = strictAlong S (old.get i) := by simp [O,j]
  rw [hGet] at hH
  have hTuple := tuple_open_iso hN born U S hS R e he
  have hU : OU.get iU = (Subtype.val : U → X) ⁻¹' old.get i := by simp [OU,iU]
  have hOpen : HironakaBaseChange.IsOpenHoloEmbedding n f := ⟨openPreimage S U,e,fun _ => rfl⟩
  have hFactor := pullback_factorOf (Y := Z) (f := f) hOpen A.E hRec.1
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hH)
  change MarkedIdeal.pullback f (factorOf A.N (strictAlong S (old.get i)) A.E) =
    factorOf AR.N (strictAlong R (OU.get iU)) AR.E
  rw [hU,hTuple.1,hTuple.2.1,hTuple.2.2]
  exact hFactor


/-- A coherent ideal and its holomorphic pullback have the same unit
status at corresponding points. -/
theorem unit_mem_iff_of_coherent_pullback {J : GermIdeal n Y} {JU : GermIdeal n Z}
    {f : Z → Y} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hJC : J.IsCoherent) (hI : GermIdeal.pullback (m := n) f J = JU) (z : Z) :
    JU.mem z 1 ↔ J.mem (f z) 1 := by
  classical
  have hJUC : JU.IsCoherent := hI ▸ GermIdealPullbackCalculus.isCoherent_pullback hf hJC
  have hZero : JU.zeroLocus = f ⁻¹' J.zeroLocus := by
    rw [←hI]
    exact BlowupExceptionalDivisor.zeroLocus_pullback hf hJC
  have hProper {V : CMfd.{u} n} {I : GermIdeal n V} (hIC : I.IsCoherent) (x : V) :
      ¬I.mem x 1 ↔ x ∈ I.zeroLocus := by
    simpa only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and] using
      actual_proper_iff_zeroLocus (F := fun _ : Fin 1 => I) (fun _ => hIC) 0 x
  apply not_iff_not.mp
  rw [hProper hJUC,hProper hJC,hZero]
  rfl

/-- In particular, the actual retained factor is nonunit exactly at
the corresponding physical point of the full transformed carrier. -/
theorem actual_retained_factor_unit_open_tower_iso_iff (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower (CMfd.of (n := n) U) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) R (restrict U S) e)
    (i : Fin old.length) (z : Z) :
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let iU : Fin OU.length := Fin.cast (List.length_map _).symm i
    (retainedFactorMarked ((Subtype.val : U → X) ⁻¹' N) OU BU R iU).ideal.mem z 1 ↔
      (retainedFactorMarked N old born S i).ideal.mem (e z).val 1 := by
  classical
  intro OU BU iU
  let J := (retainedFactorMarked N old born S i).ideal
  let JU := (retainedFactorMarked ((Subtype.val : U → X) ⁻¹' N) OU BU R iU).ideal
  let f := (Subtype.val : openPreimage S U → Y) ∘ e
  have hMarked := actual_retained_factor_open_tower_iso hn hN hE hTr hdense U S hS hFull R e he i
  have hI : GermIdeal.pullback (m := n) f J = JU :=
    congrArg (fun M : MarkedIdeal n Z => M.ideal) hMarked
  let A := geoTransformAlong (geometricTemplate N born) S
  let O := old.map (strictAlong S)
  let j : Fin O.length := Fin.cast (List.length_map _).symm i
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  have hGet : O.get j = strictAlong S (old.get i) := by simp [O,j]
  have hJC : J.IsCoherent := by
    have h := (actual_old_parts_geometry hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 j).2.2.2.2.1
    change (oldMonomialPart A.N O A.E j).IsCoherent at h
    unfold oldMonomialPart oldTraceIdeal at h
    rw [hGet] at h
    exact h
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f :=
    contMDiff_subtype_val.comp e.contMDiff
  exact unit_mem_iff_of_coherent_pullback hf hJC hI z

/-- The actual marked test gives the zero-mark geometric test on the same
carrier and ordered boundary, with the same literal blowup tower. -/
theorem isGeoTestTower_geometricTemplate_of_actual_test (M : MarkedIdeal n X)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    IsGeoTestTower (geometricTemplate M.N M.E) T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    refine ⟨ih hT.1,hT.2.1,?_,?_⟩
    · rw [template_current]
      change C ⊆ cosupport n (strictAlong T M.N) (IdealWeightPowers.unitIdeal n _) 0
      rw [cosupport_zero (fun _ _ h => h),←N_geoTransformAlong M T]
      exact hT.2.subset_N
    · rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (show
        (geometricTemplate M.N M.E).E=M.E from rfl)]
      exact hT.2.2.2

end
end Hironaka.HironakaG4RetainedFactorOpenComparison
