import Hironaka.Resolution.HironakaG4AmbientUnitTemplate
import Hironaka.Resolution.HironakaG4FullTemplateProtection
import Hironaka.Resolution.HironakaG4WindowActualParts
import Hironaka.Resolution.HironakaG4OpenUnitGerm

/-! Actual recorded unit parts protect a full-boundary test step. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ActualUnitWindowProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HironakaSharpActualFiniteChronologicalHistory HironakaG4PreparedCentreCoordinates
  HironakaG4WindowActualParts HironakaG4OpenUnitGerm HironakaG4AmbientUnitTemplate
  HironakaG4FullTemplateProtection HironakaG34LowerCleanupLift
  DivisorExponentAlong MonomialPartAlong NonmonomialTransformAlong RestrictedIdealExtension

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The actual recorded monomial-unit and residual parts, protected source
window, and the actual lower/full tests give the full protected certificate. -/
theorem actual_unit_window_protects_full_test_step (hn : 0 < n)
    (P Q : MarkedIdeal n X) (N S : Set X) (old born : List (Set X))
    (hPN : P.N ⊆ N) (hQE : Q.E = old ++ born) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i : Fin old.length) (U : Opens X) (Haux : Set U)
    (hEF : IsSNCDivisor n (Haux :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hSlice : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' N ∩ Haux)
    (hRes : GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) =
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' S))
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hP : IsGeoTestTower P (.step T C π hπ)) (hQ : IsGeoTestTower Q (.step T C π hπ))
    (x : Y) (hxU : T.proj x ∈ U) (hxN : T.proj x ∈ N)
    (hxAux : (⟨T.proj x,hxU⟩ : U) ∈ Haux)
    (hunit : (oldMonomialPart N old born i).mem (T.proj x) 1) :
    let K : MarkedIdeal n X := geometricTemplate N []
    ProtectedWindowAt (strictAlong T N) (strictAlong T S)
      ((old.eraseIdx i.val ++ born).map (strictAlong T) ++ (geoTransformAlong K T).E) C x := by
  dsimp only
  let F := old.eraseIdx i.val ++ born
  let NU := (Subtype.val : U → X) ⁻¹' N
  let B := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let I := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
  let J := nonmonomialPartAlong n NU I B
  have hParts := actual_window_normalized_parts hn hN hE hTr hDense U i
  have hcI : I.IsCoherent := hParts.1
  have hnz : ∀ y ∈ NU, IsNonzeroAlongAt NU I y := hParts.2.1
  have hcD := (actual_old_parts_geometry hn hN hE hTr hDense i).2.2.2.2.1
  have hunit' : (monomialPartAlong n NU I B).mem ⟨T.proj x,hxU⟩ 1 := by
    rw [hParts.2.2.2.1, pullback_val_unit_iff U _ hcD]
    exact hunit
  have hJZ : ∀ g, J.mem ⟨T.proj x,hxU⟩ g ↔ (vanishingIdeal (n := n) (NU ∩ Haux)).mem ⟨T.proj x,hxU⟩ g := by
    intro g
    have hJ : J = GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) := hParts.2.2.2.2
    rw [hJ,hRes,hSlice]
  have hLU : IsSNCDivisor n ((old ++ born).map ((Subtype.val : U → X) ⁻¹' ·)) :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hHL : (Subtype.val : U → X) ⁻¹' old.get i ∈
      (old ++ born).map ((Subtype.val : U → X) ⁻¹' ·) :=
    List.mem_map_of_mem (List.mem_append_left born (List.get_mem old i))
  obtain ⟨V,hxV,hVU,hDV,hSV⟩ := exists_ambient_unit_member_template hn U ⟨T.proj x,hxU⟩
    N (old.get i) S F Haux B ((old ++ born).map ((Subtype.val : U → X) ⁻¹' ·))
    hN hEF hTF hLU hHL hxN hxAux hcI (hnz _ hxN) hunit' hJZ hSlice
  have hperm : (old.get i :: F).Perm Q.E := by
    rw [hQE]
    have h := (List.getElem_cons_eraseIdx_perm i.isLt).append_right born
    simpa only [List.get_eq_getElem,List.cons_append,F] using h
  exact local_member_template_protected_by_full_test N (old.get i) S F P Q hPN hperm V hDV hSV
    T C π hπ hP hQ x hxV

end
end Hironaka.HironakaG4ActualUnitWindowProtection
