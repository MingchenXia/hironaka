import Hironaka.Resolution.HironakaActualOldIndexCleanupTransport

/-! Literal geometric templates and actual test concatenation for cleanup. -/
set_option autoImplicit false
open Set
universe u
namespace Hironaka.HironakaActualGeometricCleanupComposition
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupStrictSubmanifold HomogenizedGlueingTower MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalFirstMemberExceptionalFactor
  RelativePrincipalizationSpan RestrictedIdealExtension IdealWeightPowers NormalCrossingsComparison GermIdealOrder
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem unit_step (N C : Set X) (B : List (Set X)) (π : Y → X) :
    ((geometricTemplate N B).geoTransform C π).ideal=unitIdeal n Y := by
  rw [geoTransform_zeroMark_ideal_eq_restricted_total (geometricTemplate N B) rfl]
  change restrictOn n _ (GermIdeal.pullback (m:=n) π (unitIdeal n X))=unitIdeal n Y
  rw [BlowupExceptionalDivisor.pullback_unitIdeal]
  ext y g
  exact ⟨fun hg=>hg.1,fun hg=>le_restrictOn isCoherent_unitIdeal y g hg⟩

private theorem marked_ext {P Q : MarkedIdeal n X} (hN : P.N=Q.N) (hE : P.E=Q.E)
    (hI : P.ideal=Q.ideal) (hd : P.d=Q.d) : P=Q := by
  cases P
  cases Q
  simp_all

theorem geometricTemplate_transform (N : Set X) (B : List (Set X)) (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate N B) T=
      geometricTemplate (strictAlong T N) (geoTransformAlong (geometricTemplate N B) T).E := by
  induction T with
  | refl => rfl
  | @step Y Z T C π hπ ih =>
    have hI : (geoTransformAlong (geometricTemplate N B) (.step T C π hπ)).ideal=unitIdeal n Z:=by
      change ((geoTransformAlong (geometricTemplate N B) T).geoTransform C π).ideal=_
      conv_lhs => rw [ih]
      exact unit_step _ _ _ _
    apply marked_ext
    · exact N_geoTransformAlong _ (.step T C π hπ)
    · rfl
    · exact hI
    · exact d_geoTransformAlong _ (.step T C π hπ)

theorem full_boundary_split (N : Set X) (O B : List (Set X)) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate (univ : Set X) (O++B)) T).E=
        O.map (strictAlong T)++(geoTransformAlong (geometricTemplate N B) T).E
  | _,.refl => by simp [geometricTemplate,strictAlong]
  | _,.step T C π hπ => by
    change ((geoTransformAlong (geometricTemplate (univ : Set X) (O++B)) T).E.map
      (geoStrictTransform π C)++[π ⁻¹' C])=_
    rw [full_boundary_split N O B T,List.map_append,List.append_assoc,List.map_map]
    rfl

private theorem boundary_sublist {A M : MarkedIdeal n X} (hE : A.E.Sublist M.E) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),(geoTransformAlong A T).E.Sublist (geoTransformAlong M T).E
  | _,.refl => hE
  | _,.step T C π _hπ =>
    (List.Sublist.map (geoStrictTransform π C) (boundary_sublist hE T)).append (List.Sublist.refl _)

theorem geometric_test_of_test (M : MarkedIdeal n X) (B : List (Set X)) (hB : B.Sublist M.E) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),IsGeoTestTower M T → IsGeoTestTower (geometricTemplate M.N B) T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hT => by
    have hGE := boundary_sublist (show (geometricTemplate M.N B).E.Sublist M.E from hB) T
    have hN : (geoTransformAlong M T).N=(geoTransformAlong (geometricTemplate M.N B) T).N:=by
      rw [N_geoTransformAlong,N_geoTransformAlong]
      rfl
    have hCos : (geoTransformAlong (geometricTemplate M.N B) T).cosupp=
        (geoTransformAlong (geometricTemplate M.N B) T).N:=by
      rw [geometricTemplate_transform]
      exact cosupport_zero (fun _ _ hg=>hg)
    refine ⟨geometric_test_of_test M B hB T hT.1,⟨hT.2.1,?_,?_⟩⟩
    · rw [hCos,←hN]
      exact hT.2.2.1.trans (geoTransformAlong M T).cosupp_subset_N
    · exact hasNormalCrossings_of_forall_mem hT.2.2.2 hGE.subset

theorem geometric_test_append_iff (N : Set X) (B : List (Set X)) (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    IsGeoTestTower (geometricTemplate N B) (T.append S) ↔
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (strictAlong T N) (geoTransformAlong (geometricTemplate N B) T).E) S := by
  rw [isGeoTestTower_append_iff,geometricTemplate_transform]
  rfl

end
end Hironaka.HironakaActualGeometricCleanupComposition
