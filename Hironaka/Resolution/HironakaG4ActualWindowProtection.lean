import Hironaka.Resolution.HironakaG4PreparedLocalProtection
import Hironaka.Resolution.HironakaG4WindowActualParts
import Hironaka.Resolution.HironakaG4OpenUnitGerm

/-! Actual recorded monomial and residual parts protect a Gamma test step. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ActualWindowProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HironakaG34MaskFoldEquivariance HironakaSharpActualFiniteChronologicalHistory
  HironakaG4PreparedCentreCoordinates HironakaG4WindowActualParts HironakaG4OpenUnitGerm
  HironakaG4PreparedLocalProtection HironakaG34LowerCleanupLift
  DivisorExponentAlong MonomialPartAlong NonmonomialTransformAlong RestrictedIdealExtension

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual old/born geometry and the protected residual identity supply all
local ideal inputs for protection of a Gamma test step. -/
theorem actual_window_parts_protect_equivariant_step_with_window (hn : 0 < n)
    (P : MarkedIdeal n X) (N S W : Set X) (old born : List (Set X))
    (hPN : P.N ⊆ N) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i j : Fin old.length) (hne : j ≠ i) (U : Opens X) (Haux : Set U)
    (hEF : IsSNCDivisor n (Haux :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hSlice : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' N ∩ Haux)
    (hRes : GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) =
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' S))
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ))
    (extra : List (Set X)) (hExtra : ∀ K ∈ extra, (U : Set X) ⊆ K)
    (hEq : IsEquivariant W (extra ++ (old ++ born)) (.step T C π hπ))
    (x : Y) (hxC : x ∈ C) (hxU : T.proj x ∈ U) (hxN : T.proj x ∈ N)
    (hxAux : (⟨T.proj x,hxU⟩ : U) ∈ Haux) (hxW : T.proj x ∈ W)
    (hW : ∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ N ∩ old.get j)
    (hGamma : ¬ (oldMonomialPart N old born i).mem (T.proj x) 1) :
    let G : Set X := closure ((Subtype.val : U → X) '' Haux)
    let D : MarkedIdeal n X := geometricTemplate N (G :: (old.eraseIdx i.val ++ born))
    let K : MarkedIdeal n X := {D with E := []}
    ProtectedWindowAt (strictAlong T N) (strictAlong T S)
      ((old.eraseIdx i.val ++ born).map (strictAlong T) ++ (geoTransformAlong K T).E) C x := by
  dsimp only
  let F := old.eraseIdx i.val ++ born
  let G : Set X := closure ((Subtype.val : U → X) '' Haux)
  let D : MarkedIdeal n X := geometricTemplate N (G :: F)
  let NU := (Subtype.val : U → X) ⁻¹' N
  let B := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let I := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
  let J := nonmonomialPartAlong n NU I B
  have hParts := actual_window_normalized_parts hn hN hE hTr hDense U i
  have hcI : I.IsCoherent := hParts.1
  have hnz : ∀ y ∈ NU, IsNonzeroAlongAt NU I y := hParts.2.1
  have hfactor : I = restrictOn n NU ((monomialPartAlong n NU I B).mul J) := hParts.2.2.1
  have hcD := (actual_old_parts_geometry hn hN hE hTr hDense i).2.2.2.2.1
  have hgamma : ¬ (monomialPartAlong n NU I B).mem ⟨T.proj x,hxU⟩ 1 := by
    rw [hParts.2.2.2.1, pullback_val_unit_iff U _ hcD]
    exact hGamma
  have hJZ : ∀ g, J.mem ⟨T.proj x,hxU⟩ g ↔ (vanishingIdeal (n := n) (NU ∩ Haux)).mem ⟨T.proj x,hxU⟩ g := by
    intro g
    have hJ : J = GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) := hParts.2.2.2.2
    rw [hJ, hRes, hSlice]
  have hBsub : B.Sublist (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)) := by
    apply List.Sublist.trans _ (List.Sublist.cons _ (List.Sublist.refl _))
    change (born.map ((Subtype.val : U → X) ⁻¹' ·)).Sublist
      ((old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·))
    rw [List.map_append]
    exact List.sublist_append_right _ _
  have hLU : IsSNCDivisor n ((old ++ born).map ((Subtype.val : U → X) ⁻¹' ·)) :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hHL : (Subtype.val : U → X) ⁻¹' old.get i ∈
      (old ++ born).map ((Subtype.val : U → X) ⁻¹' ·) :=
    List.mem_map_of_mem (List.mem_append_left born (List.get_mem old i))
  have hFc : ∀ K ∈ F, IsClosed K := by
    intro K hK
    exact hE.1 K (((List.eraseIdx_sublist old i.val).append (List.Sublist.refl born)).subset hK)
  have hEsub : ∀ K ∈ extra ++ (old ++ born), K = old.get i ∨
      (K ∈ D.E ∨ (U : Set X) ⊆ K) := by
    intro K hK
    rcases List.mem_append.mp hK with hLandmark | hK
    · exact Or.inr (Or.inr (hExtra K hLandmark))
    rcases List.mem_append.mp hK with hOld | hBorn
    · obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hOld
      by_cases hai : a = i
      · exact Or.inl (by rw [hai])
      · right; left
        change old.get a ∈ G :: (old.eraseIdx i.val ++ born)
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_eraseIdx_iff_getElem.mpr ⟨a.val,a.isLt,fun he => hai (Fin.ext he),rfl⟩
    · right; left
      change K ∈ G :: (old.eraseIdx i.val ++ born)
      exact List.mem_cons_of_mem _ (List.mem_append_right _ hBorn)
  have hjmem : old.get j ∈ D.E := by
    change old.get j ∈ G :: (old.eraseIdx i.val ++ born)
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_eraseIdx_iff_getElem.mpr ⟨j.val,j.isLt,fun he => hne (Fin.ext he),rfl⟩
  obtain ⟨jD,hjD⟩ := List.mem_iff_get.mp hjmem
  have hW' : ∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ D.N ∩ D.E.get jD := by
    change ∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ N ∩ D.E.get jD
    simpa only [hjD] using hW
  exact prepared_residual_protects_equivariant_test_step_with_window hn P N S (old.get i) W F hPN hN hFc U Haux
    hEF hTF hSlice B ((old ++ born).map ((Subtype.val : U → X) ⁻¹' ·)) J hBsub hLU hHL
    T C π hπ hTest hEq x hxC hxU hxN hxAux hxW hcI hnz hfactor hgamma hJZ hEsub jD hW'

/-- Actual old and born geometry protects the step under the boundary equivariance. -/
theorem actual_window_parts_protect_equivariant_step (hn : 0 < n)
    (P : MarkedIdeal n X) (N S W : Set X) (old born : List (Set X))
    (hPN : P.N ⊆ N) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i j : Fin old.length) (hne : j ≠ i) (U : Opens X) (Haux : Set U)
    (hEF : IsSNCDivisor n (Haux :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hSlice : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' N ∩ Haux)
    (hRes : GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) =
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' S))
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ))
    (hEq : IsEquivariant W (old ++ born) (.step T C π hπ))
    (x : Y) (hxC : x ∈ C) (hxU : T.proj x ∈ U) (hxN : T.proj x ∈ N)
    (hxAux : (⟨T.proj x,hxU⟩ : U) ∈ Haux) (hxW : T.proj x ∈ W)
    (hW : ∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ N ∩ old.get j)
    (hGamma : ¬ (oldMonomialPart N old born i).mem (T.proj x) 1) :
    let G : Set X := closure ((Subtype.val : U → X) '' Haux)
    let D : MarkedIdeal n X := geometricTemplate N (G :: (old.eraseIdx i.val ++ born))
    let K : MarkedIdeal n X := {D with E := []}
    ProtectedWindowAt (strictAlong T N) (strictAlong T S)
      ((old.eraseIdx i.val ++ born).map (strictAlong T) ++ (geoTransformAlong K T).E) C x :=
  actual_window_parts_protect_equivariant_step_with_window hn P N S W old born hPN hN hE hTr hDense i j hne U Haux
    hEF hTF hSlice hRes T C π hπ hTest [] (by simp) hEq x hxC hxU hxN hxAux hxW hW hGamma

end
end Hironaka.HironakaG4ActualWindowProtection
