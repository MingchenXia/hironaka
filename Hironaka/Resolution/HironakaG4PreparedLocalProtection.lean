import Hironaka.Resolution.HironakaG4GammaLocalTraceProtection
import Hironaka.Resolution.HironakaG4AuxiliaryTemplate

/-! The prepared local residual protects the actual equivariant test centre. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4PreparedLocalProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings
  HironakaG34MaskFoldEquivariance HironakaSharpActualFiniteChronologicalHistory
  DivisorExponentAlong MonomialPartAlong RestrictedIdealExtension IdealWeightPowers
  HironakaG4AmbientPreparedGammaChart HironakaG4AuxiliaryTemplate
  HironakaG4GammaLocalTraceProtection HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Local prepared residual data and the locally identified lower trace
protect an actual equivariant test centre with its actual boundary history. -/
theorem prepared_residual_protects_equivariant_test_step_with_window (hn : 0 < n)
    (P : MarkedIdeal n X) (N S H W : Set X) (F : List (Set X))
    (hPN : P.N ⊆ N) (hN : IsClosedSubmanifold n N) (hF : ∀ K ∈ F, IsClosed K)
    (U : Opens X) (Haux : Set U)
    (hEF : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hSlice : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' N ∩ Haux)
    (B L : List (Set U)) (J : GermIdeal n U)
    (hBsub : B.Sublist (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hL : IsSNCDivisor n L) (hHL : (Subtype.val : U → X) ⁻¹' H ∈ L)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ)) {E : List (Set X)}
    (hEq : IsEquivariant W E (.step T C π hπ)) (x : Y) (hxC : x ∈ C)
    (hxU : T.proj x ∈ U) (hxN : T.proj x ∈ N) (hxHaux : (⟨T.proj x,hxU⟩ : U) ∈ Haux)
    (hxW : T.proj x ∈ W)
    (hI : (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))).IsCoherent)
    (hnz : ∀ y ∈ (Subtype.val : U → X) ⁻¹' N, IsNonzeroAlongAt ((Subtype.val : U → X) ⁻¹' N)
      (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) y)
    (hfactor : restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H)) =
      restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        ((monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
          (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
            (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mul J))
    (hgamma : ¬ (monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
      (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mem ⟨T.proj x,hxU⟩ 1)
    (hJZ : ∀ g, J.mem ⟨T.proj x,hxU⟩ g ↔
      (vanishingIdeal (n := n) (((Subtype.val : U → X) ⁻¹' N) ∩ Haux)).mem ⟨T.proj x,hxU⟩ g) :
    let G : Set X := closure ((Subtype.val : U → X) '' Haux)
    let D : MarkedIdeal n X := geometricTemplate N (G :: F)
    (∀ K ∈ E, K = H ∨ (K ∈ D.E ∨ (U : Set X) ⊆ K)) →
    (∀ j : Fin D.E.length, (∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ D.N ∩ D.E.get j) →
      let K : MarkedIdeal n X := {D with E := []}
      ProtectedWindowAt (strictAlong T N) (strictAlong T S)
        (F.map (strictAlong T) ++ (geoTransformAlong K T).E) C x) := by
  dsimp only
  intro hE j hW
  let G : Set X := closure ((Subtype.val : U → X) '' Haux)
  let D : MarkedIdeal n X := geometricTemplate N (G :: F)
  obtain ⟨hG,hDU,hSU⟩ := auxiliary_geometric_template_on_window U N S F Haux hN hEF hTF hSlice
  have hDc : ∀ K ∈ D.E, IsClosed K := by
    intro K hK
    change K ∈ G :: F at hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact hG
    · exact hF K hK
  obtain ⟨R₀,m,s,t,c,Φ,hm,hs,ht,hst,hcs,hsrc,hzero,hΦU,hNcoords,hDcoords,hHcoords⟩ :=
    exists_ambient_prepared_gamma_chart hn U ⟨T.proj x,hxU⟩ N H F Haux B L J
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U) hEF hTF hBsub hL hHL hxN hxHaux
      hI hnz hfactor hgamma hJZ
  exact gamma_chart_and_local_lower_trace_protect_step_with_window P D hPN G F rfl hN
    (isCoherent_unitIdeal (n := n) (M := X)) hDc rfl U hDU S hSU j T C π hπ hTest hEq
    x hxC hxW hW Φ hsrc hΦU s t c R₀ m hs hst hcs hm hNcoords hDcoords hHcoords hE

/-- The prepared local residual protects the step with the actual boundary symmetries. -/
theorem prepared_residual_protects_equivariant_test_step (hn : 0 < n)
    (P : MarkedIdeal n X) (N S H W : Set X) (F : List (Set X))
    (hPN : P.N ⊆ N) (hN : IsClosedSubmanifold n N) (hF : ∀ K ∈ F, IsClosed K)
    (U : Opens X) (Haux : Set U)
    (hEF : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hSlice : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' N ∩ Haux)
    (B L : List (Set U)) (J : GermIdeal n U)
    (hBsub : B.Sublist (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hL : IsSNCDivisor n L) (hHL : (Subtype.val : U → X) ⁻¹' H ∈ L)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ)) {E : List (Set X)}
    (hEq : IsEquivariant W E (.step T C π hπ)) (x : Y) (hxC : x ∈ C)
    (hxU : T.proj x ∈ U) (hxN : T.proj x ∈ N) (hxHaux : (⟨T.proj x,hxU⟩ : U) ∈ Haux)
    (hxW : T.proj x ∈ W)
    (hI : (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))).IsCoherent)
    (hnz : ∀ y ∈ (Subtype.val : U → X) ⁻¹' N, IsNonzeroAlongAt ((Subtype.val : U → X) ⁻¹' N)
      (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) y)
    (hfactor : restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H)) =
      restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        ((monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
          (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
            (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mul J))
    (hgamma : ¬ (monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
      (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mem ⟨T.proj x,hxU⟩ 1)
    (hJZ : ∀ g, J.mem ⟨T.proj x,hxU⟩ g ↔
      (vanishingIdeal (n := n) (((Subtype.val : U → X) ⁻¹' N) ∩ Haux)).mem ⟨T.proj x,hxU⟩ g) :
    let G : Set X := closure ((Subtype.val : U → X) '' Haux)
    let D : MarkedIdeal n X := geometricTemplate N (G :: F)
    (∀ K ∈ E, K = H ∨ K ∈ D.E) →
    (∀ j : Fin D.E.length, (∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ D.N ∩ D.E.get j) →
      let K : MarkedIdeal n X := {D with E := []}
      ProtectedWindowAt (strictAlong T N) (strictAlong T S)
        (F.map (strictAlong T) ++ (geoTransformAlong K T).E) C x) := by
  dsimp only
  intro hE j hW
  exact prepared_residual_protects_equivariant_test_step_with_window
    hn P N S H W F hPN hN hF U Haux hEF hTF hSlice B L J hBsub hL hHL
    T C π hπ hTest hEq x hxC hxU hxN hxHaux hxW hI hnz hfactor hgamma hJZ
    (fun K hK => (hE K hK).imp id Or.inl) j hW

end
end Hironaka.HironakaG4PreparedLocalProtection
