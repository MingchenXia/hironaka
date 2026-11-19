import Hironaka.Resolution.HironakaG3LocalStoppedCoupledProducer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryContainedGlobalLift
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory
  HironakaDisjointNativeReferenceWindow HironakaDisjointNativeOpenLift
  HironakaDisjointFiniteControlledHistory HironakaG3LocalStoppedCover
  HironakaG3LocalStoppedCoupledProducer HironakaG3StoppedBoundaryAmbientBridge
open ResolutionInvariantSpec (IsInvDomain)

/-- Native stopped histories are lifted and glued globally, with the actual
ambient charts constructed from the original coherent ideal. -/
theorem exists_global_stopped_contact_lift
    {d t : ℕ} (hd : 0 < d) (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (J : GermIdeal (d+t) X) (hJ : J.IsCoherent) (hNorm : (vanishingIdeal (n := d+t) N).Le J) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN)) (_hV : IsClosed V)
      (_hTrace : GermIdeal.pullback (m := d) (Subtype.val : N → X) J = vanishingIdeal (n := d) V)
      (_hdom : IsInvDomain d (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
        MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)))
      (O : Opens (nativeManifold (Nat.le_add_right d t) N hN))
      (_hEO : ∀ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·),
        Disjoint H (O : Set (nativeManifold (Nat.le_add_right d t) N hN)))
      {r : ℕ} (_hpure : ∀ x : O, (x : nativeManifold (Nat.le_add_right d t) N hN) ∈ V →
        RegularAtDim (n := d) V x r) (_hdense : V ⊆ closure (V ∩ O)),
    ∃ (U : X → Opens X) (Y : X → CMfd.{0} (d+t))
      (A : ∀ x, BlowupTower (CMfd.of (n := d+t) (U x)) (Y x))
      (Z : CMfd.{0} (d+t)) (P : Z → X),
      (∀ x, x ∈ U x) ∧ ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ P ∧
      IsProperMap P ∧ Surjective P ∧
      (∀ x,
        letI := chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
        letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
        ∃ (R : CMfd.{0} d)
          (T : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N (U x))
            (openSection_regular hN (U x))) R) (η : R → Y x),
          let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U x → X) J
          let Bx := B.map ((Subtype.val : U x → X) ⁻¹' ·)
          let Mx := fullMarked (Bx.map ((Subtype.val : openSection N (U x) → U x) ⁻¹' ·))
            (GermIdeal.pullback (m := d) (Subtype.val : openSection N (U x) → U x) Jx)
          IsInvDomain d Mx ∧ IsGeoTestTower Mx T ∧ IsGeoTestTower (fullMarked Bx Jx) (A x) ∧
          CoupledHistory (openSection N (U x)) Bx Jx (Subtype.val : openSection N (U x) → U x) Mx T (A x) η ∧
          HironakaG3RStoppedOverlap.stoppedClass
            (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
              MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
            (nativeWindow (Nat.le_add_right d t) N hN (U x)) _
            (MarkedIdealTowerTransport.transport (windowEquiv (Nat.le_add_right d t) N hN hNc (U x)).symm T).tower) ∧
      ∀ x, ∃ W : Opens Z, (W : Set Z) = P ⁻¹' (U x : Set X) ∧
        ∃ φ : Y x ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ CMfd.of (n := d+t) W,
          ∀ y, P (φ y : Z) = (((A x).proj y : U x) : X) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hV hTrace hdom O hEO r hpure hdense
  let M : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN) :=
    ⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩
  choose U hU Q S hStop using fun x : X =>
    exists_ambient_open_with_stopped_native_history N hNc hN M hdom O x
  have hproduce (x : X) := local_coupled_of_stopped ht N hNc hN B hB hTrans J hJ hNorm
    V hTrace hdom O (U x) (S x) (hStop x)
  choose R T Y A η hdomT hT hA hC hStopped using hproduce
  let B' : ∀ x, List (Set (U x)) := fun x => B.map ((Subtype.val : U x → X) ⁻¹' ·)
  let J' : ∀ x, GermIdeal (d+t) (U x) := fun x => GermIdeal.pullback (m := d+t) (Subtype.val : U x → X) J
  let M' : ∀ x, MarkedIdeal d (nativeManifold (Nat.le_add_right d t) (openSection N (U x)) (openSection_regular hN (U x))) := fun x => by
    let := chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
    let := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
    exact fullMarked ((B' x).map ((Subtype.val : openSection N (U x) → U x) ⁻¹' ·))
      (GermIdeal.pullback (m := d) (Subtype.val : openSection N (U x) → U x) (J' x))
  obtain ⟨Z,P,hP,hProper,hSurj,hCharts⟩ :=
    exists_glued_stopped_coupled_cover_bdry hd N hNc hN V hV (B.map ((Subtype.val : N → X) ⁻¹' ·))
      O hEO hpure hdense hdom X U (fun x => ⟨x,hU x⟩) B' J' M' hdomT R Y T A η hT hA hC hStopped
  refine ⟨U,Y,A,Z,P,hU,hP,hProper,hSurj,?_,hCharts⟩
  intro x
  exact ⟨R x,T x,η x,hdomT x,hT x,hA x,hC x,hStopped x⟩

end
end Hironaka.HironakaG3BoundaryContainedGlobalLift
