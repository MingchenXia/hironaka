import Hironaka.Resolution.HironakaG3BoundaryContainedAmbientGlobalLift
import Hironaka.Resolution.HironakaG3StoppedBoundaryAmbientBridge
import Hironaka.Resolution.HironakaG3RTowerClass
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FixedContactHeadClass
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeReferenceWindow HironakaDisjointNativeOpenLift
  HironakaDisjointFiniteControlledHistory HironakaG3RStoppedOverlap HironakaG3RBoundaryEmbedded
  HironakaG3BoundaryContainedAnalyticTrace HironakaG3BoundaryContainedOriginalInputs
  HironakaG3BoundaryContainedAmbientGlobalLift HironakaG3StoppedBoundaryAmbientBridge HironakaG3RTowerClass
open ResolutionInvariantSpec (IsInvDomain)

/-- Actual ambient heads coupled to native canonical stopped histories on a
fixed smooth contact. The full ambient test is not asserted canonical. -/
def fixedContactHead {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (W : Set X) (r : ℕ) : LocalTowerClass X := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let V : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' W
  let E := B.map ((Subtype.val : N → X) ⁻¹' ·)
  let O := bdryOpen V r E
  exact fun U Y A =>
    letI := chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
    ∃ (R : CMfd.{0} d)
      (T : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N U)
        (openSection_regular hN U)) R) (η : R → Y),
      let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) (vanishingIdeal (n := d+t) W)
      let Bx := B.map ((Subtype.val : U → X) ⁻¹' ·)
      let Mx := fullMarked (Bx.map ((Subtype.val : openSection N U → U) ⁻¹' ·))
        (GermIdeal.pullback (m := d) (Subtype.val : openSection N U → U) Jx)
      IsInvDomain d Mx ∧ IsGeoTestTower Mx T ∧ IsGeoTestTower (fullMarked Bx Jx) A ∧
      CoupledHistory (openSection N U) Bx Jx (Subtype.val : openSection N U → U) Mx T A η ∧
      stoppedClass (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
        MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
        (nativeWindow (Nat.le_add_right d t) N hN U) _
        (MarkedIdealTowerTransport.transport (windowEquiv (Nat.le_add_right d t) N hN hNc U).symm T).tower

/-- Actual proper-contact input constructs a member around every point. -/
theorem fixedContactHead_covers {d t : ℕ} (hd : 0 < d) (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H)) : Covers (fixedContactHead N hNc hN B W r) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  obtain ⟨U,Y,A,Z,P,hU,hP,hProper,hSurj,hhead,hCharts⟩ :=
    ambient_contained_global_lift hd ht N hNc hN B hB hTrans W hWa hWN hr hpure hAvoid
  intro x
  exact ⟨U x,hU x,Y x,A x,hhead x⟩

/-- All actual fixed-contact heads compare over their literal ambient overlap. -/
theorem fixedContactHead_comparisons {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H)) : HasComparisons (fixedContactHead N hNc hN B W r) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let V : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' W
  have hImage : (Subtype.val : N → X) '' V = W := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩; exact hp
    · intro hy; exact ⟨⟨y,hWN hy⟩,hy,rfl⟩
  have hVa := native_analytic_of_ambient_image N hN V (by rwa [hImage])
  have hVp := native_pure_of_ambient_image N hNc hN V r (by rwa [hImage])
  have hVA := native_dense_avoid_of_ambient_image N hNc hN V B (by rwa [hImage])
  have hInputs := original_contained_input_data hd N hNc hN B hB hTrans V hVa (by rwa [hImage]) hr hVp hVA
  dsimp only at hInputs
  obtain ⟨hJ,hNorm,hTrace,hDom,hEO,hPure,hDense⟩ := hInputs
  intro U₁ U₂ Y₁ Y₂ A₁ A₂ h₁ h₂
  obtain ⟨R₁,T₁,η₁,hM₁,hT₁,hA₁,hC₁,hStop₁⟩ := h₁
  obtain ⟨R₂,T₂,η₂,hM₂,hT₂,hA₂,hC₂,hStop₂⟩ := h₂
  exact stopped_coupled_ambient_overlap_bdry hd N hNc hN V hVa.isClosed
    (B.map ((Subtype.val : N → X) ⁻¹' ·))
    (bdryOpen V r (B.map ((Subtype.val : N → X) ⁻¹' ·))) hEO hPure hDense hDom
    U₁ U₂ hM₁ hM₂ T₁ T₂ A₁ A₂ hT₁ hT₂ hA₁ hA₂ hC₁ hC₂ hStop₁ hStop₂
end
end Hironaka.HironakaG3FixedContactHeadClass
