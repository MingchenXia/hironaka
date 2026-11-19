import Hironaka.Resolution.HironakaG3CoupledFullBoundary
import Hironaka.Resolution.HironakaG3CoupledStrictTransform
import Hironaka.Resolution.HironakaG3BoundaryContainedAmbientGlobalLift

/-!
# The full original boundary on actual stopped contained-target charts

Stopped native geometry supplies the residual normal crossings conclusion;
the actual coupled history restores every containing original boundary
member on the same ambient tower. The ordinary contained-target producer
then constructs a whole atlas with this full-boundary chart geometry.
The target dimension is strictly smaller than the smooth contact dimension.

Blueprint: `hironaka-g3-stopped-contained-boundary.tex`.
-/

set_option autoImplicit false

open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3StoppedContainedBoundary

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaDisjointNativeOpenLift
  HironakaDisjointNativeReferenceWindow HironakaActualNativeSectionFiniteHistory
  HironakaG3RBoundaryEmbedded HironakaG3RStoppedOverlap
  HironakaG3StoppedCoupledGeometry HironakaG3CoupledStrictTransform
  HironakaG3CoupledFullBoundary HironakaG3BoundaryContainedAnalyticTrace
  HironakaG3BoundaryContainedOriginalInputs HironakaG3BoundaryContainedAmbientGlobalLift

/-- Residual stopped geometry supplies the actual full-boundary conclusion
on the same coupled ambient chart, without a caller normal-crossings premise. -/
theorem actual_stopped_full_boundary_geometry
    {d t : ℕ} (hd : 0 < d) (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (E : List (Set X)) (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H)
    (J : GermIdeal (d+t) X) (hJ : J.IsCoherent) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN))
      (_hVa : IsComplexAnalyticSubset (n := d) V)
      (_hTrace : GermIdeal.pullback (m := d) (Subtype.val : N → X) J = vanishingIdeal (n := d) V)
      {r : ℕ} (_hr : r < d) (_hpure : V ⊆ closure (regularLocus (n := d) V r))
      (_hAvoid : V ⊆ closure (V \ ⋃ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·), H))
      (U : Opens X),
      letI := chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      ∀ {R : CMfd.{0} d} (T : BlowupTower
        (nativeManifold (Nat.le_add_right d t) (openSection N U) (openSection_regular hN U)) R)
        {Y : CMfd.{0} (d+t)} (A : BlowupTower (CMfd.of (n := d+t) U) Y) (η : R → Y),
        let J_U := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J
        let B_U := B.map ((Subtype.val : U → X) ⁻¹' ·)
        let M_U := fullMarked (B_U.map ((Subtype.val : openSection N U → U) ⁻¹' ·))
          (GermIdeal.pullback (m := d) (Subtype.val : openSection N U → U) J_U)
        CoupledHistory (openSection N U) B_U J_U (Subtype.val : openSection N U → U) M_U T A η →
        stoppedClass (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
          MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN))
          (bdryOpen V r (B.map ((Subtype.val : N → X) ⁻¹' ·)))
          (nativeWindow (Nat.le_add_right d t) N hN U) _
          (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U).symm T).tower →
        IsGeoTestTower (fullMarked B_U J_U) A →
        let W_U := (Subtype.val : U → X) ⁻¹' ((Subtype.val : N → X) '' V)
        let E_U := E.map ((Subtype.val : U → X) ⁻¹' ·)
        IsGeoTestTower (fullMarked E_U J_U) A ∧
          IsSNCDivisor (d+t) (geoTransformAlong (fullMarked E_U J_U) A).E ∧
          IsClosedSubmanifold (d+t) (strictTransform (d+t) A.proj W_U) ∧
          (∀ y ∈ strictTransform (d+t) A.proj W_U,
            RegularAtDim (n := d+t) (strictTransform (d+t) A.proj W_U) y r) ∧
          HasNormalCrossings (d+t) (strictTransform (d+t) A.proj W_U)
            (geoTransformAlong (fullMarked E_U J_U) A).E := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hVa hTrace r hr hpure hAvoid U
  let N_U := openSection N U
  let hNU := openSection_regular hN U
  let := chartedSpace (Nat.le_add_right d t) hNU
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hNU
  intro R T Y A η
  dsimp only
  intro hC hStop hTest
  let J_U := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J
  let B_U := B.map ((Subtype.val : U → X) ⁻¹' ·)
  let E_U := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let W_U := (Subtype.val : U → X) ⁻¹' ((Subtype.val : N → X) '' V)
  have hg := actual_stopped_coupled_geometry hd ht N hNc hN B hB hTrans J hJ
    V hVa hTrace hr hpure hAvoid U T A η hC hStop
  have heq := actual_stopped_coupled_strictTransform hd ht N hNc hN B hB hTrans J
    V hVa hr hpure hAvoid U T A η hC hStop
  have hJU : J_U.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hJ
  have hEU : IsSNCDivisor (d+t) E_U :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val (n := d+t) U)
      continuous_subtype_val hE
  have hBU : B_U.Sublist E_U := hBsub.map _
  have hOmittedU : ∀ H ∈ E_U, H ∉ B_U → N_U ⊆ H := by
    intro H hH hNot
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
    have hKB : K ∉ B := fun hk => hNot (List.mem_map.mpr ⟨K,hk,rfl⟩)
    exact fun y hy => hOmitted K hK hKB hy
  have hWNU : W_U ⊆ N_U := by
    intro y hy
    obtain ⟨z,_hz,hzy⟩ := hy
    change y.val ∈ N
    rw [←hzy]
    exact z.property
  obtain ⟨hFull,hSNC,hNC⟩ := restore_containing_boundary hC hJU hEU hBU hOmittedU hWNU
    hTest hg.2.2
  dsimp only at hg heq hNC
  rw [heq] at hg hNC
  exact ⟨hFull,hSNC,hg.1,hg.2.1,hNC⟩

/-- Ordinary proper-contact data produce the actual covering ambient histories
and one glued map, with full original-boundary geometry on every chart. -/
theorem exists_full_boundary_stopped_contained_atlas
    {d t : ℕ} (hd : 0 < d) (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (E : List (Set X)) (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H)) :
    ∃ (U : X → Opens X) (Y : X → CMfd.{0} (d+t))
      (A : ∀ x, BlowupTower (CMfd.of (n := d+t) (U x)) (Y x))
      (Z : CMfd.{0} (d+t)) (P : Z → X),
      (∀ x, x ∈ U x) ∧ ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ P ∧
      IsProperMap P ∧ Surjective P ∧
      (∀ x,
        let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U x → X)
          (vanishingIdeal (n := d+t) W)
        let Ex := E.map ((Subtype.val : U x → X) ⁻¹' ·)
        let Wx := (Subtype.val : U x → X) ⁻¹' W
        IsGeoTestTower (fullMarked Ex Jx) (A x) ∧
          IsSNCDivisor (d+t) (geoTransformAlong (fullMarked Ex Jx) (A x)).E ∧
          IsClosedSubmanifold (d+t) (strictTransform (d+t) (A x).proj Wx) ∧
          (∀ y ∈ strictTransform (d+t) (A x).proj Wx,
            RegularAtDim (n := d+t) (strictTransform (d+t) (A x).proj Wx) y r) ∧
          HasNormalCrossings (d+t) (strictTransform (d+t) (A x).proj Wx)
            (geoTransformAlong (fullMarked Ex Jx) (A x)).E) ∧
      ∀ x, ∃ Q : Opens Z, (Q : Set Z) = P ⁻¹' (U x : Set X) ∧
        ∃ φ : Y x ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ CMfd.of (n := d+t) Q,
          ∀ y, P (φ y : Z) = (((A x).proj y : U x) : X) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let V : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' W
  have hImage : (Subtype.val : N → X) '' V = W := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hy
      exact ⟨⟨y,hWN hy⟩,hy,rfl⟩
  have hImageA : IsComplexAnalyticSubset (n := d+t) ((Subtype.val : N → X) '' V) := by
    rw [hImage]
    exact hWa
  have hVa := native_analytic_of_ambient_image N hN V hImageA
  have hImagePure : ((Subtype.val : N → X) '' V) ⊆
      closure (regularLocus (n := d+t) ((Subtype.val : N → X) '' V) r) := by
    rw [hImage]
    exact hpure
  have hVPure := native_pure_of_ambient_image N hNc hN V r hImagePure
  have hImageAvoid : ((Subtype.val : N → X) '' V) ⊆
      closure (((Subtype.val : N → X) '' V) \ ⋃ H ∈ B, H) := by
    rw [hImage]
    exact hAvoid
  have hVAvoid := native_dense_avoid_of_ambient_image N hNc hN V B hImageAvoid
  have hInputs := original_contained_input_data hd N hNc hN B hB hTrans V hVa hImageA
    hr hVPure hVAvoid
  have hTrace := hInputs.2.2.1
  rw [hImage] at hTrace
  have hJ := CartanIrreducible.cartanCoherence W hWa
  obtain ⟨U,Y,A,Z,P,hcover,hP,hproper,hsurj,hlocal,hcharts⟩ :=
    ambient_contained_global_lift hd ht N hNc hN B hB hTrans W hWa hWN hr hpure hAvoid
  refine ⟨U,Y,A,Z,P,hcover,hP,hproper,hsurj,?_,hcharts⟩
  intro x
  let := chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
  obtain ⟨R,T,η,_hdom,_htest,hatest,hC,hStop⟩ := hlocal x
  have hg := actual_stopped_full_boundary_geometry hd ht N hNc hN B hB hTrans
    E hE hBsub hOmitted (vanishingIdeal (n := d+t) W) hJ V hVa hTrace
    hr hVPure hVAvoid (U x) T (A x) η hC hStop hatest
  dsimp only at hg
  rw [hImage] at hg
  exact hg

end

end Hironaka.HironakaG3StoppedContainedBoundary
