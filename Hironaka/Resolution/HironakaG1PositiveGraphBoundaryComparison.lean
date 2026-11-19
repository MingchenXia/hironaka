import Hironaka.Resolution.HironakaG1SingularGraphCodimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveGraphBoundaryComparison

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  CanonicalCentres ResolutionDriver NormalCrossings DivisorExponentAlong
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaG8LocalTransport HironakaG1NativeBoundaryCodimension
  HironakaG1NativeGraphOverlapRead HironakaG1NativeChartValueOrder
  HironakaNormalCrossingsFiniteMarkedCompletion HironakaOriginalBoundaryEmptyFilterComparison
  AnalyticDimensionBasics


open HironakaG1ActualCommonGraphNativeComparison HironakaG1CommonGraphRestrictionMaps
  HironakaG1IteratedNormalBlockIdeal HironakaG1NativeCoordinateWindow HironakaG1NormalGraphFlags
  HironakaActualOpenEmbeddingCanonicalExtension HironakaActualLocalCommonGraphModel
  HironakaG1IndependentFiniteNormalNative

open HironakaBaseChange DimensionMonotone AnalyticSubsetPreimage
  HironakaActualIntrinsicIsoPairedWindows HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces CategoryTheory

private theorem coordinate_graph_holomorphic {a b : ℕ} {A : Opens (ComplexModel a)}
    {F : ComplexModel a → ComplexModel b} (hF : ContDiffOn ℂ ∞ F A) :
    ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel b) ∞ (fun x : A => F x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hF.contDiffAt (A.isOpen.mem_nhds x.property)).contMDiffAt)

open HironakaG1CodimensionTwoChartTransport HironakaG1SingularGraphCodimension

/-- One positive block gives the actual common comparison and normalized
boundary identity for aligned ordered boundaries, using the singular native cut. -/
theorem exists_positive_actual_graph_boundary_comparison {a b : ℕ} (hb : 0 < b)
    {U : Opens (ComplexModel a)} {V : Opens (ComplexModel b)}
    {C : Set U} {D : Set V} (P : MarkedIdeal a U) (Q : MarkedIdeal b V) (h : ℕ → ℕ)
    (hP : NativeHSState (X := CMfd.of (n := a) U) P C h) (hPD : IsInvDomain a P)
    (hQ : NativeHSState (X := CMfd.of (n := b) V) Q D h) (hQD : IsInvDomain b Q)
    (e : actualSubspaceLocallyRingedSpace (n := a) C ≅
      actualSubspaceLocallyRingedSpace (n := b) D)
    (he : e.hom ≫ subspacePointMap (n := b) D = subspacePointMap (n := a) C) (c : C) :
    ∃ (A : Opens (ComplexModel a)) (B : Opens (ComplexModel b))
      (F : ComplexModel a → ComplexModel b) (G : ComplexModel b → ComplexModel a)
      (hAU : A ≤ U) (hBV : B ≤ V),
      c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      let X := CMfd.of (n := a + b) (commonDomain A B)
      let K := commonGraphSubset A B F (coordinateCarrier C ∩ (A : Set (ComplexModel a)))
      let P' := MarkedIdeal.pullback (Opens.inclusion hAU) P
      let Q' := MarkedIdeal.pullback (Opens.inclusion hBV) Q
      let L := commonGraphLeftMarked (B := B) (blockAmbientMarked (fun x : A => F x.val) P')
      let R := commonGraphRightMarked (A := A) (blockAmbientMarked (fun y : B => G y.val) Q')
      NativeHSState (X := X) L K h ∧ NativeHSState (X := X) R K h ∧
      L.d = P.d ∧ R.d = Q.d ∧ IsInvDomain (a + b) L ∧ IsInvDomain (a + b) R ∧
      (∀ x ∈ L.cosupp, ∃ p, p + 2 ≤ a + b ∧ LocDimLE (n := a + b) K x p) ∧
      (R.E = L.E →
        LocWPEquiv L R ∧ SameCarrierDim L R ∧
        ∀ F' ∈ L.E, ∀ x ∈ L.cosupp, x ∈ F' →
          R.d * divExpAlong (a + b) L.N L.ideal F' x =
            L.d * divExpAlong (a + b) R.N R.ideal F' x) ∧
      (∀ (V₀ : Opens X) (x : X), x ∈ V₀ →
        List.Forall₂ (fun F₀ G₀ : Set X => ∀ᶠ z in 𝓝 x, z ∈ F₀ ↔ z ∈ G₀)
          (L.E.filter (fun F₀ => decide (x ∈ F₀)))
          (R.E.filter (fun G₀ => decide (x ∈ G₀))) →
        ∃ O : Opens X, x ∈ O ∧ O ≤ V₀ ∧
          let A₀ := CMfd.of (n := a + b) O
          let L₀ := MarkedIdeal.pullback (M' := A₀) (Subtype.val : O → X) L
          let R₀ := MarkedIdeal.pullback (M' := A₀) (Subtype.val : O → X) R
          (nonemptyBoundary R₀).E = (nonemptyBoundary L₀).E ∧
          ∀ {Y : CMfd.{0} (a + b)} (T : BlowupTower A₀ Y),
            (IsCanonical L₀ ((invFamily (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) (a + b)).inv L₀) T ↔ IsCanonical R₀ ((invFamily (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) (a + b)).inv R₀) T) ∧
            (IsCanonical L₀ ((invFamily (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) (a + b)).inv L₀) T →
              (geoTransformAlong L₀ T).cosupp = (geoTransformAlong R₀ T).cosupp ∧
              maxLocus ((invFamily (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) (a + b)).inv L₀ T) (geoTransformAlong L₀ T).cosupp =
                maxLocus ((invFamily (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) (a + b)).inv R₀ T) (geoTransformAlong R₀ T).cosupp ∧
              let E := (geoTransformAlong L₀ T).cosupp
              let f := fun z : E => (invFamily (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) (a + b)).inv L₀ T z.val
              let g := fun z : E => (invFamily (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) (a + b)).inv R₀ T z.val
              ∃ e : range f ≃o range g, ∀ z : E, (e ⟨f z, mem_range_self z⟩ : ValTy (a + b)) = g z)) := by
  obtain ⟨A, B, F, G, hAU, hBV, hcA, hdB, hF, hG, hLS, hRS, hLd, hRd, _⟩ :=
    exists_actual_commonGraph_native_comparison P Q h hP hPD hQ hQD e he c
  obtain ⟨hD₁, hS₁⟩ := nativeHSState_coordinateWindow hP hPD hAU
  obtain ⟨hD₂, hS₂⟩ := nativeHSState_coordinateWindow hQ hQD hBV
  let P' := MarkedIdeal.pullback (Opens.inclusion hAU) P
  let Q' := MarkedIdeal.pullback (Opens.inclusion hBV) Q
  have hLeft := (blockAmbientMarked_nativeHSState _ (coordinate_graph_holomorphic hF) P' h hS₁ hD₁).1
  have hRight := (blockAmbientMarked_nativeHSState _ (coordinate_graph_holomorphic hG) Q' h hS₂ hD₂).1
  obtain ⟨hLD, hRD⟩ := actual_common_graph_domains _ _ hLeft hRight
  have hDim := actual_common_graph_codim_two_of_positive_right hb A B F
    (coordinateCarrier C ∩ (A : Set (ComplexModel a))) hF hLS
  refine ⟨A, B, F, G, hAU, hBV, hcA, hdB, hLS, hRS, hLd, hRd, hLD, hRD,
    hDim, ⟨(fun hE => native_codimension_two_zero_normalized hLS hRS hLD hRD hE hDim), ?_⟩⟩
  intro V₀ x hx hMatch
  exact exists_codimension_two_native_refinement
    (Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)) hLS hRS hLD hRD V₀ x hx hMatch
    (fun y hy _ => hDim y hy)

#print axioms exists_positive_actual_graph_boundary_comparison

end Hironaka.HironakaG1PositiveGraphBoundaryComparison
