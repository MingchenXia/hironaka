import Hironaka.Resolution.HironakaActualNativeSectionBoundaryParts
import Hironaka.Resolution.HironakaActualNativeSectionBoundaryTrace
/-! The literal induced native strict-section model is genuine and preserves
full old/born SNC transversality. Uniform whole marked records and actual
current boundary-part dictionaries are outputs, not certificates supplied
among the hypotheses. Chronological invariant values remain separate. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionStepModel
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupStrictSubmanifold SubmanifoldChartedSpace
  HironakaActualClosedContactBlowupRestriction HironakaActualNativeSectionBoundaryTrace
  HironakaActualNativeSectionBoundaryParts HironakaSmoothSubmersionCoefficientIdeals
  NormalCrossings SimultaneousNormalCrossings BlowupSNCTransform MarkedIdeals
variable {n k : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {W : Set X}

theorem actual_native_step (hn : 0<n) (hk : k≤n) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(D : Set W) (_hD : IsClosedSubmanifold k D) (_hint : interior D=∅)
      (π : Y→X) (hπ : IsBlowupAlong n ((Subtype.val : W→X) '' D) π)
      (E : List (Set X)) (_hE : IsSNCDivisor n E) (_hT : IsTransverse n W E)
      (_hnc : HasNormalCrossings n ((Subtype.val : W→X) '' D) E),
      letI := strictChartedSpace hk hWc hW hπ
      letI := strict_isComplexManifold hk hWc hW hπ
      let C:=(Subtype.val : W→X) '' D
      let S:=geoStrictTransform π C W
      let σ:=restrictedProjection hWc D hπ
      let E':=E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
      IsBlowupAlong k D σ ∧ Topology.IsClosedEmbedding (Subtype.val : S→Y) ∧
      IsSNCDivisor n E' ∧ IsTransverse n S E' ∧
      ∀(A : Set W) (J : GermIdeal n X)
        (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (d : ℕ),
        let M : MarkedIdeal n X:=⟨(Subtype.val : W→X) '' A,E,J,d⟩
        let B : MarkedIdeal k W:=⟨A,E.map ((Subtype.val : W→X) ⁻¹' ·),
          GermIdeal.pullback (m := k) (Subtype.val : W→X) J,d⟩
        markedPullback (m := k) (Subtype.val : S→Y) (M.geoTransform C π)=B.geoTransform D σ := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro D hD hint π hπ E hE hT hnc
  let := strictChartedSpace hk hWc hW hπ
  have := strict_isComplexManifold hk hWc hW hπ
  let C:=(Subtype.val : W→X) '' D
  let S:=geoStrictTransform π C W
  have hCW : C⊆W:=by
    rintro _ ⟨x,_hx,rfl⟩
    exact x.property
  have hadapt : ∀x∈C,IsAdaptedAt n C W E x:=
    fun _ hx => isAdaptedAt_of_hasNormalCrossings hn hCW hE hT hnc hx
  refine ⟨restrictedProjection_isBlowupAlong hk hWc hW D hπ hD hint,
    (isClosed_closure : IsClosed S).isClosedEmbedding_subtypeVal,
    isSNCDivisor_geoTransformE hπ hE hadapt,
    isTransverse_geoTransformE hπ hWc hE hT hadapt,?_⟩
  intro A J hJ d
  exact markedPullback_actual_restricted_geoTransform hn hk hWc hW D A J hJ d hπ hE hT hnc

open MonomialPartAlong NonmonomialOrderLocal

theorem actual_strict_section_parts (hn : 0<n) (hk : k≤n) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(D : Set W) (_hD : IsClosedSubmanifold k D) (_hint : interior D=∅)
      (π : Y→X) (hπ : IsBlowupAlong n ((Subtype.val : W→X) '' D) π)
      (E : List (Set X)) (_hE : IsSNCDivisor n E) (_hT : IsTransverse n W E)
      (_hnc : HasNormalCrossings n ((Subtype.val : W→X) '' D) E),
      letI := strictChartedSpace hk hWc hW hπ
      letI := strict_isComplexManifold hk hWc hW hπ
      let C:=(Subtype.val : W→X) '' D
      let S:=geoStrictTransform π C W
      let E':=E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
      ∀(A : Set S) (J : GermIdeal n Y)
        (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (d : ℕ),
        GermIdeal.pullback (m := k) (Subtype.val : S→Y)
          (monomialPartAlong n ((Subtype.val : S→Y) '' A) J E')=
          monomialPartAlong k A (GermIdeal.pullback (m := k) (Subtype.val : S→Y) J)
            (E'.map ((Subtype.val : S→Y) ⁻¹' ·)) ∧
        GermIdeal.pullback (m := k) (Subtype.val : S→Y)
          (nonmonomialPartAlong n ((Subtype.val : S→Y) '' A) J E')=
          nonmonomialPartAlong k A (GermIdeal.pullback (m := k) (Subtype.val : S→Y) J)
            (E'.map ((Subtype.val : S→Y) ⁻¹' ·)) ∧
        ∀p : S,
          nmOrd (M := BlowupTowers.CMfd.of (n := n) Y)
            (⟨(Subtype.val : S→Y) '' A,E',J,d⟩ : MarkedIdeal n Y) p.val=
          nmOrd (M := BlowupTowers.CMfd.of (n := k) S)
            (⟨A,E'.map ((Subtype.val : S→Y) ⁻¹' ·),
              GermIdeal.pullback (m := k) (Subtype.val : S→Y) J,d⟩ : MarkedIdeal k S) p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro D hD hint π hπ E hE hT hnc
  let := strictChartedSpace hk hWc hW hπ
  have := strict_isComplexManifold hk hWc hW hπ
  let C:=(Subtype.val : W→X) '' D
  let S:=geoStrictTransform π C W
  let E':=E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  obtain ⟨_hσ,_hClosed,hE',hT',_hRecords⟩:=actual_native_step hn hk hWc hW D hD hint π hπ E hE hT hnc
  have hCW : C⊆W:=by
    rintro _ ⟨x,_hx,rfl⟩
    exact x.property
  have hReg : ∀y∈S,RegularAtDim (n := n) S y k:=
    fun _ hy => regularAtDim_geoStrictTransform hπ hWc hW hCW hy
  dsimp only
  intro A J hJ d
  refine ⟨pullback_native_monomialPartAlong hk hReg A E' hE' hT' J hJ,
    pullback_native_nonmonomialPartAlong hk hReg A E' hE' hT' J hJ,?_⟩
  intro p
  exact nmOrd_native_eq hk hReg A E' hE' hT' J hJ d p


end
end Hironaka.HironakaActualNativeSectionStepModel
