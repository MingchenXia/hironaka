import Hironaka.Resolution.HironakaG8P1ArcOriginalTangent
import Hironaka.Analytic.RankDegeneracy

set_option autoImplicit false

/-!
# Intrinsic native tangent inclusion from the constructed arc family

Translate the checked original scalar equations to the intrinsic common
kernel of vanishing-ideal differentials. The original carrier mask already
gives all necessary scalar equations, so no second frame or new Hadamard
lemma is required.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcNativeTangent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower HironakaG8P1ArcPair
  HironakaG8P1ArcPairTrace HironakaG8P1ArcOriginalTangent

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- The common-kernel definition of the intrinsic tangent space puts its
image under the actual original flat differential in the literal carrier
mask. Only the genuine local carrier identity is used. -/
theorem map_tangent_mem_coordSubspace
    (C : Set X) (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (J : Finset (Fin n))
    (hMask : ∀ w ∈ flatDomain Φ, w ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J)
    {ξ : ComplexModel n} (hξ : ξ ∈ BlowupSpaceTangent.tangentSpace n C x) :
    fderiv ℂ (BlowupSpaceTangent.flatMap Φ x) (chartAt (ComplexModel n) x x) ξ ∈
      coordSubspace J := by
  intro i hi
  have hcoord : (vanishingIdeal (n := n) C).mem x (flatCoord Φ i) := by
    refine ⟨holomorphicAt_flatCoord Φ i (mem_flatDomain_self Φ), ?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with w hw hwC
    exact (hMask w hw).mp hwC i hi
  have hk := BlowupSpaceTangent.germDiff_eq_zero_of_mem_tangentSpace hξ hcoord
  rw [BlowupSpaceTangent.germDiff_flatCoord hsrc (mem_flatDomain_self Φ)] at hk
  exact hk

/-- The ordinary flat-representative chain rule at the original point,
extracted from the already proved local inverse identity. -/
theorem germDiff_eq_fderiv_flatRepresentative_comp
    (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    {f : X → ℂ} (hf : HolomorphicAt n f x) :
    BlowupSpaceTangent.germDiff n f x =
      (fderiv ℂ (f ∘ GiraudAlong.flatInv Φ) 0).comp
        (fderiv ℂ (BlowupSpaceTangent.flatMap Φ x) (chartAt (ComplexModel n) x x)) := by
  have hflat0 : BlowupSpaceTangent.flatMap Φ x (chartAt (ComplexModel n) x x) = 0 := by
    simp only [BlowupSpaceTangent.flatMap, BlowupSpaceTangent.chartAt_symm_self, hzero]
  have hg : DifferentiableAt ℂ (f ∘ GiraudAlong.flatInv Φ) 0 :=
    GiraudAlong.differentiableAt_comp_flatInv (GiraudAlong.zero_mem_target hzero) hsrc
      (by rw [GiraudAlong.flatInv_zero hzero]; exact hf)
  have heq : f ∘ (chartAt (ComplexModel n) x).symm =ᶠ[𝓝 (chartAt (ComplexModel n) x x)]
      (f ∘ GiraudAlong.flatInv Φ) ∘ BlowupSpaceTangent.flatMap Φ x := by
    filter_upwards [BlowupSpaceTangent.flatInverse_flatMap_eventually (mem_flatDomain_self Φ)]
      with w hw
    exact congrArg f hw.symm
  unfold BlowupSpaceTangent.germDiff
  rw [heq.fderiv_eq, fderiv_comp _ (by rw [hflat0]; exact hg)
    (BlowupSpaceTangent.differentiableAt_flatMap hsrc (mem_flatDomain_self Φ)), hflat0]

/-- The constructed actual arc family proves the intrinsic native tangent
inclusion in the order-greater-than-mark branch from ordinary pair input.
Neither an original tangent comparison nor a common-history certificate
is assumed. -/
theorem tangentSpace_le_of_native_pair_order_gt
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x) :
    BlowupSpaceTangent.tangentSpace n A.N x ≤ BlowupSpaceTangent.tangentSpace n B.N x := by
  obtain ⟨Φ, J, hsrc, hzero, hMask, hKill⟩ :=
    exists_original_frame_with_local_tangent_annihilation
      A B hA hB hEB hdim hx A' B' hsA hsB hW hE' hgreater
  obtain ⟨j, hjA⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 x (A.cosupp_subset_N hx)
  have hxB : x ∈ B.N := ((hdim x hx j).mp hjA).2.1
  intro ξ hξ
  have hξflat := map_tangent_mem_coordSubspace A.N x Φ hsrc J hMask hξ
  apply BlowupSpaceTangent.mem_tangentSpace.mpr
  intro f hf
  let g : ComplexModel n → ℂ := f ∘ GiraudAlong.flatInv Φ
  have hg : DifferentiableAt ℂ g 0 :=
    GiraudAlong.differentiableAt_comp_flatInv (GiraudAlong.zero_mem_target hzero) hsrc
      (by rw [GiraudAlong.flatInv_zero hzero]; exact hf.1)
  have hfx : f x = 0 := hf.2.self_of_nhds hxB
  have hEquation : ∀ᶠ w in 𝓝 x, w ∈ B.N → w ∈ flatDomain Φ →
      g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0 := by
    filter_upwards [hf.2] with w hw hwB hwDom
    change f (GiraudAlong.flatInv Φ (GiraudAlong.flatMap Φ w)) =
      f (GiraudAlong.flatInv Φ 0)
    rw [GiraudAlong.flatInv_flatMap hwDom, GiraudAlong.flatInv_zero hzero, hw hwB, hfx]
  have hvan := hKill g (fderiv ℂ g 0) hg.hasFDerivAt hEquation _ hξflat
  rw [germDiff_eq_fderiv_flatRepresentative_comp x Φ hsrc hzero hf.1,
    ContinuousLinearMap.comp_apply]
  exact hvan

/-- The native pair has equal intrinsic original tangent spaces in the
order-greater-than-mark branch. Equal carrier dimensions are the ordinary
input; the tangent inclusion is produced by the actual arc construction. -/
theorem tangentSpace_eq_of_native_pair_order_gt
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x) :
    BlowupSpaceTangent.tangentSpace n A.N x = BlowupSpaceTangent.tangentSpace n B.N x := by
  have hle := tangentSpace_le_of_native_pair_order_gt
    A B hA hB hEB hdim hx A' B' hsA hsB hW hE' hgreater
  obtain ⟨j, hjA⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 x (A.cosupp_subset_N hx)
  have hjB := (hdim x hx j).mp hjA
  have hfinA := RankDegeneracy.finrank_tangentSpaceIn_of_regularAtDim
    (complexChartAt (n := n) x) (mem_complexChartAt_source x) hjA
  have hfinB := RankDegeneracy.finrank_tangentSpaceIn_of_regularAtDim
    (complexChartAt (n := n) x) (mem_complexChartAt_source x) hjB
  change Module.finrank ℂ (BlowupSpaceTangent.tangentSpace n A.N x) = j at hfinA
  change Module.finrank ℂ (BlowupSpaceTangent.tangentSpace n B.N x) = j at hfinB
  exact Submodule.eq_of_le_of_finrank_eq hle (hfinA.trans hfinB.symm)

end

end Hironaka.HironakaG8P1ArcNativeTangent
