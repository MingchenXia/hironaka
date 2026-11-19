import Hironaka.Resolution.HironakaG8P1ArcCarrierPlane

set_option autoImplicit false

/-!
# Original scalar tangent equations from the actual filled arc trace

The checked ordinary common-family constructor and its genuine local
carrier-plane filling imply annihilation of all original A tangent vectors
by the derivative of each original B equation in the retained A frame.
Local equations retain their original neighborhood qualifiers.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcOriginalTangent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower HironakaG8P1ArcPair
  HironakaG8P1ArcPairTrace HironakaG8P1ArcExceptionalTrace HironakaG8P1ArcTangentTrace
  HironakaG8P1ArcCarrierPlane

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

noncomputable section

/-- A linear equation valid near zero on a coordinate plane is valid on
the whole plane, by scaling each vector inside the genuine neighborhood. -/
theorem linear_eq_zero_on_coordinatePlane_of_eventually
    {n : ℕ} (J : Finset (Fin n)) (L : ComplexModel n →L[ℂ] ℂ)
    (hkill : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ coordSubspace J → L w = 0) :
    ∀ v ∈ coordSubspace J, L v = 0 := by
  intro v hv
  have ht : Tendsto (fun t : ℂ => t • v) (𝓝 0) (𝓝 (0 : ComplexModel n)) := by
    have hc : Continuous (fun t : ℂ => t • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.tendsto (0 : ℂ)
  have hzero : ∀ᶠ t in 𝓝 (0 : ℂ), L (t • v) = 0 := by
    filter_upwards [ht hkill] with t htv
    apply htv
    intro i hi
    simp only [PiLp.smul_apply, smul_eq_mul, hv i hi, mul_zero]
  have hzero' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L (t • v) = 0 := nhdsWithin_le_nhds hzero
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht0
    exact ht0
  obtain ⟨t, htz, htne⟩ := (hzero'.and hne).exists
  rw [L.map_smul, smul_eq_mul] at htz
  exact (mul_eq_zero.mp htz).resolve_left htne

/-- Reading a local linear equation in the actual stage chart gives its
vanishing on every vector of the original coordinate plane. -/
theorem linear_eq_zero_on_originalPlane_of_chart_trace
    {n : ℕ} {Z : CMfd.{u} (n+1)}
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1))) {z : Z}
    (hz : z ∈ e.source) (hzero : e z = 0)
    (J : Finset (Fin n)) (L : ComplexModel n →L[ℂ] ℂ)
    (hkill : ∀ᶠ y in 𝓝 z,
      y ∈ e.source ∩ e ⁻¹' coordSubspace (exceptionalMask J) →
        L (oldCoordinates (e y)) = 0) :
    ∀ v ∈ coordSubspace J, L v = 0 := by
  apply linear_eq_zero_on_coordinatePlane_of_eventually J L
  let join : ComplexModel n → ComplexModel (n+1) :=
    fun v => ProductComplexManifold.prodModelEquiv n 1 (v, 0)
  have hjoin0 : join 0 = 0 := by
    change ProductComplexManifold.prodModelEquiv n 1 (0, 0) = 0
    exact map_zero _
  have hjoin : Tendsto join (𝓝 0) (𝓝 0) := by
    have hc : Continuous join := (ProductComplexManifold.prodModelEquiv n 1).continuous.comp
      (continuous_id.prodMk continuous_const)
    simpa only [hjoin0] using hc.tendsto 0
  have htarget : (0 : ComplexModel (n+1)) ∈ e.target := hzero ▸ e.map_source hz
  have hinv0 : e.symm 0 = z := by rw [← hzero, e.left_inv hz]
  have hy : Tendsto (fun v => e.symm (join v)) (𝓝 (0 : ComplexModel n)) (𝓝 z) := by
    simpa only [hinv0, Function.comp_def] using (e.symm.continuousAt htarget).tendsto.comp hjoin
  filter_upwards [hy hkill, hjoin (e.open_target.mem_nhds htarget)] with v hvKill hvTarget hvPlane
  have hOld : oldCoordinates (join v) = v := by
    simp only [join, oldCoordinates, ContinuousLinearEquiv.symm_apply_apply]
  have hLast : join v (Fin.last n) = 0 := by
    have hp := (ProductComplexManifold.prodModelEquiv_mem_complexCoordinatePlane_iff
      v (0 : ComplexModel 1)).mpr rfl
    exact hp (Fin.last n) (by simp)
  have hmem : join v ∈ coordSubspace (exceptionalMask J) :=
    (mem_exceptionalMask_iff J _).mpr ⟨hOld.symm ▸ hvPlane, hLast⟩
  have hk := hvKill ⟨e.map_target hvTarget, by
    change e (e.symm (join v)) ∈ coordSubspace (exceptionalMask J)
    rw [e.right_inv hvTarget]
    exact hmem⟩
  rw [e.right_inv hvTarget, hOld] at hk
  exact hk

variable {n : ℕ} {X : CMfd.{u} n}

/-- Ordinary native pair input in the order-greater-than-mark branch
constructs an original frame for A in which every actual B scalar equation
has derivative zero on the entire original carrier plane of A. -/
theorem exists_original_frame_with_tangent_annihilation
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (J : Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ w ∈ flatDomain Φ, w ∈ A.N ↔
        Φ.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J) ∧
      ∀ (g : ComplexModel n → ℂ) (L : ComplexModel n →L[ℂ] ℂ),
        HasFDerivAt g L 0 →
        (∀ w ∈ B.N, w ∈ flatDomain Φ →
          g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0) →
        ∀ v ∈ coordSubspace J, L v = 0 := by
  obtain ⟨hπ1, Φ, J, S, hsrc, hzero, hMask, hS, hAll⟩ :=
    exists_arcPairFamily_with_filled_exceptional_trace
      A B hA hB hEB hdim hx A' B' hsA hsB hW hE' hgreater
  refine ⟨Φ, J, hsrc, hzero, hMask, ?_⟩
  intro g L hg hEquation
  obtain ⟨_hcA, _hcB, facts, _hAtlas, _hcoords, hparameter, hcommon, hfill,
    V, hV, hzV, _hVsource, _hVdomain, hTrace⟩ := hAll A.d
  apply linear_eq_zero_on_originalPlane_of_chart_trace (S A.d).e
    (hS.arc A.d).mem_source (hS.arc A.d).eq_zero J L
  filter_upwards [hfill, hcommon (by omega), hV.mem_nhds hzV] with y hyFill hyCommon hyV hyPlane
  have hyA := hyFill.mpr hyPlane
  have hyB := hyCommon.mp hyA
  have hyStrict : y ∈ strictAlong ((arcA1 x hπ1).append (S A.d).R)
      ((Prod.fst : projectionAmbient X → X) ⁻¹' B.N) := by
    have hyN := hyB.1
    rw [N_geoTransformAlong] at hyN
    exact hyN
  exact hTrace B.N hB.isWellFormed.isClosedSubmanifold_N.1 g L hg hEquation y hyStrict hyV
    (hparameter y hyA.2)

/-- A locally valid original equation can be extended by its value at zero
outside a genuine coordinate neighborhood. It keeps the same derivative
and satisfies the global qualified equation used by the checked trace. -/
theorem exists_global_level_equation_of_local
    (x : X) (W : Set X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (g : ComplexModel n → ℂ) (L : ComplexModel n →L[ℂ] ℂ) (hg : HasFDerivAt g L 0)
    (hLocal : ∀ᶠ w in 𝓝 x, w ∈ W → w ∈ flatDomain Φ →
      g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0) :
    ∃ g' : ComplexModel n → ℂ, g' =ᶠ[𝓝 0] g ∧ HasFDerivAt g' L 0 ∧
      ∀ w ∈ W, w ∈ flatDomain Φ →
        g' (Φ.toFun (chartAt (ComplexModel n) x w)) = g' 0 := by
  classical
  have hInv : Tendsto (GiraudAlong.flatInv Φ) (𝓝 0) (𝓝 x) := by
    simpa only [GiraudAlong.flatInv_zero hzero] using
      (GiraudAlong.continuousAt_flatInv (GiraudAlong.zero_mem_target hzero) hsrc).tendsto
  obtain ⟨U, hUsub, hUopen, h0U⟩ := mem_nhds_iff.mp (hInv hLocal)
  let g' : ComplexModel n → ℂ := fun w => if w ∈ U then g w else g 0
  have hAgree : g' =ᶠ[𝓝 0] g := by
    filter_upwards [hUopen.mem_nhds h0U] with w hw
    exact if_pos hw
  refine ⟨g', hAgree, hg.congr_of_eventuallyEq hAgree, ?_⟩
  intro w hw hwDom
  by_cases hwU : Φ.toFun (chartAt (ComplexModel n) x w) ∈ U
  · have h := hUsub hwU
    change GiraudAlong.flatInv Φ (GiraudAlong.flatMap Φ w) ∈ W →
      GiraudAlong.flatInv Φ (GiraudAlong.flatMap Φ w) ∈ flatDomain Φ →
        g (GiraudAlong.flatMap Φ (GiraudAlong.flatInv Φ (GiraudAlong.flatMap Φ w))) = g 0 at h
    rw [GiraudAlong.flatInv_flatMap hwDom] at h
    simpa only [g', if_pos hwU, if_pos h0U, GiraudAlong.flatMap] using h hw hwDom
  · simp only [g', if_neg hwU, if_pos h0U]

/-- The ordinary producer applies to equations which hold only as germs
on the original B carrier. Its frame is the actual retained A frame, and
all neighborhood restrictions are discharged by the constructed extension. -/
theorem exists_original_frame_with_local_tangent_annihilation
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (J : Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ w ∈ flatDomain Φ, w ∈ A.N ↔
        Φ.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J) ∧
      ∀ (g : ComplexModel n → ℂ) (L : ComplexModel n →L[ℂ] ℂ),
        HasFDerivAt g L 0 →
        (∀ᶠ w in 𝓝 x, w ∈ B.N → w ∈ flatDomain Φ →
          g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0) →
        ∀ v ∈ coordSubspace J, L v = 0 := by
  obtain ⟨Φ, J, hsrc, hzero, hMask, hKill⟩ :=
    exists_original_frame_with_tangent_annihilation
      A B hA hB hEB hdim hx A' B' hsA hsB hW hE' hgreater
  refine ⟨Φ, J, hsrc, hzero, hMask, ?_⟩
  intro g L hg hLocal
  obtain ⟨g', _hAgree, hg', hEquation⟩ :=
    exists_global_level_equation_of_local x B.N Φ hsrc hzero g L hg hLocal
  exact hKill g' L hg' hEquation

end

end Hironaka.HironakaG8P1ArcOriginalTangent
