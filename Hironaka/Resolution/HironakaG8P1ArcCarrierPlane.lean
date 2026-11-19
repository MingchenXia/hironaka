import Hironaka.Resolution.HironakaG8P1ArcExceptionalTrace
import Hironaka.Resolution.HironakaG8BFamilyEmptyMember
import Hironaka.Analytic.RegularAtDimChart

set_option autoImplicit false

/-!
# Filling the actual native exceptional carrier trace in the retained frame

The original carrier equations and the checked geometric differential trace
put the native exceptional carrier trace inside its original tangent plane.
The native dimension is preserved by the actual admissible tower; regular
filling then supplies the converse germ inclusion. This is the point-arc
route, not the general-centre birth-chart statement of case (r1).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcCarrierPlane

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold HomogenizedGlueingTower
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower HironakaG8P1ArcPair
  HironakaG8P1ArcPairTrace HironakaG8P1ArcExceptionalTrace HironakaG8P1ArcTangentTrace

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

noncomputable section

/-- The zero-parameter copy of an original coordinate plane. -/
def exceptionalMask {n : ℕ} (J : Finset (Fin n)) : Finset (Fin (n+1)) :=
  insert (Fin.last n) (J.map (Fin.castAddEmb 1))

theorem mem_exceptionalMask_iff {n : ℕ} (J : Finset (Fin n)) (w : ComplexModel (n+1)) :
    w ∈ coordSubspace (exceptionalMask J) ↔
      oldCoordinates w ∈ coordSubspace J ∧ w (Fin.last n) = 0 := by
  constructor
  · intro h
    refine ⟨?_, h _ (Finset.mem_insert_self _ _)⟩
    intro i hi
    exact h _ (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨i, hi, rfl⟩))
  · rintro ⟨hOld, hLast⟩ i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hLast
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact hOld j hj

theorem card_exceptionalMask {n : ℕ} (J : Finset (Fin n)) :
    (exceptionalMask J).card = J.card + 1 := by
  have hlast : Fin.last n ∉ J.map (Fin.castAddEmb 1) := by
    rintro h
    obtain ⟨i, _hi, he⟩ := Finset.mem_map.mp h
    have hv := congrArg Fin.val he
    change i.val = n at hv
    exact (Nat.ne_of_lt i.isLt) hv
  simp only [exceptionalMask, Finset.card_insert_of_notMem hlast, Finset.card_map]

/-- Extraction of the existing one-step carrier regularity transport along
an actual admissible tower, keeping the original local dimension. -/
theorem regularAtDim_geoTransformAlong_carrier
    {m : ℕ} {Y : CMfd.{u} m} (M : MarkedIdeal m Y) (hwf : M.IsWellFormed) :
    ∀ {Z : CMfd.{u} m} (T : BlowupTower Y Z), IsGeoTestTower M T →
      ∀ {z : Z} {k : ℕ}, z ∈ (geoTransformAlong M T).N →
        RegularAtDim (n := m) M.N (T.proj z) k →
        RegularAtDim (n := m) (geoTransformAlong M T).N z k
  | _, .refl, _, _, _, _hz, hreg => hreg
  | _, .step T C π hπ, hT, z, k, hz, hreg => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff M T C π hπ).mp hT
      have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwf T hTT
      have hz' : π z ∈ (geoTransformAlong M T).N :=
        geoStrictTransform_subset_preimage hπ.contMDiff.continuous hw.isClosedSubmanifold_N.1 hz
      have hr := regularAtDim_geoTransformAlong_carrier M hwf T hTT hz' hreg
      exact HironakaG8SpecialLoci.regularAtDim_geoStrictTransform_carrier hπ
        hw.isClosedSubmanifold_N.1 hC.subset_N hz hr

/-- An actual atlas chart pulls back the zero-parameter original coordinate
plane to a regular germ of its expected dimension. -/
theorem regularAtDim_exceptionalPlane
    {n : ℕ} {Z : CMfd.{u} (n+1)}
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (he : e ∈ atlas (ComplexModel (n+1)) Z) {z : Z}
    (hz : z ∈ e.source) (hzero : e z = 0) (J : Finset (Fin n)) :
    RegularAtDim (n := n+1) (e.source ∩ e ⁻¹' coordSubspace (exceptionalMask J)) z
      (n - J.card) := by
  let ec : ComplexChart (n+1) Z := ⟨e, he⟩
  apply (RegularAtDimChart.regularAtDim_chart_iff ec (coordSubspace (exceptionalMask J)) hz).mpr
  have hmem : e z ∈ coordSubspace (exceptionalMask J) := by
    rw [hzero]
    intro i _hi
    rfl
  have hreg := HironakaG8BFamilyEmptyMember.regularAtDim_coordSubspace (exceptionalMask J) hmem
  rw [card_exceptionalMask] at hreg
  have hdim : n + 1 - (J.card + 1) = n - J.card := by omega
  rw [hdim] at hreg
  apply CodimOneSupport.regularAtDim_of_eventually_mem_iff _ hreg
  filter_upwards [e.open_target.mem_nhds (e.map_source hz)] with w hw
  change w ∈ coordSubspace (exceptionalMask J) ↔
    w ∈ coordSubspace (exceptionalMask J) ∧ w ∈ e.target
  simp only [hw, and_true]

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual native carrier can be read in the conventional transform
along the point-arc tower, using proved centre avoidance and density. -/
theorem mem_strictTransform_of_mem_native_arcCarrier
    (M : MarkedIdeal n X) (hN : IsClosed M.N) {x : X}
    {hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))}
    {S : ℕ → ArcStage n (arcY1 x)} (hS : IsArcFamily x hπ1 S) (r : ℕ)
    {y : (S r).Z}
    (hy : y ∈ (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).N) :
    y ∈ strictTransform (n+1) ((arcA1 x hπ1).append (S r).R).proj
      ((Prod.fst : projectionAmbient X → X) ⁻¹' M.N) := by
  rw [N_geoTransformAlong] at hy
  change y ∈ strictAlong ((arcA1 x hπ1).append (S r).R)
    ((Prod.fst : projectionAmbient X → X) ⁻¹' M.N) at hy
  rw [strictAlong_eq_conventional_of_centresAvoid _ (hN.preimage continuous_fst)
    (HironakaG8P1ArcOffHorizontal.offHorizontal X)
    (HironakaG8P1ArcOffHorizontal.product_subset_closure_offHorizontal M.N)
    _ (HironakaG8P1ArcOffHorizontal.centresAvoid_offHorizontal_arcFamily hS r)] at hy
  exact hy

/-- Original scalar coordinate equations, the actual last-divisor geometry
and the checked analytic trace put the native exceptional carrier trace in
the original carrier plane on the genuine source/domain window. -/
theorem mem_exceptionalPlane_of_mem_native_trace
    (M : MarkedIdeal n X) (hN : IsClosed M.N) (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (J : Finset (Fin n))
    (hMask : ∀ w ∈ flatDomain Φ, w ∈ M.N ↔
      Φ.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J)
    {hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))}
    {S : ℕ → ArcStage n (arcY1 x)} (hS : IsArcFamily x hπ1 S) (r : ℕ)
    (hcoords : ∀ v ∈ (S r).e.source,
      (∀ i : Fin n, flatCoord Φ i (((arcA1 x hπ1).append (S r).R).proj v).1 =
        ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
      (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n))
    (hne : (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).E ≠ [])
    {y : (S r).Z}
    (hy : y ∈ (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).N ∩
      (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).E.getLast hne)
    (hySource : y ∈ (S r).e.source)
    (hyDomain : (((arcA1 x hπ1).append (S r).R).proj y).1 ∈ flatDomain Φ) :
    (S r).e y ∈ coordSubspace (exceptionalMask J) := by
  have hyParameter := last_parameter_zero_of_arcFamily M hS r hne y hy.2
  apply (mem_exceptionalMask_iff J _).mpr
  refine ⟨?_, ((hcoords y hySource).2).symm.trans hyParameter⟩
  intro i hi
  have hEquation : ∀ w ∈ M.N, w ∈ flatDomain Φ →
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ)
        (Φ.toFun (chartAt (ComplexModel n) x w)) =
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) 0 := by
    intro w hw hwDom
    exact (hMask w hwDom).mp hw i hi
  exact derivative_eq_zero_of_arc_coordinates x Φ ((arcA1 x hπ1).append (S r).R)
    (S r).e r hcoords M.N hN (EuclideanSpace.proj i) (EuclideanSpace.proj i)
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt hEquation
    (mem_strictTransform_of_mem_native_arcCarrier M hN hS r hy.1) hySource hyDomain hyParameter

/-- The actual native carrier trace fills its original coordinate plane
near the arc point. Its dimension is transported from the literal original
mask along the actual admissible tower; no tangent-space equality is input. -/
theorem eventually_native_trace_iff_exceptionalPlane
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (J : Finset (Fin n))
    (hMask : ∀ w ∈ flatDomain Φ, w ∈ M.N ↔
      Φ.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J)
    {hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))}
    {S : ℕ → ArcStage n (arcY1 x)} (hS : IsArcFamily x hπ1 S) (r : ℕ)
    (hTest : IsGeoTestTower (projectionTest M) ((arcA1 x hπ1).append (S r).R))
    (hAtlas : (S r).e ∈ atlas (ComplexModel (n+1)) (S r).Z)
    (hcoords : ∀ v ∈ (S r).e.source,
      (∀ i : Fin n, flatCoord Φ i (((arcA1 x hπ1).append (S r).R).proj v).1 =
        ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
      (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n))
    (hne : (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).E ≠ [])
    (hzN : (S r).z ∈ (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).N)
    (hzD : (S r).z ∈
      (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).E.getLast hne)
    (V : Set (S r).Z) (hV : IsOpen V) (hzV : (S r).z ∈ V)
    (hVsource : V ⊆ (S r).e.source)
    (hVdomain : ∀ v ∈ V, (((arcA1 x hπ1).append (S r).R).proj v).1 ∈ flatDomain Φ) :
    ∀ᶠ y in 𝓝 (S r).z,
      y ∈ (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).N ∩
        (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).E.getLast hne ↔
      y ∈ (S r).e.source ∩ (S r).e ⁻¹' coordSubspace (exceptionalMask J) := by
  let T := (arcA1 x hπ1).append (S r).R
  let Q := geoTransformAlong (projectionTest M) T
  let D := Q.E.getLast hne
  have hQ : IsInvDomain (k+1) Q :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong (projection_test_isInvDomain M hM) T hTest
  have hOriginal : RegularAtDim (n := n) M.N x (n - J.card) :=
    HironakaG8MemberLoci.regularAtDim_of_flat_coordSubspace Φ hsrc hzero
      (fun hy hyΦ => hMask _ ⟨hy, hyΦ⟩)
  have hproj : (T.proj (S r).z).1 = x := (hS.arc r).proj_eq.1
  have hProduct : RegularAtDim (n := n+1) (projectionTest M).N (T.proj (S r).z)
      ((n - J.card) + 1) := by
    have hsub := (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X)
      (Y := ComplexModel 1)).isSubmersionAt (T.proj (S r).z)
    have hOriginalAt : RegularAtDim (n := n) M.N (T.proj (S r).z).1 (n - J.card) := by
      rw [hproj]
      exact hOriginal
    have hr := (HironakaOriginalSmoothIntrinsicRegularLoci.regularAtDim_preimage_iff
      (X := X) (Y := projectionAmbient X) hsub M.N (n - J.card)).mpr
        hOriginalAt
    simpa only [projectionTest, Nat.add_sub_cancel_left] using hr
  have hNative : RegularAtDim (n := n+1) Q.N (S r).z ((n - J.card) + 1) :=
    regularAtDim_geoTransformAlong_carrier (projectionTest M)
      (projection_test_isInvDomain M hM).isWellFormed T hTest hzN hProduct
  have hD : D ∈ Q.E := List.getLast_mem hne
  have hIntersection := HironakaG8P1ForeignCount.regularAtDim_inter_of_mem
    hQ.isWellFormed.isTransverse hD hzN hzD hNative
  have hTraceDim : RegularAtDim (n := n+1) (Q.N ∩ D) (S r).z (n - J.card) := by
    simpa only [Nat.add_sub_cancel] using hIntersection.2
  obtain ⟨i, hi⟩ := List.get_of_mem hD
  have hClosed : IsClosedSubmanifold (n+1) (Q.N ∩ D) := by
    have h := MemberInterAlong.isClosedSubmanifold_inter_memberInter (Nat.succ_pos n)
      hQ.isWellFormed.isClosedSubmanifold_N.1 hQ.isWellFormed.isSNCDivisor
      hQ.isWellFormed.isTransverse {i}
    rw [DivisorExponentAlong.memberInter_singleton, hi] at h
    exact h
  have hPlane := regularAtDim_exceptionalPlane (S r).e hAtlas
    (hS.arc r).mem_source (hS.arc r).eq_zero J
  apply HironakaG8P1ForeignCount.eventually_mem_iff_of_subset hClosed hTraceDim hPlane
  filter_upwards [hV.mem_nhds hzV] with y hyV hy
  exact ⟨hVsource hyV, mem_exceptionalPlane_of_mem_native_trace M
    hM.isWellFormed.isClosedSubmanifold_N.1 x Φ J hMask hS r hcoords hne hy
    (hVsource hyV) (hVdomain y hyV)⟩

/-- Ordinary native pair input produces the same actual common family with
both the common native carrier-trace germ and its filling of A's original
coordinate plane. Every frame, count and genuine-window witness is retained. -/
theorem exists_arcPairFamily_with_filled_exceptional_trace
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x) :
    ∃ (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
      (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (J : Finset (Fin n)) (S : ℕ → ArcStage n (arcY1 x)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ w ∈ flatDomain Φ, w ∈ A.N ↔
        Φ.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J) ∧ IsArcFamily x hπ1 S ∧
      ∀ r, ArcCountsRaw (k := kA) A x hπ1 (S r) r ∧
        ArcCountsRaw (k := kB) B x hπ1 (S r) r ∧
        ∃ facts : ArcPairStageFacts A B A' ((arcA1 x hπ1).append (S r).R) (S r).z x r,
        (S r).e ∈ atlas (ComplexModel (n+1)) (S r).Z ∧
        (∀ v ∈ (S r).e.source,
          (∀ i : Fin n, flatCoord Φ i (((arcA1 x hπ1).append (S r).R).proj v).1 =
            ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
          (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n)) ∧
        (∀ y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
            facts.nonemptyA, (((arcA1 x hπ1).append (S r).R).proj y).2 0 = 0) ∧
        (A.d ≤ r + 1 → ∀ᶠ y in 𝓝 (S r).z,
          y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).N ∩
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
              facts.nonemptyA ↔
          y ∈ (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).N ∩
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
              facts.nonemptyA) ∧
        (∀ᶠ y in 𝓝 (S r).z,
          y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).N ∩
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
              facts.nonemptyA ↔
          y ∈ (S r).e.source ∩ (S r).e ⁻¹' coordSubspace (exceptionalMask J)) ∧
        ∃ V : Set (S r).Z, IsOpen V ∧ (S r).z ∈ V ∧ V ⊆ (S r).e.source ∧
          (∀ v ∈ V, (((arcA1 x hπ1).append (S r).R).proj v).1 ∈ flatDomain Φ) ∧
          ∀ (W : Set X), IsClosed W →
            ∀ (g : ComplexModel n → ℂ) (L : ComplexModel n →L[ℂ] ℂ),
              HasFDerivAt g L 0 →
              (∀ w ∈ W, w ∈ flatDomain Φ →
                g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0) →
              ∀ y ∈ strictAlong ((arcA1 x hπ1).append (S r).R)
                  ((Prod.fst : projectionAmbient X → X) ⁻¹' W),
                y ∈ V → (((arcA1 x hπ1).append (S r).R).proj y).2 0 = 0 →
                L (oldCoordinates ((S r).e y)) = 0 := by
  obtain ⟨hπ1, Φ, J, S, hsrc, hzero, hMask, hS, hAll⟩ :=
    exists_arcPairFamily_with_common_exceptional_trace
      A B hA hB hEB hdim hx A' B' hsA hsB hW hE' hgreater
  refine ⟨hπ1, Φ, J, S, hsrc, hzero, hMask, hS, ?_⟩
  intro r
  obtain ⟨hcA, hcB, facts, hAtlas, hcoords, hparameter, hcommon,
    V, hV, hzV, hVsource, hVdomain, hTrace⟩ := hAll r
  have hfill := eventually_native_trace_iff_exceptionalPlane A hA x Φ hsrc hzero J hMask
    hS r facts.testA hAtlas hcoords facts.nonemptyA
    ((geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).cosupp_subset_N
      facts.mem_cosupp) facts.mem_last V hV hzV hVsource hVdomain
  exact ⟨hcA, hcB, facts, hAtlas, hcoords, hparameter, hcommon, hfill,
    V, hV, hzV, hVsource, hVdomain, hTrace⟩

end

end Hironaka.HironakaG8P1ArcCarrierPlane
