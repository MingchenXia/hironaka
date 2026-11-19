import Hironaka.Resolution.HironakaG1NativeChartValueOrder
import Hironaka.Resolution.HironakaG1NativeBoundaryCodimension
import Hironaka.Resolution.HironakaActualOpenEmbeddingCanonicalExtension

/-! Native graph overlap transport with the geometric codimension-two criterion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CodimensionTwoChartTransport

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  CanonicalCentres ResolutionDriver NormalCrossings DivisorExponentAlong
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaG8LocalTransport HironakaG1NativeBoundaryCodimension
  HironakaG1NativeGraphOverlapRead HironakaG1NativeChartValueOrder
  HironakaNormalCrossingsFiniteMarkedCompletion HironakaOriginalBoundaryEmptyFilterComparison
  AnalyticDimensionBasics

/-- The codimension-two criterion discharges the raw trace condition on
the entire prescribed neighborhood, without inspecting exponent values. -/
theorem native_good_trace_of_codimension_two {n k : ℕ} {X : CMfd.{0} n}
    {P : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hPD : IsInvDomain k P) (U : Opens X)
    (hCodim : ∀ x ∈ P.cosupp, x ∈ U → ∃ p, p + 2 ≤ n ∧ LocDimLE (n := n) D x p) :
    ∀ F ∈ P.E, ∀ x ∈ P.cosupp, x ∈ U → x ∈ F →
      (∀ᶠ y in 𝓝 x, y ∈ F → y ∈ D) →
      ∀ᶠ y in 𝓝 x, y ∈ F → y ∈ P.cosupp := by
  intro F hF x hx hxU hxF hSub
  obtain ⟨p, hp, hDim⟩ := hCodim x hx hxU
  obtain ⟨i, rfl⟩ := List.get_of_mem hF
  obtain ⟨r, hReg, hr⟩ := (snc_member_codimOne_geometry hPD.isWellFormed.isSNCDivisor i).2.2 x hxF
  have hGE := locDimGE_of_regularAtDim_eventually_subset hP.2.1 hReg hSub
  obtain ⟨O, hO, hUpper⟩ := hDim
  obtain ⟨y, hy, b, hb, hWb⟩ := hGE O hO
  have := hUpper y hy b hWb
  omega

/-- There is no supplied normalized exponent identity on successful native
charts whose common closed subset has local codimension at least two. -/
theorem native_codimension_two_zero_normalized {n k l : ℕ} {X : CMfd.{0} n}
    {P Q : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hQ : NativeHSState Q D h)
    (hPD : IsInvDomain k P) (hQD : IsInvDomain l Q) (hE : Q.E = P.E)
    (hCodim : ∀ x ∈ P.cosupp, ∃ p, p + 2 ≤ n ∧ LocDimLE (n := n) D x p) :
    LocWPEquiv P Q ∧ SameCarrierDim P Q ∧
      ∀ F ∈ P.E, ∀ x ∈ P.cosupp, x ∈ F →
        Q.d * divExpAlong n P.N P.ideal F x = P.d * divExpAlong n Q.N Q.ideal F x := by
  refine ⟨locWPEquiv_native hP hQ hE, SameCarrierDim.of_N_eq (hP.2.2.1.trans hQ.2.2.1.symm), ?_⟩
  intro F hF x hx hxF
  obtain ⟨i, rfl⟩ := List.get_of_mem hF
  obtain ⟨h₁, h₂⟩ := independent_native_boundary_exponents_zero_of_local_codimension_two
    hP hQ hPD hQD hE hCodim i x hx hxF
  rw [h₁, h₂, Nat.mul_zero, Nat.mul_zero]

set_option maxHeartbeats 1000000 in
/-- Local codimension two and matching ordered incident germs suffice for a
genuine common refinement. Both literal ordered-boundary records keep
their original canonicality, maximum loci, and attained value order. -/
theorem exists_codimension_two_native_refinement {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {P Q : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hQ : NativeHSState Q D h)
    (hPD : IsInvDomain n P) (hQD : IsInvDomain n Q)
    (V : Opens X) (x : X) (hx : x ∈ V)
    (hMatch : List.Forall₂ (fun F G : Set X => ∀ᶠ y in 𝓝 x, y ∈ F ↔ y ∈ G)
      (P.E.filter (fun F => decide (x ∈ F))) (Q.E.filter (fun F => decide (x ∈ F))))
    (hCodim : ∀ y ∈ P.cosupp, y ∈ V → ∃ p, p + 2 ≤ n ∧ LocDimLE (n := n) D y p) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ V ∧
      let A := CMfd.of (n := n) U
      let L := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) P
      let R := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) Q
      (nonemptyBoundary R).E = (nonemptyBoundary L).E ∧
      ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
        (IsCanonical L ((invFamily hn n).inv L) T ↔ IsCanonical R ((invFamily hn n).inv R) T) ∧
        (IsCanonical L ((invFamily hn n).inv L) T →
          (geoTransformAlong L T).cosupp = (geoTransformAlong R T).cosupp ∧
          maxLocus ((invFamily hn n).inv L T) (geoTransformAlong L T).cosupp =
            maxLocus ((invFamily hn n).inv R T) (geoTransformAlong R T).cosupp ∧
          let E := (geoTransformAlong L T).cosupp
          let f := fun z : E => (invFamily hn n).inv L T z.val
          let g := fun z : E => (invFamily hn n).inv R T z.val
          ∃ e : range f ≃o range g, ∀ z : E, (e ⟨f z, mem_range_self z⟩ : ValTy n) = g z) := by
  obtain ⟨U, hxU, hUV, hE⟩ := exists_refinement_of_ordered_incident_germs
    P Q hPD.isWellFormed hQD.isWellFormed V x hx hMatch
  have hGood := native_good_trace_of_codimension_two hP hPD U
    (fun y hy hyU => hCodim y hy (hUV hyU))
  refine ⟨U, hxU, hUV, hE.symm, fun T => ?_⟩
  have hRead := native_graph_overlap_canonical_and_max hn hP hQ hPD hQD U hE.symm
    (native_graph_trace_on_refinement P hPD.isWellFormed.isCoherent D U hGood) T
  have hFam : canonicalInvariant n = invFamily hn n := by
    cases n with
    | zero => omega
    | succ n => rfl
  rw [hFam] at hRead
  exact ⟨hRead.1, fun hCan => ⟨(hRead.2 hCan).1, (hRead.2 hCan).2,
    native_graph_overlap_attained_order hn hP hQ hPD hQD U hGood hE.symm T hCan⟩⟩

open HironakaG1ActualCommonGraphNativeComparison HironakaG1CommonGraphRestrictionMaps
  HironakaG1IteratedNormalBlockIdeal HironakaG1NativeCoordinateWindow HironakaG1NormalGraphFlags
  HironakaActualOpenEmbeddingCanonicalExtension HironakaActualLocalCommonGraphModel
  HironakaG1IndependentFiniteNormalNative

private def reindexAmbient {m d : ℕ} (X : CMfd.{0} m) (h : m = d) : CMfd.{0} d := by
  letI := chartedSpaceReindex (T := X) h
  letI := isComplexManifoldReindex (T := X) h
  exact CMfd.of (n := d) X

private def reindexRecord {m d : ℕ} {X : CMfd.{0} m}
    (P : MarkedIdeal m X) (h : m = d) : MarkedIdeal d (reindexAmbient X h) := by
  subst d
  exact P

private theorem reindex_domain {m d : ℕ} {X : CMfd.{0} m}
    (P : MarkedIdeal m X) (h : m = d) (hD : IsInvDomain m P) :
    IsInvDomain d (reindexRecord P h) := by
  subst d
  exact hD

/-- Both literal common-chart records inherit their ordinary domains from
their separate finite nonlinear paddings, including the actual block swap
on the right and the original ordered boundary pullbacks. -/
theorem actual_common_graph_domains {a b : ℕ} {A : Opens (ComplexModel a)}
    {B : Opens (ComplexModel b)}
    (P : MarkedIdeal (a + b) (blockOpen A b)) (Q : MarkedIdeal (b + a) (blockOpen B a))
    (hP : IsInvDomain (a + b) P) (hQ : IsInvDomain (b + a) Q) :
    IsInvDomain (a + b) (commonGraphLeftMarked (B := B) P) ∧
      IsInvDomain (a + b) (commonGraphRightMarked (A := A) Q) := by
  let X := CMfd.of (n := a + b) (commonDomain A B)
  let Y₁ := CMfd.of (n := a + b) (blockOpen A b)
  let Y₂ := CMfd.of (n := b + a) (blockOpen B a)
  have h' : IsInvDomain (a + b) (reindexRecord (X := Y₂) Q (Nat.add_comm b a)) :=
    reindex_domain (X := Y₂) Q (Nat.add_comm b a) hQ
  refine ⟨?_, ?_⟩
  · exact isInvDomain_pullback_of_isOpenHoloEmbedding (X := Y₁) (Y := X)
      (commonGraphFirstRestriction (B := B) (le_refl A))
      (commonGraphFirstRestriction_isOpenHoloEmbedding (B := B) (le_refl A)) hP
  · exact isInvDomain_pullback_of_isOpenHoloEmbedding
      (X := reindexAmbient Y₂ (Nat.add_comm b a)) (Y := X)
      (commonGraphSecondRestriction (A := A) (le_refl B))
      (commonGraphSecondRestriction_isOpenHoloEmbedding (A := A) (le_refl B)) h'

open HironakaBaseChange DimensionMonotone AnalyticSubsetPreimage
  HironakaActualIntrinsicIsoPairedWindows HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces CategoryTheory

private theorem coordinate_graph_holomorphic {a b : ℕ} {A : Opens (ComplexModel a)}
    {F : ComplexModel a → ComplexModel b} (hF : ContDiffOn ℂ ∞ F A) :
    ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel b) ∞ (fun x : A => F x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hF.contDiffAt (A.isOpen.mem_nhds x.property)).contMDiffAt)

/-- The actual common graph has dimension at most the first chart's
dimension. Its embedding in the common ambient is the literal open
embedding to the full smooth graph, so this applies to arbitrary analytic
source carrier germs, not only to smooth source varieties. -/
theorem actual_common_graph_dimLE {a b : ℕ} (A : Opens (ComplexModel a))
    (B : Opens (ComplexModel b)) (F : ComplexModel a → ComplexModel b) (D : Set (ComplexModel a))
    (hF : ContDiffOn ℂ ∞ F A) :
    AnalyticDimensionBasics.DimLE (n := a + b) (commonGraphSubset A B F D) a := by
  let X := CMfd.of (n := a + b) (commonDomain A B)
  let Y := CMfd.of (n := a + b) (blockOpen A b)
  let i : X → Y := commonGraphFirstRestriction (B := B) (le_refl A)
  let f : A → ComplexModel b := fun z => F z.val
  let G : Set Y := blockGraph f univ
  have hi := commonGraphFirstRestriction_isOpenHoloEmbedding (B := B) (le_refl A)
  have hf := coordinate_graph_holomorphic hF
  have hG : IsClosedSubmanifold (a + b) G :=
    blockGraph_closed_submanifold hf (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := a) (M := A))
  have hAnal : IsComplexAnalyticSubset (n := a + b) (i ⁻¹' G) :=
    isComplexAnalyticSubset_preimage hi.contMDiff (isComplexAnalyticSubset_of_isClosedSubmanifold hG)
  have hBound : AnalyticDimensionBasics.DimLE (n := a + b) (i ⁻¹' G) a := by
    intro z j hz
    have hReg : RegularAtDim (n := a + b) G (i z) a :=
      regularAtDim_blockGraph_of hf hz.2.1 (AnalyticIrreducibleComponents.regularAtDim_univ _)
    exact (RegularPointDimension.eq_of_regularAtDim hz (hi.regularAtDim_preimage hReg)).le
  apply DimensionMonotone.DimLE.anti hAnal _ hBound
  intro z hz
  exact ⟨mem_univ _, hz.2⟩

set_option maxHeartbeats 1300000 in
/-- Independently padded original charts of possibly different dimensions
give literal common graph records with their domains and a codimension-two
certificate whenever the right block has at least two coordinates. -/
theorem exists_actual_common_graph_codimension_two {a b : ℕ} (hb : 2 ≤ b)
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
      (∀ x : X, LocDimLE (n := a + b) K x a) ∧ a + 2 ≤ a + b := by
  obtain ⟨A, B, F, G, hAU, hBV, hcA, hdB, hF, hG, hLS, hRS, hLd, hRd, _⟩ :=
    exists_actual_commonGraph_native_comparison P Q h hP hPD hQ hQD e he c
  obtain ⟨hD₁, hS₁⟩ := nativeHSState_coordinateWindow hP hPD hAU
  obtain ⟨hD₂, hS₂⟩ := nativeHSState_coordinateWindow hQ hQD hBV
  let P' := MarkedIdeal.pullback (Opens.inclusion hAU) P
  let Q' := MarkedIdeal.pullback (Opens.inclusion hBV) Q
  have hLeft := (blockAmbientMarked_nativeHSState _ (coordinate_graph_holomorphic hF) P' h hS₁ hD₁).1
  have hRight := (blockAmbientMarked_nativeHSState _ (coordinate_graph_holomorphic hG) Q' h hS₂ hD₂).1
  obtain ⟨hLD, hRD⟩ := actual_common_graph_domains _ _ hLeft hRight
  have hDim := actual_common_graph_dimLE A B F (coordinateCarrier C ∩ (A : Set (ComplexModel a))) hF
  exact ⟨A, B, F, G, hAU, hBV, hcA, hdB, hLS, hRS, hLd, hRd, hLD, hRD,
    hDim.locDimLE, by omega⟩

set_option maxHeartbeats 1300000 in
/-- On a selected codimension-two refinement, the actual source and
endpoint tower isomorphisms descend CAN and maxima to the two charts.
The endpoint maps also identify their attained original value orders. -/
theorem codimension_two_native_chart_transport {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {P Q : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hQ : NativeHSState Q D h)
    (hPD : IsInvDomain n P) (hQD : IsInvDomain n Q) (U : Opens X)
    (hE : (nonemptyBoundary (MarkedIdeal.pullback (M' := CMfd.of (n := n) U)
      (Subtype.val : U → X) Q)).E =
      (nonemptyBoundary (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P)).E)
    (hCodim : ∀ x ∈ P.cosupp, x ∈ U → ∃ p, p + 2 ≤ n ∧ LocDimLE (n := n) D x p)
    {Y A₁ A₂ Y₁ Y₂ : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
    (T₁ : BlowupTower A₁ Y₁) (T₂ : BlowupTower A₂ Y₂)
    (e₁ : A₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U)
    (e₂ : A₂ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U)
    (χ₁ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (χ₂ : Y₂ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hi₁ : IsTowerIso e₁ T₁ T χ₁) (hi₂ : IsTowerIso e₂ T₂ T χ₂) :
    let L := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P
    let R := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) Q
    let P₁ := MarkedIdeal.pullback e₁ L
    let Q₂ := MarkedIdeal.pullback e₂ R
    let f : Y₁ → Y₂ := χ₂.symm ∘ χ₁
    let I := invFamily hn n
    (IsCanonical P₁ (I.inv P₁) T₁ ↔ IsCanonical Q₂ (I.inv Q₂) T₂) ∧
    (IsCanonical P₁ (I.inv P₁) T₁ →
      (geoTransformAlong P₁ T₁).cosupp = f ⁻¹' (geoTransformAlong Q₂ T₂).cosupp ∧
      maxLocus (I.inv P₁ T₁) (geoTransformAlong P₁ T₁).cosupp =
        f ⁻¹' maxLocus (I.inv Q₂ T₂) (geoTransformAlong Q₂ T₂).cosupp ∧
      let E := (geoTransformAlong P₁ T₁).cosupp
      let g₁ := fun z : E => I.inv P₁ T₁ z.val
      let g₂ := fun z : E => I.inv Q₂ T₂ (f z.val)
      ∃ o : range g₁ ≃o range g₂, ∀ z : E, (o ⟨g₁ z, mem_range_self z⟩ : ValTy n) = g₂ z) := by
  intro L R P₁ Q₂ f I
  have hGood := native_good_trace_of_codimension_two hP hPD U hCodim
  have hChart := native_graph_overlap_descend_to_charts hn hP hQ hPD hQD U hE hGood
    T T₁ T₂ e₁ e₂ χ₁ χ₂ hi₁ hi₂
  have hCommon := native_graph_overlap_canonical_and_max hn hP hQ hPD hQD U hE
    (native_graph_trace_on_refinement P hPD.isWellFormed.isCoherent D U hGood) T
  have hFam : canonicalInvariant n = invFamily hn n := by
    cases n with
    | zero => omega
    | succ n => rfl
  rw [hFam] at hChart hCommon
  refine ⟨hChart.1, fun hPC => ?_⟩
  obtain ⟨hCos, hMax⟩ := hChart.2 hPC
  refine ⟨hCos, hMax, ?_⟩
  have hL : IsInvDomain n L := InvDomainTowerAlong.isInvDomain_pullback_val U hPD
  have hR : IsInvDomain n R := InvDomainTowerAlong.isInvDomain_pullback_val U hQD
  have hP₁ : IsInvDomain n P₁ := InvDomainTowerAlong.isInvDomain_pullback e₁ hL
  have hLC := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
    (X := A₁) (X' := CMfd.of (n := n) U) I hP₁ e₁.symm (T' := T) (χ := χ₁.symm) hi₁.symm hPC
  rw [pullback_symm_pullback e₁ hL.isWellFormed.isCoherent] at hLC
  have hRC := hCommon.1.mp hLC
  have hCosCommon := (hCommon.2 hLC).1
  have hLT := I.isInvValue.isGeoTestTower_of_isCanonical hL T hLC
  have hPre := IsTowerIso.cosupp_geoTransformAlong e₁ hL.isWellFormed.isClosedSubmanifold_N
    hL.isWellFormed.isCoherent hi₁ hLT
  obtain ⟨o, hO⟩ := native_graph_overlap_attained_order hn hP hQ hPD hQD U hGood hE T hLC
  let E := (geoTransformAlong P₁ T₁).cosupp
  let g₁ (z : E) := I.inv P₁ T₁ z.val
  let g₂ (z : E) := I.inv Q₂ T₂ (f z.val)
  let liftPoint (z : E) : (geoTransformAlong L T).cosupp :=
    ⟨χ₁ z.val, show z.val ∈ χ₁ ⁻¹' (geoTransformAlong L T).cosupp from hPre ▸ z.property⟩
  have hValues (z : E) : g₁ z = I.inv L T (liftPoint z).val ∧ g₂ z = I.inv R T (liftPoint z).val := by
    have hz := (liftPoint z).property
    refine ⟨I.isInvValue.towerIso e₁ L hL T₁ T χ₁ hi₁ hLC z.val hz, ?_⟩
    have hz' : χ₂ (f z.val) ∈ (geoTransformAlong R T).cosupp := by
      simpa [f] using (hCosCommon ▸ hz)
    have hv := I.isInvValue.towerIso e₂ R hR T₂ T χ₂ hi₂ hRC (f z.val) hz'
    simpa [f, liftPoint, g₂, Q₂] using hv
  have hOrd (z w : E) : g₁ z < g₁ w ↔ g₂ z < g₂ w := by
    rw [(hValues z).1, (hValues w).1, (hValues z).2, (hValues w).2]
    have hx := hO (liftPoint z)
    have hy := hO (liftPoint w)
    have hlt := o.lt_iff_lt (x := ⟨I.inv L T (liftPoint z).val, mem_range_self (liftPoint z)⟩)
      (y := ⟨I.inv L T (liftPoint w).val, mem_range_self (liftPoint w)⟩)
    change (o ⟨I.inv L T (liftPoint z).val, mem_range_self (liftPoint z)⟩ : ValTy n) <
      (o ⟨I.inv L T (liftPoint w).val, mem_range_self (liftPoint w)⟩ : ValTy n) ↔ _ at hlt
    rw [hx, hy] at hlt
    exact hlt.symm
  exact ⟨attainedValueOrderIso g₁ g₂ hOrd, attainedValueOrderIso_apply g₁ g₂ hOrd⟩

end Hironaka.HironakaG1CodimensionTwoChartTransport
