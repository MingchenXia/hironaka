import Hironaka.Resolution.HironakaG8P1ArcCarrierPlane
import Hironaka.Resolution.HironakaG8P1ArcOrderTwo
import Hironaka.Analytic.MeteredDivisorSingleGenerator
import Hironaka.Invariant.MemberInterTowerAlong

/-!
# Case N: producing a sharp arc-trace point away from finite linear kernels

This module constructs the Case N sharp point from ordinary native pair and
natural order-two nontangency inputs. It does not assert the later restriction/
P1 comparison, the full Case N equivalence, or original G8/G11 goal closure.

The linear-avoidance core isolates the genuine relative-open sharp locus.
The last theorem reads its order bound from an actual count and selects its
finite proper derivative kernels from the natural original order-two
nontangency hypothesis. It constructs points off the literal original strict
members from ordinary pair inputs, without a sharp point, protection packet,
or order certificate as an assumption. Restriction/P1 is still pending.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8CaseNGenericPoint

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong GermIdealOrder
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower HironakaG8P1ArcPair
  HironakaG8P1ArcPairTrace HironakaG8P1ArcCarrierPlane HironakaG8P1ArcTangentTrace

open ResolutionInvariantSpec (IsInvDomain)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open HironakaG11InvBMClass (SameCarrierDim)
open MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open scoped Hironaka.ProductComplexManifold

/-- The literal mask plane, as a complex submodule with its native subtype
topology. This adds no geometric assumption to `coordSubspace`. -/
def maskSubmodule {n : ℕ} (J : Finset (Fin n)) : Submodule ℂ (ComplexModel n) where
  carrier := coordSubspace J
  zero_mem' := by
    intro i _hi
    simp
  add_mem' := by
    intro v w hv hw i hi
    simp only [PiLp.add_apply, hv i hi, hw i hi, add_zero]
  smul_mem' := by
    intro c v hv i hi
    simp only [PiLp.smul_apply, smul_eq_mul, hv i hi, mul_zero]

/-- The existing old-coordinate function with its actual continuous linear
map structure, so scalar equations can be restricted to the stage plane. -/
def oldCoordinatesCLM (n : ℕ) : ComplexModel (n+1) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).comp
    (ProductComplexManifold.prodModelEquiv n 1).symm.toContinuousLinearMap

/-- The natural order-two nontangency hypothesis selects an actual original
vanishing germ with nonzero derivative on the retained original frame plane.
The level equation is made globally qualified by the checked local extension;
its derivative and germ remain those of the actual selected function. -/
theorem exists_flat_equation_nonzero_of_notTangent
    {n r : ℕ} {X : CMfd.{u} n} {N H : Set X} {x : X}
    (hN : RegularAtDim (n := n) N x r) (hxH : x ∈ H)
    (hNot : x ∉ cosupport n N (vanishingIdeal (n := n) H) 2)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (J : Finset (Fin n))
    (hMask : ∀ w ∈ flatDomain Φ, w ∈ N ↔
      Φ.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J) :
    ∃ (g : ComplexModel n → ℂ) (L : ComplexModel n →L[ℂ] ℂ),
      HasFDerivAt g L 0 ∧
      (∀ w ∈ H, w ∈ flatDomain Φ →
        g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0) ∧
      ∃ v ∈ coordSubspace J, L v ≠ 0 := by
  obtain ⟨f, hf, ξ, hξ, hDiff⟩ :=
    HironakaG8P1ArcOrderTwo.exists_vanishing_germ_tangent_derivative_of_not_cosupport
      hN hxH hNot
  let g : ComplexModel n → ℂ := f ∘ GiraudAlong.flatInv Φ
  let L := fderiv ℂ g 0
  have hg : DifferentiableAt ℂ g 0 :=
    GiraudAlong.differentiableAt_comp_flatInv (GiraudAlong.zero_mem_target hzero) hsrc
      (by rw [GiraudAlong.flatInv_zero hzero]; exact hf.1)
  have hfx : f x = 0 := hf.2.self_of_nhds hxH
  have hLocal : ∀ᶠ w in 𝓝 x, w ∈ H → w ∈ flatDomain Φ →
      g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0 := by
    filter_upwards [hf.2] with w hw hwH hwDom
    change f (GiraudAlong.flatInv Φ (GiraudAlong.flatMap Φ w)) =
      f (GiraudAlong.flatInv Φ 0)
    rw [GiraudAlong.flatInv_flatMap hwDom, GiraudAlong.flatInv_zero hzero, hw hwH, hfx]
  obtain ⟨g', _hAgree, hg', hEquation⟩ :=
    HironakaG8P1ArcOriginalTangent.exists_global_level_equation_of_local
      x H Φ hsrc hzero g L hg.hasFDerivAt hLocal
  let v := fderiv ℂ (BlowupSpaceTangent.flatMap Φ x)
    (chartAt (ComplexModel n) x x) ξ
  have hv : v ∈ coordSubspace J :=
    HironakaG8P1ArcNativeTangent.map_tangent_mem_coordSubspace N x Φ hsrc J hMask hξ
  refine ⟨g', L, hg', hEquation, v, hv, ?_⟩
  intro hLv
  apply hDiff
  rw [HironakaG8P1ArcNativeTangent.germDiff_eq_fderiv_flatRepresentative_comp
    x Φ hsrc hzero hf.1, ContinuousLinearMap.comp_apply]
  exact hLv

/-- Every nonempty open part of a linear subspace contains a point avoiding
finitely many linear kernels, provided each restriction is nonzero. The open
part is an input; the point and simultaneous nonvanishing are produced. -/
theorem exists_mem_open_forall_linear_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Ξ : Submodule ℂ V) {ι : Type*} (s : Finset ι) (L : ι → V →L[ℂ] ℂ)
    (hProper : ∀ i ∈ s, ∃ v ∈ Ξ, L i v ≠ 0)
    {U : Set Ξ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ v ∈ U, ∀ i ∈ s, L i (v : V) ≠ 0 := by
  classical
  let f : ι → Ξ → ℂ := fun i v => L i v
  have hCont : ∀ i ∈ s, ContinuousOn (f i) (univ : Set Ξ) := by
    intro i _hi
    exact ((L i).continuous.comp continuous_subtype_val).continuousOn
  have hNowhere : ∀ i ∈ s,
      MeteredDivisorSingleGenerator.NowhereIdenticallyZeroOn (f i) (univ : Set Ξ) := by
    intro i hi W hW _hWsub hWne
    by_contra hAll
    push Not at hAll
    let K : Submodule ℂ Ξ := ((L i).comp Ξ.subtypeL).ker
    have hWK : W ⊆ (K : Set Ξ) := by
      intro v hv
      exact hAll v hv
    obtain ⟨v₀, hv₀⟩ := hWne
    have hInt : (interior (K : Set Ξ)).Nonempty :=
      ⟨v₀, interior_mono hWK (by simpa only [hW.interior_eq] using hv₀)⟩
    have hTop : K = ⊤ := Submodule.eq_top_of_nonempty_interior' K hInt
    obtain ⟨v, hv, hLv⟩ := hProper i hi
    apply hLv
    have hvK : (⟨v, hv⟩ : Ξ) ∈ K := by
      rw [hTop]
      exact Submodule.mem_top
    exact hvK
  obtain ⟨W, _hWopen, hWU, hWne, hWall⟩ :=
    MeteredDivisorSingleGenerator.exists_open_forall_ne_zero s isOpen_univ
      hCont hNowhere hU (subset_univ U) hUne
  obtain ⟨v, hv⟩ := hWne
  exact ⟨v, hWU hv, fun i hi => hWall i hi v hv⟩

/-- A germ of a charted linear trace which is not generically contained in a
closed high-order locus has a point outside that locus and all finitely many
proper linear kernels in every neighborhood. No sharp point is assumed. -/
theorem exists_sharp_trace_point_avoiding_finite_kernels
    {Z V : Type*} [TopologicalSpace Z] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (e : OpenPartialHomeomorph Z V) (Ξ : Submodule ℂ V)
    {z : Z} {C K : Set Z} (hK : IsClosed K)
    (hTrace : ∀ᶠ y in 𝓝 z, y ∈ C ↔ y ∈ e.source ∧ e y ∈ Ξ)
    (hNotHigh : ¬ ∀ᶠ y in 𝓝 z, y ∈ C → y ∈ K)
    {ι : Type*} (s : Finset ι) (L : ι → V →L[ℂ] ℂ)
    (hProper : ∀ i ∈ s, ∃ v ∈ Ξ, L i v ≠ 0)
    {O : Set Z} (hO : O ∈ 𝓝 z) :
    ∃ y ∈ O, y ∈ C ∧ y ∉ K ∧ y ∈ e.source ∧ ∀ i ∈ s, L i (e y) ≠ 0 := by
  obtain ⟨N, hNsub, hNopen, hzN⟩ := mem_nhds_iff.mp
    (inter_mem hO hTrace)
  have hWitness : ∃ y, y ∈ N ∧ y ∈ C ∧ y ∉ K := by
    by_contra! hNone
    apply hNotHigh
    filter_upwards [hNopen.mem_nhds hzN] with y hy hyC
    exact hNone y hy hyC
  obtain ⟨y₀, hy₀N, hy₀C, hy₀K⟩ := hWitness
  let W : Set Z := (N \ K) ∩ e.source
  have hWopen : IsOpen W := (hNopen.inter hK.isOpen_compl).inter e.open_source
  have hWsource : W ⊆ e.source := inter_subset_right
  let U : Set Ξ := (Subtype.val : Ξ → V) ⁻¹' (e '' W)
  have hUopen : IsOpen U :=
    (e.isOpen_image_of_subset_source hWopen hWsource).preimage continuous_subtype_val
  have hy₀source : y₀ ∈ e.source := ((hNsub hy₀N).2.mp hy₀C).1
  have hy₀plane : e y₀ ∈ Ξ := ((hNsub hy₀N).2.mp hy₀C).2
  have hUne : U.Nonempty :=
    ⟨⟨e y₀, hy₀plane⟩, y₀, ⟨⟨hy₀N, hy₀K⟩, hy₀source⟩, rfl⟩
  obtain ⟨v, hvU, hvL⟩ :=
    exists_mem_open_forall_linear_ne_zero Ξ s L hProper hUopen hUne
  obtain ⟨y, hyW, hey⟩ := hvU
  have hyPlane : e y ∈ Ξ := hey.symm ▸ v.property
  have hyC : y ∈ C := (hNsub hyW.1.1).2.mpr ⟨hyW.2, hyPlane⟩
  exact ⟨y, (hNsub hyW.1.1).1, hyC, hyW.1.2, hyW.2,
    fun i hi => by rw [hey]; exact hvL i hi⟩

/-- The literal A count of one actual common arc stage produces a sharp
point on the literal last trace away from finitely many proper kernels.
The high-order exclusion is derived internally from the exact count. -/
theorem exists_arc_stage_sharp_point_avoiding_finite_kernels
    {n kA : ℕ} {X : CMfd.{u} n} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A)
    (A' : MarkedIdeal (n+1) (projectionAmbient X))
    {Z : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z}
    {z : Z} {x : X} {r : ℕ} (facts : ArcPairStageFacts A B A' T z x r)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (Ξ : Submodule ℂ (ComplexModel (n+1)))
    (hTrace : ∀ᶠ y in 𝓝 z,
      y ∈ (geoTransformAlong (projectionTest A) T).N ∩
        (geoTransformAlong (projectionTest A) T).E.getLast facts.nonemptyA ↔
      y ∈ e.source ∧ e y ∈ Ξ)
    {ι : Type*} (s : Finset ι) (L : ι → ComplexModel (n+1) →L[ℂ] ℂ)
    (hProper : ∀ i ∈ s, ∃ v ∈ Ξ, L i v ≠ 0)
    {O : Set Z} (hO : O ∈ 𝓝 z) :
    ∃ y ∈ O,
      y ∈ (geoTransformAlong (projectionTest A) T).N ∩
        (geoTransformAlong (projectionTest A) T).E.getLast facts.nonemptyA ∧
      y ∉ cosupport (n+1) (geoTransformAlong (projectionTest A) T).N
        (geoTransformAlong (projectionTest A) T).ideal
        ((r+1) * (ordinaryTraceOrder A.N A.ideal x - A.d) + 1) ∧
      y ∈ e.source ∧ ∀ i ∈ s, L i (e y) ≠ 0 := by
  let QA := geoTransformAlong (projectionTest A) T
  let D := QA.E.getLast facts.nonemptyA
  let β := (r+1) * (ordinaryTraceOrder A.N A.ideal x - A.d)
  have hQA : IsInvDomain (kA+1) QA :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong
      (projection_test_isInvDomain A hA) T facts.testA
  have hClosed : IsClosed (cosupport (n+1) QA.N QA.ideal (β+1)) :=
    GiraudAlong.isClosed_cosupport_along hQA.isWellFormed.isCoherent
      hQA.isWellFormed.isClosedSubmanifold_N (β+1)
  have hNotHigh : ¬ ∀ᶠ y in 𝓝 z,
      y ∈ QA.N ∩ D → y ∈ cosupport (n+1) QA.N QA.ideal (β+1) := by
    intro h
    have hDiv : IsDivNearAlong (n+1) QA.N QA.ideal D (β+1) z := by
      filter_upwards [h] with y hy hyN hyD
      exact hy ⟨hyN, hyD⟩
    have hBound := (facts.exponentA (β+1)).mp hDiv
    change β+1 ≤ β at hBound
    omega
  exact exists_sharp_trace_point_avoiding_finite_kernels
    e Ξ hClosed hTrace hNotHigh s L hProper hO

/-- Ordinary native pair data and the natural original order-two nontangency
conditions construct sharp-order arc-trace points avoiding every literal
original strict member. The original finite family is only required to be
closed: SNC suffices for this hypothesis, without carrier transversality.

The point, its sharp A bound, its B lower count, and all boundary avoidance
are conclusions. The actual family, counts, frame, derivative equations, and
relative-open avoidance are constructed internally. Restriction/P1 is not
asserted here. -/
theorem exists_arcFamily_with_sharp_point_off_original_members
    {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x)
    (F : List (Set X)) (hClosed : ∀ H ∈ F, IsClosed H)
    (hNotTangent : ∀ H ∈ F, x ∈ H →
      x ∉ cosupport n A.N (vanishingIdeal (n := n) H) 2) :
    ∃ (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
      (S : ℕ → ArcStage n (arcY1 x)), IsArcFamily x hπ1 S ∧
      ∀ r, A.d ≤ r+1 →
        ∃ facts : ArcPairStageFacts A B A' ((arcA1 x hπ1).append (S r).R) (S r).z x r,
        ∀ O : Set (S r).Z, O ∈ 𝓝 (S r).z →
        ∃ y ∈ O,
          y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).N ∩
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
              facts.nonemptyA ∧
          y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).cosupp ∧
          y ∉ cosupport (n+1)
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).N
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).ideal
            ((r+1) * (ordinaryTraceOrder A.N A.ideal x - A.d) + 1) ∧
          y ∈ cosupport (n+1)
            (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).N
            (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).ideal
            ((r+1) * (ordinaryTraceOrder B.N B.ideal x - B.d)) ∧
          ∀ H ∈ F, y ∉ strictAlong
            ((arcA1 x hπ1).append (S r).R)
            ((Prod.fst : projectionAmbient X → X) ⁻¹' H) := by
  classical
  obtain ⟨hπ1, Φ, J, S, hsrc, hzero, hMask, hS, hAll⟩ :=
    exists_arcPairFamily_with_filled_exceptional_trace
      A B hA hB hEB hdim hx A' B' hsA hsB hW hE' hgreater
  obtain ⟨k, hRegular⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 x
    (A.cosupp_subset_N hx)
  let I := {i : Fin F.length // x ∈ F.get i}
  have hEquations : ∀ i : I,
      ∃ (g : ComplexModel n → ℂ) (L : ComplexModel n →L[ℂ] ℂ),
        HasFDerivAt g L 0 ∧
        (∀ w ∈ F.get i.val, w ∈ flatDomain Φ →
          g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0) ∧
        ∃ v ∈ coordSubspace J, L v ≠ 0 := by
    intro i
    exact exists_flat_equation_nonzero_of_notTangent hRegular i.property
      (hNotTangent _ (List.get_mem F i.val) i.property) Φ hsrc hzero J hMask
  choose g L hg hEquation hProper using hEquations
  refine ⟨hπ1, S, hS, ?_⟩
  intro r hSize
  obtain ⟨_hcA, _hcB, facts, _hAtlas, _hcoords, hParameter, hCommon, hFill,
    V, hVopen, hzV, _hVsource, _hVdomain, hScalarTrace⟩ := hAll r
  let T := (arcA1 x hπ1).append (S r).R
  let QA := geoTransformAlong (projectionTest A) T
  let QB := geoTransformAlong (projectionTest B) T
  let D := QA.E.getLast facts.nonemptyA
  let βA := (r+1) * (ordinaryTraceOrder A.N A.ideal x - A.d)
  let βB := (r+1) * (ordinaryTraceOrder B.N B.ideal x - B.d)
  let Ξ := maskSubmodule (exceptionalMask J)
  let Lstage : I → ComplexModel (n+1) →L[ℂ] ℂ :=
    fun i => (L i).comp (oldCoordinatesCLM n)
  have hProperStage : ∀ i ∈ (Finset.univ : Finset I),
      ∃ w ∈ Ξ, Lstage i w ≠ 0 := by
    intro i _hi
    obtain ⟨v, hv, hLv⟩ := hProper i
    let w := ProductComplexManifold.prodModelEquiv n 1 (v, 0)
    have hOld : oldCoordinatesCLM n w = v := by
      change ((ProductComplexManifold.prodModelEquiv n 1).symm
        (ProductComplexManifold.prodModelEquiv n 1 (v, 0))).1 = v
      rw [ContinuousLinearEquiv.symm_apply_apply]
    have hLast : w (Fin.last n) = 0 := by
      have hp := (ProductComplexManifold.prodModelEquiv_mem_complexCoordinatePlane_iff
        v (0 : ComplexModel 1)).mpr rfl
      exact hp (Fin.last n) (by simp)
    have hwPlane : w ∈ Ξ := by
      apply (mem_exceptionalMask_iff J w).mpr
      refine ⟨?_, hLast⟩
      change oldCoordinatesCLM n w ∈ coordSubspace J
      rw [hOld]
      exact hv
    refine ⟨w, hwPlane, ?_⟩
    simpa only [Lstage, ContinuousLinearMap.comp_apply, hOld] using hLv
  have hβA : A.d ≤ βA := by
    have hGap : 1 ≤ ordinaryTraceOrder A.N A.ideal x - A.d := by omega
    have hMul := Nat.mul_le_mul_left (r+1) hGap
    exact hSize.trans (by simpa only [Nat.mul_one] using hMul)
  have hDivA := (facts.exponentA A.d).mpr hβA
  have hDivB := (facts.exponentB βB).mpr (le_refl βB)
  have hMark : ∀ᶠ y in 𝓝 (S r).z, y ∈ QA.N ∩ D → y ∈ QA.cosupp := by
    filter_upwards [hDivA] with y hy hyC
    change y ∈ cosupport (n+1) QA.N QA.ideal QA.d
    have hdA : QA.d = A.d := d_geoTransformAlong (projectionTest A) T
    rw [hdA]
    exact hy hyC.1 hyC.2
  have hCountB : ∀ᶠ y in 𝓝 (S r).z,
      y ∈ QA.N ∩ D → y ∈ cosupport (n+1) QB.N QB.ideal βB := by
    filter_upwards [hCommon hSize, hDivB] with y hCommonY hDivY hyC
    have hyB := hCommonY.mp hyC
    exact hDivY hyB.1 hyB.2
  have hMissing : ∀ᶠ y in 𝓝 (S r).z, ∀ i : Fin F.length,
      x ∉ F.get i → y ∉ strictAlong T
        ((Prod.fst : projectionAmbient X → X) ⁻¹' F.get i) := by
    apply eventually_all.mpr
    intro i
    by_cases hxH : x ∈ F.get i
    · exact Eventually.of_forall fun _ hNot => False.elim (hNot hxH)
    · have hHi : IsClosed ((Prod.fst : projectionAmbient X → X) ⁻¹' F.get i) :=
        (hClosed _ (List.get_mem F i)).preimage continuous_fst
      have hzNot : (S r).z ∉ strictAlong T
          ((Prod.fst : projectionAmbient X → X) ⁻¹' F.get i) := by
        intro hzStrict
        have hzBase := MemberInterTowerAlong.strictAlong_subset_preimage T hHi hzStrict
        change (T.proj (S r).z).1 ∈ F.get i at hzBase
        rw [(hS.arc r).proj_eq.1] at hzBase
        exact hxH hzBase
      have hOpen := (MemberInterTowerAlong.isClosed_strictAlong T hHi).isOpen_compl
      filter_upwards [hOpen.mem_nhds hzNot] with y hy _hNot
      exact hy
  have hLocal : ∀ᶠ y in 𝓝 (S r).z,
      y ∈ V ∧ (y ∈ QA.N ∩ D → y ∈ QA.cosupp) ∧
      (y ∈ QA.N ∩ D → y ∈ cosupport (n+1) QB.N QB.ideal βB) ∧
      (∀ i : Fin F.length, x ∉ F.get i →
        y ∉ strictAlong T
          ((Prod.fst : projectionAmbient X → X) ⁻¹' F.get i)) := by
    filter_upwards [hVopen.mem_nhds hzV, hMark, hCountB, hMissing]
      with y hyV hyMark hyCount hyMissing
    exact ⟨hyV, hyMark, hyCount, hyMissing⟩
  refine ⟨facts, ?_⟩
  intro O hO
  have hO' : (O ∩ {y | y ∈ V ∧ (y ∈ QA.N ∩ D → y ∈ QA.cosupp) ∧
      (y ∈ QA.N ∩ D → y ∈ cosupport (n+1) QB.N QB.ideal βB) ∧
      (∀ i : Fin F.length, x ∉ F.get i →
        y ∉ strictAlong T
          ((Prod.fst : projectionAmbient X → X) ⁻¹' F.get i))}) ∈ 𝓝 (S r).z :=
    inter_mem hO hLocal
  have hTrace : ∀ᶠ y in 𝓝 (S r).z,
      y ∈ QA.N ∩ D ↔ y ∈ (S r).e.source ∧ (S r).e y ∈ Ξ := hFill
  obtain ⟨y, hyO, hyC, hySharp, _hySource, hyKernels⟩ :=
    exists_arc_stage_sharp_point_avoiding_finite_kernels A B hA A' facts
      (S r).e Ξ hTrace Finset.univ Lstage hProperStage hO'
  refine ⟨y, hyO.1, hyC, hyO.2.2.1 hyC, hySharp, hyO.2.2.2.1 hyC, ?_⟩
  intro H hHF hyStrict
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hHF
  by_cases hxH : x ∈ F.get i
  · let j : I := ⟨i, hxH⟩
    have hZero := hScalarTrace (F.get i) (hClosed _ (List.get_mem F i))
      (g j) (L j) (hg j) (hEquation j) y hyStrict hyO.2.1
      (hParameter y hyC.2)
    exact hyKernels j (Finset.mem_univ j) hZero
  · exact hyO.2.2.2.2 i hxH hyStrict

end

end Hironaka.HironakaG8CaseNGenericPoint
