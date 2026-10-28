/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualZeroCoordinateContactSeed
import Hironaka.Resolution.HironakaActualSectionInitialValues

set_option autoImplicit false

/-!
# Initial full ambient zero-coordinate recoding

Blueprint: `hironaka-disjoint-zero-coordinate-initial-recoding.tex`.
The stabilized marked ideal has the FULL ambient carrier. Its initial canonical
value is compared with the original value at one lower recursive depth. This
module does not assert stabilization of finite histories or intrinsic descent.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaDisjointZeroCoordinateInitialRecoding
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaActualZeroCoordinateContactSeed HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  GermIdealOrder RelativePrincipalizationSpan GermIdealPullbackCalculus
  InvertibleIdealQuotient IdealWeightPowers DivisorExponentAlong
  HomogenizedIdealAlong StepOneValue StepOneRegime StepOneLowerDomain
  HironakaSharpOriginalProductTraceOrder RestrictedIdealExtension InvDomainRebase
  CanonicalCentres ContactStageKept HironakaSmoothSubmersionOrderedChoiceImageTrace
  GeneralValue NonmonomialOrderTail MonomialPartAlong CompanionReductionAlong
open ResolutionInvariantSpec (IsInvDomain DimLE)

private abbrev model (n : ℕ) : CMfd n := CMfd.of (n := n) (ComplexModel n)

variable {n : ℕ}

/-- The original full-carrier, empty-boundary, marking-one input. -/
def baseMarked (W : Set (ComplexModel n)) : MarkedIdeal n (ComplexModel n) :=
  ⟨univ, [], vanishingIdeal (n := n) W, 1⟩

/-- The literal finite right branch, with constant new order and level. -/
def initialEmbedding (q : ℕ) : ValTy q ↪o ValTy (q + 1) :=
  OrderEmbedding.ofStrictMono
    (fun v => toLex (1, Sum.inrₗ
      (((toLex (0, (v : WithTop (ValTy q)))) : ℕ ×ₗ WithTop (ValTy q)) :
        WithTop (ℕ ×ₗ WithTop (ValTy q))))) (by
      intro a b h
      apply Prod.Lex.toLex_lt_toLex.mpr
      refine Or.inr ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr ?_)⟩
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, WithTop.coe_lt_coe.mpr h⟩))

private theorem zeroPlane_section (x : ComplexModel n) : tangentInclusion n 1 x ∈ zeroPlane n := by
  simp [zeroPlane]

private theorem section_projection {z : ComplexModel (n+1)} (hz : z ∈ zeroPlane n) :
    tangentInclusion n 1 (tangentProjection n 1 z) = z := by
  have hq : actualJointNormalProjection n 1 z = 0 := hz
  simpa only [HironakaActualIntrinsicStableAmbientIso.join, hq, map_zero, add_zero] using (join_projections (n := n) (m := 1) z)

private theorem coordinate_zero_iff (z : ComplexModel (n+1)) :
    addedCoordinate n z = 0 ↔ z ∈ zeroPlane n := by
  constructor
  · intro h
    change actualJointNormalProjection n 1 z = 0
    ext i
    obtain rfl : i = 0 := Fin.eq_zero i
    simpa [addedCoordinate, HironakaActualGraphFunctionalIdeal.graphFunction, zeroFunction] using h
  · intro h
    simpa [addedCoordinate, HironakaActualGraphFunctionalIdeal.graphFunction, zeroFunction] using
      congrArg (fun w : ComplexModel 1 => w 0) h

private theorem stabilized_coherent {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) : (zeroIdeal W).IsCoherent := by
  apply CartanIrreducible.cartanCoherence
  have hp := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (tangentProjection n 1).contMDiff hW
  have hq := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (actualJointNormalProjection n 1).contMDiff
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))
  exact hp.inter hq

private theorem pullback_mem_comp {a b : ℕ} {X : CMfd a} {Y : CMfd b}
    (f : Y → X) (hf : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel a) ∞ f)
    {I : GermIdeal a X} (hI : I.IsCoherent) {x : Y} {g : X → ℂ} (hg : I.mem (f x) g) :
    (GermIdeal.pullback (m := b) f I).mem x (g ∘ f) :=
  GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g, hg, rfl⟩
    ((GermIdeal.IsCoherent.holomorphicAt_mem hI hg).comp_contMDiff
      (Eventually.of_forall fun _ => hf.contMDiffAt)))

private theorem pullback_cosupport_one {a b : ℕ} {X : CMfd a} {Y : CMfd b}
    (f : Y → X) (hf : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel a) ∞ f)
    {I : GermIdeal a X} (hI : I.IsCoherent) (x : Y) :
    x ∈ cosupport b univ (GermIdeal.pullback (m := b) f I) 1 ↔
      f x ∈ cosupport a univ I 1 := by
  rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_pullback hf hI) hg),
    cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  simp only [mem_inter_iff, mem_univ, true_and]
  constructor
  · intro h g hg
    exact h (g ∘ f) (pullback_mem_comp f hf hI hg)
  · intro h g hg
    obtain ⟨_, K, s, a, hs, _, he⟩ := GermIdeal.mem_pullback_iff.mp hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨t, ht, hst⟩ := hs i
    rw [hst, Function.comp_apply, h t ht, mul_zero]

private theorem base_dim_le {q : ℕ} {W : Set (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked W)) : n ≤ q := by
  obtain ⟨j, hj, hreg⟩ := hM.dimLE 0 (mem_univ _)
  have he := RegularPointDimension.eq_of_regularAtDim hreg
    (AnalyticIrreducibleComponents.regularAtDim_univ (0 : ComplexModel n))
  exact he ▸ hj

private theorem base_comp_mem {W : Set (ComplexModel n)} {z : ComplexModel (n+1)}
    {g : ComplexModel n → ℂ} (hg : (vanishingIdeal (n := n) W).mem (tangentProjection n 1 z) g) :
    (zeroIdeal W).mem z (g ∘ tangentProjection n 1) := by
  refine ⟨hg.1.comp_contMDiff (Eventually.of_forall fun _ => (tangentProjection n 1).contMDiffAt), ?_⟩
  filter_upwards [(tangentProjection n 1).continuous.continuousAt.eventually hg.2] with y hy hyW
  exact hy hyW.1

private theorem projection_frequently {z : ComplexModel (n+1)} {g : ComplexModel n → ℂ}
    (h : ∃ᶠ y in 𝓝 (tangentProjection n 1 z), g y ≠ 0) :
    ∃ᶠ y in 𝓝 z, g (tangentProjection n 1 y) ≠ 0 := by
  by_contra hn
  have hn' := not_frequently.mp hn
  let f : ComplexModel n → ComplexModel (n+1) := fun x => HironakaActualIntrinsicStableAmbientIso.join x (actualJointNormalProjection n 1 z)
  have hf : Continuous f := (tangentInclusion n 1).continuous.add continuous_const
  have hfx : f (tangentProjection n 1 z) = z := join_projections z
  have ht : Tendsto f (𝓝 (tangentProjection n 1 z)) (𝓝 z) := by
    simpa only [hfx] using hf.tendsto (tangentProjection n 1 z)
  apply h
  filter_upwards [ht.eventually hn'] with y hy
  simpa only [f, first_join] using hy

/-- The actual full ambient stabilized record lies in the next dimension domain. -/
theorem stabilized_isInvDomain {q : ℕ} {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W)) :
    IsInvDomain (q+1) (zeroMarked W) := by
  have hc := stabilized_coherent hW
  have hN : IsClosedSubmanifold (n+1) (univ : Set (ComplexModel (n+1))) :=
    ⟨isClosed_univ, fun x _ => ⟨n+1, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  refine ⟨⟨hN, hc, NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hN⟩,
    fun x _ => ⟨n+1, Nat.add_le_add_right (base_dim_le hM) 1,
      AnalyticIrreducibleComponents.regularAtDim_univ x⟩, le_rfl, ?_⟩
  intro z _
  obtain ⟨g, hg, hf⟩ := hM.isNonzeroAlongAt (tangentProjection n 1 z) (mem_univ _)
  refine ⟨g ∘ tangentProjection n 1, base_comp_mem hg, ?_⟩
  have hf' : ∃ᶠ y in 𝓝 (tangentProjection n 1 z), g y ≠ 0 := hf.mono fun _ hy => hy.2
  exact (projection_frequently hf').mono fun _ hy => ⟨mem_univ _, hy⟩

/-- The entire stabilized cosupport is the literal zero-section image of the old cosupport. -/
theorem stabilized_cosupport {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    (zeroMarked W).cosupp = zeroCarrier (baseMarked W).cosupp := by
  have hc := stabilized_coherent hW
  have htrace := zero_section_pullback W
  have hsec (x : ComplexModel n) :
      tangentInclusion n 1 x ∈ (zeroMarked W).cosupp ↔ x ∈ (baseMarked W).cosupp := by
    have h := pullback_cosupport_one (X := model (n+1)) (Y := model n)
      (tangentInclusion n 1) (tangentInclusion n 1).contMDiff hc x
    rw [htrace] at h
    exact h.symm
  ext z
  constructor
  · intro hz
    have hcoord := (zero_coordinate_tangent W).cosupport_inter_subset
      (fun x g (hg : (zeroIdeal W).mem x g) => hg.1) (by rfl) ⟨hz, mem_univ _⟩
    have hplane := (coordinate_zero_iff z).mp hcoord
    refine ⟨?_, hplane⟩
    apply (hsec _).mp
    rwa [section_projection hplane]
  · rintro ⟨hx, hplane⟩
    have hs := (hsec _).mpr hx
    rwa [section_projection hplane] at hs

/-- The full ambient nonmonomial order at every stabilized cosupport point is one. -/
theorem stabilized_order_one {q : ℕ} {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W))
    {z : ComplexModel (n+1)} (hz : z ∈ (zeroMarked W).cosupp) :
    NonmonomialOrderLocal.nmOrd (M := model (n+1)) (zeroMarked W) z = 1 := by
  have hd := stabilized_isInvDomain hW hM
  have hc := stabilized_coherent hW
  have hl : 1 ≤ NonmonomialOrderLocal.nmOrd (M := model (n+1)) (zeroMarked W) z := by
    apply (NonmonomialOrderLocal.mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt (mem_univ _) 1).mp
    change z ∈ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked (X := model (n+1)) univ (zeroIdeal W)) 1
    rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (zeroIdeal W) hc 1]
    exact hz
  have hu := NonmonomialOrderLocal.nmOrd_le_of_notMem (M := model (n+1))
    (𝔪 := (zeroMarked W : MarkedIdeal (n+1) (model (n+1)))) (q := 1) (y := z)
    (by
      change z ∉ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked (X := model (n+1)) univ (zeroIdeal W)) 2
      rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (zeroIdeal W) hc 2]
      exact zero_coordinate_maximal_order hW z)
  exact Nat.le_antisymm hu hl

/-- Base nonzero germs rule out the full ambient initial special branch internally. -/
theorem stabilized_not_special {q : ℕ} {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W))
    (z : ComplexModel (n+1)) : ¬ IsSpecial (X := model (n+1)) (zeroMarked W) .refl z := by
  rintro (⟨_, hz⟩ | ⟨hl, _⟩)
  · have hc := stabilized_coherent hW
    have hb : barMarked (X := model (n+1)) (zeroMarked W) = zeroMarked W := stepOne_zero_marked hW
    change z ∈ CodimOneSupportAlong.codimOnePartAlong (barMarked (X := model (n+1)) (zeroMarked W)).N
      (barMarked (X := model (n+1)) (zeroMarked W)).ideal (barMarked (X := model (n+1)) (zeroMarked W)).d at hz
    rw [hb] at hz
    have hplane := (coordinate_zero_iff z).mp
      ((zero_coordinate_tangent W).cosupport_inter_subset (fun x g (hg : (zeroIdeal W).mem x g) => hg.1) (by rfl)
        ⟨CodimOneSupportAlong.codimOnePartAlong_subset hz, mem_univ _⟩)
    have he := CodimOneSupportAlong.eventually_mem_codimOnePartAlong_iff_eq_zero hc
      (stabilized_isInvDomain hW hM).isWellFormed.isClosedSubmanifold_N (by rfl)
      (zero_coordinate_tangent W) (mem_univ z) hz
    obtain ⟨g, hg, hf⟩ := hM.isNonzeroAlongAt (tangentProjection n 1 z) (mem_univ _)
    have hcomp : (zeroIdeal W).mem z (g ∘ tangentProjection n 1) := base_comp_mem hg
    have hs : Tendsto (tangentInclusion n 1) (𝓝 (tangentProjection n 1 z)) (𝓝 z) := by
      simpa only [section_projection hplane] using
        (tangentInclusion n 1).continuous.tendsto (tangentProjection n 1 z)
    have heg : ∀ᶠ y in 𝓝 z, (zeroIdeal W).mem y (g ∘ tangentProjection n 1) := by
      filter_upwards [hcomp.1.eventually_nhds, hcomp.2.eventually_nhds] with y h1 h2
      exact ⟨h1, h2⟩
    apply hf
    filter_upwards [hs.eventually he, hs.eventually heg] with y hy hgy
    have hyR := hy.mpr ⟨mem_univ _, (coordinate_zero_iff _).mpr (zeroPlane_section y)⟩
    have hyCos := CodimOneSupportAlong.codimOnePartAlong_subset hyR
    have hval := (vanishesToOrderOn_one_iff (mem_univ _)
      (GermIdeal.IsCoherent.holomorphicAt_mem hc hgy)).mp
      (hyCos.2 (g ∘ tangentProjection n 1) hgy)
    intro hneq
    exact hneq.2 (by simpa only [Function.comp_apply, tangentProjection_tangentInclusion] using hval)
  · change 1 ≤ 0 at hl
    omega

private def thinMarked (W : Set (ComplexModel n)) : MarkedIdeal (n+1) (ComplexModel (n+1)) :=
  ⟨zeroPlane n, [], zeroIdeal W, 1⟩

private theorem zeroPlane_regular {z : ComplexModel (n+1)} (hz : z ∈ zeroPlane n) :
    RegularAtDim (n := n+1) (zeroPlane n) z n := by
  have he : {y : ComplexModel (n+1) | HironakaActualGraphFunctionalIdeal.graphFunction (zeroFunction n) 0 y = 0} =
      zeroPlane n := Set.ext fun y => coordinate_zero_iff y
  have h := HironakaActualGraphContactCoefficient.graphNormalContact_regularAtDim
    (zeroFunction n) ⊤ contDiff_const.contDiffOn (0 : Fin 1) (z := z) (by trivial)
    ((coordinate_zero_iff z).mpr hz)
  simpa only [Opens.coe_top, preimage_univ, inter_univ, he, Nat.add_sub_cancel] using h

private theorem thin_isInvDomain {q : ℕ} {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W)) :
    IsInvDomain q (thinMarked W) := by
  have hN : IsClosedSubmanifold (n+1) (zeroPlane n) :=
    ⟨isClosed_eq (actualJointNormalProjection n 1).continuous continuous_const,
      fun z hz => ⟨n, zeroPlane_regular hz⟩⟩
  refine ⟨⟨hN, stabilized_coherent hW, NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hN⟩,
    fun z hz => ⟨n, base_dim_le hM, zeroPlane_regular hz⟩, le_rfl, ?_⟩
  intro z hz
  obtain ⟨g, hg, hf⟩ := hM.isNonzeroAlongAt (tangentProjection n 1 z) (mem_univ _)
  refine ⟨g ∘ tangentProjection n 1, base_comp_mem hg, ?_⟩
  by_contra hn
  have hn' := not_frequently.mp hn
  have ht : Tendsto (tangentInclusion n 1) (𝓝 (tangentProjection n 1 z)) (𝓝 z) := by
    simpa only [section_projection hz] using
      (tangentInclusion n 1).continuous.tendsto (tangentProjection n 1 z)
  apply hf
  filter_upwards [ht.eventually hn'] with y hy
  intro hyne
  apply hy
  exact ⟨zeroPlane_section y, by simpa only [Function.comp_apply, tangentProjection_tangentInclusion] using hyne.2⟩

private theorem section_cosupport {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) {x : ComplexModel n}
    (hx : x ∈ (baseMarked W).cosupp) : tangentInclusion n 1 x ∈ (zeroMarked W).cosupp := by
  rw [stabilized_cosupport hW]
  exact ⟨by simpa only [tangentProjection_tangentInclusion] using hx, zeroPlane_section x⟩

private theorem thin_initial_value {q : ℕ} (hn : 0 < n) {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W))
    (x : ComplexModel n) (hx : x ∈ (baseMarked W).cosupp) :
    (invFamily (Nat.succ_pos n) q).inv (X := model (n+1)) (thinMarked W) .refl
      (tangentInclusion n 1 x) =
    (invFamily hn q).inv (X := model n) (baseMarked W) .refl x := by
  let U : Opens (ComplexModel n) := ⊤
  let O := HironakaActualOpenZeroSectionDifferentials.productOpen U
  let JS := GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (zeroIdeal W)
  let S : MarkedIdeal (n+1) O :=
    ⟨HironakaActualOpenZeroSectionDifferentials.liftedCarrier (univ : Set U), [], JS, 1⟩
  let B : MarkedIdeal n U := ⟨univ, [], GermIdeal.pullback (m := n)
    (HironakaActualOpenZeroSectionDifferentials.zeroSection U) JS, 1⟩
  let xU : U := ⟨x, mem_univ _⟩
  let zO := HironakaActualOpenZeroSectionDifferentials.zeroSection U xU
  have hS : MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) (thinMarked W) = S := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext z
      change actualJointNormalProjection n 1 z.val = 0 ↔
        (HironakaActualOpenZeroSectionDifferentials.projection U z ∈ (univ : Set U) ∧
          actualJointNormalProjection n 1 z.val = 0)
      simp only [mem_univ, true_and]
    · rfl
    · rfl
    · rfl
  have hTrace : GermIdeal.pullback (m := n)
      (HironakaActualOpenZeroSectionDifferentials.zeroSection U) JS =
        GermIdeal.pullback (m := n) (Subtype.val : U → ComplexModel n) (vanishingIdeal (n := n) W) := by
    have hc := stabilized_coherent hW
    change GermIdeal.pullback (m := n) (HironakaActualOpenZeroSectionDifferentials.zeroSection U)
      (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (zeroIdeal W)) = _
    rw [← coherent_pullback_comp contMDiff_subtype_val
      (HironakaActualOpenZeroSectionDifferentials.zeroSection_contMDiff U) (zeroIdeal W) hc]
    have he : (Subtype.val : O → ComplexModel (n+1)) ∘
        HironakaActualOpenZeroSectionDifferentials.zeroSection U =
      tangentInclusion n 1 ∘ (Subtype.val : U → ComplexModel n) := rfl
    rw [he, coherent_pullback_comp (tangentInclusion n 1).contMDiff contMDiff_subtype_val
      (zeroIdeal W) hc, zero_section_pullback W]
  have hB : B = MarkedIdeal.pullback (Subtype.val : U → ComplexModel n) (baseMarked W) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext y
      simp only [B, MarkedIdeal.pullback, baseMarked, preimage_univ]
    · rfl
    · exact hTrace
    · rfl
  have hDom : IsInvDomain q S := by
    rw [← hS]
    exact InvDomainTowerAlong.isInvDomain_pullback_val O (thin_isInvDomain hW hM)
  have hxB : xU ∈ B.cosupp := by
    rw [hB, MarkedIdealRestrictOpen.cosupp_pullback_val (baseMarked W)
      (fun y g (hg : (vanishingIdeal (n := n) W).mem y g) => hg.1) U]
    exact hx
  have hActual := HironakaActualSectionInitialValues.actual_initial_family_values
    q hn (univ : Set U) JS 1 hDom xU hxB
  change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O) S .refl zO =
    (invFamily hn q).inv (X := CMfd.of (n := n) U) B .refl xU at hActual
  have hxThin : tangentInclusion n 1 x ∈ (thinMarked W).cosupp :=
    ⟨zeroPlane_section x, fun g hg => ((section_cosupport hW hx).2 g hg).mono_set (subset_univ _)⟩
  have hSource := (invFamily (Nat.succ_pos n) q).isInvValue.restrictOpen (X := model (n+1))
    (thinMarked W) (thin_isInvDomain hW hM) O .refl trivial zO hxThin
  change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O)
      (MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) (thinMarked W)) .refl zO =
    (invFamily (Nat.succ_pos n) q).inv (X := model (n+1)) (thinMarked W) .refl
      (tangentInclusion n 1 x) at hSource
  rw [hS] at hSource
  have hBase := (invFamily hn q).isInvValue.restrictOpen (X := model n) (baseMarked W) hM U .refl trivial xU hx
  change (invFamily hn q).inv (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → ComplexModel n) (baseMarked W)) .refl xU =
    (invFamily hn q).inv (X := model n) (baseMarked W) .refl x at hBase
  rw [hB] at hActual
  exact hSource.symm.trans (hActual.trans hBase)

private theorem contact_initial_record {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (O : Opens (ComplexModel (n+1))) :
    contactMarkedKept (X := model (n+1)) (zeroMarked W) (addedCoordinate n) .refl O =
      MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) (thinMarked W) := by
  have hc : coeffMarkedAlong (barMarked (X := model (n+1)) (zeroMarked W)) = zeroMarked W :=
    coefficient_stepOne_zero_marked hW
  have he : {z | addedCoordinate n z = 0} = zeroPlane n := Set.ext fun z => coordinate_zero_iff z
  change MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1))
    (CoefficientIdealRestriction.withN (coeffMarkedAlong (barMarked (X := model (n+1)) (zeroMarked W)))
      (univ ∩ {z | addedCoordinate n z = 0})) = _
  rw [hc, univ_inter, he]
  rfl

private theorem stabilized_contact_lower_value {q : ℕ} (hn : 0 < n) {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W))
    (x : ComplexModel n) (hx : x ∈ (baseMarked W).cosupp) :
    Seq.StepOneValueMasked.lowerValueL (invFamily (Nat.succ_pos n) q) (X := model (n+1))
      (zeroMarked W) (StepOneValueMasked.lowerMarkedM (X := model (n+1)) (zeroMarked W)) 0 .refl .refl
      (tangentInclusion n 1 x) =
      (((invFamily hn q).inv (X := model n) (baseMarked W) .refl x) : WithTop (ValTy q)) := by
  let J := zeroMarked W
  let R := invFamily (Nat.succ_pos n) q
  have hd := stabilized_isInvDomain hW hM
  have hb : barMarked (X := model (n+1)) J = J := stepOne_zero_marked hW
  have hp : tangentInclusion n 1 x ∈ (barMarked (X := model (n+1)) J).cosupp := by
    rw [hb]
    exact section_cosupport hW hx
  have hnsp := stabilized_not_special hW hM (tangentInclusion n 1 x)
  have hD := Seq.StepOneCanonicalTail.lowerDataL_refl (X := model (n+1)) J (k := q+1) R
    hd.isWellFormed hd.one_le_d (Nat.succ_pos n) (zero_coordinate_maximal_order hW)
    hd.dimLE .refl trivial hp (show stepRegime (X := model (n+1)) J 0 .refl (tangentInclusion n 1 x) from ⟨rfl, hnsp⟩)
  let O : Opens (ComplexModel (n+1)) := ⊤
  have hContact : IsInvDomain q (contactMarkedKept (X := model (n+1)) J (addedCoordinate n) .refl O) := by
    rw [contact_initial_record hW]
    exact InvDomainTowerAlong.isInvDomain_pullback_val O (thin_isInvDomain hW hM)
  have hAnchor := Seq.ContactLowerValue.lowerValueL_zero_eq (X := model (n+1)) R J hd.isWellFormed
    hd.one_le_d .refl .refl trivial (zero_coordinate_tangent W) O (subset_univ _)
    (by intro H hH; cases hH) hContact trivial (mem_univ _) hp hD
  rw [contact_initial_record hW] at hAnchor
  have hRestriction := R.isInvValue.restrictOpen (X := model (n+1)) (thinMarked W) (thin_isInvDomain hW hM) O .refl trivial
    (⟨tangentInclusion n 1 x, mem_univ _⟩ : O)
    (show tangentInclusion n 1 x ∈ (thinMarked W).cosupp from
      ⟨zeroPlane_section x, fun g hg => ((section_cosupport hW hx).2 g hg).mono_set (subset_univ _)⟩)
  have hLower := hRestriction.trans (thin_initial_value hn hW hM x hx)
  change Seq.StepOneValueMasked.lowerValueL (X := model (n+1)) R J (StepOneValueMasked.lowerMarkedM (X := model (n+1)) J) 0 .refl .refl
    (tangentInclusion n 1 x) = _ at hAnchor
  exact hAnchor.trans (congrArg (fun v : ValTy q => (v : WithTop (ValTy q))) hLower)

/-- The actual chosen Step One reference evaluates to the original lower value. -/
theorem stabilized_stepOne_initial_value {q : ℕ} (hn : 0 < n) {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W))
    (x : ComplexModel n) (hx : x ∈ (baseMarked W).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := model (n+1)) (zeroMarked W) .refl (tangentInclusion n 1 x) =
    toLex (0, (((invFamily hn q).inv (X := model n) (baseMarked W) .refl x) : WithTop (ValTy q))) := by
  have hnsp := stabilized_not_special hW hM (tangentInclusion n 1 x)
  simp only [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL, hnsp, if_false]
  change toLex (0, Seq.StepOneValueMasked.lowerValueL (invFamily (Nat.succ_pos n) q)
    (X := model (n+1)) (zeroMarked W) (StepOneValueMasked.lowerMarkedM (X := model (n+1)) (zeroMarked W)) 0
    .refl .refl (tangentInclusion n 1 x)) = _
  rw [stabilized_contact_lower_value hn hW hM x hx]

private theorem initial_companion_equiv {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    RestrictEquiv (compAt (X := model (n+1)) (zeroMarked W) 1 .refl)
      (MarkedIdeal.pullback (Subtype.val : ordMask (M := model (n+1)) (zeroMarked W) 1 → ComplexModel (n+1))
        (zeroMarked W)) := by
  let O := ordMask (M := model (n+1)) (zeroMarked W) 1
  change RestrictEquiv
    (companionAlong (X := CMfd.of (n := n+1) O) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ) []
      (nonmonomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (zeroIdeal W)) [])
      (monomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (zeroIdeal W)) []) 1 1)
    (⟨(Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ, [],
      GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (zeroIdeal W), 1⟩ : MarkedIdeal (n+1) O)
  rw [companionAlong, if_neg (Nat.lt_irrefl 1), nonmonomialPartAlong_nil_eq_restrictOn]
  exact ⟨rfl, rfl, rfl, restrictLe_restrictOn,
    restrictLe_self_restrictOn (isCoherent_pullback contMDiff_subtype_val (stabilized_coherent hW))⟩

/-- The initial order-one mask is the whole actual stabilized ambient manifold. -/
theorem stabilized_initial_orderMask {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    ordMask (M := model (n+1)) (zeroMarked W) 1 = ⊤ := by
  have hge : NonmonomialOrderLocal.ordGe (M := model (n+1)) (zeroMarked W) 2 = ∅ := by
    change NonmonomialOrderLocal.ordGe (ordinaryTraceMarked (X := model (n+1)) univ (zeroIdeal W)) 2 = ∅
    rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (zeroIdeal W) (stabilized_coherent hW) 2]
    exact eq_empty_iff_forall_notMem.mpr (zero_coordinate_maximal_order hW)
  apply Opens.ext
  change (closure (NonmonomialOrderLocal.ordGe (M := model (n+1)) (zeroMarked W) 2))ᶜ = univ
  rw [hge, closure_empty, compl_empty]

private theorem initial_companion_value {q : ℕ} (hn : 0 < n) {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W))
    (x : ComplexModel n) (hx : x ∈ (baseMarked W).cosupp)
    (hp : tangentInclusion n 1 x ∈ ordMask (M := model (n+1)) (zeroMarked W) 1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := CMfd.of (n := n+1) (ordMask (M := model (n+1)) (zeroMarked W) 1))
      (compAt (X := model (n+1)) (zeroMarked W) 1 .refl) .refl ⟨tangentInclusion n 1 x, hp⟩ =
    toLex (0, (((invFamily hn q).inv (X := model n) (baseMarked W) .refl x) : WithTop (ValTy q))) := by
  let J := zeroMarked W
  let R := invFamily (Nat.succ_pos n) q
  let O := ordMask (M := model (n+1)) J 1
  let C : MarkedIdeal (n+1) O := compAt (X := model (n+1)) J 1 .refl
  let P := MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) J
  let p : O := ⟨tangentInclusion n 1 x, hp⟩
  have hd := stabilized_isInvDomain hW hM
  have hz := section_cosupport hW hx
  have hC : IsInvDomain (q+1) C := GeneralCompare.isInvDomain_compAt
    (X := model (n+1)) (Nat.succ_pos n) (by rfl) .refl hd
  have hCM : IsMaximalOrderAlong C.N C.ideal C.d :=
    GeneralCompare.isMaximalOrderAlong_compAt (X := model (n+1)) (Nat.succ_pos n) 1 .refl hd
  have hP : IsInvDomain (q+1) P := InvDomainTowerAlong.isInvDomain_pullback_val O hd
  obtain ⟨_, _, hPM, _⟩ := StepOneRestrictOpen.hypotheses_restrict (X := model (n+1)) J O
    hd.isWellFormed hd.one_le_d (zero_coordinate_maximal_order hW) hd.dimLE
  have hEq : RestrictEquiv C P := initial_companion_equiv hW
  have hpP : p ∈ P.cosupp := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val J
      (fun y g (hg : (zeroIdeal W).mem y g) => hg.1) O]
    exact hz
  have hpC : p ∈ C.cosupp := by rw [hEq.cosupp_eq]; exact hpP
  have hF := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) R (Nat.succ_pos n)
  have hRep := hF.representative (X := CMfd.of (n := n+1) O) C P hC hCM hP hPM
    hEq .refl trivial p hpC
  have hRest := hF.restrictOpen (X := model (n+1)) J hd (zero_coordinate_maximal_order hW)
    O .refl trivial p hz
  exact hRep.trans (hRest.trans (stabilized_stepOne_initial_value hn hW hM x hx))

/-- The full ambient original invariant is the explicit one-depth recoding of the old value. -/
theorem stabilized_initial_value {q : ℕ} (hn : 0 < n) {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W))
    (x : ComplexModel n) (hx : x ∈ (baseMarked W).cosupp) :
    (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (zeroMarked W) .refl
      (tangentInclusion n 1 x) =
      initialEmbedding q ((invFamily hn q).inv (X := model n) (baseMarked W) .refl x) := by
  let R := invFamily (Nat.succ_pos n) q
  let F := fun {X : CMfd (n+1)} (K : MarkedIdeal (n+1) X) {Y : CMfd (n+1)}
    (T : BlowupTower X Y) (y : Y) => Seq.StepOneValueMasked.stepOneInvM R K T y
  have ho := stabilized_order_one hW hM (section_cosupport hW hx)
  have hp : tangentInclusion n 1 x ∈ ordMask (M := model (n+1)) (zeroMarked W) 1 := by
    rw [stabilized_initial_orderMask hW]
    trivial
  have hLower := initial_companion_value hn hW hM x hx hp
  rw [invFamily_succ, generalStep_inv]
  change genInv (X := model (n+1)) F (zeroMarked W) .refl (tangentInclusion n 1 x) = _
  rw [genInv_of_nmOrd_ne_zero (X := model (n+1)) F (zeroMarked W) .refl ho (by decide)]
  change toLex (1, Sum.inrₗ (genLowerValue (X := model (n+1)) F (zeroMarked W) 1 .refl .refl
    (tangentInclusion n 1 x))) = _
  have hGen := genLowerValue_eq_of_mem (X := model (n+1)) (T₀ := .refl) (T₁ := .refl)
    (y := tangentInclusion n 1 x) F (zeroMarked W) hp
  have hCoefficient := hGen.trans
    (congrArg (fun v : ℕ ×ₗ WithTop (ValTy q) => (v : WithTop (ℕ ×ₗ WithTop (ValTy q)))) hLower)
  exact congrArg (fun v : WithTop (ℕ ×ₗ WithTop (ValTy q)) =>
    (toLex (1, Sum.inrₗ v) : ValTy (q+1))) hCoefficient

/-- The exact first maximum locus, including empty cosupports. -/
theorem stabilized_initial_maximum_locus {q : ℕ} (hn : 0 < n) {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain q (baseMarked W)) :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1))
      (zeroMarked W) .refl) (zeroMarked W).cosupp =
    zeroCarrier (ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked W) .refl)
      (baseMarked W).cosupp) := by
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hz' := hz
    rw [stabilized_cosupport hW] at hz'
    refine ⟨⟨hz'.1, ?_⟩, hz'.2⟩
    intro y hy
    have hh := hmax (tangentInclusion n 1 y) (section_cosupport hW hy)
    rw [← section_projection hz'.2, stabilized_initial_value hn hW hM y hy,
      stabilized_initial_value hn hW hM (tangentProjection n 1 z) hz'.1] at hh
    exact (initialEmbedding q).le_iff_le.mp hh
  · rintro ⟨⟨hz, hmax⟩, hplane⟩
    have hzS : z ∈ (zeroMarked W).cosupp := by
      rw [stabilized_cosupport hW]
      exact ⟨hz, hplane⟩
    refine ⟨hzS, ?_⟩
    intro y hy
    have hy' := hy
    rw [stabilized_cosupport hW] at hy'
    rw [← section_projection hy'.2, ← section_projection hplane,
      stabilized_initial_value hn hW hM (tangentProjection n 1 y) hy'.1,
      stabilized_initial_value hn hW hM (tangentProjection n 1 z) hz]
    exact (initialEmbedding q).monotone (hmax (tangentProjection n 1 y) hy'.1)

/-- The definition of the canonical invariant gives the same actual first-centre comparison. -/
theorem stabilized_canonical_initial_maximum_locus (hn : 0 < n) {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hM : IsInvDomain n (baseMarked W)) :
    ResolutionDriver.maxLocus ((canonicalInvariant (n+1)).inv (X := model (n+1))
      (zeroMarked W) .refl) (zeroMarked W).cosupp =
    zeroCarrier (ResolutionDriver.maxLocus ((canonicalInvariant n).inv (X := model n) (baseMarked W) .refl)
      (baseMarked W).cosupp) := by
  have hI : canonicalInvariant n = invFamily hn n := by
    cases n with
    | zero => omega
    | succ n => rfl
  rw [hI]
  exact stabilized_initial_maximum_locus hn hW hM

/-- Empty cosupport is preserved, without a nonempty-support hypothesis. -/
theorem stabilized_cosupport_eq_empty_iff {W : Set (ComplexModel n)}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    (zeroMarked W).cosupp = ∅ ↔ (baseMarked W).cosupp = ∅ := by
  constructor
  · intro h
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact notMem_empty _ (h ▸ section_cosupport hW hx)
  · intro h
    rw [stabilized_cosupport hW, h]
    exact eq_empty_iff_forall_notMem.mpr (fun _ hz => hz.1)

/-- The natural base domain excludes the identically zero ideal of the entire ambient space. -/
theorem base_domain_ne_univ {q : ℕ} {W : Set (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked W)) : W ≠ univ := by
  rintro rfl
  obtain ⟨g, hg, hf⟩ := hM.isNonzeroAlongAt 0 (mem_univ _)
  apply hf
  filter_upwards [hg.2] with y hy
  intro hne
  exact hne.2 (hy (mem_univ _))

end
end Hironaka.HironakaDisjointZeroCoordinateInitialRecoding
