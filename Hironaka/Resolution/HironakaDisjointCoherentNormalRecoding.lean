/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointZeroCoordinateInitialRecoding
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeRestriction

set_option autoImplicit false

/-!
# Initial normal recoding of a nonradical coherent functional ideal

Blueprint: `hironaka-disjoint-coherent-normal-recoding.tex`.
The actual functional ideal is π*I + I_H, retaining every multiplicity of I.
The stabilized marked ideal has the FULL ambient carrier. Its initial canonical
value is compared with the original value at one lower recursive depth. This
module does not assert stabilization of finite histories or intrinsic descent.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaDisjointCoherentNormalRecoding
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
  CoefficientIdeal HomogenizedGlueing DerivativeIdeal HironakaSmoothSubmersionRelativeRestriction
  TangentDirectionAlong
open ResolutionInvariantSpec (IsInvDomain DimLE)

private abbrev model (n : ℕ) : CMfd n := CMfd.of (n := n) (ComplexModel n)

variable {n : ℕ}

/-- The original whole coherent ideal, with empty boundary and mark one. -/
def baseMarked (I : GermIdeal n (ComplexModel n)) : MarkedIdeal n (ComplexModel n) :=
  ⟨univ, [], I, 1⟩

/-- Whole functional stabilization; the original ideal is not replaced by its radical. -/
def stabilizedIdeal (I : GermIdeal n (ComplexModel n)) : GermIdeal (n+1) (ComplexModel (n+1)) :=
  sumIdeal (GermIdeal.pullback (m := n+1) (tangentProjection n 1) I)
    (vanishingIdeal (n := n+1) (zeroPlane n))

/-- The stabilized record retains the FULL smooth ambient carrier. -/
def stabilizedMarked (I : GermIdeal n (ComplexModel n)) : MarkedIdeal (n+1) (ComplexModel (n+1)) :=
  ⟨univ, [], stabilizedIdeal I, 1⟩

/-- The previously constructed literal finite constructor embedding. -/
abbrev initialEmbedding := HironakaDisjointZeroCoordinateInitialRecoding.initialEmbedding

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

private theorem normal_coherent :
    (vanishingIdeal (n := n+1) (zeroPlane n)).IsCoherent := by
  apply CartanIrreducible.cartanCoherence
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (actualJointNormalProjection n 1).contMDiff
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))

/-- Coherence of the entire functional sum follows from the original coherent ideal. -/
theorem stabilizedIdeal_isCoherent {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    (stabilizedIdeal I).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (tangentProjection n 1).contMDiff hI) normal_coherent

private theorem normal_tangent : IsTangentDirectionAlong
    (univ : Set (ComplexModel (n+1))) (vanishingIdeal (n := n+1) (zeroPlane n)) 1 univ
    (addedCoordinate n) := by
  have he : zeroCarrier (univ : Set (ComplexModel n)) = zeroPlane n := by
    ext z
    change (tangentProjection n 1 z ∈ (univ : Set (ComplexModel n)) ∧
      actualJointNormalProjection n 1 z = 0) ↔ actualJointNormalProjection n 1 z = 0
    simp only [mem_univ, true_and]
  simpa only [zeroIdeal, he] using zero_coordinate_tangent (univ : Set (ComplexModel n))

private theorem stabilized_coordinate_tangent {I : GermIdeal n (ComplexModel n)} :
    IsTangentDirectionAlong (univ : Set (ComplexModel (n+1))) (stabilizedIdeal I) 1 univ
      (addedCoordinate n) := by
  refine ⟨isOpen_univ, ?_, normal_tangent.multiplicity_one⟩
  intro x hx
  exact le_sumIdeal_right normal_coherent x _ (normal_tangent.mem x hx)

private theorem stabilized_coordinate_maximal_order {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    IsMaximalOrderAlong (univ : Set (ComplexModel (n+1))) (stabilizedIdeal I) 1 := by
  apply (isMaximalOrderAlong_univ_iff (stabilizedIdeal_isCoherent hI)).mpr
  intro x
  change (derivIdeal (stabilizedIdeal I)).mem x (fun _ => 1)
  have hu := (stabilized_coordinate_tangent (I := I)).mem x (mem_univ x)
  change (stabilizedIdeal I).mem x (addedCoordinate n) at hu
  let v := actualJointNormalInclusion n 1 (EuclideanSpace.single 0 1)
  have hd := chartDeriv_mem_derivIdeal (𝔞 := stabilizedIdeal I) (v := v) (e := complexChartAt x)
    (fun y g hg => GermIdeal.IsCoherent.holomorphicAt_mem (stabilizedIdeal_isCoherent hI) hg)
    (mem_complexChartAt_source x) hu
  have he : chartDeriv (complexChartAt x) v (addedCoordinate n) = fun _ => 1 := by
    funext y
    have h := HironakaActualGraphContactCoefficient.graphFunction_chartDeriv_eq_one
      (zeroFunction n) y (differentiableAt_const _) (0 : Fin 1)
    simpa only [v, addedCoordinate, complexChartAt, chartAt_self_eq] using h
  rwa [he] at hd

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

private theorem normal_trace_le {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    (GermIdeal.pullback (m := n) (tangentInclusion n 1)
      (vanishingIdeal (n := n+1) (zeroPlane n))).Le I := by
  intro x g hg
  obtain ⟨hgh, K, s, a, hs, _, he⟩ := GermIdeal.mem_pullback_iff.mp hg
  have hz : ∀ i, s i =ᶠ[𝓝 x] 0 := by
    intro i
    obtain ⟨b, hb, hsb⟩ := hs i
    filter_upwards [(tangentInclusion n 1).continuous.continuousAt.eventually hb.2] with y hy
    rw [hsb]
    exact hy (zeroPlane_section y)
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  refine ⟨hgh, 0, (fun i => i.elim0), (fun i => i.elim0), (fun i => i.elim0), (fun i => i.elim0), ?_⟩
  filter_upwards [he, eventually_all.mpr hz] with y hy hy0
  rw [hy]
  simp only [Fin.sum_univ_zero]
  exact Finset.sum_eq_zero fun i _ => by simp only [hy0 i, Pi.zero_apply, mul_zero]

/-- The whole actual functional ideal has precisely the original section pullback. -/
theorem section_pullback_stabilizedIdeal {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    GermIdeal.pullback (m := n) (tangentInclusion n 1) (stabilizedIdeal I) = I := by
  unfold stabilizedIdeal
  rw [pullback_sumIdeal_dimensions (tangentInclusion n 1).contMDiff
    (isCoherent_pullback (tangentProjection n 1).contMDiff hI) normal_coherent]
  have hp : GermIdeal.pullback (m := n) (tangentInclusion n 1)
      (GermIdeal.pullback (m := n+1) (tangentProjection n 1) I) = I := by
    rw [← coherent_pullback_comp (tangentProjection n 1).contMDiff (tangentInclusion n 1).contMDiff I hI,
      show (tangentProjection n 1) ∘ (tangentInclusion n 1) = id from
        funext (tangentProjection_tangentInclusion n 1), BlowupControlledTransform.pullback_id hI]
  rw [hp]
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply HomogenizedIdeal.mem_of_isInSpanAt hI
    exact IsInSpanAt.mono (fun b hb => hb.elim id (normal_trace_le hI x b))
      (IdealOrderArithmetic.mem_sumIdeal_iff.mp hg)
  · exact le_sumIdeal_left hI x g

private theorem idealPow_one_coherent {r : ℕ} {A : Type} [TopologicalSpace A]
    [ChartedSpace (ComplexModel r) A] [IsComplexManifold r A]
    (J : GermIdeal r A) (hJ : J.IsCoherent) : idealPow J 1 = J := by
  rw [idealPow_succ, idealPow_zero, BlowupControlledTransform.unitIdeal_mul hJ]

private theorem coeffMarked_one_coherent {r : ℕ} {A : Type} [TopologicalSpace A]
    [ChartedSpace (ComplexModel r) A] [IsComplexManifold r A]
    (J : GermIdeal r A) (hJ : J.IsCoherent) :
    coeffMarked (⟨univ, [], J, 1⟩ : MarkedIdeal r A) = (⟨univ, [], J, 1⟩ : MarkedIdeal r A) := by
  have he : sumExp (fun i : ℕ => 1-i) 1 0 = 1 := by simp [sumExp]
  have h0 : (idealPow (iterDerivIdeal J 0) (sumExp (fun i : ℕ => 1-i) 1 0)).IsCoherent := by
    simpa only [iterDerivIdeal_zero, he, idealPow_one_coherent J hJ] using hJ
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · rfl
  · change finSumIdeal (fun i => idealPow (iterDerivIdeal J i) (sumExp (fun j : ℕ => 1-j) 1 i)) 1 = J
    rw [finSumIdeal_one h0, iterDerivIdeal_zero, he, idealPow_one_coherent J hJ]
  · simp [coeffMarked, msum]

private theorem coefficient_stabilized {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    coeffMarkedAlong (stabilizedMarked I) = stabilizedMarked I := by
  rw [coeffMarkedAlong_eq_coeffMarked (𝔪 := stabilizedMarked I) rfl
    (fun y g hg => GermIdeal.IsCoherent.holomorphicAt_mem (stabilizedIdeal_isCoherent hI) hg)]
  exact coeffMarked_one_coherent (stabilizedIdeal I) (stabilizedIdeal_isCoherent hI)

private theorem bar_stabilized {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    barMarked (X := model (n+1)) (stabilizedMarked I) = stabilizedMarked I := by
  have hh : homMarkedAlong (stabilizedMarked I) = stabilizedMarked I := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · rfl
    · change homogenizedIdealAlong univ (stabilizedIdeal I) 1 = stabilizedIdeal I
      rw [homogenizedIdealAlong_univ
        (fun y g hg => GermIdeal.IsCoherent.holomorphicAt_mem (stabilizedIdeal_isCoherent hI) hg),
        HomogenizedIdeal.homogenizedIdeal_one (stabilizedIdeal_isCoherent hI)]
    · rfl
  change coeffMarkedAlong (homMarkedAlong (stabilizedMarked I)) = _
  rw [hh, coefficient_stabilized hI]

private theorem coeff_bar_stabilized {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    coeffMarkedAlong (barMarked (X := model (n+1)) (stabilizedMarked I)) = stabilizedMarked I := by
  rw [bar_stabilized hI, coefficient_stabilized hI]

private theorem base_dim_le {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) : n ≤ q := by
  obtain ⟨j, hj, hreg⟩ := hM.dimLE 0 (mem_univ _)
  have he := RegularPointDimension.eq_of_regularAtDim hreg
    (AnalyticIrreducibleComponents.regularAtDim_univ (0 : ComplexModel n))
  exact he ▸ hj

private theorem base_comp_mem {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent)
    {z : ComplexModel (n+1)} {g : ComplexModel n → ℂ}
    (hg : I.mem (tangentProjection n 1 z) g) :
    (stabilizedIdeal I).mem z (g ∘ tangentProjection n 1) :=
  le_sumIdeal_left (isCoherent_pullback (tangentProjection n 1).contMDiff hI) z _
    (pullback_mem_comp (X := model n) (Y := model (n+1))
      (tangentProjection n 1) (tangentProjection n 1).contMDiff hI hg)

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
theorem stabilized_isInvDomain {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    IsInvDomain (q+1) (stabilizedMarked I) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  have hc := stabilizedIdeal_isCoherent hI
  have hN : IsClosedSubmanifold (n+1) (univ : Set (ComplexModel (n+1))) :=
    ⟨isClosed_univ, fun x _ => ⟨n+1, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  refine ⟨⟨hN, hc, NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hN⟩,
    fun x _ => ⟨n+1, Nat.add_le_add_right (base_dim_le hM) 1,
      AnalyticIrreducibleComponents.regularAtDim_univ x⟩, le_rfl, ?_⟩
  intro z _
  obtain ⟨g, hg, hf⟩ := hM.isNonzeroAlongAt (tangentProjection n 1 z) (mem_univ _)
  refine ⟨g ∘ tangentProjection n 1, base_comp_mem hI hg, ?_⟩
  have hf' : ∃ᶠ y in 𝓝 (tangentProjection n 1 z), g y ≠ 0 := hf.mono fun _ hy => hy.2
  exact (projection_frequently hf').mono fun _ hy => ⟨mem_univ _, hy⟩

/-- The entire stabilized cosupport is the literal zero-section image of the old cosupport. -/
theorem stabilized_cosupport {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) :
    (stabilizedMarked I).cosupp = zeroCarrier (baseMarked I).cosupp := by
  have hc := stabilizedIdeal_isCoherent hI
  have htrace := section_pullback_stabilizedIdeal hI
  have hsec (x : ComplexModel n) :
      tangentInclusion n 1 x ∈ (stabilizedMarked I).cosupp ↔ x ∈ (baseMarked I).cosupp := by
    have h := pullback_cosupport_one (X := model (n+1)) (Y := model n)
      (tangentInclusion n 1) (tangentInclusion n 1).contMDiff hc x
    rw [htrace] at h
    exact h.symm
  ext z
  constructor
  · intro hz
    have hcoord := (stabilized_coordinate_tangent (I := I)).cosupport_inter_subset
      (fun x g (hg : (stabilizedIdeal I).mem x g) => GermIdeal.IsCoherent.holomorphicAt_mem (stabilizedIdeal_isCoherent hI) hg) (by rfl) ⟨hz, mem_univ _⟩
    have hplane := (coordinate_zero_iff z).mp hcoord
    refine ⟨?_, hplane⟩
    apply (hsec _).mp
    rwa [section_projection hplane]
  · rintro ⟨hx, hplane⟩
    have hs := (hsec _).mpr hx
    rwa [section_projection hplane] at hs

/-- The full ambient nonmonomial order at every stabilized cosupport point is one. -/
theorem stabilized_order_one {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I))
    {z : ComplexModel (n+1)} (hz : z ∈ (stabilizedMarked I).cosupp) :
    NonmonomialOrderLocal.nmOrd (M := model (n+1)) (stabilizedMarked I) z = 1 := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  have hd := stabilized_isInvDomain hM
  have hc := stabilizedIdeal_isCoherent hI
  have hl : 1 ≤ NonmonomialOrderLocal.nmOrd (M := model (n+1)) (stabilizedMarked I) z := by
    apply (NonmonomialOrderLocal.mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt (mem_univ _) 1).mp
    change z ∈ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked (X := model (n+1)) univ (stabilizedIdeal I)) 1
    rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (stabilizedIdeal I) hc 1]
    exact hz
  have hu := NonmonomialOrderLocal.nmOrd_le_of_notMem (M := model (n+1))
    (𝔪 := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))) (q := 1) (y := z)
    (by
      change z ∉ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked (X := model (n+1)) univ (stabilizedIdeal I)) 2
      rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (stabilizedIdeal I) hc 2]
      exact stabilized_coordinate_maximal_order hI z)
  exact Nat.le_antisymm hu hl

/-- Base nonzero germs rule out the full ambient initial special branch internally. -/
theorem stabilized_not_special {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I))
    (z : ComplexModel (n+1)) : ¬ IsSpecial (X := model (n+1)) (stabilizedMarked I) .refl z := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  rintro (⟨_, hz⟩ | ⟨hl, _⟩)
  · have hc := stabilizedIdeal_isCoherent hI
    have hb : barMarked (X := model (n+1)) (stabilizedMarked I) = stabilizedMarked I := bar_stabilized hI
    change z ∈ CodimOneSupportAlong.codimOnePartAlong (barMarked (X := model (n+1)) (stabilizedMarked I)).N
      (barMarked (X := model (n+1)) (stabilizedMarked I)).ideal (barMarked (X := model (n+1)) (stabilizedMarked I)).d at hz
    rw [hb] at hz
    have hplane := (coordinate_zero_iff z).mp
      ((stabilized_coordinate_tangent (I := I)).cosupport_inter_subset (fun x g (hg : (stabilizedIdeal I).mem x g) => GermIdeal.IsCoherent.holomorphicAt_mem (stabilizedIdeal_isCoherent hI) hg) (by rfl)
        ⟨CodimOneSupportAlong.codimOnePartAlong_subset hz, mem_univ _⟩)
    have he := CodimOneSupportAlong.eventually_mem_codimOnePartAlong_iff_eq_zero hc
      (stabilized_isInvDomain hM).isWellFormed.isClosedSubmanifold_N (by rfl)
      (stabilized_coordinate_tangent (I := I)) (mem_univ z) hz
    obtain ⟨g, hg, hf⟩ := hM.isNonzeroAlongAt (tangentProjection n 1 z) (mem_univ _)
    have hcomp : (stabilizedIdeal I).mem z (g ∘ tangentProjection n 1) := base_comp_mem hI hg
    have hs : Tendsto (tangentInclusion n 1) (𝓝 (tangentProjection n 1 z)) (𝓝 z) := by
      simpa only [section_projection hplane] using
        (tangentInclusion n 1).continuous.tendsto (tangentProjection n 1 z)
    have heg : ∀ᶠ y in 𝓝 z, (stabilizedIdeal I).mem y (g ∘ tangentProjection n 1) :=
      HomogenizedGlueing.eventually_mem (stabilizedIdeal_isCoherent hI) hcomp
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

private def thinMarked (I : GermIdeal n (ComplexModel n)) : MarkedIdeal (n+1) (ComplexModel (n+1)) :=
  ⟨zeroPlane n, [], stabilizedIdeal I, 1⟩

private theorem zeroPlane_regular {z : ComplexModel (n+1)} (hz : z ∈ zeroPlane n) :
    RegularAtDim (n := n+1) (zeroPlane n) z n := by
  have he : {y : ComplexModel (n+1) | HironakaActualGraphFunctionalIdeal.graphFunction (zeroFunction n) 0 y = 0} =
      zeroPlane n := Set.ext fun y => coordinate_zero_iff y
  have h := HironakaActualGraphContactCoefficient.graphNormalContact_regularAtDim
    (zeroFunction n) ⊤ contDiff_const.contDiffOn (0 : Fin 1) (z := z) (by trivial)
    ((coordinate_zero_iff z).mpr hz)
  simpa only [Opens.coe_top, preimage_univ, inter_univ, he, Nat.add_sub_cancel] using h

private theorem thin_isInvDomain {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    IsInvDomain q (thinMarked I) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  have hN : IsClosedSubmanifold (n+1) (zeroPlane n) :=
    ⟨isClosed_eq (actualJointNormalProjection n 1).continuous continuous_const,
      fun z hz => ⟨n, zeroPlane_regular hz⟩⟩
  refine ⟨⟨hN, stabilizedIdeal_isCoherent hI, NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hN⟩,
    fun z hz => ⟨n, base_dim_le hM, zeroPlane_regular hz⟩, le_rfl, ?_⟩
  intro z hz
  obtain ⟨g, hg, hf⟩ := hM.isNonzeroAlongAt (tangentProjection n 1 z) (mem_univ _)
  refine ⟨g ∘ tangentProjection n 1, base_comp_mem hI hg, ?_⟩
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

private theorem section_cosupport {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) {x : ComplexModel n}
    (hx : x ∈ (baseMarked I).cosupp) : tangentInclusion n 1 x ∈ (stabilizedMarked I).cosupp := by
  rw [stabilized_cosupport hI]
  exact ⟨by simpa only [tangentProjection_tangentInclusion] using hx, zeroPlane_section x⟩

private theorem thin_initial_value {q : ℕ} (hn : 0 < n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I))
    (x : ComplexModel n) (hx : x ∈ (baseMarked I).cosupp) :
    (invFamily (Nat.succ_pos n) q).inv (X := model (n+1)) (thinMarked I) .refl
      (tangentInclusion n 1 x) =
    (invFamily hn q).inv (X := model n) (baseMarked I) .refl x := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  let U : Opens (ComplexModel n) := ⊤
  let O := HironakaActualOpenZeroSectionDifferentials.productOpen U
  let JS := GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)
  let S : MarkedIdeal (n+1) O :=
    ⟨HironakaActualOpenZeroSectionDifferentials.liftedCarrier (univ : Set U), [], JS, 1⟩
  let B : MarkedIdeal n U := ⟨univ, [], GermIdeal.pullback (m := n)
    (HironakaActualOpenZeroSectionDifferentials.zeroSection U) JS, 1⟩
  let xU : U := ⟨x, mem_univ _⟩
  let zO := HironakaActualOpenZeroSectionDifferentials.zeroSection U xU
  have hS : MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) (thinMarked I) = S := by
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
        GermIdeal.pullback (m := n) (Subtype.val : U → ComplexModel n) (I) := by
    have hc := stabilizedIdeal_isCoherent hI
    change GermIdeal.pullback (m := n) (HironakaActualOpenZeroSectionDifferentials.zeroSection U)
      (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)) = _
    rw [← coherent_pullback_comp contMDiff_subtype_val
      (HironakaActualOpenZeroSectionDifferentials.zeroSection_contMDiff U) (stabilizedIdeal I) hc]
    have he : (Subtype.val : O → ComplexModel (n+1)) ∘
        HironakaActualOpenZeroSectionDifferentials.zeroSection U =
      tangentInclusion n 1 ∘ (Subtype.val : U → ComplexModel n) := rfl
    rw [he, coherent_pullback_comp (tangentInclusion n 1).contMDiff contMDiff_subtype_val
      (stabilizedIdeal I) hc, section_pullback_stabilizedIdeal hI]
  have hB : B = MarkedIdeal.pullback (Subtype.val : U → ComplexModel n) (baseMarked I) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext y
      simp only [B, MarkedIdeal.pullback, baseMarked, preimage_univ]
    · rfl
    · exact hTrace
    · rfl
  have hDom : IsInvDomain q S := by
    rw [← hS]
    exact InvDomainTowerAlong.isInvDomain_pullback_val O (thin_isInvDomain hM)
  have hxB : xU ∈ B.cosupp := by
    rw [hB, MarkedIdealRestrictOpen.cosupp_pullback_val (baseMarked I)
      (fun y g (hg : I.mem y g) => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) U]
    exact hx
  have hActual := HironakaActualSectionInitialValues.actual_initial_family_values
    q hn (univ : Set U) JS 1 hDom xU hxB
  change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O) S .refl zO =
    (invFamily hn q).inv (X := CMfd.of (n := n) U) B .refl xU at hActual
  have hxThin : tangentInclusion n 1 x ∈ (thinMarked I).cosupp :=
    ⟨zeroPlane_section x, fun g hg => ((section_cosupport hI hx).2 g hg).mono_set (subset_univ _)⟩
  have hSource := (invFamily (Nat.succ_pos n) q).isInvValue.restrictOpen (X := model (n+1))
    (thinMarked I) (thin_isInvDomain hM) O .refl trivial zO hxThin
  change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O)
      (MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) (thinMarked I)) .refl zO =
    (invFamily (Nat.succ_pos n) q).inv (X := model (n+1)) (thinMarked I) .refl
      (tangentInclusion n 1 x) at hSource
  rw [hS] at hSource
  have hBase := (invFamily hn q).isInvValue.restrictOpen (X := model n) (baseMarked I) hM U .refl trivial xU hx
  change (invFamily hn q).inv (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → ComplexModel n) (baseMarked I)) .refl xU =
    (invFamily hn q).inv (X := model n) (baseMarked I) .refl x at hBase
  rw [hB] at hActual
  exact hSource.symm.trans (hActual.trans hBase)

private theorem contact_initial_record {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) (O : Opens (ComplexModel (n+1))) :
    contactMarkedKept (X := model (n+1)) (stabilizedMarked I) (addedCoordinate n) .refl O =
      MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) (thinMarked I) := by
  have hc : coeffMarkedAlong (barMarked (X := model (n+1)) (stabilizedMarked I)) = stabilizedMarked I :=
    coeff_bar_stabilized hI
  have he : {z | addedCoordinate n z = 0} = zeroPlane n := Set.ext fun z => coordinate_zero_iff z
  change MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1))
    (CoefficientIdealRestriction.withN (coeffMarkedAlong (barMarked (X := model (n+1)) (stabilizedMarked I)))
      (univ ∩ {z | addedCoordinate n z = 0})) = _
  rw [hc, univ_inter, he]
  rfl

private theorem stabilized_contact_lower_value {q : ℕ} (hn : 0 < n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I))
    (x : ComplexModel n) (hx : x ∈ (baseMarked I).cosupp) :
    Seq.StepOneValueMasked.lowerValueL (invFamily (Nat.succ_pos n) q) (X := model (n+1))
      (stabilizedMarked I) (StepOneValueMasked.lowerMarkedM (X := model (n+1)) (stabilizedMarked I)) 0 .refl .refl
      (tangentInclusion n 1 x) =
      (((invFamily hn q).inv (X := model n) (baseMarked I) .refl x) : WithTop (ValTy q)) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  let J := stabilizedMarked I
  let R := invFamily (Nat.succ_pos n) q
  have hd := stabilized_isInvDomain hM
  have hb : barMarked (X := model (n+1)) J = J := bar_stabilized hI
  have hp : tangentInclusion n 1 x ∈ (barMarked (X := model (n+1)) J).cosupp := by
    rw [hb]
    exact section_cosupport hI hx
  have hnsp := stabilized_not_special hM (tangentInclusion n 1 x)
  have hD := Seq.StepOneCanonicalTail.lowerDataL_refl (X := model (n+1)) J (k := q+1) R
    hd.isWellFormed hd.one_le_d (Nat.succ_pos n) (stabilized_coordinate_maximal_order hI)
    hd.dimLE .refl trivial hp (show stepRegime (X := model (n+1)) J 0 .refl (tangentInclusion n 1 x) from ⟨rfl, hnsp⟩)
  let O : Opens (ComplexModel (n+1)) := ⊤
  have hContact : IsInvDomain q (contactMarkedKept (X := model (n+1)) J (addedCoordinate n) .refl O) := by
    rw [contact_initial_record hI]
    exact InvDomainTowerAlong.isInvDomain_pullback_val O (thin_isInvDomain hM)
  have hAnchor := Seq.ContactLowerValue.lowerValueL_zero_eq (X := model (n+1)) R J hd.isWellFormed
    hd.one_le_d .refl .refl trivial (stabilized_coordinate_tangent (I := I)) O (subset_univ _)
    (by intro H hH; cases hH) hContact trivial (mem_univ _) hp hD
  rw [contact_initial_record hI] at hAnchor
  have hRestriction := R.isInvValue.restrictOpen (X := model (n+1)) (thinMarked I) (thin_isInvDomain hM) O .refl trivial
    (⟨tangentInclusion n 1 x, mem_univ _⟩ : O)
    (show tangentInclusion n 1 x ∈ (thinMarked I).cosupp from
      ⟨zeroPlane_section x, fun g hg => ((section_cosupport hI hx).2 g hg).mono_set (subset_univ _)⟩)
  have hLower := hRestriction.trans (thin_initial_value hn hM x hx)
  change Seq.StepOneValueMasked.lowerValueL (X := model (n+1)) R J (StepOneValueMasked.lowerMarkedM (X := model (n+1)) J) 0 .refl .refl
    (tangentInclusion n 1 x) = _ at hAnchor
  exact hAnchor.trans (congrArg (fun v : ValTy q => (v : WithTop (ValTy q))) hLower)

/-- The actual chosen Step One reference evaluates to the original lower value. -/
theorem stabilized_stepOne_initial_value {q : ℕ} (hn : 0 < n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I))
    (x : ComplexModel n) (hx : x ∈ (baseMarked I).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := model (n+1)) (stabilizedMarked I) .refl (tangentInclusion n 1 x) =
    toLex (0, (((invFamily hn q).inv (X := model n) (baseMarked I) .refl x) : WithTop (ValTy q))) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  have hnsp := stabilized_not_special hM (tangentInclusion n 1 x)
  simp only [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL, hnsp, if_false]
  change toLex (0, Seq.StepOneValueMasked.lowerValueL (invFamily (Nat.succ_pos n) q)
    (X := model (n+1)) (stabilizedMarked I) (StepOneValueMasked.lowerMarkedM (X := model (n+1)) (stabilizedMarked I)) 0
    .refl .refl (tangentInclusion n 1 x)) = _
  rw [stabilized_contact_lower_value hn hM x hx]

private theorem initial_companion_equiv {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) :
    RestrictEquiv (compAt (X := model (n+1)) (stabilizedMarked I) 1 .refl)
      (MarkedIdeal.pullback (Subtype.val : ordMask (M := model (n+1)) (stabilizedMarked I) 1 → ComplexModel (n+1))
        (stabilizedMarked I)) := by
  let O := ordMask (M := model (n+1)) (stabilizedMarked I) 1
  change RestrictEquiv
    (companionAlong (X := CMfd.of (n := n+1) O) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ) []
      (nonmonomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)) [])
      (monomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)) []) 1 1)
    (⟨(Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ, [],
      GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I), 1⟩ : MarkedIdeal (n+1) O)
  rw [companionAlong, if_neg (Nat.lt_irrefl 1), nonmonomialPartAlong_nil_eq_restrictOn]
  exact ⟨rfl, rfl, rfl, restrictLe_restrictOn,
    restrictLe_self_restrictOn (isCoherent_pullback contMDiff_subtype_val (stabilizedIdeal_isCoherent hI))⟩

/-- The initial order-one mask is the whole actual stabilized ambient manifold. -/
theorem stabilized_initial_orderMask {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) :
    ordMask (M := model (n+1)) (stabilizedMarked I) 1 = ⊤ := by
  have hge : NonmonomialOrderLocal.ordGe (M := model (n+1)) (stabilizedMarked I) 2 = ∅ := by
    change NonmonomialOrderLocal.ordGe (ordinaryTraceMarked (X := model (n+1)) univ (stabilizedIdeal I)) 2 = ∅
    rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (stabilizedIdeal I) (stabilizedIdeal_isCoherent hI) 2]
    exact eq_empty_iff_forall_notMem.mpr (stabilized_coordinate_maximal_order hI)
  apply Opens.ext
  change (closure (NonmonomialOrderLocal.ordGe (M := model (n+1)) (stabilizedMarked I) 2))ᶜ = univ
  rw [hge, closure_empty, compl_empty]

private theorem initial_companion_value {q : ℕ} (hn : 0 < n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I))
    (x : ComplexModel n) (hx : x ∈ (baseMarked I).cosupp)
    (hp : tangentInclusion n 1 x ∈ ordMask (M := model (n+1)) (stabilizedMarked I) 1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := CMfd.of (n := n+1) (ordMask (M := model (n+1)) (stabilizedMarked I) 1))
      (compAt (X := model (n+1)) (stabilizedMarked I) 1 .refl) .refl ⟨tangentInclusion n 1 x, hp⟩ =
    toLex (0, (((invFamily hn q).inv (X := model n) (baseMarked I) .refl x) : WithTop (ValTy q))) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  let J := stabilizedMarked I
  let R := invFamily (Nat.succ_pos n) q
  let O := ordMask (M := model (n+1)) J 1
  let C : MarkedIdeal (n+1) O := compAt (X := model (n+1)) J 1 .refl
  let P := MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) J
  let p : O := ⟨tangentInclusion n 1 x, hp⟩
  have hd := stabilized_isInvDomain hM
  have hz := section_cosupport hI hx
  have hC : IsInvDomain (q+1) C := GeneralCompare.isInvDomain_compAt
    (X := model (n+1)) (Nat.succ_pos n) (by rfl) .refl hd
  have hCM : IsMaximalOrderAlong C.N C.ideal C.d :=
    GeneralCompare.isMaximalOrderAlong_compAt (X := model (n+1)) (Nat.succ_pos n) 1 .refl hd
  have hP : IsInvDomain (q+1) P := InvDomainTowerAlong.isInvDomain_pullback_val O hd
  obtain ⟨_, _, hPM, _⟩ := StepOneRestrictOpen.hypotheses_restrict (X := model (n+1)) J O
    hd.isWellFormed hd.one_le_d (stabilized_coordinate_maximal_order hI) hd.dimLE
  have hEq : RestrictEquiv C P := initial_companion_equiv hI
  have hpP : p ∈ P.cosupp := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val J
      (fun y g (hg : (stabilizedIdeal I).mem y g) => GermIdeal.IsCoherent.holomorphicAt_mem (stabilizedIdeal_isCoherent hI) hg) O]
    exact hz
  have hpC : p ∈ C.cosupp := by rw [hEq.cosupp_eq]; exact hpP
  have hF := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) R (Nat.succ_pos n)
  have hRep := hF.representative (X := CMfd.of (n := n+1) O) C P hC hCM hP hPM
    hEq .refl trivial p hpC
  have hRest := hF.restrictOpen (X := model (n+1)) J hd (stabilized_coordinate_maximal_order hI)
    O .refl trivial p hz
  exact hRep.trans (hRest.trans (stabilized_stepOne_initial_value hn hM x hx))

/-- The full ambient original invariant is the explicit one-depth recoding of the old value. -/
theorem stabilized_initial_value {q : ℕ} (hn : 0 < n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I))
    (x : ComplexModel n) (hx : x ∈ (baseMarked I).cosupp) :
    (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) .refl
      (tangentInclusion n 1 x) =
      initialEmbedding q ((invFamily hn q).inv (X := model n) (baseMarked I) .refl x) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  let R := invFamily (Nat.succ_pos n) q
  let F := fun {X : CMfd (n+1)} (K : MarkedIdeal (n+1) X) {Y : CMfd (n+1)}
    (T : BlowupTower X Y) (y : Y) => Seq.StepOneValueMasked.stepOneInvM R K T y
  have ho := stabilized_order_one hM (section_cosupport hI hx)
  have hp : tangentInclusion n 1 x ∈ ordMask (M := model (n+1)) (stabilizedMarked I) 1 := by
    rw [stabilized_initial_orderMask hI]
    trivial
  have hLower := initial_companion_value hn hM x hx hp
  rw [invFamily_succ, generalStep_inv]
  change genInv (X := model (n+1)) F (stabilizedMarked I) .refl (tangentInclusion n 1 x) = _
  rw [genInv_of_nmOrd_ne_zero (X := model (n+1)) F (stabilizedMarked I) .refl ho (by decide)]
  change toLex (1, Sum.inrₗ (genLowerValue (X := model (n+1)) F (stabilizedMarked I) 1 .refl .refl
    (tangentInclusion n 1 x))) = _
  have hGen := genLowerValue_eq_of_mem (X := model (n+1)) (T₀ := .refl) (T₁ := .refl)
    (y := tangentInclusion n 1 x) F (stabilizedMarked I) hp
  have hCoefficient := hGen.trans
    (congrArg (fun v : ℕ ×ₗ WithTop (ValTy q) => (v : WithTop (ℕ ×ₗ WithTop (ValTy q)))) hLower)
  exact congrArg (fun v : WithTop (ℕ ×ₗ WithTop (ValTy q)) =>
    (toLex (1, Sum.inrₗ v) : ValTy (q+1))) hCoefficient

/-- The exact first maximum locus, including empty cosupports. -/
theorem stabilized_initial_maximum_locus {q : ℕ} (hn : 0 < n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1))
      (stabilizedMarked I) .refl) (stabilizedMarked I).cosupp =
    zeroCarrier (ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked I) .refl)
      (baseMarked I).cosupp) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hz' := hz
    rw [stabilized_cosupport hI] at hz'
    refine ⟨⟨hz'.1, ?_⟩, hz'.2⟩
    intro y hy
    have hh := hmax (tangentInclusion n 1 y) (section_cosupport hI hy)
    rw [← section_projection hz'.2, stabilized_initial_value hn hM y hy,
      stabilized_initial_value hn hM (tangentProjection n 1 z) hz'.1] at hh
    exact (initialEmbedding q).le_iff_le.mp hh
  · rintro ⟨⟨hz, hmax⟩, hplane⟩
    have hzS : z ∈ (stabilizedMarked I).cosupp := by
      rw [stabilized_cosupport hI]
      exact ⟨hz, hplane⟩
    refine ⟨hzS, ?_⟩
    intro y hy
    have hy' := hy
    rw [stabilized_cosupport hI] at hy'
    rw [← section_projection hy'.2, ← section_projection hplane,
      stabilized_initial_value hn hM (tangentProjection n 1 y) hy'.1,
      stabilized_initial_value hn hM (tangentProjection n 1 z) hz]
    exact (initialEmbedding q).monotone (hmax (tangentProjection n 1 y) hy'.1)

/-- The definition of the canonical invariant gives the same actual first-centre comparison. -/
theorem stabilized_canonical_initial_maximum_locus (hn : 0 < n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain n (baseMarked I)) :
    ResolutionDriver.maxLocus ((canonicalInvariant (n+1)).inv (X := model (n+1))
      (stabilizedMarked I) .refl) (stabilizedMarked I).cosupp =
    zeroCarrier (ResolutionDriver.maxLocus ((canonicalInvariant n).inv (X := model n) (baseMarked I) .refl)
      (baseMarked I).cosupp) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  have hCanonical : canonicalInvariant n = invFamily hn n := by
    cases n with
    | zero => omega
    | succ n => rfl
  rw [hCanonical]
  exact stabilized_initial_maximum_locus hn hM

/-- Empty cosupport is preserved, without a nonempty-support hypothesis. -/
theorem stabilized_cosupport_eq_empty_iff {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) :
    (stabilizedMarked I).cosupp = ∅ ↔ (baseMarked I).cosupp = ∅ := by
  constructor
  · intro h
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact notMem_empty _ (h ▸ section_cosupport hI hx)
  · intro h
    rw [stabilized_cosupport hI, h]
    exact eq_empty_iff_forall_notMem.mpr (fun _ hz => hz.1)


end
end Hironaka.HironakaDisjointCoherentNormalRecoding
