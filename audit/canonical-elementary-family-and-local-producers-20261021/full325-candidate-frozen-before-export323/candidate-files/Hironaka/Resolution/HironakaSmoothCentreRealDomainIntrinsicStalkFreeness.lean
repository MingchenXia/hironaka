/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainOriginalCentreOpen
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance

/-! # Intrinsic actual original relative stalk freeness
Complete three-node mathematics precedes code. Genuine existing nonlinear
chart transitions transport BOTH whole original ideals and their independently
descended centre scalar actions. No sheaf normal-cone identification is claimed.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainIntrinsicStalkFreeness
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainOriginalCentreOpen HironakaSmoothCentreCanonicalLayers
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
  RelativePrincipalizationSpan InvertibleIdealQuotient HadamardBridge BlowupFlatCoordinates

private theorem actual_module_flat_of_free {R L : Type*} [CommSemiring R] [AddCommMonoid L]
    [Module R L] (hf : Module.Free R L) : Module.Flat R L := by
  let : Module.Free R L := hf
  infer_instance

private theorem intrinsicCentreQuotientRingHomInvPair {R S : Type*} [CommRing R] [CommRing S]
    (J : Ideal R) (K : Ideal S) (E : R ≃+* S) (hK : K = Ideal.map E.toRingHom J) :
    RingHomInvPair (centreQuotientEquiv J K E hK).toRingHom
      (centreQuotientEquiv J K E hK).symm.toRingHom := by
  constructor
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).symm_apply_apply x
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).apply_symm_apply x

private theorem intrinsicCentreQuotientRingHomInvPairSymm {R S : Type*} [CommRing R] [CommRing S]
    (J : Ideal R) (K : Ideal S) (E : R ≃+* S) (hK : K = Ideal.map E.toRingHom J) :
    RingHomInvPair (centreQuotientEquiv J K E hK).symm.toRingHom
      (centreQuotientEquiv J K E hK).toRingHom := by
  constructor
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).apply_symm_apply x
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).symm_apply_apply x

attribute [local instance] intrinsicCentreQuotientRingHomInvPair intrinsicCentreQuotientRingHomInvPairSymm

/-- True semilinear centre equivalences transport ALL genuine degrees and the ENTIRE sum. -/
theorem allRelativeIdealDegreesFree_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J)
    (hf : allRelativeIdealDegreesFree I J) : allRelativeIdealDegreesFree I' J' := by
  let : SMul (R ⧸ J) (⨁ q : ℕ, layerFamily R I J q) :=
    (idealPowerAssociatedCentreModule R I J).toSMul
  let := idealPowerAssociatedCentreModule R I J
  let : SMul (S ⧸ J') (⨁ q : ℕ, layerFamily S I' J' q) :=
    (idealPowerAssociatedCentreModule S I' J').toSMul
  let := idealPowerAssociatedCentreModule S I' J'
  let : Module.Free (R ⧸ J) (⨁ q : ℕ, layerFamily R I J q) := hf.1.1
  have hwhole : Module.Free (S ⧸ J') (⨁ q : ℕ, layerFamily S I' J' q) :=
    Module.Free.of_equiv (actualPowerAssociatedCentreEquiv R I J I' J' E hI hJ)
  refine ⟨⟨hwhole,actual_module_flat_of_free hwhole⟩,?_⟩
  intro q
  let : SMul (R ⧸ J) (idealPowerLayer R I J q) := (idealPowerLayerCentreModule R I J q).toSMul
  let := idealPowerLayerCentreModule R I J q
  let : SMul (S ⧸ J') (idealPowerLayer S I' J' q) := (idealPowerLayerCentreModule S I' J' q).toSMul
  let := idealPowerLayerCentreModule S I' J' q
  let : Module.Finite (R ⧸ J) (idealPowerLayer R I J q) := (hf.2 q).1
  let : Module.Free (R ⧸ J) (idealPowerLayer R I J q) := (hf.2 q).2.1
  let e := actualPowerLayerCentreEquiv R I J I' J' E hI hJ q
  have hfree : Module.Free (S ⧸ J') (idealPowerLayer S I' J' q) := Module.Free.of_equiv e
  have hfinite : Module.Finite (S ⧸ J') (idealPowerLayer S I' J' q) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact ⟨hfinite,hfree,actual_module_flat_of_free hfree⟩

/-- The reverse direction uses the same genuine whole centre actions, with the inverse ring map. -/
theorem allRelativeIdealDegreesFree_ringEquiv_iff {R S : Type*} [CommRing R] [CommRing S]
    (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) :
    allRelativeIdealDegreesFree I J ↔ allRelativeIdealDegreesFree I' J' := by
  have he : E.symm.toRingHom.comp E.toRingHom = RingHom.id R := by
    apply RingHom.ext
    intro r
    exact E.symm_apply_apply r
  have hIback : I = Ideal.map E.symm.toRingHom I' := by
    simp only [hI,Ideal.map_map,he,Ideal.map_id]
  have hJback : J = Ideal.map E.symm.toRingHom J' := by
    simp only [hJ,Ideal.map_map,he,Ideal.map_id]
  exact ⟨allRelativeIdealDegreesFree_of_ringEquiv I J I' J' E hI hJ,
    allRelativeIdealDegreesFree_of_ringEquiv I' J' I J E.symm hIback hJback⟩

section Manifold
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The point predicate uses the entire original membership and centre ideals in the actual preferred chart at that point. -/
def originalRelativeStalkFreeAt (A : GermIdeal n M) (C : Set M) (y : M) : Prop :=
  allRelativeIdealDegreesFree
    (wholeChartStalkIdeal A y y (mem_chart_source (ComplexModel n) y))
    (wholeChartStalkIdeal (vanishingIdeal (n := n) C) y y (mem_chart_source (ComplexModel n) y))

/-- BOTH whole original dictionaries are internally supplied by the genuine nonlinear translated chart transition. -/
theorem original_relative_stalk_degrees_free_chart_iff (A : GermIdeal n M) (C : Set M)
    (x x' y : M) (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hy' : y ∈ (chartAt (ComplexModel n) x').source) :
    allRelativeIdealDegreesFree (wholeChartStalkIdeal A x y hy)
      (wholeChartStalkIdeal (vanishingIdeal (n := n) C) x y hy) ↔
    allRelativeIdealDegreesFree (wholeChartStalkIdeal A x' y hy')
      (wholeChartStalkIdeal (vanishingIdeal (n := n) C) x' y hy') := by
  let E := localGermAlgEquiv (translatedChartTransition x' x y hy' hy)
    (translatedChartTransition_zero x' x y hy' hy)
  exact allRelativeIdealDegreesFree_ringEquiv_iff _ _ _ _ E.toRingEquiv
    (map_wholeChartStalkIdeal A x' x y hy' hy).symm
    (map_wholeChartStalkIdeal (vanishingIdeal (n := n) C) x' x y hy' hy).symm

/-- The ONE preferred-chart point predicate has exactly the same meaning in EVERY actual chart containing the original point. -/
theorem originalRelativeStalkFreeAt_iff_fixedChart (A : GermIdeal n M) (C : Set M)
    (x y : M) (hy : y ∈ (chartAt (ComplexModel n) x).source) :
    originalRelativeStalkFreeAt A C y ↔
      allRelativeIdealDegreesFree (wholeChartStalkIdeal A x y hy)
        (wholeChartStalkIdeal (vanishingIdeal (n := n) C) x y hy) :=
  original_relative_stalk_degrees_free_chart_iff A C y x y
    (mem_chart_source (ComplexModel n) y) hy

end Manifold

section Centre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original geometry/coherence/containment supplies ONE original centre open with intrinsic WHOLE and ALL-degree freeness. -/
theorem exists_original_regular_intrinsic_all_stalk_degrees_free_centre_open
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (_hyCO : y ∈ C ∩ O),
        originalRelativeStalkFreeAt A C y ∧
        ∀ (x' : M) (hy' : y ∈ (chartAt (ComplexModel (d+t)) x').source),
          allRelativeIdealDegreesFree (wholeChartStalkIdeal A x' y hy')
            (wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x' y hy') := by
  obtain ⟨Φ,_hsrc,_h0,_hflat,O,hO,hOdom,hcl,hall⟩ :=
    exists_original_regular_relative_centre_open_all_stalk_degrees_free C x hreg A hA hAC
  refine ⟨O,hO,hcl,?_⟩
  intro y hyCO
  have hfixed := hall y hyCO
  have hpreferred : originalRelativeStalkFreeAt A C y :=
    (originalRelativeStalkFreeAt_iff_fixedChart A C x y (hOdom hyCO.2).1).mpr hfixed.2.2
  refine ⟨hpreferred,?_⟩
  intro x' hy'
  exact (originalRelativeStalkFreeAt_iff_fixedChart A C x' y hy').mp hpreferred

end Centre

end
end Hironaka.HironakaSmoothCentreRealDomainIntrinsicStalkFreeness
