import Hironaka.Resolution.HironakaG10NormalInitialArtinRees
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk

/-!
# Uniform Artin--Rees on an original regular-centre neighbourhood

Mathematics first:
`work/hironaka-codex-20261112/G10-GRAPH-BRIDGE-MATHEMATICS.md`.
Blueprint: `hironaka-g10-regular-centre-uniform-artin-rees.tex`.
Source: Hironaka (1975), Lemma 3.2, printed p. 531 (PDF p. 30).

The existing real-domain initial-ideal producer is used without assuming a
global coherent extension of a flattened ideal. The final statements assume
only original regular-centre geometry and original coherence. The exponent is
chosen internally from the actual finite original homogeneous family.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10RegularCentreUniformArtinRees

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaG10ChowUniformArtinRees HironakaG10NormalInitialArtinRees
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainNearbyInitialKernel
  HironakaSmoothCentreRealDomainOriginalStalkFreeness
  HironakaSmoothCentreRealDomainOriginalCentreOpen
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaRelativeNormalIdeal HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalDeformationFiniteRelationsSpread
  HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  BlowupFlatCoordinates

/-- A genuine ring equivalence preserves the chosen Artin--Rees exponent
because it preserves the complete ideals, intersections, powers and products. -/
theorem isArtinReesNumber_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (E : R ≃+* S) {I J : Ideal R} {α : ℕ} (h : IsArtinReesNumber I J α) :
    IsArtinReesNumber (Ideal.map E.toRingHom I) (Ideal.map E.toRingHom J) α := by
  have hinf : ∀ K L : Ideal R, Ideal.map E.toRingHom (K ⊓ L) =
      Ideal.map E.toRingHom K ⊓ Ideal.map E.toRingHom L := by
    intro K L
    apply le_antisymm (Ideal.map_inf_le E.toRingHom)
    intro z hz
    obtain ⟨a,ha,rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hz.1
    obtain ⟨b,hb,hba⟩ :=
      (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hz.2
    have hba' : b = a := E.injective hba
    subst b
    exact Ideal.mem_map_of_mem E.toRingHom ⟨ha,hb⟩
  intro m hm
  have hh : Ideal.map E.toRingHom (I ⊓ J^m) ≤
      Ideal.map E.toRingHom (J^(m-α) * (I ⊓ J^α)) := Ideal.map_mono (h m hm)
  simpa only [hinf, Ideal.map_pow, Ideal.map_mul] using hh

section Original

variable {d t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original regularity and coherence internally construct ONE exponent on
ONE actual original neighbourhood. Both full ideals are in the preferred
chart of each nearby original centre point. No global flattened extension,
finite initial family, degree bound or uniformity certificate is an input. -/
theorem exists_original_regular_centre_uniform_artinRees
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ α : ℕ, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∀ y ∈ C ∩ O, IsArtinReesNumber
        (wholeChartStalkIdeal A y y (mem_chart_source (ComplexModel (d+t)) y))
        (wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) y y
          (mem_chart_source (ComplexModel (d+t)) y)) α := by
  classical
  let := tangentAlgebra d t
  obtain ⟨Φ,hsrc,h0,hflat,_N,_U,V,_hU,_h0U,_hUV,_hcol,_hchain,_hsat,
    _hV,_h0V,_hVsub,_hcent,_hcoeff,_hpoly,_hdegree,_hfg,_hcentral,
    hW,h0W,hpoint,hc,hkernels⟩ :=
    exists_original_regular_real_all_nearby_initial_polynomial_kernels C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let S := actualOriginalRelationFamily d t F
  let W : Set (ComplexModel d) := (tangentInclusion d t) ⁻¹' V
  choose q hq using fun P : ↥S =>
    actualOriginalHomogeneousRelations_homogeneous d t (originalCoherentOriginIdeal F)
      P.val P.property
  let α : ℕ := Finset.univ.sup q
  let O := originalCentreBaseOpen x Φ W
  have hO : IsOpen O := isOpen_originalCentreBaseOpen x Φ W hW
  have hxO : x ∈ O := by
    refine ⟨⟨mem_chart_source (ComplexModel (d+t)) x, Φ.center_mem_source⟩, ?_⟩
    change tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x x)) ∈ W
    simpa only [h0, map_zero] using h0W
  refine ⟨α, O, hO, hxO, fun y hyCO => ?_⟩
  change y ∈ C ∩ originalCentreBaseOpen x Φ W at hyCO
  rw [originalCentreBaseOpen_centre_eq_image C x Φ hsrc hflat W
    (fun a ha => (hpoint a ha).1)] at hyCO
  obtain ⟨a, ha, rfl⟩ := hyCO
  let b := tangentInclusion d t a
  have hb : b ∈ Φ.target := (hpoint a ha).1
  let J := actualTranslatedOriginalSheaf F b
  let P := fun Q : ↥S => actualNearbyCoefficientPolynomial d t Q.val a (hc a ha Q)
  obtain ⟨_hJFG,_hDFG,_hst,_hunion,_hH,hspan,_hecentral,_htranslate,_hmodel,_hcontract⟩ :=
    hkernels a ha
  have hAR : IsArtinReesNumber (originalCoherentOriginIdeal J) (normalIdeal d t) α := by
    apply isArtinReesNumber_of_normal_initial_generators d t α
      (originalCoherentOriginIdeal J) P q
    · exact fun Q => Finset.le_sup (Finset.mem_univ Q)
    · exact fun Q => actualNearbyCoefficientPolynomial_homogeneous d t Q.val a
        (hc a ha Q) (hq Q)
    · exact hspan
  let y := actualFlatteningInverseMap x Φ b
  let hy := actualNearbyPoint_mem_chart_source x Φ hsrc b hb
  let E := actualNearbyGermEquiv Φ b hb
  have hAmap := (whole_original_stalk_dictionary_at_actual_target A hA x Φ hsrc b hb).1
  have hCmap := whole_nearby_vanishing_stalk_eq_map_normalIdeal x C Φ hsrc hflat b hb
    (tangentInclusion_mem_plane d t a)
  have hfixed : IsArtinReesNumber (wholeChartStalkIdeal A x y hy)
      (wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x y hy) α := by
    have hh := isArtinReesNumber_map_ringEquiv E.toRingEquiv hAR
    rwa [hAmap, ← hCmap] at hh
  let hy' := mem_chart_source (ComplexModel (d+t)) y
  let E' := localGermAlgEquiv (translatedChartTransition y x y hy' hy)
    (translatedChartTransition_zero y x y hy' hy)
  have hpreferred := isArtinReesNumber_map_ringEquiv E'.toRingEquiv hfixed
  rwa [map_wholeChartStalkIdeal A y x y hy' hy,
    map_wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) y x y hy' hy] at hpreferred

/-- The SAME constructed exponent works on the actual original
structure-sheaf stalks, independently of the preferred chart presentation. -/
theorem exists_original_regular_centre_uniform_actualStalk_artinRees
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ α : ℕ, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∀ y ∈ C ∩ O, IsArtinReesNumber (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) α := by
  obtain ⟨α,O,hO,hxO,hAR⟩ := exists_original_regular_centre_uniform_artinRees C x hreg A hA
  refine ⟨α,O,hO,hxO,fun y hy => ?_⟩
  have hh := isArtinReesNumber_map_ringEquiv (actualStalkChartEquiv (n := d+t) y).symm
    (hAR y hy)
  simpa only [← actualWholeSheafStalkIdeal_eq_map_chart] using hh

end Original

end

end Hironaka.HironakaG10RegularCentreUniformArtinRees
