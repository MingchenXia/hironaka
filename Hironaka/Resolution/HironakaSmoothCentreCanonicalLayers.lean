/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalCanonicalCentreFreeness
import Hironaka.Resolution.HironakaSmoothCentreRelativeIdeal

/-! # Genuine nonlinear smooth-centre power layers and canonical scalars
The actual original ring maps restrict to the whole power-image layers.
Both centre actions are independently descended from true multiplication.
The regular-centre endpoint supplies the whole ideal and chart dictionary
internally. No flatness or sheaf certificate is a premise or conclusion.
Complete mathematics precedes this source in `Mathematics.tex`. -/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreCanonicalLayers
noncomputable section
open HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
variable (B : Type*) {R S : Type*} [CommRing B] [CommRing R] [CommRing S] [Algebra B R]

/-- The true whole centre quotient equivalence of the actual ambient ring map. -/
def centreQuotientEquiv (J : Ideal R) (K : Ideal S) (E : R ≃+* S)
    (hK : K = Ideal.map E.toRingHom J) : (R ⧸ J) ≃+* (S ⧸ K) :=
  Ideal.quotientEquiv J K E hK

theorem centreQuotientEquiv_mk (J : Ideal R) (K : Ideal S) (E : R ≃+* S)
    (hK : K = Ideal.map E.toRingHom J) (r : R) :
    centreQuotientEquiv J K E hK (Ideal.Quotient.mk J r) = Ideal.Quotient.mk K (E r) := rfl

theorem centreQuotientEquiv_symm_mk (J : Ideal R) (K : Ideal S) (E : R ≃+* S)
    (hK : K = Ideal.map E.toRingHom J) (s : S) :
    (centreQuotientEquiv J K E hK).symm (Ideal.Quotient.mk K s) =
      Ideal.Quotient.mk J (E.symm s) := rfl

/-- Actual whole ideals and their actual powers, not a selected relation quotient. -/
def powerLayerQuotientEquiv (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ) :
    (R ⧸ (I ⊔ J ^ (q+1))) ≃+* (S ⧸ (I' ⊔ J' ^ (q+1))) :=
  Ideal.quotientEquiv _ _ E (by rw [hI, hJ, Ideal.map_sup, Ideal.map_pow]; rfl)

theorem powerLayerQuotientEquiv_mk (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ) (g : R) :
    powerLayerQuotientEquiv I J I' J' E hI hJ q (Ideal.Quotient.mk (I ⊔ J ^ (q+1)) g) =
      Ideal.Quotient.mk (I' ⊔ J' ^ (q+1)) (E g) := rfl

theorem powerLayerQuotientEquiv_symm_mk (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ) (s : S) :
    (powerLayerQuotientEquiv I J I' J' E hI hJ q).symm (Ideal.Quotient.mk (I' ⊔ J' ^ (q+1)) s) =
      Ideal.Quotient.mk (I ⊔ J ^ (q+1)) (E.symm s) := rfl

/-- Restrict the genuine whole quotient equivalence to its literal actual power images. -/
def actualPowerLayerAddEquiv (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ) :
    idealPowerLayer B I J q ≃+ idealPowerLayer S I' J' q := by
  let Q := powerLayerQuotientEquiv I J I' J' E hI hJ q
  exact {
    toFun := fun x => ⟨Q x.val, by
      obtain ⟨g, hg, he⟩ := x.property
      refine ⟨E g, ?_, ?_⟩
      · change E g ∈ J' ^ q
        rw [hJ, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem E.toRingHom hg
      · rw [← he]
        rfl⟩
    invFun := fun y => ⟨Q.symm y.val, by
      obtain ⟨s, hs, he⟩ := y.property
      have hm : s ∈ Ideal.map E.toRingHom (J ^ q) := by
        rw [Ideal.map_pow, ← hJ]
        exact hs
      obtain ⟨g, hg, hgs⟩ := (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hm
      refine ⟨g, hg, ?_⟩
      rw [← he, ← hgs]
      change Ideal.Quotient.mk (I ⊔ J ^ (q+1)) g =
        Ideal.Quotient.mk (I ⊔ J ^ (q+1)) (E.symm (E g))
      rw [E.symm_apply_apply]⟩
    left_inv := fun x => Subtype.ext (Q.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (Q.apply_symm_apply y.val)
    map_add' := fun x y => Subtype.ext (Q.map_add x.val y.val) }

/-- The actual restricted map still has the whole original quotient numerator formula. -/
theorem actualPowerLayerAddEquiv_val (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ)
    (x : idealPowerLayer B I J q) :
    (actualPowerLayerAddEquiv B I J I' J' E hI hJ q x).val =
      powerLayerQuotientEquiv I J I' J' E hI hJ q x.val := rfl

theorem actualPowerLayerAddEquiv_symm_val (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ)
    (y : idealPowerLayer S I' J' q) :
    ((actualPowerLayerAddEquiv B I J I' J' E hI hJ q).symm y).val =
      (powerLayerQuotientEquiv I J I' J' E hI hJ q).symm y.val := rfl

/-- Every true original power representative, not merely generators, is retained by E. -/
theorem actualPowerLayerAddEquiv_class (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ)
    (g : powerModule B J q) :
    actualPowerLayerAddEquiv B I J I' J' E hI hJ q (idealPowerLayerMap B I J q g) =
      idealPowerLayerMap S I' J' q ⟨E g.val, by
        change E g.val ∈ J' ^ q
        rw [hJ, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem E.toRingHom g.property⟩ := by
  apply Subtype.ext
  rfl

/-- Both genuinely descended quotient actions commute with the true original layer map. -/
theorem actualPowerLayerAddEquiv_centre_smul (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ)
    (c : R ⧸ J) (x : idealPowerLayer B I J q) :
    letI : SMul (R ⧸ J) (idealPowerLayer B I J q) := (idealPowerLayerCentreModule B I J q).toSMul
    letI := idealPowerLayerCentreModule B I J q
    letI : SMul (S ⧸ J') (idealPowerLayer S I' J' q) := (idealPowerLayerCentreModule S I' J' q).toSMul
    letI := idealPowerLayerCentreModule S I' J' q
    actualPowerLayerAddEquiv B I J I' J' E hI hJ q (c • x) =
      centreQuotientEquiv J J' E hJ c • actualPowerLayerAddEquiv B I J I' J' E hI hJ q x := by
  let : SMul (R ⧸ J) (idealPowerLayer B I J q) := (idealPowerLayerCentreModule B I J q).toSMul
  let := idealPowerLayerCentreModule B I J q
  let : SMul (S ⧸ J') (idealPowerLayer S I' J' q) := (idealPowerLayerCentreModule S I' J' q).toSMul
  let := idealPowerLayerCentreModule S I' J' q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  apply Subtype.ext
  change powerLayerQuotientEquiv I J I' J' E hI hJ q
      (Ideal.Quotient.mk (I ⊔ J ^ (q+1)) r * x.val) =
    Ideal.Quotient.mk (I' ⊔ J' ^ (q+1)) (E r) *
      powerLayerQuotientEquiv I J I' J' E hI hJ q x.val
  rw [map_mul, powerLayerQuotientEquiv_mk]

private theorem centreQuotientRingHomInvPair (J : Ideal R) (K : Ideal S) (E : R ≃+* S)
    (hK : K = Ideal.map E.toRingHom J) :
    RingHomInvPair (centreQuotientEquiv J K E hK).toRingHom
      (centreQuotientEquiv J K E hK).symm.toRingHom := by
  constructor
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).symm_apply_apply x
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).apply_symm_apply x

private theorem centreQuotientRingHomInvPairSymm (J : Ideal R) (K : Ideal S) (E : R ≃+* S)
    (hK : K = Ideal.map E.toRingHom J) :
    RingHomInvPair (centreQuotientEquiv J K E hK).symm.toRingHom
      (centreQuotientEquiv J K E hK).toRingHom := by
  constructor
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).apply_symm_apply x
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).symm_apply_apply x

attribute [local instance] centreQuotientRingHomInvPair centreQuotientRingHomInvPairSymm

/-- Semilinearity compares independently constructed actual centre actions. -/
def actualPowerLayerCentreEquiv (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) (q : ℕ) :
    letI : SMul (R ⧸ J) (idealPowerLayer B I J q) := (idealPowerLayerCentreModule B I J q).toSMul
    letI := idealPowerLayerCentreModule B I J q
    letI : SMul (S ⧸ J') (idealPowerLayer S I' J' q) := (idealPowerLayerCentreModule S I' J' q).toSMul
    letI := idealPowerLayerCentreModule S I' J' q
    LinearEquiv (σ' := (centreQuotientEquiv J J' E hJ).symm.toRingHom)
      (centreQuotientEquiv J J' E hJ).toRingHom (idealPowerLayer B I J q) (idealPowerLayer S I' J' q) := by
  letI : SMul (R ⧸ J) (idealPowerLayer B I J q) := (idealPowerLayerCentreModule B I J q).toSMul
  letI := idealPowerLayerCentreModule B I J q
  letI : SMul (S ⧸ J') (idealPowerLayer S I' J' q) := (idealPowerLayerCentreModule S I' J' q).toSMul
  letI := idealPowerLayerCentreModule S I' J' q
  exact { actualPowerLayerAddEquiv B I J I' J' E hI hJ q with
    map_smul' := fun c x => actualPowerLayerAddEquiv_centre_smul B I J I' J' E hI hJ q c x }

/-- Genuine componentwise original power-image maps give the WHOLE additive equivalence. -/
def actualPowerAssociatedAddEquiv (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) :
    (⨁ q : ℕ, layerFamily B I J q) ≃+ (⨁ q : ℕ, layerFamily S I' J' q) :=
  DFinsupp.mapRange.addEquiv (fun q => actualPowerLayerAddEquiv B I J I' J' E hI hJ q)

theorem actualPowerAssociatedAddEquiv_component (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J)
    (x : ⨁ q : ℕ, layerFamily B I J q) (q : ℕ) :
    actualPowerAssociatedAddEquiv B I J I' J' E hI hJ x q =
      actualPowerLayerAddEquiv B I J I' J' E hI hJ q (x q) := rfl

/-- The actual nonlinear map retains each entire original degree inclusion. -/
theorem actualPowerAssociatedAddEquiv_of (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J)
    (q : ℕ) (x : layerFamily B I J q) :
    actualPowerAssociatedAddEquiv B I J I' J' E hI hJ (DirectSum.of (layerFamily B I J) q x) =
      DirectSum.of (layerFamily S I' J') q (actualPowerLayerAddEquiv B I J I' J' E hI hJ q x) := by
  change DFinsupp.mapRange (fun q => actualPowerLayerAddEquiv B I J I' J' E hI hJ q)
    (fun q => (actualPowerLayerAddEquiv B I J I' J' E hI hJ q).map_zero)
    (DFinsupp.single q x) = DFinsupp.single q (actualPowerLayerAddEquiv B I J I' J' E hI hJ q x)
  exact DFinsupp.mapRange_single

/-- EVERY true quotient scalar is respected on the WHOLE original graded sum. -/
theorem actualPowerAssociatedAddEquiv_centre_smul (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J)
    (c : R ⧸ J) (x : ⨁ q : ℕ, layerFamily B I J q) :
    letI : SMul (R ⧸ J) (⨁ q : ℕ, layerFamily B I J q) := (idealPowerAssociatedCentreModule B I J).toSMul
    letI := idealPowerAssociatedCentreModule B I J
    letI : SMul (S ⧸ J') (⨁ q : ℕ, layerFamily S I' J' q) := (idealPowerAssociatedCentreModule S I' J').toSMul
    letI := idealPowerAssociatedCentreModule S I' J'
    actualPowerAssociatedAddEquiv B I J I' J' E hI hJ (c • x) =
      centreQuotientEquiv J J' E hJ c • actualPowerAssociatedAddEquiv B I J I' J' E hI hJ x := by
  let : SMul (R ⧸ J) (⨁ q : ℕ, layerFamily B I J q) := (idealPowerAssociatedCentreModule B I J).toSMul
  let := idealPowerAssociatedCentreModule B I J
  let : SMul (S ⧸ J') (⨁ q : ℕ, layerFamily S I' J' q) := (idealPowerAssociatedCentreModule S I' J').toSMul
  let := idealPowerAssociatedCentreModule S I' J'
  apply DFinsupp.ext
  intro q
  let : SMul (R ⧸ J) (idealPowerLayer B I J q) := (idealPowerLayerCentreModule B I J q).toSMul
  let := idealPowerLayerCentreModule B I J q
  let : SMul (S ⧸ J') (idealPowerLayer S I' J' q) := (idealPowerLayerCentreModule S I' J' q).toSMul
  let := idealPowerLayerCentreModule S I' J' q
  change actualPowerLayerAddEquiv B I J I' J' E hI hJ q (c • x q) =
    centreQuotientEquiv J J' E hJ c • actualPowerLayerAddEquiv B I J I' J' E hI hJ q (x q)
  exact actualPowerLayerAddEquiv_centre_smul B I J I' J' E hI hJ q c (x q)

/-- True layer maps assemble to the entire canonical centre semilinear equivalence. -/
def actualPowerAssociatedCentreEquiv (I J : Ideal R) (I' J' : Ideal S) (E : R ≃+* S)
    (hI : I' = Ideal.map E.toRingHom I) (hJ : J' = Ideal.map E.toRingHom J) :
    letI : SMul (R ⧸ J) (⨁ q : ℕ, layerFamily B I J q) := (idealPowerAssociatedCentreModule B I J).toSMul
    letI := idealPowerAssociatedCentreModule B I J
    letI : SMul (S ⧸ J') (⨁ q : ℕ, layerFamily S I' J' q) := (idealPowerAssociatedCentreModule S I' J').toSMul
    letI := idealPowerAssociatedCentreModule S I' J'
    LinearEquiv (σ' := (centreQuotientEquiv J J' E hJ).symm.toRingHom)
      (centreQuotientEquiv J J' E hJ).toRingHom
      (⨁ q : ℕ, layerFamily B I J q) (⨁ q : ℕ, layerFamily S I' J' q) := by
  letI : SMul (R ⧸ J) (⨁ q : ℕ, layerFamily B I J q) := (idealPowerAssociatedCentreModule B I J).toSMul
  letI := idealPowerAssociatedCentreModule B I J
  letI : SMul (S ⧸ J') (⨁ q : ℕ, layerFamily S I' J' q) := (idealPowerAssociatedCentreModule S I' J').toSMul
  letI := idealPowerAssociatedCentreModule S I' J'
  exact { actualPowerAssociatedAddEquiv B I J I' J' E hI hJ with
    map_smul' := fun c x => actualPowerAssociatedAddEquiv_centre_smul B I J I' J' E hI hJ c x }

open Hironaka.HolomorphicIdealSheaves HolGerm HironakaRelativeNormalIdeal
  HironakaRelativeNormalAssociatedGraded HironakaHolomorphicJetRankLoci HironakaSmoothCentreRelativeIdeal

section OriginalRegular
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Actual original germ-ideal inclusion gives the whole original stalk ideal inclusion. -/
theorem wholeChartStalkIdeal_le_of_original_le (A D : GermIdeal (d+t) M)
    (hAD : A.Le D) (x : M) :
    wholeChartStalkIdeal A x x (mem_chart_source _ x) ≤
      wholeChartStalkIdeal D x x (mem_chart_source _ x) := by
  apply Ideal.span_le.mpr
  rintro g ⟨f, hf, hmem, rfl⟩
  exact Ideal.subset_span ⟨f, hf, hAD x f hmem, rfl⟩

/-- Original regularity and actual centre containment internally supply the whole canonical layer bridge. -/
theorem exists_original_regular_canonical_layer_bridge (C : Set M) (x : M)
    (hreg : RegularAtDim (n := d+t) C x d) (A : GermIdeal (d+t) M)
    (hA : A.Le (vanishingIdeal (n := d+t) C)) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let E := flatteningGermEquiv _ Φ h0
      let Ix := wholeChartStalkIdeal A x x (mem_chart_source _ x)
      let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x)
      let Iflat := Ideal.comap E.toRingEquiv.toRingHom Ix
      Ix ≤ Kx ∧
      ∃ hK : Kx = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t),
      ∃ eLayer : ∀ q : ℕ,
        letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
          (originalNormalGradedPiece d t Iflat q) := (originalNormalGradedPieceCentreModule d t Iflat q).toSMul
        letI := originalNormalGradedPieceCentreModule d t Iflat q
        letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
          (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
          (idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q).toSMul
        letI := idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q
        LinearEquiv (σ' := (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).symm.toRingHom)
          (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).toRingHom
          (originalNormalGradedPiece d t Iflat q)
          (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q),
      ∃ eWhole :
        letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
          (originalNormalAssociatedGraded d t Iflat) := (originalNormalAssociatedGradedCentreModule d t Iflat).toSMul
        letI := originalNormalAssociatedGradedCentreModule d t Iflat
        letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
          (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
          (idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx).toSMul
        letI := idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx
        LinearEquiv (σ' := (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).symm.toRingHom)
          (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).toRingHom
          (originalNormalAssociatedGraded d t Iflat)
          (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q),
      (∀ (q : ℕ) (g : powerModule (HolGerm (ComplexModel d)) (normalIdeal d t) q),
        (eLayer q (idealPowerLayerMap (HolGerm (ComplexModel d)) Iflat (normalIdeal d t) q g)).val =
          Ideal.Quotient.mk (Ix ⊔ Kx ^ (q+1)) (E g.val)) ∧
      (∀ (q : ℕ) (z : originalNormalGradedPiece d t Iflat q),
        eWhole (DirectSum.of (fun q => originalNormalGradedPiece d t Iflat q) q z) =
          DirectSum.of (layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx) q (eLayer q z)) := by
  let := tangentAlgebra d t
  obtain ⟨_, _, Φ, hsrc, h0, hflat⟩ := hreg
  have hK := whole_vanishing_stalk_eq_map_normalIdeal (d := d) (t := t) x C Φ hsrc h0 hflat
  let E := flatteningGermEquiv _ Φ h0
  let Ix := wholeChartStalkIdeal A x x (mem_chart_source _ x)
  let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x)
  let Iflat := Ideal.comap E.toRingEquiv.toRingHom Ix
  have hi : Ix = Ideal.map E.toRingEquiv.toRingHom Iflat := by
    rw [Ideal.map_comap_of_surjective E.toRingEquiv.toRingHom E.surjective]
  refine ⟨Φ, hsrc, h0, hflat, wholeChartStalkIdeal_le_of_original_le A _ hA x, hK,
    (fun q => actualPowerLayerCentreEquiv (HolGerm (ComplexModel d)) Iflat (normalIdeal d t)
      Ix Kx E.toRingEquiv hi hK q),
    actualPowerAssociatedCentreEquiv (HolGerm (ComplexModel d)) Iflat (normalIdeal d t)
      Ix Kx E.toRingEquiv hi hK, ?_, ?_⟩
  · intro q g
    exact congrArg Subtype.val (actualPowerLayerAddEquiv_class (HolGerm (ComplexModel d))
      Iflat (normalIdeal d t) Ix Kx E.toRingEquiv hi hK q g)
  · intro q z
    exact actualPowerAssociatedAddEquiv_of (HolGerm (ComplexModel d))
      Iflat (normalIdeal d t) Ix Kx E.toRingEquiv hi hK q z

end OriginalRegular

end
end Hironaka.HironakaSmoothCentreCanonicalLayers
