import Hironaka.Analytic.Unibranch.OriginalNativeShadowFlatWindows

/-! Actual INITIAL native windows and the SAME physical canonical prefixes over
an ordinary native base OPEN. Blueprint FIRST: original-native-hs-base-open-windows.tex.
Current born boundaries are preserved, never reset. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenWindows
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11PresLineState HironakaG11PresReduction
  HironakaG1CanonicalStageCentreIdeal BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealTowerTransport MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism.MarkedIdeal HironakaActualPowerBoundaryExponents
  HironakaG11StrictTransformTowers HomogenizedGlueingTower ResolutionInvariantSeq
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {X B : SourceReducedComplexSpace} {n : ℕ} {ι : Type*}
  (w : ι → DimEmbedding X n) (j : B ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)

/-- The internally constructed WHOLE old ambient trace of the native base open. -/
def traceOpen (i : ι) : Opens (w i).ambient :=
  (OriginalNativeEmbeddingOpenPullback.ambientTrace (w i).toLocalEmbedding j hj).openSet

/-- The genuine actual local embedding in the new native base. -/
def window (i : ι) : DimEmbedding B n :=
  DimEmbedding.ofLocalEmbedding (OriginalNativeEmbeddingOpenPullback.embedding (w i).toLocalEmbedding j hj)

private theorem coordinate_dictionary (i : ι) (z : (w i).ambient) :
    z ∈ traceOpen w j hj i ↔ z.val ∈ (window w j hj i).ambient := by
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨u, hu, heq⟩
    exact (Subtype.ext heq : u = z) ▸ hu

/-- The ACTUAL coordinate equivalence to the old ambient trace. -/
def baseEquiv (i : ι) : Amb (window w j hj) i ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (traceOpen w j hj i) :=
  (MaxLocusLocal.nestedDiffeo (w i).ambient (traceOpen w j hj i) (window w j hj i).ambient
    (coordinate_dictionary w j hj i)
    (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (w i).toLocalEmbedding j hj)).symm

theorem carrier_dictionary (i : ι) : (window w j hj i).carrier =
    (baseEquiv w j hj i) ⁻¹' ((Subtype.val : traceOpen w j hj i → (w i).ambient) ⁻¹' (w i).carrier) := rfl

/-- FULL original native quotient square. -/
theorem base_square (i : ι) :
    EmbeddedBlowupOverlap.chartMorphism (window w j hj i).toLocalEmbedding ≫ j =
      EmbeddedBlowupOverlap.chartMorphism
        (OriginalNativeEmbeddingOpenPullback.restricted (w i).toLocalEmbedding j hj) :=
  OriginalNativeEmbeddingOpenPullback.nativeLift_square (w i).toLocalEmbedding j hj

theorem range_dictionary (i : ι) : j.hom.left.base ⁻¹' range (w i).toLocalEmbedding.toPoint =
    range (window w j hj i).toLocalEmbedding.toPoint :=
  OriginalNativeEmbeddingOpenPullback.range_dictionary (w i).toLocalEmbedding j hj

variable (raw : ∀ i, MarkedIdeal n (Amb w i))

def rawRecord (i : ι) : MarkedIdeal n (Amb (window w j hj) i) :=
  pullback (baseEquiv w j hj i) (pullback (Subtype.val : traceOpen w j hj i → (w i).ambient) (raw i))

variable {H : ℕ → ℕ} (hRaw : ∀ i, IsNativeWindowRecord (w i) (raw i) H)

include hRaw

theorem raw_native (i : ι) : NativeHSState (rawRecord w j hj raw i) (window w j hj i).carrier H :=
  NativeHSState.pullback (baseEquiv w j hj i) ((hRaw i).2.2.restrict (traceOpen w j hj i))

theorem raw_domain (i : ι) : IsInvDomain n (rawRecord w j hj raw i) :=
  InvDomainTowerAlong.isInvDomain_pullback (baseEquiv w j hj i)
    (InvDomainTowerAlong.isInvDomain_pullback_val (traceOpen w j hj i) (hRaw i).1)

theorem raw_boundary (i : ι) : (rawRecord w j hj raw i).E = [] := by
  change ((raw i).E.map _).map _ = []
  rw [(hRaw i).2.1, List.map_nil, List.map_nil]

theorem native_record (i : ι) : IsNativeWindowRecord (window w j hj i) (rawRecord w j hj raw i) H :=
  ⟨raw_domain w j hj raw hRaw i, raw_boundary w j hj raw hRaw i, raw_native w j hj raw hRaw i⟩

variable (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)

def record (i : ι) : MarkedIdeal n (Amb (window w j hj) i) := powerMarked (rawRecord w j hj raw i) (e i)

theorem record_eq_pullback (i : ι) : record w j hj raw e i =
    pullback (baseEquiv w j hj i) (pullback (Subtype.val : traceOpen w j hj i → (w i).ambient)
      (powerMarked (raw i) (e i))) := by
  have hOpen := HironakaG11PresClassTransport.pullback_powerMarked
    (M := Amb w i) (M' := CMfd.of (n := n) (traceOpen w j hj i))
    contMDiff_subtype_val (raw i) (hRaw i).1.isWellFormed.isCoherent (e i)
  have hTrace := InvDomainTowerAlong.isInvDomain_pullback_val (traceOpen w j hj i) (hRaw i).1
  have hFlat := HironakaG11PresClassTransport.pullback_powerMarked
    (M := CMfd.of (n := n) (traceOpen w j hj i)) (M' := Amb (window w j hj) i)
    (baseEquiv w j hj i).contMDiff _ hTrace.isWellFormed.isCoherent (e i)
  exact hFlat.symm.trans (congrArg (pullback (baseEquiv w j hj i)) hOpen.symm)

variable (hd : ∀ i k, (powerMarked (raw i) (e i)).d = (powerMarked (raw k) (e k)).d)

include he hd in
theorem initialClass : InitialClassData (window w j hj) (record w j hj raw e) :=
  HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers (window w j hj)
    (rawRecord w j hj raw) H (native_record w j hj raw hRaw) e he hd

omit hRaw

variable {Λ : Type*} [LinearOrder Λ] (R : ResolutionInvariant.{0} n n Λ)
  (i : ι) {Y : CMfd.{0} n} (T : BlowupTower (Amb w i) Y)
  (hT : IsCanonical (powerMarked (raw i) (e i)) (R.inv (powerMarked (raw i) (e i))) T)

private def restrictedTower : BlowupTower (CMfd.of (n := n) (traceOpen w j hj i))
    (CMfd.of (n := n) (openPreimage T (traceOpen w j hj i))) := restrict (traceOpen w j hj i) T

/-- First restrict the SAME physical history, then genuinely transport its base. -/
def history : TowerTransport (Amb (window w j hj) i) (CMfd.of (n := n) (openPreimage T (traceOpen w j hj i))) :=
  MarkedIdealTowerTransport.transport (baseEquiv w j hj i) (restrictedTower w j hj i T)

theorem history_isTowerIso : IsTowerIso (baseEquiv w j hj i) (history w j hj i T).tower
    (restrict (traceOpen w j hj i) T) (history w j hj i T).back :=
  BlowupTowerIsomorphism.transport_isTowerIso (baseEquiv w j hj i) (restrictedTower w j hj i T)

include hT hRaw he in
theorem history_canonical : IsCanonical (record w j hj raw e i) (R.inv (record w j hj raw e i))
    (history w j hj i T).tower := by
  rw [record_eq_pullback w j hj raw hRaw e i]
  exact Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R
    (InvDomainTowerAlong.isInvDomain_pullback_val (traceOpen w j hj i)
      (powerMarked_isInvDomain _ (hRaw i).1 (he i)))
    (baseEquiv w j hj i) (history_isTowerIso w j hj i T)
    (Seq.ResolutionInvariantExt.isCanonical_restrict R (powerMarked_isInvDomain _ (hRaw i).1 (he i))
      (traceOpen w j hj i) T hT)

theorem history_length : (history w j hj i T).tower.length = T.length :=
  (history_isTowerIso w j hj i T).length_eq.trans (length_restrict _ _)

include hT hRaw he in
theorem history_transform : geoTransformAlong (record w j hj raw e i) (history w j hj i T).tower =
    pullback (history w j hj i T).back
      (pullback (Subtype.val : openPreimage T (traceOpen w j hj i) → Y)
        (geoTransformAlong (powerMarked (raw i) (e i)) T)) := by
  have hD := powerMarked_isInvDomain _ (hRaw i).1 (he i)
  have hD' := InvDomainTowerAlong.isInvDomain_pullback_val (traceOpen w j hj i) hD
  have hCan := Seq.ResolutionInvariantExt.isCanonical_restrict R hD (traceOpen w j hj i) T hT
  rw [record_eq_pullback w j hj raw hRaw e i]
  exact (IsTowerIso.geoTransformAlong_eq (baseEquiv w j hj i)
    hD'.isWellFormed.isClosedSubmanifold_N hD'.isWellFormed.isCoherent
    (history_isTowerIso w j hj i T)
    (R.isInvValue.isGeoTestTower_of_isCanonical hD' _ hCan)).trans
    (congrArg (pullback (history w j hj i T).back)
      (MarkedIdealRestrictOpen.geoTransformAlong_restrict (traceOpen w j hj i)
        hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent T
        (R.isInvValue.isGeoTestTower_of_isCanonical hD T hT)))

include hT hRaw he in
theorem history_boundary : (geoTransformAlong (record w j hj raw e i) (history w j hj i T).tower).E =
    ((geoTransformAlong (powerMarked (raw i) (e i)) T).E.map
      ((Subtype.val : openPreimage T (traceOpen w j hj i) → Y) ⁻¹' ·)).map
        ((history w j hj i T).back ⁻¹' ·) :=
  congrArg MarkedIdeal.E (history_transform w j hj raw hRaw e he R i T hT)

include hT hRaw he in
theorem history_value (z : (history w j hj i T).target)
    (hz : ((history w j hj i T).back z).val ∈ (geoTransformAlong (powerMarked (raw i) (e i)) T).cosupp) :
    R.inv (record w j hj raw e i) (history w j hj i T).tower z =
      R.inv (powerMarked (raw i) (e i)) T ((history w j hj i T).back z).val := by
  have hD := powerMarked_isInvDomain _ (hRaw i).1 (he i)
  have hD' := InvDomainTowerAlong.isInvDomain_pullback_val (traceOpen w j hj i) hD
  have hCan := Seq.ResolutionInvariantExt.isCanonical_restrict R hD (traceOpen w j hj i) T hT
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hD T hT
  have hz' : (history w j hj i T).back z ∈
      (geoTransformAlong (pullback (Subtype.val : traceOpen w j hj i → (w i).ambient)
        (powerMarked (raw i) (e i))) (restrict (traceOpen w j hj i) T)).cosupp := by
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent
      (traceOpen w j hj i) T hTest]
    exact hz
  rw [record_eq_pullback w j hj raw hRaw e i]
  exact (R.isInvValue.towerIso (baseEquiv w j hj i) _ hD'
    (history w j hj i T).tower (restrict (traceOpen w j hj i) T)
    (history w j hj i T).back (history_isTowerIso w j hj i T) hCan z hz').trans
    (R.isInvValue.restrictOpen _ hD (traceOpen w j hj i) T hT
      ((history w j hj i T).back z) hz)

theorem history_carrier : strictAlong (history w j hj i T).tower (window w j hj i).carrier =
    (history w j hj i T).back ⁻¹'
      ((Subtype.val : openPreimage T (traceOpen w j hj i) → Y) ⁻¹' strictAlong T (w i).carrier) := by
  rw [carrier_dictionary w j hj i]
  exact ((history_isTowerIso w j hj i T).strictAlong_eq _).trans
    (congrArg ((history w j hj i T).back ⁻¹' ·) (HironakaG11StrictTransformTowers.strictAlong_restrict (traceOpen w j hj i) T (w i).carrier))

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenWindows
