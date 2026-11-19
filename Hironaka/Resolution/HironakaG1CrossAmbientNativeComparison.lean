import Hironaka.Resolution.HironakaG1NativeChartCanonicalComparison

/-! Comparing two actual supported ambient histories through one literal
native chart history, at their own offset bounds. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1CrossAmbientNativeComparison

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres NormalCrossings
  HironakaActualNativeSectionFiniteHistory HironakaG1NativeChartCanonicalComparison
  HironakaSmoothSubmersionCanonicalValueDimensionShift

variable {m m₁ m₂ k q : ℕ} {A Z : CMfd.{0} k}
  {C : MarkedIdeal k A} {S : BlowupTower A Z}

/-- A supported ambient history together with its actual native realization
in a specified chart tower. The source marked record, including every
boundary slot, is identified in that chart. -/
structure NativeChartRealization {k : ℕ} {A Z : CMfd.{0} k}
    (C : MarkedIdeal k A) (S : BlowupTower A Z) (m q : ℕ) where
  base : CMfd.{0} m
  target : CMfd.{0} m
  record : MarkedIdeal m base
  domain : IsInvDomain q record
  tower : BlowupTower base target
  dimLE : k ≤ m
  sourceSupport : Set base
  sourceClosed : IsClosed sourceSupport
  sourceRegular : ∀ x ∈ sourceSupport, RegularAtDim (n := m) sourceSupport x k
  carrier : record.N ⊆ sourceSupport
  transverse : IsTransverse m sourceSupport record.E
  targetSupport : Set target
  targetClosed : IsClosed targetSupport
  targetRegular : ∀ y ∈ targetSupport, RegularAtDim (n := m) targetSupport y k
  nativeTower : BlowupTower (nativeManifold dimLE sourceSupport sourceRegular)
    (nativeManifold dimLE targetSupport targetRegular)
  lift : Lift dimLE sourceSupport sourceClosed sourceRegular record.E tower
    targetSupport targetClosed targetRegular nativeTower
  sourceEquiv : A ≃ₘ⟮𝓘(ℂ, ComplexModel k), 𝓘(ℂ, ComplexModel k)⟯
    nativeManifold dimLE sourceSupport sourceRegular
  targetEquiv : Z ≃ₘ⟮𝓘(ℂ, ComplexModel k), 𝓘(ℂ, ComplexModel k)⟯
    nativeManifold dimLE targetSupport targetRegular
  towerIso : IsTowerIso sourceEquiv S nativeTower targetEquiv
  record_eq : MarkedIdeal.pullback sourceEquiv
    (nativePullback dimLE sourceSupport sourceRegular record) = C

/-- The comparison of endpoints uses the actual native tower chart map. -/
def NativeChartRealization.endpointMap (R : NativeChartRealization C S m q) (z : Z) : R.target :=
  (R.targetEquiv z).val

/-- The ambient value function at the offset depth for the realized native
bound, on all prefixes of the actual ambient base. -/
def NativeChartRealization.ambientInvariant (R : NativeChartRealization C S m q)
    (hkpos : 0 < k) {Y : CMfd.{0} m} (T : BlowupTower R.base Y) : Y → ValTy ((m - k) + q) :=
  (invFamily (hkpos.trans_le R.dimLE) ((m - k) + q)).inv R.record T

set_option maxHeartbeats 650000 in
/-- The actual chart realization preserves and reflects canonicality and,
on a canonical history, transports the cosupport, recursive values and
maximum loci in the same endpoint maps. -/
theorem NativeChartRealization.compare (R : NativeChartRealization C S m q) (hkpos : 0 < k) :
    let f := R.ambientInvariant hkpos R.tower
    let g := (invFamily hkpos q).inv C S
    let D := (geoTransformAlong C S).cosupp
    let E := (geoTransformAlong R.record R.tower).cosupp
    (IsCanonical C ((invFamily hkpos q).inv C) S ↔
      IsCanonical R.record (R.ambientInvariant hkpos) R.tower) ∧
    (IsCanonical R.record (R.ambientInvariant hkpos) R.tower →
      R.endpointMap '' D = E ∧ D = R.endpointMap ⁻¹' E ∧
      (∀ z ∈ D, f (R.endpointMap z) = familyDimensionMap (m - k) q (g z)) ∧
      maxLocus g D = R.endpointMap ⁻¹' maxLocus f E ∧
      R.endpointMap '' maxLocus g D = maxLocus f E) := by
  intro f g D E
  have h := original_native_chart_comparison (hkpos.trans_le R.dimLE) hkpos
    R.record R.domain R.carrier R.transverse R.lift R.sourceEquiv S R.targetEquiv R.towerIso
  dsimp only at h
  rw [R.record_eq] at h
  refine ⟨h.2.1, fun hCan => ?_⟩
  obtain ⟨hPre, hImage, hValue, hMaxPre, hMaxImage⟩ := h.2.2 hCan
  refine ⟨hImage, hPre, fun z hz => hValue z ?_, hMaxPre, hMaxImage⟩
  change z ∈ (fun z : Z => (R.targetEquiv z).val) ⁻¹' (geoTransformAlong R.record R.tower).cosupp
  rwa [← hPre]

set_option maxHeartbeats 650000 in
/-- Two supported ambient realizations of a literal native history have
equivalent original canonicality and induce exactly the same order at
the paired cosupport points. The common chart maximum maps onto both
ambient maximum loci, with exact preimages. The two ambient dimensions
and their offset bounds can differ. -/
theorem cross_ambient_native_comparison
    (R₁ : NativeChartRealization C S m₁ q) (R₂ : NativeChartRealization C S m₂ q) (hkpos : 0 < k) :
    let f₁ := R₁.ambientInvariant hkpos R₁.tower
    let f₂ := R₂.ambientInvariant hkpos R₂.tower
    let g := (invFamily hkpos q).inv C S
    let D := (geoTransformAlong C S).cosupp
    let E₁ := (geoTransformAlong R₁.record R₁.tower).cosupp
    let E₂ := (geoTransformAlong R₂.record R₂.tower).cosupp
    (IsCanonical R₁.record (R₁.ambientInvariant hkpos) R₁.tower ↔
      IsCanonical R₂.record (R₂.ambientInvariant hkpos) R₂.tower) ∧
    (IsCanonical R₁.record (R₁.ambientInvariant hkpos) R₁.tower →
      R₁.endpointMap '' D = E₁ ∧ R₂.endpointMap '' D = E₂ ∧
      (∀ x ∈ D, ∀ y ∈ D, f₁ (R₁.endpointMap x) < f₁ (R₁.endpointMap y) ↔
        f₂ (R₂.endpointMap x) < f₂ (R₂.endpointMap y)) ∧
      R₁.endpointMap ⁻¹' maxLocus f₁ E₁ = R₂.endpointMap ⁻¹' maxLocus f₂ E₂ ∧
      R₁.endpointMap '' maxLocus g D = maxLocus f₁ E₁ ∧
      R₂.endpointMap '' maxLocus g D = maxLocus f₂ E₂) := by
  intro f₁ f₂ g D E₁ E₂
  obtain ⟨hCan₁, hData₁⟩ := R₁.compare hkpos
  obtain ⟨hCan₂, hData₂⟩ := R₂.compare hkpos
  have hCan := hCan₁.symm.trans hCan₂
  refine ⟨hCan, fun h => ?_⟩
  obtain ⟨hS₁, _, hv₁, hPre₁, hMax₁⟩ := hData₁ h
  obtain ⟨hS₂, _, hv₂, hPre₂, hMax₂⟩ := hData₂ (hCan.mp h)
  refine ⟨hS₁, hS₂, ?_, hPre₁.symm.trans hPre₂, hMax₁, hMax₂⟩
  intro x hx y hy
  have h₁ : f₁ (R₁.endpointMap x) < f₁ (R₁.endpointMap y) ↔ g x < g y := by
    have hX : f₁ (R₁.endpointMap x) = familyDimensionMap (m₁ - k) q (g x) := hv₁ x hx
    have hY : f₁ (R₁.endpointMap y) = familyDimensionMap (m₁ - k) q (g y) := hv₁ y hy
    rw [hX, hY]
    exact (strictMono_familyDimensionMap (m₁ - k) q).lt_iff_lt
  have h₂ : f₂ (R₂.endpointMap x) < f₂ (R₂.endpointMap y) ↔ g x < g y := by
    have hX : f₂ (R₂.endpointMap x) = familyDimensionMap (m₂ - k) q (g x) := hv₂ x hx
    have hY : f₂ (R₂.endpointMap y) = familyDimensionMap (m₂ - k) q (g y) := hv₂ y hy
    rw [hX, hY]
    exact (strictMono_familyDimensionMap (m₂ - k) q).lt_iff_lt
  exact h₁.trans h₂.symm

end

end Hironaka.HironakaG1CrossAmbientNativeComparison
