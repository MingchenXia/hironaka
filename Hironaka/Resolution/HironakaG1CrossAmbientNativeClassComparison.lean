import Hironaka.Resolution.HironakaG1CrossAmbientNativeComparison
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical

/-! Actual cross-ambient comparison through two native representatives
of one weak test class, with their original marks. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1CrossAmbientNativeClassComparison

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres DivisorExponentAlong
  HironakaActualNativeInvariantDomain HironakaG1CrossAmbientNativeComparison
  HironakaG1OriginalUnequalMarkCanonical HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaSmoothSubmersionCanonicalValueDimensionShift

variable {m m₁ m₂ k q : ℕ} {A Z : CMfd.{0} k}
  {C C₁ C₂ : MarkedIdeal k A} {S : BlowupTower A Z}

private theorem chartDomain (R : NativeChartRealization C S m q) (hk : 0 < k) : IsInvDomain q C := by
  rw [← R.record_eq]
  exact InvDomainTowerAlong.isInvDomain_pullback R.sourceEquiv
    (isInvDomain_nativePullback (hk.trans_le R.dimLE) R.dimLE R.sourceRegular
      R.record R.domain R.carrier R.transverse)

set_option maxHeartbeats 850000 in
/-- Two supported ambient histories may use different actual native
representatives. Source weak test equivalence, the common carrier
dimension and normalized boundary exponents suffice for cross-ambient
canonicality, order and maximum-locus comparison. -/
theorem cross_ambient_native_comparison_of_class
    (R₁ : NativeChartRealization C₁ S m₁ q) (R₂ : NativeChartRealization C₂ S m₂ q)
    (hk : 0 < k) (hClass : LocWPEquiv C₁ C₂) (hDim : SameCarrierDim C₁ C₂)
    (hExp : ∀ H ∈ C₁.E, ∀ x ∈ C₁.cosupp, x ∈ H →
      C₂.d * divExpAlong k C₁.N C₁.ideal H x = C₁.d * divExpAlong k C₂.N C₂.ideal H x) :
    let f₁ := R₁.ambientInvariant hk R₁.tower
    let f₂ := R₂.ambientInvariant hk R₂.tower
    let g₁ := (invFamily hk q).inv C₁ S
    let D := (geoTransformAlong C₁ S).cosupp
    let E₁ := (geoTransformAlong R₁.record R₁.tower).cosupp
    let E₂ := (geoTransformAlong R₂.record R₂.tower).cosupp
    (IsCanonical R₁.record (R₁.ambientInvariant hk) R₁.tower ↔
      IsCanonical R₂.record (R₂.ambientInvariant hk) R₂.tower) ∧
    (IsCanonical R₁.record (R₁.ambientInvariant hk) R₁.tower →
      R₁.endpointMap '' D = E₁ ∧ R₂.endpointMap '' D = E₂ ∧
      (∀ x ∈ D, ∀ y ∈ D, f₁ (R₁.endpointMap x) < f₁ (R₁.endpointMap y) ↔
        f₂ (R₂.endpointMap x) < f₂ (R₂.endpointMap y)) ∧
      R₁.endpointMap ⁻¹' maxLocus f₁ E₁ = R₂.endpointMap ⁻¹' maxLocus f₂ E₂ ∧
      R₁.endpointMap '' maxLocus g₁ D = maxLocus f₁ E₁ ∧
      R₂.endpointMap '' maxLocus g₁ D = maxLocus f₂ E₂) := by
  intro f₁ f₂ g₁ D E₁ E₂
  let I := invFamily hk q
  let g₂ := I.inv C₂ S
  let D₂ := (geoTransformAlong C₂ S).cosupp
  have hC₁ := chartDomain R₁ hk
  have hC₂ := chartDomain R₂ hk
  obtain ⟨hCan₁, hData₁⟩ := R₁.compare hk
  obtain ⟨hCan₂, hData₂⟩ := R₂.compare hk
  have hChartCan := invFamily_isCanonical_iff_of_local hk C₁ C₂ hC₁ hC₂ hClass hDim hExp S
  have hCan := hCan₁.symm.trans (hChartCan.trans hCan₂)
  refine ⟨hCan, fun h => ?_⟩
  have hNC₁ := hCan₁.mpr h
  have hNC₂ := hChartCan.mp hNC₁
  have hTest := I.isInvValue.isGeoTestTower_of_isCanonical hC₁ S hNC₁
  have hCos : D = D₂ := (hClass.wEquiv.2 S).2 hTest
  obtain ⟨hS₁, _, hv₁, hPre₁, hMax₁⟩ := hData₁ h
  obtain ⟨hS₂, _, hv₂, hPre₂, hMax₂⟩ := hData₂ (hCan.mp h)
  have hOrder (x y : Z) (hx : x ∈ D) (hy : y ∈ D) :
      g₁ x < g₁ y ↔ g₂ x < g₂ y :=
    canonicalTwoPairCuts_invFamily hk q C₁ C₂ C₁ C₂ hC₁ hC₂ hC₁ hC₂
      hClass hDim hExp hClass hDim hExp rfl rfl trivial trivial trivial trivial
      S S hNC₁ hNC₂ hNC₁ hNC₂ x hx y hy
  have hMaxChart : maxLocus g₁ D = maxLocus g₂ D₂ := by
    rw [← hCos]
    ext z
    change (z ∈ D ∧ ∀ y ∈ D, g₁ y ≤ g₁ z) ↔ (z ∈ D ∧ ∀ y ∈ D, g₂ y ≤ g₂ z)
    constructor
    · rintro ⟨hz, hMax⟩
      exact ⟨hz, fun y hy => not_lt.mp ((not_congr (hOrder z y hz hy)).mp (not_lt.mpr (hMax y hy)))⟩
    · rintro ⟨hz, hMax⟩
      exact ⟨hz, fun y hy => not_lt.mp ((not_congr (hOrder z y hz hy)).mpr (not_lt.mpr (hMax y hy)))⟩
  refine ⟨hS₁, hCos.symm ▸ hS₂, ?_, hPre₁.symm.trans (hMaxChart.trans hPre₂), hMax₁,
    (congrArg (fun L => R₂.endpointMap '' L) hMaxChart).trans hMax₂⟩
  intro x hx y hy
  have h₁ : f₁ (R₁.endpointMap x) < f₁ (R₁.endpointMap y) ↔ g₁ x < g₁ y := by
    have hX : f₁ (R₁.endpointMap x) = familyDimensionMap (m₁ - k) q (g₁ x) := hv₁ x hx
    have hY : f₁ (R₁.endpointMap y) = familyDimensionMap (m₁ - k) q (g₁ y) := hv₁ y hy
    rw [hX, hY]
    exact (strictMono_familyDimensionMap (m₁ - k) q).lt_iff_lt
  have h₂ : f₂ (R₂.endpointMap x) < f₂ (R₂.endpointMap y) ↔ g₂ x < g₂ y := by
    have hx₂ : x ∈ D₂ := hCos ▸ hx
    have hy₂ : y ∈ D₂ := hCos ▸ hy
    have hX : f₂ (R₂.endpointMap x) = familyDimensionMap (m₂ - k) q (g₂ x) := hv₂ x hx₂
    have hY : f₂ (R₂.endpointMap y) = familyDimensionMap (m₂ - k) q (g₂ y) := hv₂ y hy₂
    rw [hX, hY]
    exact (strictMono_familyDimensionMap (m₂ - k) q).lt_iff_lt
  exact h₁.trans ((hOrder x y hx hy).trans h₂.symm)

end

end Hironaka.HironakaG1CrossAmbientNativeClassComparison
