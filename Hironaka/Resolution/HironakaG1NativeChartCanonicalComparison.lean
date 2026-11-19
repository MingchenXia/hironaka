import Hironaka.Resolution.HironakaG1NormalUnequalDepth
import Hironaka.Resolution.HironakaG8LocalTransport

/-! Original invariant comparisons for an actual native lift written in
an independent source chart. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NativeChartCanonicalComparison

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  RelativePrincipalizationSpan BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  NormalCrossings HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeInvariantDomain HironakaActualNativeSectionOrderHistory
  HironakaG1NormalUnequalDepth HironakaG1NormalCentreTransport
  HironakaOriginalFamilyDepthStability HironakaActualSectionBoundaryDimension
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaG8LocalTransport

variable {m k q : ℕ} {X Y : CMfd.{0} m} {A Z : CMfd.{0} k} {hk : k ≤ m}
  {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := m) W x k}
  {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := m) V y k}

set_option maxHeartbeats 900000 in
/-- On a genuine native lift of a supported marked record, writing the
native source and endpoint in independent biholomorphic charts preserves
and reflects original canonicality. At the offset bound it gives the
exact recursive comparison and both maximum-locus formulas. -/
theorem original_native_chart_comparison (hm : 0 < m) (hkpos : 0 < k)
    (M : MarkedIdeal m X) (hM : IsInvDomain q M) (hMN : M.N ⊆ W)
    (hTrans : IsTransverse m W M.E)
    {T : BlowupTower X Y} {N : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (hLift : Lift hk W hWc hW M.E T V hVc hV N)
    (e : A ≃ₘ⟮𝓘(ℂ, ComplexModel k), 𝓘(ℂ, ComplexModel k)⟯ nativeManifold hk W hW)
    (S : BlowupTower A Z)
    (χ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel k), 𝓘(ℂ, ComplexModel k)⟯ nativeManifold hk V hV)
    (hIso : IsTowerIso e S N χ) :
    let B := nativePullback hk W hW M
    let C := MarkedIdeal.pullback e B
    let i := fun z : Z => (χ z).val
    let f := (invFamily hm ((m - k) + q)).inv M T
    let g := (invFamily hkpos q).inv C S
    let D := maxLocus f (geoTransformAlong M T).cosupp
    let L := maxLocus g (geoTransformAlong C S).cosupp
    IsInvDomain q C ∧
      (IsCanonical C ((invFamily hkpos q).inv C) S ↔
        IsCanonical M ((invFamily hm ((m - k) + q)).inv M) T) ∧
      (IsCanonical M ((invFamily hm ((m - k) + q)).inv M) T →
        (geoTransformAlong C S).cosupp = i ⁻¹' (geoTransformAlong M T).cosupp ∧
        i '' (geoTransformAlong C S).cosupp = (geoTransformAlong M T).cosupp ∧
        (∀ z : Z, i z ∈ (geoTransformAlong M T).cosupp →
          f (i z) = familyDimensionMap (m - k) q (g z)) ∧
        L = i ⁻¹' D ∧ i '' L = D) := by
  intro B C i f g D L
  let R := invFamily hkpos q
  have hB : IsInvDomain q B := isInvDomain_nativePullback hm hk hW M hM hMN hTrans
  have hC : IsInvDomain q C := InvDomainTowerAlong.isInvDomain_pullback e hB
  have hBack : MarkedIdeal.pullback e.symm C = B :=
    pullback_symm_pullback e hB.isWellFormed.isCoherent
  have hCcan : IsCanonical C (R.inv C) S ↔ IsCanonical B (R.inv B) N := by
    constructor
    · intro h
      have h' := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
        (X := A) (X' := nativeManifold hk W hW) R hC e.symm
        (T' := N) (χ := χ.symm) hIso.symm h
      rwa [hBack] at h'
    · exact Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
        (X := nativeManifold hk W hW) (X' := A) R hB e (T' := S) (χ := χ) hIso
  have hAmbient := Lift.original_padded_bound_comparison hm hkpos (m - k)
    M hM hMN hTrans hLift
  refine ⟨hC, hCcan.trans hAmbient.1, fun hCan => ?_⟩
  have hCanB := hAmbient.1.mpr hCan
  have hTestB := R.isInvValue.isGeoTestTower_of_isCanonical hB N hCanB
  have hValB (z : nativeManifold hk V hV) (hz : z.val ∈ (geoTransformAlong M T).cosupp) :
      f z.val = familyDimensionMap (m - k) q (R.inv B N z) :=
    (hAmbient.2 hCan z hz).trans (depthPadMap_sameIndexMap (m - k) q _)
  have hCosB := Lift.current_cosupport hLift hm hM.isWellFormed.isSNCDivisor hTrans M rfl hMN
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent h)
  have hCosC := IsTowerIso.cosupp_geoTransformAlong (X' := A) e
    hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hIso hTestB
  have hPre : (geoTransformAlong C S).cosupp = i ⁻¹' (geoTransformAlong M T).cosupp :=
    hCosC.trans (congrArg (fun E => χ ⁻¹' E) hCosB)
  have hRange : (geoTransformAlong M T).cosupp ⊆ range i := by
    intro y hy
    have hyV := Lift.current_carrier_subset hLift M hMN ((geoTransformAlong M T).cosupp_subset_N hy)
    exact ⟨χ.symm ⟨y, hyV⟩, congrArg Subtype.val (χ.apply_symm_apply ⟨y, hyV⟩)⟩
  have hImage : i '' (geoTransformAlong C S).cosupp = (geoTransformAlong M T).cosupp := by
    rw [hPre, image_preimage_eq_inter_range]
    exact inter_eq_left.mpr hRange
  have hValue (z : Z) (hz : i z ∈ (geoTransformAlong M T).cosupp) :
      f (i z) = familyDimensionMap (m - k) q (g z) := by
    have hzB : χ z ∈ (geoTransformAlong B N).cosupp := hCosB.symm ▸ hz
    have heq := R.isInvValue.towerIso (X' := A) e B hB S N χ hIso hCanB z hzB
    exact (hValB (χ z) hz).trans (congrArg (familyDimensionMap (m - k) q) heq.symm)
  have hMax : L = i ⁻¹' D := by
    ext z
    change (z ∈ (geoTransformAlong C S).cosupp ∧
      ∀ x ∈ (geoTransformAlong C S).cosupp, g x ≤ g z) ↔
      (i z ∈ (geoTransformAlong M T).cosupp ∧
        ∀ x ∈ (geoTransformAlong M T).cosupp, f x ≤ f (i z))
    rw [hPre]
    have compare (x : Z) (hx : i x ∈ (geoTransformAlong M T).cosupp)
        (hz : i z ∈ (geoTransformAlong M T).cosupp) :
        f (i x) ≤ f (i z) ↔ g x ≤ g z := by
      rw [hValue x hx, hValue z hz]
      exact (strictMono_familyDimensionMap (m - k) q).le_iff_le
    constructor
    · rintro ⟨hz, hMax⟩
      refine ⟨hz, fun x hx => ?_⟩
      obtain ⟨w, rfl⟩ := hRange hx
      exact (compare w hx hz).mpr (hMax w hx)
    · exact fun ⟨hz, hMax⟩ => ⟨hz, fun x hx => (compare x hx hz).mp (hMax _ hx)⟩
  refine ⟨hPre, hImage, hValue, hMax, ?_⟩
  rw [hMax, image_preimage_eq_inter_range]
  exact inter_eq_left.mpr (fun x hx => hRange hx.1)

end

end Hironaka.HironakaG1NativeChartCanonicalComparison
