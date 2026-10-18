/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteCentreImageSuperlevels
import Hironaka.Resolution.HironakaOriginalTerminalChoiceComparison
/-! Arbitrary FULL thresholds along EVERY actual ORIGINAL canonical history.
Real empty compression/whole-value order embedding and genuine finite canonical
alignment retain history. No current-invariant rebasing or analytic certificates.
Transformed original coefficient semicoherence / general BM13.4 driver OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalFullHistorySuperlevelsAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  BlowupTowerIsomorphism ResolutionInvariantSeq ResolutionInvariantDriver ResolutionInvariantOrder
  ResolutionDriver CanonicalCentres HironakaOriginalCompactUpperCutGlobalPhase
  HironakaOriginalFiniteCentreImageSuperlevels HironakaOriginalFiniteEmptyCompression
  HironakaOriginalTerminalChoiceComparison
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- The actual preimage under a genuine whole-value embedding is EMPTY or an
internally attained least-threshold cut; no surjectivity is assumed. -/
theorem threshold_preimage_of_orderEmbedding [WellFoundedLT Λ] (F : Λ ↪o Λ) (b : Λ) :
    (∀ v,¬b ≤ F v) ∨ ∃ c,∀ v,(b ≤ F v ↔ c ≤ v) := by
  by_cases hne : ({v | b ≤ F v} : Set Λ).Nonempty
  · obtain ⟨c,hc,hmin⟩ := (wellFounded_lt : WellFounded ((·<·) : Λ → Λ → Prop)).has_min {v | b ≤ F v} hne
    exact Or.inr ⟨c,fun v => ⟨fun hv => le_of_not_gt (hmin v hv),fun hv => hc.trans (F.monotone hv)⟩⟩
  · exact Or.inl (fun v hv => hne ⟨v,hv⟩)

private theorem same_base_segments_iso
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (Q : BlowupTower X Y) (V : BlowupTower X Z)
    (hQ : IsCanonicalSegment m (R.inv m) Q) (hV : IsCanonicalSegment m (R.inv m) V)
    (hlen : Q.length=V.length) :
    ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q V χ := by
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hpull : pullback Φ m=m := ContactCanonicalAlong.pullback_id m h.isWellFormed.isCoherent
  apply CanonicalResolution.exists_isTowerIso_of_length_eq R h Φ Q V
  · rw [hpull]
    exact hQ
  · exact hV
  · exact hlen

/-- Genuine partial/terminal alignment internally bounds the actual nonempty
canonical prefix length, without a caller length or head certificate. -/
theorem nonempty_canonical_length_le_terminal
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (Q : BlowupTower X Y) (V : BlowupTower X Z)
    (hQ : IsCanonicalSegment m (R.inv m) Q) (hV : IsCanonicalSegment m (R.inv m) V)
    (hrV : IsGeoResolution m V) : Q.length ≤ V.length := by
  by_contra hno
  have hgt : V.length<Q.length := Nat.lt_of_not_ge hno
  let r := Q.length-V.length
  have hsplit := head_append_tail Q r
  have hH : IsCanonicalSegment m (R.inv m) (head Q r) :=
    CanonicalResolution.isCanonicalSegment_of_append m (R.inv m) (head Q r) (tail Q r)
      (by rw [hsplit];exact hQ)
  have hlen : V.length=(head Q r).length := by rw [length_head];dsimp [r];omega
  obtain ⟨χ,hi⟩ := same_base_segments_iso R m h V (head Q r) hV hH hlen
  have hcanH := isCanonical_of_isCanonicalSegment (𝔪 := m) (R.inv m) (head Q r) hH
  have htH := R.isInvValue.isGeoTestTower_of_isCanonical h (head Q r) hcanH
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hpull : pullback Φ m=m := ContactCanonicalAlong.pullback_id m h.isWellFormed.isCoherent
  have hcos : (geoTransformAlong m (head Q r)).cosupp=∅ := by
    have he := IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hi htH
    rw [hpull,hrV.2] at he
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨p,rfl⟩ := χ.toEquiv.surjective y
    have hp : p ∈ χ ⁻¹' (geoTransformAlong m (head Q r)).cosupp := hy
    rw [← he] at hp
    exact hp
  have hz := CanonicalResolution.length_eq_zero_of_cosupp_eq_empty m (R.inv m) (head Q r) hcos (tail Q r)
    (by rw [hsplit];exact hQ)
  rw [length_tail] at hz
  dsimp [r] at hz
  omega

/-- Actual head/tail comparison plus actual canonical erasure constructs the
analytic cut, with true whole cosupport/value transport at the original history. -/
theorem nonempty_canonical_full_cut_analytic
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (Q : BlowupTower X Y) (V : BlowupTower X Z)
    (hQ : IsCanonicalSegment m (R.inv m) Q) (hV : IsCanonicalSegment m (R.inv m) V)
    (hrV : IsGeoResolution m V) (b : Λ) :
    IsComplexAnalyticSubset (n := n) (actualUpperCut R m Q b) := by
  have hle := nonempty_canonical_length_le_terminal R m h Q V hQ hV hrV
  let r := V.length-Q.length
  let H := head V r
  let S := tail V r
  have hsplit : H.append S=V := head_append_tail V r
  have hH : IsCanonicalSegment m (R.inv m) H :=
    CanonicalResolution.isCanonicalSegment_of_append m (R.inv m) H S (by rw [hsplit];exact hV)
  have hlen : Q.length=H.length := by change Q.length=(head V r).length;rw [length_head];dsimp [r];omega
  obtain ⟨χ,hi⟩ := same_base_segments_iso R m h Q H hQ hH hlen
  have hcH := isCanonical_of_isCanonicalSegment (𝔪 := m) (R.inv m) H hH
  have htH := R.isInvValue.isGeoTestTower_of_isCanonical h H hcH
  have hcApp : IsCanonical m (R.inv m) (H.append S) := by
    rw [hsplit]
    exact isCanonical_of_isCanonicalSegment (𝔪 := m) (R.inv m) V hV
  have hclear : actualUpperCut R m (H.append S) b=∅ := by
    rw [hsplit]
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hh := hz.1
    rw [hrV.2] at hh
    exact hh
  have hA := full_cut_analytic_of_actual_erasure R m h H b S hcApp hclear
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hpull : pullback Φ m=m := ContactCanonicalAlong.pullback_id m h.isWellFormed.isCoherent
  have hcos := IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hi htH
  rw [hpull] at hcos
  have hval : ∀ y ∈ (geoTransformAlong m Q).cosupp,R.inv m Q y=R.inv m H (χ y) := by
    intro y hy
    have hyH : χ y ∈ (geoTransformAlong m H).cosupp := by
      rw [hcos] at hy
      exact hy
    have hv := R.isInvValue.towerIso Φ m h Q H χ hi hcH y hyH
    rw [hpull] at hv
    exact hv
  have he : actualUpperCut R m Q b=χ ⁻¹' actualUpperCut R m H b := by
    ext y
    constructor
    · intro hy
      have hyH : χ y ∈ (geoTransformAlong m H).cosupp := by
        have hy0 := hy.1
        rw [hcos] at hy0
        exact hy0
      exact ⟨hyH,hy.2.trans_eq (hval y hy.1)⟩
    · intro hy
      have hyQ : y ∈ (geoTransformAlong m Q).cosupp := by rw [hcos];exact hy.1
      exact ⟨hyQ,hy.2.trans_eq (hval y hyQ).symm⟩
  rw [he]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage χ.contMDiff hA

/-- Original-only TRUE empty compression supplies actual Q/χ/F, actual
terminal compression, and BOTH full-threshold transport before analyticity. -/
theorem original_full_cut_analytic_of_actual_terminal (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y) (V : BlowupTower X Z)
    (hcT : IsCanonical m ((invFamily hn d).inv m) T)
    (hcV : IsCanonical m ((invFamily hn d).inv m) V) (hrV : IsGeoResolution m V) (b : ValTy d) :
    IsComplexAnalyticSubset (n := n) (actualUpperCut (invFamily hn d) m T b) := by
  obtain ⟨A,Q,χ,F,hneQ,_hlenQ,hcQ,_hp,hcos,hval,_hres⟩ :=
    original_recursive_family_empty_free_compression hn d m h T hcT
  obtain ⟨B,W,_ψ,_G,hneW,_hlenW,hcW,_hpW,_hcosW,_hvalW,hrW⟩ :=
    original_recursive_family_empty_free_compression hn d m h V hcV
  have hsQ := isCanonicalSegment_of_actual_nonempty_centres m ((invFamily hn d).inv m) Q hcQ hneQ
  have hsW := isCanonicalSegment_of_actual_nonempty_centres m ((invFamily hn d).inv m) W hcW hneW
  have hAQ : ∀ c,IsComplexAnalyticSubset (n := n) (actualUpperCut (invFamily hn d) m Q c) :=
    fun c => nonempty_canonical_full_cut_analytic (invFamily hn d) m h Q W hsQ hsW (hrW.mp hrV) c
  rcases threshold_preimage_of_orderEmbedding F b with hnone | ⟨c,hc⟩
  · have he : actualUpperCut (invFamily hn d) m T b=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hv : (invFamily hn d).inv m T y=F ((invFamily hn d).inv m Q (χ.symm y)) := hval y hy.1
      have hb := hy.2
      change b ≤ (invFamily hn d).inv m T y at hb
      rw [hv] at hb
      exact hnone _ hb
    rw [he]
    exact isComplexAnalyticSubset_empty
  · have he : actualUpperCut (invFamily hn d) m T b=χ.symm ⁻¹' actualUpperCut (invFamily hn d) m Q c := by
      ext y
      constructor
      · intro hy
        have hyQ : χ.symm y ∈ (geoTransformAlong m Q).cosupp := by
          have hy0 := hy.1
          rw [hcos] at hy0
          exact hy0
        have hv : (invFamily hn d).inv m T y=F ((invFamily hn d).inv m Q (χ.symm y)) := hval y hy.1
        have hb := hy.2
        change b ≤ (invFamily hn d).inv m T y at hb
        rw [hv] at hb
        exact ⟨hyQ,(hc _).mp hb⟩
      · intro hy
        have hyT : y ∈ (geoTransformAlong m T).cosupp := by rw [hcos];exact hy.1
        have hv : (invFamily hn d).inv m T y=F ((invFamily hn d).inv m Q (χ.symm y)) := hval y hyT
        refine ⟨hyT,?_⟩
        rw [hv]
        exact (hc _).mpr hy.2
    rw [he]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage χ.symm.contMDiff (hAQ c)

/-- ONLY original marked-domain/CAN/history inputs internally supply all true
local terminal/compressed/aligned histories, proving GLOBAL arbitrary FULL cuts. -/
theorem original_all_depth_full_history_global_analytic (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (b : ValTy d) :
    IsComplexAnalyticSubset (n := n) (actualUpperCut (invFamily hn d) m T b) := by
  intro y
  obtain ⟨U,hKU,Z,V,hcV,hrV⟩ := HironakaEmbeddedResolutionLocal.exists_local_resolution_isCanonical (invFamily hn d) h
    (K := ({T.proj y} : Set X)) isCompact_singleton
  let M := pullback (Subtype.val : U → X) m
  have hM := InvDomainTowerAlong.isInvDomain_pullback_val U h
  have hcU := Seq.ResolutionInvariantExt.isCanonical_restrict (invFamily hn d) h U T hc
  have hA := original_full_cut_analytic_of_actual_terminal hn d M hM (restrict U T) V hcU hcV hrV b
  have he := actual_upper_cut_open_preimage (invFamily hn d) m h U T hc b
  have hpre : IsComplexAnalyticSubset (n := n)
      ((Subtype.val : openPreimage T U → Y) ⁻¹' actualUpperCut (invFamily hn d) m T b) := he ▸ hA
  let p : openPreimage T U := ⟨y,hKU (mem_singleton (T.proj y))⟩
  obtain ⟨P⟩ := hpre p
  exact ⟨AnalyticSubsetOpens.presentationOfPreimageVal p P⟩

end
end Hironaka.HironakaOriginalFullHistorySuperlevelsAnalytic
