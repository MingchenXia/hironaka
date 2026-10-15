/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison
/-! Actual further restrictions of independent original local overlap maps.
Complete three-node mathematics preceded proof code. All real smaller-domain
memberships and pairwise transition compatibility are derived internally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalTerminalOverlapRestriction
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres MaxLocusLocal
  HironakaOriginalTerminalOverlapComparison
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

def commonOpenPointInclusion {U W W' : Opens X} (hW'W : W' ≤ W)
    (S : BlowupTower (CMfd.of (n := n) U) Y)
    (y : openPreimage S (nestedOpens U W')) : openPreimage S (nestedOpens U W) :=
  ⟨y.val,hW'W y.property⟩

theorem commonOpenPointInclusion_point {U W W' : Opens X} (hW'W : W' ≤ W)
    (S : BlowupTower (CMfd.of (n := n) U) Y)
    (y : openPreimage S (nestedOpens U W')) : (commonOpenPointInclusion hW'W S y).val=y.val := rfl

theorem commonOpenPointInclusion_holomorphic {U W W' : Opens X} (hW'W : W' ≤ W)
    (S : BlowupTower (CMfd.of (n := n) U) Y) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (commonOpenPointInclusion hW'W S) := by
  unfold commonOpenPointInclusion
  exact BlowupRestrictOpen.contMDiff_opens_mk (n := n) (m := n) (X := Y)
    (Z := openPreimage S (nestedOpens U W')) (V := openPreimage S (nestedOpens U W))
    contMDiff_subtype_val (fun y => hW'W y.property)

section OriginalRestriction
variable (M : MarkedIdeal n X) (hM : IsInvDomain n M)
  {U V W W' : Opens X} (hWU : W ≤ U) (hWV : W ≤ V) (hW'W : W' ≤ W)
  (S : BlowupTower (CMfd.of (n := n) U) Y)
  (T : BlowupTower (CMfd.of (n := n) V) Z)
  (hs : IsCanonical (pullback (Subtype.val : U → X) M)
    ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) S)
  (ht : IsCanonical (pullback (Subtype.val : V → X) M)
    ((canonicalInvariant n).inv (pullback (Subtype.val : V → X) M)) T)
  (hrs : IsGeoResolution (pullback (Subtype.val : U → X) M) S)
  (hrt : IsGeoResolution (pullback (Subtype.val : V → X) M) T)

/-- Original larger comparison supplies BOTH actual smaller subtype domains
and true inverse/holomorphic equations before smaller-map uniqueness. -/
def restrictedCommonOpenComparison :
    CMfd.of (n := n) (openPreimage S (nestedOpens U W'))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T (nestedOpens V W')) := by
  let η := commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt
  have hp := commonOpenTerminalComparison_proj M hM hWU hWV S T hs ht hrs hrt
  have hfwd : ∀ y : openPreimage S (nestedOpens U W'),
      (η (commonOpenPointInclusion hW'W S y)).val ∈ openPreimage T (nestedOpens V W') := by
    intro y
    change (T.proj (η (commonOpenPointInclusion hW'W S y)).val).val ∈ W'
    rw [hp,commonOpenPointInclusion_point]
    exact y.property
  have hinv : ∀ z : openPreimage T (nestedOpens V W'),
      (η.symm (commonOpenPointInclusion hW'W T z)).val ∈ openPreimage S (nestedOpens U W') := by
    intro z
    have h := hp (η.symm (commonOpenPointInclusion hW'W T z))
    rw [η.apply_symm_apply,commonOpenPointInclusion_point] at h
    change (S.proj (η.symm (commonOpenPointInclusion hW'W T z)).val).val ∈ W'
    rw [← h]
    exact z.property
  exact {
    toFun y := ⟨(η (commonOpenPointInclusion hW'W S y)).val,hfwd y⟩
    invFun z := ⟨(η.symm (commonOpenPointInclusion hW'W T z)).val,hinv z⟩
    left_inv y := by
      apply Subtype.ext
      change (η.symm (η (commonOpenPointInclusion hW'W S y))).val=y.val
      exact congrArg Subtype.val (η.symm_apply_apply (commonOpenPointInclusion hW'W S y))
    right_inv z := by
      apply Subtype.ext
      change (η (η.symm (commonOpenPointInclusion hW'W T z))).val=z.val
      exact congrArg Subtype.val (η.apply_symm_apply (commonOpenPointInclusion hW'W T z))
    contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
      (contMDiff_subtype_val.comp (η.contMDiff.comp (commonOpenPointInclusion_holomorphic hW'W S))) hfwd
    contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
      (contMDiff_subtype_val.comp (η.symm.contMDiff.comp (commonOpenPointInclusion_holomorphic hW'W T))) hinv }

theorem restrictedCommonOpenComparison_point (y : openPreimage S (nestedOpens U W')) :
    (restrictedCommonOpenComparison M hM hWU hWV hW'W S T hs ht hrs hrt y).val=
      (commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt
        (commonOpenPointInclusion hW'W S y)).val := rfl

theorem restrictedCommonOpenComparison_proj (y : openPreimage S (nestedOpens U W')) :
    (T.proj (restrictedCommonOpenComparison M hM hWU hWV hW'W S T hs ht hrs hrt y).val).val=
      (S.proj y.val).val := by
  rw [restrictedCommonOpenComparison_point,commonOpenTerminalComparison_proj,
    commonOpenPointInclusion_point]

theorem restrictedCommonOpenComparison_eq_smaller :
    restrictedCommonOpenComparison M hM hWU hWV hW'W S T hs ht hrs hrt=
      commonOpenTerminalComparison M hM (hW'W.trans hWU) (hW'W.trans hWV) S T hs ht hrs hrt := by
  apply biholomorphisms_eq_of_common_open_original_proj_eq T
  intro y
  exact (restrictedCommonOpenComparison_proj M hM hWU hWV hW'W S T hs ht hrs hrt y).trans
    (commonOpenTerminalComparison_proj M hM (hW'W.trans hWU) (hW'W.trans hWV) S T hs ht hrs hrt y).symm

/-- EVERY smaller original point retains its exact larger comparison value. -/
theorem commonOpenTerminalComparison_smaller_point
    (y : openPreimage S (nestedOpens U W')) :
    (commonOpenTerminalComparison M hM (hW'W.trans hWU) (hW'W.trans hWV) S T hs ht hrs hrt y).val=
      (commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt
        (commonOpenPointInclusion hW'W S y)).val := by
  rw [← restrictedCommonOpenComparison_eq_smaller]
  rfl
end OriginalRestriction

variable {P : CMfd.{u} n}

theorem original_pairwise_terminal_triple_transition
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U V O : Opens X)
    (S : BlowupTower (CMfd.of (n := n) U) Y)
    (T : BlowupTower (CMfd.of (n := n) V) Z)
    (R : BlowupTower (CMfd.of (n := n) O) P)
    (hs : IsCanonical (pullback (Subtype.val : U → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) S)
    (ht : IsCanonical (pullback (Subtype.val : V → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : V → X) M)) T)
    (hr : IsCanonical (pullback (Subtype.val : O → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : O → X) M)) R)
    (hrs : IsGeoResolution (pullback (Subtype.val : U → X) M) S)
    (hrt : IsGeoResolution (pullback (Subtype.val : V → X) M) T)
    (hrr : IsGeoResolution (pullback (Subtype.val : O → X) M) R)
    (y : openPreimage S (nestedOpens U (U ⊓ V)))
    (hyO : (S.proj y.val).val ∈ O) :
    ∃ z : openPreimage T (nestedOpens V (V ⊓ O)),
      z.val=(commonOpenTerminalComparison M hM inf_le_left inf_le_right S T hs ht hrs hrt y).val ∧
      (commonOpenTerminalComparison M hM inf_le_left inf_le_right T R ht hr hrt hrr z).val=
        (commonOpenTerminalComparison M hM inf_le_left inf_le_right S R hs hr hrs hrr
          ⟨y.val,⟨(S.proj y.val).property,hyO⟩⟩).val := by
  let η := commonOpenTerminalComparison M hM (W := U ⊓ V) inf_le_left inf_le_right S T hs ht hrs hrt
  have hzVO : (η y).val ∈ openPreimage T (nestedOpens V (V ⊓ O)) := by
    change (T.proj (η y).val).val ∈ V ⊓ O
    refine ⟨(T.proj (η y).val).property,?_⟩
    rw [commonOpenTerminalComparison_proj]
    exact hyO
  let z : openPreimage T (nestedOpens V (V ⊓ O)) := ⟨(η y).val,hzVO⟩
  refine ⟨z,rfl,?_⟩
  let Q : Opens X := (U ⊓ V) ⊓ O
  have hQU : Q ≤ U := inf_le_left.trans inf_le_left
  have hQV : Q ≤ V := inf_le_left.trans inf_le_right
  have hQO : Q ≤ O := inf_le_right
  have hQUV : Q ≤ U ⊓ V := inf_le_left
  have hQVO : Q ≤ V ⊓ O := le_inf hQV hQO
  have hQUO : Q ≤ U ⊓ O := le_inf hQU hQO
  let yw : openPreimage S (nestedOpens U Q) := ⟨y.val,⟨y.property,hyO⟩⟩
  let ηST := commonOpenTerminalComparison M hM hQU hQV S T hs ht hrs hrt
  let ηTR := commonOpenTerminalComparison M hM hQV hQO T R ht hr hrt hrr
  let ηSR := commonOpenTerminalComparison M hM hQU hQO S R hs hr hrs hrr
  have heST := commonOpenTerminalComparison_smaller_point M hM inf_le_left inf_le_right hQUV
    S T hs ht hrs hrt yw
  change (ηST yw).val=z.val at heST
  have heTR := commonOpenTerminalComparison_smaller_point M hM inf_le_left inf_le_right hQVO
    T R ht hr hrt hrr (ηST yw)
  have hincTR : commonOpenPointInclusion hQVO T (ηST yw)=z := Subtype.ext heST
  rw [hincTR] at heTR
  have heSR := commonOpenTerminalComparison_smaller_point M hM inf_le_left inf_le_right hQUO
    S R hs hr hrs hrr yw
  have hincSR : commonOpenPointInclusion hQUO S yw=
      (⟨y.val,⟨(S.proj y.val).property,hyO⟩⟩ : openPreimage S (nestedOpens U (U ⊓ O))) := rfl
  rw [hincSR] at heSR
  have hco := congrArg (fun e => (e yw).val)
    (commonOpenTerminalComparison_trans M hM hQU hQV S T hs ht hrs hrt hQO R hr hrr)
  change (ηTR (ηST yw)).val=(ηSR yw).val at hco
  exact heTR.symm.trans (hco.trans heSR)

end
end Hironaka.HironakaOriginalTerminalOverlapRestriction
