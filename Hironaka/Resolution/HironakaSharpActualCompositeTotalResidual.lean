/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualOriginalTotalHistoryResidual

/-! Literal ORIGINAL composite raw pullback, with true carrier normalization,
BEFORE the WHOLE ALL-accumulated nonmonomial/chronological STRICT dictionary.
No earlier original full-invariant history or modified decrease is inferred. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCompositeTotalResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualOriginalTotalHistoryResidual HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MarkedIdealOperationsAlong GermIdealOrder InvertibleIdealQuotient RestrictLeCalculus
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- BOTH actual finite restricted-span relations pull back before WHOLE
normalization; no submersion or endpoint dictionary is supplied. -/
theorem actual_normalized_pullback_restrictOn {N : Set X} {W : Set Y}
    (hN : IsClosedSubmanifold n N) (hW : IsClosed W) {I : GermIdeal n X} (hI : I.IsCoherent)
    {f : Y → X} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hWN : ∀ y ∈ W,f y ∈ N) :
    restrictOn n W (GermIdeal.pullback f (restrictOn n N I))=restrictOn n W (GermIdeal.pullback f I) := by
  have hc := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  exact restrictOn_eq_of_restrictLe hW
    (restrictLe_pullback hf hWN hI restrictLe_restrictOn)
    (restrictLe_pullback hf hWN hc (restrictLe_self_restrictOn hI))

/-- The literal actual zero-mark record at EVERY true finite position equals
ORIGINAL raw pullback by its actual composite projection, normalized on SAME N. -/
theorem original_zero_history_eq_composite_total {W : Set X} {E : List (Set X)}
    {I : GermIdeal n X} (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W E) T →
      let M : MarkedIdeal n X := ⟨W,E,restrictOn n W I,0⟩
      let Q := geoTransformAlong M T
      Q.ideal=restrictOn n Q.N (GermIdeal.pullback T.proj I)
  | _, .refl, _ => by
    change restrictOn n W I=restrictOn n W (GermIdeal.pullback (id : X → X) I)
    rw [BlowupControlledTransform.pullback_id hI]
  | _, .step T C π hπ, hT => by
    let M : MarkedIdeal n X := ⟨W,E,restrictOn n W I,0⟩
    let Q := geoTransformAlong M T
    have hcM := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
    obtain ⟨hNc,_hIc⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier hW hcM
      (𝔍 := M) (𝔪 := geometricTemplate W E) rfl T hT.1
    have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W E) rfl T
    have hCN : C ⊆ Q.N := by rw [hQN]; exact hT.2.subset_N
    have hNew := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hNc hCN
    have hMap : ∀ y ∈ (Q.geoTransform C π).N,π y ∈ Q.N :=
      fun _ hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc.1 hy
    have hcB := GermIdealPullbackCalculus.isCoherent_pullback T.contMDiff_proj hI
    have hIH := original_zero_history_eq_composite_total hW hI T hT.1
    change Q.ideal=restrictOn n Q.N (GermIdeal.pullback T.proj I) at hIH
    change (Q.geoTransform C π).ideal=restrictOn n (Q.geoTransform C π).N (GermIdeal.pullback (T.proj ∘ π) I)
    rw [geoTransform_zeroMark_ideal_eq_restricted_total Q (d_geoTransformAlong M T),hIH,
      GermIdealTotalTransform.pullback_comp T.contMDiff_proj hπ.contMDiff hI]
    exact actual_normalized_pullback_restrictOn hNc hNew.1 hcB hπ.contMDiff hMap

/-- ONLY original SNC/density and actual geometry history: strip ALL real
accumulated exceptional factors from LITERAL composite ORIGINAL member TOTAL. -/
theorem original_member_composite_total_residual_eq (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let M := originalRelativeMemberMarked W (E.get i)
    let Q := geoTransformAlong M T
    nonmonomialPartAlong n Q.N (GermIdeal.pullback T.proj (vanishingIdeal (n := n) (E.get i))) Q.E=
      (chronologicalMarked M T).ideal := by
  let M := originalRelativeMemberMarked W (E.get i)
  let Q := geoTransformAlong M T
  have hcI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hWhole := original_zero_history_eq_composite_total (E := []) hW hcI T hT
  have hHist := original_member_total_history_residual_eq hn hW hE hdense i T hT
  change nonmonomialPartAlong n Q.N Q.ideal Q.E=(chronologicalMarked M T).ideal at hHist
  change Q.ideal=restrictOn n Q.N (GermIdeal.pullback T.proj (vanishingIdeal (n := n) (E.get i))) at hWhole
  rw [hWhole] at hHist
  have hQcoh := isCoherent_restrictOn hcI (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
  obtain ⟨hNc,_hcQ⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier hW hQcoh
    (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T hT
  have hcB := GermIdealPullbackCalculus.isCoherent_pullback T.contMDiff_proj hcI
  exact (MonomialPartEtale.nonmonomialPartAlong_congr hNc.1
    (restrictLe_self_restrictOn hcB) restrictLe_restrictOn).trans hHist

end
end Hironaka.HironakaSharpActualCompositeTotalResidual
