import Hironaka.Resolution.HironakaCompactFootprintSharpExtension
import Hironaka.Resolution.HironakaG34NonPureLowDim
import Hironaka.Resolution.HironakaG3CentresOverGenericFactor
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Invariant.ContactMarkedCanonical

/-! Patch an actual sharp service on a closed crest near an arbitrary compact
enclosure by shrinking only where the crest still needs service. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4SharpClosedCrestPatch
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  NormalCrossings NormalCrossingsComparison HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport GermIdealPullbackCalculus IdealWeightPowers
  RestrictEmptyTower MaxLocusLocal HironakaG3CentresOverGenericFactor
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaCompactFootprintSharpExtension HironakaG34NonPureLowDim

variable {n : ℕ} {X A Z : CMfd.{u} n}

/-- A finite actual sharp history on an open containing the part of a closed
crest met by an enclosure gives a whole actual history on a neighbourhood
of the enclosure. The support stays over the exact restricted crest, and
the given open history is identified as an actual restriction. -/
theorem exists_current_sharp_closed_crest_patch_over_open_equiv
    (N : Set X) (E : List (Set X)) (M : MarkedIdeal n X)
    (hNM : IsClosedSubmanifold n M.N) (hIM : M.ideal.IsCoherent)
    (U V : Opens X) (hVU : V ≤ U) {C K : Set X} (hC : IsClosed C)
    (hKU : K ⊆ U) (hKV : K ∩ C ⊆ V)
    (ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
    (T : BlowupTower A Z)
    (hOver : CentresOver (((Subtype.val : V → X) ∘ ψ) ⁻¹' C) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set A)
      (E.map (((Subtype.val : V → X) ∘ ψ) ⁻¹' ·))) T)
    (hM : IsGeoTestTower (MarkedIdeal.pullback ((Subtype.val : V → X) ∘ ψ) M) T)
    (hSharp : CurrentSharpCentres (((Subtype.val : V → X) ∘ ψ) ⁻¹' N)
      (E.map (((Subtype.val : V → X) ∘ ψ) ⁻¹' ·)) T) :
    ∃ (O : Opens X), K ⊆ O ∧ O ≤ U ∧ C ∩ (O : Set X) ⊆ V ∧ ∃ (hVO : V ≤ O) (Y : CMfd.{u} n)
        (Q : BlowupTower (CMfd.of (n := n) O) Y),
      IsGeoTestTower (geometricTemplate (univ : Set O)
        (E.map ((Subtype.val : O → X) ⁻¹' ·))) Q ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) Q ∧
      CurrentSharpCentres ((Subtype.val : O → X) ⁻¹' N)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) Q ∧
      CentresOver ((Subtype.val : O → X) ⁻¹' C) Q ∧
      ∃ χ : CMfd.of (n := n) (openPreimage Q (nestedOpens O V))
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
        IsTowerIso ((nestedOpensDiffeo hVO).trans ψ.symm) (restrict (nestedOpens O V) Q) T χ := by
  classical
  let O : Opens X := U ⊓ ⟨Cᶜ ∪ V,hC.isOpen_compl.union V.isOpen⟩
  have hKO : K ⊆ O := by
    intro x hx
    refine ⟨hKU hx,?_⟩
    by_cases hxC : x ∈ C
    · exact Or.inr (hKV ⟨hx,hxC⟩)
    · exact Or.inl hxC
  have hVO : V ≤ O := fun _ hx => ⟨hVU hx,Or.inr hx⟩
  let W := nestedOpens O V
  let β := (nestedOpensDiffeo (n := n) hVO).trans ψ.symm
  let v := (Subtype.val : V → X) ∘ ψ
  let w := (Subtype.val : O → X) ∘ (Subtype.val : W → O)
  have hPoint (p : W) : v (β p) = w p := by
    change ((ψ (ψ.symm ((nestedOpensDiffeo (n := n) hVO) p))) : X) = p.val.val
    rw [ψ.apply_symm_apply,nestedOpensDiffeo_apply]
  have hPoint' (p : A) : w (β.symm p) = v p := by
    rw [← hPoint,β.apply_symm_apply]
  let T₀ := (transport β T).tower
  have hIso := transport_isTowerIso β T
  let F := (Subtype.val : O → X) ⁻¹' C
  have hFC : IsClosed F := hC.preimage continuous_subtype_val
  have hFW : F ⊆ W := by
    intro x hx
    rcases x.property.2 with hCompl | hV
    · exact False.elim (hCompl hx)
    · exact hV
  have hOver₀ : CentresOver ((Subtype.val : W → O) ⁻¹' F) T₀ := by
    have hSupp : β ⁻¹' (v ⁻¹' C) = w ⁻¹' C := by
      ext p
      change v (β p) ∈ C ↔ w p ∈ C
      rw [hPoint]
    exact hSupp ▸ centresOver_of_isTowerIso hIso _ hOver
  let N₀ := (Subtype.val : O → X) ⁻¹' N
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let Eᵥ := E.map (v ⁻¹' ·)
  let E₁ := E₀.map ((Subtype.val : W → O) ⁻¹' ·)
  let M₀ := MarkedIdeal.pullback (Subtype.val : O → X) M
  have hv : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ v :=
    contMDiff_subtype_val.comp ψ.contMDiff
  have hMNV : IsClosedSubmanifold n (MarkedIdeal.pullback v M).N :=
    (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff ψ).mpr
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNM V)
  have hMIV : (MarkedIdeal.pullback v M).ideal.IsCoherent := isCoherent_pullback hv hIM
  have hMPull := (IsTowerIso.isGeoTestTower_iff β hMNV hMIV hIso).mpr hM
  have hMarked : MarkedIdeal.pullback β (MarkedIdeal.pullback v M) =
      MarkedIdeal.pullback (Subtype.val : W → O) M₀ :=
    ContactMarkedCanonical.pullback_pullback_of_comp_eq hIM hv β.contMDiff
      contMDiff_subtype_val contMDiff_subtype_val hPoint
  rw [hMarked] at hMPull
  have hFullPull := (IsTowerIso.isGeoTestTower_iff β isClosedSubmanifold_univ isCoherent_unitIdeal hIso).mpr hFull
  rw [HironakaG34NonPureLowDim.template_pullback (Y := CMfd.of (n := n) W) β] at hFullPull
  have hBoundary : Eᵥ.map (β ⁻¹' ·) = E₁ := by
    simp only [E₁,E₀,Eᵥ,List.map_map]
    apply List.map_congr_left
    intro H _hH
    ext p
    change v (β p) ∈ H ↔ w p ∈ H
    rw [hPoint]
  rw [Set.preimage_univ,hBoundary] at hFullPull
  have hSharp₀ : CurrentSharpCentres ((Subtype.val : W → O) ⁻¹' N₀) E₁ T₀ := by
    apply currentSharp_of_isTowerIso ((Subtype.val : W → O) ⁻¹' N₀) E₁ β.symm hIso.symm hFullPull
    have hBoundary' : E₁.map (β.symm ⁻¹' ·) = Eᵥ := by
      simp only [E₁,E₀,Eᵥ,List.map_map]
      apply List.map_congr_left
      intro H _hH
      ext p
      change w (β.symm p) ∈ H ↔ v p ∈ H
      rw [hPoint']
    have hCarrier : β.symm ⁻¹' ((Subtype.val : W → O) ⁻¹' N₀) = v ⁻¹' N := by
      ext p
      change w (β.symm p) ∈ N ↔ v p ∈ N
      rw [hPoint']
    rw [hBoundary',hCarrier]
    exact hSharp
  have hFull₀ : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → O)
      (geometricTemplate (X := CMfd.of (n := n) O) (univ : Set O) E₀)) T₀ := by
    rw [HironakaG34NonPureLowDim.template_pullback (X := CMfd.of (n := n) O) (Y := CMfd.of (n := n) W)
      (Subtype.val : W → O),Set.preimage_univ]
    exact hFullPull
  obtain ⟨Y,Q,hFullQ,hMQ,hSharpQ,hOverQ,e,he,_hLen,_hProj⟩ :=
    exists_current_sharp_joint_test_extension_of_closed (X := CMfd.of (n := n) O) N₀ E₀ M₀
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNM O)
      (isCoherent_pullback contMDiff_subtype_val hIM) W F hFC hFW T₀ hOver₀ hFull₀ hMPull hSharp₀
  have hCO : C ∩ (O : Set X) ⊆ V := fun x hx => hFW (show (⟨x,hx.2⟩ : O) ∈ F from hx.1)
  refine ⟨O,hKO,inf_le_left,hCO,hVO,Y,Q,hFullQ,hMQ,hSharpQ,hOverQ,e.symm.trans (transport β T).back,?_⟩
  have hComp := he.symm.trans hIso
  have hBase : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) W ∞).symm.trans β = β := by
    ext x
    rfl
  rw [hBase] at hComp
  exact hComp

end
end Hironaka.HironakaG4SharpClosedCrestPatch
