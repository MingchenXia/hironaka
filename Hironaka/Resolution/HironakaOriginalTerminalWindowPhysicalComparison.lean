import Hironaka.Resolution.HironakaOriginalTerminalPhysicalComparison
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison

/-! The restriction of two canonical terminal histories of the same
original marked record gives an actual empty-aware comparison. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalTerminalWindowPhysicalComparison

open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres MaxLocusLocal
  HironakaOriginalTerminalOverlapComparison HironakaOriginalTerminalPhysicalComparison
  HironakaG3EmptyAwareHistory ResolutionInvariantSpec

variable {n k : ℕ} {X Y Z : CMfd.{u} n}

/-- Canonical terminal histories of the same actual original record
compare on the literal common open, including all nonempty blowups and
the original input and output projection squares. -/
theorem original_family_terminal_windows_emptyAware (hn : 0 < n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V)
    (S : BlowupTower (CMfd.of (n := n) U) Y)
    (T : BlowupTower (CMfd.of (n := n) V) Z) :
    let M₁ := MarkedIdeal.pullback (Subtype.val : U → X) M
    let M₂ := MarkedIdeal.pullback (Subtype.val : V → X) M
    IsCanonical M₁ ((invFamily hn k).inv M₁) S → IsCanonical M₂ ((invFamily hn k).inv M₂) T →
    IsGeoResolution M₁ S → IsGeoResolution M₂ T →
    ∃ χ : CMfd.of (n := n) (openPreimage S (nestedOpens U W))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T (nestedOpens V W)),
      EmptyAwareTowerIso (overlapBaseEquiv hWU hWV)
        (restrict (nestedOpens U W) S) (restrict (nestedOpens V W) T) χ := by
  intro M₁ M₂ hS hT hResS hResT
  let L := nestedOpens U W
  let R := nestedOpens V W
  let I := invFamily hn k
  let A := MarkedIdeal.pullback (Subtype.val : L → U) M₁
  let B := MarkedIdeal.pullback (Subtype.val : R → V) M₂
  have hM₁ : IsInvDomain k M₁ := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hM₂ : IsInvDomain k M₂ := InvDomainTowerAlong.isInvDomain_pullback_val V hM
  have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_pullback_val R hM₂
  have hCanS := Seq.ResolutionInvariantExt.isCanonical_restrict I hM₁ L S hS
  have hCanT := Seq.ResolutionInvariantExt.isCanonical_restrict I hM₂ R T hT
  have hSL := isGeoResolution_restrict L
    hM₁.isWellFormed.isClosedSubmanifold_N hM₁.isWellFormed.isCoherent hResS
  have hTR := isGeoResolution_restrict R
    hM₂.isWellFormed.isClosedSubmanifold_N hM₂.isWellFormed.isCoherent hResT
  have hDim : DimLE n M.N n := by
    intro x hx
    obtain ⟨d,_hd,hr⟩ := hM.dimLE x hx
    exact ⟨d,hr.1,hr⟩
  have hAmbient : IsInvDomain n M :=
    ⟨hM.isWellFormed,hDim,hM.one_le_d,hM.isNonzeroAlongAt⟩
  have hEq : MarkedIdeal.pullback (overlapBaseEquiv hWU hWV) B = A :=
    original_overlap_whole_marked_dictionary M hAmbient hWU hWV
  exact original_terminal_histories_emptyAware_over_pullback hn B hB
    (overlapBaseEquiv hWU hWV) (restrict L S) (restrict R T)
    (by rw [hEq]; exact hCanS) hCanT (by rw [hEq]; exact hSL) hTR

end Hironaka.HironakaOriginalTerminalWindowPhysicalComparison
