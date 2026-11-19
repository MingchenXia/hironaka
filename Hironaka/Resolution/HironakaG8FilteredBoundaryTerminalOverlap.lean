import Hironaka.Resolution.HironakaG8FullBoundaryTerminalOverlap
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison
import Hironaka.Resolution.HironakaG3EmptyAwareFilteredBoundary
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison

/-! Empty boundary positions left by restricted higher-profile histories
are harmless for physical comparison of genuine terminal native phases. -/

set_option autoImplicit false

open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8FilteredBoundaryTerminalOverlap

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec CanonicalCentres HironakaG11PresLineState
  HironakaG3EmptyAwareHistory HironakaG8FullBoundaryTerminalOverlap
  HironakaOriginalBoundaryEmptyFilterComparison HironakaG8LocalHistory
  BlowupTowerIsomorphism HironakaG3EmptyAwareFilteredBoundary HironakaG3EmptyAwareBornSlots
  HironakaNormalCrossingsSeparationChoiceComparison

/-- The original physical towers compare when their ordered boundary
lists have the same nonempty members. Each tower keeps its full list. -/
theorem native_terminal_emptyAware_of_filtered_boundary {n k : ℕ} (hn : 0 < n)
    {X Y Z : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    {W : Set X} {H : ℕ → ℕ} (hSP : NativeHSState P W H) (hSQ : NativeHSState Q W H)
    (hE : P.E.filter (fun B => decide B.Nonempty) = Q.E.filter (fun B => decide B.Nonempty))
    (hNot : ∀ B ∈ P.E, ∀ x ∈ P.cosupp, x ∈ B → ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ W)
    (TP : BlowupTower X Y) (TQ : BlowupTower X Z)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) TP)
    (hCanQ : IsCanonical Q ((invFamily hn k).inv Q) TQ)
    (hResP : IsGeoResolution P TP) (hResQ : IsGeoResolution Q TQ) :
    ∃ χ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) TQ TP χ := by
  refine native_terminal_emptyAware_of_common_boundary hn (nonemptyBoundary P) (nonemptyBoundary Q)
    (isInvDomain_nonemptyBoundary P hP) (isInvDomain_nonemptyBoundary Q hQ)
    hSP hSQ hE ?_ TP TQ
    ((isCanonical_invFamily_nonemptyBoundary_iff hn k P TP).mpr hCanP)
    ((isCanonical_invFamily_nonemptyBoundary_iff hn k Q TQ).mpr hCanQ)
    ((isGeoResolution_nonemptyBoundary_iff P TP).mpr hResP)
    ((isGeoResolution_nonemptyBoundary_iff Q TQ).mpr hResQ)
  intro B hB x hx hxB
  exact hNot B (List.mem_of_mem_filter hB) x hx hxB

/-- Phase comparison over an already identified ambient overlap, even if
the chronologies carry different empty boundary positions there. -/
theorem native_terminal_emptyAware_along_filtered_boundary {n k : ℕ} (hn : 0 < n)
    {X X' Y Y' : CMfd.{0} n} (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (P : MarkedIdeal n X') (Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    {W : Set X} {H : ℕ → ℕ} (hSP : NativeHSState P (φ ⁻¹' W) H) (hSQ : NativeHSState Q W H)
    (hE : P.E.filter (fun B => decide B.Nonempty) =
      (Q.E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hNot : ∀ B ∈ P.E, ∀ x ∈ P.cosupp, x ∈ B →
      ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ φ ⁻¹' W)
    (TP : BlowupTower X' Y') (TQ : BlowupTower X Y)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) TP)
    (hCanQ : IsCanonical Q ((invFamily hn k).inv Q) TQ)
    (hResP : IsGeoResolution P TP) (hResQ : IsGeoResolution Q TQ) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
      EmptyAwareTowerIso φ TP TQ χ := by
  let tr := transport φ TQ
  have hIso := transport_isTowerIso φ TQ
  have hCan := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
    (invFamily hn k) hQ φ hIso hCanQ
  have hRes := (isGeoResolution_transport_iff φ hQ.isWellFormed.isCoherent TQ).mpr hResQ
  obtain ⟨χ,hχ⟩ := native_terminal_emptyAware_of_filtered_boundary hn P (MarkedIdeal.pullback φ Q)
    hP (InvDomainTowerAlong.isInvDomain_pullback φ hQ) hSP (hSQ.pullback φ) hE hNot
    TP tr.tower hCanP hCan hResP hRes
  refine ⟨χ.symm.trans tr.back, ?_⟩
  have h := HironakaG3EmptyAwareComposition.trans (HironakaG3EmptyAwareSymmetry.symm hχ)
    (emptyAware_of_isTowerIso hIso)
  simpa only [Diffeomorph.symm_refl, Diffeomorph.refl_trans] using h

/-- Physical empty-aware prefix and suffix comparisons compose under
literal tower concatenation. -/
theorem emptyAware_append_same_base_transport {n : ℕ} {X X' Y Y' : CMfd.{0} n}
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hPrefix : EmptyAwareTowerIso φ T' T ψ)
    {Z Z' : CMfd.{0} n} {S' : BlowupTower Y' Z'} {S : BlowupTower Y Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
    (hTail : EmptyAwareTowerIso ψ S' S χ) :
    EmptyAwareTowerIso φ (T'.append S') (T.append S) χ := by
  induction hTail with
  | refl => exact hPrefix
  | step _ hπ₁ hπ₂ χ hcomm hC ih => exact .step ih hπ₁ hπ₂ χ hcomm hC
  | leftEmpty _ hπ e he ih => exact .leftEmpty ih hπ e he
  | rightEmpty _ hπ e he ih => exact .rightEmpty ih hπ e he

/-- A physical prefix comparison lifts through one aligned native phase
on the actual current carriers, using the filtered accumulated boundary
computed from the two original histories. -/
theorem native_terminal_append_of_filtered_prefix {n k : ℕ} (hn : 0 < n)
    {X X' Y Y' Z Z' : CMfd.{0} n}
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hPrefix : EmptyAwareTowerIso φ T' T ψ)
    (M' : MarkedIdeal n X') (M : MarkedIdeal n X)
    (hE : M'.E.filter (fun B => decide B.Nonempty) =
      (M.E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hClosed : ∀ B ∈ M.E, IsClosed B)
    {W : Set X} (hW : IsClosed W) (H : ℕ → ℕ)
    (P : MarkedIdeal n Y') (Q : MarkedIdeal n Y)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hPE : P.E = (geoTransformAlong M' T').E) (hQE : Q.E = (geoTransformAlong M T).E)
    (hSP : NativeHSState P (strictTransform n T'.proj (φ ⁻¹' W)) H)
    (hSQ : NativeHSState Q (strictTransform n T.proj W) H)
    (hNot : ∀ B ∈ P.E, ∀ x ∈ P.cosupp, x ∈ B →
      ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ strictTransform n T'.proj (φ ⁻¹' W))
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) S')
    (hCanQ : IsCanonical Q ((invFamily hn k).inv Q) S)
    (hResP : IsGeoResolution P S') (hResQ : IsGeoResolution Q S) :
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z,
      EmptyAwareTowerIso φ (T'.append S') (T.append S) χ := by
  have hBoundary := full_boundary_transport_of_filtered_initial hPrefix M' M hE hClosed
  rw [← hPE, ← hQE, ← filter_map_bijection ψ ψ.surjective] at hBoundary
  have hCarrier := strictTransform_preimage_of_square φ ψ T'.contMDiff_proj T.contMDiff_proj W hW
    (emptyAware_proj_comm hPrefix)
  rw [hCarrier] at hSP hNot
  obtain ⟨χ,hTail⟩ := native_terminal_emptyAware_along_filtered_boundary hn ψ P Q hP hQ hSP hSQ
    hBoundary hNot S' S hCanP hCanQ hResP hResQ
  exact ⟨χ, emptyAware_append_same_base_transport hPrefix hTail⟩

end
end Hironaka.HironakaG8FilteredBoundaryTerminalOverlap
