import Hironaka.Resolution.HironakaG8NativeHSCommonHistory
import Hironaka.Resolution.HironakaOriginalTerminalChoiceComparison
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSIndependentTerminal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HironakaG8LocalHistory HironakaG11InvBMClass DivisorExponentAlong
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG1OriginalUnequalMarkCanonical
  HironakaOriginalTerminalChoiceComparison

/-- Two independently supplied terminal canonical histories for native HS
presentations of the same family have isomorphic final spaces over the original
ambient, allowing arbitrary empty steps. -/
theorem native_hs_independent_terminal_comparison {n k : ℕ} (hn : 0<n)
    {X Y Z : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hEP : P.E = []) (hEQ : Q.E = [])
    {W : Set X} {H : ℕ → ℕ} (hSP : NativeHSState P W H) (hSQ : NativeHSState Q W H)
    (TP : BlowupTower X Y) (TQ : BlowupTower X Z)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) TP)
    (hCanQ : IsCanonical Q ((invFamily hn k).inv Q) TQ)
    (hResP : IsGeoResolution P TP) (hResQ : IsGeoResolution Q TQ) :
    ∃ η : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
      ∀ z, TP.proj (η z) = TQ.proj z := by
  have hL := locWPEquiv_native hSP hSQ (hEQ.trans hEP.symm)
  have hD := SameCarrierDim.of_N_eq (hSP.2.2.1.trans hSQ.2.2.1.symm)
  have hI : ∀ D ∈ P.E, ∀ x ∈ P.cosupp, x ∈ D →
      Q.d * divExpAlong n P.N P.ideal D x = P.d * divExpAlong n Q.N Q.ideal D x := by
    intro D hD; rw [hEP] at hD; exact (List.not_mem_nil hD).elim
  have hCanQP := (invFamily_isCanonical_iff_of_local hn P Q hP hQ hL hD hI TQ).mpr hCanQ
  have hT : IsGeoTestTower P TQ := (hL.wEquiv.2 TQ).1.mpr hResQ.1
  have hResQP : IsGeoResolution P TQ := by
    refine ⟨hT, ?_⟩
    rw [(hL.wEquiv.2 TQ).2 hT, hResQ.2]
  let e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X := Diffeomorph.refl _ _ _
  have he : MarkedIdeal.pullback e P = P := by
    change MarkedIdeal.pullback id P = P
    exact ContactCanonicalAlong.pullback_id P hP.isWellFormed.isCoherent
  have hCan' : IsCanonical (MarkedIdeal.pullback e P) ((invFamily hn k).inv (MarkedIdeal.pullback e P)) TQ := by
    rw [he]; exact hCanQP
  have hRes' : IsGeoResolution (MarkedIdeal.pullback e P) TQ := by rw [he]; exact hResQP
  obtain ⟨η,hη⟩ := original_terminal_histories_biholomorphic_base_comparison hn k P hP e TQ TP hCan' hCanP hRes' hResP
  exact ⟨η,fun z => by simpa [e] using hη z⟩
end
end Hironaka.HironakaG8NativeHSIndependentTerminal
