import Hironaka.Resolution.HironakaNormalCrossingsLabelledHistoryExtension

/-!
# Actual strict centre support survives the same whole-open extension

Real tower centre equalities, whole original cosupport coverage and literal
strict transform restriction prove ambient support; permissions are not used
as a proxy for centre containment.
Blueprint: `hironaka-normal-crossings-actual-centre-support-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsActualCentreSupport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism HomogenizedGlueingTower
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  CoefficientIdealRestriction RestrictEmptyTower
variable {n : ℕ} {X X' Y Y' Z : CMfd.{u} n}

theorem centresIn_pullback_of_towerIso (H : Set X)
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {S : BlowupTower X' Y'} {T : BlowupTower X Y}
    {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (he : IsTowerIso Φ S T e) (hCentres : CentresIn H T) : CentresIn (Φ ⁻¹' H) S := by
  revert hCentres
  induction he with
  | refl => intro _;trivial
  | @step Y' Y Z' Z S T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hCentres
    refine ⟨ih hCentres.1,?_⟩
    intro x hx
    have hxC : χ x∈C := by
      change x∈χ ⁻¹' C
      rw [hC]
      exact hx
    rw [h.strictAlong_eq H]
    exact hCentres.2 hxC

theorem centresIn_of_restrict_whole_cosupport (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (H : Set X) (U : Opens X) (hU : M.cosupp⊆U) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T →
      CentresIn ((Subtype.val : U→X) ⁻¹' H) (restrict U T) → CentresIn H T
  | _,.refl,_,_ => trivial
  | _,.step T C π hπ,hT,hLocal => by
    refine ⟨centresIn_of_restrict_whole_cosupport M hN hI H U hU T hT.1 hLocal.1,?_⟩
    intro y hy
    have hBase:=(HironakaAdmissibleSequence.centresOver_cosupp M hN hI (.step T C π hπ) hT).2 hy
    let p : openPreimage T U:=⟨y,hU hBase⟩
    have hp:=hLocal.2 (show p∈(Subtype.val : openPreimage T U→_) ⁻¹' C from hy)
    rw [strictAlong_restrict] at hp
    exact hp

theorem centresIn_actual_extension (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (H : Set X) (U : Opens X) (hU : M.cosupp⊆U)
    (S : BlowupTower (CMfd.of (n:=n) U) Z) (Q : BlowupTower X Y)
    (hQ : IsGeoTestTower M Q)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) S (restrict U Q) e)
    (hS : CentresIn ((Subtype.val : U→X) ⁻¹' H) S) : CentresIn H Q := by
  have hLocal:=centresIn_pullback_of_towerIso ((Subtype.val : U→X) ⁻¹' H) he.symm hS
  change CentresIn ((id : U→U) ⁻¹' ((Subtype.val : U→X) ⁻¹' H)) (restrict U Q) at hLocal
  rw [preimage_id_eq] at hLocal
  exact centresIn_of_restrict_whole_cosupport M hN hI H U hU Q hQ hLocal

theorem centresIn_mono {H K : Set X} (hHK : H⊆K) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresIn H T → CentresIn K T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,h => ⟨centresIn_mono hHK T h.1,fun _ hx=>strictAlong_mono T hHK (h.2 hx)⟩

theorem centresIn_append (H : Set X) (P : BlowupTower X Y) :
    ∀ {Z : CMfd.{u} n} (Q : BlowupTower Y Z),CentresIn H P →
      CentresIn (strictAlong P H) Q → CentresIn H (P.append Q)
  | _,.refl,hP,_ => hP
  | _,.step Q C π hπ,hP,hQ => by
    refine ⟨centresIn_append H P Q hP hQ.1,?_⟩
    rw [MemberInterLocusAlong.strictAlong_append]
    exact hQ.2

end
end Hironaka.HironakaNormalCrossingsActualCentreSupport
