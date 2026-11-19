import Hironaka.Resolution.HironakaG8NativeSimultaneousComparison
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG8LabelledNativeHead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NativeFirstSlotSymmetry

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaG8NativeRelativeClearing HironakaG8NativeNumericalOverlap
  HironakaG8NativeSimultaneousCentre HironakaG8NativePhaseCertificate HironakaG8LabelledNativeHead
  HironakaG8LabelledNativeHistory HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaActualPowerBoundaryExponents
  HironakaG1OriginalInvariantClassFunctorial HironakaActualVanishingIntrinsicHSTransport
  HironakaG11PresTowerState HironakaHolomorphicJetChartInvariance

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n} {W : Set X} {H : ℕ → ℕ}

private abbrev bm (n : ℕ) :
    BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n (ValTy n) :=
  ⟨canonicalInvariant n,classFunctorialFor_canonicalInvariant n⟩

/-- The first simultaneous native maximum on the full exact-HS cover
is stable under any ambient automorphism preserving the reduced input. -/
theorem first_native_centre_symmetry (hn : 0 < n) {I : Type}
    (A : NativeWindows X I W [] H (phaseLevel W H))
    (φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (hW : φ ⁻¹' W = W)
    {C : Set X} {m : ValTy n}
    (hCentre : NativeSimultaneousCentre (canonicalInvariant n) A.openSet A.powered
      (.refl : BlowupTower X X) C m)
    {a : X} (ha : φ a ∈ C) : a ∈ C := by
  let B := A.transportBase φ
  obtain ⟨i,hi⟩ := hCentre.covered (φ a) ha
  let x : A.openSet i := ⟨φ a,hi⟩
  have hxT := (Set.ext_iff.mp (hCentre.trace i) x).mp ha
  have hxP : x ∈ (A.record i).cosupp :=
    powerMarked_cosupp (A.record i) (A.domain i) (A.positive i) ▸ hxT.1
  have hxH : hilbertSamuelAt (vanishingIdeal (n := n) W) (φ a) = H := by
    have hh := Set.ext_iff.mp (A.native i).cosupp_eq x |>.mp hxP
    exact (funext (hilbertSamuelAt_vanishing_actual_open_any (A.openSet i) W x)).symm.trans (funext hh)
  have haH : a ∈ phaseLevel W H := by
    have h := funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any φ W a)
    rwa [hW,hxH] at h
  obtain ⟨j,hj⟩ := A.covers a haH
  let v : B.openSet i := ⟨a,hi⟩
  let y : A.openSet j := ⟨a,hj⟩
  let g := A.windowEquiv φ i
  have hg : g v = x := rfl
  have hvP : v ∈ (B.record i).cosupp := by
    change v ∈ (MarkedIdeal.pullback g (A.record i)).cosupp
    rw [MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback g.contMDiff g.symm.contMDiff
      g.apply_symm_apply g.symm_apply_apply _ (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent
        (A.domain i).isWellFormed.isCoherent)]
    change g v ∈ (A.record i).cosupp
    exact hg.symm ▸ hxP
  have hValG := (canonicalInvariant n).isInvValue.towerIso g (A.powered i) (A.powered_domain i)
    .refl .refl g IsTowerIso.refl trivial v (hg.symm ▸ hxT.1)
  rw [← A.transportBase_powered φ i] at hValG
  have hState : HironakaG11PresLineState.NativeHSState (B.record i)
      ((Subtype.val : B.openSet i → X) ⁻¹' W) H := by
    exact (congrArg (fun S : Set X => HironakaG11PresLineState.NativeHSState (B.record i)
      ((Subtype.val : B.openSet i → X) ⁻¹' S) H) hW) ▸ B.native i
  obtain ⟨hyP,hTie⟩ := native_window_initial_values_agree hn (bm n)
    (B.openSet i) (A.openSet j) (B.record i) (A.record j) (B.domain i) (A.domain j) W H
    hState (A.native j) [] (B.boundary i) (A.boundary j)
    (B.exponent i) (A.exponent j) (B.positive i) (A.positive j)
    ((B.commonMark i).trans (A.commonMark j).symm)
    (by simp) (show a ∈ B.openSet i from hi) hj hvP
  apply (Set.ext_iff.mp (hCentre.trace j) y).mpr
  refine ⟨(powerMarked_cosupp (A.record j) (A.domain j) (A.positive j)).symm ▸ hyP,?_⟩
  exact hTie.symm.trans (hValG.trans (hg ▸ hxT.2))

private theorem first_slot_of_simultaneous {I : Type} (hn : 0 < n)
    (A : NativeWindows X I W [] H (phaseLevel W H))
    (φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (hW : φ ⁻¹' W = W)
    (a : X) : ∀ {Y : CMfd.{0} n} (S : BlowupTower X Y),
    NativeSimultaneousStages (canonicalInvariant n) A.openSet A.powered S →
    φ a ∈ slotFootprint S 0 → a ∈ slotFootprint S 0
  | _, .refl, _, ha => ha.elim
  | _, .step S C π hπ, hS, ha => by
    cases S with
    | refl =>
      have hHit : φ a ∈ C := by simpa [slotFootprint] using ha
      have hC : a ∈ C := by
        rcases hS.2 with hEmpty | ⟨m,hm⟩
        · rw [hEmpty] at hHit
          exact hHit.elim
        · exact first_native_centre_symmetry hn A φ hW hm hHit
      simpa [slotFootprint] using hC
    | step P D q hq =>
      have hNot : 0 ≠ (P.step D q hq).length := by simp
      rw [slotFootprint,if_neg hNot] at ha ⊢
      exact first_slot_of_simultaneous hn A φ hW a (P.step D q hq) hS.1 ha

/-- No native epoch can stagger the original first raw footprint across
an exact symmetry of the reduced input with empty initial boundary. -/
theorem labelled_native_first_slot_symmetry (hn : 0 < n)
    (φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (hW : φ ⁻¹' W = W)
    {K : Set X} {a : X} {L : List (ℕ → ℕ)} {Y : CMfd.{0} n} {T : BlowupTower X Y}
    (hT : LabelledNativeTower n W [] K T L) (ha : φ a ∈ slotFootprint T 0) :
    a ∈ slotFootprint T 0 := by
  induction L generalizing Y with
  | nil =>
    obtain ⟨hLen,_⟩ := finished_of_empty_labels hT rfl
    have h := hit_slot_lt_length T ha
    omega
  | cons H L ih =>
    obtain ⟨B,Z,S,Q,χ,hPhase,_,_,hLater,hIso⟩ := exists_head_phase hT H L rfl
    rw [slotFootprint_of_isTowerIso hIso,Diffeomorph.coe_refl,preimage_id] at ha ⊢
    cases S with
    | refl =>
      rw [BlowupTower.refl_append] at ha ⊢
      have hLater' : LabelledNativeTower n W [] K Q L := by
        simpa only [BlowupTower.proj_refl,strictTransform_id hT.source_analytic.isClosed,
          geoTransformAlong_refl,preimage_id] using hLater
      exact ih hLater' ha
    | step P C π hπ =>
      have hLen : 0 < (P.step C π hπ).length := by simp
      rw [slotFootprint_append,if_pos hLen] at ha ⊢
      obtain ⟨I,A,_,hSync⟩ := hPhase.nativeStages
      exact first_slot_of_simultaneous hn A φ hW a _ (hSync trivial) ha

end
end Hironaka.HironakaG8NativeFirstSlotSymmetry
