import Hironaka.Resolution.HironakaOriginalNCMarkedStratumStepDrop
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumAdmissibleLevels
import Hironaka.Analytic.TowerPreimageCompact

/-!
# A finite native marked-stratum driver with the prescribed H

Only the original native domain, compact WHOLE original cosupport and
adaptation of the prescribed external H are natural inputs. The proof
constructs actual blowups of entire maxima, all raw canonical stages and
their actual native/ALLbranch histories internally. Properness gives
compact current cosupports; native NEW USC forces every unresolved centre
to hit the preimage of the original compact cosupport. The true WF-derived
ANYGrowing bound then forces a finite actual resolving stage.

Mathematics/API first: work/hironaka-g9-new-marked-stratum-driver-fields-20261023/
compact-finite-driver-math-api-20261024/ (math 903ec0e7, API 59efb253).
SOURCE ONLY: no Lean or kernel check is claimed. There is no H-free Seq
installation, noncompact-cosupport G3 scheduler, terminal embedded-NC
interface, Blueprint credit or original G9 closure assertion.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumCompactDriver

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionDriver ResolutionInvariantOrder ResolutionInvariantDriver
  ResolutionInvariantSeq MarkedIdealRestrictOpen
  HironakaNormalCrossingsBoundaryTransform
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCMarkedStratumCanonicalHistory
  HironakaOriginalNCMarkedStratumNativeFields
  HironakaOriginalNCMarkedStratumAdmissibleLevels HironakaOriginalNCMarkedStratumStepDrop
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine native compactness on the actual proper preimage of the WHOLE
original compact cosupport. No ambient or carrier compactness is assumed. -/
private theorem current_cosupport_compact
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hK : IsCompact M.cosupp)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    IsCompact (geoTransformAlong M T).cosupp ∧
      (geoTransformAlong M T).cosupp ⊆ T.proj ⁻¹' M.cosupp := by
  have hPreimage := TowerPreimageCompact.isCompact_preimage_proj hK T
  have hClosed := TowerPreimageCompact.isClosed_cosupp_geoTransformAlong hM T hT
  have hSub := TransformOffCentre.cosupp_geoTransformAlong_subset M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT
  exact ⟨hPreimage.of_isClosed_subset hClosed hSub, hSub⟩

/-- The computed ENTIRE maximum is admissible by the actual all-open field.
All native tests/coherence come internally from the original raw CAN. -/
private theorem whole_maximum_admissible
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hCan : IsCanonical M (markedStratumHistoryValue M H) T) :
    (geoTransformAlong M T).IsAdmissibleCentre
      (maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp) := by
  by_cases hNe : (maxLocus (markedStratumHistoryValue M H T)
      (geoTransformAlong M T).cosupp).Nonempty
  · obtain ⟨x, hx⟩ := hNe
    have hLevel := markedStratum_history_value_levels_admissible M hM h T hCan
      ⊤ (markedStratumHistoryValue M H T x) (fun y hy _ => hx.2 y hy)
    rw [← maxLocus_eq_level hx] at hLevel
    obtain ⟨hT, _hHistory, _hBirth, _hFrames⟩ :=
      markedStratum_canonical_history_joint_interpretation M hM h T hCan
    have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hCurrent.isWellFormed.isCoherent hg) hLevel
  · rw [Set.not_nonempty_iff_eq_empty.mp hNe]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- A true finite resolving tower for the SAME prescribed-H NEW value.
Only the original native domain, compact whole cosupport and H-adaptation
are inputs; selectors, future CAN/tests, maxima and the WF bound are internal. -/
theorem exists_markedStratum_canonical_resolving_tower
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hK : IsCompact M.cosupp)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution M T ∧ IsCanonical M (markedStratumHistoryValue M H) T ∧
        IsOriginalBranchTestTower M H T := by
  let A := {p : Σ Y : CMfd.{u} n, BlowupTower X Y //
    IsCanonical M (markedStratumHistoryValue M H) p.2}
  have hext : ∀ p : A, ∃ q : A,
      ∃ (C : Set p.1.1) (π : q.1.1 → p.1.1) (hπ : IsBlowupAlong n C π),
        q.1.2 = .step p.1.2 C π hπ ∧
          C = maxLocus (markedStratumHistoryValue M H p.1.2)
            (geoTransformAlong M p.1.2).cosupp := by
    intro p
    let C := maxLocus (markedStratumHistoryValue M H p.1.2)
      (geoTransformAlong M p.1.2).cosupp
    have hAdm := whole_maximum_admissible M hM h p.1.2 p.2
    obtain ⟨hTest, _hHistory, _hBirth, _hFrames⟩ :=
      markedStratum_canonical_history_joint_interpretation M hM h p.1.2 p.2
    have hInterior := interior_maxLocus_eq_empty hM p.1.2 hTest
      (markedStratumHistoryValue M H p.1.2)
    obtain ⟨Z, π, hπ⟩ := exists_blowup C hAdm.1 hInterior
    let T' : BlowupTower X Z := .step p.1.2 C π hπ
    have hCan' : IsCanonical M (markedStratumHistoryValue M H) T' := ⟨p.2, Or.inr rfl⟩
    exact ⟨⟨⟨Z, T'⟩, hCan'⟩, C, π, hπ, rfl, rfl⟩
  choose next hnext using hext
  let a0 : A := ⟨⟨X, .refl⟩, trivial⟩
  let s : GrowingSeq X := GrowingSeq.ofIterate (fun p : A => p.1) next a0 rfl (fun p => by
    obtain ⟨C, π, hπ, he, _hC⟩ := hnext p
    exact ⟨C, π, hπ, he⟩)
  have hCan : ∀ i, IsCanonical M (markedStratumHistoryValue M H) (s.stage i).2 :=
    fun i => (next^[i] a0).2
  have hMaps : ∀ i,
      ∃ (C : Set (s.stage i).1) (π : (s.stage (i + 1)).1 → (s.stage i).1)
        (hπ : IsBlowupAlong n C π),
        (s.stage (i + 1)).2 = .step (s.stage i).2 C π hπ ∧
          C = maxLocus (markedStratumHistoryValue M H (s.stage i).2)
            (geoTransformAlong M (s.stage i).2).cosupp := by
    intro i
    change ∃ (C : Set (next^[i] a0).1.1)
      (π : (next^[i + 1] a0).1.1 → (next^[i] a0).1.1) (hπ : IsBlowupAlong n C π),
      (next^[i + 1] a0).1.2 = .step (next^[i] a0).1.2 C π hπ ∧ _
    rw [Function.iterate_succ_apply']
    exact hnext (next^[i] a0)
  have hTerminal : ∃ N, (geoTransformAlong M (s.stage N).2).cosupp = ∅ := by
    by_contra hNo
    have hNe : ∀ i, (geoTransformAlong M (s.stage i).2).cosupp.Nonempty := by
      intro i
      exact Set.nonempty_iff_ne_empty.mpr (fun he => hNo ⟨i, he⟩)
    obtain ⟨bound, hBound⟩ := markedStratum_history_value_growing_sequence_bound M hM h s hCan M.cosupp
    have hCount : ∀ i, countCentresMeeting M.cosupp (s.stage i).2 = i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        obtain ⟨C, π, hπ, he, hC⟩ := hMaps i
        obtain ⟨hTest, _hHistory, _hBirth, _hFrames⟩ :=
          markedStratum_canonical_history_joint_interpretation M hM h (s.stage i).2 (hCan i)
        obtain ⟨hCompact, hSub⟩ := current_cosupport_compact M hM hK (s.stage i).2 hTest
        obtain ⟨x, hx, hMax⟩ :=
          (markedStratum_history_value_isInvUSCOn M hM h (s.stage i).2 (hCan i)).exists_isMaxOn
            hCompact (hNe i)
        have hHit : (C ∩ (s.stage i).2.proj ⁻¹' M.cosupp).Nonempty :=
          ⟨x, hC.symm ▸ ⟨hx, hMax⟩, hSub hx⟩
        rw [he]
        simp only [countCentresMeeting, if_pos hHit, ih]
    have hBad := hBound (bound + 1)
    rw [hCount] at hBad
    omega
  obtain ⟨N, hN⟩ := hTerminal
  obtain ⟨hTest, hHistory, _hBirth, _hFrames⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h (s.stage N).2 (hCan N)
  exact ⟨(s.stage N).1, (s.stage N).2, ⟨hTest, hN⟩, hCan N, hHistory⟩

end
end Hironaka.HironakaOriginalNCMarkedStratumCompactDriver
