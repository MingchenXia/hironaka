import Hironaka.Resolution.HironakaG8NativeEmptyStepWindow
import Hironaka.Resolution.HironakaG8NativeSimultaneousPrefix
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical

/-! Deleting one shared identity empty stage retains the simultaneous
maximum at every surviving native stage on the same physical tower. -/

set_option autoImplicit false
set_option maxHeartbeats 3500000

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeEmptyStep

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaStageCenters BlowupTowerIsoTail HironakaOriginalInteriorEmptyHistory
  HironakaOriginalRecursiveBoundaryHistoryMap HironakaG8NativeEmptyStepWindow
  HironakaG8NativeSimultaneousCentre HironakaG8NativeSimultaneousPrefix
  HironakaSmoothSubmersionOriginalAmbientCanonical

variable {n : ℕ} {X A Y Z : CMfd.{0} n} {I : Type}
variable (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))

local notation "ref" B => Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞
local notation "inv" => ResolutionInvariantSeq.ResolutionInvariant.inv (canonicalInvariant n)

private theorem window_open_after_empty_trade (O : Opens X) (H : BlowupTower X A) (S : BlowupTower A Y) :
    openPreimage (H.append S) O = openPreimage (interiorEmptyHistory H S) O := by
  ext y
  change (H.append S).proj y ∈ O ↔ (interiorEmptyHistory H S).proj y ∈ O
  rw [proj_interiorEmptyHistory]

/-- The simultaneous maximum stage survives deletion with the same
literal centre, because every native window uses the same rank shift. -/
private theorem simultaneousCentre_delete_identity_empty (hn : 0 < n) (L : ℕ)
    (hDomain : ∀ i, IsInvDomain n (P i)) (hLen : ∀ i, (P i).E.length = L)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hCan : ∀ i, IsCanonical (P i) (inv (P i)) (restrict (U i) (interiorEmptyHistory H S)))
    {C : Set Y} {m : ValTy n} (hC : C.Nonempty)
    (h : NativeSimultaneousCentre (canonicalInvariant n) U P (interiorEmptyHistory H S) C m) :
    ∃ m', NativeSimultaneousCentre (canonicalInvariant n) U P (H.append S) C m' := by
  let φ (i : I) := opensCongr (n := n) (window_open_after_empty_trade (U i) H S)
  have hRead i := (original_window_identity_empty_deletion hn n (U i) (P i) (hDomain i) H S
    (by simpa only [canonicalInvariant_eq_invFamily hn] using hCan i)).2
  have hPoint (i : I) (y : openPreimage (H.append S) (U i)) :=
    hRead i (φ i y) y rfl
  have hRank (i : I) (y : openPreimage (H.append S) (U i))
      (hy : y ∈ (geoTransformAlong (P i) (restrict (U i) (H.append S))).cosupp) :
      inv (P i) (restrict (U i) (interiorEmptyHistory H S)) (φ i y) =
        recursiveHistoryShift n (L+H.length) (inv (P i) (restrict (U i) (H.append S)) y) := by
    have hv := (hPoint i y).2 ((hPoint i y).1.mpr hy)
    rw [hLen] at hv
    simpa only [canonicalInvariant_eq_invFamily hn] using hv
  obtain ⟨q,hq⟩ := hC
  obtain ⟨j,hj⟩ := h.covered q hq
  let v : openPreimage (H.append S) (U j) :=
    ⟨q,(window_open_after_empty_trade (U j) H S).symm ▸ hj⟩
  have hvOld := (Set.ext_iff.mp (h.trace j) (φ j v)).mp hq
  have hvNew := (hPoint j v).1.mp hvOld.1
  have hMax := (hRank j v hvNew).symm.trans hvOld.2
  let F := recursiveHistoryShift n (L+H.length)
  have hF : StrictMono F := strictMono_recursiveHistoryShift n (L+H.length)
  refine ⟨inv (P j) (restrict (U j) (H.append S)) v,?_,?_,?_⟩
  · intro y hy
    obtain ⟨i,hi⟩ := h.covered y hy
    exact ⟨i,(window_open_after_empty_trade (U i) H S).symm ▸ hi⟩
  · intro i y hy
    apply hF.le_iff_le.mp
    change recursiveHistoryShift n (L+H.length) _ ≤ recursiveHistoryShift n (L+H.length) _
    rw [hMax,← hRank i y hy]
    exact h.upper i (φ i y) ((hPoint i y).1.mpr hy)
  · intro i
    ext y
    have hTrace := Set.ext_iff.mp (h.trace i) (φ i y)
    constructor
    · intro hy
      obtain ⟨hyOld,hEq⟩ := hTrace.mp hy
      have hyNew := (hPoint i y).1.mp hyOld
      exact ⟨hyNew,hF.injective ((hRank i y hyNew).symm.trans (hEq.trans hMax.symm))⟩
    · rintro ⟨hy,hEq⟩
      apply hTrace.mpr
      refine ⟨(hPoint i y).1.mpr hy,?_⟩
      exact (hRank i y hy).trans ((congrArg F hEq).trans hMax)

/-- Every surviving stage retains its actual common-maximum
certificate after the same chronological deletion in all native windows. -/
theorem simultaneous_stages_delete_identity_empty (hn : 0 < n) (L : ℕ)
    (hDomain : ∀ i, IsInvDomain n (P i)) (hLen : ∀ i, (P i).E.length = L)
    (H : BlowupTower X A) :
    ∀ {Y : CMfd.{0} n} (S : BlowupTower A Y),
      (∀ i, IsCanonical (P i) (inv (P i)) (restrict (U i) (interiorEmptyHistory H S))) →
      NativeSimultaneousStages (canonicalInvariant n) U P (interiorEmptyHistory H S) →
      NativeSimultaneousStages (canonicalInvariant n) U P (H.append S)
  | _, .refl, _, h => h.1
  | _, .step S C _ _, hCan, h => by
    have hCanPrev i := (hCan i).1
    refine ⟨simultaneous_stages_delete_identity_empty hn L hDomain hLen H S hCanPrev h.1,?_⟩
    by_cases hEmpty : C = ∅
    · exact Or.inl hEmpty
    · obtain ⟨m,hm⟩ := h.2.resolve_left hEmpty
      exact Or.inr (simultaneousCentre_delete_identity_empty U P hn L hDomain hLen H S
        hCanPrev (Set.nonempty_iff_ne_empty.mpr hEmpty) hm)

/-- Actual tower isomorphism over the same base retains the synchronized
stage history on the literally same initial windows. -/
theorem simultaneous_stages_at_same_base_iso
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hIso : IsTowerIso (ref X) T S χ)
    (hDomain : ∀ i, IsInvDomain n (P i))
    (hCan : ∀ i, IsCanonical (P i) (inv (P i)) (restrict (U i) S))
    (h : NativeSimultaneousStages (canonicalInvariant n) U P S) :
    NativeSimultaneousStages (canonicalInvariant n) U P T := by
  induction hIso with
  | refl => trivial
  | @step Y Z Y' Z' T S χ hIso C π hπ D ρ hρ ψ hComm hD ih =>
    have hCanPrev i := (hCan i).1
    refine ⟨ih hCanPrev h.1,?_⟩
    rw [← hD]
    rcases h.2 with hEmpty | ⟨m,hm⟩
    · exact Or.inl (hEmpty ▸ preimage_empty)
    · exact Or.inr ⟨m,simultaneous_centre_at_same_base_iso (canonicalInvariant n) U P hDomain
        hIso hCanPrev hm⟩

/-- The terminal active state of each actual window is retained when
the shared identity empty stage is removed. -/
theorem canonical_window_delete_identity_empty (hn : 0 < n)
    (hDomain : ∀ i, IsInvDomain n (P i))
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hCan : ∀ i, IsCanonical (P i) (inv (P i)) (restrict (U i) (interiorEmptyHistory H S)))
    (hClear : ∀ i, (geoTransformAlong (P i) (restrict (U i) (interiorEmptyHistory H S))).cosupp = ∅) :
    (∀ i, IsCanonical (P i) (inv (P i)) (restrict (U i) (H.append S))) ∧
    (∀ i, (geoTransformAlong (P i) (restrict (U i) (H.append S))).cosupp = ∅) := by
  have hRead i := original_window_identity_empty_deletion hn n (U i) (P i) (hDomain i) H S
    (by simpa only [canonicalInvariant_eq_invFamily hn] using hCan i)
  refine ⟨fun i => ?_,fun i => ?_⟩
  · simpa only [canonicalInvariant_eq_invFamily hn] using (hRead i).1
  · apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    let x := opensCongr (n := n) (window_open_after_empty_trade (U i) H S) y
    have hx := ((hRead i).2 x y rfl).1.mpr hy
    rw [hClear] at hx
    exact hx

end
end Hironaka.HironakaG8NativeEmptyStep
