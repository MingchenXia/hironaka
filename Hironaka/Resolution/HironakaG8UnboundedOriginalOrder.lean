import Hironaka.Resolution.HironakaG8ChronologicalRestartObstruction
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix

/-! An unbounded original order prevents a single global canonical occupied step. -/
set_option autoImplicit false

open Set

namespace Hironaka.HironakaG8UnboundedOriginalOrder

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantExt CanonicalCentres NonmonomialOrderLocal
  SmoothCentreInvariant InvDomainRebase HironakaOriginalEmptyHeadPrefix
  HironakaG8ChronologicalRestartObstruction

variable {n : ℕ} {X : CMfd.{0} (n+1)} (M : MarkedIdeal (n+1) X)

/-- Arbitrarily large original nonmonomial order persists through the same
projection of any finite empty prefix. -/
theorem active_order_unbounded_after_empty_prefix
    (hM : IsInvDomain (n+1) M)
    (hUnbounded : ∀ k, ∃ x ∈ M.cosupp, k < nmOrd M x)
    {Y : CMfd.{0} (n+1)} (P : BlowupTower X Y) (hEmpty : IsEmptyTower P) :
    ∀ k, ∃ y ∈ (geoTransformAlong M P).cosupp, k < nmOrd (geoTransformAlong M P) y := by
  intro k
  obtain ⟨x, hx, hk⟩ := hUnbounded k
  obtain ⟨e, he⟩ := exists_empty_tower_projection P hEmpty
  obtain ⟨y, hy⟩ := e.surjective x
  have hyProj : P.proj y = x := (he y).symm.trans hy
  have hyCos : y ∈ (geoTransformAlong M P).cosupp :=
    (mem_cosupp_geoTransformAlong_of_isEmptyTower M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent P hEmpty y).2 (hyProj ▸ hx)
  have hxOrder : x ∈ ordGe M (k+1) := mem_ordGe_of_succ_le hk
  have hyOrder : y ∈ ordGe (geoTransformAlong M P) (k+1) :=
    (mem_ordGe_geoTransformAlong_of_isEmptyTower (Nat.succ_pos n) hM (k+1) P hEmpty y).2
      (hyProj ▸ hxOrder)
  have hMP := isInvDomain_geoTransformAlong_of_isEmptyTower hM P hEmpty
  exact ⟨y, hyCos, (mem_ordGe_iff hMP.isWellFormed hMP.isNonzeroAlongAt
    ((geoTransformAlong M P).cosupp_subset_N hyCos) (k+1)).1 hyOrder⟩

/-- If the original order is unbounded on a noncompact active locus,
every step of a single ambient canonical tower has empty centre. -/
theorem isEmptyTower_of_original_canonical_of_unbounded_order
    (hM : IsInvDomain (n+1) M)
    (hUnbounded : ∀ k, ∃ x ∈ M.cosupp, k < nmOrd M x)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical M ((canonicalInvariant (n+1)).inv M) T) :
    IsEmptyTower T := by
  induction T with
  | refl => trivial
  | step P C π hπ ih =>
    have hEmpty := ih hCan.1
    refine ⟨hEmpty,?_⟩
    by_contra hC
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hC
    obtain ⟨y, hy, hHigher⟩ := active_order_unbounded_after_empty_prefix M hM hUnbounded P hEmpty
      (nmOrd (geoTransformAlong M P) x)
    exact (not_canonical_restart_step_of_higher_residual_competitor M P hπ hx hy hHigher) hCan

/-- The global canonical obstruction prevents marker exhaustion. -/
theorem not_original_canonical_resolution_of_unbounded_order
    (hM : IsInvDomain (n+1) M)
    (hUnbounded : ∀ k, ∃ x ∈ M.cosupp, k < nmOrd M x)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical M ((canonicalInvariant (n+1)).inv M) T) :
    ¬ IsGeoResolution M T := by
  intro hResolved
  have hEmpty := isEmptyTower_of_original_canonical_of_unbounded_order M hM hUnbounded T hCan
  obtain ⟨y, hy, _⟩ := active_order_unbounded_after_empty_prefix M hM hUnbounded T hEmpty 0
  rw [hResolved.2] at hy
  exact hy

end Hironaka.HironakaG8UnboundedOriginalOrder
