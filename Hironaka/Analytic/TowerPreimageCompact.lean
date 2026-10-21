/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.TowerRestrictionStep
import Hironaka.Invariant.TowerCosupportCentreCounting
import Hironaka.Blowup.BlowupCompact
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.StepOneWellFounded

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sequences of blowups are proper; the compact part of the cosupport; centres counted after a stage

Hironaka phase H2 (TN3), for the per-sequence local finiteness of the resolution invariant (`hir:centre-function` (8) in the
form chosen by the human on inbox I-1139, option (b)); claim I-0977 C-0211.  Blueprint `bcalc:tower-preimage-compact`
(chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the proof of Proposition `pr:resol`
(finiteness of the resolution over a relatively compact set); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`),
local finiteness over compact sets.

The phase argument for local finiteness (in the Step 1 value and in the general step) fixes a stage `T₀` of a growing sequence
`T₀ S₁ ⊂ T₀ S₂ ⊂ ⋯` of canonical segments and counts the later nonempty centres meeting the preimage of a compact `K` of the base
against a compact subset of the stage `T₀`, inside an open set on which a lower-dimensional invariant lives.  This module
provides the topological half of that step:

* **`isCompact_preimage_of_isBlowupAlong`**: a blowup is proper (the preimage of a compact set is compact; from the local
  compactness of preimages in `BlowupCompact`); **`isCompact_preimage_proj`**: so is the projection of every tower;
* **`isCompact_preimage_inter_cosupp`**: along a multiple test blow-up `T` of a marked ideal of the domain, the part
  `T⁻¹K ∩ cosupp 𝔪_T` of the cosupport over a compact `K` is compact;
* **`proj_mem_cosupp_append`**: along a multiple test blow-up `T S` the points of the cosupport lie over the cosupport at `T`;
* **`countCentresMeeting_append`**: the centres of `T S` meeting the preimage of `K` are those of `T` plus those of `S` meeting
  the preimage of `T⁻¹K`; **`countCentresMeeting_append_eq_inter_cosupp`**: for `T S` a multiple test blow-up, the latter are
  the centres of `S` meeting the preimage of the compact `T⁻¹K ∩ cosupp 𝔪_T`;
* **`countCentresMeeting_append_eq_restrict`**: if `W` is an open set of the stage `T` containing that compact set, the count is
  that along the restricted tail `S|_W` of a compact subset of `W` (with
  `ResolutionInvariantSegments.countCentresMeeting_restrict_of_subset`); **`exists_restrict_step`**: the restriction of a
  one-step extension is a one-step extension of the restriction, so restricted growing sequences are growing.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.TowerPreimageCompact

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupFlatCoordinates
open Hironaka.ResolutionInvariantSpec (IsInvDomain countCentresMeeting)

noncomputable section

/-! ### Blowups and towers are proper -/

section Blowup

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

/-- **Every point has a neighbourhood with compact preimage** under a blowup (on the centre: the preimage of a closed ball of a
flattening chart, `BlowupCompact.isCompact_preimage_flatBall`; off it: `BlowupCompact.isCompact_preimage_of_disjoint`). -/
theorem exists_mem_nhds_isCompact_preimage (hπ : IsBlowupAlong n C π) (y : M) :
    ∃ K ∈ 𝓝 y, IsCompact (π ⁻¹' K) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  by_cases hy : y ∈ C
  · obtain ⟨k, -, -, Φ, hΦsrc, -, hflat⟩ := hπ.1.2 y hy
    set q := Φ.toFun (chartAt (ComplexModel n) y y)
    have hq : q ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
    obtain ⟨R, hR, hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.isOpen_target.mem_nhds hq)
    refine ⟨_, ?_, BlowupCompact.isCompact_preimage_flatBall hπ hΦsrc hflat hRsub⟩
    have hy' := mem_flatDomain_self Φ
    have hcont : ContinuousAt (fun y' => Φ.toFun (chartAt (ComplexModel n) y y')) y :=
      ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy'.2)).continuousAt).comp
        ((chartAt (ComplexModel n) y).continuousAt hy'.1)
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy', hcont.eventually (Metric.closedBall_mem_nhds q hR)]
      with y' h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (hπ.1.1.isOpen_compl.mem_nhds hy)
    exact ⟨K, hK, BlowupCompact.isCompact_preimage_of_disjoint hπ hKc
      (Set.disjoint_left.mpr fun _ h hC => hKsub h hC)⟩

/-- **A blowup is proper**: the preimage of a compact set is compact (finitely many neighbourhoods with compact preimages cover
it, and the preimage is closed). -/
theorem isCompact_preimage_of_isBlowupAlong (hπ : IsBlowupAlong n C π) {K : Set M} (hK : IsCompact K) :
    IsCompact (π ⁻¹' K) := by
  choose L hL hLc using exists_mem_nhds_isCompact_preimage hπ
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover L fun y _ => hL y
  refine IsCompact.of_isClosed_subset (t.isCompact_biUnion fun y _ => hLc y)
    (hK.isClosed.preimage hπ.contMDiff.continuous) ?_
  intro z hz
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (hcover hz)
  exact mem_iUnion₂.mpr ⟨y, hy, hzy⟩

end Blowup

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The projection of a tower is proper.** -/
theorem isCompact_preimage_proj {K : Set X} (hK : IsCompact K) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCompact (T.proj ⁻¹' K)
  | _, .refl => hK
  | _, .step T C π hπ => by
      rw [BlowupTower.proj_step, preimage_comp]
      exact isCompact_preimage_of_isBlowupAlong hπ (isCompact_preimage_proj hK T)

open Classical in
/-- **Counting centres along a concatenation**: those of `T`, then those of `S` meeting the preimage of `T⁻¹K`. -/
theorem countCentresMeeting_append (K : Set X) {Y₀ : CMfd.{u} n} (T : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y),
      countCentresMeeting K (T.append S) = countCentresMeeting K T + countCentresMeeting (T.proj ⁻¹' K) S
  | _, .refl => rfl
  | _, .step S C π hπ => by
      have ih := countCentresMeeting_append K T S
      show countCentresMeeting K (T.append S) + (if (C ∩ (T.append S).proj ⁻¹' K).Nonempty then 1 else 0) =
        countCentresMeeting K T + (countCentresMeeting (T.proj ⁻¹' K) S +
          if (C ∩ S.proj ⁻¹' (T.proj ⁻¹' K)).Nonempty then 1 else 0)
      rw [ih, BlowupTower.proj_append, preimage_comp, Nat.add_assoc]


end Tower

/-! ### The compact part of the cosupport, and the count after a stage -/

section Cosupp

variable {n : ℕ} {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X}

/-- Along a multiple test blow-up of a marked ideal of the domain the cosupport is closed. -/
theorem isClosed_cosupp_geoTransformAlong (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) : IsClosed (geoTransformAlong 𝔪 T).cosupp := by
  have hwf := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
  exact GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _

/-- **The compact part of the cosupport over `K`**: along a multiple test blow-up `T` of a marked ideal of the domain, for
`K` compact, `T⁻¹K ∩ cosupp 𝔪_T` is compact. -/
theorem isCompact_preimage_inter_cosupp (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) {K : Set X} (hK : IsCompact K) :
    IsCompact (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp) :=
  (isCompact_preimage_proj hK T).inter_right (isClosed_cosupp_geoTransformAlong h T hT)



/-- **The count along a multiple test blow-up `T S`, split at the stage `T`**: the centres of `T` meeting `T`'s preimage of
`K`, plus the centres of `S` meeting the preimage of the compact set `T⁻¹K ∩ cosupp 𝔪_T`. -/
theorem countCentresMeeting_append_eq_inter_cosupp (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (K : Set X) {Y₀ Y : CMfd.{u} n} (T : BlowupTower X Y₀) (S : BlowupTower Y₀ Y) (hT : IsGeoTestTower 𝔪 (T.append S)) :
    countCentresMeeting K (T.append S) =
      countCentresMeeting K T + countCentresMeeting (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp) S := by
  rw [countCentresMeeting_append, countCentresMeeting_eq_inter_cosupp hN h𝔞 K T S hT]

/-- **The count after the stage `T`, on an open set of that stage**: if `W` is an open set of the last stage of `T` containing
`T⁻¹K ∩ cosupp 𝔪_T` (`𝔪` in the domain, `T S` a multiple test blow-up, `K` compact), then the centres of `T S` meeting the
preimage of `K` are those of `T` plus those of the restricted tail `S|_W` meeting the preimage of a compact subset of `W`
(namely of `T⁻¹K ∩ cosupp 𝔪_T`, read in `W`). -/
theorem countCentresMeeting_append_eq_restrict (h : IsInvDomain k 𝔪) {K : Set X} (hK : IsCompact K)
    {Y₀ Y : CMfd.{u} n} (T : BlowupTower X Y₀) (S : BlowupTower Y₀ Y) (hT : IsGeoTestTower 𝔪 (T.append S))
    (W : Opens Y₀) (hW : T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp ⊆ W) :
    IsCompact ((Subtype.val : W → Y₀) ⁻¹' (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp)) ∧
      countCentresMeeting K (T.append S) = countCentresMeeting K T +
        countCentresMeeting ((Subtype.val : W → Y₀) ⁻¹' (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp))
          (restrict W S) := by
  have hT₀ : IsGeoTestTower 𝔪 T := ((isGeoTestTower_append_iff 𝔪 T S).mp hT).1
  refine ⟨?_, ?_⟩
  · refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).mpr
      (isCompact_preimage_inter_cosupp h T hT₀ hK)
    intro y hy
    exact ⟨⟨y, hW hy⟩, rfl⟩
  · rw [countCentresMeeting_append_eq_inter_cosupp h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent K T S
      hT, ResolutionInvariantSegments.countCentresMeeting_restrict_of_subset W hW S]

end Cosupp

end

end Hironaka.TowerPreimageCompact
