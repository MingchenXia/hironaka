import Hironaka.Resolution.HironakaExhaustionBlockLocalFiniteness
import Hironaka.Analytic.TowerPreimageCompact
import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Mathlib.Topology.Compactness.SigmaCompact

/-! # The exhaustion priority rule: served compact tasks stay served, and the schedule is locally finite

Lane G3 (run 0080, round 1).  Blueprint: `hironaka-g3-r-task-schedule.tex`.
Notes: `work/hironaka-resume-20261111/G3/NONCOMPACT-SCHEDULE.md` (why a locally canonical
ℕ-schedule does not exist in general, and why the fair rule serves compact tasks in exhaustion order).

* `resolved_persists`, `centresAvoid_of_resolved`, `isEmptyTower_restrict_of_resolved`: a set over which
  the cosupport is empty stays so along EVERY multiple test blow-up, whose centres avoid it (all its
  restricted steps are empty) -- "earlier served tasks stay served" (the first half of G3O02);
* `countCentresMeeting_append_of_resolved`: after a stage resolved over `K`, no centre meets `K`;
* **`exhaustion_service_schedule`**: for a compact exhaustion `K₀ ⊆ K₁ ⊆ ⋯` and ANY block rule `next j`
  whose block is a multiple test blow-up that serves task `j` (cosupport empty over `K j`), the
  recursively selected schedule is a finite resolution or a locally finite growing sequence of
  multiple test blow-ups which, over a neighbourhood of every compact set, is eventually resolved and
  eventually constant (all later restricted steps empty).  The service hypothesis is the block producer
  (G3M route); it is NOT proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RTaskSchedule

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
  HironakaLocallyFiniteResolutionSequence HironakaExhaustionBlockLocalFiniteness RestrictEmptyTower
  MarkedIdealRestrictOpen
open ResolutionInvariantSpec (countCentresMeeting)

variable {n : ℕ}

/-! ### Served sets stay served -/

section Persist

variable {Y : CMfd.{u} n} (𝔫 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔫.N) (h𝔞 : 𝔫.ideal.IsCoherent)

include hN h𝔞

/-- **A set over which the cosupport is empty stays so along every multiple test blow-up.** -/
theorem resolved_persists (A : Set Y) (hA : Disjoint 𝔫.cosupp A) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z), IsGeoTestTower 𝔫 S →
      Disjoint (geoTransformAlong 𝔫 S).cosupp (S.proj ⁻¹' A)
  | _, .refl, _ => hA
  | _, .step S C π hπ, hS => by
      obtain ⟨hSt, hC⟩ := hS
      have ih := resolved_persists A hA S hSt
      obtain ⟨hNS, hcS⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 S hSt
      refine disjoint_left.mpr fun z hz hzA => ?_
      have hzA' : π z ∈ S.proj ⁻¹' A := hzA
      have hz' : z ∈ ((geoTransformAlong 𝔫 S).geoTransform C π).cosupp := hz
      have hπz : π z ∉ C := fun hc => disjoint_left.mp ih (hC.2.1 hc) hzA'
      have hmem := (TransformOffCentre.mem_cosupp_geoTransform_iff _ hNS.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcS hg) hπ hπz).mp hz'
      exact disjoint_left.mp ih hmem hzA'

/-- **The centres of every multiple test blow-up avoid a served open set.** -/
theorem centresAvoid_of_resolved (U : Opens Y) (hU : Disjoint 𝔫.cosupp (U : Set Y)) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z), IsGeoTestTower 𝔫 S → CentresAvoid U S
  | _, .refl, _ => trivial
  | _, .step S _ _ _, hS =>
      ⟨centresAvoid_of_resolved U hU S hS.1, disjoint_left.mpr fun _c hc hcU =>
        disjoint_left.mp (resolved_persists 𝔫 hN h𝔞 (U : Set Y) hU S hS.1) (hS.2.2.1 hc) hcU⟩

/-- **Over a served open set every multiple test blow-up restricts to an empty tower.** -/
theorem isEmptyTower_restrict_of_resolved (U : Opens Y) (hU : Disjoint 𝔫.cosupp (U : Set Y))
    {Z : CMfd.{u} n} (S : BlowupTower Y Z) (hS : IsGeoTestTower 𝔫 S) :
    ResolutionInvariantExt.IsEmptyTower (restrict U S) :=
  (isEmptyTower_restrict_iff U S).mpr (centresAvoid_of_resolved 𝔫 hN h𝔞 U hU S hS)

end Persist

/-! ### Counts after a served stage -/

section Count

variable {X : CMfd.{u} n}

open Classical in
theorem countCentresMeeting_empty {Y₀ : CMfd.{u} n} :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), countCentresMeeting (∅ : Set Y₀) S = 0
  | _, .refl => rfl
  | _, .step S C _ _ => by
      show countCentresMeeting ∅ S + (if (C ∩ S.proj ⁻¹' (∅ : Set Y₀)).Nonempty then 1 else 0) = 0
      rw [countCentresMeeting_empty S, preimage_empty, inter_empty]
      simp

/-- **After a stage served over `K`, no centre of a multiple test blow-up meets `K`.** -/
theorem countCentresMeeting_append_of_resolved (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (K : Set X) {Y₀ Y : CMfd.{u} n} (T : BlowupTower X Y₀) (S : BlowupTower Y₀ Y)
    (hTS : IsGeoTestTower 𝔪 (T.append S)) (hres : Disjoint (geoTransformAlong 𝔪 T).cosupp (T.proj ⁻¹' K)) :
    countCentresMeeting K (T.append S) = countCentresMeeting K T := by
  rw [TowerPreimageCompact.countCentresMeeting_append_eq_inter_cosupp hN h𝔞 K T S hTS]
  have h0 : T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp = ∅ := by
    rw [inter_comm]; exact disjoint_iff_inter_eq_empty.mp hres
  rw [h0, countCentresMeeting_empty, add_zero]

end Count

/-! ### The exhaustion priority rule -/

section Schedule

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (K : CompactExhaustion X)
  (next : ∀ (_j : ℕ) {Y : CMfd.{u} n}, BlowupTower X Y → Σ Z : CMfd.{u} n, BlowupTower Y Z)
  (hnext : ∀ (j : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
    IsGeoTestTower (geoTransformAlong 𝔪 T) (next j T).2)
  (hserve : ∀ (j : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
    Disjoint (geoTransformAlong 𝔪 (T.append (next j T).2)).cosupp ((T.append (next j T).2).proj ⁻¹' K j))

/-- Later block endpoints extend earlier ones. -/
theorem blockEndpoints_prefix (a : ℕ) : ∀ b, a ≤ b →
    ∃ S : BlowupTower (blockEndpoints next a).1 (blockEndpoints next b).1,
      (blockEndpoints next b).2 = (blockEndpoints next a).2.append S := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact ⟨.refl, rfl⟩
  | succ b _ ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨Q, hQ⟩ := blockEndpoints_extend next b
    refine ⟨S.append Q, ?_⟩
    rw [hQ, hS, BlowupTower.append_assoc]

include hN h𝔞 hnext hserve in
/-- **Served tasks stay served at every later block endpoint.** -/
theorem blockEndpoints_resolved (a b : ℕ) (hab : a + 1 ≤ b) :
    Disjoint (geoTransformAlong 𝔪 (blockEndpoints next b).2).cosupp
      ((blockEndpoints next b).2.proj ⁻¹' K a) := by
  have hBt := isGeoTestTower_blockEndpoints next 𝔪 hnext
  have h1 : Disjoint (geoTransformAlong 𝔪 (blockEndpoints next (a + 1)).2).cosupp
      ((blockEndpoints next (a + 1)).2.proj ⁻¹' K a) :=
    hserve a (blockEndpoints next a).2 (hBt a)
  obtain ⟨S, hS⟩ := blockEndpoints_prefix next (a + 1) b hab
  have hTS := hBt b
  rw [hS] at hTS ⊢
  obtain ⟨hT, hSt⟩ := (isGeoTestTower_append_iff 𝔪 _ _).mp hTS
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 _ hT
  rw [geoTransformAlong_append, BlowupTower.proj_append, preimage_comp]
  exact resolved_persists _ hNT hcT _ h1 S hSt

include hN h𝔞 hnext hserve in
/-- **The exhaustion priority rule** (fair global schedule): serving the compact tasks `K 0, K 1, …` of a
compact exhaustion one block at a time, by ANY block rule whose blocks are multiple test blow-ups serving
their task, gives either a finite resolution, or a locally finite growing sequence of multiple test
blow-ups which over a neighbourhood of every compact set is eventually resolved and eventually constant. -/
theorem exhaustion_service_schedule :
    (∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsGeoResolution 𝔪 T) ∨
      ∃ s : GrowingSeq X, (∀ i, IsGeoTestTower 𝔪 (s.stage i).2) ∧ LocallyFinite (centreImage s) ∧
        ∀ L : Set X, IsCompact L → ∃ (U : Opens X) (N : ℕ), L ⊆ U ∧
          (∀ i, N ≤ i → Disjoint (geoTransformAlong 𝔪 (s.stage i).2).cosupp ((s.stage i).2.proj ⁻¹' U)) ∧
          ∀ r, ResolutionInvariantExt.IsEmptyTower (restrict (openPreimage (s.stage N).2 U) (tailTower s N r)) := by
  classical
  have hBt := isGeoTestTower_blockEndpoints next 𝔪 hnext
  have hres := blockEndpoints_resolved 𝔪 hN h𝔞 K next hnext hserve
  let U : ℕ → Opens X := fun a => ⟨interior (K a), isOpen_interior⟩
  have hcover : ∀ x : X, ∃ a, x ∈ U a := fun x => by
    obtain ⟨a, ha⟩ := K.exists_mem x
    exact ⟨a + 1, K.subset_interior_succ a ha⟩
  have hbound : ∀ a, ∃ m, ∀ j, countCentresMeeting (U a : Set X) (blockEndpoints next j).2 ≤ m := by
    intro a
    refine ⟨countCentresMeeting (U a : Set X) (blockEndpoints next (a + 1)).2, fun j => ?_⟩
    rcases le_total j (a + 1) with hj | hj
    · obtain ⟨S, hS⟩ := blockEndpoints_prefix next j (a + 1) hj
      rw [hS, TowerPreimageCompact.countCentresMeeting_append]
      exact Nat.le_add_right _ _
    · obtain ⟨S, hS⟩ := blockEndpoints_prefix next (a + 1) j hj
      have hTS := hBt j
      rw [hS] at hTS ⊢
      refine (countCentresMeeting_append_of_resolved 𝔪 hN h𝔞 _ _ S hTS ?_).le
      exact (hres a (a + 1) le_rfl).mono_right (preimage_mono interior_subset)
  rcases finite_or_locallyFinite_test_schedule next 𝔪 hnext U hcover hbound with ⟨a, ha⟩ | ⟨s, hsB, hst, hlf, -⟩
  · -- the block endpoints stop: the last one is a resolution
    left
    refine ⟨_, (blockEndpoints next a).2, hBt a, eq_empty_iff_forall_notMem.mpr fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := K.exists_mem ((blockEndpoints next a).2.proj y)
    let P : (Σ Y : CMfd.{u} n, BlowupTower X Y) → Prop := fun p =>
      Disjoint (geoTransformAlong 𝔪 p.2).cosupp (p.2.proj ⁻¹' K c)
    have hb : P (blockEndpoints next (max a (c + 1))) := hres c _ (le_max_right _ _)
    rw [ha _ (le_max_left _ _)] at hb
    exact disjoint_left.mp hb hy hc
  · right
    refine ⟨s, hst, hlf, fun L hL => ?_⟩
    obtain ⟨c, hc⟩ := K.exists_superset_of_isCompact hL
    let N := (blockEndpoints next (c + 2)).2.length
    have hsN : s.stage N = blockEndpoints next (c + 2) := hsB (c + 2)
    let P : (Σ Y : CMfd.{u} n, BlowupTower X Y) → Prop := fun p =>
      Disjoint (geoTransformAlong 𝔪 p.2).cosupp (p.2.proj ⁻¹' K (c + 1))
    have hN0 : P (s.stage N) := by rw [hsN]; exact hres (c + 1) (c + 2) le_rfl
    have hNU : Disjoint (geoTransformAlong 𝔪 (s.stage N).2).cosupp ((s.stage N).2.proj ⁻¹' (U (c + 1) : Set X)) :=
      hN0.mono_right (preimage_mono interior_subset)
    obtain ⟨hNN, hcN⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 _ (hst N)
    have htail : ∀ r, IsGeoTestTower (geoTransformAlong 𝔪 (s.stage N).2) (tailTower s N r) := fun r => by
      have h := hst (N + r)
      rw [← append_tailTower s N r] at h
      exact ((isGeoTestTower_append_iff 𝔪 _ _).mp h).2
    refine ⟨U (c + 1), N, hc.trans (K.subset_interior_succ c), fun i hi => ?_, fun r => ?_⟩
    · obtain ⟨r, rfl⟩ : ∃ r, i = N + r := ⟨i - N, by omega⟩
      rw [← append_tailTower s N r, geoTransformAlong_append, BlowupTower.proj_append, preimage_comp]
      exact resolved_persists _ hNN hcN _ hNU _ (htail r)
    · exact isEmptyTower_restrict_of_resolved _ hNN hcN (openPreimage (s.stage N).2 (U (c + 1))) hNU _ (htail r)

end Schedule

end

end Hironaka.HironakaG3RTaskSchedule
