import Hironaka.Resolution.HironakaG34JointMaskEquivariance

/-!
# The current data along an equivariant prefix, and the equivariant mask step (third brick of EQ_d)

Lane G34 (run 0080, round 8).  Blueprint: `hironaka-g34-resume-mask-step-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §2(c)(ii).

The mask fold of the carrier phase (`HironakaActualRetainedBoundaryProfileExit`, private `mask_block_at`) applies, at a
prefix `S` of the construction, the joint mask block to the CURRENT data: the carrier `A.N` and the boundary `A.E` of the
transform `A` of the geometric template `(N, born)` along `S`, and the strict transforms `old.map (strictAlong S)` of the old
members.  This module shows that the current data are preserved by the lift `χ` of a data-preserving biholomorphism
`φ : V ≅ V'` along every prefix `S` with `S|_V ≅ S|_{V'}` over `φ` (the full boundary is the boundary of the transform of the
full template `(X, old ++ born)`: `retained_born_full_boundary_ordered_dictionary`), so that appending a joint mask block of
the current data keeps the tower equivariant: the inductive step of the mask fold with an equivariance conclusion.

## Main results

* `pullback_restrict_geometricTemplate`: a geometric template is natural under biholomorphisms preserving its data;
* `preserves_of_pullback_restrict_eq`: a natural marked ideal has its carrier and each boundary member preserved;
* **`current_data_preserved`**: along `S` (both geometric tests) with `S|_V ≅ S|_{V'}` over `φ` (last-stage map `χ`), `χ`
  preserves the current carrier and every member of `old.map (strictAlong S) ++ A.E`;
* **`exists_isTowerIso_restrict_append_joint_mask_block`**: appending, at such an `S`, a canonical `invFamily` tower of the
  joint profile marked ideal of the current data keeps `(S R)|_V ≅ (S R)|_{V'}` over `φ`.

New file; no existing statement changed; no named input.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG34MaskStepEquivariance

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealBiholomorphism
  Hironaka.NormalCrossings
  Hironaka.HironakaActualRetainedBoundaryJointStep
  Hironaka.HironakaSharpActualFiniteChronologicalHistory
  Hironaka.HironakaG34CanonicalLocalEquivariance
  Hironaka.HironakaG34JointMaskEquivariance
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

section Template

variable {X : CMfd.{u} n} {V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

/-- **A geometric template is natural** under a biholomorphism of opens preserving its carrier and every member. -/
theorem pullback_restrict_geometricTemplate {N : Set X} {E : List (Set X)}
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ N ↔ (p : X) ∈ N)
    (hφH : ∀ H ∈ E, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H) :
    MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X) (geometricTemplate N E)) =
      MarkedIdeal.pullback (Subtype.val : V → X) (geometricTemplate N E) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · ext p
    exact hφN p
  · change (E.map ((Subtype.val : V' → X) ⁻¹' ·)).map (φ ⁻¹' ·) = E.map ((Subtype.val : V → X) ⁻¹' ·)
    rw [List.map_map]
    exact List.map_congr_left fun H hH => Set.ext fun p => hφH H hH p
  · change GermIdeal.pullback (m := n) φ (GermIdeal.pullback (m := n) (Subtype.val : V' → X)
        (IdealWeightPowers.unitIdeal n X)) =
      GermIdeal.pullback (m := n) (Subtype.val : V → X) (IdealWeightPowers.unitIdeal n X)
    rw [BlowupExceptionalDivisor.pullback_unitIdeal, BlowupExceptionalDivisor.pullback_unitIdeal,
      BlowupExceptionalDivisor.pullback_unitIdeal]

/-- **A natural marked ideal has its carrier and every boundary member preserved.** -/
theorem preserves_of_pullback_restrict_eq {𝔪 : MarkedIdeal n X}
    (h : MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) =
      MarkedIdeal.pullback (Subtype.val : V → X) 𝔪) :
    (∀ p : V, ((φ p : V') : X) ∈ 𝔪.N ↔ (p : X) ∈ 𝔪.N) ∧
      ∀ H ∈ 𝔪.E, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H := by
  have hN := congrArg MarkedIdeal.N h
  have hE := congrArg MarkedIdeal.E h
  change φ ⁻¹' ((Subtype.val : V' → X) ⁻¹' 𝔪.N) = (Subtype.val : V → X) ⁻¹' 𝔪.N at hN
  change (𝔪.E.map ((Subtype.val : V' → X) ⁻¹' ·)).map (φ ⁻¹' ·) = 𝔪.E.map ((Subtype.val : V → X) ⁻¹' ·) at hE
  rw [List.map_map, List.map_inj_left] at hE
  refine ⟨fun p => Set.ext_iff.mp hN p, fun H hH p => ?_⟩
  exact Set.ext_iff.mp (hE H hH) p

end Template

section Current

variable {X Y : CMfd.{u} n} {V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

/-- **The current data are preserved along an equivariant prefix**: if `φ` preserves `N` and every member of
`old ++ born`, and `S` (a multiple test blow-up of both geometric templates) has `S|_V ≅ S|_{V'}` over `φ` with last-stage
map `χ`, then `χ` preserves the current carrier `A.N` and every member of `old.map (strictAlong S) ++ A.E`, where `A` is the
transform of the geometric template `(N, born)` along `S`. -/
theorem current_data_preserved {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ N ↔ (p : X) ∈ N)
    (hφH : ∀ H ∈ old ++ born, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    {χ : CMfd.of (n := n) (openPreimage S V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S V')} (hχ : IsTowerIso φ (restrict V S) (restrict V' S) χ) :
    (∀ p : openPreimage S V, ((χ p : openPreimage S V') : Y) ∈ (geoTransformAlong (geometricTemplate N born) S).N ↔
      (p : Y) ∈ (geoTransformAlong (geometricTemplate N born) S).N) ∧
    ∀ H ∈ old.map (strictAlong S) ++ (geoTransformAlong (geometricTemplate N born) S).E,
      ∀ p : openPreimage S V, ((χ p : openPreimage S V') : Y) ∈ H ↔ (p : Y) ∈ H := by
  have hunit : (IdealWeightPowers.unitIdeal n X).IsCoherent := IdealWeightPowers.isCoherent_unitIdeal
  -- the template `(N, born)`
  have hnat := pullback_restrict_geometricTemplate φ (E := born) hφN
    (fun H hH p => hφH H (List.mem_append_right _ hH) p)
  have hA := pullback_restrict_geoTransformAlong φ (𝔪 := geometricTemplate N born) hN hunit hnat S hS hχ
  have hAp := preserves_of_pullback_restrict_eq χ hA
  -- the full template `(X, old ++ born)`
  have hnatF := pullback_restrict_geometricTemplate φ (N := (univ : Set X)) (E := old ++ born)
    (fun _ => ⟨fun _ => trivial, fun _ => trivial⟩) hφH
  have hF := pullback_restrict_geoTransformAlong φ (𝔪 := geometricTemplate (univ : Set X) (old ++ born))
    HomogenizedGlueingTower.isClosedSubmanifold_univ hunit hnatF S hFull hχ
  have hFp := preserves_of_pullback_restrict_eq χ hF
  refine ⟨hAp.1, fun H hH p => ?_⟩
  have hH' : H ∈ (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) S).E := by
    rw [HironakaActualRetainedBornResidualHistory.retained_born_full_boundary_ordered_dictionary N old born S]
    exact hH
  exact hFp.2 H hH' p

/-- **The equivariant mask step**: at a prefix `S` as in `current_data_preserved` (with `N`, `old ++ born` the geometric
hypotheses of the mask block), every tower `R` whose centres are empty or maximum loci of the canonical invariant of the
joint profile marked ideal of the CURRENT data (carrier `A.N`, old members `old.map (strictAlong S)`, born list `A.E`; any
mark `q` and mask `P`; in the domain) keeps the concatenation equivariant: `(S R)|_V ≅ (S R)|_{V'}` over `φ`. -/
theorem exists_isTowerIso_restrict_append_joint_mask_block (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ N ↔ (p : X) ∈ N)
    (hφH : ∀ H ∈ old ++ born, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    {χ : CMfd.of (n := n) (openPreimage S V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S V')} (hχ : IsTowerIso φ (restrict V S) (restrict V' S) χ)
    (q : ℕ) (P : Finset (Fin (old.map (strictAlong S)).length))
    (hdom : IsInvDomain (n + 1) (jointProfileMarked (geoTransformAlong (geometricTemplate N born) S).N
      (old.map (strictAlong S)) (geoTransformAlong (geometricTemplate N born) S).E q P))
    {Z : CMfd.{u} n} (R : BlowupTower Y Z)
    (hR : IsCanonical (jointProfileMarked (geoTransformAlong (geometricTemplate N born) S).N
        (old.map (strictAlong S)) (geoTransformAlong (geometricTemplate N born) S).E q P)
      ((CanonicalCentres.invFamily hn (n + 1)).inv (jointProfileMarked
        (geoTransformAlong (geometricTemplate N born) S).N (old.map (strictAlong S))
        (geoTransformAlong (geometricTemplate N born) S).E q P)) R) :
    ∃ χ' : CMfd.of (n := n) (openPreimage (S.append R) V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (S.append R) V'),
      IsTowerIso φ (restrict V (S.append R)) (restrict V' (S.append R)) χ' := by
  have hRec := HironakaActualRetainedBornResidualHistory.actual_retained_born_recorded_residual_dictionary
    hn hN hE hTr hdense S hS hFull
  obtain ⟨hcN, hcH⟩ := current_data_preserved φ hN hφN hφH S hS hFull hχ
  obtain ⟨χ₁, h₁⟩ := exists_isTowerIso_restrict_joint_mask_block χ hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 q P hdom
    hcN hcH R hR
  exact exists_isTowerIso_restrict_append φ S hχ R h₁

end Current

end

end Hironaka.HironakaG34MaskStepEquivariance
