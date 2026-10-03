/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The canonical resolution of marked ideals

Sources: Włodarczyk 2005 (`hiron.tex`), Theorem 1.0.1 / Proposition `pr:resol` (the canonical resolution: blow up
the maximum locus of the invariant until the cosupport is empty; compatibility with open embeddings and
biholomorphisms); Bierstone--Milman 2008 (functoriality).

Let `R` be a resolution invariant in dimension `≤ k` (`ResolutionInvariantSeq.ResolutionInvariant`), e.g. the
canonical one `CanonicalCentres.canonicalInvariant n` in dimension `≤ n`. A **canonical resolution** of a marked
ideal `𝔪` of the domain is a canonical segment of `R.inv 𝔪` without empty centres
(`ResolutionDriver.IsCanonicalSegment`: every centre is the nonempty maximum locus of the invariant on the
cosupport) which is a resolution.

## Main results

* `isCanonicalSegment_of_append`: prefixes of canonical segments without empty centres are such;
* `length_eq_zero_of_cosupp_eq_empty`: after an empty cosupport a canonical segment without empty centres stops;
* `exists_isTowerIso_of_length_eq`: two canonical segments without empty centres of `𝔪` and of `Φ^*𝔪` (`Φ` a biholomorphism)
  with the same number of steps are isomorphic over `Φ` (`IsTowerIso`): the centres correspond by property (6) of the invariant,
  and the blowups along corresponding centres are isomorphic (`BlowupUniqueness.exists_biholomorphism_over`);
* **`exists_isTowerIso_of_isGeoResolution`**: two canonical resolutions of `𝔪` and of `Φ^*𝔪` are isomorphic over `Φ` -- in
  particular two canonical resolutions of `𝔪` are isomorphic over the identity;
* **`canonicalResolution`** (`hir:canonical-resolution`): over a compact base every marked ideal of the domain has a canonical
  resolution `T`, and (1) every centre of `T` is the maximum locus of the invariant on the cosupport, which is upper semicontinuous
  on the cosupport along every canonical segment; (2) for every open `U ⊆ X` the restriction of `T` to `U` is a canonical segment of
  `𝔪|_U` (its centres empty or maximum loci); (3) for every biholomorphism `Φ : X' ≅ X`, every canonical resolution of `Φ^*𝔪` is
  isomorphic to `T` over `Φ` (stage-by-stage biholomorphisms commuting with the blowups);
* `canonicalResolution_canonicalInvariant`: the same for the canonical invariant in dimension `≤ n`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.CanonicalResolution

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.ResolutionInvariantSeq
open Hironaka.MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment isCanonicalSegment_step_iff)
open Hironaka.ResolutionInvariantOrder (IsInvUSCOn)
open Hironaka.ResolutionInvariantSegments (maxLocus_preimage_of_surjective)
open Hironaka.ResolutionInvariantDriver (isCanonical_of_isCanonicalSegment)

noncomputable section

variable {n : ℕ}

/-! ### Canonical segments without empty centres -/

section Segments

variable {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
  (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

/-- **Prefixes of canonical segments without empty centres are such.** -/
theorem isCanonicalSegment_of_append {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), IsCanonicalSegment 𝔪 inv (T₀.append S) → IsCanonicalSegment 𝔪 inv T₀
  | _, .refl, h => h
  | _, .step S C π hπ, h => isCanonicalSegment_of_append T₀ S ((isCanonicalSegment_step_iff 𝔪 inv _ C π hπ).mp h).1

/-- **After an empty cosupport a canonical segment without empty centres stops**: its centres are nonempty maximum loci on the
cosupport, and the maximum locus on the empty set is empty. -/
theorem length_eq_zero_of_cosupp_eq_empty {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : (geoTransformAlong 𝔪 T₀).cosupp = ∅) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), IsCanonicalSegment 𝔪 inv (T₀.append S) → S.length = 0
  | _, .refl, _ => rfl
  | _, .step S C π hπ, h => by
      obtain ⟨hS, hne, hC⟩ := (isCanonicalSegment_step_iff 𝔪 inv _ C π hπ).mp h
      have ih := length_eq_zero_of_cosupp_eq_empty T₀ hT₀ S hS
      cases S with
      | refl =>
        exfalso
        obtain ⟨c, hc⟩ := hne
        have hc' : c ∈ maxLocus (inv T₀) (geoTransformAlong 𝔪 T₀).cosupp := hC ▸ hc
        have := hc'.1
        rw [hT₀] at this
        exact this
      | step S' C' π' hπ' =>
        simp [BlowupTower.length] at ih

end Segments

/-! ### Uniqueness up to isomorphism -/

section Unique

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ) {X X' : CMfd.{u} n}
  {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
  (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)

include h in
/-- **Canonical segments without empty centres of `Φ^*𝔪` and of `𝔪` with the same number of steps are isomorphic over `Φ`**:
by induction, the centres correspond under the stage biholomorphism (property (6): the invariants correspond, so do the
cosupports and the maximum loci), and blowups along corresponding centres are isomorphic over it. -/
theorem exists_isTowerIso_of_length_eq :
    ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y') (T : BlowupTower X Y),
      IsCanonicalSegment (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T' → IsCanonicalSegment 𝔪 (R.inv 𝔪) T →
        T'.length = T.length →
          ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T' T χ
  | _, _, .refl, .refl, _, _, _ => ⟨Φ, .refl⟩
  | _, _, .refl, .step _ _ _ _, _, _, hlen => by simp [BlowupTower.length] at hlen
  | _, _, .step _ _ _ _, .refl, _, _, hlen => by simp [BlowupTower.length] at hlen
  | _, _, .step T' C' π' hπ', .step T C π hπ, hT', hT, hlen => by
      obtain ⟨hT'₀, -, hC'⟩ := (isCanonicalSegment_step_iff _ _ T' C' π' hπ').mp hT'
      obtain ⟨hT₀, -, hC⟩ := (isCanonicalSegment_step_iff _ _ T C π hπ).mp hT
      have hlen₀ : T'.length = T.length := by simpa [BlowupTower.length] using hlen
      obtain ⟨χ, hiso⟩ := exists_isTowerIso_of_length_eq T' T hT'₀ hT₀ hlen₀
      have hcan := isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) T hT₀
      have hTt := R.isInvValue.isGeoTestTower_of_isCanonical h T hcan
      -- the centres correspond
      have hCC : χ ⁻¹' C = C' := by
        rw [hC', hC, IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent
          hiso hTt]
        exact (maxLocus_preimage_of_surjective χ.toEquiv.surjective
          (fun p hp => R.isInvValue.towerIso Φ 𝔪 h T' T χ hiso hcan p hp)).symm
      -- the blowups along corresponding centres are isomorphic
      have hB := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply
        χ.symm_apply_apply hπ
      rw [hCC] at hB
      obtain ⟨e, f, he, hf, hπe, -, hfe, hef⟩ := BlowupUniqueness.exists_biholomorphism_over hπ' hB
      refine ⟨⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩, IsTowerIso.step hiso hπ' hπ _ (fun p => ?_) hCC⟩
      have h1 : χ.symm (π (e p)) = π' p := congrFun hπe p
      show π (e p) = χ (π' p)
      rw [← h1, χ.apply_symm_apply]

include h in
/-- **Two canonical resolutions of `Φ^*𝔪` and of `𝔪` are isomorphic over `Φ`**: canonical segments without empty centres
which are resolutions have the same number of steps (otherwise the longer one would continue after an empty cosupport, by
`exists_isTowerIso_of_length_eq` applied to its prefix), and are then isomorphic. -/
theorem exists_isTowerIso_of_isGeoResolution {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (hT' : IsCanonicalSegment (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T') (hT : IsCanonicalSegment 𝔪 (R.inv 𝔪) T)
    (hres' : IsGeoResolution (pullback Φ 𝔪) T') (hres : IsGeoResolution 𝔪 T) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T' T χ := by
  refine exists_isTowerIso_of_length_eq R h Φ T' T hT' hT ?_
  rcases lt_trichotomy T'.length T.length with hlt | heq | hgt
  · -- `T` is longer: its prefix of the length of `T'` has empty cosupport
    exfalso
    set r := T.length - T'.length
    have hsplit := head_append_tail T r
    have hcanH : IsCanonicalSegment 𝔪 (R.inv 𝔪) (head T r) :=
      isCanonicalSegment_of_append 𝔪 (R.inv 𝔪) (head T r) (tail T r) (by rw [hsplit]; exact hT)
    have hlenH : T'.length = (head T r).length := by rw [length_head]; omega
    obtain ⟨χ, hiso⟩ := exists_isTowerIso_of_length_eq R h Φ T' (head T r) hT' hcanH hlenH
    have hcan := isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) _ hcanH
    have hTt := R.isInvValue.isGeoTestTower_of_isCanonical h _ hcan
    have hcos : (geoTransformAlong 𝔪 (head T r)).cosupp = ∅ := by
      have h' := IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent
        hiso hTt
      rw [hres'.2] at h'
      refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      obtain ⟨p, rfl⟩ := χ.toEquiv.surjective y
      have hp : p ∈ χ ⁻¹' (geoTransformAlong 𝔪 (head T r)).cosupp := hy
      rw [← h'] at hp
      exact hp
    have h0 := length_eq_zero_of_cosupp_eq_empty 𝔪 (R.inv 𝔪) (head T r) hcos (tail T r) (by rw [hsplit]; exact hT)
    rw [length_tail] at h0
    omega
  · exact heq
  · -- `T'` is longer: its prefix of the length of `T` has empty cosupport
    exfalso
    set r := T'.length - T.length
    have hsplit := head_append_tail T' r
    have hcanH : IsCanonicalSegment (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) (head T' r) :=
      isCanonicalSegment_of_append _ _ (head T' r) (tail T' r) (by rw [hsplit]; exact hT')
    have hlenH : (head T' r).length = T.length := by rw [length_head]; omega
    obtain ⟨χ, hiso⟩ := exists_isTowerIso_of_length_eq R h Φ (head T' r) T hcanH hT hlenH
    have hcan := isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) _ hT
    have hTt := R.isInvValue.isGeoTestTower_of_isCanonical h _ hcan
    have hcos : (geoTransformAlong (pullback Φ 𝔪) (head T' r)).cosupp = ∅ := by
      rw [IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hiso hTt,
        hres.2, preimage_empty]
    have h0 := length_eq_zero_of_cosupp_eq_empty _ _ (head T' r) hcos (tail T' r) (by rw [hsplit]; exact hT')
    rw [length_tail] at h0
    omega

end Unique

/-! ### The canonical resolution -/

section Resolution

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)

/-- **The canonical resolution** (`hir:canonical-resolution`): over a compact base every marked ideal `𝔪` of the domain of a
resolution invariant `R` has a resolution `T` which is a canonical segment without empty centres, such that
1. every centre of `T` is the maximum locus of the invariant on the cosupport (`IsCanonicalSegment`), and the invariant is upper
   semicontinuous on the cosupport along every canonical segment;
2. for every open `U ⊆ X` the restriction of `T` to `U` is a canonical segment of `𝔪|_U` (each restricted centre empty or the
   maximum locus of the invariant of `𝔪|_U`);
3. for every biholomorphism `Φ : X' ≅ X`, every resolution of `Φ^*𝔪` which is a canonical segment without empty centres is
   isomorphic to `T` over `Φ`: there are biholomorphisms of the stages, the last one `χ`, commuting with the blowups
   (`IsTowerIso Φ T' T χ`). -/
theorem canonicalResolution {X : CMfd.{u} n} [CompactSpace X] {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsGeoResolution 𝔪 T ∧ IsCanonicalSegment 𝔪 (R.inv 𝔪) T ∧
      (∀ {Y₁ : CMfd.{u} n} (T₁ : BlowupTower X Y₁), IsCanonical 𝔪 (R.inv 𝔪) T₁ →
        IsInvUSCOn (R.inv 𝔪 T₁) (geoTransformAlong 𝔪 T₁).cosupp) ∧
      (∀ U : Opens X, IsCanonical (pullback (Subtype.val : U → X) 𝔪) (R.inv (pullback (Subtype.val : U → X) 𝔪))
        (restrict U T)) ∧
      (∀ {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' : CMfd.{u} n}
        (T' : BlowupTower X' Y'), IsCanonicalSegment (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T' →
          IsGeoResolution (pullback Φ 𝔪) T' →
            ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T' T χ) := by
  obtain ⟨Y, T, hcan, hres⟩ := exists_isGeoResolution_isCanonicalSegment R h
  refine ⟨Y, T, hres, hcan, fun T₁ hT₁ => R.isInvValue.usc 𝔪 h T₁ hT₁, fun U => ?_,
    fun {_} Φ {_} T' hT' hres' => exists_isTowerIso_of_isGeoResolution R h Φ T' T hT' hcan hres' hres⟩
  exact Seq.ResolutionInvariantExt.isCanonical_restrict R h U T (isCanonical_of_isCanonicalSegment _ T hcan)

/-- **The canonical resolution for the canonical invariant** in dimension `≤ n` (`CanonicalCentres.canonicalInvariant`): every
marked ideal of the domain over a compact complex manifold of dimension `n` has a canonical resolution with properties (1)--(3) of
`canonicalResolution`. -/
theorem canonicalResolution_canonicalInvariant {X : CMfd.{u} n} [CompactSpace X] {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain n 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsGeoResolution 𝔪 T ∧
      IsCanonicalSegment 𝔪 ((CanonicalCentres.canonicalInvariant n).inv 𝔪) T ∧
      (∀ {Y₁ : CMfd.{u} n} (T₁ : BlowupTower X Y₁), IsCanonical 𝔪 ((CanonicalCentres.canonicalInvariant n).inv 𝔪) T₁ →
        IsInvUSCOn ((CanonicalCentres.canonicalInvariant n).inv 𝔪 T₁) (geoTransformAlong 𝔪 T₁).cosupp) ∧
      (∀ U : Opens X, IsCanonical (pullback (Subtype.val : U → X) 𝔪)
        ((CanonicalCentres.canonicalInvariant n).inv (pullback (Subtype.val : U → X) 𝔪)) (restrict U T)) ∧
      (∀ {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' : CMfd.{u} n}
        (T' : BlowupTower X' Y'),
          IsCanonicalSegment (pullback Φ 𝔪) ((CanonicalCentres.canonicalInvariant n).inv (pullback Φ 𝔪)) T' →
          IsGeoResolution (pullback Φ 𝔪) T' →
            ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T' T χ) :=
  canonicalResolution (CanonicalCentres.canonicalInvariant n) h

end Resolution

end

end Hironaka.CanonicalResolution
