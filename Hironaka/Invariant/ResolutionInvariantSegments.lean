import Hironaka.Invariant.ResolutionInvariantDriver

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Canonical segments of a resolution invariant: open sets, isomorphisms of towers, counting centres

Blueprint `hir:canonical-segments` (`blueprint/src/hironaka.tex`, Hironaka phase H4).  Sources: Włodarczyk 2005,
Proposition `pr:resol` (4) and §2.4 (the pullback of the canonical resolution along an étale map -- here an open
embedding or a biholomorphism -- is an *extension* of the canonical resolution of the pullback: the same nonempty
centres, with steps of empty centre inserted), and the remark after Definition `hir:centre-function`.

Let `R` be a resolution invariant in dimension `≤ k` (`ResolutionInvariantSpec.ResolutionInvariant`) and `𝔪` a marked
ideal of its domain.

## Main results

* `maxLocus_preimage`, `maxLocus_preimage_of_surjective`: a maximum locus pulls back along a map preserving the values
  on the set, if the pulled-back locus is nonempty or the map is surjective;
* `cosupp_geoTransformAlong_restrict`: along the restriction to `U` of a multiple test blow-up, the cosupport is the trace
  of the cosupport;
* `isCanonical_restrict`: **the restriction to an open `U` of a canonical segment of `𝔪` is a canonical segment of
  `𝔪|_U`** (property (5): a restricted centre is empty or, the maximum being attained in `U`, the maximum locus of the
  restricted invariant);
* `isCanonical_of_isTowerIso`: **canonical segments correspond along isomorphisms of towers** (property (6));
* `countCentresMeeting_empty`, `countCentresMeeting_mono`, `countCentresMeeting_union_le`,
  `countCentresMeeting_biUnion_le`, `countCentresMeeting_restrict`, `countCentresMeeting_restrict_of_subset`: the number of
  nonempty centres meeting (the preimage of) `K` is monotone and finitely subadditive in `K`, and it is the same for a
  tower and for its restriction to an open `U ⊇ K` -- the bookkeeping of local finiteness (8) over finitely many charts.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ResolutionInvariantSegments

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdealBiholomorphism.MarkedIdeal
  Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism
  Hironaka.ResolutionInvariantSpec Hironaka.ResolutionDriver
  Hironaka.ResolutionInvariantDriver

noncomputable section

variable {n : ℕ}

/-! ### Maximum loci along maps -/

section MaxLocus

variable {Λ : Type*} [LinearOrder Λ]

/-- **A maximum locus pulls back** along a map `ι` with `g = f ∘ ι` on `ι⁻¹ s`, as soon as the pulled-back locus is
nonempty (the maximum of `f` on `s` is then attained in the image of `ι`). -/
theorem maxLocus_preimage {Y Y' : Type*} (ι : Y' → Y) {f : Y → Λ} {g : Y' → Λ} {s : Set Y}
    (hfg : ∀ p, ι p ∈ s → g p = f (ι p)) (hne : (ι ⁻¹' maxLocus f s).Nonempty) :
    maxLocus g (ι ⁻¹' s) = ι ⁻¹' maxLocus f s := by
  obtain ⟨p₀, hp₀s, hp₀⟩ := hne
  ext p
  constructor
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun y hy => ?_⟩
    calc f y ≤ f (ι p₀) := hp₀ y hy
      _ = g p₀ := (hfg p₀ hp₀s).symm
      _ ≤ g p := hp p₀ hp₀s
      _ = f (ι p) := hfg p hps
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun q hq => ?_⟩
    rw [hfg q hq, hfg p hps]
    exact hp (ι q) hq

/-- **A maximum locus pulls back along a surjection** with `g = f ∘ χ` on `χ⁻¹ s`. -/
theorem maxLocus_preimage_of_surjective {Y Y' : Type*} {χ : Y' → Y} (hχ : Function.Surjective χ) {f : Y → Λ}
    {g : Y' → Λ} {s : Set Y} (hfg : ∀ p, χ p ∈ s → g p = f (χ p)) :
    maxLocus g (χ ⁻¹' s) = χ ⁻¹' maxLocus f s := by
  ext p
  constructor
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun y hy => ?_⟩
    obtain ⟨q, rfl⟩ := hχ y
    rw [← hfg q hy, ← hfg p hps]
    exact hp q hy
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun q hq => ?_⟩
    rw [hfg q hq, hfg p hps]
    exact hp (χ q) hq

end MaxLocus

/-! ### Open sets -/

section Restrict

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **The cosupport along a restricted multiple test blow-up is the trace of the cosupport.** -/
theorem cosupp_geoTransformAlong_restrict {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong (pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp =
      (Subtype.val : openPreimage T U → _) ⁻¹' (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_restrict U hN h𝔞 T hT, cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg)]

/-- **The restriction of a canonical segment to an open set is a canonical segment** of the restricted marked ideal
(Włodarczyk's extensions): a restricted centre is empty, or it is nonempty and then the maximum of the invariant on the
cosupport is attained in the open set, so by property (5) the restricted centre is the maximum locus of the restricted
invariant. -/
theorem isCanonical_restrict (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪)
    (U : Opens X) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T →
      IsCanonical (pullback (Subtype.val : U → X) 𝔪) (R.inv (pullback (Subtype.val : U → X) 𝔪)) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
          (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have ih := isCanonical_restrict R hdom U T hT
      have hTt := isGeoTestTower_of_isCanonical R hdom T hT
      show IsCanonical (pullback (Subtype.val : U → X) 𝔪) (R.inv (pullback (Subtype.val : U → X) 𝔪)) (restrict U T) ∧
        (((Subtype.val : openPreimage T U → _) ⁻¹' C) = ∅ ∨
          ((Subtype.val : openPreimage T U → _) ⁻¹' C) = maxLocus (R.inv (pullback (Subtype.val : U → X) 𝔪)
            (restrict U T)) (geoTransformAlong (pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp)
      refine ⟨ih, ?_⟩
      rcases hC with rfl | rfl
      · exact Or.inl (preimage_empty)
      · by_cases hne : ((Subtype.val : openPreimage T U → _) ⁻¹'
            maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
        · right
          rw [cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent
            U T hTt]
          exact (maxLocus_preimage _ (fun p hp => R.restrictOpen 𝔪 hdom U T hTt p hp) hne).symm
        · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

end Restrict

/-! ### Isomorphisms of towers -/

section Iso

variable {X X' : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **Canonical segments correspond along isomorphisms of towers** (property (6)): if `χ : T' → T` is an isomorphism of
towers over a biholomorphism `Φ` and `T` is a canonical segment of `𝔪`, then `T'` is one of `Φ^*𝔪` -- the centres of
`T'` are the preimages of those of `T`, and the invariant of `Φ^*𝔪` along `T'` is that of `𝔪` along `T` composed with the
stage biholomorphisms. -/
theorem isCanonical_of_isTowerIso (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (hdom : IsInvDomain k 𝔪) (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ) :
    IsCanonical 𝔪 (R.inv 𝔪) T → IsCanonical (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T' := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hcan
    obtain ⟨hT, hCc⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
        (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
    have hTt := isGeoTestTower_of_isCanonical R hdom T hT
    show IsCanonical (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T' ∧
      (C' = ∅ ∨ C' = maxLocus (R.inv (pullback Φ 𝔪) T') (geoTransformAlong (pullback Φ 𝔪) T').cosupp)
    refine ⟨ih hT, ?_⟩
    subst hC
    rcases hCc with rfl | rfl
    · exact Or.inl preimage_empty
    · right
      rw [IsTowerIso.cosupp_geoTransformAlong Φ hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent
        hiso hTt]
      exact (maxLocus_preimage_of_surjective χ.toEquiv.surjective
        (fun p hp => R.towerIso Φ 𝔪 hdom T' T χ hiso hTt p hp)).symm

end Iso

/-! ### Counting centres -/

section Count

variable {X : CMfd.{u} n}

/-- No centre meets the preimage of the empty set. -/
theorem countCentresMeeting_empty : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting (∅ : Set X) T = 0
  | _, .refl => rfl
  | _, .step T C π hπ => by
      have h : ¬ (C ∩ T.proj ⁻¹' (∅ : Set X)).Nonempty := by
        rw [preimage_empty, inter_empty]
        exact not_nonempty_empty
      simp only [countCentresMeeting, countCentresMeeting_empty T, if_neg h]

/-- **The count is monotone in `K`.** -/
theorem countCentresMeeting_mono {K K' : Set X} (hK : K ⊆ K') : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting K T ≤ countCentresMeeting K' T
  | _, .refl => le_rfl
  | _, .step T C π hπ => by
      have ih := countCentresMeeting_mono hK T
      have hsub : C ∩ T.proj ⁻¹' K ⊆ C ∩ T.proj ⁻¹' K' := inter_subset_inter_right _ (preimage_mono hK)
      simp only [countCentresMeeting]
      by_cases h1 : (C ∩ T.proj ⁻¹' K).Nonempty
      · rw [if_pos h1, if_pos (h1.mono hsub)]
        omega
      · rw [if_neg h1]
        split_ifs <;> omega

/-- **The count is subadditive in `K`.** -/
theorem countCentresMeeting_union_le (K K' : Set X) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting (K ∪ K') T ≤ countCentresMeeting K T + countCentresMeeting K' T
  | _, .refl => le_rfl
  | _, .step T C π hπ => by
      have ih := countCentresMeeting_union_le K K' T
      simp only [countCentresMeeting]
      by_cases h : (C ∩ T.proj ⁻¹' (K ∪ K')).Nonempty
      · rw [if_pos h]
        rw [preimage_union, inter_union_distrib_left] at h
        rcases union_nonempty.mp h with h1 | h2
        · rw [if_pos h1]
          split_ifs <;> omega
        · rw [if_pos h2]
          split_ifs <;> omega
      · rw [if_neg h]
        split_ifs <;> omega

/-- **The count is finitely subadditive**: for finitely many sets `K i`, the centres meeting the preimage of their union
are at most the sum of the counts. -/
theorem countCentresMeeting_biUnion_le {ι : Type*} (s : Finset ι) (K : ι → Set X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) : countCentresMeeting (⋃ i ∈ s, K i) T ≤ ∑ i ∈ s, countCentresMeeting (K i) T := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, Finset.sum_empty]
    exact (countCentresMeeting_empty T).le
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (countCentresMeeting_union_le _ _ T).trans (Nat.add_le_add_left ih _)

open Classical in
/-- **Counting along a restricted tower**: the nonempty centres of `T|_U` meeting the preimage of `K ∩ U` are the traces
of the centres of `T` meeting the preimage of `K ∩ U`. -/
theorem countCentresMeeting_restrict (U : Opens X) (K : Set X) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) (restrict U T) = countCentresMeeting (K ∩ U) T
  | _, .refl => rfl
  | _, .step T C π hπ => by
      have ih := countCentresMeeting_restrict U K T
      have hiff : (((Subtype.val : openPreimage T U → _) ⁻¹' C) ∩
          (restrict U T).proj ⁻¹' ((Subtype.val : U → X) ⁻¹' K)).Nonempty ↔
          (C ∩ T.proj ⁻¹' (K ∩ (U : Set X))).Nonempty := by
        constructor
        · rintro ⟨p, hpC, hpK⟩
          refine ⟨p.1, hpC, ?_, p.2⟩
          have := proj_restrict U T p
          simp only [mem_preimage] at hpK
          rw [this] at hpK
          exact hpK
        · rintro ⟨y, hyC, hyK, hyU⟩
          refine ⟨⟨y, hyU⟩, hyC, ?_⟩
          simp only [mem_preimage]
          rw [proj_restrict U T ⟨y, hyU⟩]
          exact hyK
      show countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) (restrict U T) +
          (if (((Subtype.val : openPreimage T U → _) ⁻¹' C) ∩
            (restrict U T).proj ⁻¹' ((Subtype.val : U → X) ⁻¹' K)).Nonempty then 1 else 0) =
        countCentresMeeting (K ∩ U) T + (if (C ∩ T.proj ⁻¹' (K ∩ (U : Set X))).Nonempty then 1 else 0)
      rw [ih]
      by_cases h : (C ∩ T.proj ⁻¹' (K ∩ (U : Set X))).Nonempty
      · rw [if_pos h, if_pos (hiff.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/-- For `K ⊆ U` the count along `T|_U` is the count along `T`. -/
theorem countCentresMeeting_restrict_of_subset (U : Opens X) {K : Set X} (hKU : K ⊆ U) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) :
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) (restrict U T) = countCentresMeeting K T := by
  rw [countCentresMeeting_restrict, inter_eq_left.mpr hKU]

end Count

end

end Hironaka.ResolutionInvariantSegments
