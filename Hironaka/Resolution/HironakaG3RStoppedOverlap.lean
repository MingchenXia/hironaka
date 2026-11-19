import Hironaka.Resolution.HironakaG3RTowerClass
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyBaseComparison
import Hironaka.Resolution.HironakaOriginalIndependentStoppedSource
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-! # G3: stopped canonical prefixes agree on overlaps (A-miss-3, step (i))

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-stopped-overlap.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (A-miss-3, section 4, step 2).

For the embedded resolution of a closed analytic set `V` of pure dimension on a (noncompact) complex manifold `X`, the local
pieces are the **stopped prefixes**: a canonical segment of `(U, U, ∅, 𝓘_{V ∩ U}, 1)` whose centres miss the preimage of an
open set `O` (in practice `X ∖ V_sing`) and which is stopped there: either its maximum locus meets the preimage of `O` (the
next canonical centre would meet it), or it resolves.

* **`IsStopped M O S`**, `centresAvoid_restrict`.
* **`exists_comparison_of_isStopped`**: two stopped prefixes over biholomorphic bases (the marked ideals corresponding)
  are biholomorphic over the base, provided the cosupport of the marked ideal meets `O` or is empty.  Ingredients: the held
  `HironakaOriginalBoundaryEmptyBaseComparison.first_meeting_choice_over_base_across_empty_boundaries` (first-meeting
  case) and `HironakaOriginalTerminalOverlapComparison.original_ambient_terminal_base_existsUnique` (resolved case).
* **`isStopped_restrict`**: the restriction of a stopped prefix of `(Z, Z, ∅, 𝓘_V, 1)` to an open `B` is stopped.  If
  `V ∩ O ∩ B ≠ ∅`, the held homogeneity `HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim` puts every
  point over `V ∩ O` in the maximum locus, so the restricted maximum locus still meets the preimage of `O`; otherwise
  `V ∩ B = ∅` (density of `V ∩ O` in `V`) and the restriction resolves.
* **`stoppedClass M O`** (a class of local towers in the sense of `HironakaG3RTowerClass`), **`covers_stoppedClass`**
  (canonical local resolutions cut at their first centre meeting `O`), **`hasComparisons_stoppedClass`** (the overlap lemma).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RStoppedOverlap

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal RestrictEmptyTower
  HironakaOriginalTerminalOverlapComparison HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RTowerClass
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

variable {n : ℕ}

/-- **A stopped prefix** of `M` relative to an open set `O`: a canonical segment whose centres miss the preimages of `O`,
whose maximum locus meets the preimage of `O` (the first centre meeting `O` would come next) or which resolves `M`. -/
def IsStopped {Z Y : CMfd.{u} n} (M : MarkedIdeal n Z) (O : Opens Z) (S : BlowupTower Z Y) : Prop :=
  IsCanonical M ((canonicalInvariant n).inv M) S ∧ CentresAvoid O S ∧
    ((∃ c ∈ maxLocus ((canonicalInvariant n).inv M S) (geoTransformAlong M S).cosupp, S.proj c ∈ O) ∨
      IsGeoResolution M S)

theorem IsStopped.congr_open {Z Y : CMfd.{u} n} {M : MarkedIdeal n Z} {O O' : Opens Z} {S : BlowupTower Z Y}
    (h : (O : Set Z) = O') (hS : IsStopped M O S) : IsStopped M O' S := by
  have : O = O' := Opens.ext h
  subst this
  exact hS

/-- **Restriction of avoidance**: if the centres of `T` miss `O`, the centres of `T|_B` miss every open of `B` lying in `O`. -/
theorem centresAvoid_restrict {Z : CMfd.{u} n} (B : Opens Z) {O : Opens Z} {O' : Opens B}
    (hO : ∀ q : B, q ∈ O' → (q : Z) ∈ O) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower Z Y), CentresAvoid O T → CentresAvoid O' (restrict B T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
    show CentresAvoid O' (restrict B T) ∧
      Disjoint ((Subtype.val : openPreimage T B → _) ⁻¹' C) ((restrict B T).proj ⁻¹' (O' : Set B))
    refine ⟨centresAvoid_restrict B hO T h.1, Set.disjoint_left.mpr fun p hpC hpO => ?_⟩
    refine Set.disjoint_left.mp h.2 hpC ?_
    change T.proj p.1 ∈ O
    rw [← proj_restrict]
    exact hO _ hpO

/-! ### Comparison over a biholomorphic base -/

/-- **Stopped prefixes over biholomorphic bases are biholomorphic over the base.**  Let `M` be in the domain on `Z`,
`Φ : Z' ≃ Z` a biholomorphism, `O ⊆ Z` open, and suppose the cosupport of `M` meets `O` or is empty.  A stopped prefix
`S` of `Φ^*M` relative to `Φ⁻¹ O` and a stopped prefix `T` of `M` relative to `O` have biholomorphic last stages over `Φ`. -/
theorem exists_comparison_of_isStopped {Z Z' Y Y' : CMfd.{u} n} (M : MarkedIdeal n Z) (hM : IsInvDomain n M)
    (Φ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z) (O : Opens Z)
    (hcases : (M.cosupp ∩ O).Nonempty ∨ M.cosupp = ∅) (S : BlowupTower Z' Y') (T : BlowupTower Z Y)
    (hS : IsStopped (pullback Φ M) (baseOpen Φ O) S) (hT : IsStopped M O T) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, ∀ y, T.proj (η y) = Φ (S.proj y) := by
  have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  have hmem : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hcos' : (pullback Φ M).cosupp = Φ ⁻¹' M.cosupp :=
    MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
      Φ.symm_apply_apply M hmem
  rcases hcases with ⟨x, hxM, hxO⟩ | hempty
  · -- the cosupport meets `O`: both prefixes meet the maximum locus over `O`
    have htT := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hT.1
    have htS := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM' S hS.1
    have hmT : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp, T.proj c ∈ O := by
      rcases hT.2.2 with h | h
      · exact h
      · exfalso
        obtain ⟨y, hy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence x
        have hyO : T.proj y ∈ O := by rw [hy]; exact hxO
        have hyc := (HironakaOriginalIndependentStoppedSource.mem_cosupp_iff_of_centresAvoid M hM.isWellFormed T htT O
          hT.2.1 y hyO).mpr (by rw [hy]; exact hxM)
        rw [h.2] at hyc
        exact hyc
    have hmS : ∃ c ∈ maxLocus ((canonicalInvariant n).inv (pullback Φ M) S) (geoTransformAlong (pullback Φ M) S).cosupp,
        S.proj c ∈ baseOpen Φ O := by
      rcases hS.2.2 with h | h
      · exact h
      · exfalso
        obtain ⟨y, hy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence (Φ.symm x)
        have hyO : S.proj y ∈ baseOpen Φ O := by
          change Φ (S.proj y) ∈ O
          rw [hy, Φ.apply_symm_apply]
          exact hxO
        have hyc := (HironakaOriginalIndependentStoppedSource.mem_cosupp_iff_of_centresAvoid (pullback Φ M)
          hM'.isWellFormed S htS (baseOpen Φ O) hS.2.1 y hyO).mpr (by
            rw [hcos', hy]
            change Φ (Φ.symm x) ∈ M.cosupp
            rw [Φ.apply_symm_apply]
            exact hxM)
        rw [h.2] at hyc
        exact hyc
    obtain ⟨η, hη, -⟩ := first_meeting_choice_over_base_across_empty_boundaries M (pullback Φ M) hM Φ rfl rfl rfl rfl
      S T hS.1 hT.1 O hS.2.1 hT.2.1 hmS hmT
    exact ⟨η, hη.1⟩
  · -- empty cosupport: both resolve
    have hr := (HironakaOriginalIndependentStoppedSource.canonical_histories_empty_of_original_cosupp_empty M hM hempty
      T hT.1).2
    have hr' := (HironakaOriginalIndependentStoppedSource.canonical_histories_empty_of_original_cosupp_empty
      (pullback Φ M) hM' (by rw [hcos', hempty, preimage_empty]) S hS.1).2
    obtain ⟨η, hη, -⟩ := original_ambient_terminal_base_existsUnique M hM Φ S T hS.1 hT.1 hr' hr
    exact ⟨η, hη⟩

/-! ### Restriction of stopped prefixes -/

/-- **The restriction of a stopped prefix is stopped.**  Let `V ⊆ Z` be closed, `O ⊆ Z` open, `V` regular of dimension `d`
at the points of `V ∩ O`, and `V ∩ O` dense in `V`.  For a stopped prefix `S` of `(Z, Z, ∅, 𝓘_V, 1)` relative to `O` and an
open `B ⊆ Z`, the restriction `S|_B` is a stopped prefix of the restriction relative to `O ∩ B`. -/
theorem isStopped_restrict {Z Y : CMfd.{u} n} {V : Set Z} (hV : IsClosed V) (O : Opens Z) {d : ℕ}
    (hpure : ∀ x : O, (x : Z) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z)) (B : Opens Z)
    (S : BlowupTower Z Y) (hS : IsStopped (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z) O S) :
    IsStopped (pullback (Subtype.val : B → Z) (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z))
      (nestedOpens B O) (restrict B S) := by
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have hdomB := InvDomainTowerAlong.isInvDomain_pullback_val B hdom
  have hcanB := Seq.ResolutionInvariantExt.isCanonical_restrict (canonicalInvariant n) hdom B S hS.1
  refine ⟨hcanB, centresAvoid_restrict B (fun q hq => hq) S hS.2.1, ?_⟩
  have htS := hF.isGeoTestTower_of_isCanonical hdom S hS.1
  have hres := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent B S htS
  by_cases hx : ∃ x ∈ V, x ∈ O ∧ x ∈ B
  · obtain ⟨x, hxV, hxO, hxB⟩ := hx
    left
    obtain ⟨y, hy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence x
    have hyO : S.proj y ∈ O := by rw [hy]; exact hxO
    have hyV : S.proj y ∈ V := by rw [hy]; exact hxV
    have hycos := (HironakaEmbeddedBoundary.mem_cosupp_iff_of_centresAvoid hV hdom O S htS hS.2.1 hyO).mpr hyV
    obtain ⟨c, hc, hcO⟩ : ∃ c ∈ maxLocus ((canonicalInvariant n).inv
        (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z) S)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z) S).cosupp,
        S.proj c ∈ O := by
      rcases hS.2.2 with h | h
      · exact h
      · rw [h.2] at hycos
        exact absurd hycos (notMem_empty y)
    have hym := (HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hV O
      (fun H hH => absurd hH List.not_mem_nil) hpure hdom S hS.1 hS.2.1 hc hcO hyO).mpr hyV
    have hyB : y ∈ openPreimage S B := by
      change S.proj y ∈ B
      rw [hy]
      exact hxB
    let p : openPreimage S B := ⟨y, hyB⟩
    refine ⟨p, ⟨?_, ?_⟩, ?_⟩
    · rw [hres]
      exact hym.1
    · intro p' hp'
      rw [hres] at hp'
      rw [(canonicalInvariant n).isInvValue.restrictOpen _ hdom B S hS.1 p' hp',
        (canonicalInvariant n).isInvValue.restrictOpen _ hdom B S hS.1 p hym.1]
      exact hym.2 _ hp'
    · show (((restrict B S).proj p : B) : Z) ∈ O
      rw [proj_restrict]
      exact hyO
  · right
    have hVB : ∀ x ∈ V, x ∉ B := fun x hxV hxB => by
      obtain ⟨x', hx'B, hx'V, hx'O⟩ := mem_closure_iff.mp (hdense hxV) B B.isOpen hxB
      exact hx ⟨x', hx'V, hx'O, hx'B⟩
    have hmem : ∀ x g, (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z).ideal.mem x g →
        HolomorphicAt n g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
    have hcos : (pullback (Subtype.val : B → Z) (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z)).cosupp
        = ∅ := by
      rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem B, HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hV]
      exact eq_empty_of_forall_notMem fun q hq => hVB q hq q.2
    exact (HironakaOriginalIndependentStoppedSource.canonical_histories_empty_of_original_cosupp_empty _ hdomB hcos _
      hcanB).2

/-! ### The class of stopped prefixes -/

/-- **The class of stopped prefixes** of `M` relative to `O`: over an open `U`, the stopped prefixes of `M|_U` relative to
`O ∩ U`. -/
def stoppedClass {X : CMfd.{u} n} (M : MarkedIdeal n X) (O : Opens X) : LocalTowerClass X :=
  fun U _ S => IsStopped (pullback (Subtype.val : U → X) M) (nestedOpens U O) S

/-- **Stopped prefixes exist locally**: cut a canonical local resolution before its first centre meeting `O`. -/
theorem covers_stoppedClass {X : CMfd.{u} n} {M : MarkedIdeal n X} (hM : IsInvDomain n M) (O : Opens X) :
    Covers (stoppedClass M O) := by
  intro x
  obtain ⟨U, hxU, Y, T, hc, hr⟩ := HironakaEmbeddedResolutionLocal.exists_local_resolution_isCanonical
    (canonicalInvariant n) hM (K := ({x} : Set X)) isCompact_singleton
  refine ⟨U, hxU (mem_singleton x), ?_⟩
  by_cases ha : CentresAvoid (nestedOpens U O) T
  · exact ⟨Y, T, hc, ha, Or.inr hr⟩
  · obtain ⟨Y', T', -, -, h1, h2, c, hc', hcU⟩ := EmbeddedFromResolution.exists_first_centre _ _ (nestedOpens U O) T hc ha
    exact ⟨Y', T', h1, h2, Or.inl ⟨c, hc', hcU⟩⟩

/-- Restricting a member of the stopped class of `(X, X, ∅, 𝓘_V, 1)` over `U` to an open `W ⊆ U`. -/
theorem isStopped_restrict_nested {X : CMfd.{u} n} {V : Set X} (hV : IsClosed V) (O : Opens X) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (U W : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : stoppedClass (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U Y T) :
    IsStopped (pullback (Subtype.val : nestedOpens U W → U)
        (pullback (Subtype.val : U → X) (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)))
      (nestedOpens (nestedOpens U W) (nestedOpens U O)) (restrict (nestedOpens U W) T) := by
  have e := SmoothCentreInvariant.pullback_val_smoothCentreMarked U V
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  change IsStopped (pullback (Subtype.val : U → X) (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (nestedOpens U O) T at hT
  rw [e] at hT hdomU ⊢
  have hdenseU : (Subtype.val : U → X) ⁻¹' V ⊆ closure ((Subtype.val : U → X) ⁻¹' V ∩ nestedOpens U O) := by
    intro q hq
    have h2 := (U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val (V ∩ O)
    exact (Set.ext_iff.mp h2 q).mp (hdense hq)
  exact isStopped_restrict (hV.preimage continuous_subtype_val) (nestedOpens U O)
    (fun x hx => (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U)).mpr (hpure ⟨((x : U) : X), x.2⟩ hx)) hdenseU hdomU
    (nestedOpens U W) T hT

/-- **A-miss-3 (i): stopped prefixes agree on overlaps.**  For a closed `V ⊆ X`, an open `O ⊆ X` on which `V` is regular of
dimension `d`, with `V ∩ O` dense in `V` and `(X, X, ∅, 𝓘_V, 1)` in the domain, any two stopped prefixes over `U₁` and `U₂`
are compared over `U₁ ∩ U₂` by a biholomorphism commuting with the projections. -/
theorem hasComparisons_stoppedClass {X : CMfd.{u} n} {V : Set X} (hV : IsClosed V) (O : Opens X) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) :
    HasComparisons (stoppedClass (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  have hR₁ := isStopped_restrict_nested hV O hpure hdense hdom U₁ (U₁ ⊓ U₂) T₁ h₁
  have hR₂ := isStopped_restrict_nested hV O hpure hdense hdom U₂ (U₁ ⊓ U₂) T₂ h₂
  have he := original_overlap_whole_marked_dictionary _ hdom (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  rw [← he] at hR₁
  have hdomU₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens U₂ (U₁ ⊓ U₂)) hdomU₂
  have hmem : ∀ x g, (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X).ideal.mem x g →
      HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hmemU : ∀ x g, (pullback (Subtype.val : U₂ → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomU₂.isWellFormed.isCoherent hg
  have hcosW : (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp =
      {q : nestedOpens U₂ (U₁ ⊓ U₂) | ((q : U₂) : X) ∈ V} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmemU, MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem,
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hV]
    rfl
  have hcases : ((pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp ∩
        (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ O) : Set _)).Nonempty ∨
      (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
        (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp = ∅ := by
    rw [hcosW]
    by_cases hx : ∃ x ∈ V, x ∈ O ∧ x ∈ U₁ ∧ x ∈ U₂
    · obtain ⟨x, hxV, hxO, hx₁, hx₂⟩ := hx
      exact Or.inl ⟨⟨⟨x, hx₂⟩, hx₁, hx₂⟩, hxV, hxO⟩
    · refine Or.inr (eq_empty_of_forall_notMem fun q hq => ?_)
      have hq₁ : ((q : U₂) : X) ∈ (U₁ ⊓ U₂ : Opens X) := q.2
      obtain ⟨x', hx'W, hx'V, hx'O⟩ := mem_closure_iff.mp (hdense hq) _ (U₁ ⊓ U₂).isOpen hq₁
      exact hx ⟨x', hx'V, hx'O, hx'W.1, hx'W.2⟩
  obtain ⟨η, hη⟩ := exists_comparison_of_isStopped _ hdomW (overlapBaseEquiv (n := n)
    (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) _ hcases _ _ (hR₁.congr_open (Set.ext fun _ => Iff.rfl)) hR₂
  refine ⟨η, fun y => ?_⟩
  have hz := congrArg (fun q : nestedOpens U₂ (U₁ ⊓ U₂) => q.val.val) (hη y)
  rw [overlapBaseEquiv_point] at hz
  have htproj := congrArg (fun q : U₂ => q.val) (proj_restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂ (η y))
  have hsproj := congrArg (fun q : U₁ => q.val) (proj_restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁ y)
  exact htproj.symm.trans (hz.trans hsproj)

end

end Hironaka.HironakaG3RStoppedOverlap
