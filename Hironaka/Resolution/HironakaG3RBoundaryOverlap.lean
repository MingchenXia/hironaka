import Hironaka.Resolution.HironakaG3RStoppedOverlap

/-! # G3: stopped canonical prefixes relative to a boundary agree on overlaps

Lane G3 (run 0080, round 6).  Blueprint: `hironaka-g3-r-boundary-overlap.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (G3P03′, boundary-relative embedded resolution).

The boundary version of `HironakaG3RStoppedOverlap`.  For the embedded resolution of a closed analytic set `V` relative to a
divisor `E` (a list of closed sets, in practice with simple normal crossings) the local pieces are the stopped prefixes of
`(U, U, E|_U, 𝓘_{V ∩ U}, 1)` relative to an open set `O` MISSING the members of `E` (in practice
`X ∖ (V_sing ∪ |E|)`).  The only place where the empty divisor was used in `HironakaG3RStoppedOverlap` is the homogeneity of
the invariant over `O`; for a divisor whose members miss `O` it is the held
`HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim`.

* **`isStopped_restrict_bdry`**, **`isStopped_restrict_nested_bdry`**: restrictions of stopped prefixes are stopped.
* **`hasComparisons_stoppedClass_bdry`** (the overlap lemma): two stopped prefixes of `(X, X, E, 𝓘_V, 1)` relative to `O` are
  compared over the intersection of their bases.  With `E = []` it is `HironakaG3RStoppedOverlap.hasComparisons_stoppedClass`.
* **`biUnion_E_geoTransformAlong`** (generic): the union of the transformed divisor along a tower is the total transform of
  the union of the initial divisor together with the support of the exceptional divisor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RBoundaryOverlap

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal RestrictEmptyTower
  HironakaOriginalTerminalOverlapComparison HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RTowerClass
  HironakaG3RStoppedOverlap BlowupStrictSubmanifold
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

variable {n : ℕ}

/-! ### The union of the transformed divisor -/

/-- **The union of the transformed divisor is the total transform of the initial divisor together with the support of the
exceptional divisor** (members closed): `⋃ E(𝔪_T) = T⁻¹(⋃ E(𝔪)) ∪ supp E_T`.  The members are carried by strict transforms,
and `π⁻¹ H ⊆ π̃(H) ∪ π⁻¹ C ⊆ π⁻¹ H ∪ π⁻¹ C`. -/
theorem biUnion_E_geoTransformAlong {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (h𝔪 : ∀ H ∈ 𝔪.E, IsClosed H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (⋃ H ∈ (geoTransformAlong 𝔪 T).E, H) =
        T.proj ⁻¹' (⋃ H ∈ 𝔪.E, H) ∪ (BlowupTowerTransforms.exceptionalDivisor T).support
  | _, .refl => by
      rw [geoTransformAlong_refl, BlowupTower.proj_refl, preimage_id]
      have h0 : (BlowupTowerTransforms.exceptionalDivisor (BlowupTower.refl : BlowupTower X X)).support = ∅ := by
        ext x
        simp only [mem_empty_iff_false, iff_false]
        intro hx
        exact one_ne_zero (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1))
      rw [h0, union_empty]
  | _, .step T C π hπ => by
      have ih := biUnion_E_geoTransformAlong 𝔪 h𝔪 T
      have hcl := HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong 𝔪 h𝔪 T
      show (⋃ H ∈ ((geoTransformAlong 𝔪 T).geoTransform C π).E, H) =
        (T.proj ∘ π) ⁻¹' (⋃ H ∈ 𝔪.E, H) ∪ (GermIdealTotalTransform.EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (BlowupTowerTransforms.exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support
      rw [HironakaPrincipalization.support_add, BlowupExceptionalDivisor.support_totalTransform,
        BlowupExceptionalDivisor.support_exceptionalDivisor, geoTransform_E, preimage_comp]
      have hpre : π ⁻¹' (T.proj ⁻¹' (⋃ H ∈ 𝔪.E, H)) ∪ π ⁻¹' (BlowupTowerTransforms.exceptionalDivisor T).support =
          π ⁻¹' (⋃ H ∈ (geoTransformAlong 𝔪 T).E, H) := by
        rw [ih, preimage_union]
      rw [← union_assoc, hpre]
      ext z
      simp only [mem_union, mem_preimage, mem_iUnion, List.mem_append, List.mem_map, List.mem_singleton,
        exists_prop]
      constructor
      · rintro ⟨H', (⟨H, hH, rfl⟩ | rfl), hz⟩
        · left
          refine ⟨H, hH, ?_⟩
          have hsub : geoStrictTransform π C H ⊆ π ⁻¹' H :=
            closure_minimal (fun w hw => hw.1) ((hcl H hH).preimage hπ.contMDiff.continuous)
          exact hsub hz
        · exact Or.inr hz
      · rintro (⟨H, hH, hzH⟩ | hzC)
        · by_cases hzC : π z ∈ C
          · exact ⟨π ⁻¹' C, Or.inr rfl, hzC⟩
          · exact ⟨geoStrictTransform π C H, Or.inl ⟨H, hH, rfl⟩, subset_closure ⟨hzH, hzC⟩⟩
        · exact ⟨π ⁻¹' C, Or.inr rfl, hzC⟩

/-! ### Restriction of stopped prefixes relative to a boundary -/

/-- **The restriction of a stopped prefix relative to a boundary is stopped.**  Let `V ⊆ Z` be closed, `E` a list of sets,
`O ⊆ Z` an open set missing the members of `E`, `V` regular of dimension `d` at the points of `V ∩ O`, and `V ∩ O` dense in
`V`.  For a stopped prefix `S` of `(Z, Z, E, 𝓘_V, 1)` relative to `O` and an open `B ⊆ Z`, the restriction `S|_B` is a stopped
prefix of the restriction relative to `O ∩ B`. -/
theorem isStopped_restrict_bdry {Z Y : CMfd.{u} n} {V : Set Z} (hV : IsClosed V) {E : List (Set Z)} (O : Opens Z)
    (hEO : ∀ H ∈ E, Disjoint H (O : Set Z)) {d : ℕ}
    (hpure : ∀ x : O, (x : Z) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z)) (B : Opens Z)
    (S : BlowupTower Z Y) (hS : IsStopped (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z) O S) :
    IsStopped (pullback (Subtype.val : B → Z) (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z))
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
        (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z) S)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z) S).cosupp,
        S.proj c ∈ O := by
      rcases hS.2.2 with h | h
      · exact h
      · rw [h.2] at hycos
        exact absurd hycos (notMem_empty y)
    have hym := (HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hV O hEO hpure hdom S hS.1
      hS.2.1 hc hcO hyO).mpr hyV
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
    have hmem : ∀ x g, (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z).ideal.mem x g →
        HolomorphicAt n g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
    have hcos : (pullback (Subtype.val : B → Z) (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n Z)).cosupp
        = ∅ := by
      rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem B, HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hV]
      exact eq_empty_of_forall_notMem fun q hq => hVB q hq q.2
    exact (HironakaOriginalIndependentStoppedSource.canonical_histories_empty_of_original_cosupp_empty _ hdomB hcos _
      hcanB).2

/-- Restricting a member of the stopped class of `(X, X, E, 𝓘_V, 1)` over `U` to an open `W ⊆ U`. -/
theorem isStopped_restrict_nested_bdry {X : CMfd.{u} n} {V : Set X} (hV : IsClosed V) {E : List (Set X)} (O : Opens X)
    (hEO : ∀ H ∈ E, Disjoint H (O : Set X)) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (U W : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : stoppedClass (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U Y T) :
    IsStopped (pullback (Subtype.val : nestedOpens U W → U)
        (pullback (Subtype.val : U → X) (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)))
      (nestedOpens (nestedOpens U W) (nestedOpens U O)) (restrict (nestedOpens U W) T) := by
  have e := HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal U E V
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  change IsStopped (pullback (Subtype.val : U → X) (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (nestedOpens U O) T at hT
  rw [e] at hT hdomU ⊢
  have hdenseU : (Subtype.val : U → X) ⁻¹' V ⊆ closure ((Subtype.val : U → X) ⁻¹' V ∩ nestedOpens U O) := by
    intro q hq
    have h2 := (U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val (V ∩ O)
    exact (Set.ext_iff.mp h2 q).mp (hdense hq)
  have hEOU : ∀ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), Disjoint H (nestedOpens U O : Set U) := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact Set.disjoint_left.mpr fun q hq hqO => Set.disjoint_left.mp (hEO H₀ hH₀) hq hqO
  exact isStopped_restrict_bdry (hV.preimage continuous_subtype_val) (nestedOpens U O) hEOU
    (fun x hx => (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U)).mpr (hpure ⟨((x : U) : X), x.2⟩ hx))
    hdenseU hdomU (nestedOpens U W) T hT

/-- **Stopped prefixes relative to a boundary agree on overlaps.**  For a closed `V ⊆ X`, a list `E` of sets, an open `O ⊆ X`
missing the members of `E` on which `V` is regular of dimension `d`, with `V ∩ O` dense in `V` and `(X, X, E, 𝓘_V, 1)` in the
domain, any two stopped prefixes over `U₁` and `U₂` are compared over `U₁ ∩ U₂` by a biholomorphism commuting with the
projections. -/
theorem hasComparisons_stoppedClass_bdry {X : CMfd.{u} n} {V : Set X} (hV : IsClosed V) {E : List (Set X)}
    (O : Opens X) (hEO : ∀ H ∈ E, Disjoint H (O : Set X)) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) :
    HasComparisons (stoppedClass (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  have hR₁ := isStopped_restrict_nested_bdry hV O hEO hpure hdense hdom U₁ (U₁ ⊓ U₂) T₁ h₁
  have hR₂ := isStopped_restrict_nested_bdry hV O hEO hpure hdense hdom U₂ (U₁ ⊓ U₂) T₂ h₂
  have he := original_overlap_whole_marked_dictionary _ hdom (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  rw [← he] at hR₁
  have hdomU₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens U₂ (U₁ ⊓ U₂)) hdomU₂
  have hmem : ∀ x g, (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X).ideal.mem x g →
      HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hmemU : ∀ x g, (pullback (Subtype.val : U₂ → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomU₂.isWellFormed.isCoherent hg
  have hcosW : (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp =
      {q : nestedOpens U₂ (U₁ ⊓ U₂) | ((q : U₂) : X) ∈ V} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmemU, MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem,
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hV]
    rfl
  have hcases : ((pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp ∩
        (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ O) : Set _)).Nonempty ∨
      (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
        (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp = ∅ := by
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

end Hironaka.HironakaG3RBoundaryOverlap
