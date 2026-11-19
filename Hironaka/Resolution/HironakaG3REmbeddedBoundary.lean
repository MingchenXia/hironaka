import Hironaka.Resolution.HironakaG3RGlobalSNC

/-! # G3: the chart boundaries of a glued embedded resolution agree on overlaps

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-embedded-boundary.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md`.

* `exists_comparison_boundary_of_isStopped`: the comparison of stopped prefixes over a base biholomorphism
  (`HironakaG3RStoppedOverlap.exists_comparison_of_isStopped`) carries the ordered nonempty members of the boundaries
  (held `first_meeting_choice_over_base_across_empty_boundaries`, `terminal_choice_over_base_across_empty_boundaries`).
* `incl_comparison`: the two chart identifications of a glued embedded resolution agree through any comparison (rigidity).
* **`chartBoundary_overlap`**: for two charts of a glued embedded resolution the ordered lists of nonempty traces of their
  boundaries on `P⁻¹(U¹ ∩ U²)` are equal (the embedded analogue of `HironakaG3RGluedBoundary.chartBoundary_overlap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3REmbeddedBoundary

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal RestrictEmptyTower
  HironakaOriginalTerminalOverlapComparison HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RTowerClass
  HironakaG3RStoppedOverlap HironakaG3RGluedEmbedded HironakaG3RGluedUniqueness
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open EmbeddedFromResolution (regularOpen regularAtDim_of_mem_regularOpen isInvDomain_vanishingIdeal_of_dim_lt)

variable {n : ℕ}

/-- **Stopped prefixes over biholomorphic bases, with their boundaries.** -/
theorem exists_comparison_boundary_of_isStopped {Z Z' Y Y' : CMfd.{u} n} (M : MarkedIdeal n Z) (hM : IsInvDomain n M)
    (Φ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z) (O : Opens Z)
    (hcases : (M.cosupp ∩ O).Nonempty ∨ M.cosupp = ∅) (S : BlowupTower Z' Y') (T : BlowupTower Z Y)
    (hS : IsStopped (pullback Φ M) (baseOpen Φ O) S) (hT : IsStopped M O T) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, (∀ y, T.proj (η y) = Φ (S.proj y)) ∧
      (geoTransformAlong (pullback Φ M) S).E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  have hmem : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hcos' : (pullback Φ M).cosupp = Φ ⁻¹' M.cosupp :=
    MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
      Φ.symm_apply_apply M hmem
  rcases hcases with ⟨x, hxM, hxO⟩ | hempty
  · have htT := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hT.1
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
    exact ⟨η, hη⟩
  · have hr := (HironakaOriginalIndependentStoppedSource.canonical_histories_empty_of_original_cosupp_empty M hM hempty
      T hT.1).2
    have hr' := (HironakaOriginalIndependentStoppedSource.canonical_histories_empty_of_original_cosupp_empty
      (pullback Φ M) hM' (by rw [hcos', hempty, preimage_empty]) S hS.1).2
    obtain ⟨η, hη, -⟩ := terminal_choice_over_base_across_empty_boundaries M (pullback Φ M) hM Φ rfl rfl rfl rfl
      S T hS.1 hT.1 hr' hr
    exact ⟨η, hη⟩

variable {X : CMfd.{u} n} {V : ClosedIrreducibleAnalyticSubvariety n X} {X' : CMfd.{u} n} {P : X' → X}

/-- **The two chart identifications agree through any comparison** (rigidity). -/
theorem incl_comparison (c₁ c₂ : TowerChart (embeddedClass V) X' P) {W : Opens X} (hW₂ : W ≤ c₂.U)
    (η : CMfd.of (n := n) (openPreimage c₁.T (nestedOpens c₁.U W)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage c₂.T (nestedOpens c₂.U W)))
    (hη : ∀ z, ((c₂.T.proj (η z).1 : c₂.U) : X) = ((c₁.T.proj z.1 : c₁.U) : X))
    (z : openPreimage c₁.T (nestedOpens c₁.U W)) :
    chartIncl c₂ (η z).1 = chartIncl c₁ z.1 := by
  have hmem : ∀ z : openPreimage c₁.T (nestedOpens c₁.U W), chartIncl c₁ z.1 ∈ c₂.V := by
    intro z
    apply c₂.mem_V
    rw [proj_chartIncl c₁ z.1]
    exact hW₂ z.2
  have hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : openPreimage c₁.T (nestedOpens c₁.U W) => (⟨chartIncl c₁ z.1, hmem z⟩ : c₂.V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (contMDiff_subtype_val.comp (c₁.φ.contMDiff.comp contMDiff_subtype_val)) hmem
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val ∘ η : openPreimage c₁.T (nestedOpens c₁.U W) → c₂.Y) :=
    contMDiff_subtype_val.comp η.contMDiff
  have hexc : exceptionalLocus n (Subtype.val ∘ η : openPreimage c₁.T (nestedOpens c₁.U W) → c₂.Y) = ∅ := by
    rw [exceptionalLocus_val_comp η.contMDiff]
    exact eq_empty_of_forall_notMem fun a ha => MarkedIdealTowerTransport.notMem_exceptionalLocus η a ha
  have h := eq_of_proj_eq (Z := CMfd.of (n := n) (openPreimage c₁.T (nestedOpens c₁.U W))) c₂.T
    (Subtype.val ∘ η) (c₂.φ.symm ∘ fun z => (⟨chartIncl c₁ z.1, hmem z⟩ : c₂.V)) hf
    (c₂.φ.symm.contMDiff.comp hk) (by rw [hexc, interior_empty]) (fun z => by
      apply Subtype.ext
      change ((c₂.T.proj (η z).1 : c₂.U) : X) = ((c₂.T.proj (c₂.φ.symm ⟨chartIncl c₁ z.1, hmem z⟩) : c₂.U) : X)
      rw [c₂.proj_symm, hη]
      exact (proj_chartIncl c₁ z.1).symm)
  have hz := congrArg (fun y => chartIncl c₂ y) (congrFun h z)
  simp only [Function.comp_apply] at hz
  rw [hz]
  simp [chartIncl]

theorem chartIncl_image_inter_preimage (c : TowerChart (embeddedClass V) X' P) (W : Opens X) (H : Set c.Y) :
    chartIncl c '' H ∩ P ⁻¹' (W : Set X) =
      (chartIncl c ∘ (Subtype.val : openPreimage c.T (nestedOpens c.U W) → c.Y)) ''
        ((Subtype.val : openPreimage c.T (nestedOpens c.U W) → c.Y) ⁻¹' H) := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    have hy' : y ∈ openPreimage c.T (nestedOpens c.U W) := by
      show ((c.T.proj y : c.U) : X) ∈ (W : Set X)
      rw [← proj_chartIncl c y]
      exact hz
    exact ⟨⟨y, hy'⟩, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y.1, hy, rfl⟩, ?_⟩
    show P (chartIncl c y.1) ∈ (W : Set X)
    rw [proj_chartIncl c y.1]
    exact y.2

/-- **The chart boundaries of a glued embedded resolution agree on overlaps.** -/
theorem chartBoundary_overlap (hV : V.dim < n) (c₁ c₂ : TowerChart (embeddedClass V) X' P) :
    ((chartBoundary c₁).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) =
      ((chartBoundary c₂).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty) := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) :=
    isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV
      (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic)
  have hpure : ∀ x : regularOpen V, (x : X) ∈ V.carrier → RegularAtDim (n := n) V.carrier x V.dim :=
    fun x hx => regularAtDim_of_mem_regularOpen hx x.2
  have hdense := HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V
  have hWU : c₁.U ⊓ c₂.U ≤ c₁.U := inf_le_left
  have hWV : c₁.U ⊓ c₂.U ≤ c₂.U := inf_le_right
  have hR₁ := isStopped_restrict_nested V.isClosed_carrier (regularOpen V) hpure hdense hdom c₁.U (c₁.U ⊓ c₂.U) c₁.T
    c₁.mem
  have hR₂ := isStopped_restrict_nested V.isClosed_carrier (regularOpen V) hpure hdense hdom c₂.U (c₁.U ⊓ c₂.U) c₂.T
    c₂.mem
  have he := original_overlap_whole_marked_dictionary _ hdom hWU hWV
  rw [← he] at hR₁
  have hdomU₁ := InvDomainTowerAlong.isInvDomain_pullback_val c₁.U hdom
  have hdomU₂ := InvDomainTowerAlong.isInvDomain_pullback_val c₂.U hdom
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) hdomU₂
  have hmem : ∀ x g, (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X).ideal.mem x g →
      HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hmemU : ∀ x g, (pullback (Subtype.val : c₂.U → X)
      (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomU₂.isWellFormed.isCoherent hg
  have hcosW : (pullback (Subtype.val : nestedOpens c₂.U (c₁.U ⊓ c₂.U) → c₂.U) (pullback (Subtype.val : c₂.U → X)
      (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))).cosupp =
      {q : nestedOpens c₂.U (c₁.U ⊓ c₂.U) | ((q : c₂.U) : X) ∈ V.carrier} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmemU, MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem,
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal V.isClosed_carrier]
    rfl
  have hcases : ((pullback (Subtype.val : nestedOpens c₂.U (c₁.U ⊓ c₂.U) → c₂.U) (pullback (Subtype.val : c₂.U → X)
      (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))).cosupp ∩
        (nestedOpens (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) (nestedOpens c₂.U (regularOpen V)) : Set _)).Nonempty ∨
      (pullback (Subtype.val : nestedOpens c₂.U (c₁.U ⊓ c₂.U) → c₂.U) (pullback (Subtype.val : c₂.U → X)
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))).cosupp = ∅ := by
    rw [hcosW]
    by_cases hx : ∃ x ∈ V.carrier, x ∈ regularOpen V ∧ x ∈ c₁.U ∧ x ∈ c₂.U
    · obtain ⟨x, hxV, hxO, hx₁, hx₂⟩ := hx
      exact Or.inl ⟨⟨⟨x, hx₂⟩, hx₁, hx₂⟩, hxV, hxO⟩
    · refine Or.inr (eq_empty_of_forall_notMem fun q hq => ?_)
      have hq₁ : ((q : c₂.U) : X) ∈ (c₁.U ⊓ c₂.U : Opens X) := q.2
      obtain ⟨x', hx'W, hx'V, hx'O⟩ := mem_closure_iff.mp (hdense hq) _ (c₁.U ⊓ c₂.U).isOpen hq₁
      exact hx ⟨x', hx'V, hx'O, hx'W.1, hx'W.2⟩
  obtain ⟨η, hη, hE⟩ := exists_comparison_boundary_of_isStopped _ hdomW (overlapBaseEquiv (n := n) hWU hWV) _ hcases
    _ _ (hR₁.congr_open (Set.ext fun _ => Iff.rfl)) hR₂
  rw [he] at hE
  have ht₁ := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hdomU₁ c₁.T c₁.mem.1
  have ht₂ := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hdomU₂ c₂.T c₂.mem.1
  rw [MarkedIdealRestrictOpen.geoTransformAlong_restrict _ hdomU₁.isWellFormed.isClosedSubmanifold_N
      hdomU₁.isWellFormed.isCoherent c₁.T ht₁,
    MarkedIdealRestrictOpen.geoTransformAlong_restrict _ hdomU₂.isWellFormed.isClosedSubmanifold_N
      hdomU₂.isWellFormed.isCoherent c₂.T ht₂] at hE
  have hη' : ∀ z, ((c₂.T.proj (η z).1 : c₂.U) : X) = ((c₁.T.proj z.1 : c₁.U) : X) := by
    intro y
    have hz := congrArg (fun q : nestedOpens c₂.U (c₁.U ⊓ c₂.U) => q.val.val) (hη y)
    rw [overlapBaseEquiv_point] at hz
    have htproj := congrArg (fun q : c₂.U => q.val)
      (proj_restrict (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) c₂.T (η y))
    have hsproj := congrArg (fun q : c₁.U => q.val)
      (proj_restrict (nestedOpens c₁.U (c₁.U ⊓ c₂.U)) c₁.T y)
    exact htproj.symm.trans (hz.trans hsproj)
  have hincl := incl_comparison c₁ c₂ hWV η hη'
  have hL : ∀ c : TowerChart (embeddedClass V) X' P,
      (chartBoundary c).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X)) =
        ((geoTransformAlong (pullback (Subtype.val : c.U → X)
            (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) c.T).E.map
          ((Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y) ⁻¹' ·)).map
          ((chartIncl c ∘ (Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y)) '' ·) := by
    intro c
    unfold chartBoundary
    rw [List.map_map, List.map_map]
    congr 1
    funext H
    exact chartIncl_image_inter_preimage c _ H
  rw [hL c₁, hL c₂, HironakaG3RGluedBoundary.filter_nonempty_map_image,
    HironakaG3RGluedBoundary.filter_nonempty_map_image]
  erw [hE]
  rw [List.map_map]
  congr 1
  funext B
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨η a, ha, hincl a⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨η.symm b, show η (η.symm b) ∈ B by rw [η.apply_symm_apply]; exact hb, ?_⟩
    have h := hincl (η.symm b)
    rw [η.apply_symm_apply] at h
    exact h.symm

end

end Hironaka.HironakaG3REmbeddedBoundary
