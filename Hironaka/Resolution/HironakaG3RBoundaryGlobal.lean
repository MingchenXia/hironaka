import Hironaka.Resolution.HironakaG3RBoundaryEmbedded
import Hironaka.Resolution.HironakaG3RPureBoundary

/-! # G3: the global boundary of the glued embedded resolution relative to a simple normal crossings boundary

Lane G3 (run 0080, round 6).  Blueprint: `hironaka-g3-r-boundary-global.tex`.  The boundary version of
`HironakaG3RPureBoundary`.

* **`chartBoundary_overlap`**: for two charts of a glued embedded resolution of `(W, d)` relative to `E₀`, the ordered lists
  of nonempty traces of their boundaries (the strict transforms of the members of `E₀`, then the new members) on
  `P⁻¹(U¹ ∩ U²)` are equal.
* **`exists_globalBoundary`**: `P⁻¹|E₀| ∪ Exc P` is the union of a locally finite indexed simple normal crossings family of
  nonempty closed sets (`HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor`) with which the strict transform of
  `W` has only normal crossings (`HironakaActualIndexedBoundaryContinuation.HasNormalCrossingsWithBoundary`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RBoundaryGlobal

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings CanonicalCentres MaxLocusLocal
  RestrictEmptyTower HironakaOriginalTerminalOverlapComparison HironakaG3RTowerClass HironakaG3RStoppedOverlap
  HironakaG3RGluedUniqueness HironakaG3RPureEmbedded HironakaG3RPureBoundary HironakaG3RBoundaryOverlap
  HironakaG3RBoundaryEmbedded
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open HironakaActualIndexedBoundaryContinuation (HasNormalCrossingsWithBoundary)
open HironakaActualLocallyFiniteBoundary (IsLocallyFiniteSNCDivisor)

variable {n : ℕ}

/-! ### Chart boundaries agree on overlaps -/

section Overlap

variable {X : CMfd.{u} n} {W : Set X} {d : ℕ} {E₀ : List (Set X)} {X' : CMfd.{u} n} {P : X' → X}

/-- **The chart boundaries of a glued embedded resolution relative to a boundary agree on overlaps.** -/
theorem chartBoundary_overlap (hWa : IsComplexAnalyticSubset (n := n) W) (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (c₁ c₂ : TowerChart (bdryClass W d E₀) X' P) :
    ((chartBoundary c₁ (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
        (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) =
      ((chartBoundary c₂ (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
        (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) := by
  have hdom : IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) :=
    isInvDomain_bdry hWa hd hpure hE₀
  have hW := hWa.isClosed
  have hpure' : ∀ x : bdryOpen W d E₀, (x : X) ∈ W → RegularAtDim (n := n) W x d :=
    fun x hx => regularAtDim_of_mem_bdryOpen hW hE₀.1 hx x.2
  have hdense := subset_closure_inter_bdryOpen hW hpure hE₀.1 hE₀W
  have hEO := disjoint_bdryOpen hW d hE₀.1
  have hWU : c₁.U ⊓ c₂.U ≤ c₁.U := inf_le_left
  have hWV : c₁.U ⊓ c₂.U ≤ c₂.U := inf_le_right
  have hR₁ := isStopped_restrict_nested_bdry hW (bdryOpen W d E₀) hEO hpure' hdense hdom c₁.U (c₁.U ⊓ c₂.U) c₁.T
    c₁.mem
  have hR₂ := isStopped_restrict_nested_bdry hW (bdryOpen W d E₀) hEO hpure' hdense hdom c₂.U (c₁.U ⊓ c₂.U) c₂.T
    c₂.mem
  have he := original_overlap_whole_marked_dictionary _ hdom hWU hWV
  rw [← he] at hR₁
  have hdomU₁ := InvDomainTowerAlong.isInvDomain_pullback_val c₁.U hdom
  have hdomU₂ := InvDomainTowerAlong.isInvDomain_pullback_val c₂.U hdom
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) hdomU₂
  have hmem : ∀ x g, (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X).ideal.mem x g →
      HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hmemU : ∀ x g, (pullback (Subtype.val : c₂.U → X)
      (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomU₂.isWellFormed.isCoherent hg
  have hcosW : (pullback (Subtype.val : nestedOpens c₂.U (c₁.U ⊓ c₂.U) → c₂.U) (pullback (Subtype.val : c₂.U → X)
      (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))).cosupp =
      {q : nestedOpens c₂.U (c₁.U ⊓ c₂.U) | ((q : c₂.U) : X) ∈ W} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmemU, MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem,
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW]
    rfl
  have hcases : ((pullback (Subtype.val : nestedOpens c₂.U (c₁.U ⊓ c₂.U) → c₂.U) (pullback (Subtype.val : c₂.U → X)
      (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))).cosupp ∩
        (nestedOpens (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) (nestedOpens c₂.U (bdryOpen W d E₀)) : Set _)).Nonempty ∨
      (pullback (Subtype.val : nestedOpens c₂.U (c₁.U ⊓ c₂.U) → c₂.U) (pullback (Subtype.val : c₂.U → X)
        (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))).cosupp = ∅ := by
    rw [hcosW]
    by_cases hx : ∃ x ∈ W, x ∈ bdryOpen W d E₀ ∧ x ∈ c₁.U ∧ x ∈ c₂.U
    · obtain ⟨x, hxV, hxO, hx₁, hx₂⟩ := hx
      exact Or.inl ⟨⟨⟨x, hx₂⟩, hx₁, hx₂⟩, hxV, hxO⟩
    · refine Or.inr (eq_empty_of_forall_notMem fun q hq => ?_)
      have hq₁ : ((q : c₂.U) : X) ∈ (c₁.U ⊓ c₂.U : Opens X) := q.2
      obtain ⟨x', hx'W, hx'V, hx'O⟩ := mem_closure_iff.mp (hdense hq) _ (c₁.U ⊓ c₂.U).isOpen hq₁
      exact hx ⟨x', hx'V, hx'O, hx'W.1, hx'W.2⟩
  obtain ⟨η, hη, hE⟩ := HironakaG3REmbeddedBoundary.exists_comparison_boundary_of_isStopped _ hdomW
    (overlapBaseEquiv (n := n) hWU hWV) _ hcases _ _ (hR₁.congr_open (Set.ext fun _ => Iff.rfl)) hR₂
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
  have hL : ∀ c : TowerChart (bdryClass W d E₀) X' P,
      (chartBoundary c (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
          (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X)) =
        ((geoTransformAlong (pullback (Subtype.val : c.U → X)
            (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) c.T).E.map
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

end Overlap

/-! ### The global boundary -/

section Global

open HironakaG3REmbeddedGlobalSNC

variable {X : CMfd.{u} n} {W : Set X} {d : ℕ} {E₀ : List (Set X)} {X' : CMfd.{u} n} {P : X' → X}

/-- **The global boundary of a glued embedded resolution relative to a boundary**: a locally finite indexed simple normal
crossings family of nonempty closed sets whose union is the total transform of `|E₀|` together with the exceptional locus,
`P⁻¹|E₀| ∪ Exc P`, and with which the strict transform of `W` has only normal crossings. -/
theorem exists_globalBoundary (hWa : IsComplexAnalyticSubset (n := n) W) (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (h : IsGluedBoundaryResolution W d E₀ X' P) :
    ∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧
      (∀ i, (D i).Nonempty) ∧ (⋃ i, D i) = P ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n P ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) D := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let K := CompactExhaustion.choice X
  have hU : ∀ k : ℕ, ∃ c : TowerChart (bdryClass W d E₀) X' P, c.U = ⟨interior (K (k + 1)), isOpen_interior⟩ :=
    fun k => exists_chart_of_subset_isCompact hWa hd hpure hE₀ hE₀W h _ (K.isCompact (k + 1)) interior_subset
  choose c hc using hU
  have hUmono : ∀ {j k : ℕ}, j ≤ k → (c j).U ≤ (c k).U := fun {j k} hjk => by
    rw [hc, hc]
    exact interior_mono (K.subset (by omega))
  have hVmono : ∀ {j k : ℕ}, j ≤ k → ((c j).V : Set X') ⊆ (c k).V := fun {j k} hjk y hy => by
    have h' : y ∈ ((c j).V : Set X') := hy
    rw [(c j).V_eq] at h'
    exact (c k).mem_V (hUmono hjk h')
  have hcover : ∀ y : X', ∃ k, y ∈ (c k).V := fun y => by
    obtain ⟨k, hk⟩ := K.exists_mem (P y)
    refine ⟨k, (c k).mem_V ?_⟩
    rw [hc]
    exact K.subset_interior_succ k hk
  have hnested : ∀ {j k : ℕ}, j ≤ k →
      ((chartBoundary (c k) (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
          (· ∩ ((c j).V : Set X'))).filter (fun H => decide H.Nonempty) =
        (chartBoundary (c j) (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).filter
          (fun H => decide H.Nonempty) := fun {j k} hjk => by
    have hov := chartBoundary_overlap hWa hd hpure hE₀ hE₀W (c j) (c k)
    have hpre : P ⁻¹' (((c j).U ⊓ (c k).U : Opens X) : Set X) = ((c j).V : Set X') := by
      rw [(c j).V_eq]
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, hUmono hjk h⟩⟩
    rw [hpre] at hov
    have hself : (chartBoundary (c j) (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
        (· ∩ ((c j).V : Set X')) =
          chartBoundary (c j) (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) := by
      conv_rhs => rw [← List.map_id (chartBoundary (c j) _)]
      exact List.map_congr_left fun H hH => inter_eq_left.mpr (chartBoundary_subset_V (c j) _ hH)
    rw [hself] at hov
    exact hov.symm
  let Ex : SNCExhaustion X' :=
    { W := fun k => (c k).V
      B := fun k => chartBoundary (c k) (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      mono := hVmono
      cover := hcover
      sub := fun {k} {H} hH => chartBoundary_subset_V (c k) _ hH
      snc := fun k => (chart_boundary hWa hd hpure hE₀ hE₀W h (c k)).1
      nested := hnested }
  refine ⟨{D : Set X' // Ex.IsGlobalMember D}, fun i => i.1,
    ⟨Ex.locallyFinite_globalMember, fun i => Ex.isClosed_globalMember i.2, Ex.coordinates_globalMember⟩,
    fun i => i.2.1, Ex.iUnion_globalMember.trans ?_,
    HironakaG3REmbeddedNC.SNCExhaustion'.hasNormalCrossingsWithBoundary Ex _ fun k =>
      (chart_boundary hWa hd hpure hE₀ hE₀W h (c k)).2.2⟩
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk'⟩ := mem_iUnion.mp hy
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hk'
    have hy' : y ∈ ⋃ H ∈ chartBoundary (c k) (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X), H :=
      mem_biUnion hH hyH
    rw [(chart_boundary hWa hd hpure hE₀ hE₀W h (c k)).2.1] at hy'
    exact hy'.1
  · intro hy
    obtain ⟨k, hk⟩ := hcover y
    have hy' : y ∈ ⋃ H ∈ chartBoundary (c k) (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X), H := by
      rw [(chart_boundary hWa hd hpure hE₀ hE₀W h (c k)).2.1]
      exact ⟨hy, hk⟩
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hy'
    exact mem_iUnion.mpr ⟨k, mem_iUnion₂.mpr ⟨H, hH, hyH⟩⟩

end Global

end

end Hironaka.HironakaG3RBoundaryGlobal
