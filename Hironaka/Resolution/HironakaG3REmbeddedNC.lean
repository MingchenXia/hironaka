import Hironaka.Resolution.HironakaG3REmbeddedGlobalSNC
import Hironaka.Resolution.HironakaActualIndexedBoundaryContinuation

/-! # G3: the strict transform has normal crossings with the global embedded boundary

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-embedded-nc.tex`.

* `SNCExhaustion.hasNormalCrossingsWithBoundary` (generic): if a set `C` has normal crossings with every list `B k` on
  `W k`, it has normal crossings with the global family (held indexed convention
  `HironakaActualIndexedBoundaryContinuation.HasNormalCrossingsWithBoundary`).
* **`exists_globalBoundary_embeddedResolution`**: for every glued embedded resolution `P : X' → X` of a closed
  irreducible `V` with `dim V < n`, a locally finite indexed simple normal crossings family of nonempty closed sets with
  union `Exc P = P⁻¹ V_sing`, with which the strict transform of `V` has only normal crossings.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3REmbeddedNC

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.NonKahlerLocus Hironaka.BlowupSequences BlowupTowers MarkedIdeals NormalCrossings
  HironakaG3RTowerClass HironakaG3RGluedEmbedded HironakaG3REmbeddedGlobalSNC
open HironakaActualIndexedBoundaryContinuation (HasNormalCrossingsWithBoundary)

variable {n : ℕ}

namespace SNCExhaustion'

variable {X' : CMfd.{u} n} (Ex : SNCExhaustion X')

/-- **Normal crossings with the global family**, from normal crossings with each list. -/
theorem hasNormalCrossingsWithBoundary (C : Set X')
    (hNC : ∀ k, HasNormalCrossings n ((Subtype.val : Ex.W k → X') ⁻¹' C)
      ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·))) :
    HasNormalCrossingsWithBoundary C (fun i : {D : Set X' // Ex.IsGlobalMember D} => (i : Set X')) := by
  intro x hxC
  obtain ⟨k, hk⟩ := Ex.cover x
  obtain ⟨S₀, S, ⟨Φ, hsrc, hzero, hcoord⟩, hcard⟩ := hNC k ⟨x, hk⟩ hxC
  have hpos : ∀ i : {D : Set X' // Ex.IsGlobalMember D}, ((i : Set X') ∩ Ex.W k) ∈ Ex.B k →
      ∃ p : Fin ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).length,
        ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).get p =
          (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') := fun i hi => by
    obtain ⟨p, hp⟩ := List.mem_iff_get.mp (List.mem_map_of_mem (f := ((Subtype.val : Ex.W k → X') ⁻¹' ·)) hi)
    refine ⟨p, hp.trans ?_⟩
    ext q
    exact ⟨fun h => h.1, fun h => ⟨h, q.2⟩⟩
  let S' : {D : Set X' // Ex.IsGlobalMember D} → Finset (Fin n) := fun i =>
    if hi : ((i : Set X') ∩ Ex.W k) ∈ Ex.B k then S (hpos i hi).choose else ∅
  have hmemx : ∀ i : {D : Set X' // Ex.IsGlobalMember D}, x ∈ (i : Set X') → ((i : Set X') ∩ Ex.W k) ∈ Ex.B k :=
    fun i hx => i.2.mem_of_nonempty Ex k ⟨x, hx, hk⟩
  have hS' : ∀ (i : {D : Set X' // Ex.IsGlobalMember D}) (hx : x ∈ (i : Set X')),
      S' i = S (hpos i (hmemx i hx)).choose := fun i hx => dif_pos (hmemx i hx)
  have hget : ∀ (i : {D : Set X' // Ex.IsGlobalMember D}) (hx : x ∈ (i : Set X')),
      ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).get (hpos i (hmemx i hx)).choose =
        (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') := fun i hx => (hpos i (hmemx i hx)).choose_spec
  refine ⟨S₀, S', ?_, ?_⟩
  · have hfam : (fun o : Option {D : Set X' // Ex.IsGlobalMember D} =>
        (Subtype.val : Ex.W k → X') ⁻¹' (o.elim C fun i => (i : Set X'))) =
        fun o => o.elim ((Subtype.val : Ex.W k → X') ⁻¹' C) fun i => (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') := by
      funext o
      cases o <;> rfl
    apply (NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff (x := (⟨x, hk⟩ : Ex.W k))).mp
    rw [hfam]
    refine ⟨Φ, hsrc, hzero, fun o hxo y hy hyΦ => ?_⟩
    cases o with
    | none => exact hcoord none hxo hy hyΦ
    | some i =>
      have hxi' : x ∈ (i : Set X') := hxo
      change y ∈ (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') ↔
        Φ.toFun ((complexChartAt (n := n) (⟨x, hk⟩ : Ex.W k)).val y) ∈ coordSubspace (S' i)
      rw [hS' i hxi']
      have h := hcoord (some (hpos i (hmemx i hxi')).choose) (by
        change (⟨x, hk⟩ : Ex.W k) ∈ ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).get _
        rw [hget i hxi']
        exact hxi') hy hyΦ
      change y ∈ ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).get _ ↔ _ at h
      rw [hget i hxi'] at h
      exact h
  · intro i hxi
    rw [hS' i hxi]
    exact hcard _ (by rw [hget i hxi]; exact hxi)

end SNCExhaustion'

section Embedded

open HironakaG3REmbeddedBoundary HironakaG3RChartOfMember

variable {X : CMfd.{u} n} {V : ClosedIrreducibleAnalyticSubvariety n X} {X' : CMfd.{u} n} {P : X' → X}

/-- **The global boundary of a glued embedded resolution**: a locally finite indexed simple normal crossings family of
nonempty closed sets with union `Exc P = P⁻¹ V_sing`, with which the strict transform of `V` has only normal crossings. -/
theorem exists_globalBoundary_embeddedResolution (hV : V.dim < n) (h : IsGluedEmbeddedResolution V X' P) :
    ∃ (ι : Type u) (D : ι → Set X'), HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor n D ∧
      (∀ i, (D i).Nonempty) ∧ (⋃ i, D i) = exceptionalLocus n P ∧
      HasNormalCrossingsWithBoundary (strictTransform n P V.carrier) D := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let K := CompactExhaustion.choice X
  have hU : ∀ k : ℕ, ∃ c : TowerChart (embeddedClass V) X' P, c.U = ⟨interior (K (k + 1)), isOpen_interior⟩ :=
    fun k => exists_embeddedChart_of_subset_isCompact hV h _ (K.isCompact (k + 1)) interior_subset
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
      ((chartBoundary (c k)).map (· ∩ ((c j).V : Set X'))).filter (fun H => decide H.Nonempty) =
        (chartBoundary (c j)).filter (fun H => decide H.Nonempty) := fun {j k} hjk => by
    have hov := chartBoundary_overlap hV (c j) (c k)
    have hpre : P ⁻¹' (((c j).U ⊓ (c k).U : Opens X) : Set X) = ((c j).V : Set X') := by
      rw [(c j).V_eq]
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, hUmono hjk h⟩⟩
    rw [hpre] at hov
    have hself : (chartBoundary (c j)).map (· ∩ ((c j).V : Set X')) = chartBoundary (c j) := by
      conv_rhs => rw [← List.map_id (chartBoundary (c j))]
      exact List.map_congr_left fun H hH => inter_eq_left.mpr (chartBoundary_subset_V (c j) hH)
    rw [hself] at hov
    exact hov.symm
  let Ex : SNCExhaustion X' :=
    { W := fun k => (c k).V
      B := fun k => chartBoundary (c k)
      mono := hVmono
      cover := hcover
      sub := fun {k} {H} hH => chartBoundary_subset_V (c k) hH
      snc := fun k => (chart_boundary hV h (c k)).1
      nested := hnested }
  refine ⟨{D : Set X' // Ex.IsGlobalMember D}, fun i => i.1,
    ⟨Ex.locallyFinite_globalMember, fun i => Ex.isClosed_globalMember i.2, Ex.coordinates_globalMember⟩,
    fun i => i.2.1, Ex.iUnion_globalMember.trans ?_,
    SNCExhaustion'.hasNormalCrossingsWithBoundary Ex _ fun k => (chart_boundary hV h (c k)).2.2⟩
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk'⟩ := mem_iUnion.mp hy
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hk'
    have hy' : y ∈ ⋃ H ∈ chartBoundary (c k), H := mem_biUnion hH hyH
    rw [(chart_boundary hV h (c k)).2.1] at hy'
    exact hy'.1
  · intro hy
    obtain ⟨k, hk⟩ := hcover y
    have hy' : y ∈ ⋃ H ∈ chartBoundary (c k), H := by
      rw [(chart_boundary hV h (c k)).2.1]
      exact ⟨hy, hk⟩
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hy'
    exact mem_iUnion.mpr ⟨k, mem_iUnion₂.mpr ⟨H, hH, hyH⟩⟩

end Embedded

end

end Hironaka.HironakaG3REmbeddedNC
