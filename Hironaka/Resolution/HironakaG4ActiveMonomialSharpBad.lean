import Hironaka.Resolution.HironakaG4BoundaryDifferentialCriterion
import Hironaka.Resolution.HironakaSharpActualTraceIncidence

set_option autoImplicit false

/-! Actual original NC points have no old trace factor along another boundary
position. Blueprint: `hironaka-g4-active-monomial-sharp-bad.tex`.
This is current sharp-good avoidance, not a future resolving schedule. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ActiveMonomialSharpBad

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings SimultaneousNormalCrossings BlowupFlatCoordinates
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpNestedNormalCrossingsInheritance HironakaG4BoundaryDifferentialCriterion
  HironakaSharpActualTraceIncidence RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdealOperationsAlong MonomialPartAlong DivisorExponentAlong GermIdealOrder
  RankDegeneracy HadamardBridge BlowupSNCTransform InvertibleIdealQuotient

variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual full NC forbids a whole old trace factor along a DISTINCT incident
boundary position, before any preparation of residual supports. -/
theorem divExpAlong_restricted_member_eq_zero_at_normalCrossings (hn : 0 < n)
    {N : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hdense : N ⊆ closure (N \ ⋃ H ∈ E, H))
    {x : X} (hxN : x ∈ N) (hNC : normalCrossingsAt (n := n) N E x)
    (i j : Fin E.length) (hij : i ≠ j) (hxj : x ∈ E.get j) :
    divExpAlong n N (restrictOn n N (vanishingIdeal (n := n) (E.get i)))
      (E.get j) x = 0 := by
  classical
  let I := restrictOn n N (vanishingIdeal (n := n) (E.get i))
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hcI : I.IsCoherent := isCoherent_restrictOn hcH
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  have hhol := fun y g (hg : I.mem y g) =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcI hg
  by_contra hne
  have hpos : 1 ≤ divExpAlong n N I (E.get j) x := Nat.one_le_iff_ne_zero.mpr hne
  have hdiv := (isDivNearAlong_divExpAlong hhol x).mono hpos
  have hxZ : x ∈ I.zeroLocus := by
    intro g hg
    exact (vanishesToOrderOn_one_iff hxN (hhol x g hg)).mp
      ((hdiv.self_of_nhds hxN hxj).2 g hg)
  have hxi : x ∈ E.get i := by
    have hz := (zeroLocus_restrictOn_iff hcH hxN).mp hxZ
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hE.1 _ (List.get_mem E i))] at hz
  have hnot : ∀ a : Fin E.length, x ∈ E.get a →
      ¬∀ᶠ y in 𝓝 x, y ∈ N → y ∈ E.get a := by
    intro a _ha hcontains
    have hfreq := mem_closure_iff_frequently.mp (hdense hxN)
    obtain ⟨y, ⟨hyN, hyE⟩, hyH⟩ := (hfreq.and_eventually hcontains).exists
    exact hyE (mem_iUnion₂.mpr ⟨E.get a, List.get_mem E a, hyH hyN⟩)
  obtain ⟨S₀, S, ⟨Φ, hsrc, h0, hfam⟩, hfree⟩ :=
    exists_actual_free_family_of_germ_noncontainment hxN hNC hnot
  obtain ⟨a, haS⟩ := Finset.card_eq_one.mp (hfree i hxi).1
  obtain ⟨b, hbS⟩ := Finset.card_eq_one.mp (hfree j hxj).1
  have hxD := mem_flatDomain_self Φ
  have hA (k : Fin E.length) (hk : x ∈ E.get k) : ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ E.get k ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S k)) :=
    fun hy hyΦ => hfam (some k) hk hy hyΦ
  have hAi : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) a = 0) := by
    intro y hy hyΦ
    simpa only [haS, mem_coordSubspace_singleton] using hA i hxi hy hyΦ
  have hAj : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ E.get j ↔ Φ.toFun ((complexChartAt (n := n) x).val y) b = 0) := by
    intro y hy hyΦ
    simpa only [hbS, mem_coordSubspace_singleton] using hA j hxj hy hyΦ
  have hab : a ≠ b := by
    intro heq
    apply hij
    apply eq_of_eventually_mem_iff hE hxi hxj
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with y hy
    rw [hAi hy.1 hy.2, hAj hy.1 hy.2, heq]
  have haN : a ∉ S₀ := by
    have h := (hfree i hxi).2
    rw [haS] at h
    exact Finset.disjoint_singleton_left.mp h
  let f := flatCoord Φ a
  have hf : HolomorphicAt n f x := holomorphicAt_flatCoord Φ a hxD
  have hfH : (vanishingIdeal (n := n) (E.get i)).mem x f :=
    (MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ hAi hxD f).mpr (isInSpanAt_self rfl hf)
  have hfI : I.mem x f := le_restrictOn hcH x f hfH
  let K := N ∩ E.get j
  have hfK : (vanishingIdeal (n := n) K).mem x f := by
    refine ⟨hf, ?_⟩
    filter_upwards [hdiv, HadamardBridge.eventually_mem_of_isCoherent hcI hfI] with y hy hyI hyK
    exact (vanishesToOrderOn_one_iff hyK.1 (hhol y f hyI)).mp
      ((hy hyK.1 hyK.2).2 f hyI)
  have hNflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace S₀) :=
    fun hy hyΦ => hfam none hxN hy hyΦ
  have hKflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ K ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S₀ ∪ {b})) := by
    intro y hy hyΦ
    change (y ∈ N ∧ y ∈ E.get j) ↔ _
    rw [hNflat hy hyΦ, hAj hy hyΦ]
    constructor
    · rintro ⟨hS, hb⟩ r hr
      rcases Finset.mem_union.mp hr with hr | hr
      · exact hS r hr
      · rw [Finset.mem_singleton.mp hr]
        exact hb
    · intro h
      exact ⟨fun r hr => h r (Finset.mem_union_left _ hr),
        h b (Finset.mem_union_right _ (Finset.mem_singleton_self _))⟩
  have haK : a ∉ S₀ ∪ {b} := by simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using And.intro haN hab
  obtain ⟨v, hv⟩ := exists_tangent_free_coordinate_vector Φ hsrc h0 (S₀ ∪ {b}) hKflat a haK
  have hzero := mem_tangentSpaceIn.mp v.property f hfK
  change chartDifferential f x (v : ComplexModel n) = 0 at hzero
  have hone : chartDifferential f x (v : ComplexModel n) = 1 := by
    simpa [f] using hv a
  exact one_ne_zero (hone.symm.trans hzero)

/-- The whole actual old monomial part contains one at every original NC point,
for any retained ordered list of other boundary positions. -/
theorem one_mem_old_monomialPartAlong_at_normalCrossings (hn : 0 < n)
    {N : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hdense : N ⊆ closure (N \ ⋃ H ∈ E, H))
    {x : X} (hxN : x ∈ N) (hNC : normalCrossingsAt (n := n) N E x)
    (i : Fin E.length) (L : List (Fin E.length)) (hL : ∀ j ∈ L, i ≠ j) :
    (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) (E.get i)))
      (L.map E.get)).mem x 1 := by
  apply (one_mem_monomialPartAlong_iff _ _ hxN).mpr
  intro k hxk
  have hget : (L.map E.get).get k = E.get (L.get (Fin.cast (List.length_map _) k)) := by
    simp only [List.get_eq_getElem, List.getElem_map]
    rfl
  rw [hget] at hxk ⊢
  exact divExpAlong_restricted_member_eq_zero_at_normalCrossings hn hN hE hdense hxN hNC
    i _ (hL _ (List.get_mem L _)) hxk

/-- Properness of a genuine old monomial factor forces membership in the
literal original sharp bad locus, without prepared-residual hypotheses. -/
theorem active_old_monomial_subset_originalSharpBadLocus (hn : 0 < n)
    {N : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hdense : N ⊆ closure (N \ ⋃ H ∈ E, H))
    (i : Fin E.length) (L : List (Fin E.length)) (hL : ∀ j ∈ L, i ≠ j) :
    {x | x ∈ N ∧ ¬(monomialPartAlong n N
      (restrictOn n N (vanishingIdeal (n := n) (E.get i))) (L.map E.get)).mem x 1} ⊆
      originalSharpBadLocus (n := n) N E := by
  intro x hx
  exact ⟨hx.1, fun hNC => hx.2
    (one_mem_old_monomialPartAlong_at_normalCrossings hn hN hE hdense hx.1 hNC i L hL)⟩

end

end Hironaka.HironakaG4ActiveMonomialSharpBad
