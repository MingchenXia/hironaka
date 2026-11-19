import Hironaka.Analytic.Unibranch.HironakaG10TmSourceLargeOmega

/-!
# Hironaka's boundary at an ARBITRARY stratum index, including index 0 (lane G10TM, G10-03-06.b)

Plan item G10-03-06.b of lane G10RD's re-split (`G10RD/G10-03-03-sum-centre-globalization.md` §5).  The library
chain for one selected stratum (`HironakaG10AnalyticStratumBoundary.stratumBoundary`,
`…LocallyAnalyticBoundary`, `…LocalStratumClosure`, `…LocalBoundaryGlobalCut`, `…SchemeBoundaryThickening`,
`…TrackedBoundaryNextStratum`, `…TrackedBoundaryCSet`, `…TrackedBoundaryCoincidence`,
`…BoundarySupportContainment`, and lane G10TM's `HironakaG10TmSourceLargeOmega`) is written for the positive
stratum `strata f B (i + 1)` (Hironaka's index `i ≥ 1`).  Here every statement is restated for
`strata f B k`, `k` ARBITRARY; the proofs are the library proofs (they never use that the index is a
successor).  For `k = 0`, `strata f B 0 = B` and `stratumBoundaryAt f B V Z 0 = closure ((B ∩ V) \ Z) ∩ Z` is
Hironaka's `E_0` (proof of `II_{n-1} ⇒ I_n`, case `i = 0`, printed p. 544); `k = i + 1` recovers the library
(`stratumBoundary_eq_stratumBoundaryAt`, by `rfl`).  The only change of content: "the boundary lies in the
non-flat image" holds for `k ≥ 1` only, so the admissibility of the centre is read off from
`Cset … k ⊆ nonflatImage f` (G10RD §5).

No named input; no existing statement changed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open Hironaka
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10TmStratumBoundaryAt
open Hironaka HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10LocalBoundaryGlobalCut
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact
  Hironaka.Analytic.Unibranch.HironakaG10FiniteIdealSumCentre
  Hironaka.Analytic.Unibranch.HironakaG10SourceIdentifiedSumCentre
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10SumCentreFlat
  Hironaka.Analytic.Unibranch.HironakaG10SourceFamilySeparation
  Hironaka.Analytic.Unibranch.HironakaG10SourceIdealSeparation
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

open Hironaka HironakaG10HirIdealGerms
  HironakaG10FiniteIdealFamilyArithmetic HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
  Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCoincidence
  Hironaka.Analytic.Unibranch.HironakaG10BoundarySupportContainment
  Hironaka.Analytic.Unibranch.HironakaG10LargeOmegaAgreement
  Hironaka.Analytic.Unibranch.HironakaG10UniformRadicalPower
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus


open Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact Hironaka.Analytic.Unibranch.HironakaG10TmUniformColon

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10LocalSupportAnalytic
  Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryNextStratum
  Hironaka.Analytic.Unibranch.HironakaG10BoundaryGermCoincidence
  Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity
  Hironaka.Analytic.Unibranch.HironakaG10TmUniformColon
open Hironaka.ClosureDifferenceAnalytic
  Hironaka.HironakaG10GlobalSumIdealModule

noncomputable section

/-! ### The boundary at stratum `k` -/

/-- Hironaka's boundary of the stratum of index `k` (any `k`, including `0`) against a set `Z`. -/
def stratumBoundaryAt {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B W Z : Set X.obj.left) (k : ℕ) : Set X.obj.left :=
  closure ((strata f B k ∩ W) \ Z) ∩ Z

theorem stratumBoundary_eq_stratumBoundaryAt {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B W Z : Set X.obj.left) (i : ℕ) :
    stratumBoundary f B W Z i = stratumBoundaryAt f B W Z (i + 1) :=
  rfl

/-- At index `0` the boundary is `closure ((B ∩ W) \ Z) ∩ Z` (Hironaka's `E_0`). -/
theorem stratumBoundaryAt_zero {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B W Z : Set X.obj.left) :
    stratumBoundaryAt f B W Z 0 = closure ((B ∩ W) \ Z) ∩ Z :=
  rfl

/-! ### Local analyticity and the global cut -/

theorem locallyAnalytic_stratumBoundaryAt
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (B : Set X.obj.left)
    (Z : LocalFlattener f) (k : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B k)) (x : X.obj.left) (hx : x ∈ Z.V) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧ range e.toPoint ⊆ Z.V ∧
      ∃ A : Set e.ambient, IsComplexAnalyticSubset (n := e.dim) A ∧
        e.toPoint ⁻¹' stratumBoundaryAt f B Z.V Z.support k = Subtype.val ⁻¹' A := by
  obtain ⟨e,he,heV,A,hA,htrace⟩ := local_support_analytic Z x hx
  let SA : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' strata f B k)
  let SZ : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' Z.support)
  have hSA : IsComplexAnalyticSubset (n := e.dim) SA := analytic_image_local_trace hS e heV
  have hSZ : IsComplexAnalyticSubset (n := e.dim) SZ := by
    dsimp [SZ]
    rw [htrace, Set.image_preimage_eq_inter_range, Subtype.range_coe]
    exact hA.inter e.analytic
  refine ⟨e,he,heV,closure (SA \ SZ) ∩ SZ,
    (isComplexAnalyticSubset_closure_diff hSA hSZ).inter hSZ, ?_⟩
  have heW : e.toPoint ⁻¹' Z.V = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    exact heV ⟨z,rfl⟩
  have hdiff : e.toPoint ⁻¹' ((strata f B k ∩ Z.V) \ Z.support) =
      (e.toPoint ⁻¹' strata f B k) \ (e.toPoint ⁻¹' Z.support) := by
    rw [Set.preimage_sdiff, Set.preimage_inter, heW, Set.inter_univ]
  change e.toPoint ⁻¹' (closure ((strata f B k ∩ Z.V) \ Z.support) ∩ Z.support) = _
  rw [Set.preimage_inter, e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
    e.isOpenEmbedding_toPoint.continuous, hdiff,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Set.image_sdiff Subtype.val_injective]
  dsimp [SA, SZ]
  rw [Set.preimage_image_eq _ Subtype.val_injective]

theorem locallyAnalytic_stratumClosureAt
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (B : Set X.obj.left)
    (Z : LocalFlattener f) (k : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B k)) (x : X.obj.left) (hx : x ∈ Z.V) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧ range e.toPoint ⊆ Z.V ∧
      ∃ A : Set e.ambient, IsComplexAnalyticSubset (n := e.dim) A ∧
        e.toPoint ⁻¹' closure ((strata f B k ∩ Z.V) \ Z.support) = Subtype.val ⁻¹' A := by
  obtain ⟨e,he,heV,A,hA,htrace⟩ := local_support_analytic Z x hx
  let SA : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' strata f B k)
  let SZ : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' Z.support)
  have hSA : IsComplexAnalyticSubset (n := e.dim) SA := analytic_image_local_trace hS e heV
  have hSZ : IsComplexAnalyticSubset (n := e.dim) SZ := by
    dsimp [SZ]
    rw [htrace, Set.image_preimage_eq_inter_range, Subtype.range_coe]
    exact hA.inter e.analytic
  refine ⟨e,he,heV,closure (SA \ SZ),
    isComplexAnalyticSubset_closure_diff hSA hSZ, ?_⟩
  have heW : e.toPoint ⁻¹' Z.V = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    exact heV ⟨z,rfl⟩
  have hdiff : e.toPoint ⁻¹' ((strata f B k ∩ Z.V) \ Z.support) =
      (e.toPoint ⁻¹' strata f B k) \ (e.toPoint ⁻¹' Z.support) := by
    rw [Set.preimage_sdiff, Set.preimage_inter, heW, Set.inter_univ]
  change e.toPoint ⁻¹' closure ((strata f B k ∩ Z.V) \ Z.support) = _
  rw [e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
    e.isOpenEmbedding_toPoint.continuous, hdiff,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Set.image_sdiff Subtype.val_injective]

theorem analytic_global_cutAt {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B C : Set X.obj.left) (Z : LocalFlattener f) (k : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B k))
    (hC : IsLocallyAnalyticOn X Z.V C) (hCclosed : IsClosed C) (hCV : C ⊆ Z.V) :
    X.IsAnalyticSubset (C ∩ stratumBoundaryAt f B Z.V Z.support k) := by
  intro x
  by_cases hxC : x ∈ C
  · obtain ⟨e,he,heV,A,hA,htrace⟩ := locallyAnalytic_stratumBoundaryAt f B Z k hS x (hCV hxC)
    let AC : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' C)
    have hAC : IsComplexAnalyticSubset (n := e.dim) AC := analytic_image_local_trace hC e heV
    refine ⟨e,he,AC ∩ A,hAC.inter hA,?_⟩
    rw [Set.preimage_inter, htrace, Set.preimage_inter]
    dsimp [AC]
    rw [Set.preimage_image_eq _ Subtype.val_injective]
  · obtain ⟨e,he,heC,_⟩ := LocalEmbedding.exists_domain x hCclosed.isOpen_compl hxC
    refine ⟨e,he,∅,isComplexAnalyticSubset_empty,?_⟩
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => (heC ⟨y,rfl⟩) h.1

/-! ### The global thickening -/

theorem closure_locallyAnalyticAt {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) (Z : LocalFlattener f) (k : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B k)) :
    IsLocallyAnalyticOn X Z.V (closure ((strata f B k ∩ Z.V) \ Z.support)) := by
  intro x hx
  obtain ⟨e,he,_,A,hA,htrace⟩ := locallyAnalytic_stratumClosureAt f B Z k hS x hx
  exact ⟨e,he,A,hA,htrace⟩

theorem exists_scheme_boundary_thickeningAt {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B C : Set X.obj.left)
    (Z : LocalFlattener f) (k ω : ℕ) (hω : ω ≠ 0)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B k))
    (hC : IsLocallyAnalyticOn X Z.V C) (hCclosed : IsClosed C) (hCV : C ⊆ Z.V) :
    let G := closure ((strata f B k ∩ Z.V) \ Z.support)
    let E := stratumBoundaryAt f B Z.V Z.support k
    let Q := C ∩ E
    ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
      (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
      D.IsFiniteType ∧ nonunitLocus D d = Q ∧
      (∀ x ∈ Z.V, LinearMap.range
        (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x)) ∧
      (∀ x ∉ Q, LinearMap.range
        (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) = ⊤) := by
  let G := closure ((strata f B k ∩ Z.V) \ Z.support)
  let E := stratumBoundaryAt f B Z.V Z.support k
  let Q := C ∩ E
  let IC := intrinsicCentreStalkRange X.obj.left C
  let IG := intrinsicCentreStalkRange X.obj.left G
  let IE := fun x => IG x ⊔ Z.H x
  have hG : IsLocallyAnalyticOn X Z.V G := closure_locallyAnalyticAt f B Z k hS
  have hIC : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IC :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Z.V C hC
  have hIG : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IG :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Z.V G hG
  have hIE : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IE :=
    isLocallyFinitelyGeneratedOn_sup Z.V IG Z.H hIG Z.fg
  have hQ : X.IsAnalyticSubset Q := analytic_global_cutAt f B C Z k hS hC hCclosed hCV
  have hQV : Q ⊆ Z.V := fun _ hx => hCV hx.1
  have htop : ∀ x ∈ Z.V, x ∉ Q → IC x ^ ω ⊔ IE x = ⊤ := by
    intro x hxV hxQ
    change (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
      (intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x) = ⊤
    by_cases hxC : x ∈ C
    · by_cases hxG : x ∈ G
      · have hxH : Z.H x = ⊤ := by
          by_contra hH
          exact hxQ ⟨hxC,hxG,⟨hxV,hH⟩⟩
        rw [hxH, sup_top_eq, sup_top_eq]
      · rw [intrinsicCentreStalkRange_eq_top_of_not_mem X Z.V G Z.isOpen hG x hxV hxG,
          top_sup_eq, sup_top_eq]
    · rw [intrinsicCentreStalkRange_eq_top_of_not_mem X Z.V C Z.isOpen hC x hxV hxC,
        Ideal.top_pow, top_sup_eq]
  obtain ⟨D,d,hfinite,hstalk,houtside⟩ := exists_global_sum_ideal_module
    X.obj.left Z.V Q Z.isOpen hQ.isClosed hQV IC IE hIC hIE ω htop
  have hDQ : nonunitLocus D d ⊆ Q := by
    intro x hx
    by_contra hxQ
    exact hx (houtside x hxQ)
  have hQD : Q ⊆ nonunitLocus D d := by
    intro x hxQ hunit
    have hle : IC x ^ ω ⊔ IE x ≤ IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x) :=
      sup_le ((Ideal.pow_le_self hω).trans (intrinsicCentreStalkRange_le_maximalIdeal _ _ _ hxQ.1))
        (sup_le (intrinsicCentreStalkRange_le_maximalIdeal _ _ _ hxQ.2.1)
          (IsLocalRing.le_maximalIdeal hxQ.2.2.2))
    rw [← hstalk x (hQV hxQ), hunit] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk x)).ne_top
      (top_le_iff.mp hle)
  exact ⟨D,d,hfinite,Set.Subset.antisymm hDQ hQD,hstalk,houtside⟩

/-! ### Tracked boundaries -/

theorem tracked_boundary_subset_next_stratumAt {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) (Z : LocalFlattener f) (k : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B k)) :
    stratumBoundaryAt f B Z.V Z.support k ⊆ strata f B (k + 1) := by
  intro x hx
  have hxZ : x ∈ Z.support := hx.2
  have hxS : x ∈ strata f B k :=
    mem_of_mem_closure_inter_domain Z.isOpen hS hxZ.1
      (closure_mono (show (strata f B k ∩ Z.V) \ Z.support ⊆
        strata f B k ∩ Z.V from sdiff_subset) hx.1)
  change x ∈ strata f B k ∧ ¬ FlatOverAt f x
    (vanishingIdealAt X.obj.left (strata f B k) x)
  refine ⟨hxS, ?_⟩
  intro hflat
  let IS := intrinsicCentreStalkRange X.obj.left (strata f B k)
  have hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Z.V _ hS
  have hle : Z.H x ≤ IS x := by
    apply (Z.flattener x hxZ.1 hxZ.2 (IS x)).1
    change FlatOverAt f x (intrinsicCentreStalkRange X.obj.left (strata f B k) x)
    rw [← vanishingIdealAt_eq_intrinsicCentreStalkRange]
    exact hflat
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Z.V ∧ Z.H y ≤ IS y := by
    filter_upwards [Z.isOpen.mem_nhds hxZ.1,
      eventually_le_of_le Z.fg hIS Z.isOpen Z.isOpen hxZ.1 hxZ.1 hle] with y hyV hy
    exact ⟨hyV,hy⟩
  obtain ⟨y,hy,hyS,hyNot⟩ := (mem_closure_iff_nhds.mp hx.1) _ hnear
  have hISproper : IS y ≠ ⊤ := by
    intro htop
    have hmax := intrinsicCentreStalkRange_le_maximalIdeal X.obj.left (strata f B k) y hyS.1
    change IS y ≤ IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk y) at hmax
    rw [htop] at hmax
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk y)).ne_top
      (top_le_iff.mp hmax)
  have hZproper : Z.H y ≠ ⊤ := fun htop => hISproper (top_le_iff.mp (htop ▸ hy.2))
  exact hyNot ⟨hy.1,hZproper⟩

theorem tracked_boundary_subset_csetAt {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → LocalFlattener f) (k : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B k))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j →
      ∃ C, IsStratumComponent f B j C ∧ x ∈ C) :
    ∀ p, stratumBoundaryAt f B (Z p).V (Z p).support k ⊆
      Cset f B (fun p => (Z p).support) k := by
  intro p x hx
  have hxnext := tracked_boundary_subset_next_stratumAt f B (Z p) k (hS p) hx
  obtain ⟨j,hj,hxj,hxnext'⟩ := exists_last_stratum f B N hN (k + 1) hxnext
  obtain ⟨C,hC,hxC⟩ := hcover j x hxj
  have hji : k < j := lt_of_lt_of_le (Nat.lt_succ_self k) hj
  have hselected : (j,C) ∈ selectedHigherComponents f B (fun p => (Z p).support) k :=
    ⟨hji,hC,p,⟨x,⟨hxC,hxnext'⟩,hx.2⟩⟩
  exact Set.mem_iUnion.mpr ⟨(j,C),Set.mem_iUnion.mpr ⟨hselected,hxC⟩⟩

theorem tracked_boundary_scheme_agreesAt {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → LocalFlattener f)
    (Zaux : LocalFlattener f) (k : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B k))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hC : Cset f B (fun p => (Z p).support) k ⊆ Zaux.support) :
    ∀ p x, x ∈ stratumBoundaryAt f B (Z p).V (Z p).support k →
      ∀ᶠ y in 𝓝 x,
        intrinsicCentreStalkRange X.obj.left
          (closure ((strata f B k ∩ Zaux.V) \ Zaux.support)) y ⊔ Zaux.H y =
        intrinsicCentreStalkRange X.obj.left
          (closure ((strata f B k ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y := by
  intro p x hx
  have hxC := tracked_boundary_subset_csetAt f B Z k hS N hN hcover p hx
  exact eventually_scheme_boundary_eq f Zaux (Z p) (strata f B k) (hC hxC) hx.2

theorem schemeBoundary_nonunit_iffAt {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) (Z : LocalFlattener f) (k : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B k))
    (x : X.obj.left) (hxV : x ∈ Z.V) :
    (intrinsicCentreStalkRange X.obj.left
      (closure ((strata f B k ∩ Z.V) \ Z.support)) x ⊔ Z.H x) ≠ ⊤ ↔
      x ∈ stratumBoundaryAt f B Z.V Z.support k := by
  let G := closure ((strata f B k ∩ Z.V) \ Z.support)
  have hG : IsLocallyAnalyticOn X Z.V G := closure_locallyAnalyticAt f B Z k hS
  change intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x ≠ ⊤ ↔ x ∈ G ∧ x ∈ Z.support
  constructor
  · intro h
    have hxG : x ∈ G := by
      by_contra hn
      have ht := intrinsicCentreStalkRange_eq_top_of_not_mem X Z.V G Z.isOpen hG x hxV hn
      exact h (by rw [ht, top_sup_eq])
    have hxH : Z.H x ≠ ⊤ := fun ht => h (by rw [ht, sup_top_eq])
    exact ⟨hxG,hxV,hxH⟩
  · rintro ⟨hxG,hxV',hxH⟩ htop
    have hle : intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x ≤
        IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x) :=
      sup_le (intrinsicCentreStalkRange_le_maximalIdeal _ _ _ hxG)
        (IsLocalRing.le_maximalIdeal hxH)
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk x)).ne_top
      (top_le_iff.mp hle)

theorem eventually_auxBoundary_support_subset_csetAt {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → LocalFlattener f)
    (Zaux : LocalFlattener f) (k : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B k))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hC : Cset f B (fun p => (Z p).support) k ⊆ Zaux.support)
    (p : Fin q) (x : X.obj.left) (hx : x ∈ stratumBoundaryAt f B (Z p).V (Z p).support k) :
    ∀ᶠ y in 𝓝 x,
      (intrinsicCentreStalkRange X.obj.left
        (closure ((strata f B k ∩ Zaux.V) \ Zaux.support)) y ⊔ Zaux.H y) ≠ ⊤ →
        y ∈ Cset f B (fun p => (Z p).support) k := by
  have hEq := tracked_boundary_scheme_agreesAt f B Z Zaux k hS N hN hcover hC p x hx
  have hV := (Z p).isOpen.mem_nhds hx.2.1
  filter_upwards [hEq,hV] with y hyEq hyV hyNonunit
  have hyNonunit' : (intrinsicCentreStalkRange X.obj.left
      (closure ((strata f B k ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y) ≠ ⊤ := by
    rw [← hyEq]
    exact hyNonunit
  have hyE := (schemeBoundary_nonunit_iffAt f B (Z p) k (hS p) y hyV).mp hyNonunit'
  exact tracked_boundary_subset_csetAt f B Z k hS N hN hcover p hyE

/-! ### Large-`ω` sum centres at stratum `k` -/

/-- `exists_source_large_omega_exact'` at an arbitrary stratum index `k` (index `0` included). -/
theorem exists_source_large_omega_exactAt {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → LocalFlattener f) (Zaux : LocalFlattener f) (k : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B k))
    (hSaux : IsLocallyAnalyticOn X Zaux.V (strata f B k))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents f B (fun p => (Z p).support) k).Finite)
    (hmax : ∀ jC ∈ badComponents f B (fun p => (Z p).support), jC.1 ≤ k)
    (hC : Cset f B (fun p => (Z p).support) k ⊆ Zaux.support) :
    let C := Cset f B (fun p => (Z p).support) k
    ∃ ω₀ : ℕ, ∀ ω ≥ ω₀, ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        D.IsFiniteType ∧ nonunitLocus D d = C ∩ stratumBoundaryAt f B Zaux.V Zaux.support k ∧
        (∀ x ∈ Zaux.V, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B k ∩ Zaux.V) \ Zaux.support)) x ⊔ Zaux.H x)) ∧
        ∀ p x, x ∈ stratumBoundaryAt f B (Z p).V (Z p).support k →
          ∀ᶠ y in 𝓝 x, LinearMap.range
            (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d y) =
              intrinsicCentreStalkRange X.obj.left
                (closure ((strata f B k ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y := by
  let C := Cset f B (fun p => (Z p).support) k
  let G := closure ((strata f B k ∩ Zaux.V) \ Zaux.support)
  let IE := fun x => intrinsicCentreStalkRange X.obj.left G x ⊔ Zaux.H x
  obtain ⟨hCa, hCc, _, _⟩ := Cset_closed_relOpen_and_nonflat f B (fun p => (Z p).support)
    k hfinite hmax
  have hCV : C ⊆ Zaux.V := fun x hx => (hC hx).1
  have hG : IsLocallyAnalyticOn X Zaux.V G := closure_locallyAnalyticAt f B Zaux k hSaux
  have hIE : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IE :=
    isLocallyFinitelyGeneratedOn_sup Zaux.V _ _
      (local_intrinsicCentreStalkRange_finitelyGenerated X Zaux.V G hG) Zaux.fg
  let IC := intrinsicCentreStalkRange X.obj.left C
  have hClocal : IsLocallyAnalyticOn X Zaux.V C := locallyAnalytic_of_analytic hCa Zaux.V
  have hIC : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IC :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Zaux.V C hClocal
  obtain ⟨ω₁, hω₁⟩ := exists_uniform_colon_power Zaux.V Zaux.isOpen IC IE hIC hIE C
    hCc.isCompact hCV
  refine ⟨max ω₁ 1, fun ω hω => ?_⟩
  have hω0 : ω ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right ω₁ 1).trans hω))
  obtain ⟨D, d, hfin, hQ, hsource, _⟩ :=
    exists_scheme_boundary_thickeningAt f B C Zaux k ω hω0 hSaux hClocal hCc hCV
  refine ⟨D, d, hfin, hQ, hsource, fun p x hxE => ?_⟩
  have hxC : x ∈ C := tracked_boundary_subset_csetAt f B Z k hS N hN hcover p hxE
  have hxV : x ∈ Zaux.V := hCV hxC
  have hrad : IC x ≤ (IE x).radical :=
    Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz.intrinsicCentre_le_radical_of_support_subset
      Zaux.V C Zaux.isOpen IE hIE x hxV
      (eventually_auxBoundary_support_subset_csetAt f B Z Zaux k hS N hN hcover hC p x hxE)
  have hfgx : (IC x).FG := by
    obtain ⟨O, hxO, r, s, hs⟩ := hIC x hxV
    rw [hs x hxO hxV]
    exact Submodule.fg_span (Set.finite_range _)
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfgx
  have hev : ∀ᶠ z in 𝓝 x, IC z ^ m ≤ IE z :=
    eventually_le_of_le (isLocallyFinitelyGeneratedOn_pow Zaux.V IC hIC m) hIE
      Zaux.isOpen Zaux.isOpen hxV hxV hm
  have hpow := hω₁ x hxC ⟨m, hev⟩ ω ((le_max_left ω₁ 1).trans hω)
  have hEq := tracked_boundary_scheme_agreesAt f B Z Zaux k hS N hN hcover hC p x hxE
  filter_upwards [hpow, hEq, Zaux.isOpen.mem_nhds hxV] with y hy hyEq hyV
  rw [hsource y hyV]
  exact (sup_eq_right.mpr hy).trans hyEq

/-- **Admissible centre-flat sum centres with the tracked-boundary formula at every tracked boundary
point** (lane G10RD's `exists_source_large_omega_sumCentreAt`, G10-03-06.a): the library theorem
`exists_source_large_omega_sumCentre` without the compact set `K`. -/
theorem exists_source_large_omega_sumCentreAt {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → LocalFlattener f) (Zaux : LocalFlattener f) (k : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B k))
    (hSaux : IsLocallyAnalyticOn X Zaux.V (strata f B k))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents f B (fun p => (Z p).support) k).Finite)
    (hmax : ∀ jC ∈ badComponents f B (fun p => (Z p).support), jC.1 ≤ k)
    (hC : Cset f B (fun p => (Z p).support) k ⊆ Zaux.support)
    (hdense : Dense (nonflatImage f)ᶜ) :
    let C := Cset f B (fun p => (Z p).support) k
    let Q := C ∩ stratumBoundaryAt f B Zaux.V Zaux.support k
    ∃ ω₀ : ℕ, ∀ ω ≥ ω₀, ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        D.IsFiniteType ∧ nonunitLocus D d = Q ∧
        (∀ x ∈ Zaux.V, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B k ∩ Zaux.V) \ Zaux.support)) x ⊔ Zaux.H x)) ∧
        ∃ α : ℕ, ∀ β : ℕ, α ≤ β → ∃ c : AdmissibleCentre f,
          nonunitLocus c.B c.b = Q ∧ IsSumCentreFor c.B c.b f β ∧
          (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt f x
            (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b x))) ∧
          (β ≠ 0 → letI : c.B.IsFiniteType := c.finiteType
            ∀ x' : (OriginalFiniteIdealBlowup.sourceObject c.B c.b c.dense).obj.left,
            (stepProj c.B c.b c.dense).hom.left.base x' ∈ Zaux.V →
            ¬ (OnStrictTransform (stepProj c.B c.b c.dense) x'
                (wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x'))
                ((wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x')) ^ β ⊔
                  Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x')) ∧
              OnStrictTransform (stepProj c.B c.b c.dense) x'
                (Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x'))
                ((wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x')) ^ β ⊔
                  Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x')))) ∧
          ∀ p x, x ∈ stratumBoundaryAt f B (Z p).V (Z p).support k →
            ∀ᶠ y in 𝓝 x, LinearMap.range
              (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b y) =
                (intrinsicCentreStalkRange X.obj.left
                  (closure ((strata f B k ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y) ^ β ⊔
                    (Z p).H y := by
  let C := Cset f B (fun p => (Z p).support) k
  let Q := C ∩ stratumBoundaryAt f B Zaux.V Zaux.support k
  obtain ⟨hCa, hCc, _, hCnf⟩ := Cset_closed_relOpen_and_nonflat f B (fun p => (Z p).support)
    k hfinite hmax
  have hClocal : IsLocallyAnalyticOn X Zaux.V C := locallyAnalytic_of_analytic hCa Zaux.V
  have hCV : C ⊆ Zaux.V := fun x hx => (hC hx).1
  have hCdense : Dense Cᶜ := hdense.mono (Set.compl_subset_compl.mpr hCnf)
  have hQZ : Q ⊆ Zaux.support := fun _ hx => hx.2.2
  have hQcompact : IsCompact Q :=
    (analytic_global_cutAt f B C Zaux k hSaux hClocal hCc hCV).isClosed.isCompact
  have hQnonflat : Q ⊆ nonflatImage f := fun x hx => hCnf hx.1
  have hQdense : Dense Qᶜ := hCdense.mono (Set.compl_subset_compl.mpr inter_subset_left)
  obtain ⟨ω₀, hω⟩ := exists_source_large_omega_exactAt
    f B Z Zaux k hS hSaux N hN hcover hfinite hmax hC
  refine ⟨ω₀, fun ω hω₀ => ?_⟩
  obtain ⟨D, d, hDfin, hDQ, hDsource, hDtracked⟩ := hω ω hω₀
  let : D.IsFiniteType := hDfin
  let IS := wholeIdealFamily D d
  have hIS : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IS :=
    locallyFinite_wholeIdealFamily D d Zaux.V
  have hQIS : {x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤} = Q := by
    ext x
    constructor
    · intro hx
      have hxD : x ∈ nonunitLocus D d := hx.2
      rw [hDQ] at hxD
      exact hxD
    · intro hx
      have hxD : x ∈ nonunitLocus D d := by rw [hDQ]; exact hx
      exact ⟨hQZ hx, hxD⟩
  have hcompact : IsCompact {x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤} :=
    hQIS.symm ▸ hQcompact
  have hdense' : Dense {x : X.obj.left | ¬ (x ∈ Zaux.support ∧ IS x ≠ ⊤)} := by
    change Dense ({x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤}ᶜ)
    rw [hQIS]
    exact hQdense
  obtain ⟨α, hα⟩ := exists_sourceIdentified_sumCentre f Zaux IS hIS hcompact hdense'
  refine ⟨D, d, hDfin, hDQ, hDsource, α, fun β hαβ => ?_⟩
  obtain ⟨T, t, htfinite, htQ, htdense, htsum, htsource⟩ := hα β hαβ
  let c : AdmissibleCentre f := ⟨T, t, htfinite, htdense, by rw [htQ, hQIS]; exact hQnonflat⟩
  let : T.IsFiniteType := htfinite
  refine ⟨c, htQ.trans hQIS, htsum, flatOver_sumCentre f c.B c.b β htsum, ?_, ?_⟩
  · intro hβ x' hx'
    exact source_families_separated_unpowered f Zaux IS β hβ T t htdense htsource x' hx'
  intro p x hxE
  have hxC := tracked_boundary_subset_csetAt f B Z k hS N hN hcover p hxE
  have hxAux : x ∈ Zaux.support := hC hxC
  have hH := Zaux.eventually_eq (Z p) hxAux hxE.2
  have hD := hDtracked p x hxE
  filter_upwards [Zaux.isOpen.mem_nhds hxAux.1, hH, hD] with y hyV hyH hyD
  change LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf T t y) = _
  change IS y = _ at hyD
  rw [htsource y hyV, hyD, hyH]

end
end Hironaka.Analytic.Unibranch.HironakaG10TmStratumBoundaryAt
