import Hironaka.Resolution.HironakaSharpActualOrderOneCurveTransverseCoordinates
import Hironaka.Analytic.ThinDimensionDrop

set_option autoImplicit false

/-!
# Order-one singleton sharp geometry in arbitrary carrier dimension

The actual contact-coordinate inverse retains all normal directions of a smooth
carrier. It recognizes the whole singleton sharp bad locus as the genuine
mark-two trace cosupport. Blueprint: `hironaka-g4-order-one-transverse-coordinates.tex`.
The higher-dimensional multiboundary sharp driver remains a separate problem.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4OrderOneTransverseCoordinates

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualOrderOneCurveTransverseCoordinates HironakaSharpOriginalOrderOneTraceGeometry
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpSingleBoundaryTraceCentre HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalMultiBoundaryBadLocus RelativePrincipalizationSpan GermIdealOrder
  TangentDirectionAlong NormalCrossings BlowupFlatCoordinates MonomialPart MonomialPartAlong
  InvertibleIdealQuotient OrderTaylor DivisorExponentAlong MonomialCase BlowupSNCTransform
  MemberPullback GiraudAlong AnalyticDimensionBasics

variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual order-one contact replaces a genuinely tangential coordinate and
retains every normal direction, in arbitrary carrier dimension. -/
theorem actual_order_one_member_simultaneous_coordinates (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H)) {x : X} (hxW : x ∈ W) (hxH : x ∈ H)
    (hOrd : ordinaryTraceOrder W (vanishingIdeal (n := n) H) x = 1) :
    ∃ (S₀ : Finset (Fin n)) (S : Fin [H].length → Finset (Fin n)),
      IsCoordinateFamilyAt n
        (fun t : Option (Fin [H].length) => t.elim W (fun i => [H].get i))
        (fun t => t.elim S₀ S) x ∧
      ∀ i, x ∈ [H].get i → (S i).card = 1 ∧ Disjoint (S i) S₀ := by
  obtain ⟨U,u,_f,_c,hxU,hu,hux,_hf,_hgen,_hc,_hcx,_hcu,hSupp⟩ :=
    exists_actual_order_one_member_ambient_unit_contact hn hW hH hdense hxW hxH hOrd
  obtain ⟨k, _hkn, _hx, Φ, hΦsrc, hΦ0, hflat⟩ := hW.2 x hxW
  change LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) at Φ
  change Φ.source ⊆ (chartAt (ComplexModel n) x).target at hΦsrc
  change Φ.toFun (chartAt (ComplexModel n) x x) = 0 at hΦ0
  change ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
    chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ W ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k) at hflat
  have huhol : ∀ y ∈ U, HolomorphicAt n u y := fun y hy =>
    (show (vanishingIdeal (n := n) H).mem y u from hu.mem y hy).1
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one x hxU hux
  obtain ⟨j,hjk,hjne⟩ := exists_flatPartial_ne_zero hΦsrc hflat
    (mem_flatDomain_self Φ) hxW (huhol x hxU) hξ hne
  obtain ⟨G,hGsub,hGo,hxG⟩ := mem_nhds_iff.mp hSupp
  let O := (U ∩ flatDomain Φ) ∩ G
  have hO : IsOpen O := (hu.isOpen.inter (isOpen_flatDomain Φ)).inter hGo
  have hxO : x ∈ O := ⟨⟨hxU, mem_flatDomain_self Φ⟩, hxG⟩
  have hWs : ∀ y ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (contactCoords Φ j j u) y := by
    intro y hy
    exact contMDiffAt_of_eventually_mdifferentiableAt
      (eventually_of_mem (hO.mem_nhds hy) fun z hz =>
        mdifferentiableAt_contactCoords j j hz.1.2 (huhol z hz.1.1))
  have hWx : contactCoords Φ j j u x = 0 := by
    ext r
    rw [contactCoords_apply]
    split_ifs
    · exact hux
    · simpa [flatMap] using congrArg (fun v : ComplexModel n => v r) hΦ0
  obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_recentred_coords hO hWs hxO
    (injective_fderiv_contactCoords (l := j) hΦsrc (huhol x hxU) hjne)
  let S₀ : Finset (Fin n) := Finset.univ.filter fun r => k ≤ r.val
  let S : Fin [H].length → Finset (Fin n) := fun _ => {j}
  refine ⟨S₀, S, ⟨Θ, hΘsrc, hΘ0, ?_⟩, ?_⟩
  · rintro (_ | i) _hxi y hy hyΘ
    · obtain ⟨hyO,hΘy⟩ := hΘ hy hyΘ
      rw [hWx, sub_zero] at hΘy
      change Θ.toFun (chartAt (ComplexModel n) x y) = contactCoords Φ j j u y at hΘy
      change y ∈ W ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S₀
      rw [hΘy]
      change y ∈ W ↔ contactCoords Φ j j u y ∈
        coordSubspace (Finset.univ.filter fun r : Fin n => k ≤ r.val)
      rw [coordSubspace_eq_complexCoordinatePlane]
      constructor
      · intro hyW r hr
        rw [contactCoords_apply, if_neg (by intro he; subst r; omega),
          Equiv.swap_self, Equiv.refl_apply]
        exact ((hflat hyO.1.2.1 hyO.1.2.2).mp hyW) r hr
      · intro h
        apply (hflat hyO.1.2.1 hyO.1.2.2).mpr
        intro r hr
        have hh := h r hr
        rw [contactCoords_apply, if_neg (by intro he; subst r; omega),
          Equiv.swap_self, Equiv.refl_apply] at hh
        exact hh
    · obtain ⟨hyO,hΘy⟩ := hΘ hy hyΘ
      rw [hWx, sub_zero] at hΘy
      change Θ.toFun (chartAt (ComplexModel n) x y) = contactCoords Φ j j u y at hΘy
      change y ∈ [H].get i ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {j}
      rw [hΘy]
      have hi0 : i = (0 : Fin [H].length) := Fin.eq_zero i
      subst i
      rw [show [H].get (0 : Fin [H].length) = H from rfl]
      change y ∈ H ↔ ∀ r ∈ ({j} : Finset (Fin n)), contactCoords Φ j j u y r = 0
      simp only [Finset.mem_singleton, forall_eq]
      rw [contactCoords_apply, if_pos rfl]
      exact hGsub hyO.2
  · intro i _hi
    refine ⟨Finset.card_singleton j, Finset.disjoint_left.mpr ?_⟩
    intro r hrj hrW
    have he : r = j := Finset.mem_singleton.mp hrj
    subst r
    have hh := (Finset.mem_filter.mp hrW).2
    omega

/-- Genuine pointwise order one gives the actual singleton transversality
predicate, with no fixed dimension assumption on the smooth carrier. -/
theorem actual_singleton_transverse_of_order_one (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H))
    (hOrd : ∀ x ∈ W, x ∈ H → ordinaryTraceOrder W (vanishingIdeal (n := n) H) x = 1) :
    IsTransverse n W [H] := by
  intro x hx
  by_cases hxH : x ∈ H
  · exact actual_order_one_member_simultaneous_coordinates hn hW hH hdense hx hxH (hOrd x hx hxH)
  · obtain ⟨k,hkx⟩ := hW.2 x hx
    refine ⟨Finset.univ.filter (fun r : Fin n => k ≤ r.val), fun _ => ∅,
      isCoordinateFamilyAt_of_regularAtDim hkx [H] (fun _ => ∅) ?_, ?_⟩
    · intro i hi
      exact hxH (by simpa using hi)
    · intro i hi
      exact (hxH (by simpa using hi)).elim

/-- The independently defined pointwise NC predicate is equivalent to true
ordinary trace order one at every incident point, in arbitrary dimension. -/
theorem normalCrossingsAt_singleton_iff_order_one (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H)) {x : X} (hxW : x ∈ W) (hxH : x ∈ H) :
    normalCrossingsAt (n := n) W [H] x ↔
      ordinaryTraceOrder W (vanishingIdeal (n := n) H) x = 1 := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (originalBoundary_isClosedSubmanifold hn hH)
  have hnz : ∀ y ∈ W, IsNonzeroAlongAt W (vanishingIdeal (n := n) H) y :=
    fun _ hy => originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hy
  have hdense' : W ⊆ closure (W \ ⋃ A ∈ [H], A) := by simpa using hdense
  have hpos : 1 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) H) x :=
    (one_le_originalMemberTraceOrder_iff hn hW hH hdense' hxW (0 : Fin [H].length)).mpr hxH
  constructor
  · intro hNC
    have hxGood := (normalCrossingsAt_iff_mem_originalSmoothNCRegion hW.1
      (hH.1 H (by simp)) hxW).mp hNC
    have hnot : ¬2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) H) x := by
      intro htwo
      have hxCos := (ordinaryTraceOrder_cosupport_iff hW hI hnz hxW 2).mpr htwo
      exact Set.disjoint_left.mp
        (originalBoundaryTraceMarked_cosupp_disjoint_goodRegion hn hH hdense) hxCos hxGood
    omega
  · intro hOrd
    obtain ⟨S₀,S,hfam,hfree⟩ :=
      actual_order_one_member_simultaneous_coordinates hn hW hH hdense hxW hxH hOrd
    exact ⟨S₀, S, hfam, fun i hi => (hfree i hi).1⟩

/-- The whole literal singleton sharp bad locus is exactly the genuine
trace-mark-two cosupport, with no caller-provided bad-locus identification. -/
theorem originalSharpBadLocus_singleton_eq_cosupport (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H)) :
    originalSharpBadLocus (n := n) W [H] = cosupport n W (vanishingIdeal (n := n) H) 2 := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (originalBoundary_isClosedSubmanifold hn hH)
  have hnz : ∀ y ∈ W, IsNonzeroAlongAt W (vanishingIdeal (n := n) H) y :=
    fun _ hy => originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hy
  have hdense' : W ⊆ closure (W \ ⋃ A ∈ [H], A) := by simpa using hdense
  ext x
  constructor
  · intro hx
    have hxH : x ∈ H := by
      have hh := (originalSharpBadLocus_subset_boundary hW hx).2
      simpa using hh
    have hpos : 1 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) H) x :=
      (one_le_originalMemberTraceOrder_iff hn hW hH hdense' hx.1 (0 : Fin [H].length)).mpr hxH
    have hne : ordinaryTraceOrder W (vanishingIdeal (n := n) H) x ≠ 1 :=
      fun h => hx.2 ((normalCrossingsAt_singleton_iff_order_one hn hW hH hdense hx.1 hxH).mpr h)
    exact (ordinaryTraceOrder_cosupport_iff hW hI hnz hx.1 2).mpr (by omega)
  · intro hx
    have hxWH := originalBoundaryTraceMarked_cosupp_subset_inter hH hx
    refine ⟨hxWH.1, ?_⟩
    intro hNC
    have hOrd := (normalCrossingsAt_singleton_iff_order_one hn hW hH hdense hxWH.1 hxWH.2).mp hNC
    have htwo := (ordinaryTraceOrder_cosupport_iff hW hI hnz hxWH.1 2).mp hx
    omega

/-- Actual coherent order equations make the entire singleton sharp bad
locus analytic in every smooth carrier dimension. -/
theorem isComplexAnalyticSubset_originalSharpBadLocus_singleton (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H)) :
    IsComplexAnalyticSubset (n := n) (originalSharpBadLocus (n := n) W [H]) := by
  rw [originalSharpBadLocus_singleton_eq_cosupport hn hW hH hdense]
  exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
    (VanishingIdealCoherent.isCoherent_vanishingIdeal
      (originalBoundary_isClosedSubmanifold hn hH)) hW (by omega)

/-- The exact singleton sharp bad locus is thin in the genuine carrier,
so its regular dimensions strictly drop from the actual pure carrier dimension. -/
theorem dimLE_originalSharpBadLocus_singleton (hn : 0 < n)
    {W H : Set X} (hW : IsClosedSubmanifold n W) (hH : IsSNCDivisor n [H])
    (hdense : W ⊆ closure (W \ H)) (q : ℕ)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x q) :
    DimLE (n := n) (originalSharpBadLocus (n := n) W [H]) (q - 1) := by
  have hbad := originalSharpBadLocus_singleton_eq_cosupport hn hW hH hdense
  have hsub : originalSharpBadLocus (n := n) W [H] ⊆ W ∩ H := by
    rw [hbad]
    exact originalBoundaryTraceMarked_cosupp_subset_inter hH
  apply ThinDimensionDrop.dimLE_pred_of_thin
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW)
    (hsub.trans inter_subset_left)
  · intro O hO hOW
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxO,hxW⟩
    obtain ⟨y,hyO,hyW,hyH⟩ := mem_closure_iff.mp (hdense hxW) O hO hxO
    exact hyH (hsub (hOW ⟨hyO,hyW⟩)).2
  · intro x k hx
    exact (RegularPointDimension.eq_of_regularAtDim hx (hreg x hx.2.1)).le

end

end Hironaka.HironakaG4OrderOneTransverseCoordinates
