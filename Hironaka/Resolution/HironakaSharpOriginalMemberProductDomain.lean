/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalMemberProduct

/-! Genuine original product coherence and nonzero restriction at ALL carrier
points, including bad points. Complete mathematics-first blueprint precedes code.
The empty auxiliary boundary is not original-boundary centre admissibility. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalMemberProductDomain
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSharpOriginalMemberProduct NormalCrossings SimultaneousNormalCrossings
  IdealWeightPowers MonomialPart BlowupFlatCoordinates DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers GermIdealOrder
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
theorem isCoherent_idealListProduct (L : List (GermIdeal n M))
    (hL : ∀ I ∈ L, I.IsCoherent) : (idealListProduct L).IsCoherent := by
  induction L with
  | nil => exact isCoherent_unitIdeal
  | cons I L ih =>
    exact isCoherent_mul (hL I (by simp)) (ih fun J hJ => hL J (List.mem_cons_of_mem _ hJ))

theorem isCoherent_originalMemberProduct (hn : 0 < n) {E : List (Set M)}
    (hE : IsSNCDivisor n E) : (originalMemberProduct (n := n) E).IsCoherent := by
  apply isCoherent_idealListProduct
  intro I hI
  obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
  exact VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_get hn hE i)

/-- Ambient SNC and TRUE whole-boundary density construct a real product trace germ,
even at BAD original carrier points where W is not NC with the original E. -/
theorem originalMemberProduct_isNonzeroAlongAt (hn : 0 < n) {W : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {x : M} (hx : x ∈ W) : IsNonzeroAlongAt W (originalMemberProduct (n := n) E) x := by
  classical
  obtain ⟨k,Φ,σ,hsrc,_hW,_hfree,_hinj,hA,hp,hgen,_hres⟩ :=
    exists_actual_original_member_product_normal_form hn hE
      (isTransverse_univ_of_isSNCDivisor hE) (mem_univ x)
  let T : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i
  let p : M → ℂ := fun z => ∏ i ∈ T,flatCoord Φ (σ i) z
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  refine ⟨p,(hgen p).mpr (isInSpanAt_eq_iff.mpr
    ⟨hp,1,holomorphicAt_const 1,Eventually.of_forall fun z => (one_mul (p z)).symm⟩),?_⟩
  apply frequently_iff.mpr
  intro U hU
  have hV : U ∩ flatDomain Φ ∈ 𝓝 x := inter_mem hU ((isOpen_flatDomain Φ).mem_nhds hxD)
  obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp hV
  obtain ⟨z,hzV,hzW,hzE⟩ := mem_closure_iff.mp (hdense hx) V hVo hxV
  refine ⟨z,(hVsub hzV).1,hzW,?_⟩
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi hz0
  have hzH := (hA i (Finset.mem_filter.mp hi).2 (hVsub hzV).2.1 (hVsub hzV).2.2).mpr hz0
  exact hzE (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hzH⟩)

variable {X : CMfd.{u} n}

theorem originalMemberIdeal_isNonzeroAlongAt {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {H : Set X} (hH : H ∈ E) {x : X} (hx : x ∈ W) :
    IsNonzeroAlongAt W (vanishingIdeal (n := n) H) x := by
  have hEH : IsSNCDivisor n [H] := NormalCrossingsComparison.isSNCDivisor_of_sublist hE
    (List.singleton_sublist.mpr hH)
  have hdH : W ⊆ closure (W \ H) := hdense.trans (closure_mono (by
    rintro y ⟨hyW,hyE⟩
    exact ⟨hyW,fun hyH => hyE (mem_iUnion₂.mpr ⟨H,hH,hyH⟩)⟩))
  exact HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hEH hdH hx

/-- The true original product auxiliary input, with the explicit EMPTY auxiliary
boundary; original E centre admissibility still requires its separate geometry. -/
def originalMemberProductMarked (W : Set X) (E : List (Set X)) (q : ℕ) : MarkedIdeal n X :=
  ⟨W,[],originalMemberProduct (n := n) E,q⟩

theorem originalMemberProductMarked_isInvDomain (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d q : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (hq : 1 ≤ q) :
    IsInvDomain n (originalMemberProductMarked W E q) where
  isWellFormed := ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold hW⟩
  dimLE := fun x hx => ⟨d,hd,hreg x hx⟩
  one_le_d := hq
  isNonzeroAlongAt := fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx

theorem isComplexAnalyticSubset_originalMemberProduct_cosupport (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (q : ℕ) : IsComplexAnalyticSubset (n := n) (cosupport n W (originalMemberProduct (n := n) E) q) := by
  have hI := isCoherent_originalMemberProduct hn hE
  cases q with
  | zero =>
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW
  | succ q =>
    exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hI hW (Nat.succ_pos q)

end
end Hironaka.HironakaSharpOriginalMemberProductDomain
