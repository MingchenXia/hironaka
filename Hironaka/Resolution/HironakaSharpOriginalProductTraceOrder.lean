/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.SharpGeometryExact
import Hironaka.Resolution.HironakaSharpOriginalMemberProductDomain

/-! True original ordinary trace-order dictionary, real factor USC and
restricted product additivity. Complete mathematics-first blueprint precedes code.
No constant-order or original-boundary centre certificate is a premise. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalProductTraceOrder
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan MonomialPartAlong RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers GermIdealOrder
  NonmonomialOrderLocal DivisorExponentAlong IdealWeightPowers
  OrderTaylor GermOrderProduct MonomialCase MemberPullback BlowupFlatCoordinates SimultaneousNormalCrossings
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}

/-- The literal empty-boundary nonmonomial colon is the actual restricted extension. -/
theorem nonmonomialPartAlong_nil_eq_restrictOn (W : Set X) (I : GermIdeal n X) :
    nonmonomialPartAlong n W I [] = restrictOn n W I := by
  ext x g
  constructor
  · rintro ⟨_hg,hcolon⟩
    have h1 := hcolon (fun _ => 1) ⟨holomorphicAt_const 1,fun i => i.elim0⟩
    simpa only [one_mul] using h1
  · intro hg
    exact ⟨hg.1,fun a ha => restrictOn_mul_left ha.1 hg⟩

/-- The actual ordinary marked input, independently of any order or centre witness. -/
def ordinaryTraceMarked (W : Set X) (I : GermIdeal n X) : MarkedIdeal n X := ⟨W,[],I,1⟩

def ordinaryTraceOrder (W : Set X) (I : GermIdeal n X) (x : X) : ℕ := nmOrd (ordinaryTraceMarked W I) x

theorem ordGe_ordinaryTraceMarked_eq_cosupport (W : Set X) (I : GermIdeal n X)
    (hI : I.IsCoherent) (q : ℕ) : ordGe (ordinaryTraceMarked W I) q = cosupport n W I q := by
  change cosupport n W (nonmonomialPartAlong n W I []) q = _
  rw [nonmonomialPartAlong_nil_eq_restrictOn]
  exact Subset.antisymm
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hI) q)
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe restrictLe_restrictOn q)

theorem ordinaryTraceMarked_isWellFormed {W : Set X} {I : GermIdeal n X}
    (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent) : (ordinaryTraceMarked W I).IsWellFormed :=
  ⟨hW,hI,NormalCrossings.isSNCDivisor_nil,NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hW⟩

theorem ordinaryTraceOrder_cosupport_iff {W : Set X} {I : GermIdeal n X}
    (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent)
    (hne : ∀ y ∈ W,IsNonzeroAlongAt W I y) {x : X} (hx : x ∈ W) (q : ℕ) :
    x ∈ cosupport n W I q ↔ q ≤ ordinaryTraceOrder W I x := by
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport W I hI q]
  exact mem_ordGe_iff (ordinaryTraceMarked_isWellFormed hW hI) hne hx q

theorem exists_notMem_ordinaryTrace_cosupport {W : Set X} {I : GermIdeal n X}
    (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent)
    (hne : ∀ y ∈ W,IsNonzeroAlongAt W I y) {x : X} (hx : x ∈ W) :
    ∃ q, x ∉ cosupport n W I (q+1) := by
  obtain ⟨q,hq⟩ := exists_notMem_ordGe (ordinaryTraceMarked_isWellFormed hW hI) hne hx
  exact ⟨q,by rwa [ordGe_ordinaryTraceMarked_eq_cosupport W I hI] at hq⟩

theorem eventually_ordinaryTraceOrder_le (hn : 0 < n) {W : Set X} {I : GermIdeal n X}
    (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent)
    (hne : ∀ y ∈ W,IsNonzeroAlongAt W I y) {x : X} (hx : x ∈ W) :
    ∀ᶠ y in 𝓝 x,ordinaryTraceOrder W I y ≤ ordinaryTraceOrder W I x :=
  eventually_nmOrd_le hn (ordinaryTraceMarked_isWellFormed hW hI) hne hx

theorem eventually_originalMemberTraceOrder_le (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {x : X} (hx : x ∈ W) (i : Fin E.length) :
    ∀ᶠ y in 𝓝 x, ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) y ≤
      ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hE i)
  exact eventually_ordinaryTraceOrder_le hn hW hI
    (fun _ hy => originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hy) hx

theorem eventually_originalProductTraceOrder_le (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {x : X} (hx : x ∈ W) :
    ∀ᶠ y in 𝓝 x, ordinaryTraceOrder W (originalMemberProduct (n := n) E) y ≤
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) x :=
  eventually_ordinaryTraceOrder_le hn hW (isCoherent_originalMemberProduct hn hE)
    (fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy) hx

theorem cosupport_principal_iff_vanishes {W : Set X} {I : GermIdeal n X}
    {f : X → ℂ} {x : X} (hx : x ∈ W) (hf : HolomorphicAt n f x)
    (hI : ∀ g, I.mem x g ↔ IsInSpanAt (n := n) (· = f) x g) (q : ℕ) :
    x ∈ cosupport n W I q ↔ VanishesToOrderOn n W x q f := by
  constructor
  · intro hq
    exact hq.2 f ((hI f).mpr (isInSpanAt_eq_iff.mpr
      ⟨hf,1,holomorphicAt_const 1,Eventually.of_forall fun z => (one_mul (f z)).symm⟩))
  · intro hq
    refine ⟨hx,fun g hg => ?_⟩
    obtain ⟨_hg,c,hc,hgc⟩ := isInSpanAt_eq_iff.mp ((hI g).mp hg)
    obtain ⟨a,ha,hca⟩ := hq.mul_left hc
    refine ⟨a,ha,?_⟩
    filter_upwards [hgc,hca] with z hz hza hzW
    rw [hz]
    exact hza hzW

/-- Two true principal factor dictionaries and actual carrier geometry construct
real restricted order additivity; no product-order equality is a premise. -/
theorem ordinaryTraceOrder_mul_of_principal {W : Set X} {I J : GermIdeal n X}
    (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hneI : ∀ y ∈ W,IsNonzeroAlongAt W I y) (hneJ : ∀ y ∈ W,IsNonzeroAlongAt W J y)
    {x : X} (hx : x ∈ W) {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hIf : ∀ a, I.mem x a ↔ IsInSpanAt (n := n) (· = f) x a)
    (hJg : ∀ a, J.mem x a ↔ IsInSpanAt (n := n) (· = g) x a) :
    ordinaryTraceOrder W (I.mul J) x = ordinaryTraceOrder W I x + ordinaryTraceOrder W J x := by
  let a := ordinaryTraceOrder W I x
  let b := ordinaryTraceOrder W J x
  have hfa : VanishesToOrderOn n W x a f :=
    (cosupport_principal_iff_vanishes hx hf hIf a).mp
      ((ordinaryTraceOrder_cosupport_iff hW hI hneI hx a).mpr le_rfl)
  have hgb : VanishesToOrderOn n W x b g :=
    (cosupport_principal_iff_vanishes hx hg hJg b).mp
      ((ordinaryTraceOrder_cosupport_iff hW hJ hneJ hx b).mpr le_rfl)
  have hnfa : ¬ VanishesToOrderOn n W x (a+1) f := by
    intro h
    exact Nat.not_succ_le_self a ((ordinaryTraceOrder_cosupport_iff hW hI hneI hx (a+1)).mp
      ((cosupport_principal_iff_vanishes hx hf hIf (a+1)).mpr h))
  have hngb : ¬ VanishesToOrderOn n W x (b+1) g := by
    intro h
    exact Nat.not_succ_le_self b ((ordinaryTraceOrder_cosupport_iff hW hJ hneJ hx (b+1)).mp
      ((cosupport_principal_iff_vanishes hx hg hJg (b+1)).mpr h))
  obtain ⟨d,hd⟩ := hW.2 x hx
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hd
  have hfp := hr.vanishesToOrderOn_iff.mp hfa
  have hgp := hr.vanishesToOrderOn_iff.mp hgb
  have hnfp : ¬(idealPow (pointIdeal n x) (a+1)).mem x (f ∘ r) :=
    fun h => hnfa (hr.vanishesToOrderOn_iff.mpr h)
  have hngp : ¬(idealPow (pointIdeal n x) (b+1)).mem x (g ∘ r) :=
    fun h => hngb (hr.vanishesToOrderOn_iff.mpr h)
  have hprodPower := mul_mem_idealPow_add (fun _ _ hh => holomorphicAt_of_mem_pointIdeal hh) hfp hgp
  have hprodNot := mul_notMem_idealPow (hr.holomorphicAt_comp hf) (hr.holomorphicAt_comp hg) hnfp hngp
  have hprodVan : VanishesToOrderOn n W x (a+b) (f*g) :=
    hr.vanishesToOrderOn_iff.mpr hprodPower
  have hprodNotVan : ¬ VanishesToOrderOn n W x (a+b+1) (f*g) :=
    fun h => hprodNot (hr.vanishesToOrderOn_iff.mp h)
  have hprodGen := mul_mem_iff_principal hf hg hIf hJg
  have hcos := (cosupport_principal_iff_vanishes hx (hf.mul hg) hprodGen (a+b)).mpr hprodVan
  have hncos : x ∉ cosupport n W (I.mul J) (a+b+1) :=
    fun h => hprodNotVan ((cosupport_principal_iff_vanishes hx (hf.mul hg) hprodGen _).mp h)
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport W (I.mul J) (isCoherent_mul hI hJ)] at hcos hncos
  have hupper := nmOrd_le_of_notMem hncos
  have hlower : a+b ≤ nmOrd (ordinaryTraceMarked W (I.mul J)) x := by
    cases hsum : a+b with
    | zero => simpa only [hsum] using Nat.zero_le (nmOrd (ordinaryTraceMarked W (I.mul J)) x)
    | succ k =>
      rw [hsum] at hcos
      have hfin : ∃ q,x ∉ ordGe (ordinaryTraceMarked W (I.mul J)) (q+1) := ⟨a+b,hncos⟩
      simpa only [hsum] using succ_le_nmOrd_of_mem hfin hcos
  exact hupper.antisymm hlower

theorem exists_originalMember_principal (hn : 0 < n) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor n E) {H : Set X} (hH : H ∈ E) (x : X) :
    ∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,(vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g := by
  by_cases hxH : x ∈ H
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH
    obtain ⟨Φ,σ,_hsrc,_h0,_hinj,hA⟩ := exists_snc_chart hn hE x
    have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
    have hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0) := by
      rw [← hi]
      exact hA i (by rwa [hi])
    exact ⟨flatCoord Φ (σ i),holomorphicAt_flatCoord Φ (σ i) hxD,
      vanishingIdeal_mem_iff_flatCoord Φ hflat hxD⟩
  · refine ⟨1,holomorphicAt_const 1,?_⟩
    intro g
    have hUnit : (vanishingIdeal (n := n) H).mem x g ↔ (unitIdeal n X).mem x g := by
      refine ⟨fun hg => hg.1,fun hg => ⟨hg,?_⟩⟩
      filter_upwards [(hE.1 H hH).isOpen_compl.mem_nhds hxH] with y hy hyH
      exact False.elim (hy hyH)
    exact hUnit.trans (unit_mem_iff_principal g)

theorem exists_originalProduct_principal (hn : 0 < n) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor n E) (x : X) :
    ∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,(originalMemberProduct (n := n) E).mem x g ↔ IsInSpanAt (n := n) (· = f) x g := by
  obtain ⟨_k,Φ,σ,_hs,_hW,_hfree,_hinj,_hA,hf,hgen,_hres⟩ :=
    exists_actual_original_member_product_normal_form hn hE
      (isTransverse_univ_of_isSNCDivisor hE) (mem_univ x)
  exact ⟨_,hf,hgen⟩

/-- ALL original factors, including their true multiplicities at bad points; this
is not the DISTINCT proper branch count, which remains independently defined. -/
theorem originalMemberProduct_traceOrder_eq_sum (hn : 0 < n) {W : Set X}
    (hW : IsClosedSubmanifold n W) (E : List (Set X)) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {x : X} (hx : x ∈ W) :
    ordinaryTraceOrder W (originalMemberProduct (n := n) E) x =
      (E.map fun H => ordinaryTraceOrder W (vanishingIdeal (n := n) H) x).sum := by
  induction E with
  | nil =>
    have hnot : x ∉ ordGe (ordinaryTraceMarked W (originalMemberProduct (n := n) ([] : List (Set X)))) 1 := by
      change x ∉ ordGe (ordinaryTraceMarked W (unitIdeal n X)) 1
      rw [ordGe_ordinaryTraceMarked_eq_cosupport W _ isCoherent_unitIdeal]
      rw [cosupport_unitIdeal (show 1 ≤ 1 from le_rfl)]
      simp
    exact Nat.eq_zero_of_le_zero (nmOrd_le_of_notMem hnot)
  | cons H E ih =>
    have hTail : NormalCrossings.IsSNCDivisor n E :=
      NormalCrossingsComparison.isSNCDivisor_of_sublist hE (List.sublist_cons_self H E)
    have hdTail : W ⊆ closure (W \ ⋃ A ∈ E,A) := hdense.trans (closure_mono (by
      rintro y ⟨hyW,hyE⟩
      exact ⟨hyW,fun hh => hyE (by
        obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp hh
        exact mem_iUnion₂.mpr ⟨A,List.mem_cons_of_mem H hA,hyA⟩)⟩))
    have hIH : (vanishingIdeal (n := n) H).IsCoherent :=
      VanishingIdealCoherent.isCoherent_vanishingIdeal
        (HironakaSharpSingleBoundaryTraceCentre.originalBoundary_isClosedSubmanifold hn
          (NormalCrossingsComparison.isSNCDivisor_of_sublist hE (List.singleton_sublist.mpr (by simp))))
    have hProd := isCoherent_originalMemberProduct hn hTail
    have hNEH : ∀ y ∈ W,IsNonzeroAlongAt W (vanishingIdeal (n := n) H) y :=
      fun _ hy => originalMemberIdeal_isNonzeroAlongAt hE hdense (by simp) hy
    have hNEP : ∀ y ∈ W,IsNonzeroAlongAt W (originalMemberProduct (n := n) E) y :=
      fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hTail hdTail hy
    obtain ⟨f,hf,hfGen⟩ := exists_originalMember_principal hn hE (show H ∈ H::E by simp) x
    obtain ⟨g,hg,hgGen⟩ := exists_originalProduct_principal hn hTail x
    change ordinaryTraceOrder W ((vanishingIdeal (n := n) H).mul (originalMemberProduct (n := n) E)) x =
      ordinaryTraceOrder W (vanishingIdeal (n := n) H) x +
        (E.map fun A => ordinaryTraceOrder W (vanishingIdeal (n := n) A) x).sum
    rw [ordinaryTraceOrder_mul_of_principal hW hIH hProd hNEH hNEP hx hf hg hfGen hgGen,
      ih hTail hdTail]

end
end Hironaka.HironakaSharpOriginalProductTraceOrder
