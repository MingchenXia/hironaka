/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualPrincipalSharedBranchDimension

/-! Actual relative-product generators, true carrier order additivity and
nonzero product germs. Carrier-normal germs are retained by real normalization. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualRelativeProductOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProduct RelativePrincipalizationSpan RestrictedIdealExtension
  GermIdealOrder TangentDirectionAlong DerivativeIdealAlong GiraudAlong DivisorExponentAlong
  IdealWeightPowers InvertibleIdealQuotient MonomialPartAlong OrderTaylor GermOrderProduct MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X : CMfd.{u} n}

/-- Both true relative dictionaries give BOTH normalized product directions. -/
theorem restrictOn_mul_relative_principal_mem_iff {N : Set X} {I J : GermIdeal n X}
    {x : X} {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hI : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hJ : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a) (a : X → ℂ) :
    (restrictOn n N (I.mul J)).mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f*g) x a := by
  constructor
  · rintro ⟨ha,hspan⟩
    refine ⟨ha,IsInSpanOnAt.trans (fun b hb => ?_) hspan⟩
    change IsInSpanAt (n := n) (fun s => ∃ b c,I.mem x b ∧ J.mem x c ∧ s=b*c) x b at hb
    refine IsInSpanOnAt.trans (fun v hv => ?_) (IsInSpanAt.restrict hb)
    obtain ⟨b,c,hb,hc,rfl⟩ := hv
    obtain ⟨s,hs,hbs⟩ := isInSpanOnAt_eq_iff.mp ((hI b).mp hb).2
    obtain ⟨t,ht,hct⟩ := isInSpanOnAt_eq_iff.mp ((hJ c).mp hc).2
    refine isInSpanOnAt_eq_iff.mpr ⟨s*t,hs.mul ht,?_⟩
    filter_upwards [hbs,hct] with y hyb hyc hyN
    change b y*c y=(s y*t y)*(f y*g y)
    rw [hyb hyN,hyc hyN]
    ring
  · rintro ⟨ha,hspan⟩
    have hfI : I.mem x f := (hI f).mpr ⟨hf,isInSpanOnAt_eq_iff.mpr
      ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
    have hgJ : J.mem x g := (hJ g).mpr ⟨hg,isInSpanOnAt_eq_iff.mpr
      ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
    have hp : (I.mul J).mem x (f*g) := by
      change IsInSpanAt (n := n) (fun s => ∃ b c,I.mem x b ∧ J.mem x c ∧ s=b*c) x (f*g)
      exact isInSpanAt_self ⟨f,g,hfI,hgJ,rfl⟩ (hf.mul hg)
    exact ⟨ha,IsInSpanOnAt.mono (S := (·=f*g)) (fun b hb => hb ▸ hp) hspan⟩

/-- Actual relative principal membership gives the real carrier order predicate. -/
theorem cosupport_relative_principal_iff_vanishes {N : Set X} {I : GermIdeal n X}
    {x : X} (hx : x ∈ N) {f : X → ℂ} (hf : HolomorphicAt n f x)
    (hI : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a) (q : ℕ) :
    x ∈ cosupport n N I q ↔ VanishesToOrderOn n N x q f := by
  constructor
  · intro hq
    exact hq.2 f ((hI f).mpr ⟨hf,isInSpanOnAt_eq_iff.mpr
      ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩)
  · intro hq
    refine ⟨hx,fun a ha => ?_⟩
    obtain ⟨c,hc,hac⟩ := isInSpanOnAt_eq_iff.mp ((hI a).mp ha).2
    exact CodimOneCentreAlong.VanishesToOrderOn.congr_on (hq.mul_left hc) (hac.mono fun y hy hyN => (hy hyN).symm)

/-- Literal product cosupport, rather than a desired product certificate. -/
theorem cosupport_mul_relative_principal_iff_vanishes {N : Set X} {I J : GermIdeal n X}
    (hI : I.IsCoherent) (hJ : J.IsCoherent) {x : X} (hx : x ∈ N)
    {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hIf : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hJg : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a) (q : ℕ) :
    x ∈ cosupport n N (I.mul J) q ↔ VanishesToOrderOn n N x q (f*g) := by
  have hnorm : cosupport n N (restrictOn n N (I.mul J)) q=cosupport n N (I.mul J) q :=
    Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe
      (restrictLe_self_restrictOn (isCoherent_mul hI hJ)) q)
      (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe restrictLe_restrictOn q)
  rw [← hnorm]
  exact cosupport_relative_principal_iff_vanishes hx (hf.mul hg) (restrictOn_mul_relative_principal_mem_iff hf hg hIf hJg) q

private theorem actual_relative_product_order_bounds {N : Set X} {I J : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hj : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hIf : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hJg : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a) :
    VanishesToOrderOn n N x (ordinaryTraceOrder N I x+ordinaryTraceOrder N J x) (f*g) ∧
      ¬VanishesToOrderOn n N x (ordinaryTraceOrder N I x+ordinaryTraceOrder N J x+1) (f*g) := by
  let a := ordinaryTraceOrder N I x
  let b := ordinaryTraceOrder N J x
  have hfa : VanishesToOrderOn n N x a f := (cosupport_relative_principal_iff_vanishes hx hf hIf a).mp
    ((ordinaryTraceOrder_cosupport_iff hN hI hi hx a).mpr le_rfl)
  have hgb : VanishesToOrderOn n N x b g := (cosupport_relative_principal_iff_vanishes hx hg hJg b).mp
    ((ordinaryTraceOrder_cosupport_iff hN hJ hj hx b).mpr le_rfl)
  have hnfa : ¬VanishesToOrderOn n N x (a+1) f := fun h => Nat.not_succ_le_self a
    ((ordinaryTraceOrder_cosupport_iff hN hI hi hx (a+1)).mp ((cosupport_relative_principal_iff_vanishes hx hf hIf _).mpr h))
  have hngb : ¬VanishesToOrderOn n N x (b+1) g := fun h => Nat.not_succ_le_self b
    ((ordinaryTraceOrder_cosupport_iff hN hJ hj hx (b+1)).mp ((cosupport_relative_principal_iff_vanishes hx hg hJg _).mpr h))
  obtain ⟨d,hd⟩ := hN.2 x hx
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hd
  have hfp := hr.vanishesToOrderOn_iff.mp hfa
  have hgp := hr.vanishesToOrderOn_iff.mp hgb
  have hnfp : ¬(idealPow (pointIdeal n x) (a+1)).mem x (f ∘ r) := fun h => hnfa (hr.vanishesToOrderOn_iff.mpr h)
  have hngp : ¬(idealPow (pointIdeal n x) (b+1)).mem x (g ∘ r) := fun h => hngb (hr.vanishesToOrderOn_iff.mpr h)
  have hprodPower := mul_mem_idealPow_add (fun _ _ hh => holomorphicAt_of_mem_pointIdeal hh) hfp hgp
  have hprodNot := mul_notMem_idealPow (hr.holomorphicAt_comp hf) (hr.holomorphicAt_comp hg) hnfp hngp
  exact ⟨hr.vanishesToOrderOn_iff.mpr hprodPower,fun h => hprodNot (hr.vanishesToOrderOn_iff.mp h)⟩

/-- Genuine relative-product order additivity retains actual multiplicities. -/
theorem ordinaryTraceOrder_mul_of_relative_principal {N : Set X} {I J : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hj : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hIf : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hJg : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a) :
    ordinaryTraceOrder N (I.mul J) x=ordinaryTraceOrder N I x+ordinaryTraceOrder N J x := by
  let a := ordinaryTraceOrder N I x
  let b := ordinaryTraceOrder N J x
  obtain ⟨hvan,hnvan⟩ := actual_relative_product_order_bounds hN hI hJ hi hj hx hf hg hIf hJg
  have hcos := (cosupport_mul_relative_principal_iff_vanishes hI hJ hx hf hg hIf hJg (a+b)).mpr hvan
  have hncos : x ∉ cosupport n N (I.mul J) (a+b+1) := fun h => hnvan
    ((cosupport_mul_relative_principal_iff_vanishes hI hJ hx hf hg hIf hJg _).mp h)
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport N (I.mul J) (isCoherent_mul hI hJ)] at hcos hncos
  have hupper := NonmonomialOrderLocal.nmOrd_le_of_notMem hncos
  have hlower : a+b ≤ NonmonomialOrderLocal.nmOrd (ordinaryTraceMarked N (I.mul J)) x := by
    cases hsum : a+b with
    | zero => simpa only [hsum] using Nat.zero_le (NonmonomialOrderLocal.nmOrd (ordinaryTraceMarked N (I.mul J)) x)
    | succ k =>
      rw [hsum] at hcos
      have hfin : ∃ q,x ∉ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked N (I.mul J)) (q+1) := ⟨a+b,hncos⟩
      simpa only [hsum] using NonmonomialOrderLocal.succ_le_nmOrd_of_mem hfin hcos
  exact hupper.antisymm hlower

/-- Actual next-power exclusion gives a real nonzero product germ, internally. -/
theorem isNonzeroAlongAt_mul_of_relative_principal {N : Set X} {I J : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hj : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hIf : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hJg : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a) :
    IsNonzeroAlongAt N (I.mul J) x := by
  have hfI := (hIf f).mpr ⟨hf,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hgJ := (hJg g).mpr ⟨hg,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hp : (I.mul J).mem x (f*g) := by
    change IsInSpanAt (n := n) (fun s => ∃ b c,I.mem x b ∧ J.mem x c ∧ s=b*c) x (f*g)
    exact isInSpanAt_self ⟨f,g,hfI,hgJ,rfl⟩ (hf.mul hg)
  refine ⟨f*g,hp,?_⟩
  have hnvan := (actual_relative_product_order_bounds hN hI hJ hi hj hx hf hg hIf hJg).2
  apply frequently_iff.mpr
  intro U hU
  by_contra hno
  apply hnvan
  have hz : ∀ q,(idealPow (pointIdeal n x) q).mem x (0 : X → ℂ) := by
    intro q
    cases q with
    | zero => exact holomorphicAt_const 0
    | succ q => exact ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,(fun i => i.elim0),(fun i => i.elim0),
        Eventually.of_forall fun _ => by simp⟩
  refine ⟨0,hz _,?_⟩
  filter_upwards [hU] with y hy hyN
  by_contra hne
  exact hno ⟨y,hy,hyN,hne⟩

/-- ONLY original finite histories supply BOTH current relative ideals and
true product order/nonzero; no ambient-principal substitution is used. -/
theorem original_chronological_two_member_product_order (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i j : Fin E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal
    (∀ y ∈ N,ordinaryTraceOrder N (I.mul J) y=ordinaryTraceOrder N I y+ordinaryTraceOrder N J y) ∧
    (∀ y ∈ N,IsNonzeroAlongAt N (I.mul J) y) ∧
    ∀ y ∈ N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ a,(restrictOn n N (I.mul J)).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a := by
  obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  obtain ⟨hNj,_hEj,_hmj,hwj,hnzj,hprj⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  have hN := hwi.isClosedSubmanifold_N
  rw [hNi] at hN hnzi hpri
  rw [hNj] at hnzj hprj
  refine ⟨?_,?_,?_⟩
  · intro y hy
    obtain ⟨f,hf,hfi⟩ := hpri y hy
    obtain ⟨g,hg,hgj⟩ := hprj y hy
    exact ordinaryTraceOrder_mul_of_relative_principal hN hwi.isCoherent hwj.isCoherent hnzi hnzj hy hf hg hfi hgj
  · intro y hy
    obtain ⟨f,hf,hfi⟩ := hpri y hy
    obtain ⟨g,hg,hgj⟩ := hprj y hy
    exact isNonzeroAlongAt_mul_of_relative_principal hN hwi.isCoherent hwj.isCoherent hnzi hnzj hy hf hg hfi hgj
  · intro y hy
    obtain ⟨f,hf,hfi⟩ := hpri y hy
    obtain ⟨g,hg,hgj⟩ := hprj y hy
    exact ⟨f*g,hf.mul hg,restrictOn_mul_relative_principal_mem_iff hf hg hfi hgj⟩

end
end Hironaka.HironakaSharpActualRelativeProductOrder
