/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalMultiBoundaryBadLocus

/-! Literal original member product and genuinely constructed restricted normal
forms. Complete mathematics-first blueprint precedes the implementation. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold

namespace Hironaka.HironakaSharpOriginalMemberProduct
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers HomogenizedIdeal MemberPullback
  NormalCrossings BlowupFlatCoordinates GermIdealOrder DivisorExponentAlong MonomialPartAlong MonomialCase OrderTaylor
open Classical
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal finite original ideal product, with its actual holomorphic unit ideal. -/
def idealListProduct : List (GermIdeal n M) → GermIdeal n M
  | [] => unitIdeal n M
  | I :: L => I.mul (idealListProduct L)

omit [IsComplexManifold n M] in
theorem unit_mem_iff_principal {x : M} (g : M → ℂ) :
    (unitIdeal n M).mem x g ↔ IsInSpanAt (n := n) (· = (1 : M → ℂ)) x g := by
  constructor
  · intro hg
    exact isInSpanAt_eq_iff.mpr ⟨hg,g,hg,Eventually.of_forall fun _ => by simp⟩
  · exact fun hg => hg.holomorphicAt

omit [IsComplexManifold n M] in
/-- Both actual factor membership dictionaries construct both product directions. -/
theorem mul_mem_iff_principal {I J : GermIdeal n M} {a b : M → ℂ} {x : M}
    (ha : HolomorphicAt n a x) (hb : HolomorphicAt n b x)
    (hI : ∀ g, I.mem x g ↔ IsInSpanAt (n := n) (· = a) x g)
    (hJ : ∀ g, J.mem x g ↔ IsInSpanAt (n := n) (· = b) x g) (g : M → ℂ) :
    (I.mul J).mem x g ↔ IsInSpanAt (n := n) (· = a * b) x g := by
  change IsInSpanAt (n := n) (fun s => ∃ u v, I.mem x u ∧ J.mem x v ∧ s = u * v) x g ↔ _
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ hg
    rintro s ⟨u,v,hu,hv,rfl⟩
    obtain ⟨huh,c,hc,huc⟩ := isInSpanAt_eq_iff.mp ((hI u).mp hu)
    obtain ⟨hvh,d,hd,hvd⟩ := isInSpanAt_eq_iff.mp ((hJ v).mp hv)
    refine isInSpanAt_eq_iff.mpr ⟨huh.mul hvh,c * d,hc.mul hd,?_⟩
    filter_upwards [huc,hvd] with z huz hvz
    change u z * v z = (c z * d z) * (a z * b z)
    rw [huz,hvz]
    ring
  · intro hg
    have haI : I.mem x a := (hI a).mpr
      (isInSpanAt_eq_iff.mpr ⟨ha,1,holomorphicAt_const 1,Eventually.of_forall fun _ => by simp⟩)
    have hbJ : J.mem x b := (hJ b).mpr
      (isInSpanAt_eq_iff.mpr ⟨hb,1,holomorphicAt_const 1,Eventually.of_forall fun _ => by simp⟩)
    exact IsInSpanAt.mono (fun _ hs => ⟨a,b,haI,hbJ,hs⟩) hg

omit [IsComplexManifold n M] in
/-- Actual list induction keeps every original factor and its genuine function. -/
theorem paired_list_product_principal (P : List (GermIdeal n M × (M → ℂ))) {x : M}
    (hP : ∀ p ∈ P, HolomorphicAt n p.2 x ∧
      ∀ g, p.1.mem x g ↔ IsInSpanAt (n := n) (· = p.2) x g) :
    HolomorphicAt n (P.map Prod.snd).prod x ∧
      ∀ g, (idealListProduct (P.map Prod.fst)).mem x g ↔
        IsInSpanAt (n := n) (· = (P.map Prod.snd).prod) x g := by
  induction P with
  | nil => exact ⟨holomorphicAt_const 1,unit_mem_iff_principal⟩
  | cons p P ih =>
    obtain ⟨hp,hgen⟩ := hP p (by simp)
    obtain ⟨hprod,hrest⟩ := ih (fun a ha => hP a (List.mem_cons_of_mem _ ha))
    exact ⟨hp.mul hprod,fun g => mul_mem_iff_principal hp hprod hgen hrest g⟩

/-- The SAME literal original boundary list, independently of any coordinates. -/
def originalMemberProduct (E : List (Set M)) : GermIdeal n M :=
  idealListProduct (E.map (vanishingIdeal (n := n)))

omit [IsComplexManifold n M] in
theorem restricted_span_iff_principal {W : Set M} {I : GermIdeal n M} {a : M → ℂ} {x : M}
    (ha : HolomorphicAt n a x) (hI : ∀ g, I.mem x g ↔ IsInSpanAt (n := n) (· = a) x g)
    (g : M → ℂ) : IsInSpanOnAt (n := n) W (I.mem x) x g ↔
      IsInSpanOnAt (n := n) W (· = a) x g := by
  constructor
  · exact IsInSpanOnAt.trans fun s hs => IsInSpanAt.restrict ((hI s).mp hs)
  · exact IsInSpanOnAt.mono fun s hs => hs ▸ (hI a).mpr
      (isInSpanAt_eq_iff.mpr ⟨ha,1,holomorphicAt_const 1,Eventually.of_forall fun _ => by simp⟩)

/-- Original transverse SNC data construct the ACTUAL whole member-product normal form. -/
theorem exists_actual_original_member_product_normal_form (hn : 0 < n)
    {W : Set M} {E : List (Set M)} (hE : IsSNCDivisor n E) (hT : IsTransverse n W E)
    {x : M} (hx : x ∈ W) :
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (σ : Fin E.length → Fin n),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ W ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)) ∧
      (∀ i, x ∈ E.get i → (σ i).1 < k) ∧ Set.InjOn σ {i | x ∈ E.get i} ∧
      (∀ i, x ∈ E.get i → ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0)) ∧
      let p : M → ℂ := fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i), flatCoord Φ (σ i) z
      HolomorphicAt n p x ∧
      (∀ g, (originalMemberProduct (n := n) E).mem x g ↔ IsInSpanAt (n := n) (· = p) x g) ∧
      ∀ g, IsInSpanOnAt (n := n) W ((originalMemberProduct (n := n) E).mem x) x g ↔
        IsInSpanOnAt (n := n) W (· = p) x g := by
  classical
  obtain ⟨kC,kW,Φ,σ,hΦsrc,hσk,hσinj,hflat⟩ :=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hT
      hT.hasNormalCrossings hx
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  let f : Fin E.length → M → ℂ := fun i => if x ∈ E.get i then flatCoord Φ (σ i) else 1
  let P : List (GermIdeal n M × (M → ℂ)) :=
    List.ofFn fun i : Fin E.length => (vanishingIdeal (n := n) (E.get i),f i)
  have hP : ∀ p ∈ P, HolomorphicAt n p.2 x ∧
      ∀ g, p.1.mem x g ↔ IsInSpanAt (n := n) (· = p.2) x g := by
    rintro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    by_cases hi : x ∈ E.get i
    · have hA : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
          chartAt (ComplexModel n) x y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0) :=
        fun hy1 hy2 => (hflat hy1 hy2).2.2 i hi
      simpa only [f,if_pos hi] using
        And.intro (holomorphicAt_flatCoord Φ (σ i) hxD)
          (vanishingIdeal_mem_iff_flatCoord Φ hA hxD)
    · have hunit : ∀ g, (vanishingIdeal (n := n) (E.get i)).mem x g ↔ HolomorphicAt n g x := by
        intro g
        refine ⟨fun hg => hg.1,fun hg => ⟨hg,?_⟩⟩
        filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hi] with y hy hyH
        exact False.elim (hy hyH)
      refine ⟨?_,?_⟩
      · change HolomorphicAt n (if x ∈ E.get i then flatCoord Φ (σ i) else 1) x
        rw [if_neg hi]
        change HolomorphicAt n (fun _ : M => (1 : ℂ)) x
        exact holomorphicAt_const 1
      · intro g
        simpa only [f,if_neg hi] using (hunit g).trans (unit_mem_iff_principal g)
  obtain ⟨hprod,hgen⟩ := paired_list_product_principal P hP
  have hIdeal : P.map Prod.fst = E.map (vanishingIdeal (n := n)) := by
    simp only [P,List.map_ofFn]
    change List.ofFn ((vanishingIdeal (n := n)) ∘ E.get) = E.map (vanishingIdeal (n := n))
    rw [← List.map_ofFn,List.ofFn_get]
  have hgenerator : (P.map Prod.snd).prod =
      (fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i),flatCoord Φ (σ i) z) := by
    simp only [P,List.map_ofFn,List.prod_ofFn]
    funext z
    simp only [Function.comp_apply,Finset.prod_apply,f]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> rfl
  rw [hgenerator] at hprod hgen
  rw [hIdeal] at hgen
  refine ⟨kW,Φ,σ,hΦsrc,fun hy1 hy2 => (hflat hy1 hy2).2.1,hσk,hσinj,
    fun i hi _ hy1 hy2 => (hflat hy1 hy2).2.2 i hi,hprod,hgen,?_⟩
  exact restricted_span_iff_principal hprod hgen

theorem exists_actual_original_member_product_neighborhood (hn : 0 < n)
    {W : Set M} {E : List (Set M)} (hW : IsClosed W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {x : M}
    (hx : HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) W E x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      let WU := (Subtype.val : U → M) ⁻¹' W
      let EU := E.map ((Subtype.val : U → M) ⁻¹' ·)
      IsSNCDivisor n EU ∧ IsTransverse n WU EU ∧
      ∀ y : U, y ∈ WU →
        ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y))
          (σ : Fin EU.length → Fin n),
          Φ.source ⊆ (chartAt (ComplexModel n) y).target ∧
          (∀ {z : U}, z ∈ (chartAt (ComplexModel n) y).source → chartAt (ComplexModel n) y z ∈ Φ.source →
            (z ∈ WU ↔ Φ.toFun (chartAt (ComplexModel n) y z) ∈ complexCoordinatePlane n k)) ∧
          (∀ i, y ∈ EU.get i → (σ i).1 < k) ∧ Set.InjOn σ {i | y ∈ EU.get i} ∧
          (∀ i, y ∈ EU.get i → ∀ {z : U}, z ∈ (chartAt (ComplexModel n) y).source →
            chartAt (ComplexModel n) y z ∈ Φ.source →
            (z ∈ EU.get i ↔ Φ.toFun (chartAt (ComplexModel n) y z) (σ i)=0)) ∧
          let p : U → ℂ := fun z => ∏ i ∈ Finset.univ.filter (fun i => y ∈ EU.get i), flatCoord Φ (σ i) z
          HolomorphicAt n p y ∧
          (∀ g, (originalMemberProduct (n := n) EU).mem y g ↔ IsInSpanAt (n := n) (· = p) y g) ∧
          ∀ g, IsInSpanOnAt (n := n) WU ((originalMemberProduct (n := n) EU).mem y) y g ↔
            IsInSpanOnAt (n := n) WU (· = p) y g := by
  obtain ⟨U,hxU,hEU,hTU⟩ :=
    HironakaSharpOriginalMultiBoundaryBadLocus.exists_actual_original_transverse_neighborhood hW hE hdense hx
  exact ⟨U,hxU,hEU,hTU,fun _ hy => exists_actual_original_member_product_normal_form hn hEU hTU hy⟩

theorem actual_member_product_cosupport_iff_distinct_trace_count (hn : 0 < n)
    {W : Set M} {E : List (Set M)} (hE : IsSNCDivisor n E) (hT : IsTransverse n W E)
    {x : M} (hx : x ∈ W) (q : ℕ) :
    x ∈ cosupport n W (originalMemberProduct (n := n) E) q ↔
      q ≤ HironakaSharpOriginalMultiBoundaryBadLocus.distinctProperTraceGermCount (n := n) W E x := by
  classical
  rw [HironakaSharpOriginalMultiBoundaryBadLocus.distinctProperTraceGermCount_eq_boundaryCount hn hE hT hx]
  obtain ⟨k,Φ,σ,hΦsrc,hWflat,hσk,_hσinj,hA,hp,hgen,_hres⟩ :=
    exists_actual_original_member_product_normal_form hn hE hT hx
  let T : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i
  let p : M → ℂ := fun z => ∏ i ∈ T,flatCoord Φ (σ i) z
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hzero : ∀ i ∈ T, flatCoord Φ (σ i) x = 0 :=
    fun i hi => (hA i (Finset.mem_filter.mp hi).2 hxD.1 hxD.2).mp (Finset.mem_filter.mp hi).2
  have hpow : (idealPow (pointIdeal n x) T.card).mem x p ∧
      ¬(idealPow (pointIdeal n x) (T.card+1)).mem x p := by
    simpa [p] using
      prod_flatCoord_pow_order Φ σ (fun _ => 1) hxD T hzero
  have hr : IsLocalRetraction n W (flatRetract Φ k) x :=
    isLocalRetraction_flatRetract hΦsrc hWflat hxD hx
  have hpr : p ∘ flatRetract Φ k =ᶠ[𝓝 x] p := by
    have hev := (eventually_all_finset T).mpr fun i hi =>
      eventually_flatMap_flatRetract hΦsrc hWflat hxD hx (hσk i (Finset.mem_filter.mp hi).2)
    filter_upwards [hev] with z hz
    change (∏ i ∈ T,flatCoord Φ (σ i) (flatRetract Φ k z)) = ∏ i ∈ T,flatCoord Φ (σ i) z
    exact Finset.prod_congr rfl fun i hi => (hz i hi).2
  change x ∈ cosupport n W (originalMemberProduct (n := n) E) q ↔ q ≤ T.card
  constructor
  · intro hcos
    by_contra hlt
    have hpI : (originalMemberProduct (n := n) E).mem x p := (hgen p).mpr
      (isInSpanAt_eq_iff.mpr ⟨hp,1,holomorphicAt_const 1,
        Eventually.of_forall fun z => (one_mul (p z)).symm⟩)
    have hpq := mem_idealPow_congr (hr.vanishesToOrderOn_iff.mp (hcos.2 p hpI)) hpr
    exact hpow.2 (idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg)
      (by omega : T.card+1 ≤ q) x p hpq)
  · intro hq
    refine ⟨hx,fun g hg => ?_⟩
    obtain ⟨_hg,c,hc,hgc⟩ := isInSpanAt_eq_iff.mp ((hgen g).mp hg)
    refine ⟨fun z => c z * p z,?_,hgc.mono fun _ hz _ => hz⟩
    exact idealPow_le_of_le (fun _ _ hh => holomorphicAt_of_mem_pointIdeal hh) hq x _
      (mul_mem_idealPow hc hpow.1)

theorem exists_actual_original_product_order_neighborhood (hn : 0 < n)
    {W : Set M} {E : List (Set M)} (hW : IsClosed W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {x : M}
    (hx : HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) W E x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      let WU := (Subtype.val : U → M) ⁻¹' W
      let EU := E.map ((Subtype.val : U → M) ⁻¹' ·)
      IsSNCDivisor n EU ∧ IsTransverse n WU EU ∧
      ∀ y : U, y ∈ WU → ∀ q : ℕ,
        y ∈ cosupport n WU (originalMemberProduct (n := n) EU) q ↔
          q ≤ HironakaSharpOriginalMultiBoundaryBadLocus.distinctProperTraceGermCount (n := n) WU EU y := by
  obtain ⟨U,hxU,hEU,hTU⟩ :=
    HironakaSharpOriginalMultiBoundaryBadLocus.exists_actual_original_transverse_neighborhood hW hE hdense hx
  exact ⟨U,hxU,hEU,hTU,fun _ hy q => actual_member_product_cosupport_iff_distinct_trace_count hn hEU hTU hy q⟩

end
end Hironaka.HironakaSharpOriginalMemberProduct
