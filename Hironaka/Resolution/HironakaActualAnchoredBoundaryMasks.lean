import Hironaka.Resolution.HironakaActualAnchoredStrictCarrierMask
import Mathlib.Data.List.OfFn

/-! Every native boundary slot on the SAME anchored point-tail window.
Only initial source masks are inputs; current masks/words are derived.
Blueprint FIRST: `hironaka-actual-anchored-boundary-masks.tex`. -/

set_option autoImplicit false

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualAnchoredBoundaryMasks

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HironakaActualAnchoredVerticalChart
  HironakaActualAnchoredStrictCarrierMask HironakaActualProjectionTestRecord
  HironakaActualProjectionVerticalBlowupChart

open scoped ProductComplexManifold

noncomputable section

/-- Source LAST containment gives genuine LOCAL strict emptiness; the actual
new birth is LAST=0 on the whole native target chart source. -/
theorem strict_point_chart_last_empty {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (N : Set X) (x : X) {π : Y→X}
    (hπ : IsBlowupAlong (n+1) ({x} : Set X) π)
    (a : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1)))
    (U : Set X) (hU : IsOpen U) (hxa : x∈a.source) (ha0 : a x=0)
    (hSource : ∀v∈U∩a.source,v∈N→a v (Fin.last n)=0)
    (hNative : ∀v∈e.source,
      π v∈a.source ∧ a (π v)=monomial 0 (Fin.last n) (e v)) :
    (∀v∈e.source,v∈π ⁻¹' ({x} : Set X) ↔ e v (Fin.last n)=0) ∧
    (∀v∈e.source∩π ⁻¹' (U∩a.source),
      v∉geoStrictTransform π ({x} : Set X) N) := by
  have hCentre (v : Y) (hv : v∈e.source) :
      v∈π ⁻¹' ({x} : Set X) ↔ e v (Fin.last n)=0 := by
    rw [mem_preimage,mem_singleton_iff]
    constructor
    · intro h
      have hc := congrArg (fun w : ComplexModel (n+1)=>w (Fin.last n)) (hNative v hv).2
      rw [h,ha0] at hc
      simpa [monomial_apply] using hc.symm
    · intro h
      have hz : monomial 0 (Fin.last n) (e v)=0 := by
        ext i
        simp [monomial_apply,h]
        rintro rfl
        exact h
      exact a.injOn (hNative v hv).1 hxa (by rw [(hNative v hv).2,hz,ha0])
  refine ⟨hCentre,?_⟩
  let W : Set Y := e.source∩π ⁻¹' (U∩a.source)
  have hW : IsOpen W := e.open_source.inter
    ((hU.inter a.open_source).preimage hπ.contMDiff.continuous)
  intro v hv hcl
  obtain ⟨w,hw,hOff⟩ := mem_closure_iff_nhds.mp hcl W (hW.mem_nhds hv)
  have hLast := hSource (π w) hw.2 hOff.1
  have hc := congrArg (fun q : ComplexModel (n+1)=>q (Fin.last n)) (hNative w hw.1).2
  rw [hLast] at hc
  have ht : e w (Fin.last n)=0 := by simpa [monomial_apply] using hc.symm
  exact hOff.2 ((hCentre w hw.1).mpr ht)

private theorem strict_trace_source_inter {X Y : Type u} [TopologicalSpace Y]
    (π : Y→X) (C K U : Set X) (W : Set Y) (hW : IsOpen W)
    (hWU : ∀v∈W,π v∈U) :
    W∩geoStrictTransform π C K = W∩geoStrictTransform π C (U∩K) := by
  ext v
  constructor
  · rintro ⟨hv,hcl⟩
    refine ⟨hv,?_⟩
    change v∈closure (π ⁻¹' ((U∩K)\C))
    rw [mem_closure_iff_nhds]
    intro A hA
    obtain ⟨w,hw,hOff⟩ := mem_closure_iff_nhds.mp hcl _
      (Filter.inter_mem hA (hW.mem_nhds hv))
    exact ⟨w,hw.1,⟨hWU w hw.2,hOff.1⟩,hOff.2⟩
  · rintro ⟨hv,hcl⟩
    have hSub : π ⁻¹' ((U∩K)\C) ⊆ π ⁻¹' (K\C) :=
      fun _ hw=>⟨hw.1.2,hw.2⟩
    exact ⟨hv,closure_mono hSub hcl⟩

private theorem map_eq_ofFn {α β : Type*} (L : List α) (f : α→β)
    (g : Fin L.length→β) (h : ∀i,f (L.get i)=g i) :
    L.map f=List.ofFn g := by
  have hh : List.ofFn (fun i : Fin L.length=>f (L.get i))=L.map f :=
    List.ofFn_getElem_eq_map L f
  exact hh.symm.trans (congrArg List.ofFn (funext h))

private theorem boundary_word_along {n : ℕ} {X : CMfd.{u} (n+1)}
    (M0 : MarkedIdeal (n+1) X)
    (L : List (Set X)) (H : Set X) (hE : M0.E=L++[H])
    (a : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (a0 : X) (ha0 : a0∈a.source) (haZero : a a0=0)
    (U : Set X) (hU : IsOpen U) (haU : a0∈U)
    (S : Fin L.length→Finset (Fin (n+1))) (P : Fin L.length→Prop)
    (hS : ∀i,Fin.last n∉S i)
    (hSource : ∀i,∀v∈U∩a.source,
      v∈L.get i ↔ P i ∧ a v∈coordSubspace (S i))
    (hBirth : ∀v∈U∩a.source,v∈H ↔ a v (Fin.last n)=0) :
    {Y : CMfd.{u} (n+1)} → (R : BlowupTower X Y) →
      (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) →
      AnchoredInheritedLastChartChain a R e →
      let V := e.source∩R.proj ⁻¹' (U∩a.source)
      (M0.geoTransformAlong R).E.map (fun K=>V∩K) =
        List.ofFn (fun i : Fin L.length =>
          {v | v∈V ∧ P i ∧ e v∈coordSubspace (S i)}) ++
        List.replicate R.length (∅ : Set Y) ++
        [V∩{v | e v (Fin.last n)=0}]
  | _,.refl,e,h => by
      obtain ⟨he,_ha⟩ := h
      subst e
      let V : Set X := a.source∩(U∩a.source)
      have hHead : L.map (fun K=>V∩K)=List.ofFn (fun i : Fin L.length=>
          {v | v∈V ∧ P i ∧ a v∈coordSubspace (S i)}) := by
        apply map_eq_ofFn
        intro i
        ext v
        constructor
        · rintro ⟨hv,hvL⟩
          exact ⟨hv,(hSource i v hv.2).mp hvL⟩
        · rintro ⟨hv,hvP⟩
          exact ⟨hv,(hSource i v hv.2).mpr hvP⟩
      have hLast : V∩H=V∩{v | a v (Fin.last n)=0} := by
        ext v
        constructor
        · rintro ⟨hv,hvH⟩
          exact ⟨hv,(hBirth v hv.2).mp hvH⟩
        · rintro ⟨hv,hv0⟩
          exact ⟨hv,(hBirth v hv.2).mpr hv0⟩
      change M0.E.map (fun K=>V∩K)=_ ++ [] ++ [_]
      rw [hE,List.map_append,List.map_singleton,hHead,hLast,List.append_nil]
      rfl
  | _,.step R C π hπ,e',h => by
      obtain ⟨_he',e,x,Φ,hPrev,hC,hx,h0,_hSrc,_hFlat,hInh,_hNative⟩ := h
      subst C
      let Uold : Set _ := e.source∩R.proj ⁻¹' (U∩a.source)
      let V : Set _ := e'.source∩(R.proj ∘ π) ⁻¹' (U∩a.source)
      have hUold : IsOpen Uold := e.open_source.inter
        ((hU.inter a.open_source).preimage R.contMDiff_proj.continuous)
      have hV : IsOpen V := e'.open_source.inter
        ((hU.inter a.open_source).preimage (R.contMDiff_proj.comp hπ.contMDiff).continuous)
      have hImage (v) (hv : v∈V) : π v∈Uold := ⟨(hInh v hv.1).1,hv.2⟩
      have hWindow (v) (hv : v∈V) : v∈e'.source∩π ⁻¹' (Uold∩e.source) :=
        ⟨hv.1,hImage v hv,(hInh v hv.1).1⟩
      have hOrigin := anchored_origin_preimage_window a R e hPrev
        a0 ha0 haZero x hx h0 U hU haU
      have hxUold : x∈Uold := ⟨hx,by
        change R.proj x∈U∩a.source
        rw [hOrigin.1]
        exact ⟨haU,ha0⟩⟩
      let Ψ := fun K : Set _ => V∩geoStrictTransform π ({x} : Set _) K
      have hEmpty (K : Set _) (hK : ∀w∈Uold∩e.source,w∈K→e w (Fin.last n)=0) :
          Ψ K=∅ := by
        have hh := (strict_point_chart_last_empty K x hπ e e' Uold hUold hx h0 hK hInh).2
        ext v
        constructor
        · rintro ⟨hv,hvK⟩
          exact (hh v (hWindow v hv)) hvK
        · exact False.elim
      let B := fun i : Fin L.length =>
        {w | w∈Uold ∧ P i ∧ e w∈coordSubspace (S i)}
      have hMapB (i : Fin L.length) :
          Ψ (B i)={v | v∈V ∧ P i ∧ e' v∈coordSubspace (S i)} := by
        by_cases hi : P i
        · have hMask : ∀w∈Uold∩e.source,w∈B i ↔ e w∈coordSubspace (S i) := by
            intro w hw
            exact ⟨fun hm=>hm.2.2,fun hm=>⟨hw.1,hi,hm⟩⟩
          have hh := strict_point_chart_mask (B i) x hπ e e' Uold hUold
            hxUold hx h0 (S i) (hS i) hMask hInh
          ext v
          constructor
          · rintro ⟨hv,hvB⟩
            exact ⟨hv,hi,(hh v (hWindow v hv)).mp hvB⟩
          · rintro ⟨hv,_hi,hvS⟩
            exact ⟨hv,(hh v (hWindow v hv)).mpr hvS⟩
        · have hh : Ψ (B i)=∅ := hEmpty (B i) (fun _ _ hm=>False.elim (hi hm.2.1))
          rw [hh]
          ext v
          simp [hi]
      have hEmpty0 : Ψ (∅ : Set _)=∅ := hEmpty ∅ (fun _ _ hm=>False.elim hm)
      have hKill : Ψ (Uold∩{w | e w (Fin.last n)=0})=∅ :=
        hEmpty _ (fun _ _ hm=>hm.2)
      have hBorn0 := (strict_point_chart_last_empty (∅ : Set _) x hπ e e' Uold hUold hx h0
        (fun _ _ hm=>False.elim hm) hInh).1
      have hBorn : V∩π ⁻¹' ({x} : Set _)=V∩{v | e' v (Fin.last n)=0} := by
        ext v
        exact ⟨fun ⟨hv,hvC⟩=>⟨hv,(hBorn0 v hv.1).mp hvC⟩,
          fun ⟨hv,hv0⟩=>⟨hv,(hBorn0 v hv.1).mpr hv0⟩⟩
      have hOld := boundary_word_along M0 L H hE a a0 ha0 haZero U hU haU S P hS hSource hBirth R e hPrev
      change (M0.geoTransformAlong R).E.map (fun K=>Uold∩K)=
        List.ofFn B ++ List.replicate R.length (∅ : Set _) ++
          [Uold∩{w | e w (Fin.last n)=0}] at hOld
      have hLocalization : (M0.geoTransformAlong R).E.map
          (fun K=>V∩geoStrictTransform π ({x} : Set _) K)=
          ((M0.geoTransformAlong R).E.map (fun K=>Uold∩K)).map Ψ := by
        rw [List.map_map]
        apply List.map_congr_left
        intro K _hK
        exact strict_trace_source_inter π {x} K Uold V hV hImage
      have hHeads : (List.ofFn B).map Ψ=List.ofFn (fun i : Fin L.length=>
          {v | v∈V ∧ P i ∧ e' v∈coordSubspace (S i)}) := by
        rw [List.map_ofFn]
        exact congrArg List.ofFn (funext hMapB)
      have hRep : (List.replicate R.length (∅ : Set _)).map Ψ=
          List.replicate R.length (∅ : Set _) := by
        rw [List.map_replicate,hEmpty0]
      change (((M0.geoTransformAlong R).E.map (geoStrictTransform π {x}))++[π ⁻¹' {x}]).map
        (fun K=>V∩K)=_ ++ List.replicate (R.length+1) (∅ : Set _) ++ [_]
      rw [List.map_append,List.map_singleton,List.map_map]
      simp only [Function.comp_def]
      rw [hLocalization,hOld]
      rw [List.map_append,List.map_append,hHeads,hRep,List.map_singleton,hKill,hBorn]
      rw [List.replicate_succ']
      simp only [List.append_assoc]
      rfl

/-- All literal current boundary slots and native clocks follow from fixed
INITIAL source masks only. Empty and duplicate slots are never deleted. -/
theorem anchored_boundary_word_masks {n : ℕ} {X : CMfd.{u} (n+1)}
    (M0 : MarkedIdeal (n+1) X)
    (L : List (Set X)) (H : Set X) (hE : M0.E=L++[H])
    (a : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (a0 : X) (ha0 : a0∈a.source) (haZero : a a0=0)
    (U : Set X) (hU : IsOpen U) (haU : a0∈U)
    (S : Fin L.length→Finset (Fin (n+1))) (P : Fin L.length→Prop)
    (hS : ∀i,Fin.last n∉S i)
    (hSource : ∀i,∀v∈U∩a.source,
      v∈L.get i ↔ P i ∧ a v∈coordSubspace (S i))
    (hBirth : ∀v∈U∩a.source,v∈H ↔ a v (Fin.last n)=0) :
    ∀{Y : CMfd.{u} (n+1)} (R : BlowupTower X Y)
      (e : OpenPartialHomeomorph Y (ComplexModel (n+1))),
      AnchoredInheritedLastChartChain a R e →
      let V := e.source∩R.proj ⁻¹' (U∩a.source)
      (M0.geoTransformAlong R).d=M0.d ∧
      (M0.geoTransformAlong R).E.length=L.length+1+R.length ∧
      IsOpen V ∧
      ((M0.geoTransformAlong R).E.map (fun K=>V∩K) =
        List.ofFn (fun i : Fin L.length =>
          {v | v∈V ∧ P i ∧ e v∈coordSubspace (S i)}) ++
        List.replicate R.length (∅ : Set Y) ++
        [V∩{v | e v (Fin.last n)=0}]) ∧
      (∀z∈e.source,e z=0→z∈V) := by
  intro Y R e h
  dsimp only
  have hLength := length_E_geoTransformAlong M0 R
  rw [hE,List.length_append,List.length_singleton] at hLength
  refine ⟨d_geoTransformAlong M0 R,hLength,
    e.open_source.inter ((hU.inter a.open_source).preimage R.contMDiff_proj.continuous),
    boundary_word_along M0 L H hE a a0 ha0 haZero U hU haU S P hS hSource hBirth R e h,?_⟩
  intro z hz he0
  have hOrigin := anchored_origin_preimage_window a R e h a0 ha0 haZero z hz he0 U hU haU
  refine ⟨hz,?_⟩
  change R.proj z∈U∩a.source
  rw [hOrigin.1]
  exact ⟨haU,ha0⟩

/-- ONLY original data choose one actual first seed, before every given tail.
The entire native ordered E, including empty and duplicate slots, is retained. -/
theorem exists_original_anchored_boundary_masks
    {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (x : X) (hx : x∈M.cosupp) :
    let p : projectionAmbient X := (x,0)
    let C : Set (projectionAmbient X) := {p}
    let _ : Fact (IsClosedSubmanifold (n+1) C) :=
      ⟨(projection_point_centre M hM x hx).1.1⟩
    let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
    let π1 : Y1→projectionAmbient X := blowupProj (n+1) C
    let Q1 : MarkedIdeal (n+1) Y1 := (projectionTest M).geoTransform C π1
    ∃ (c : FlatChart (n+1) C)
      (SE : Fin M.E.length→Finset (Fin (n+1))) (U : Set Y1),
      c.y₀=p ∧ c.k=0 ∧ c.j=Fin.last n ∧
      (∀i,Fin.last n∉SE i) ∧
      c.homeo∈atlas (ComplexModel (n+1)) Y1 ∧
      c.invFun 0∈c.source ∧ c.toFun (c.invFun 0)=0 ∧
      IsOpen U ∧ c.invFun 0∈U ∧ U⊆c.source ∧
      Q1.d=M.d ∧
      Q1.E=M.E.map (fun K=>geoStrictTransform π1 C
        ((Prod.fst : projectionAmbient X→X) ⁻¹' K)) ++
        [geoStrictTransform π1 C (horizontal X),π1 ⁻¹' C] ∧
      ∀{Y : CMfd.{u} (n+1)} (R : BlowupTower Y1 Y)
        (e : OpenPartialHomeomorph Y (ComplexModel (n+1))),
        AnchoredInheritedLastChartChain c.homeo R e →
        let V := e.source∩R.proj ⁻¹' (U∩c.source)
        (Q1.geoTransformAlong R).d=M.d ∧
        (Q1.geoTransformAlong R).E.length=M.E.length+2+R.length ∧
        IsOpen V ∧
        ((Q1.geoTransformAlong R).E.map (fun K=>V∩K) =
          List.ofFn (fun i : Fin M.E.length =>
            {v | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) ++
          [(∅ : Set Y)] ++ List.replicate R.length (∅ : Set Y) ++
          [V∩{v | e v (Fin.last n)=0}]) ∧
        (∀z∈e.source,e z=0→z∈V) := by
  dsimp only
  let p : projectionAmbient X := (x,0)
  let C : Set (projectionAmbient X) := {p}
  let _ : Fact (IsClosedSubmanifold (n+1) C) :=
    ⟨(projection_point_centre M hM x hx).1.1⟩
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X := blowupProj (n+1) C
  let Q1 : MarkedIdeal (n+1) Y1 := (projectionTest M).geoTransform C π1
  obtain ⟨Φ,c,SN,SE,U,hSeed⟩ := exists_original_anchored_vertical_frame M hM x hx
  rcases hSeed with ⟨_hΦs,_hΦ0,hcp,hck,hcj,_hOld,_hLast,_hSourceN,_hSourceE,
    _hSN,hSE,_h0c,hzSource,_hzp,hWz,_hπ,hAtlas,_hQ,_hzQ,hdQ,hEword,_hLength,
    hU,hzU,hUc,_hNmask,hEmask,hEmptyH,hBorn,_hAnchor0,_hTails⟩
  refine ⟨c,SE,U,hcp,hck,hcj,hSE,hAtlas,hzSource,hWz,hU,hzU,hUc,hdQ,hEword,?_⟩
  let L : List (Set Y1) := M.E.map (fun K=>geoStrictTransform π1 C
    ((Prod.fst : projectionAmbient X→X) ⁻¹' K)) ++ [geoStrictTransform π1 C (horizontal X)]
  have hLenL : L.length=M.E.length+1 := by simp [L]
  have hE0 : Q1.E=L++[π1 ⁻¹' C] := by
    simpa only [L,List.append_assoc,List.cons_append,List.nil_append] using hEword
  let S : Fin L.length→Finset (Fin (n+1)) := fun i=>
    if hi : i.val<M.E.length then SE ⟨i.val,hi⟩ else ∅
  let P : Fin L.length→Prop := fun i=>
    if hi : i.val<M.E.length then x∈M.E.get ⟨i.val,hi⟩ else False
  have hS : ∀i,Fin.last n∉S i := by
    intro i
    dsimp only [S]
    split_ifs with hi
    · exact hSE ⟨i.val,hi⟩
    · simp
  have hSource : ∀i,∀v∈U∩c.homeo.source,
      v∈L.get i ↔ P i ∧ c.homeo v∈coordSubspace (S i) := by
    intro i v hv
    by_cases hi : i.val<M.E.length
    · have hGet : L.get i=geoStrictTransform π1 C
          ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get ⟨i.val,hi⟩) := by
        simp only [L,List.get_eq_getElem]
        rw [List.getElem_append_left (by simpa using hi),List.getElem_map]
      rw [hGet]
      simp only [S,P,dif_pos hi]
      constructor
      · intro hvK
        by_cases hxi : x∈M.E.get ⟨i.val,hi⟩
        · exact ⟨hxi,((hEmask ⟨i.val,hi⟩).1 hxi v hv.1).mp hvK⟩
        · exact False.elim ((hEmask ⟨i.val,hi⟩).2 hxi v hv.1 hvK)
      · rintro ⟨hxi,hvS⟩
        exact ((hEmask ⟨i.val,hi⟩).1 hxi v hv.1).mpr hvS
    · have hi0 : i.val=M.E.length := by
        have hil : i.val<M.E.length+1 := lt_of_lt_of_eq i.isLt hLenL
        omega
      have hGet : L.get i=geoStrictTransform π1 C (horizontal X) := by
        simp only [L,List.get_eq_getElem]
        rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
        simp [hi0]
      rw [hGet]
      simp only [S,P,dif_neg hi]
      constructor
      · exact fun hvK=>False.elim (hEmptyH v hv.1 hvK)
      · exact fun hvK=>False.elim hvK.1
  intro Y R e hAnchor
  let V : Set Y := e.source∩R.proj ⁻¹' (U∩c.source)
  have hh := anchored_boundary_word_masks Q1 L (π1 ⁻¹' C) hE0 c.homeo (c.invFun 0)
    hzSource hWz U hU hzU S P hS hSource (fun v hv=>hBorn v hv.1) R e hAnchor
  rcases hh with ⟨hd,hLen,hOpen,hWord,hOrigin⟩
  have hMasks : List.ofFn (fun i : Fin L.length=>
      {v : Y | v∈V ∧ P i ∧ e v∈coordSubspace (S i)}) =
      List.ofFn (fun i : Fin M.E.length=>
        {v : Y | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) ++ [∅] := by
    rw [List.ofFn_congr hLenL,List.ofFn_succ']
    have hHead : (fun i : Fin M.E.length=>
        {v : Y | v∈V ∧ P (Fin.cast hLenL.symm i.castSucc) ∧
          e v∈coordSubspace (S (Fin.cast hLenL.symm i.castSucc))}) =
        (fun i : Fin M.E.length=>
          {v : Y | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) := by
      funext i
      simp [S,P,i.isLt]
    have hLast : {v : Y | v∈V ∧ P (Fin.cast hLenL.symm (Fin.last M.E.length)) ∧
        e v∈coordSubspace (S (Fin.cast hLenL.symm (Fin.last M.E.length)))}=∅ := by
      ext v
      simp [S,P]
    rw [hHead,hLast,List.concat_eq_append]
  refine ⟨hd.trans hdQ,?_,hOpen,?_,hOrigin⟩
  · change (Q1.geoTransformAlong R).E.length=M.E.length+2+R.length
    rw [hLen]
    omega
  · change (Q1.geoTransformAlong R).E.map (fun K=>V∩K)=
      List.ofFn (fun i : Fin L.length=>{v | v∈V ∧ P i ∧ e v∈coordSubspace (S i)}) ++
        List.replicate R.length (∅ : Set Y) ++ [V∩{v | e v (Fin.last n)=0}] at hWord
    rw [hMasks] at hWord
    simpa only [List.append_assoc] using hWord

end

end Hironaka.HironakaActualAnchoredBoundaryMasks
