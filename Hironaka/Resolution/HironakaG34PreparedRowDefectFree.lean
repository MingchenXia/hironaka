import Hironaka.Resolution.HironakaG34PreparedRowCarrierOrder
import Hironaka.Resolution.HironakaActualGlobalDefectProfileFold

/-! # The true chronological distinct defect misses a prepared support

Lane G34 (run 0080).  Blueprint: `hironaka-g34-resume-prepared-row-defect-free.tex`.

Setting as in `HironakaG34PreparedRowCarrierOrder`: an actual original mixed prefix `T`, row `i`
prepared (order `≤ 1`, `S_i` NC with `F_i = old.eraseIdx i ++ born`, dense off `F_i`).

* `actual_prepared_row_no_coincidence`: at a point `x ∈ S_i`, two DIFFERENT rows `k ≠ l` with
  `x ∈ S_k` never have the same residual germ at `x`.  If `J_k = J_l` at `x`, then the whole ideal
  `I(H_l)_x` lies in `J_l,x = J_k,x`, so it vanishes on `S_k` near `x`; but `S_k` is dense off `H_l`
  near `x` (for `k = i` by preparedness of row `i`, for `k ≠ i` by the held lower prepared
  neighbourhood of `S_k` at `x`), so some germ of `I(H_l)_x` is frequently nonzero on `S_k`.
* `actual_prepared_row_defect_free`: no point of `S_i` lies in the TRUE chronological distinct
  defect (all rows have order `≤ 1` there and the proper residual germs are pairwise distinct).
* `actual_prepared_row_defect_free_near`: for pure-dimensional `W`, the complement of the (closed)
  distinct defect is an open neighbourhood of `S_i`.

No defect-erasing history is constructed here. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34PreparedRowDefectFree
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  HironakaG4OriginalSelectedResidualTail HironakaG4RecordedTowerResidualCompatibility
  HironakaG4LowerPreparedNeighborhood HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpSingleBoundaryTraceCentre
  GermIdealOrder RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
  NonmonomialTransformAlong MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong
  HironakaG34PreparedRowCarrierOrder HomogenizedGlueingTower BlowupStrictSubmanifold

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Private copy (`HironakaActualGlobalDefectProfileFold`, private there): the order of the
chronological member product is the sum of the row orders. -/
private theorem chronological_product_order_sum (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) x=
      ∑ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x := by
  have h := (original_chronological_full_product_actual_geometry hn hW hE hdense T hT).2.2.2 x hx
  have hL : chronologicalMemberFamily W E T=List.ofFn
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) := by
    unfold chronologicalMemberFamily
    conv_lhs => rw [←List.ofFn_get E,List.map_ofFn]
    rfl
  simpa only [hL,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using h

/-- Generic contradiction: an ideal whose germ at `x` contains `I(H)_x` cannot vanish on a set that
is dense off `H` near `x`. -/
private theorem no_coincidence_of_dense {S H V : Set Y} {Jk Jl : GermIdeal n Y}
    (hcJk : Jk.IsCoherent) (hSk : S ⊆ Jk.zeroLocus) (hH : IsSNCDivisor n [H])
    (hVS : V ⊆ S) (hdense : V ⊆ closure (V \ H)) {x : Y} (hxV : x ∈ V)
    (hIn : ∀ g, (vanishingIdeal (n := n) H).mem x g → Jl.mem x g)
    (hEq : ∀ a, Jk.mem x a ↔ Jl.mem x a) : False := by
  obtain ⟨g,hg,hfreq⟩ := originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hxV
  have hgk : Jk.mem x g := (hEq g).mpr (hIn g hg)
  have hev := HomogenizedGlueing.eventually_mem hcJk hgk
  obtain ⟨y,⟨hyV,hyne⟩,hyJ⟩ := (hfreq.and_eventually hev).exists
  exact hyne (hSk (hVS hyV) g hyJ)

/-- Density on an open subtype gives density in the ambient space. -/
private theorem dense_of_subtype {U : Opens Y} {S H : Set Y} {F : List (Set U)}
    (hHF : (Subtype.val : U → Y) ⁻¹' H ∈ F)
    (h : (Subtype.val : U → Y) ⁻¹' S ⊆ closure ((Subtype.val : U → Y) ⁻¹' S \ ⋃ G ∈ F,G)) :
    S ∩ U ⊆ closure ((S ∩ U) \ H) := by
  intro z hz
  let zU : U := ⟨z,hz.2⟩
  have h1 : zU ∈ closure ((Subtype.val : U → Y) ⁻¹' S \ ⋃ G ∈ F,G) := h hz.1
  have h2 : zU ∈ closure ((Subtype.val : U → Y) ⁻¹' S \ (Subtype.val : U → Y) ⁻¹' H) :=
    closure_mono (fun w hw => (⟨hw.1,fun hwH => hw.2 (mem_iUnion₂.mpr ⟨_,hHF,hwH⟩)⟩ :
      w ∈ (Subtype.val : U → Y) ⁻¹' S \ (Subtype.val : U → Y) ⁻¹' H)) h1
  have h3 : z ∈ closure ((Subtype.val : U → Y) ''
      ((Subtype.val : U → Y) ⁻¹' S \ (Subtype.val : U → Y) ⁻¹' H)) :=
    image_closure_subset_closure_image continuous_subtype_val (mem_image_of_mem _ h2)
  refine closure_mono ?_ h3
  rintro _ ⟨w,hw,rfl⟩
  exact ⟨⟨hw.1,w.property⟩,hw.2⟩

/-- **No coincident residual germs at a point of a prepared support.** -/
theorem actual_prepared_row_no_coincidence
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (k l : Fin E.length) (hkl : k ≠ l) {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hxk : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get k)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get k)) T).ideal.zeroLocus)
    (hEq : ∀ a, (chronologicalMarked (originalRelativeMemberMarked W (E.get k)) T).ideal.mem x a ↔
      (chronologicalMarked (originalRelativeMemberMarked W (E.get l)) T).ideal.mem x a) : False := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let H := strictAlong T (E.get l)
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  obtain ⟨hcI,_hnzI,hNm,_hFactor⟩ := hRecorded.2.2.2.2 l
  have hHmem : H ∈ old ++ A.E :=
    List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E l))
  have hH : IsSNCDivisor n [H] :=
    isSNCDivisor_of_sublist hRecorded.2.1 (List.singleton_sublist.mpr hHmem)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (originalBoundary_isClosedSubmanifold hn hH)
  have hIn : ∀ g, (vanishingIdeal (n := n) H).mem x g → (J l).mem x g := by
    intro g hg
    change (chronologicalMarked (originalRelativeMemberMarked W (E.get l)) T).ideal.mem x g
    rw [←hNm]
    exact le_nonmonomialPartAlong_self hcI x g (le_restrictOn hcH x g hg)
  obtain ⟨_hNk,_hEk,_hDk,hwk,_hnzk,_hprk⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense k T hT
  -- `H_l` is a member of `old.eraseIdx m` for every `m ≠ l`
  have hHerase : ∀ m : Fin E.length, m ≠ l → H ∈ old.eraseIdx m.val := by
    intro m hml
    let ll : Fin old.length := ⟨l.val,by simp [old]⟩
    have hGet : old.get ll = H := by simp [old,ll,H]
    exact List.mem_eraseIdx_iff_getElem.mpr
      ⟨l.val,ll.isLt,(fun heq => hml (Fin.ext heq.symm)),by
        simpa only [List.get_eq_getElem] using hGet⟩
  by_cases hki : k = i
  · subst hki
    have hDenseH : A.N ∩ (J k).zeroLocus ⊆ closure ((A.N ∩ (J k).zeroLocus) \ H) := by
      apply (show A.N ∩ (J k).zeroLocus ⊆ closure ((A.N ∩ (J k).zeroLocus) \
          ⋃ G ∈ old.eraseIdx k.val ++ A.E,G) from hDenseS).trans (closure_mono ?_)
      intro z hz
      exact ⟨hz.1,fun hzH => hz.2 (mem_iUnion₂.mpr
        ⟨H,List.mem_append_left _ (hHerase k hkl),hzH⟩)⟩
    have hAN : (chronologicalMarked (originalRelativeMemberMarked W (E.get k)) T).N = A.N :=
      (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get k)) T).1
    have hxS : x ∈ A.N ∩ (J k).zeroLocus := ⟨hAN ▸ hxi.1,hxi.2⟩
    exact no_coincidence_of_dense hwk.isCoherent (fun z hz => hz.2) hH (subset_refl _)
      hDenseH hxS hIn hEq
  · obtain ⟨U,hxU,_hLc,_hEc,_hTc,hDc,_hRows,_hPrep⟩ :=
      actual_original_lower_prepared_neighborhood hn hW hE hdense i T hT hFull hOrd hNC hDenseS
        k hki hxi hxk
    have hHU : (Subtype.val : U → Y) ⁻¹' H ∈
        (old.eraseIdx k.val).map ((Subtype.val : U → Y) ⁻¹' ·) ++
          A.E.map ((Subtype.val : U → Y) ⁻¹' ·) :=
      List.mem_append_left _ (List.mem_map_of_mem (hHerase k hkl))
    have hDenseH := dense_of_subtype hHU hDc
    have hAN : (chronologicalMarked (originalRelativeMemberMarked W (E.get k)) T).N = A.N :=
      (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get k)) T).1
    have hxS : x ∈ (A.N ∩ (J k).zeroLocus) ∩ (U : Set Y) := ⟨⟨hAN ▸ hxk.1,hxk.2⟩,hxU⟩
    exact no_coincidence_of_dense hwk.isCoherent (fun z hz => hz.2) hH inter_subset_left
      hDenseH hxS hIn hEq

/-- **A prepared support misses the true chronological distinct defect.** -/
theorem actual_prepared_row_defect_free
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) :
    x ∉ chronologicalDistinctDefect W E T := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let F := fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  have hAN : ∀ a : Fin E.length,
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).N = A.N := fun a =>
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get a)) T).1
  have hxN : x ∈ A.N := hAN i ▸ hxi.1
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hGeo : ∀ a : Fin E.length, (F a).IsCoherent ∧ ∀ z ∈ A.N, IsNonzeroAlongAt A.N (F a) z := by
    intro a
    obtain ⟨hNa,_hEa,_hDa,hwa,hnza,_hpra⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense a T hT
    refine ⟨hwa.isCoherent,?_⟩
    rw [←hNa]
    exact hnza
  -- every row has order `≤ 1` at `x`
  have hLe : ∀ a : Fin E.length, ordinaryTraceOrder A.N (F a) x ≤ 1 := by
    intro a
    by_cases hai : a = i
    · subst hai
      have h := hOrd x hxi.1
      rw [hAN a] at h
      exact h
    · exact actual_prepared_row_other_order_le_one hn hW hE hdense i T hT hFull hOrd hNC hDenseS
        a hai hxi
  -- a non-proper row has order `0`
  have hZero : ∀ a : Fin E.length, a ∉ actualProperPositions F x →
      ordinaryTraceOrder A.N (F a) x = 0 := by
    intro a ha
    have h1 : (F a).mem x (1 : Y → ℂ) := by
      by_contra hne
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a,hne⟩)
    by_contra hpos
    have hge : 1 ≤ ordinaryTraceOrder A.N (F a) x := Nat.one_le_iff_ne_zero.mpr hpos
    have hcos := (ordinaryTraceOrder_cosupport_iff hN (hGeo a).1 (hGeo a).2 hxN 1).mpr hge
    have hv := (vanishesToOrderOn_one_iff hxN (holomorphicAt_const (n := n) (M := Y) (x := x) 1)).mp
      (hcos.2 _ h1)
    exact one_ne_zero hv
  -- the proper positions inject into the germ classes
  have hInj : Set.InjOn (Quotient.mk (actualIdealGermSetoid F x))
      (actualProperPositions F x : Set (Fin E.length)) := by
    intro k hk l _hl hkl
    by_contra hne
    have hrel : ∀ a, (F k).mem x a ↔ (F l).mem x a := Quotient.exact hkl
    have hxk : x ∈ (F k).zeroLocus :=
      (actual_proper_iff_zeroLocus (fun a => (hGeo a).1) k x).mp hk
    exact actual_prepared_row_no_coincidence hn hW hE hdense i T hT hFull hOrd hNC hDenseS
      k l hne hxi ⟨(hAN k).symm ▸ hxN,hxk⟩ hrel
  have hCount : actualDistinctProperCount F x = (actualProperPositions F x).card :=
    Finset.card_image_of_injOn hInj
  have hSum : ordinaryTraceOrder A.N (chronologicalMemberProduct W E T) x ≤
      (actualProperPositions F x).card := by
    rw [chronological_product_order_sum hn hW hE hdense T hT hxN]
    unfold actualProperPositions
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : ¬(F a).mem x (1 : Y → ℂ)
    · rw [if_pos ha]
      exact hLe a
    · rw [if_neg ha]
      have hnp : a ∉ actualProperPositions F x := fun hm =>
        ha (Finset.mem_filter.mp hm).2
      exact (hZero a hnp).le
  intro hDef
  have hlt := hDef.2
  change actualDistinctProperCount F x <
    ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) x at hlt
  rw [←chronological_product_eq_actual_family_product W E T] at hlt
  omega

/-- **The complement of the distinct defect is an open neighbourhood of a prepared support.** -/
theorem actual_prepared_row_defect_free_near
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) :
    ∃ U : Opens Y, (U : Set Y) = (chronologicalDistinctDefect W E T)ᶜ ∧
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U := by
  have hClosed := (original_chronological_distinct_defect_analytic hn hW hE hdense d hReg T hT).isClosed
  exact ⟨⟨_,hClosed.isOpen_compl⟩,rfl,fun x hx =>
    actual_prepared_row_defect_free hn hW hE hdense i T hT hFull hOrd hNC hDenseS hx⟩

end
end Hironaka.HironakaG34PreparedRowDefectFree
