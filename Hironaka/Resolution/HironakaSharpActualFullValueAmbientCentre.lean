import Hironaka.Resolution.HironakaSharpActualIncidentCentreTrace
import Hironaka.Resolution.HironakaSharpActualFullBornIncidence
import Hironaka.Resolution.HironakaSharpOriginalDynamicGoodPrefixes

/-! SAME positive FULL centres preserve actual retained ambient incidence.
Whole trace residual dictionaries are lower induction inputs here; the original
finite producer constructs them internally. Full mathematics precedes source in
`hironaka-sharp-incident-ambient-dynamic-prefixes-extension.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFullValueAmbientCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms HomogenizedGlueingTower HironakaSharpActualIncidentCentreTrace HironakaSharpActualFullBornIncidence
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualDynamicDistinctCentre
  HironakaSharpOriginalAllBoundaryCentre HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProductDomain RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers InvertibleIdealQuotient RestrictLeCalculus
  NonmonomialOrderLocal NonmonomialTransformAlong MarkedIdealOperationsAlong CanonicalCentres
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem span_on_value_zero {N : Set X} {S : (X → ℂ) → Prop} {x : X} {g : X → ℂ}
    (hx : x∈N) (h : IsInSpanOnAt (n := n) N S x g) (hz : ∀ s,S s → s x=0) : g x=0 := by
  obtain ⟨k,s,a,hs,_ha,he⟩ := h
  rw [he.self_of_nhds hx]
  exact Finset.sum_eq_zero fun i _ => by rw [hz (s i) (hs i),mul_zero]

private theorem pow_vanishing_value_zero {H : Set X} {x : X} {g : X → ℂ} {q : ℕ}
    (hx : x∈H) (hq : 0<q) (hg : (idealPow (vanishingIdeal (n := n) H) q).mem x g) : g x=0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  change IsInSpanAt (n := n) (fun s => ∃ a b,
    (idealPow (vanishingIdeal (n := n) H) r).mem x a ∧
      (vanishingIdeal (n := n) H).mem x b ∧ s=a*b) x g at hg
  obtain ⟨_hh,k,s,a,hs,_ha,he⟩ := hg
  rw [he.self_of_nhds]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨u,v,_hu,hv,hsi⟩ := hs i
  rw [hsi]
  simp only [Pi.mul_apply,hv.2.self_of_nhds hx,mul_zero]

private theorem monomial_zero_of_positive_exponent {N : Set X} {B : List (Set X)}
    {I : GermIdeal n X} {x : X} (hx : x∈N) (j : Fin B.length) (hj : x∈B.get j)
    (hpos : 0<divExpAlong n N I (B.get j) x) :
    x∈(monomialPartAlong n N I B).zeroLocus := by
  intro g hg
  exact span_on_value_zero hx (hg.2 j hx hj)
    (fun s hs => pow_vanishing_value_zero hj hpos hs)

/-- Positivity is produced from actual properness; actual transverse born
exponent constancy and the real incidence law propagate the WHOLE zero locus. -/
theorem eventually_monomial_zeroLocus_of_born_incidence (hn : 0<n)
    {N C : Set X} {B : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hB : IsSNCDivisor n B) (hT : IsTransverse n N B)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y∈N,IsNonzeroAlongAt N I y)
    (hCN : C⊆N) {x : X} (hx : x∈C)
    (hBorn : ∀ j : Fin B.length,x∈B.get j → ∀ᶠ y in 𝓝 x,y∈C → y∈B.get j)
    (hxD : x∈(monomialPartAlong n N I B).zeroLocus) :
    ∀ᶠ y in 𝓝 x,y∈C → y∈(monomialPartAlong n N I B).zeroLocus := by
  have hSome : ∃ j : Fin B.length,x∈B.get j ∧ 0<divExpAlong n N I (B.get j) x := by
    by_contra h
    push Not at h
    have hOne : (monomialPartAlong n N I B).mem x (1 : X → ℂ) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      intro j _hjN hj
      have he : divExpAlong n N I (B.get j) x=0 := Nat.eq_zero_of_le_zero (h j hj)
      rw [he,idealPow_zero]
      exact IsInSpanAt.restrict (isInSpanAt_self (holomorphicAt_const 1) (holomorphicAt_const 1))
    exact one_ne_zero (hxD 1 hOne)
  obtain ⟨j,hj,hpos⟩ := hSome
  filter_upwards [hBorn j hj,eventually_divExpAlong_get_eq hn hN hB hT hI hnz j (hCN hx) hj]
    with y hy hExp hyC
  apply monomial_zero_of_positive_exponent (hCN hyC) j (hy hyC)
  rw [hExp (hCN hyC) (hy hyC)]
  exact hpos

private theorem normalized_zeroLocus_iff {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {x : X} (hx : x∈N) :
    x∈(restrictOn n N I).zeroLocus ↔ x∈I.zeroLocus := by
  exact ⟨fun h g hg => h g (le_restrictOn hI x g hg),
    fun h g hg => span_on_value_zero hx hg.2 h⟩

private theorem trace_zeroLocus_iff {N H : Set X} (hH : IsClosed H) {x : X} (hx : x∈N) :
    x∈(restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus ↔ x∈H := by
  constructor
  · intro hz
    by_contra hout
    have h1 : (vanishingIdeal (n := n) H).mem x (1 : X → ℂ) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hH.isOpen_compl.mem_nhds hout] with y hy hyH
      exact (hy hyH).elim
    exact one_ne_zero (hz 1 ⟨holomorphicAt_const 1,IsInSpanAt.restrict (isInSpanAt_self h1 (holomorphicAt_const 1))⟩)
  · intro hxH g hg
    exact span_on_value_zero hx hg.2 (fun s hs => hs.2.self_of_nhds hxH)

private theorem zeroLocus_iff_positive_order {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y∈N,IsNonzeroAlongAt N I y)
    {x : X} (hx : x∈N) : x∈I.zeroLocus ↔ 1≤ordinaryTraceOrder N I x := by
  rw [←ordinaryTraceOrder_cosupport_iff hN hI hnz hx 1,
    cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  exact ⟨fun h => ⟨hx,h⟩,fun h => h.2⟩

private theorem actual_family_sum {m : ℕ} {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {x : X} (hx : x ∈ N) :
    ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=∑ i,ordinaryTraceOrder N (F i) x := by
  have hall : ∀ I ∈ List.ofFn F,I.IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N I y) ∧
      ∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,I.mem y a ↔
        HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact ⟨hc i,hnz i,hpr i⟩
  have hh := (relativeIdealListProduct_actual_geometry hN (List.ofFn F)
    (fun I hI => (hall I hI).1) (fun I hI => (hall I hI).2.1) (fun I hI => (hall I hI).2.2)).2.2.2 x hx
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hh


/-- Real finite factor USC and exact sum equality preserve every original
indexed factor, including coincident positions, on the SAME full-value centre. -/
theorem eventually_chronological_factor_orders_eq (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) {C : Set Y}
    (hCN : C⊆(geoTransformAlong (geometricTemplate W []) T).N)
    (hFull : ∀ x∈C,∀ y∈C,(invFamily hn (n+1)).inv (currentProductMarked W E T) .refl x=
      (invFamily hn (n+1)).inv (currentProductMarked W E T) .refl y)
    {x : Y} (hx : x∈C) :
    ∀ᶠ y in 𝓝 x,y∈C → ∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y=
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let J := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hN : IsClosedSubmanifold n N := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (show (geometricTemplate W []).IsWellFormed from
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩) T hT).isClosedSubmanifold_N
  have hg (i : Fin E.length) := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  have hc (i : Fin E.length) : (J i).IsCoherent := (hg i).2.2.2.1.isCoherent
  have hz (i : Fin E.length) : ∀ y∈N,IsNonzeroAlongAt N (J i) y := by
    simpa only [(hg i).1] using (hg i).2.2.2.2.1
  have hp (i : Fin E.length) : ∀ y∈N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
      ∀ g,(J i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
    simpa only [(hg i).1] using (hg i).2.2.2.2.2
  have hBounds : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,
      ordinaryTraceOrder N (J i) y≤ordinaryTraceOrder N (J i) x :=
    eventually_all.mpr fun i => eventually_ordinaryTraceOrder_le hn hN (hc i) (hz i) (hCN hx)
  filter_upwards [hBounds] with y hy hyC
  have hv := congrArg (fun v : ValTy (n+1) => (ofLex v).1) (hFull y hyC x hx)
  change nmOrd (currentProductMarked W E T) y=nmOrd (currentProductMarked W E T) x at hv
  rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT,
    currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT,
    chronological_product_eq_actual_family_product W E T] at hv
  rw [actual_family_sum hN hc hz hp (hCN hyC),
    actual_family_sum hN hc hz hp (hCN hx)] at hv
  exact fun i => factor_eq_of_sum_eq hy hv i

/-- Whole genuine ambient trace dictionaries and SAME actual positive FULL
values internally produce each retained original member's incidence containment. -/
theorem full_value_centre_retained_incidence (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1≤n)
    (hr : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hAmbient : IsSNCDivisor n (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E))
    (hDense : ∀ i : Fin E.length,(geoTransformAlong (geometricTemplate W []) T).N⊆
      closure ((geoTransformAlong (geometricTemplate W []) T).N \ strictAlong T (E.get i)))
    (hNm : ∀ i : Fin E.length,nonmonomialPartAlong n (geoTransformAlong (geometricTemplate W []) T).N
      (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
        (vanishingIdeal (n := n) (strictAlong T (E.get i))))
      (geoTransformAlong (geometricTemplate W []) T).E=
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal)
    {C : Set Y} (hCZ : C⊆chronologicalDistinctDefect W E T)
    (hFull : ∀ x∈C,∀ y∈C,(invFamily hn (n+1)).inv (currentProductMarked W E T) .refl x=
      (invFamily hn (n+1)).inv (currentProductMarked W E T) .refl y) :
    ∀ x∈C,∀ i : Fin E.length,x∈strictAlong T (E.get i) → ∀ᶠ y in 𝓝 x,y∈C → y∈strictAlong T (E.get i) := by
  let M := currentProductMarked W E T
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let B := (geoTransformAlong (geometricTemplate W []) T).E
  have hDom := currentProductMarked_isInvDomain hn hW hE hdense hK hd hr T hT
  have hCN : C⊆N := fun _ hx => (hCZ hx).1
  have hPos : ∀ x∈C,0<nmOrd M x := by
    intro x hx
    rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT]
    have hp := (hCZ hx).2
    rw [←chronological_product_eq_actual_family_product W E T] at hp
    omega
  have hCos : C⊆M.cosupp := fun x hx =>
    (ordinaryTraceOrder_cosupport_iff hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent hDom.isNonzeroAlongAt (hCN hx) 1).mpr (by
        change 1≤ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x
        have hp : 0<nmOrd (currentProductMarked W E T) x := hPos x hx
        rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT] at hp
        exact hp)
  intro x hx i hxi
  let H := strictAlong T (E.get i)
  let I := restrictOn n N (vanishingIdeal (n := n) H)
  let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let D := monomialPartAlong n N I B
  have hHS : IsSNCDivisor n [H] := NormalCrossingsComparison.isSNCDivisor_of_sublist hAmbient
    (List.singleton_sublist.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨E.get i,List.get_mem E i,rfl⟩)))
  have hH : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hHS (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hcI : I.IsCoherent := isCoherent_restrictOn hcH
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hDom.isWellFormed.isClosedSubmanifold_N)
  have hzI : ∀ y∈N,IsNonzeroAlongAt N I y := by
    intro y hy
    obtain ⟨g,hg,hfreq⟩ := HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hHS (hDense i) hy
    exact ⟨g,le_restrictOn hcH y g hg,hfreq⟩
  obtain ⟨hcR,hcD,_hzD,_hmD,_hNo,_hzR,hFactor⟩ := parts_hypotheses hn
    (⟨N,B,I,0⟩ : MarkedIdeal n Y)
    ⟨hDom.isWellFormed.isClosedSubmanifold_N,hcI,hDom.isWellFormed.isSNCDivisor,hDom.isWellFormed.isTransverse⟩ hzI
  have hJ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  have hcJ : J.IsCoherent := hJ.2.2.2.1.isCoherent
  have hzJ : ∀ y∈N,IsNonzeroAlongAt N J y := by simpa only [hJ.1] using hJ.2.2.2.2.1
  have hWhole : I=restrictOn n N (D.mul J) := by
    have he := restrictOn_eq_of_restrictLe hDom.isWellFormed.isClosedSubmanifold_N.1 hFactor.le hFactor.ge
    rw [hNm i,RestrictLeCalculus.mul_comm'] at he
    apply Eq.trans ?_ he
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩,
      fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun s hs => hs.2) hg.2⟩⟩
  have hProper : x∈(D.mul J).zeroLocus := by
    apply (normalized_zeroLocus_iff (isCoherent_mul hcD hcJ) (hCN hx)).mp
    rw [←hWhole]
    exact (trace_zeroLocus_iff hH.1 (hCN hx)).mpr hxi
  have hCases : x∈D.zeroLocus ∨ x∈J.zeroLocus := by
    by_contra h
    exact notMem_zeroLocus_mul hcD hcJ (fun hxD => h (Or.inl hxD)) (fun hxJ => h (Or.inr hxJ)) hProper
  have hZeroToH (y : Y) (hy : y∈N) (hZ : y∈(D.mul J).zeroLocus) : y∈H := by
    apply (trace_zeroLocus_iff hH.1 hy).mp
    change y∈I.zeroLocus
    rw [hWhole]
    exact (normalized_zeroLocus_iff (isCoherent_mul hcD hcJ) hy).mpr hZ
  rcases hCases with hxD | hxJ
  · have hBorn := eventually_born_incidence_of_constant_full_refl hn M hDom hCos hPos hFull hx
    have hBD : ∀ j : Fin B.length,x∈B.get j → ∀ᶠ y in 𝓝 x,y∈C → y∈B.get j :=
      fun j hj => hBorn.mono fun y hy hyC => (hy hyC j).mpr hj
    filter_upwards [eventually_monomial_zeroLocus_of_born_incidence hn hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isSNCDivisor hDom.isWellFormed.isTransverse hcI hzI hCN hx hBD hxD] with y hy hyC
    apply hZeroToH y (hCN hyC)
    rw [RestrictLeCalculus.mul_comm']
    exact zeroLocus_right_subset_mul J D (hy hyC)
  · have hxOrder := (zeroLocus_iff_positive_order hDom.isWellFormed.isClosedSubmanifold_N hcJ hzJ (hCN hx)).mp hxJ
    filter_upwards [eventually_chronological_factor_orders_eq hn hW hE hdense T hT hCN hFull hx] with y hy hyC
    apply hZeroToH y (hCN hyC)
    exact zeroLocus_right_subset_mul D J
      ((zeroLocus_iff_positive_order hDom.isWellFormed.isClosedSubmanifold_N hcJ hzJ (hCN hyC)).mpr (by
        change 1≤ordinaryTraceOrder N J y
        have he : ordinaryTraceOrder N J y=ordinaryTraceOrder N J x := hy hyC i
        rw [he]
        exact hxOrder))

/-- Whole retained-list NC follows from real local incidence containment. -/
theorem full_value_centre_hasNormalCrossings_ambient (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1≤n)
    (hr : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hAmbient : IsSNCDivisor n (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E))
    (hDense : ∀ i : Fin E.length,(geoTransformAlong (geometricTemplate W []) T).N⊆
      closure ((geoTransformAlong (geometricTemplate W []) T).N \ strictAlong T (E.get i)))
    (hNm : ∀ i : Fin E.length,nonmonomialPartAlong n (geoTransformAlong (geometricTemplate W []) T).N
      (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
        (vanishingIdeal (n := n) (strictAlong T (E.get i))))
      (geoTransformAlong (geometricTemplate W []) T).E=
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal)
    {C : Set Y} (hC : IsClosedSubmanifold n C) (hCZ : C⊆chronologicalDistinctDefect W E T)
    (hFull : ∀ x∈C,∀ y∈C,(invFamily hn (n+1)).inv (currentProductMarked W E T) .refl x=
      (invFamily hn (n+1)).inv (currentProductMarked W E T) .refl y) :
    HasNormalCrossings n C (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) := by
  have hOld := full_value_centre_retained_incidence hn hW hE hdense hK hd hr T hT hAmbient hDense hNm hCZ hFull
  have hDom := currentProductMarked_isInvDomain hn hW hE hdense hK hd hr T hT
  have hPos : ∀ x∈C,0<nmOrd (currentProductMarked W E T) x := by
    intro x hx
    rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT]
    have hp := (hCZ hx).2
    rw [←chronological_product_eq_actual_family_product W E T] at hp
    omega
  have hCos : C⊆(currentProductMarked W E T).cosupp := by
    intro x hx
    apply (ordinaryTraceOrder_cosupport_iff hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent hDom.isNonzeroAlongAt (hCZ hx).1 1).mpr
    change 1≤ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) x
    have hp := hPos x hx
    rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT] at hp
    exact hp
  apply hasNormalCrossings_of_eventually_incident_containment hC hAmbient
  intro x hx j hj
  have hm : (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E).get j∈
      E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E := List.get_mem _ j
  rcases List.mem_append.mp hm with hO | hB
  · obtain ⟨K,hK',hKe⟩ := List.mem_map.mp hO
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hK'
    rw [←hKe] at hj ⊢
    exact hOld x hx i hj
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hB
    have hBorn := eventually_born_incidence_of_constant_full_refl hn _ hDom hCos hPos hFull hx
    rw [←hi] at hj ⊢
    exact hBorn.mono fun y hy hyC => (hy hyC i).mpr hj

end
end Hironaka.HironakaSharpActualFullValueAmbientCentre
