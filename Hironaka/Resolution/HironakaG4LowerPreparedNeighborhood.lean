import Hironaka.Resolution.HironakaG4ProtectedResidualEndpoint
import Hironaka.Resolution.HironakaSharpActualAccumulatedTraceResidual

/-! A genuine current lower prepared neighborhood of a processed residual.
Complete source-first proof: hironaka-g4-lower-prepared-neighborhood.tex.
The actual lower old/born partition and whole normal germs are retained.
No future history, selector, comparison or all-other-order premise. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4LowerPreparedNeighborhood

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings NormalCrossingsComparison
  NormalCrossingsInvariance SimultaneousNormalCrossings BlowupFlatCoordinates
  HironakaG4ProtectedResidualEndpoint HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedTowerResidualCompatibility HironakaG4OriginalSelectedResidualTail
  HironakaSharpActualAccumulatedTraceResidual HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  InvertibleIdealQuotient GermIdealOrder MarkedIdealOperationsAlong RestrictLeCalculus RestrictedIdealWeight
  MonomialPartAlong MonomialCaseAlong NonmonomialTransformAlong DivisorExponentAlong MarkedIdeals
  MarkedIdeals.MarkedIdeal IdealWeightPowers

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem member_index_lt_of_dense {C : Set X} {E : List (Set X)}
    (hdense : C ⊆ closure (C \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ C)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (k : ℕ) (s : Fin E.length → Fin n)
    (hC : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k))
    (hH : ∀ i,x ∈ E.get i → ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s i)=0)) :
    ∀ i,x ∈ E.get i → (s i).val < k := by
  intro i hi
  by_contra hnot
  have hge : k ≤ (s i).val := Nat.le_of_not_gt hnot
  let e := (complexChartAt (n := n) x).val
  have hU : IsOpen (e.source ∩ e ⁻¹' Φ.source) :=
    e.continuousOn.isOpen_inter_preimage e.open_source Φ.isOpen_source
  have hxU : x ∈ e.source ∩ e ⁻¹' Φ.source :=
    ⟨mem_complexChartAt_source x,Φ.center_mem_source⟩
  obtain ⟨y,hyU,hyC,hyE⟩ := mem_closure_iff.mp (hdense hx) _ hU hxU
  have hyCoord := (hC hyU.1 hyU.2).mp hyC
  have hyH : y ∈ E.get i := (hH i hi hyU.1 hyU.2).mpr (hyCoord (s i) hge)
  exact hyE (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hyH⟩)

private theorem monomialPart_eq_of_normalized_monomial (hn : 0 < n)
    {N : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {M : GermIdeal n X}
    (hc : M.IsCoherent) (hm : IsMonomialAlong n N M E)
    (hNorm : restrictOn n N M=M) : monomialPartAlong n N M E=M := by
  ext x g
  constructor
  · intro hg
    rw [←hNorm]
    by_cases hx : x ∈ N
    · exact ⟨hg.1,hm x hx g hg⟩
    · exact restrictOn_eq_top_of_disjoint hN.1.isOpen_compl hx (by simp) hg.1
  · exact le_monomialPartAlong hn hE hT hc x g

private theorem restricted_monomial_geometry (hn : 0 < n)
    {L N : Set X} {E : List (Set X)} (hL : IsClosedSubmanifold n L)
    (hN : IsClosedSubmanifold n N) (hLN : L ⊆ N) (hE : IsSNCDivisor n E)
    (hTN : IsTransverse n N E) (hTL : IsTransverse n L E)
    (hdense : L ⊆ closure (L \ ⋃ H ∈ E,H)) {M : GermIdeal n X}
    (hc : M.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N M x)
    (hm : IsMonomialAlong n N M E) :
    (restrictOn n L M).IsCoherent ∧
      (∀ x ∈ L,IsNonzeroAlongAt L (restrictOn n L M) x) ∧
      IsMonomialAlong n L (restrictOn n L M) E := by
  have hcR := isCoherent_restrictOn hc (VanishingIdealCoherent.isCoherent_vanishingIdeal hL)
  refine ⟨hcR,isNonzeroAlongAt_and_isMonomialAlong_of_principal hn hL hE hTL hcR ?_⟩
  intro x hx
  obtain ⟨kL,kN,Φ,s,hsrc,hsN,hsinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn hLN hE hTN hTL.hasNormalCrossings hx
  have hLflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ L ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kL) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hNflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kN) :=
    fun hy hyΦ => (hflat hy hyΦ).2.1
  have hH : ∀ i,x ∈ E.get i → ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s i)=0) :=
    fun i hi _ hy hyΦ => (hflat hy hyΦ).2.2 i hi
  have hsL := member_index_lt_of_dense hdense hx Φ kL s hLflat hH
  let e : Fin E.length → ℕ := fun i => divExpAlong n N M (E.get i) x
  let m : X → ℂ := fun y => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i),
    flatCoord Φ (s i) y ^ e i
  have hgenN : ∀ g,IsInSpanOnAt (n := n) N (M.mem x) x g ↔
      IsInSpanOnAt (n := n) N (·=m) x g :=
    isInSpanOnAt_iff_generator_of_isMonomialAlong hsrc hNflat hH hn hN hE hTN hc hnz hm
      (hLN hx) hsN hsinj
  refine ⟨kL,Φ,s,e,hsrc,hLflat,hsL,hsinj,hH,?_⟩
  intro g
  change IsInSpanOnAt (n := n) L ((restrictOn n L M).mem x) x g ↔
    IsInSpanOnAt (n := n) L (·=m) x g
  constructor
  · intro hg
    have hspan : IsInSpanOnAt (n := n) L (M.mem x) x g :=
      IsInSpanOnAt.trans (fun _ ha => ha.2) hg
    apply IsInSpanOnAt.trans (fun a ha => ?_) hspan
    apply CodimOneCentreAlong.isInSpanOnAt_subset hLN
    exact (hgenN a).mp (IsInSpanAt.restrict
      (isInSpanAt_self ha (GermIdeal.IsCoherent.holomorphicAt_mem hc ha)))
  · intro hg
    apply IsInSpanOnAt.trans (fun a ha => ?_) hg
    rw [ha]
    have hspanN : IsInSpanOnAt (n := n) N (M.mem x) x m :=
      (hgenN m).mpr (isInSpanOnAt_eq_iff.mpr
        ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩)
    exact IsInSpanOnAt.mono (fun b hb => le_restrictOn hc x b hb)
      (CodimOneCentreAlong.isInSpanOnAt_subset hLN hspanN)

private theorem bounded_order_one_dimensions {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hc : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) {x : X}
    (hx : x ∈ N ∩ I.zeroLocus)
    (hpr : ∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hOrd : ordinaryTraceOrder N I x=1)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (kC kN : ℕ)
    (hCflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ∩ I.zeroLocus ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kC))
    (hNflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kN)) :
    min kN n=min kC n+1 := by
  have hRegN : RegularAtDim (n := n) N x (min kN n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun hy hyΦ => by rw [BoundaryCount.complexCoordinatePlane_min];exact hNflat hy hyΦ)
      hx.1 (mem_complexChartAt_source x) Φ.center_mem_source
  have hRegC : RegularAtDim (n := n) (N ∩ I.zeroLocus) x (min kC n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun hy hyΦ => by rw [BoundaryCount.complexCoordinatePlane_min];exact hCflat hy hyΦ)
      hx (mem_complexChartAt_source x) Φ.center_mem_source
  have hPos : 0 < min kN n := by
    by_contra hnot
    have he : min kN n=0 := by omega
    rw [he] at hRegN
    obtain ⟨O,hOo,hxO,hIso⟩ :=
      PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hRegN
    obtain ⟨g,hg,hFreq⟩ := hnz x hx.1
    obtain ⟨y,⟨hyN,hgy⟩,hyO⟩ := (hFreq.and_eventually (hOo.mem_nhds hxO)).exists
    have hyx : y=x := Set.mem_singleton_iff.mp (hIso ⟨hyN,hyO⟩)
    apply hgy
    rw [hyx]
    exact hx.2 g hg
  obtain ⟨f,hf,hgen⟩ := hpr
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,_hRed,k,hNk,hCk⟩ :=
    HironakaSharpActualPrincipalOrderOneTrace.actual_orderOne_relative_reduced_trace
      hN hc hnz hx.1 f hf hgen hOrd
  have hk : k=min kN n := RegularPointDimension.eq_of_regularAtDim hNk hRegN
  have hCdim : min kC n=k-1 := RegularPointDimension.eq_of_regularAtDim hRegC hCk
  omega

private theorem exists_centered_nested_chart_from_transverse_window (hn : 0 < n)
    {C N : Set X} {E : List (Set X)} (hCN : C ⊆ N)
    (hE : IsSNCDivisor n E) (hCNC : HasNormalCrossings n C E)
    {x : X} (hx : x ∈ C) (U : Opens X) (hxU : x ∈ U)
    (hTrU : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))) :
    ∃ (kC kN : ℕ)
      (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
      (s : Fin E.length → Fin n),
      kC ≤ n ∧ kN ≤ n ∧ Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x)=0 ∧
      (∀ i,x ∈ E.get i → (s i).val < kN) ∧ Set.InjOn s {i | x ∈ E.get i} ∧
      ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kC) ∧
        (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kN) ∧
        ∀ i,x ∈ E.get i →
          (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s i)=0) := by
  let u : U := ⟨x,hxU⟩
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let c : Fin E.length → Fin EU.length := Fin.cast (List.length_map _).symm
  have hget (i : Fin E.length) : EU.get (c i)=(Subtype.val : U → X) ⁻¹' E.get i := by
    simp [EU,c,List.get_eq_getElem]
  have hEU : IsSNCDivisor n EU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hCNCU := hasNormalCrossings_preimage (pullsBackCoordinates_val U) hCNC
  obtain ⟨a,b,Ψ,s₀,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (preimage_mono hCN) hEU hTrU hCNCU (x := u) hx
  let QC : Finset (Fin n) := Finset.univ.filter fun t : Fin n => a ≤ t.val
  let QN : Finset (Fin n) := Finset.univ.filter fun t : Fin n => b ≤ t.val
  let A : Option (Option (Fin E.length)) → Set X :=
    fun o => o.elim C (fun p => p.elim N E.get)
  let S : Option (Option (Fin E.length)) → Finset (Fin n) :=
    fun o => o.elim QC (fun p => p.elim QN (fun i => {s₀ (c i)}))
  have hFamilyFlat : ∀ o,u ∈ (Subtype.val : U → X) ⁻¹' A o → ∀ {z : U},
      z ∈ (complexChartAt (n := n) u).val.source →
      (complexChartAt (n := n) u).val z ∈ Ψ.source →
      (z ∈ (Subtype.val : U → X) ⁻¹' A o ↔
        Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace (S o)) := by
    rintro (_ | (_ | i)) hi z hz hzΨ
    · change (z.val ∈ C ↔ Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace QC)
      simp only [QC,coordSubspace_eq_complexCoordinatePlane]
      exact (hflat hz hzΨ).1
    · change (z.val ∈ N ↔ Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace QN)
      simp only [QN,coordSubspace_eq_complexCoordinatePlane]
      exact (hflat hz hzΨ).2.1
    · change (z.val ∈ E.get i ↔
        Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace {s₀ (c i)})
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have hiU : u ∈ EU.get (c i) := by rw [hget];exact hi
      have hh := (hflat hz hzΨ).2.2 (c i) hiU
      rw [hget] at hh
      exact hh
  have hFamilyU : IsCoordinateFamilyAt n
      (fun o => (Subtype.val : U → X) ⁻¹' A o) S u :=
    coordinateFamilyAt_of_flattening Ψ hFamilyFlat
      (mem_complexChartAt_source u) Ψ.center_mem_source (fun _ hi => hi)
  have hFamilyX : IsCoordinateFamilyAt n A S x := isCoordinateFamilyAt_preimage_val_iff.mp hFamilyU
  obtain ⟨Φ,hΦsrc,hΦ0,hΦ⟩ := hFamilyX
  refine ⟨min a n,min b n,Φ,(fun i => s₀ (c i)),min_le_right _ _,min_le_right _ _,
    hΦsrc,hΦ0,?_,?_,?_⟩
  · intro i hi
    have hiU : u ∈ EU.get (c i) := by rw [hget];exact hi
    exact lt_min (hs (c i) hiU) (s₀ (c i)).isLt
  · intro i hi j hj heq
    have hiU : u ∈ EU.get (c i) := by rw [hget];exact hi
    have hjU : u ∈ EU.get (c j) := by rw [hget];exact hj
    have hc := hinj hiU hjU heq
    exact Fin.ext (by simpa [c] using congrArg Fin.val hc)
  · intro y hy hyΦ
    refine ⟨?_,?_,?_⟩
    · rw [BoundaryCount.complexCoordinatePlane_min]
      have hh := hΦ none hx hy hyΦ
      change (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QC) at hh
      simpa only [QC,coordSubspace_eq_complexCoordinatePlane] using hh
    · rw [BoundaryCount.complexCoordinatePlane_min]
      have hh := hΦ (some none) (hCN hx) hy hyΦ
      change (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QN) at hh
      simpa only [QN,coordSubspace_eq_complexCoordinatePlane] using hh
    · intro i hi
      have hh := hΦ (some (some i)) hi hy hyΦ
      change (y ∈ E.get i ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s₀ (c i)}) at hh
      simpa only [BlowupSNCTransform.mem_coordSubspace_singleton] using hh

private theorem actual_processed_nested_chart
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
    {x : Y} (hx : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
      (s : Fin F.length → Fin n),
      k+1 ≤ n ∧ Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x)=0 ∧
      (∀ a,x ∈ F.get a → (s a).val < k) ∧ Set.InjOn s {a | x ∈ F.get a} ∧
      ∀ {y : Y},y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ S ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k) ∧
        (y ∈ A.N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n (k+1)) ∧
        ∀ a,x ∈ F.get a →
          (y ∈ F.get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s a)=0) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let S := A.N ∩ I.zeroLocus
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
  obtain ⟨hNi,_hEi,_hdi,hwi,hnzi,hpri⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  rw [hNi] at hOrd hx hnzi hpri
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hRecorded.2.1
    ((List.eraseIdx_sublist (E.map (strictAlong T)) i.val).append (List.Sublist.refl A.E))
  obtain ⟨_hS,_hWhole,hWindows,_hLocal,_hDisjoint⟩ :=
    actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull hOrd hNC hDenseS
  obtain ⟨U,hxU,_hEU,hTransU⟩ := hWindows x hx
  obtain ⟨kC,kN,Φ,s,hkC,hkN,hsrc,h0,_hsN,hinj,hflat⟩ :=
    exists_centered_nested_chart_from_transverse_window hn inter_subset_left hF hNC hx U hxU hTransU
  have hCflat := fun {y : Y} hy hyΦ => (hflat (y := y) hy hyΦ).1
  have hNflat := fun {y : Y} hy hyΦ => (hflat (y := y) hy hyΦ).2.1
  have hHflat := fun a ha {y : Y} hy hyΦ => (hflat (y := y) hy hyΦ).2.2 a ha
  have hcos : x ∈ cosupport n A.N I 1 := by
    rw [GermIdealOrder.cosupport_one (fun _ _ hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem hwi.isCoherent hg)]
    exact hx
  have hLower := (ordinaryTraceOrder_cosupport_iff hN hwi.isCoherent hnzi hx.1 1).mp hcos
  have hOne : ordinaryTraceOrder A.N I x=1 := (hOrd x hx.1).antisymm hLower
  have hDim := bounded_order_one_dimensions hN hwi.isCoherent hnzi hx (hpri x hx.1)
    hOne Φ kC kN hCflat hNflat
  simp only [min_eq_left hkC,min_eq_left hkN] at hDim
  have hsC := member_index_lt_of_dense hDenseS hx Φ kC s hCflat hHflat
  refine ⟨kC,Φ,s,by omega,hsrc,h0,hsC,hinj,?_⟩
  intro y hy hyΦ
  rw [←hDim]
  exact hflat hy hyΦ

private def postcompose_linear_chart {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (e : ComplexModel n ≃L[ℂ] ComplexModel n) :
    LocalHolomorphicEquivAt (n := n) p where
  source := Φ.source
  target := e.symm ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source
  isOpen_target := Φ.isOpen_target.preimage e.symm.continuous
  center_mem_source := Φ.center_mem_source
  toFun := fun z => e (Φ.toFun z)
  invFun := fun z => Φ.invFun (e.symm z)
  toFun_holomorphic := e.differentiable.comp_differentiableOn Φ.toFun_holomorphic
  invFun_holomorphic := Φ.invFun_holomorphic.comp e.symm.differentiable.differentiableOn
    (fun _ hz => hz)
  mapsTo_toFun := fun z hz => by
    change e.symm (e (Φ.toFun z)) ∈ Φ.target
    simpa only [e.symm_apply_apply] using Φ.mapsTo_toFun hz
  mapsTo_invFun := fun _ hz => Φ.mapsTo_invFun hz
  left_inv := fun z hz => by
    rw [e.symm_apply_apply]
    exact Φ.left_inv z hz
  right_inv := fun z hz => by
    rw [Φ.right_inv (e.symm z) hz,e.apply_symm_apply]

private def swapped_chart {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (a b : Fin n) :
    LocalHolomorphicEquivAt (n := n) p :=
  postcompose_linear_chart Φ
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap a b).symm).toContinuousLinearEquiv

private theorem swapped_chart_apply {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (a b t : Fin n) (z : ComplexModel n) :
    (swapped_chart Φ a b).toFun z t=Φ.toFun z (Equiv.swap a b t) := rfl

private theorem swapped_chart_plane {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) {k : ℕ} {a b : Fin n}
    (ha : a.val < k) (hb : b.val < k) (z : ComplexModel n) :
    (swapped_chart Φ a b).toFun z ∈ complexCoordinatePlane n k ↔
      Φ.toFun z ∈ complexCoordinatePlane n k := by
  have hfix (t : Fin n) (ht : k ≤ t.val) : Equiv.swap a b t=t := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro heq
    · have hh := congrArg Fin.val heq
      omega
    · have hh := congrArg Fin.val heq
      omega
  constructor <;> intro hz t ht
  · have hh := hz t ht
    rwa [swapped_chart_apply,hfix t ht] at hh
  · rw [swapped_chart_apply,hfix t ht]
    exact hz t ht

private theorem swapped_chart_codim_one_plane {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) {k : ℕ} (hk : k < n)
    {a : Fin n} (ha : a.val < k) (z : ComplexModel n) :
    (swapped_chart Φ a ⟨k,hk⟩).toFun z ∈ complexCoordinatePlane n k ↔
      Φ.toFun z ∈ complexCoordinatePlane n (k+1) ∧ Φ.toFun z a=0 := by
  let r : Fin n := ⟨k,hk⟩
  constructor
  · intro hz
    refine ⟨?_,?_⟩
    · apply (swapped_chart_plane Φ (k := k+1) (a := a) (b := r)
        (by omega) (by dsimp [r];omega) z).mp
      intro t ht
      exact hz t (by omega)
    · have hh := hz r (by simp [r])
      simpa only [r,swapped_chart_apply,Equiv.swap_apply_right] using hh
  · rintro ⟨hz,hza⟩ t ht
    by_cases htk : t.val=k
    · have htr : t=r := Fin.ext htk
      subst t
      simpa only [r,swapped_chart_apply,Equiv.swap_apply_right] using hza
    · have hta : t ≠ a := by intro he;have hv := congrArg Fin.val he;omega
      have htr : t ≠ r := fun he => htk (congrArg Fin.val he)
      rw [swapped_chart_apply,Equiv.swap_apply_of_ne_of_ne hta htr]
      exact hz t (by omega)

private theorem swapped_chart_old_plane {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) {k : ℕ} (hk : k < n)
    {a : Fin n} (ha : a.val < k) (z : ComplexModel n) :
    Φ.toFun z ∈ complexCoordinatePlane n k ↔
      (swapped_chart Φ a ⟨k,hk⟩).toFun z ∈ complexCoordinatePlane n (k+1) ∧
        (swapped_chart Φ a ⟨k,hk⟩).toFun z a=0 := by
  have hswap := swapped_chart_plane Φ (k := k+1) (a := a) (b := ⟨k,hk⟩) (by omega)
    (show (⟨k,hk⟩ : Fin n).val < k+1 by simp) z
  rw [hswap,swapped_chart_apply,Equiv.swap_apply_left]
  constructor
  · intro hz
    exact ⟨fun t ht => hz t (by omega),hz ⟨k,hk⟩ le_rfl⟩
  · rintro ⟨hz,hzr⟩ t ht
    by_cases htk : t.val=k
    · exact (congrArg (fun t : Fin n => Φ.toFun z t) (Fin.ext htk)).trans hzr
    · exact hz t (by omega)

private theorem exists_lower_coordinate_window {C N Z : Set X} {E : List (Set X)}
    (hClosed : ∀ H ∈ E,IsClosed H) {x : X}
    (k : ℕ) (hk : k+1 ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (s : Fin E.length → Fin n)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x)=0)
    (hs : ∀ a,x ∈ E.get a → (s a).val < k) (hinj : Set.InjOn s {a | x ∈ E.get a})
    (hflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k) ∧
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n (k+1)) ∧
      ∀ a,x ∈ E.get a →
        (y ∈ E.get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s a)=0))
    (j : Fin E.length) (hxj : x ∈ E.get j)
    (hZ : ∀ᶠ y in 𝓝 x,y ∈ Z ↔ y ∈ N ∩ E.get j) :
    ∃ (U : Opens X) (Θ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
      x ∈ U ∧ (U : Set X) ⊆ flatDomain Θ ∧ flatDomain Θ ⊆ (U : Set X) ∧
      Θ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Θ.toFun ((complexChartAt (n := n) x).val x)=0 ∧
      ∀ y : U,
        (y.val ∈ N ↔ Θ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n (k+1)) ∧
        (y.val ∈ Z ↔ Θ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n k) ∧
        (y.val ∈ C ↔ Θ.toFun ((complexChartAt (n := n) x).val y.val) ∈
          complexCoordinatePlane n (k+1) ∧ flatCoord Θ (s j) y.val=0) ∧
        (∀ a,a ≠ j →
          (y.val ∈ E.get a ↔ x ∈ E.get a ∧ flatCoord Θ (s a) y.val=0)) ∧
        (y.val ∈ Z ↔ y.val ∈ N ∩ E.get j) := by
  let r : Fin n := ⟨k,by omega⟩
  let Θ := swapped_chart Φ (s j) r
  have hsj := hs j hxj
  have hseen := eventually_incident_subset E.get (fun a => hClosed _ (List.get_mem E a)) x
  have hData : ∀ᶠ y in 𝓝 x,y ∈ flatDomain Φ ∧
      (y ∈ Z ↔ y ∈ N ∩ E.get j) ∧ ∀ a,y ∈ E.get a → x ∈ E.get a := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),hZ,hseen]
      with y hy hZy hsy
    exact ⟨hy,hZy,hsy⟩
  obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp hData
  let U : Opens X := ⟨V,hVo⟩
  let e := (complexChartAt (n := n) x).val
  let P : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (U : Set X)
  have hPo : IsOpen P := e.continuousOn_symm.isOpen_inter_preimage e.open_target U.isOpen
  have hxp : e x ∈ Θ.source ∩ P := by
    refine ⟨Θ.center_mem_source,e.map_source (mem_complexChartAt_source x),?_⟩
    change e.symm (e x) ∈ U
    rw [e.left_inv (mem_complexChartAt_source x)]
    exact hxV
  let Θ' := Θ.restrict P hPo (e x) hxp
  have hU : (U : Set X) ⊆ flatDomain Θ' := by
    intro y hy
    have hyD := (hVsub hy).1
    refine ⟨hyD.1,hyD.2,e.map_source hyD.1,?_⟩
    change e.symm (e y) ∈ U
    rw [e.left_inv hyD.1]
    exact hy
  have hDomain : flatDomain Θ' ⊆ (U : Set X) := by
    intro y hy
    have hh := hy.2.2.2
    change e.symm (e y) ∈ U at hh
    rwa [e.left_inv hy.1] at hh
  refine ⟨U,Θ',hxV,hU,hDomain,(fun _ hz => hsrc hz.1),?_,?_⟩
  · change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.swap (s j) r).symm).toContinuousLinearEquiv
        (Φ.toFun ((complexChartAt (n := n) x).val x))=0
    rw [h0,map_zero]
  · intro y
    have hyD := (hVsub y.property).1
    have hyF := hflat hyD.1 hyD.2
    have hNswap := swapped_chart_plane Φ (k := k+1) (a := s j) (b := r)
      (by omega) (by dsimp [r];omega) ((complexChartAt (n := n) x).val y.val)
    have hZswap := swapped_chart_codim_one_plane Φ r.isLt hsj
      ((complexChartAt (n := n) x).val y.val)
    have hCswap := swapped_chart_old_plane Φ r.isLt hsj
      ((complexChartAt (n := n) x).val y.val)
    refine ⟨hyF.2.1.trans hNswap.symm,?_,hyF.1.trans hCswap,?_,(hVsub y.property).2.1⟩
    · exact (hVsub y.property).2.1.trans ((and_congr hyF.2.1 (hyF.2.2 j hxj)).trans hZswap.symm)
    · intro a hne
      by_cases hxa : x ∈ E.get a
      · have hsa : s a ≠ s j := fun he => hne (hinj hxa hxj he)
        have hsr : s a ≠ r := by
          intro he
          have hh := congrArg Fin.val he
          have hsa' := hs a hxa
          dsimp [r] at hh
          omega
        change y.val ∈ E.get a ↔ x ∈ E.get a ∧
          (swapped_chart Φ (s j) r).toFun ((complexChartAt (n := n) x).val y.val) (s a)=0
        rw [swapped_chart_apply,Equiv.swap_apply_of_ne_of_ne hsa hsr]
        simpa only [hxa,true_and] using hyF.2.2 a hxa
      · exact iff_of_false (fun hy => hxa ((hVsub y.property).2.2 a hy))
          (fun hy => hxa hy.1)

private theorem actual_original_lower_coordinate_frame
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
    (j : Fin E.length) (hne : j ≠ i) {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let Sj := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
    ∃ (k : ℕ) (s : Fin F.length → Fin n) (a : Fin F.length) (U : Opens Y)
      (Θ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
      0 < k ∧ k+1 ≤ n ∧ F.get a=strictAlong T (E.get j) ∧
      (∀ b,x ∈ F.get b → (s b).val < k) ∧ Set.InjOn s {b | x ∈ F.get b} ∧
      x ∈ F.get a ∧ x ∈ U ∧ (U : Set Y) ⊆ flatDomain Θ ∧ flatDomain Θ ⊆ (U : Set Y) ∧
      Θ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Θ.toFun ((complexChartAt (n := n) x).val x)=0 ∧
      ∀ y : U,
        (y.val ∈ A.N ↔ Θ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n (k+1)) ∧
        (y.val ∈ Sj ↔ Θ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n k) ∧
        (y.val ∈ Si ↔ Θ.toFun ((complexChartAt (n := n) x).val y.val) ∈
          complexCoordinatePlane n (k+1) ∧ flatCoord Θ (s a) y.val=0) ∧
        (∀ b,b ≠ a →
          (y.val ∈ F.get b ↔ x ∈ F.get b ∧ flatCoord Θ (s b) y.val=0)) ∧
        (y.val ∈ Sj ↔ y.val ∈ A.N ∩ F.get a) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let F := old.eraseIdx i.val ++ A.E
  let J := fun h : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  let Sj := A.N ∩ (J j).zeroLocus
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hNi := (chronologicalMarked_geometric_fields
    (originalRelativeMemberMarked W (E.get i)) T).1
  have hNj := (chronologicalMarked_geometric_fields
    (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N=A.N at hNj
  have hOrdA : ∀ y ∈ A.N,ordinaryTraceOrder A.N (J i) y ≤ 1 := by
    simpa only [hNi] using hOrd
  have hxiA : x ∈ Si := by simpa only [hNi] using hxi
  have hxjA : x ∈ Sj := by simpa only [hNj] using hxj
  have hProtect := actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull
    hOrdA hNC hDenseS
  let oj : Fin old.length := ⟨j.val,by simpa only [old,List.length_map] using j.isLt⟩
  have hGet : old.get oj=strictAlong T (E.get j) := by simp [old,oj]
  have hMem : strictAlong T (E.get j) ∈ F := by
    apply List.mem_append_left
    rw [←hGet]
    exact List.mem_eraseIdx_iff_getElem.mpr
      ⟨oj.val,oj.isLt,fun he => hne (Fin.ext he),rfl⟩
  obtain ⟨a,ha⟩ := List.mem_iff_get.mp hMem
  have hOldSNC := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left old A.E)
  have hH : IsClosedSubmanifold n (strictAlong T (E.get j)) := by
    rw [←hGet]
    exact MonomialPart.isClosedSubmanifold_get hn hOldSNC oj
  have hSets : ∀ᶠ y in 𝓝 x,y ∈ Sj ↔ y ∈ A.N ∩ strictAlong T (E.get j) :=
    support_near_of_whole_trace_germ hH
      ((hProtect.2.2.2.1 j hne x hxiA).mono (fun _ hy => hy.2))
  have hxa : x ∈ F.get a := by
    rw [ha]
    exact (hSets.self_of_nhds.mp hxjA).2
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hRecorded.2.1
    ((List.eraseIdx_sublist old i.val).append (List.Sublist.refl A.E))
  obtain ⟨k,Φ,s,hk,hsrc,h0,hs,hinj,hflat⟩ :=
    actual_processed_nested_chart hn hW hE hdense i T hT hFull hOrd hNC hDenseS hxi
  have hZa : ∀ᶠ y in 𝓝 x,y ∈ Sj ↔ y ∈ A.N ∩ F.get a := by
    simpa only [ha] using hSets
  obtain ⟨U,Θ,hxU,hU,hDomain,hΘsrc,hΘ0,hFinal⟩ :=
    exists_lower_coordinate_window hF.1 k hk Φ s hsrc h0 hs hinj hflat a hxa hZa
  have hka := hs a hxa
  exact ⟨k,s,a,U,Θ,by omega,hk,ha,hs,hinj,hxa,hxU,hU,hDomain,hΘsrc,hΘ0,hFinal⟩

private theorem closedSmooth_on_coordinate_window {Z : Set X} (hZ : IsClosed Z)
    {x : X} (k : ℕ) (hk : k ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ) (hDomain : flatDomain Φ ⊆ (U : Set X))
    (hFlat : ∀ y : U,y.val ∈ Z ↔
      Φ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n k) :
    IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' Z) := by
  refine ⟨hZ.preimage continuous_subtype_val,fun y hy => ⟨k,?_⟩⟩
  apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
  exact RegularPatchNeighborhood.regularAtDim_of_flattening hk Φ
    (fun hz hzΦ => hFlat ⟨_,hDomain ⟨hz,hzΦ⟩⟩) hy (hU y.property).1 (hU y.property).2

private theorem transverse_on_coordinate_window {Z : Set X} {E : List (Set X)}
    {x : X} (hxZ : x ∈ Z) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (s : Fin E.length → Fin n)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ) (hDomain : flatDomain Φ ⊆ (U : Set X))
    (hZflat : ∀ y : U,y.val ∈ Z ↔
      Φ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n k)
    (hEflat : ∀ y : U,∀ a,y.val ∈ E.get a ↔ x ∈ E.get a ∧ flatCoord Φ (s a) y.val=0)
    (hFree : ∀ a,x ∈ E.get a → (s a).val < k) :
    IsTransverse n ((Subtype.val : U → X) ⁻¹' Z)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) := by
  let Q : Finset (Fin n) := Finset.univ.filter fun t : Fin n => k ≤ t.val
  let A : Option (Fin E.length) → Set X := fun o => o.elim Z E.get
  let S : Option (Fin E.length) → Finset (Fin n) := fun o => o.elim Q (fun a => {s a})
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let c : Fin EU.length → Fin E.length := Fin.cast (List.length_map _)
  have hget (a : Fin EU.length) : EU.get a=(Subtype.val : U → X) ⁻¹' E.get (c a) := by
    simp only [EU,c,List.get_eq_getElem,List.getElem_map,Fin.val_cast]
  have hflat : ∀ o,x ∈ A o → ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ A o ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S o)) := by
    rintro (_ | a) hi y hy hyΦ
    · simpa only [A,S,Option.elim,Q,coordSubspace_eq_complexCoordinatePlane] using
        hZflat ⟨y,hDomain ⟨hy,hyΦ⟩⟩
    · change x ∈ E.get a at hi
      change y ∈ E.get a ↔ _
      simpa only [S,Option.elim,BlowupSNCTransform.mem_coordSubspace_singleton,hi,true_and,flatCoord,complexChartAt] using
        hEflat ⟨y,hDomain ⟨hy,hyΦ⟩⟩ a
  intro y hyZ
  have hseen : ∀ o,y.val ∈ A o → x ∈ A o := by
    rintro (_ | a) hi
    · exact hxZ
    · exact ((hEflat y a).mp hi).1
  have hFamily := isCoordinateFamilyAt_preimage_val_iff.mpr
    (coordinateFamilyAt_of_flattening Φ hflat (hU y.property).1 (hU y.property).2 hseen)
  refine ⟨Q,fun a => {s (c a)},?_,?_⟩
  · exact IsCoordinateFamilyAt.reindex hFamily (Option.map c)
      (by rintro (_ | a);rfl;exact hget a) (by rintro (_ | a) <;> rfl)
  · intro a ha
    have haE : y.val ∈ E.get (c a) := by rwa [hget] at ha
    have hxE := ((hEflat y (c a)).mp haE).1
    refine ⟨Finset.card_singleton _,Finset.disjoint_left.mpr ?_⟩
    intro t ht htQ
    rw [Finset.mem_singleton.mp ht] at htQ
    exact Nat.not_lt_of_ge (Finset.mem_filter.mp htQ).2 (hFree (c a) hxE)

private theorem normalized_coordinate_member_trace_mem_iff {N H : Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (Q : Finset (Fin n)) (p : Fin n) (hp : p ∉ Q)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x)=0)
    (hNflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q))
    (hHflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ H ↔ Φ.toFun ((complexChartAt (n := n) x).val y) p=0)) (g : X → ℂ) :
    (restrictOn n N (vanishingIdeal (n := n) H)).mem x g ↔
      (vanishingIdeal (n := n) (N ∩ H)).mem x g := by
  have hRflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ∩ H ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (Q ∪ {p})) := by
    intro y hy hyΦ
    rw [ExceptionalPushforwardAlong.coordSubspace_union]
    change (y ∈ N ∧ y ∈ H) ↔
      Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {p}
    rw [BlowupSNCTransform.mem_coordSubspace_singleton]
    exact and_congr (hNflat hy hyΦ) (hHflat hy hyΦ)
  have hf : HolomorphicAt n (flatCoord Φ p) x := holomorphicAt_flatCoord Φ p (mem_flatDomain_self Φ)
  have hHwhole := fun a : X → ℂ =>
    MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ hHflat (mem_flatDomain_self Φ) a
  have hTrace : (restrictOn n N (vanishingIdeal (n := n) H)).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=flatCoord Φ p) x g :=
    and_congr_right fun _ => HironakaSharpOriginalMemberProduct.restricted_span_iff_principal
      hf hHwhole g
  exact hTrace.trans (vanishingIdeal_coordinate_trace_mem_iff Φ Q p hp hsrc h0 hNflat hRflat g).symm

private theorem normalized_vanishingIdeal_of_subset {R L : Set X} (hRL : R ⊆ L) :
    restrictOn n L (vanishingIdeal (n := n) R)=vanishingIdeal (n := n) R := by
  ext x g
  exact ⟨fun hg => MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt hRL hg.1 hg.2,
    fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩

private theorem canonical_parts_of_actual_reduced_factor (hn : 0 < n)
    {L R : Set X} {B : List (Set X)} (hL : IsClosedSubmanifold n L)
    (hR : IsClosedSubmanifold n R) (hRL : R ⊆ L)
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n L B)
    {I M : GermIdeal n X} (hcM : M.IsCoherent)
    (hnzM : ∀ x ∈ L,IsNonzeroAlongAt L M x) (hmM : IsMonomialAlong n L M B)
    (hNormM : restrictOn n L M=M)
    (hnzR : ∀ x ∈ L,IsNonzeroAlongAt L (vanishingIdeal (n := n) R) x)
    (hNoR : ∀ x ∈ L,∀ b : Fin B.length,x ∈ B.get b →
      ∃ f,(vanishingIdeal (n := n) R).mem x f ∧
        ¬IsInSpanOnAt (n := n) L ((vanishingIdeal (n := n) (B.get b)).mem x) x f)
    (hWhole : I=restrictOn n L (M.mul (vanishingIdeal (n := n) R))) :
    monomialPartAlong n L I B=M ∧
      nonmonomialPartAlong n L I B=vanishingIdeal (n := n) R := by
  let K := vanishingIdeal (n := n) R
  have hcK : K.IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal hR
  have hWhole' : I=restrictOn n L (K.mul M) := by
    rw [hWhole,RestrictLeCalculus.mul_comm' M K]
  have hf : RestrictLe L I (K.mul M) := by
    rw [hWhole']
    exact restrictLe_restrictOn
  have hb : RestrictLe L (K.mul M) I := by
    rw [hWhole']
    exact restrictLe_self_restrictOn (isCoherent_mul hcK hcM)
  have hD := (monomialPartAlong_eq_of_factor hn hL hB hTr hcK hcM hNoR hf hb).trans
    (monomialPart_eq_of_normalized_monomial hn hL hB hTr hcM hmM hNormM)
  have hNmK : nonmonomialPartAlong n L K B=K :=
    (HironakaSharpActualChronologicalResidualDictionary.nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
      hL hB hTr hcK hNoR).trans (normalized_vanishingIdeal_of_subset hRL)
  refine ⟨hD,?_⟩
  rw [hWhole]
  exact (actual_normalized_monomial_product_nonmonomial_eq hn hL hB hTr hcM hcK hnzM hnzR hmM).trans hNmK

private theorem coordinate_nonzero_along_at {L : Set X} {I : GermIdeal n X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (Q : Finset (Fin n)) (p : Fin n) (hp : p ∉ Q)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x)=0)
    (hLflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ L ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q))
    (hg : I.mem x (flatCoord Φ p)) : IsNonzeroAlongAt L I x := by
  refine ⟨flatCoord Φ p,hg,?_⟩
  apply (MonomialPart.frequently_flatMap_ne_zero hsrc (mem_flatDomain_self Φ) {p}).mono
  rintro y ⟨hyD,hyne,hyKeep⟩
  refine ⟨(hLflat hyD.1 hyD.2).mpr ?_,hyne p (Finset.mem_singleton_self p)⟩
  intro t ht
  have htp : t ≠ p := fun he => hp (he ▸ ht)
  have hh := hyKeep t (by simpa only [Finset.mem_singleton] using htp)
  change Φ.toFun ((complexChartAt (n := n) x).val y) t=
    Φ.toFun ((complexChartAt (n := n) x).val x) t at hh
  rw [hh,h0]
  rfl

private theorem coordinate_member_order_le_one_at {L : Set X} (hL : IsClosedSubmanifold n L)
    {I : GermIdeal n X} (hcI : I.IsCoherent)
    (hnzI : ∀ z ∈ L,IsNonzeroAlongAt L I z) {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (k : ℕ) (p : Fin n) (hp : p.val < k)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (hLflat : ∀ {z : X},z ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val z ∈ Φ.source →
      (z ∈ L ↔ Φ.toFun ((complexChartAt (n := n) x).val z) ∈ complexCoordinatePlane n k))
    {y : X} (hyD : y ∈ flatDomain Φ) (hyL : y ∈ L)
    (hmem : I.mem y (flatCoord Φ p)) : ordinaryTraceOrder L I y ≤ 1 := by
  have hr := isLocalRetraction_flatRetract hsrc hLflat hyD hyL
  have hcomp : (flatCoord Φ p) ∘ flatRetract Φ k =ᶠ[𝓝 y] flatCoord Φ p := by
    filter_upwards [eventually_flatMap_flatRetract hsrc hLflat hyD hyL hp] with z hz
    exact hz.2
  have hnot : y ∉ cosupport n L I 2 := by
    intro hyC
    apply MonomialCase.flatCoord_notMem_idealPow_two Φ p hyD
    exact OrderTaylor.mem_idealPow_congr (hr.vanishesToOrderOn_iff.mp (hyC.2 _ hmem)) hcomp
  have hlt : ¬2 ≤ ordinaryTraceOrder L I y :=
    fun he => hnot ((ordinaryTraceOrder_cosupport_iff hL hcI hnzI hyL 2).mpr he)
  omega

private theorem coordinate_trace_no_born_factor_at {L R : Set X} {B : List (Set X)}
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n L B) {x : X} (hxL : x ∈ L)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (Q : Finset (Fin n)) (p q : Fin n) (hp : p ∉ Q) (hpq : p ≠ q)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x)=0)
    (hLflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ L ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q))
    (hRflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ R ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (Q ∪ {p})))
    (b : Fin B.length)
    (hBflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ L ∩ B.get b ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (Q ∪ {q}))) :
    ∃ f,(vanishingIdeal (n := n) R).mem x f ∧
      ¬IsInSpanOnAt (n := n) L ((vanishingIdeal (n := n) (B.get b)).mem x) x f := by
  let f := flatCoord Φ p
  have hf : HolomorphicAt n f x := holomorphicAt_flatCoord Φ p (mem_flatDomain_self Φ)
  have hfR : (vanishingIdeal (n := n) R).mem x f :=
    (vanishingIdeal_coordinate_trace_mem_iff Φ Q p hp hsrc h0 hLflat hRflat f).mpr
      ⟨hf,isInSpanOnAt_eq_iff.mpr
        ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp [f]⟩⟩
  refine ⟨f,hfR,fun hspan => ?_⟩
  have hvan := (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem hB hTr hxL b hf).mp hspan
  have hFreq : ∃ᶠ y in 𝓝 x,y ∈ L ∩ B.get b ∧ f y ≠ 0 := by
    apply (MonomialPart.frequently_flatMap_ne_zero hsrc (mem_flatDomain_self Φ) {p}).mono
    rintro y ⟨hyD,hyne,hyKeep⟩
    refine ⟨(hBflat hyD.1 hyD.2).mpr ?_,hyne p (Finset.mem_singleton_self p)⟩
    have hZero (t : Fin n) (ht : t ≠ p) :
        Φ.toFun ((complexChartAt (n := n) x).val y) t=0 := by
      have hh := hyKeep t (by simpa only [Finset.mem_singleton] using ht)
      change Φ.toFun ((complexChartAt (n := n) x).val y) t=
        Φ.toFun ((complexChartAt (n := n) x).val x) t at hh
      rw [hh,h0]
      rfl
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact hZero t (fun he => hp (he ▸ ht))
    · rw [Finset.mem_singleton.mp ht]
      exact hZero q hpq.symm
  obtain ⟨y,⟨hyB,hyne⟩,hyvan⟩ := (hFreq.and_eventually hvan.2).exists
  exact hyne (hyvan hyB)

private theorem density_off_coordinate_window {Z : Set X} {E : List (Set X)} {x : X}
    (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (s : Fin E.length → Fin n)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ) (hDomain : flatDomain Φ ⊆ (U : Set X))
    (hZflat : ∀ y : U,y.val ∈ Z ↔
      Φ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n k)
    (hEflat : ∀ y : U,y.val ∈ Z → ∀ a,
      y.val ∈ E.get a ↔ x ∈ E.get a ∧ flatCoord Φ (s a) y.val=0)
    (hFree : ∀ a,x ∈ E.get a → (s a).val < k) :
    (Subtype.val : U → X) ⁻¹' Z ⊆ closure ((Subtype.val : U → X) ⁻¹' Z \
      ⋃ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
  let T : Finset (Fin n) := (Finset.univ.filter fun a => x ∈ E.get a).image s
  intro y hyZ
  have hFreq : ∃ᶠ z in 𝓝 y.val,z ∈ Z \ ⋃ H ∈ E,H := by
    apply (MonomialPart.frequently_flatMap_ne_zero hsrc (hU y.property) T).mono
    rintro z ⟨hzD,hzne,hzKeep⟩
    let v : U := ⟨z,hDomain hzD⟩
    have hzZ : z ∈ Z := by
      apply (hZflat v).mpr
      intro t ht
      have htT : t ∉ T := by
        intro htT
        obtain ⟨a,ha,hst⟩ := Finset.mem_image.mp htT
        have hlt := hFree a (Finset.mem_filter.mp ha).2
        rw [hst] at hlt
        omega
      have he := hzKeep t htT
      change Φ.toFun ((complexChartAt (n := n) x).val z) t=
        Φ.toFun ((complexChartAt (n := n) x).val y.val) t at he
      rw [he]
      exact ((hZflat y).mp hyZ) t ht
    refine ⟨hzZ,?_⟩
    intro hzUnion
    obtain ⟨H,hHE,hzH⟩ := mem_iUnion₂.mp hzUnion
    obtain ⟨a,ha⟩ := List.mem_iff_get.mp hHE
    have hzE : z ∈ E.get a := by rw [ha];exact hzH
    obtain ⟨hxa,hzero⟩ := (hEflat v hzZ a).mp hzE
    have hsT : s a ∈ T := Finset.mem_image.mpr
      ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxa⟩,rfl⟩
    exact hzne (s a) hsT hzero
  have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (Z \ ⋃ H ∈ E,H) :=
    mem_closure_iff_frequently.mpr hFreq
  erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (Z \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

private theorem restrictOn_nested_eq {L N : Set X} (hLN : L ⊆ N)
    {I : GermIdeal n X} (hcI : I.IsCoherent) :
    restrictOn n L (restrictOn n N I)=restrictOn n L I := by
  ext x g
  constructor
  · intro hg
    exact ⟨hg.1,IsInSpanOnAt.trans
      (fun a ha => CodimOneCentreAlong.isInSpanOnAt_subset hLN ha.2) hg.2⟩
  · intro hg
    exact ⟨hg.1,IsInSpanOnAt.mono (fun a ha => le_restrictOn hcI x a ha) hg.2⟩

private theorem restrictOn_mul_normalized_eq {L : Set X} (hL : IsClosed L)
    {I J : GermIdeal n X} (hcI : I.IsCoherent) (hcJ : J.IsCoherent) :
    restrictOn n L ((restrictOn n L I).mul (restrictOn n L J))=restrictOn n L (I.mul J) := by
  apply restrictOn_eq_of_restrictLe hL
  · exact restrictLe_mul
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcJ hg)
      restrictLe_restrictOn restrictLe_restrictOn
  · exact restrictLe_mul (fun _ _ hg => hg.1) (fun _ _ hg => hg.1)
      (restrictLe_self_restrictOn hcI) (restrictLe_self_restrictOn hcJ)

private theorem nested_relative_principal_mem_iff {L N : Set X} (hLN : L ⊆ N)
    {I : GermIdeal n X} {x : X} {f : X → ℂ} (hf : HolomorphicAt n f x)
    (hGen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (g : X → ℂ) :
    (restrictOn n L I).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) L (·=f) x g := by
  have hfI : I.mem x f := (hGen f).mpr ⟨hf,isInSpanOnAt_eq_iff.mpr
    ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  constructor
  · intro hg
    exact ⟨hg.1,IsInSpanOnAt.trans
      (fun a ha => CodimOneCentreAlong.isInSpanOnAt_subset hLN ((hGen a).mp ha).2) hg.2⟩
  · intro hg
    exact ⟨hg.1,IsInSpanOnAt.mono (by rintro a rfl;exact hfI) hg.2⟩

private theorem lower_geometric_window (hn : 0 < n) {C N Z : Set X}
    (hC : IsClosedSubmanifold n C) (hCN : C ⊆ N) (hZ : IsClosed Z)
    {F : List (Set X)} (hF : IsSNCDivisor n F) (hCNC : HasNormalCrossings n C F)
    (hCDense : C ⊆ closure (C \ ⋃ H ∈ F,H))
    {x : X} (hxZ : x ∈ Z) (k : ℕ) (hk : k ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (s : Fin F.length → Fin n) (a : Fin F.length)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ) (hDomain : flatDomain Φ ⊆ (U : Set X))
    (hZflat : ∀ y : U,y.val ∈ Z ↔
      Φ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n k)
    (hSet : ∀ y : U,y.val ∈ Z ↔ y.val ∈ N ∩ F.get a)
    (hOther : ∀ y : U,∀ b,b ≠ a →
      (y.val ∈ F.get b ↔ x ∈ F.get b ∧ flatCoord Φ (s b) y.val=0))
    (hFree : ∀ b,x ∈ F.get b → (s b).val < k) :
    let L := (Subtype.val : U → X) ⁻¹' Z
    let G := (F.eraseIdx a.val).map ((Subtype.val : U → X) ⁻¹' ·)
    IsClosedSubmanifold n L ∧ IsSNCDivisor n G ∧ IsTransverse n L G ∧
      L ⊆ closure (L \ ⋃ H ∈ G,H) ∧
      IsClosedSubmanifold n (L ∩ (Subtype.val : U → X) ⁻¹' C) := by
  let G₀ := F.eraseIdx a.val
  have hChoice (b : Fin G₀.length) : ∃ c : Fin F.length,c ≠ a ∧ F.get c=G₀.get b := by
    obtain ⟨j,hj,hja,hGet⟩ := List.mem_eraseIdx_iff_getElem.mp (List.get_mem G₀ b)
    exact ⟨⟨j,hj⟩,fun he => hja (congrArg Fin.val he),hGet⟩
  let c : Fin G₀.length → Fin F.length := fun b => Classical.choose (hChoice b)
  have hc (b : Fin G₀.length) : c b ≠ a ∧ F.get (c b)=G₀.get b := Classical.choose_spec (hChoice b)
  have hGflat (y : U) (b : Fin G₀.length) : y.val ∈ G₀.get b ↔
      x ∈ G₀.get b ∧ flatCoord Φ (s (c b)) y.val=0 := by
    simpa only [(hc b).2] using hOther y (c b) (hc b).1
  have hFreeG (b : Fin G₀.length) (hb : x ∈ G₀.get b) : (s (c b)).val < k :=
    hFree (c b) (by rw [(hc b).2];exact hb)
  have hL : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' Z) :=
    closedSmooth_on_coordinate_window hZ k hk Φ U hU hDomain hZflat
  have hG : IsSNCDivisor n G₀ := isSNCDivisor_of_sublist hF (List.eraseIdx_sublist F a.val)
  have hGU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hG
  have hTr := transverse_on_coordinate_window hxZ k Φ (fun b => s (c b)) U hU hDomain hZflat hGflat hFreeG
  have hDense := density_off_coordinate_window k Φ (fun b => s (c b)) hsrc U hU hDomain hZflat
    (fun y _ => hGflat y) hFreeG
  have hTrC := HironakaNormalCrossingsTransversality.isTransverse_of_hasNormalCrossings_of_subset_closure_diff
    hCNC hCDense
  have hR : IsClosedSubmanifold n (C ∩ F.get a) := by
    convert MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hC.1 hF hTrC {a} using 1
    ext y
    simp only [Set.mem_inter_iff,BoundaryCount.memberInter,Set.mem_ofPred_eq,Finset.mem_singleton,forall_eq]
  have hRopen : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' (C ∩ F.get a)) := by
    refine ⟨hR.1.preimage continuous_subtype_val,fun y hy => ?_⟩
    obtain ⟨d,hd⟩ := hR.2 y.val hy
    exact ⟨d,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hd⟩
  have hEq : ((Subtype.val : U → X) ⁻¹' Z) ∩ ((Subtype.val : U → X) ⁻¹' C)=
      (Subtype.val : U → X) ⁻¹' (C ∩ F.get a) := by
    ext y
    constructor
    · rintro ⟨hyZ,hyC⟩
      exact ⟨hyC,((hSet y).mp hyZ).2⟩
    · rintro ⟨hyC,hyF⟩
      exact ⟨(hSet y).mpr ⟨hCN hyC,hyF⟩,hyC⟩
  exact ⟨hL,hGU,hTr,hDense,hEq ▸ hRopen⟩

private def windowSetFamily (C N Z : Set X) (E : List (Set X)) :
    Option (Option (Option (Option (Fin E.length ⊕ Fin E.length)))) → Set X :=
  fun o => o.elim N (fun o => o.elim Z (fun o => o.elim C
    (fun o => o.elim (Z ∩ C) (Sum.elim E.get (fun b => Z ∩ E.get b)))))

private def windowNormalFamily (k : ℕ) (p : Fin n) {m : ℕ} (s : Fin m → Fin n) :
    Option (Option (Option (Option (Fin m ⊕ Fin m)))) → Finset (Fin n) :=
  let QN := Finset.univ.filter fun t : Fin n => k+1 ≤ t.val
  let QZ := Finset.univ.filter fun t : Fin n => k ≤ t.val
  fun o => o.elim QN (fun o => o.elim QZ (fun o => o.elim (QN ∪ {p})
    (fun o => o.elim (QZ ∪ {p}) (Sum.elim (fun b => {s b}) (fun b => QZ ∪ {s b})))))

private theorem joint_frame_on_coordinate_window {C N Z : Set X} {E : List (Set X)}
    (hZN : Z ⊆ N) {x : X} (hxN : x ∈ N) (hxZ : x ∈ Z) (hxC : x ∈ C)
    (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (p : Fin n) (s : Fin E.length → Fin n)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ) (hDomain : flatDomain Φ ⊆ (U : Set X))
    (hFlat : ∀ y : U,
      (y.val ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n (k+1)) ∧
      (y.val ∈ Z ↔ Φ.toFun ((complexChartAt (n := n) x).val y.val) ∈ complexCoordinatePlane n k) ∧
      (y.val ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y.val) ∈
        complexCoordinatePlane n (k+1) ∧ flatCoord Φ p y.val=0) ∧
      ∀ b,y.val ∈ E.get b ↔ x ∈ E.get b ∧ flatCoord Φ (s b) y.val=0) :
    ∀ y : U,IsCoordinateFamilyAt n
      (fun o => (Subtype.val : U → X) ⁻¹' windowSetFamily C N Z E o)
      (windowNormalFamily k p s) y := by
  let A := windowSetFamily C N Z E
  let S := windowNormalFamily k p s
  have hflat : ∀ o,x ∈ A o → ∀ {z : X},
      z ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val z ∈ Φ.source →
      (z ∈ A o ↔ Φ.toFun ((complexChartAt (n := n) x).val z) ∈ coordSubspace (S o)) := by
    rintro (_ | (_ | (_ | (_ | b)))) hi z hz hzΦ
    · simpa only [A,S,windowSetFamily,windowNormalFamily,Option.elim,
        coordSubspace_eq_complexCoordinatePlane] using (hFlat ⟨z,hDomain ⟨hz,hzΦ⟩⟩).1
    · simpa only [A,S,windowSetFamily,windowNormalFamily,Option.elim,
        coordSubspace_eq_complexCoordinatePlane] using (hFlat ⟨z,hDomain ⟨hz,hzΦ⟩⟩).2.1
    · change z ∈ C ↔ _
      simp only [S,windowNormalFamily,Option.elim,ExceptionalPushforwardAlong.coordSubspace_union,
        Set.mem_inter_iff,coordSubspace_eq_complexCoordinatePlane,
        BlowupSNCTransform.mem_coordSubspace_singleton]
      simpa only [flatCoord,complexChartAt] using (hFlat ⟨z,hDomain ⟨hz,hzΦ⟩⟩).2.2.1
    · change z ∈ Z ∩ C ↔ _
      simp only [S,windowNormalFamily,Option.elim,ExceptionalPushforwardAlong.coordSubspace_union,
        Set.mem_inter_iff,coordSubspace_eq_complexCoordinatePlane,
        BlowupSNCTransform.mem_coordSubspace_singleton]
      have hF := hFlat ⟨z,hDomain ⟨hz,hzΦ⟩⟩
      constructor
      · rintro ⟨hzZ,hzC⟩
        exact ⟨hF.2.1.mp hzZ,(hF.2.2.1.mp hzC).2⟩
      · rintro ⟨hzZ,hzp⟩
        have hzZ' := hF.2.1.mpr hzZ
        exact ⟨hzZ',hF.2.2.1.mpr ⟨hF.1.mp (hZN hzZ'),hzp⟩⟩
    · rcases b with b | b
      · change x ∈ E.get b at hi
        simpa only [A,S,windowSetFamily,windowNormalFamily,Option.elim,Sum.elim_inl,
          BlowupSNCTransform.mem_coordSubspace_singleton,hi,true_and,flatCoord,complexChartAt] using
          (hFlat ⟨z,hDomain ⟨hz,hzΦ⟩⟩).2.2.2 b
      · change x ∈ Z ∩ E.get b at hi
        change z ∈ Z ∩ E.get b ↔ _
        simp only [S,windowNormalFamily,Option.elim,Sum.elim_inr,
          ExceptionalPushforwardAlong.coordSubspace_union,Set.mem_inter_iff,
          coordSubspace_eq_complexCoordinatePlane,BlowupSNCTransform.mem_coordSubspace_singleton]
        have hF := hFlat ⟨z,hDomain ⟨hz,hzΦ⟩⟩
        apply and_congr hF.2.1
        simpa only [hi.2,true_and,flatCoord,complexChartAt] using hF.2.2.2 b
  intro y
  have hseen : ∀ o,y.val ∈ A o → x ∈ A o := by
    rintro (_ | (_ | (_ | (_ | b)))) hi
    · exact hxN
    · exact hxZ
    · exact hxC
    · exact ⟨hxZ,hxC⟩
    · rcases b with b | b
      · exact ((hFlat y).2.2.2 b).mp hi |>.1
      · exact ⟨hxZ,((hFlat y).2.2.2 b).mp hi.2 |>.1⟩
  exact isCoordinateFamilyAt_preimage_val_iff.mpr
    (coordinateFamilyAt_of_flattening Φ hflat (hU y.property).1 (hU y.property).2 hseen)

private theorem nested_actual_whole_factor {L N : Set X} (hLN : L ⊆ N) (hL : IsClosed L)
    {I D J K : GermIdeal n X} (hcI : I.IsCoherent) (hcD : D.IsCoherent) (hcJ : J.IsCoherent)
    (hUpper : restrictOn n N I=restrictOn n N (D.mul J))
    (hLowerJ : restrictOn n L J=K) :
    restrictOn n L I=restrictOn n L ((restrictOn n L D).mul K) := by
  calc
    restrictOn n L I=restrictOn n L (restrictOn n N I) := (restrictOn_nested_eq hLN hcI).symm
    _=restrictOn n L (restrictOn n N (D.mul J)) := by rw [hUpper]
    _=restrictOn n L (D.mul J) := restrictOn_nested_eq hLN (isCoherent_mul hcD hcJ)
    _=restrictOn n L ((restrictOn n L D).mul (restrictOn n L J)) :=
      (restrictOn_mul_normalized_eq hL hcD hcJ).symm
    _=restrictOn n L ((restrictOn n L D).mul K) := by rw [hLowerJ]

private theorem coordinate_reduced_family_geometry {L R : Set X} {B : List (Set X)}
    (hL : IsClosedSubmanifold n L) (hR : IsClosedSubmanifold n R)
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n L B)
    (k : ℕ) (p r : Fin n) (q : Fin B.length → Fin n) (hr : r.val < k)
    (hp : ∀ y ∈ R,p.val < k)
    (hFrame : ∀ y ∈ L,IsCoordinateFamilyAt n
      (fun o : Option (Option (Fin B.length)) => o.elim L (fun o => o.elim R (fun b => L ∩ B.get b)))
      (fun o => o.elim (Finset.univ.filter fun t : Fin n => k ≤ t.val)
        (fun o => (Finset.univ.filter fun t : Fin n => k ≤ t.val) ∪ {o.elim p q})) y)
    (hDiff : ∀ y ∈ R,∀ b : Fin B.length,y ∈ B.get b → p ≠ q b) :
    (∀ y ∈ L,IsNonzeroAlongAt L (vanishingIdeal (n := n) R) y) ∧
      (∀ y ∈ L,ordinaryTraceOrder L (vanishingIdeal (n := n) R) y ≤ 1) ∧
      (∀ y ∈ L,∀ b : Fin B.length,y ∈ B.get b →
        ∃ f,(vanishingIdeal (n := n) R).mem y f ∧
          ¬IsInSpanOnAt (n := n) L ((vanishingIdeal (n := n) (B.get b)).mem y) y f) := by
  let Q : Finset (Fin n) := Finset.univ.filter fun t : Fin n => k ≤ t.val
  have hcR := VanishingIdealCoherent.isCoherent_vanishingIdeal hR
  have hLocal (y : X) (hyL : y ∈ L) :
      ∃ (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)) (t : Fin n),
        t.val < k ∧ Φ.source ⊆ (complexChartAt (n := n) y).val.target ∧
        Φ.toFun ((complexChartAt (n := n) y).val y)=0 ∧
        (∀ {z : X},z ∈ (complexChartAt (n := n) y).val.source →
          (complexChartAt (n := n) y).val z ∈ Φ.source →
          (z ∈ L ↔ Φ.toFun ((complexChartAt (n := n) y).val z) ∈ complexCoordinatePlane n k)) ∧
        (vanishingIdeal (n := n) R).mem y (flatCoord Φ t) := by
    obtain ⟨Φ,hsrc,h0,hflat⟩ := hFrame y hyL
    have hLflat {z : X} (hz : z ∈ (complexChartAt (n := n) y).val.source)
        (hzΦ : (complexChartAt (n := n) y).val z ∈ Φ.source) :
        z ∈ L ↔ Φ.toFun ((complexChartAt (n := n) y).val z) ∈ complexCoordinatePlane n k := by
      simpa only [Option.elim,coordSubspace_eq_complexCoordinatePlane] using hflat none hyL hz hzΦ
    by_cases hyR : y ∈ R
    · have hpQ : p ∉ Q := by simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hp y hyR
      refine ⟨Φ,p,hp y hyR,hsrc,h0,hLflat,?_⟩
      apply (vanishingIdeal_coordinate_trace_mem_iff Φ Q p hpQ hsrc h0
        (fun hz hzΦ => by simpa only [Q,coordSubspace_eq_complexCoordinatePlane] using hLflat hz hzΦ)
        (fun hz hzΦ => hflat (some none) hyR hz hzΦ) _).mpr
      exact ⟨holomorphicAt_flatCoord Φ p (mem_flatDomain_self Φ),
        isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
    · refine ⟨Φ,r,hr,hsrc,h0,hLflat,holomorphicAt_flatCoord Φ r (mem_flatDomain_self Φ),?_⟩
      filter_upwards [hR.1.isOpen_compl.mem_nhds hyR] with z hz hzR
      exact (hz hzR).elim
  have hnz : ∀ y ∈ L,IsNonzeroAlongAt L (vanishingIdeal (n := n) R) y := by
    intro y hyL
    obtain ⟨Φ,t,ht,hsrc,h0,hflat,hmem⟩ := hLocal y hyL
    exact coordinate_nonzero_along_at Φ Q t
      (by simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using ht)
      hsrc h0 (fun hz hzΦ => by simpa only [Q,coordSubspace_eq_complexCoordinatePlane] using hflat hz hzΦ) hmem
  refine ⟨hnz,?_,?_⟩
  · intro y hyL
    obtain ⟨Φ,t,ht,hsrc,_h0,hflat,hmem⟩ := hLocal y hyL
    exact coordinate_member_order_le_one_at hL hcR hnz Φ k t ht hsrc hflat (mem_flatDomain_self Φ) hyL hmem
  · intro y hyL b hyB
    by_cases hyR : y ∈ R
    · obtain ⟨Φ,hsrc,h0,hflat⟩ := hFrame y hyL
      exact coordinate_trace_no_born_factor_at hB hTr hyL Φ Q p (q b)
        (by simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hp y hyR)
        (hDiff y hyR b hyB) hsrc h0
        (fun hz hzΦ => hflat none hyL hz hzΦ)
        (fun hz hzΦ => hflat (some none) hyR hz hzΦ) b
        (fun hz hzΦ => hflat (some (some b)) ⟨hyL,hyB⟩ hz hzΦ)
    · have hOne : (vanishingIdeal (n := n) R).mem y 1 := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [hR.1.isOpen_compl.mem_nhds hyR] with z hz hzR
        exact (hz hzR).elim
      refine ⟨1,hOne,fun hspan => ?_⟩
      have hvan := (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem hB hTr hyL b
        (holomorphicAt_const (1 : ℂ))).mp hspan
      exact one_ne_zero (hvan.2.self_of_nhds ⟨hyL,hyB⟩)

theorem actual_original_lower_prepared_neighborhood
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
    (j : Fin E.length) (hne : j ≠ i) {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let born := A.E
    let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let Sj := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Di := monomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) born
    ∃ U : Opens Y,x ∈ U ∧
      let L : Set U := (Subtype.val : U → Y) ⁻¹' Sj
      let oldU := (old.eraseIdx j.val).map ((Subtype.val : U → Y) ⁻¹' ·)
      let bornU := born.map ((Subtype.val : U → Y) ⁻¹' ·)
      let Mi := restrictOn n L (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Di)
      IsClosedSubmanifold n L ∧ IsSNCDivisor n (oldU ++ bornU) ∧
        IsTransverse n L bornU ∧ L ⊆ closure (L \ ⋃ H ∈ oldU ++ bornU,H) ∧
        (∀ h : Fin E.length,h ≠ j → ∃ a : Fin oldU.length,
          oldU.get a=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h) ∧
          if h=i then
            oldMonomialPart (X := CMfd.of (n := n) U) L oldU bornU a=Mi ∧
              oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU a=
                vanishingIdeal (n := n) (L ∩ (Subtype.val : U → Y) ⁻¹' Si)
          else
            (∀ y ∈ L,(oldMonomialPart (X := CMfd.of (n := n) U) L oldU bornU a).mem y 1) ∧
              oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU a=
                vanishingIdeal (n := n) (L ∩ (Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h))) ∧
        ∀ y ∈ L,(∀ a,ordinaryTraceOrder L
          (oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU a) y ≤ 1) ∧
          IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) L oldU bornU y := by
  classical
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let B := A.E
  let J := fun h : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  let Sj := A.N ∩ (J j).zeroLocus
  let F := old.eraseIdx i.val ++ B
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hFullE : IsSNCDivisor n (old ++ B) := hRecorded.2.1
  have hTr : IsTransverse n A.N B := hRecorded.2.2.1
  have hNi := (chronologicalMarked_geometric_fields
    (originalRelativeMemberMarked W (E.get i)) T).1
  have hNj := (chronologicalMarked_geometric_fields
    (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N=A.N at hNj
  have hOrdA : ∀ y ∈ A.N,ordinaryTraceOrder A.N (J i) y ≤ 1 := by
    simpa only [hNi] using hOrd
  have hxiA : x ∈ Si := by simpa only [hNi] using hxi
  have hxjA : x ∈ Sj := by simpa only [hNj] using hxj
  have hProtect := actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull
    hOrdA hNC hDenseS
  have hSi : IsClosedSubmanifold n Si := hProtect.1
  have hWholeSi : J i=vanishingIdeal (n := n) Si := hProtect.2.1
  obtain ⟨_hNj,_hEj,_hdj,hwJj,_hnzJj,_hprJj⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  have hSjClosed : IsClosed Sj := hN.1.inter
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hwJj.isCoherent).isClosed
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hFullE
    ((List.eraseIdx_sublist old i.val).append (List.Sublist.refl B))
  obtain ⟨k,s,a,U,Φ,hkpos,hkn,hGet,hs,hinj,hxa,hxU,hU,hDomain,hsrc,h0,hRaw⟩ :=
    actual_original_lower_coordinate_frame hn hW hE hdense i T hT hFull hOrd hNC hDenseS
      j hne hxi hxj
  have hGeo := lower_geometric_window hn hSi inter_subset_left hSjClosed hF hNC hDenseS
    hxjA k (by omega) Φ s a hsrc U hU hDomain
      (fun y => (hRaw y).2.1) (fun y => (hRaw y).2.2.2.2)
      (fun y => (hRaw y).2.2.2.1) hs
  let L : Set U := (Subtype.val : U → Y) ⁻¹' Sj
  let oldU := (old.eraseIdx j.val).map ((Subtype.val : U → Y) ⁻¹' ·)
  let bornU := B.map ((Subtype.val : U → Y) ⁻¹' ·)
  have hLowerFull : IsSNCDivisor n (oldU ++ bornU) := by
    have he := isSNCDivisor_of_sublist hFullE
      ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl B))
    simpa only [List.map_append] using
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val he
  let G₀ := F.eraseIdx a.val
  let G := G₀.map ((Subtype.val : U → Y) ⁻¹' ·)
  let fj : Fin (old ++ B).length := ⟨j.val,by simp only [List.length_append,old,List.length_map];omega⟩
  have hGetj : (old ++ B).get fj=strictAlong T (E.get j) := by
    have hj : j.val < old.length := by simpa only [old,List.length_map] using j.isLt
    simp only [List.get_eq_getElem,fj,List.getElem_append_left hj,old,List.getElem_map]
  have hxHj : x ∈ strictAlong T (E.get j) := by rw [←hGet];exact hxa
  have hDistinct (c : Fin (old ++ B).length) (hcf : c ≠ fj) :
      (old ++ B).get c ≠ strictAlong T (E.get j) := by
    intro he
    have hc : x ∈ (old ++ B).get c := by rw [he];exact hxHj
    have hf : x ∈ (old ++ B).get fj := by rw [hGetj];exact hxHj
    apply hcf
    exact eq_of_eventually_mem_iff hFullE hc hf (Eventually.of_forall fun _ => by rw [he,hGetj])
  have hGmem {H : Set Y} (hHF : H ∈ F) (hneH : H ≠ strictAlong T (E.get j)) : H ∈ G₀ := by
    obtain ⟨b,hb⟩ := List.mem_iff_get.mp hHF
    exact List.mem_eraseIdx_iff_getElem.mpr
      ⟨b.val,b.isLt,fun he => hneH (hb.symm.trans ((congrArg F.get (Fin.ext he)).trans hGet)),hb⟩
  have hBornG (H : Set Y) (hHB : H ∈ B) : H ∈ G₀ := by
    obtain ⟨b,hb⟩ := List.mem_iff_get.mp hHB
    let c : Fin (old ++ B).length := ⟨old.length+b.val,by simp only [List.length_append];omega⟩
    have hc : (old ++ B).get c=H := by
      simp only [List.get_eq_getElem,c,List.getElem_append_right (by omega : old.length ≤ old.length+b.val),
        Nat.add_sub_cancel_left]
      exact hb
    apply hGmem (List.mem_append_right _ hHB)
    rw [←hc]
    apply hDistinct c
    intro he
    have hv := congrArg Fin.val he
    change old.length+b.val=j.val at hv
    have hj : j.val < old.length := by simpa only [old,List.length_map] using j.isLt
    omega
  have hBornSub : ∀ H ∈ bornU,H ∈ G := by
    intro H hH
    obtain ⟨K,hKB,rfl⟩ := List.mem_map.mp hH
    exact List.mem_map.mpr ⟨K,hBornG K hKB,rfl⟩
  have hTrBorn : IsTransverse n L bornU := isTransverse_of_forall_mem hGeo.2.2.1 hBornSub
  have hOtherG (h : Fin E.length) (hhi : h ≠ i) (hhj : h ≠ j) :
      strictAlong T (E.get h) ∈ G₀ := by
    have hHF : strictAlong T (E.get h) ∈ F := by
      apply List.mem_append_left
      exact List.mem_eraseIdx_iff_getElem.mpr
        ⟨h.val,by simpa only [old,List.length_map] using h.isLt,
          fun he => hhi (Fin.ext he),by simp only [old,List.getElem_map,List.get_eq_getElem]⟩
    apply hGmem hHF
    let c : Fin (old ++ B).length := ⟨h.val,by simp only [List.length_append,old,List.length_map];omega⟩
    have hc : (old ++ B).get c=strictAlong T (E.get h) := by
      have hh : h.val < old.length := by simpa only [old,List.length_map] using h.isLt
      simp only [List.get_eq_getElem,c,List.getElem_append_left hh,old,List.getElem_map]
    rw [←hc]
    exact hDistinct c (fun he => hhj (Fin.ext
      (congrArg (fun z : Fin (old ++ B).length => z.val) he)))
  have hChoice (b : Fin G₀.length) : ∃ c : Fin F.length,c ≠ a ∧ F.get c=G₀.get b := by
    obtain ⟨v,hv,hva,hgv⟩ := List.mem_eraseIdx_iff_getElem.mp (List.get_mem G₀ b)
    exact ⟨⟨v,hv⟩,fun he => hva (congrArg Fin.val he),hgv⟩
  let c : Fin G₀.length → Fin F.length := fun b => Classical.choose (hChoice b)
  have hc (b : Fin G₀.length) : c b ≠ a ∧ F.get (c b)=G₀.get b := Classical.choose_spec (hChoice b)
  have hGflat (y : U) (b : Fin G₀.length) : y.val ∈ G₀.get b ↔
      x ∈ G₀.get b ∧ flatCoord Φ (s (c b)) y.val=0 := by
    have hh : y.val ∈ F.get (c b) ↔ x ∈ F.get (c b) ∧ flatCoord Φ (s (c b)) y.val=0 :=
      (hRaw y).2.2.2.1 (c b) (hc b).1
    rwa [(hc b).2] at hh
  have hFrame := joint_frame_on_coordinate_window
    (inter_subset_left : Sj ⊆ A.N) hxiA.1 hxjA hxiA k Φ (s a) (fun b => s (c b))
    U hU hDomain (fun y => ⟨(hRaw y).1,(hRaw y).2.1,(hRaw y).2.2.1,hGflat y⟩)
  let NU : Set U := (Subtype.val : U → Y) ⁻¹' A.N
  let CU : Set U := (Subtype.val : U → Y) ⁻¹' Si
  let R := L ∩ CU
  let QN : Finset (Fin n) := Finset.univ.filter fun t : Fin n => k+1 ≤ t.val
  let QL : Finset (Fin n) := Finset.univ.filter fun t : Fin n => k ≤ t.val
  have hpN : s a ∉ QN := by
    simp only [QN,Finset.mem_filter,Finset.mem_univ,true_and,not_le]
    have ha := hs a hxa
    omega
  have hpL : s a ∉ QL := by
    simpa only [QL,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hs a hxa
  have hCUclosed : IsClosed CU := hSi.1.preimage continuous_subtype_val
  have hcCU := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (show IsClosedSubmanifold n CU from ⟨hCUclosed,fun y hy => by
      obtain ⟨d,hd⟩ := hSi.2 y.val hy
      exact ⟨d,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hd⟩⟩)
  have hLC : restrictOn n L (vanishingIdeal (n := n) CU)=vanishingIdeal (n := n) R := by
    ext y g
    constructor
    · intro hg
      apply MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt
        (inter_subset_left : R ⊆ L) hg.1
      exact IsInSpanOnAt.mono (fun f hf => ⟨hf.1,hf.2.mono fun z hz hzR => hz hzR.2⟩) hg.2
    · intro hg
      by_cases hyL : y ∈ L
      · by_cases hyC : y ∈ CU
        · obtain ⟨Ψ,hΨsrc,hΨ0,hΨflat⟩ := hFrame y
          have hyN : y ∈ NU := hyL.1
          have hNflat := fun {z : U} (hz : z ∈ (complexChartAt (n := n) y).val.source)
            (hzΨ : (complexChartAt (n := n) y).val z ∈ Ψ.source) => hΨflat none hyN hz hzΨ
          have hLflat := fun {z : U} (hz : z ∈ (complexChartAt (n := n) y).val.source)
            (hzΨ : (complexChartAt (n := n) y).val z ∈ Ψ.source) => hΨflat (some none) hyL hz hzΨ
          have hCflat := fun {z : U} (hz : z ∈ (complexChartAt (n := n) y).val.source)
            (hzΨ : (complexChartAt (n := n) y).val z ∈ Ψ.source) => hΨflat (some (some none)) hyC hz hzΨ
          have hRflat := fun {z : U} (hz : z ∈ (complexChartAt (n := n) y).val.source)
            (hzΨ : (complexChartAt (n := n) y).val z ∈ Ψ.source) => hΨflat (some (some (some none))) (show y ∈ R from ⟨hyL,hyC⟩) hz hzΨ
          have hf := holomorphicAt_flatCoord Ψ (s a) (mem_flatDomain_self Ψ)
          have hCgen := fun f : U → ℂ => vanishingIdeal_coordinate_trace_mem_iff (X := CMfd.of (n := n) U)
            Ψ QN (s a) hpN hΨsrc hΨ0 hNflat hCflat f
          have hRgen := vanishingIdeal_coordinate_trace_mem_iff (X := CMfd.of (n := n) U)
            Ψ QL (s a) hpL hΨsrc hΨ0 hLflat hRflat g
          exact (nested_relative_principal_mem_iff (X := CMfd.of (n := n) U)
            (show L ⊆ NU from inter_subset_left) hf hCgen g).mpr (hRgen.mp hg)
        · apply le_restrictOn hcCU y g
          refine ⟨hg.1,?_⟩
          filter_upwards [hCUclosed.isOpen_compl.mem_nhds hyC] with z hz hzC
          exact (hz hzC).elim
      · exact restrictOn_eq_top_of_disjoint (W := L) (𝔞 := vanishingIdeal (n := n) CU)
          hGeo.1.1.isOpen_compl hyL (Set.compl_inter_self L) hg.1
  let upperOldU := old.map ((Subtype.val : U → Y) ⁻¹' ·)
  have hNU : IsClosedSubmanifold n NU := by
    refine ⟨hN.1.preimage continuous_subtype_val,fun y hy => ?_⟩
    obtain ⟨d,hd⟩ := hN.2 y.val hy
    exact ⟨d,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hd⟩
  have hUpperFull : IsSNCDivisor n (upperOldU ++ bornU) := by
    simpa only [List.map_append] using
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hFullE
  have hTrNU : IsTransverse n NU bornU :=
    isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseNU : NU ⊆ closure (NU \ ⋃ H ∈ upperOldU ++ bornU,H) := by
    intro y hy
    have hp : y ∈ (Subtype.val : U → Y) ⁻¹' closure (A.N \ ⋃ H ∈ old ++ B,H) :=
      hRecorded.2.2.2.1 hy
    erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (A.N \ ⋃ H ∈ old ++ B,H)] at hp
    have hMap : upperOldU ++ bornU=(old ++ B).map ((Subtype.val : U → Y) ⁻¹' ·) :=
      List.map_append.symm
    have hComp : (Subtype.val : U → Y) ⁻¹' (A.N \ ⋃ H ∈ old ++ B,H)=
        NU \ ⋃ H ∈ upperOldU ++ bornU,H := by
      ext z
      constructor
      · rintro ⟨hzN,hzNot⟩
        refine ⟨hzN,fun hh => ?_⟩
        obtain ⟨K,hK,hzK⟩ := mem_iUnion₂.mp hh
        rw [hMap] at hK
        obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hK
        exact hzNot (mem_iUnion₂.mpr ⟨H,hH,hzK⟩)
      · rintro ⟨hzN,hzNot⟩
        refine ⟨hzN,fun hh => ?_⟩
        obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hh
        apply hzNot
        exact mem_iUnion₂.mpr ⟨_,hMap.symm ▸ List.mem_map.mpr ⟨H,hH,rfl⟩,hzH⟩
    exact (congrArg (fun Q : Set U => y ∈ closure Q) hComp).mp hp
  let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
  let ui : Fin upperOldU.length := ⟨i.val,by simpa only [upperOldU,old,List.length_map] using i.isLt⟩
  have hOldi : old.get oi=strictAlong T (E.get i) := by simp [old,oi]
  have hUpperi : upperOldU.get ui=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i) := by
    simp [upperOldU,old,ui]
  have hParts := actual_old_parts_geometry hn hN hFullE hTr hRecorded.2.2.2.1 oi
  have hPartsU := actual_old_parts_geometry (X := CMfd.of (n := n) U)
    (old := upperOldU) (born := bornU) hn hNU hUpperFull hTrNU hDenseNU ui
  let I := oldTraceIdeal A.N old oi
  let D := oldMonomialPart A.N old B oi
  let DU := oldMonomialPart (X := CMfd.of (n := n) U) NU upperOldU bornU ui
  have hNm : oldResidualPart A.N old B oi=J i := by
    simpa only [oldResidualPart,oldTraceIdeal,hOldi] using (hRecorded.2.2.2.2 i).2.2.1
  have hHism : IsClosedSubmanifold n (strictAlong T (E.get i)) := by
    rw [←hOldi]
    exact MonomialPart.isClosedSubmanifold_get hn
      (isSNCDivisor_of_sublist hFullE (List.sublist_append_left _ _)) oi
  have hOpenI : oldTraceIdeal (X := CMfd.of (n := n) U) NU upperOldU ui=
      GermIdeal.pullback (m := n) (Subtype.val : U → Y) I := by
    simpa only [I,oldTraceIdeal,hOldi,hUpperi] using
      HironakaSharpActualStrictTraceOpenNonmonomial.actual_normalized_trace_whole_open_pullback hN hHism U
  have hDU : GermIdeal.pullback (m := n) (Subtype.val : U → Y) D=DU := by
    have hh := MonomialPartEtale.pullback_monomialPartAlong (N := A.N) (E := B) (𝔞 := I)
      (fun y : U => ⟨DerivativeIdealAlongEtale.openInv U y,DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hParts.1 hg)
    change GermIdeal.pullback (m := n) (Subtype.val : U → Y) D=
      monomialPartAlong n NU (GermIdeal.pullback (m := n) (Subtype.val : U → Y) I) bornU at hh
    change GermIdeal.pullback (m := n) (Subtype.val : U → Y) D=
      monomialPartAlong n NU (oldTraceIdeal (X := CMfd.of (n := n) U) NU upperOldU ui) bornU
    rw [hOpenI]
    exact hh
  have hJU : oldResidualPart (X := CMfd.of (n := n) U) NU upperOldU bornU ui=vanishingIdeal (n := n) CU := by
    have hh := MonomialPartEtale.pullback_nonmonomialPartAlong (N := A.N) (E := B) (𝔞 := I)
      (fun y : U => ⟨DerivativeIdealAlongEtale.openInv U y,DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩)
      hParts.1 hParts.2.2.2.2.1 hParts.2.2.1
    change GermIdeal.pullback (m := n) (Subtype.val : U → Y)
      (oldResidualPart A.N old B oi)=nonmonomialPartAlong n NU
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) I) bornU at hh
    rw [hNm,hWholeSi] at hh
    rw [←hOpenI] at hh
    apply hh.symm.trans
    ext y g
    exact (MarkedIdealRestrictOpen.mem_pullback_val_iff U
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hSi)).trans
      (BlowupRestrictOpen.vanishingIdeal_opens_mem_iff U).symm
  have hDenseBorn : L ⊆ closure (L \ ⋃ H ∈ bornU,H) := by
    apply hGeo.2.2.2.1.trans (closure_mono ?_)
    intro y hy
    refine ⟨hy.1,fun hh => ?_⟩
    obtain ⟨H,hHB,hyH⟩ := mem_iUnion₂.mp hh
    exact hy.2 (mem_iUnion₂.mpr ⟨H,hBornSub H hHB,hyH⟩)
  let Mi := restrictOn n L (GermIdeal.pullback (m := n) (Subtype.val : U → Y) D)
  have hMiGeometry : Mi.IsCoherent ∧ (∀ y ∈ L,IsNonzeroAlongAt L Mi y) ∧
      IsMonomialAlong n L Mi bornU := by
    rw [show Mi=restrictOn n L DU from congrArg (restrictOn n L) hDU]
    exact restricted_monomial_geometry (X := CMfd.of (n := n) U) hn hGeo.1 hNU (inter_subset_left : L ⊆ NU)
      (isSNCDivisor_of_sublist hUpperFull (List.sublist_append_right _ _))
      hTrNU hTrBorn hDenseBorn hPartsU.2.2.2.2.1 hPartsU.2.2.2.2.2.1 hPartsU.2.2.2.2.2.2.1
  have hMiNorm : restrictOn n L Mi=Mi := restrictOn_nested_eq (X := CMfd.of (n := n) U) (Subset.refl L)
    (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hParts.2.2.2.2.1)
  have hProcessedFactor : restrictOn n L
      (vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i)))=
      restrictOn n L (Mi.mul (vanishingIdeal (n := n) R)) := by
    have hFactorU := hPartsU.2.2.2.2.2.2.2
    change restrictOn n NU (vanishingIdeal (n := n) (upperOldU.get ui))=
      restrictOn n NU (DU.mul (oldResidualPart (X := CMfd.of (n := n) U) NU upperOldU bornU ui)) at hFactorU
    rw [hUpperi] at hFactorU
    have hh := nested_actual_whole_factor (X := CMfd.of (n := n) U) (inter_subset_left : L ⊆ NU) hGeo.1.1
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (show IsClosedSubmanifold n
        ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i)) from by
          refine ⟨hHism.1.preimage continuous_subtype_val,fun y hy => ?_⟩
          obtain ⟨d,hd⟩ := hHism.2 y.val hy
          exact ⟨d,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hd⟩))
      hPartsU.2.2.2.2.1 hPartsU.2.2.1
      hFactorU
      (show restrictOn n L (oldResidualPart (X := CMfd.of (n := n) U) NU upperOldU bornU ui)=vanishingIdeal (n := n) R from by
        rw [hJU];exact hLC)
    change restrictOn n L (vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i)))=
      restrictOn n L ((restrictOn n L DU).mul (vanishingIdeal (n := n) R)) at hh
    exact hh.trans (congrArg (fun K => restrictOn n L (K.mul (vanishingIdeal (n := n) R)))
      (show restrictOn n L DU=Mi from (congrArg (restrictOn n L) hDU).symm))
  have hBornChoice (b : Fin bornU.length) : ∃ d : Fin G₀.length,
      (Subtype.val : U → Y) ⁻¹' G₀.get d=bornU.get b := by
    have hMem : bornU.get b ∈ G := hBornSub _ (List.get_mem bornU b)
    obtain ⟨H,hH,hEq⟩ := List.mem_map.mp hMem
    obtain ⟨d,hd⟩ := List.mem_iff_get.mp hH
    exact ⟨d,by rw [hd];exact hEq⟩
  let bG : Fin bornU.length → Fin G₀.length := fun b => Classical.choose (hBornChoice b)
  have hbG (b : Fin bornU.length) : (Subtype.val : U → Y) ⁻¹' G₀.get (bG b)=bornU.get b :=
    Classical.choose_spec (hBornChoice b)
  let q : Fin bornU.length → Fin n := fun b => s (c (bG b))
  have hProcFrame (y : U) (_hyL : y ∈ L) : IsCoordinateFamilyAt n
      (fun o : Option (Option (Fin bornU.length)) => o.elim L (fun o => o.elim R (fun b => L ∩ bornU.get b)))
      (fun o => o.elim QL (fun o => QL ∪ {o.elim (s a) q})) y := by
    apply IsCoordinateFamilyAt.reindex (hFrame y)
      (fun o : Option (Option (Fin bornU.length)) => o.elim (some none)
        (fun o => o.elim (some (some (some none)))
          (fun b => some (some (some (some (Sum.inr (bG b))))))))
    · rintro (_ | (_ | b))
      · rfl
      · rfl
      · change L ∩ bornU.get b=(Subtype.val : U → Y) ⁻¹' (Sj ∩ G₀.get (bG b))
        rw [Set.preimage_inter,hbG]
    · rintro (_ | (_ | b)) <;> rfl
  have hProcDiff (y : U) (_hyR : y ∈ R) (b : Fin bornU.length) (hyB : y ∈ bornU.get b) :
      s a ≠ q b := by
    have hyG : y.val ∈ G₀.get (bG b) := by rw [←hbG] at hyB;exact hyB
    have hxG := ((hGflat y (bG b)).mp hyG).1
    have hxF : x ∈ F.get (c (bG b)) := by rw [(hc (bG b)).2];exact hxG
    intro he
    exact (hc (bG b)).1 (hinj hxa hxF he).symm
  have hRsm : IsClosedSubmanifold n R := hGeo.2.2.2.2
  have hBornSNC : IsSNCDivisor n bornU :=
    isSNCDivisor_of_sublist hLowerFull (List.sublist_append_right _ _)
  have hRGeometry := coordinate_reduced_family_geometry (X := CMfd.of (n := n) U)
    hGeo.1 hRsm hBornSNC hTrBorn k (s a) (s a) q (hs a hxa)
    (fun _ _ => hs a hxa) hProcFrame hProcDiff
  have hProcParts := canonical_parts_of_actual_reduced_factor (X := CMfd.of (n := n) U)
    hn hGeo.1 hRsm (inter_subset_left : R ⊆ L) hBornSNC hTrBorn hMiGeometry.1
    hMiGeometry.2.1 hMiGeometry.2.2 hMiNorm hRGeometry.1 hRGeometry.2.2 hProcessedFactor
  have hOtherParts (e : Fin oldU.length) (d : Fin G₀.length)
      (hGetOld : oldU.get e=(Subtype.val : U → Y) ⁻¹' G₀.get d) :
      (∀ y ∈ L,(oldMonomialPart (X := CMfd.of (n := n) U) L oldU bornU e).mem y 1) ∧
        oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e=
          vanishingIdeal (n := n) (L ∩ oldU.get e) ∧
        ∀ y ∈ L,ordinaryTraceOrder L
          (oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e) y ≤ 1 := by
    let Z := L ∩ oldU.get e
    let gd : Fin G.length := ⟨d.val,by simpa only [G,List.length_map] using d.isLt⟩
    have hgd : G.get gd=(Subtype.val : U → Y) ⁻¹' G₀.get d := by
      simp only [G,List.get_eq_getElem,List.getElem_map,gd]
    have hZ : IsClosedSubmanifold n Z := by
      have hh := MemberInterAlong.isClosedSubmanifold_inter_memberInter (N := L) (E := G)
        hn hGeo.1.1 hGeo.2.1 hGeo.2.2.1 {gd}
      convert hh using 1
      ext y
      simp only [Z,Set.mem_inter_iff,BoundaryCount.memberInter,Set.mem_ofPred_eq,
        Finset.mem_singleton,forall_eq,hgd,←hGetOld]
    have hFZ (y : U) (_hyL : y ∈ L) : IsCoordinateFamilyAt n
        (fun o : Option (Option (Fin bornU.length)) => o.elim L (fun o => o.elim Z (fun b => L ∩ bornU.get b)))
        (fun o => o.elim QL (fun o => QL ∪ {o.elim (s (c d)) q})) y := by
      apply IsCoordinateFamilyAt.reindex (hFrame y)
        (fun o : Option (Option (Fin bornU.length)) => o.elim (some none)
          (fun o => o.elim (some (some (some (some (Sum.inr d)))))
            (fun b => some (some (some (some (Sum.inr (bG b))))))))
      · rintro (_ | (_ | b))
        · rfl
        · change L ∩ oldU.get e=(Subtype.val : U → Y) ⁻¹' (Sj ∩ G₀.get d)
          rw [Set.preimage_inter,hGetOld]
        · change L ∩ bornU.get b=(Subtype.val : U → Y) ⁻¹' (Sj ∩ G₀.get (bG b))
          rw [Set.preimage_inter,hbG]
      · rintro (_ | (_ | b)) <;> rfl
    have hFreeZ (y : U) (hy : y ∈ Z) : (s (c d)).val < k := by
      have hyG : y.val ∈ G₀.get d := by
        have hh : y ∈ oldU.get e := hy.2
        rw [hGetOld] at hh
        exact hh
      have hxG := ((hGflat y d).mp hyG).1
      apply hs (c d)
      change x ∈ F.get (c d)
      rw [(hc d).2]
      exact hxG
    have hDiffZ (y : U) (hy : y ∈ Z) (b : Fin bornU.length) (hyB : y ∈ bornU.get b) :
        s (c d) ≠ q b := by
      have hyG : y.val ∈ G₀.get d := by
        have hh : y ∈ oldU.get e := hy.2
        rw [hGetOld] at hh
        exact hh
      have hyGb : y.val ∈ G₀.get (bG b) := by rw [←hbG] at hyB;exact hyB
      have hxG : x ∈ F.get (c d) := by rw [(hc d).2];exact ((hGflat y d).mp hyG).1
      have hxGb : x ∈ F.get (c (bG b)) := by
        rw [(hc (bG b)).2];exact ((hGflat y (bG b)).mp hyGb).1
      intro he
      have hIndices := hinj hxG hxGb he
      have hSets : G₀.get d=G₀.get (bG b) :=
        (hc d).2.symm.trans ((congrArg F.get hIndices).trans (hc (bG b)).2)
      have hSame : oldU.get e=bornU.get b :=
        hGetOld.trans ((congrArg ((Subtype.val : U → Y) ⁻¹' ·) hSets).trans (hbG b))
      let v : Fin (oldU ++ bornU).length := ⟨e.val,by simp only [List.length_append];omega⟩
      let w : Fin (oldU ++ bornU).length := ⟨oldU.length+b.val,by simp only [List.length_append];omega⟩
      have hv : (oldU ++ bornU).get v=oldU.get e := by
        simp only [v,List.get_eq_getElem,List.getElem_append_left e.isLt]
      have hw : (oldU ++ bornU).get w=bornU.get b := by
        simp only [w,List.get_eq_getElem,List.getElem_append_right (by omega : oldU.length ≤ oldU.length+b.val),
          Nat.add_sub_cancel_left]
      have heq := eq_of_eventually_mem_iff hLowerFull
        (show y ∈ (oldU ++ bornU).get v from by rw [hv];exact hy.2)
        (show y ∈ (oldU ++ bornU).get w from by rw [hw];exact hyB)
        (Eventually.of_forall fun _ => by rw [hv,hw,hSame])
      have hh := congrArg Fin.val heq
      change e.val=oldU.length+b.val at hh
      omega
    have hGeom := coordinate_reduced_family_geometry (X := CMfd.of (n := n) U)
      hGeo.1 hZ hBornSNC hTrBorn k (s (c d)) (s a) q (hs a hxa) hFreeZ hFZ hDiffZ
    have hcZ := VanishingIdealCoherent.isCoherent_vanishingIdeal hZ
    have hTrace : oldTraceIdeal (X := CMfd.of (n := n) U) L oldU e=vanishingIdeal (n := n) Z := by
      ext y g
      constructor
      · intro hg
        apply MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt (inter_subset_left : Z ⊆ L) hg.1
        exact IsInSpanOnAt.mono (fun f hf => ⟨hf.1,hf.2.mono fun z hz hzZ => hz hzZ.2⟩) hg.2
      · intro hg
        by_cases hyL : y ∈ L
        · have hspan := (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem (N := L) (E := G)
            hGeo.2.1 hGeo.2.2.1 hyL gd hg.1).mpr
              (show (vanishingIdeal (n := n) (L ∩ G.get gd)).mem y g from by
                simpa only [hgd,←hGetOld] using hg)
          exact ⟨hg.1,by simpa only [hgd,←hGetOld] using hspan⟩
        · exact restrictOn_eq_top_of_disjoint (W := L) (𝔞 := vanishingIdeal (n := n) (oldU.get e))
            hGeo.1.1.isOpen_compl hyL (Set.compl_inter_self L) hg.1
    have hDunit := HironakaSharpActualChronologicalResidualDictionary.monomialPartAlong_eq_unit_of_no_member_factor
      hBornSNC hTrBorn hcZ hGeom.2.2
    have hJ := (HironakaSharpActualChronologicalResidualDictionary.nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
      hGeo.1 hBornSNC hTrBorn hcZ hGeom.2.2).trans
        (normalized_vanishingIdeal_of_subset (X := CMfd.of (n := n) U) (inter_subset_left : Z ⊆ L))
    have hJwhole : oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e=vanishingIdeal (n := n) Z := by
      change nonmonomialPartAlong n L (oldTraceIdeal (X := CMfd.of (n := n) U) L oldU e) bornU=_
      rw [hTrace]
      exact hJ
    refine ⟨?_,hJwhole,?_⟩
    · intro y _hyL
      change (monomialPartAlong n L (oldTraceIdeal (X := CMfd.of (n := n) U) L oldU e) bornU).mem y 1
      rw [hTrace,hDunit]
      exact holomorphicAt_const 1
    · intro y hyL
      rw [hJwhole]
      exact hGeom.2.1 y hyL
  have hOldInput (e : Fin oldU.length) : ∃ h : Fin E.length,h ≠ j ∧
      oldU.get e=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h) := by
    let v : Fin (old.eraseIdx j.val).length := Fin.cast (List.length_map _) e
    have hv : oldU.get e=(Subtype.val : U → Y) ⁻¹' (old.eraseIdx j.val).get v := by
      simp only [oldU,v,List.get_eq_getElem,List.getElem_map,Fin.val_cast]
    obtain ⟨m,hm,hmj,hget⟩ := List.mem_eraseIdx_iff_getElem.mp (List.get_mem (old.eraseIdx j.val) v)
    let h : Fin E.length := ⟨m,by simpa only [old,List.length_map] using hm⟩
    have hGetm : old.get ⟨m,hm⟩=strictAlong T (E.get h) := by
      simp only [old,List.get_eq_getElem,List.getElem_map,h]
    exact ⟨h,fun he => hmj (congrArg Fin.val he),hv.trans
      (congrArg ((Subtype.val : U → Y) ⁻¹' ·) (hget.symm.trans hGetm))⟩
  have hCoverage (e : Fin oldU.length) : ∃ t : Option (Fin G₀.length),
      oldU.get e=t.elim ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i))
        (fun d => (Subtype.val : U → Y) ⁻¹' G₀.get d) := by
    obtain ⟨h,hhj,he⟩ := hOldInput e
    by_cases hhi : h=i
    · exact ⟨none,by simpa only [Option.elim,hhi] using he⟩
    · obtain ⟨d,hd⟩ := List.mem_iff_get.mp (hOtherG h hhi hhj)
      exact ⟨some d,he.trans (congrArg ((Subtype.val : U → Y) ⁻¹' ·) hd.symm)⟩
  let t : Fin oldU.length → Option (Fin G₀.length) := fun e => Classical.choose (hCoverage e)
  have hCover (e : Fin oldU.length) : oldU.get e=(t e).elim
      ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i))
      (fun d => (Subtype.val : U → Y) ⁻¹' G₀.get d) := Classical.choose_spec (hCoverage e)
  let K : Option (Fin G₀.length) → Set U := fun o => o.elim R
    (fun d => L ∩ (Subtype.val : U → Y) ⁻¹' G₀.get d)
  let p : Option (Fin G₀.length) → Fin n := fun o => o.elim (s a) (fun d => s (c d))
  have hRows (e : Fin oldU.length) :
      oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e=vanishingIdeal (n := n) (K (t e)) ∧
      ∀ y ∈ L,ordinaryTraceOrder L (oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e) y ≤ 1 := by
    have he := hCover e
    cases ht : t e with
    | none =>
      have hJ : oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e=vanishingIdeal (n := n) R := by
        change nonmonomialPartAlong n L (restrictOn n L (vanishingIdeal (n := n) (oldU.get e))) bornU=_
        rw [ht] at he
        rw [he]
        exact hProcParts.2
      refine ⟨by simpa only [ht,K,Option.elim] using hJ,?_⟩
      intro y hyL
      rw [hJ]
      exact hRGeometry.2.1 y hyL
    | some d =>
      rw [ht] at he
      have hh := hOtherParts e d he
      refine ⟨?_,hh.2.2⟩
      simpa only [ht,K,Option.elim,he] using hh.2.1
  have hPosition (h : Fin E.length) (hhj : h ≠ j) : ∃ e : Fin oldU.length,
      oldU.get e=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h) := by
    apply List.mem_iff_get.mp
    apply List.mem_map.mpr
    refine ⟨strictAlong T (E.get h),?_,rfl⟩
    exact List.mem_eraseIdx_iff_getElem.mpr
      ⟨h.val,by simpa only [old,List.length_map] using h.isLt,
        fun he => hhj (Fin.ext he),by simp only [old,List.getElem_map,List.get_eq_getElem]⟩
  have hOriginalRows (h : Fin E.length) (hhj : h ≠ j) : ∃ e : Fin oldU.length,
      oldU.get e=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h) ∧
      if h=i then
        oldMonomialPart (X := CMfd.of (n := n) U) L oldU bornU e=Mi ∧
          oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e=vanishingIdeal (n := n) R
      else
        (∀ y ∈ L,(oldMonomialPart (X := CMfd.of (n := n) U) L oldU bornU e).mem y 1) ∧
          oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e=
            vanishingIdeal (n := n) (L ∩ (Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h)) := by
    obtain ⟨e,he⟩ := hPosition h hhj
    refine ⟨e,he,?_⟩
    by_cases hhi : h=i
    · rw [if_pos hhi]
      subst h
      simpa only [oldMonomialPart,oldResidualPart,oldTraceIdeal,he] using hProcParts
    · simp only [if_neg hhi]
      obtain ⟨d,hd⟩ := List.mem_iff_get.mp (hOtherG h hhi hhj)
      have hE : oldU.get e=(Subtype.val : U → Y) ⁻¹' G₀.get d :=
        he.trans (congrArg ((Subtype.val : U → Y) ⁻¹' ·) hd.symm)
      have hh := hOtherParts e d hE
      exact ⟨hh.1,by simpa only [he] using hh.2.1⟩
  have hAvoidHi (y : U) (hyL : y ∈ L) (hyC : y ∉ CU)
      (hyB : ∀ H ∈ B,y.val ∉ H) : y.val ∉ strictAlong T (E.get i) := by
    have hD1 : D.mem y.val 1 :=
      ⟨holomorphicAt_const 1,fun b _ hb => (hyB _ (List.get_mem B b) hb).elim⟩
    have hJ1 : (J i).mem y.val 1 := by
      rw [hWholeSi]
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hSi.1.isOpen_compl.mem_nhds hyC] with z hz hzSi
      exact (hz hzSi).elim
    have hcol : (nonmonomialPartAlong n A.N I B).mem y.val 1 := by
      change (oldResidualPart A.N old B oi).mem y.val 1
      rw [hNm]
      exact hJ1
    have hres := hcol.2 1 hD1
    have hcHi := VanishingIdealCoherent.isCoherent_vanishingIdeal hHism
    have hNormI : restrictOn n A.N I=I := by
      dsimp only [I,oldTraceIdeal]
      exact restrictOn_nested_eq (Subset.refl A.N)
        (VanishingIdealCoherent.isCoherent_vanishingIdeal
          (MonomialPart.isClosedSubmanifold_get hn
            (isSNCDivisor_of_sublist hFullE (List.sublist_append_left _ _)) oi))
    change (restrictOn n A.N I).mem y.val (1*1) at hres
    rw [hNormI] at hres
    have hI1 : I.mem y.val 1 := by simpa only [one_mul] using hres
    intro hyHi
    have hz : y.val ∈ I.zeroLocus := by
      have hIform : I=restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i))) := by
        simp only [I,oldTraceIdeal,hOldi]
      rw [hIform]
      apply (HironakaSharpActualTraceIncidence.zeroLocus_restrictOn_iff hcHi hyL.1).mpr
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHism.1]
    exact one_ne_zero (hz 1 hI1)
  let sd : Fin (Si :: G₀).length → Fin n := Fin.cases (s a) (fun d => s (c d))
  have hDenseCandidate := density_off_coordinate_window k Φ sd hsrc U hU hDomain
    (fun y => (hRaw y).2.1)
    (fun y hyL e => by
      refine Fin.cases ?_ (fun d => ?_) e
      · change y.val ∈ Si ↔ x ∈ Si ∧ flatCoord Φ (s a) y.val=0
        rw [and_iff_right hxiA]
        exact (hRaw y).2.2.1.trans (and_iff_right ((hRaw y).1.mp hyL.1))
      · change y.val ∈ G₀.get d ↔ x ∈ G₀.get d ∧ flatCoord Φ (s (c d)) y.val=0
        exact hGflat y d)
    (fun e he => by
      revert he
      refine Fin.cases ?_ (fun d => ?_) e
      · intro _
        exact hs a hxa
      · intro hd
        apply hs (c d)
        change x ∈ F.get (c d)
        rw [(hc d).2]
        exact hd)
  have hDenseLower : L ⊆ closure (L \ ⋃ H ∈ oldU ++ bornU,H) := by
    apply hDenseCandidate.trans (closure_mono ?_)
    intro y hy
    have hNotC : y ∉ CU := fun hh => hy.2 (mem_iUnion₂.mpr
      ⟨CU,List.mem_map.mpr ⟨Si,List.mem_cons_self,rfl⟩,hh⟩)
    have hNotG (H : Set U) (hHG : H ∈ G) : y ∉ H := by
      intro hh
      obtain ⟨K₀,hK,rfl⟩ := List.mem_map.mp hHG
      exact hy.2 (mem_iUnion₂.mpr
        ⟨_,List.mem_map.mpr ⟨K₀,List.mem_cons_of_mem Si hK,rfl⟩,hh⟩)
    have hNoHi : y.val ∉ strictAlong T (E.get i) := hAvoidHi y hy.1 hNotC (fun H hHB hyH =>
      hNotG _ (List.mem_map.mpr ⟨H,hBornG H hHB,rfl⟩) hyH)
    refine ⟨hy.1,fun hh => ?_⟩
    obtain ⟨H,hH,hyH⟩ := mem_iUnion₂.mp hh
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨e,rfl⟩ := List.mem_iff_get.mp hH
      have he := hCover e
      cases ht : t e with
      | none =>
        rw [ht] at he
        change oldU.get e=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i) at he
        rw [he] at hyH
        exact hNoHi hyH
      | some d =>
        rw [ht] at he
        apply hNotG _ (List.mem_map.mpr ⟨G₀.get d,List.get_mem G₀ d,rfl⟩)
        change oldU.get e=(Subtype.val : U → Y) ⁻¹' G₀.get d at he
        rw [he] at hyH
        exact hyH
    · exact hNotG H (hBornSub H hH) hyH
  have hKclosed (o : Option (Fin G₀.length)) : IsClosed (K o) := by
    cases o with
    | none => exact hRsm.1
    | some d =>
      exact hGeo.1.1.inter (((isSNCDivisor_of_sublist hF (List.eraseIdx_sublist F a.val)).1
        _ (List.get_mem G₀ d)).preimage continuous_subtype_val)
  have hKL (o : Option (Fin G₀.length)) : K o ⊆ L := by
    cases o <;> exact inter_subset_left
  have hSupportOld (e : Fin oldU.length) :
      preparedSupport (X := CMfd.of (n := n) U) L oldU bornU (Sum.inl e)=K (t e) := by
    change L ∩ (oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e).zeroLocus=K (t e)
    rw [(hRows e).1,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hKclosed (t e))]
    exact Set.inter_eq_right.mpr (hKL (t e))
  have hBaseG (y : U) (d : Fin G₀.length) (hy : y.val ∈ G₀.get d) : x ∈ F.get (c d) := by
    rw [(hc d).2]
    exact ((hGflat y d).mp hy).1
  have hOldFree (y : U) (e : Fin oldU.length) (hy : y ∈ K (t e)) : p (t e) ∉ QL := by
    cases ht : t e with
    | none => simpa only [ht,p,Option.elim] using hpL
    | some d =>
      have hyG : y.val ∈ G₀.get d := by
        rw [ht] at hy
        exact hy.2
      have hh := hs (c d) (hBaseG y d hyG)
      simpa only [ht,p,Option.elim,QL,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hh
  have hBornFree (y : U) (b : Fin bornU.length) (hyB : y ∈ bornU.get b) : q b ∉ QL := by
    have hyG : y.val ∈ G₀.get (bG b) := by rw [←hbG] at hyB;exact hyB
    have hh := hs (c (bG b)) (hBaseG y (bG b) hyG)
    simpa only [q,QL,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hh
  let pp : Fin oldU.length ⊕ Fin bornU.length → Fin n := Sum.elim (fun e => p (t e)) q
  have hPreparedFrame (y : U) : IsCoordinateFamilyAt n
      (fun o : Option (Fin oldU.length ⊕ Fin bornU.length) =>
        o.elim L (preparedSupport (X := CMfd.of (n := n) U) L oldU bornU))
      (fun o => o.elim QL (fun b => QL ∪ {pp b})) y := by
    apply IsCoordinateFamilyAt.reindex (hFrame y)
      (fun o : Option (Fin oldU.length ⊕ Fin bornU.length) => o.elim (some none)
        (Sum.elim
          (fun e => (t e).elim (some (some (some none)))
            (fun d => some (some (some (some (Sum.inr d))))))
          (fun b => some (some (some (some (Sum.inr (bG b))))))))
    · rintro (_ | (e | b))
      · rfl
      · change preparedSupport (X := CMfd.of (n := n) U) L oldU bornU (Sum.inl e)=_
        rw [hSupportOld]
        cases ht : t e <;> simp only [Option.elim,Sum.elim_inl,ht,windowSetFamily] <;> rfl
      · change L ∩ bornU.get b=(Subtype.val : U → Y) ⁻¹' (Sj ∩ G₀.get (bG b))
        rw [Set.preimage_inter,hbG]
    · rintro (_ | (e | b))
      · rfl
      · cases ht : t e <;> simp only [Option.elim,Sum.elim_inl,pp,p,ht,windowNormalFamily] <;> rfl
      · rfl
  have hSiHi : Si ⊆ strictAlong T (E.get i) := by
    intro y hy
    have hz : y ∈ (vanishingIdeal (n := n) (strictAlong T (E.get i))).zeroLocus := by
      intro f hf
      have hfI : I.mem y f := by
        change (restrictOn n A.N (vanishingIdeal (n := n) (old.get oi))).mem y f
        rw [hOldi]
        exact le_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hHism) y f hf
      have hfJ : (J i).mem y f := by
        rw [←hNm]
        exact le_nonmonomialPartAlong_self hParts.1 y f hfI
      exact hy.2 f hfJ
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHism.1] at hz
  have hRHi : R ⊆ (Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i) := fun _ hy => hSiHi hy.2
  have hOldSNC : IsSNCDivisor n oldU :=
    isSNCDivisor_of_sublist hLowerFull (List.sublist_append_left _ _)
  have hOldBornNe (y : U) (e : Fin oldU.length) (b : Fin bornU.length)
      (hye : y ∈ oldU.get e) (hyb : y ∈ bornU.get b) : oldU.get e ≠ bornU.get b := by
    intro hSame
    let v : Fin (oldU ++ bornU).length := ⟨e.val,by simp only [List.length_append];omega⟩
    let w : Fin (oldU ++ bornU).length := ⟨oldU.length+b.val,by simp only [List.length_append];omega⟩
    have hv : (oldU ++ bornU).get v=oldU.get e := by
      simp only [v,List.get_eq_getElem,List.getElem_append_left e.isLt]
    have hw : (oldU ++ bornU).get w=bornU.get b := by
      simp only [w,List.get_eq_getElem,List.getElem_append_right (by omega : oldU.length ≤ oldU.length+b.val),
        Nat.add_sub_cancel_left]
    have heq := eq_of_eventually_mem_iff hLowerFull
      (show y ∈ (oldU ++ bornU).get v from by rw [hv];exact hye)
      (show y ∈ (oldU ++ bornU).get w from by rw [hw];exact hyb)
      (Eventually.of_forall fun _ => by rw [hv,hw,hSame])
    have hh := congrArg Fin.val heq
    change e.val=oldU.length+b.val at hh
    omega
  have hSameG (y : U) (d e : Fin G₀.length) (hyd : y.val ∈ G₀.get d)
      (hye : y.val ∈ G₀.get e) (he : s (c d)=s (c e)) : G₀.get d=G₀.get e :=
    (hc d).2.symm.trans ((congrArg F.get (hinj (hBaseG y d hyd) (hBaseG y e hye) he)).trans (hc e).2)
  have hOldCoordsInj (y : U) : Set.InjOn (fun e => p (t e)) {e | y ∈ K (t e)} := by
    intro e hye f hyf he
    change y ∈ K (t e) at hye
    change y ∈ K (t f) at hyf
    cases hte : t e with
    | none =>
      have hyeR : y ∈ R := by simpa only [K,hte,Option.elim] using hye
      have hee : oldU.get e=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i) := by
        simpa only [hte,Option.elim] using hCover e
      cases htf : t f with
      | none =>
        have hyfR : y ∈ R := by simpa only [K,htf,Option.elim] using hyf
        have hff : oldU.get f=(Subtype.val : U → Y) ⁻¹' strictAlong T (E.get i) := by
          simpa only [htf,Option.elim] using hCover f
        exact eq_of_eventually_mem_iff hOldSNC (by rw [hee];exact hRHi hyeR)
          (by rw [hff];exact hRHi hyfR) (Eventually.of_forall fun _ => by rw [hee,hff])
      | some d =>
        have hyG : y.val ∈ G₀.get d := by rw [htf] at hyf;exact hyf.2
        have hEq : s a=s (c d) := by simpa only [p,hte,htf,Option.elim] using he
        exact ((hc d).1 (hinj hxa (hBaseG y d hyG) hEq).symm).elim
    | some d =>
      have hyG : y.val ∈ G₀.get d := by rw [hte] at hye;exact hye.2
      have hee : oldU.get e=(Subtype.val : U → Y) ⁻¹' G₀.get d := by
        simpa only [hte,Option.elim] using hCover e
      cases htf : t f with
      | none =>
        have hEq : s (c d)=s a := by simpa only [p,hte,htf,Option.elim] using he
        exact ((hc d).1 (hinj (hBaseG y d hyG) hxa hEq)).elim
      | some v =>
        have hyV : y.val ∈ G₀.get v := by rw [htf] at hyf;exact hyf.2
        have hff : oldU.get f=(Subtype.val : U → Y) ⁻¹' G₀.get v := by
          simpa only [htf,Option.elim] using hCover f
        have hEq : s (c d)=s (c v) := by simpa only [p,hte,htf,Option.elim] using he
        have hSets := hSameG y d v hyG hyV hEq
        exact eq_of_eventually_mem_iff hOldSNC (by rw [hee];exact hyG) (by rw [hff];exact hyV)
          (Eventually.of_forall fun _ => by rw [hee,hff,hSets])
  have hBornCoordsInj (y : U) : Set.InjOn q {b | y ∈ bornU.get b} := by
    intro b hyb v hyv he
    change y ∈ bornU.get b at hyb
    change y ∈ bornU.get v at hyv
    have hyB : y.val ∈ G₀.get (bG b) := by rw [←hbG] at hyb;exact hyb
    have hyV : y.val ∈ G₀.get (bG v) := by rw [←hbG] at hyv;exact hyv
    have hSets := hSameG y (bG b) (bG v) hyB hyV he
    have hEqual : bornU.get b=bornU.get v :=
      (hbG b).symm.trans ((congrArg ((Subtype.val : U → Y) ⁻¹' ·) hSets).trans (hbG v))
    exact eq_of_eventually_mem_iff hBornSNC hyb hyv (Eventually.of_forall fun _ => by rw [hEqual])
  have hCrossCoords (y : U) (e : Fin oldU.length) (hye : y ∈ K (t e))
      (b : Fin bornU.length) (hyB : y ∈ bornU.get b) : p (t e) ≠ q b := by
    intro he
    cases hte : t e with
    | none =>
      have hyR : y ∈ R := by simpa only [hte,K,Option.elim] using hye
      exact hProcDiff y hyR b hyB (by simpa only [p,hte,Option.elim] using he)
    | some d =>
      have hyG : y.val ∈ G₀.get d := by rw [hte] at hye;exact hye.2
      have hyGb : y.val ∈ G₀.get (bG b) := by rw [←hbG] at hyB;exact hyB
      have hEq : s (c d)=s (c (bG b)) := by simpa only [p,hte,Option.elim,q] using he
      have hSets := hSameG y d (bG b) hyG hyGb hEq
      have hee : oldU.get e=(Subtype.val : U → Y) ⁻¹' G₀.get d := by
        simpa only [hte,Option.elim] using hCover e
      exact hOldBornNe y e b (by rw [hee];exact hyG) hyB
        (hee.trans ((congrArg ((Subtype.val : U → Y) ⁻¹' ·) hSets).trans (hbG b)))
  refine ⟨U,hxU,hGeo.1,hLowerFull,hTrBorn,hDenseLower,?_,?_⟩
  · simpa only [Mi,D,oldMonomialPart,oldTraceIdeal,hOldi] using hOriginalRows
  · change ∀ y ∈ L,(∀ e,ordinaryTraceOrder L
      (oldResidualPart (X := CMfd.of (n := n) U) L oldU bornU e) y ≤ 1) ∧
        IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) L oldU bornU y
    intro y hyL
    refine ⟨fun e => (hRows e).2 y hyL,QL,pp,hPreparedFrame y,?_,?_⟩
    · rintro (e | b) hz
      · exact hOldFree y e (hSupportOld e ▸ hz)
      · exact hBornFree y b hz.2
    · intro z hz v hv he
      rcases z with e | b
      · rcases v with f | v
        · exact congrArg Sum.inl (hOldCoordsInj y (show y ∈ K (t e) from hSupportOld e ▸ hz)
          (show y ∈ K (t f) from hSupportOld f ▸ hv) he)
        · exact (hCrossCoords y e (hSupportOld e ▸ hz) v hv.2 he).elim
      · rcases v with e | v
        · exact (hCrossCoords y e (hSupportOld e ▸ hv) b hz.2 he.symm).elim
        · exact congrArg Sum.inr (hBornCoordsInj y hz.2 hv.2 he)

end
end Hironaka.HironakaG4LowerPreparedNeighborhood
