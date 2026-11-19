import Hironaka.Resolution.HironakaG34FoldRecords
import Hironaka.Resolution.HironakaG34LocalIdentityCover
import Hironaka.Resolution.HironakaG8P1ForeignCount

/-! # Dimension 3 of route (L): centres of dimension ≤ 1 inside the lower bad locus of a surface are protected

Lane G34 (run 0080, round 6).  Blueprint: `hironaka-g34-resume-surface-protection.tex`.
Route note: `work/hironaka-resume-20261111/G34/DIM3-ROUTE.md`.

* `protectedWindowAt_of_curve_cover` (local, tower-free): on a carrier `N` pure of dimension `3` with
  a family of prepared windows (`Haux :: (L ++ born)` SNC and transverse to `N`), a closed submanifold
  `C` of dimension `≤ 1` at `x` lying near `x` in `N ∩ H ∩ ⋃ born` (`H` a member of `L`) carries the
  protected-window certificate at `x`: a point (point NC), or a curve, which by the identity cover is
  inside ONE `N ∩ H ∩ born_b` and by same-dimension filling equals it near `x` (a stratum). -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34SurfaceProtection
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail
  HomogenizedGlueingTower HironakaG4RecordedTowerResidualCompatibility
  HironakaG34LowerCleanupLift RestrictEmptyTower BoundaryCount

section Lists
variable {α β : Type*}

theorem get_map_append_left (f : α → β) (L K : List α) (a : Fin L.length) :
    ((L ++ K).map f).get ⟨a.val, by simp only [List.length_map, List.length_append]; omega⟩ =
      f (L.get a) := by
  simp

theorem get_map_append_right (f : α → β) (L K : List α) (b : Fin K.length) :
    ((L ++ K).map f).get ⟨L.length + b.val, by simp only [List.length_map, List.length_append]; omega⟩ =
      f (K.get b) := by
  simp [List.getElem_append_right]

theorem get_cons_succ' (h : β) (L : List β) (a : ℕ) (ha : a < L.length) :
    (h :: L).get ⟨a + 1, by simp only [List.length_cons]; omega⟩ = L.get ⟨a, ha⟩ := by
  simp

end Lists

section Local
variable {n : ℕ} {Y : CMfd.{u} n}

/-- **The certificate at a point of a centre of dimension `≤ 1` covered by curves of a 3-dimensional
carrier** (tower-free). -/
theorem protectedWindowAt_of_curve_cover (hn : 0 < n) {N Si Hj C : Set Y} {L born : List (Set Y)}
    (hNc : IsClosed N) (hN3 : ∀ z ∈ N, RegularAtDim (n := n) N z 3)
    (a : Fin L.length) (ha : L.get a = Hj)
    (hHj : IsComplexAnalyticSubset (n := n) Hj)
    (hborn : ∀ b : Fin born.length, IsComplexAnalyticSubset (n := n) (born.get b))
    {x : Y}
    (hWin : ∀ O : Opens Y, x ∈ O → ∃ U : Opens Y, x ∈ U ∧ (U : Set Y) ⊆ O ∧ ∃ Haux : Set U,
      IsSNCDivisor n (Haux :: (L ++ born).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → Y) ⁻¹' N)
        (Haux :: (L ++ born).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
      (Subtype.val : U → Y) ⁻¹' Si = (Subtype.val : U → Y) ⁻¹' N ∩ Haux)
    (hC : IsClosedSubmanifold n C) (hxC : x ∈ C)
    (hCdim : ∀ k, RegularAtDim (n := n) C x k → k ≤ 1)
    (hcov : ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ N ∧ y ∈ Hj ∧ ∃ b, y ∈ born.get b) :
    ProtectedWindowAt N Si (L ++ born) C x := by
  obtain ⟨k, hk⟩ := hC.2 x hxC
  have hk1 := hCdim k hk
  rcases Nat.lt_or_ge k 1 with hk0 | hk1'
  · have hk0' : k = 0 := by omega
    subst hk0'
    obtain ⟨O, hOsub, hOo, hxO⟩ :=
      mem_nhds_iff.mp (HironakaG34SurfaceSharpCleanup.eventually_mem_iff_eq_of_regularAtDim_zero hk)
    obtain ⟨U, hxU, hUO, Haux, hSNC, hTr, hSlice⟩ := hWin ⟨O, hOo⟩ hxO
    refine ⟨U, hxU, Haux, hSlice, hSNC, hTr, ?_⟩
    refine HironakaG34SurfaceSharpCleanup.hasNormalCrossings_of_regularAtDim_zero hSNC fun z hz => ?_
    have hzx : z.val = x := (show _ ↔ _ from hOsub (hUO z.2)).mp hz
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (by rw [hzx]; exact hk)
  · have hkeq : k = 1 := by omega
    subst hkeq
    have hNan : IsComplexAnalyticSubset (n := n) N :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        ⟨hNc, fun z hz => ⟨3, hN3 z hz⟩⟩
    have hCan : IsComplexAnalyticSubset (n := n) C :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC
    -- one born member contains `C` near `x`
    obtain ⟨b, hb⟩ := HironakaG34LocalIdentityCover.exists_eventually_subset_of_cover hk
      (fun b : Fin born.length => born.get b) hborn (hcov.mono fun y hy hyC => (hy hyC).2.2)
    have hLan : IsComplexAnalyticSubset (n := n) (N ∩ Hj ∩ born.get b) :=
      (hNan.inter hHj).inter (hborn b)
    have hCL : ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ N ∩ Hj ∩ born.get b :=
      (hcov.and hb).mono fun y hy hyC => ⟨⟨(hy.1 hyC).1, (hy.1 hyC).2.1⟩, hy.2 hyC⟩
    -- the curve `N ∩ Hj ∩ born_b` is regular of dimension 1 near `x` (analysis window)
    have hLdim : ∀ᶠ y in 𝓝 x, y ∈ N ∩ Hj ∩ born.get b →
        RegularAtDim (n := n) (N ∩ Hj ∩ born.get b) y 1 := by
      obtain ⟨U₀, hxU₀, -, Haux₀, hSNC₀, hTr₀, -⟩ := hWin ⊤ (by simp)
      filter_upwards [U₀.isOpen.mem_nhds hxU₀] with y hyU hyL
      let z : U₀ := ⟨y, hyU⟩
      let f : Set Y → Set U₀ := ((Subtype.val : U₀ → Y) ⁻¹' ·)
      let G : List (Set U₀) := Haux₀ :: (L ++ born).map f
      have hjlt : a.val + 1 < G.length := by
        have := a.isLt
        simp only [G, List.length_cons, List.length_map, List.length_append]
        omega
      have hblt : L.length + b.val + 1 < G.length := by
        have := b.isLt
        simp only [G, List.length_cons, List.length_map, List.length_append]
        omega
      let jG : Fin G.length := ⟨a.val + 1, hjlt⟩
      let bG : Fin G.length := ⟨L.length + b.val + 1, hblt⟩
      have hjG : G.get jG = f Hj := by
        rw [← ha]
        simp [G, jG]
      have hbG : G.get bG = f (born.get b) := by
        simp [G, bG, List.getElem_append_right]
      have hjb : jG ≠ bG := by
        intro h
        have := congrArg Fin.val h
        simp only [jG, bG] at this
        omega
      have hzN : z ∈ f N := hyL.1.1
      have hzH : z ∈ f Hj := hyL.1.2
      have hzb : z ∈ f (born.get b) := hyL.2
      have hN3z : RegularAtDim (n := n) (f N) z 3 :=
        AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hN3 y hyL.1.1)
      have hHmem : f Hj ∈ G := by
        rw [← hjG]; exact List.get_mem G jG
      obtain ⟨-, h2⟩ := HironakaG8P1ForeignCount.regularAtDim_inter_of_mem hTr₀ hHmem hzN hzH hN3z
      have hTr2 : IsTransverse n (f N ∩ memberInter G {jG}) [f (born.get b)] :=
        BoundaryCountAlong.isTransverse_inter_memberInter_of_forall hSNC₀ hTr₀ {jG}
          (fun H hH => ⟨bG, by simpa using hjb.symm, by rw [List.mem_singleton.mp hH, hbG]⟩)
      rw [DivisorExponentAlong.memberInter_singleton, hjG] at hTr2
      obtain ⟨-, h1⟩ := HironakaG8P1ForeignCount.regularAtDim_inter_of_mem hTr2
        (List.mem_singleton_self _) ⟨hzN, hzH⟩ hzb h2
      exact (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U₀) (A := N ∩ Hj ∩ born.get b)
        (x := z) (k := 1)).mp h1
    have hLC := HironakaG34LocalIdentityCover.eventually_subset_of_same_dim hCan hLan hk hLdim hCL
    obtain ⟨O, hOsub, hOo, hxO⟩ := mem_nhds_iff.mp (hCL.and hLC)
    obtain ⟨U, hxU, hUO, Haux, hSNC, hTr, hSlice⟩ := hWin ⟨O, hOo⟩ hxO
    refine protectedWindowAt_of_window_strata hn U hxU Haux hSlice hSNC hTr ?_
    let f : Set Y → Set U := ((Subtype.val : U → Y) ⁻¹' ·)
    have hjlt : a.val < ((L ++ born).map f).length := by
      have := a.isLt
      simp only [List.length_map, List.length_append]
      omega
    have hblt : L.length + b.val < ((L ++ born).map f).length := by
      have := b.isLt
      simp only [List.length_map, List.length_append]
      omega
    let jF : Fin ((L ++ born).map f).length := ⟨a.val, hjlt⟩
    let bF : Fin ((L ++ born).map f).length := ⟨L.length + b.val, hblt⟩
    have hjF : ((L ++ born).map f).get jF = f Hj := by
      rw [← ha]; exact get_map_append_left f L born a
    have hbF : ((L ++ born).map f).get bF = f (born.get b) := get_map_append_right f L born b
    have hiff : ∀ y : U, y ∈ (Subtype.val : U → Y) ⁻¹' C ↔
        y ∈ (Subtype.val : U → Y) ⁻¹' N ∩ memberInter ((L ++ born).map f) {jF, bF} := by
      intro y
      have hyO := (show _ ∧ _ from hOsub (hUO y.2))
      have hmi : y ∈ memberInter ((L ++ born).map f) {jF, bF} ↔ y ∈ f Hj ∧ y ∈ f (born.get b) := by
        simp only [memberInter, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
          forall_eq, mem_ofPred_eq, hjF, hbF]
      rw [mem_inter_iff, hmi]
      constructor
      · intro hyC
        obtain ⟨⟨h1, h2⟩, h3⟩ := hyO.1 hyC
        exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact hyO.2 ⟨⟨h1, h2⟩, h3⟩
    intro z hz
    exact ⟨{jF, bF}, (hiff z).mp hz, Eventually.of_forall hiff⟩

end Local

section CopiedSupport
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MemberInterTowerAlong NormalCrossings
  HironakaG4OriginalSelectedResidualTail HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualTraceIncidence
  HironakaSharpActualCurveWholeBoundaryTransversality NormalCrossingsComparison
  HironakaSharpOriginalProductTraceOrder SimultaneousNormalCrossings
  NonmonomialTransformAlong RelativePrincipalizationSpan RestrictedIdealExtension
  CoefficientIdealRestriction DropMembers GermIdealOrder IdealWeightPowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MemberInterLocusAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Private verbatim copy of `HironakaG4OriginalSelectedLowerBoundaryHistory.actual_selected_support_subset_own_old`
(private there): the selected support lies in the strict transform of its own original member. -/
private theorem support_subset_own_old (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    A.N ∩ A.ideal.zeroLocus ⊆ strictAlong T (E.get i) := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let H := strictAlong T (E.get i)
  let I := restrictOn n B.N (vanishingIdeal (n := n) H)
  have hAN : A.N=B.N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hActual := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  obtain ⟨hcI,_hnzI,hNm,_hFactor⟩ := hActual.2.2.2.2 i
  have hIle : I.Le A.ideal := by
    rw [←hNm]
    exact le_nonmonomialPartAlong_self hcI
  have hMem : H ∈ E.map (strictAlong T) ++ B.E :=
    List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E i))
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hMem
  have hHsmooth := MonomialPart.isClosedSubmanifold_get hn hActual.2.1 k
  rw [hk] at hHsmooth
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsmooth
  change A.N ∩ A.ideal.zeroLocus ⊆ strictAlong T (E.get i)
  intro x hx
  have hxN : x ∈ B.N := hAN ▸ hx.1
  have hxI : x ∈ I.zeroLocus := fun g hg => hx.2 g (hIle x g hg)
  have hxH := (zeroLocus_restrictOn_iff hcH hxN).mp hxI
  rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1] at hxH

/-- Private verbatim copy from `HironakaG4OriginalSelectedLowerBadHistory` (private there). -/
private theorem actual_remaining_boundary_dictionary {Q : CMfd.{u} n} (W : Set X) (E : List (Set X))
    (i : ℕ) (T : BlowupTower X Y) (S : Set Y) (R : BlowupTower Y Q) :
    let B := geoTransformAlong (geometricTemplate W []) T
    (geoTransformAlong (geometricTemplate S ((E.map (strictAlong T)).eraseIdx i ++ B.E)) R).E=
      (E.map (strictAlong (T.append R))).eraseIdx i ++
        (geoTransformAlong (geometricTemplate W []) (T.append R)).E := by
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx i ++ B.E
  let K := geometricTemplate (univ : Set Y) []
  have hOld : (E.map (strictAlong T)).map (strictAlong R)=E.map (strictAlong (T.append R)) := by
    rw [List.map_map]
    exact congrArg (fun f : Set X → Set Q => E.map f)
      (funext fun H => (strictAlong_append T H R).symm)
  have hBorn : (geoTransformAlong (geometricTemplate W []) (T.append R)).E=
      B.E.map (strictAlong R) ++ (geoTransformAlong K R).E := by
    rw [geoTransformAlong_append]
    exact HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
      B K rfl R
  calc
    (geoTransformAlong (geometricTemplate S F) R).E
        = F.map (strictAlong R) ++ (geoTransformAlong K R).E :=
      HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
        (geometricTemplate S F) K rfl R
    _ = ((E.map (strictAlong T)).eraseIdx i).map (strictAlong R) ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [List.map_append,List.append_assoc]
    _ = (E.map (strictAlong (T.append R))).eraseIdx i ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [←List.eraseIdx_map,hOld]
    _ = _ := by rw [←hBorn]

end CopiedSupport

section Tower
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **The certificate at a point of a prepared support, for a centre of dimension `≤ 1` inside the
lower sharp bad locus `B_j` of a 3-dimensional carrier.** -/
theorem protectedWindowAt_of_surface_bad (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hReg3 : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x 3)
    (i : Fin E.length) (hPrep : ActualRowPrepared W E i T)
    (j : Fin E.length) (hne : j ≠ i)
    {C : Set Y} (hC : IsClosedSubmanifold n C)
    (hCdim : ∀ z ∈ C, ∀ k, RegularAtDim (n := n) C z k → k ≤ 1)
    (hCB : C ⊆ originalSharpBadLocus (n := n)
      ((geoTransformAlong (geometricTemplate W []) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
      ((E.map (strictAlong T)).eraseIdx j.val ++ (geoTransformAlong (geometricTemplate W []) T).E))
    {x : Y} (hx : x ∈ C ∩ ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)) :
    ProtectedWindowAt (geoTransformAlong (geometricTemplate W []) T).N
      ((geoTransformAlong (geometricTemplate W []) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
      ((E.map (strictAlong T)).eraseIdx i.val ++ (geoTransformAlong (geometricTemplate W []) T).E)
      C x := by
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNi
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  have hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus := by
    rw [hNi]; exact hx.2
  have hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus := by
    rw [hNj]; exact (hCB hx.1).1
  obtain ⟨U₁, hxU₁, hU₁⟩ :=
    HironakaG34LowerBadMonomialSupport.actual_prepared_row_lower_bad_eq_monomial_support hn hW hE
      hdense i T hT hFull hPrep.1 hPrep.2.1 hPrep.2.2 j hne hxi hxj
  have hSjH := support_subset_own_old hn hW hE hdense j T hT hFull
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus ⊆
    strictAlong T (E.get j) at hSjH
  rw [hNj] at hSjH
  have hcov : ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      y ∈ strictAlong T (E.get j) ∧
      ∃ b, y ∈ (geoTransformAlong (geometricTemplate W []) T).E.get b := by
    filter_upwards [U₁.isOpen.mem_nhds hxU₁] with y hyU hyC
    obtain ⟨hySj, hyD⟩ := (hU₁ y hyU).mp (hCB hyC)
    refine ⟨hySj.1, hSjH hySj, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hyD ⟨holomorphicAt_const 1, fun b _ hyb => (hnone b hyb).elim⟩
  have hWin : ∀ O : Opens Y, x ∈ O → ∃ U : Opens Y, x ∈ U ∧ (U : Set Y) ⊆ O ∧ ∃ Haux : Set U,
      IsSNCDivisor n (Haux :: ((E.map (strictAlong T)).eraseIdx i.val ++
        (geoTransformAlong (geometricTemplate W []) T).E).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → Y) ⁻¹' (geoTransformAlong (geometricTemplate W []) T).N)
        (Haux :: ((E.map (strictAlong T)).eraseIdx i.val ++
          (geoTransformAlong (geometricTemplate W []) T).E).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
      (Subtype.val : U → Y) ⁻¹' ((geoTransformAlong (geometricTemplate W []) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) =
        (Subtype.val : U → Y) ⁻¹' (geoTransformAlong (geometricTemplate W []) T).N ∩ Haux := by
    intro O hxO
    obtain ⟨U, hxU, hUO, Haux, hSNC, hTr, hSlice, -⟩ :=
      HironakaActualProtectedOtherRowLocalStep.protected_slice_window hn hW hE hdense i T hT hFull
        hPrep.1 hPrep.2.1 hPrep.2.2 hxi O hxO
    exact ⟨U, hxU, hUO, Haux, hSNC, hTr, hSlice⟩
  have hjmem : strictAlong T (E.get j) ∈ (E.map (strictAlong T)).eraseIdx i.val :=
    List.mem_eraseIdx_iff_getElem.mpr ⟨j.val, by simp, fun h => hne (Fin.ext h), by simp⟩
  obtain ⟨a, ha⟩ := List.mem_iff_get.mp hjmem
  have hOld := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_left _ _)
  have hBorn := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_right _ _)
  have hHj : IsClosedSubmanifold n (strictAlong T (E.get j)) := by
    have hk := MonomialPart.isClosedSubmanifold_get hn hOld ⟨j.val, by simp⟩
    simpa using hk
  exact protectedWindowAt_of_curve_cover hn hRec.1.1 hReg3 a ha
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hHj)
    (fun b => AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (MonomialPart.isClosedSubmanifold_get hn hBorn b))
    hWin hC hx.1 (hCdim x hx.1) hcov

/-- Centres in the current sharp bad locus of a problem pure of dimension `d + 1` have dimension `≤ d`. -/
theorem regularAtDim_le_of_subset_sharpBad (hn : 0 < n) {Z : Set Y} {F : List (Set Y)} (d : ℕ)
    (hZ : IsClosedSubmanifold n Z) (hF : IsSNCDivisor n F)
    (hZd : Z ⊆ closure (Z \ ⋃ H ∈ F, H)) (hZreg : ∀ x ∈ Z, RegularAtDim (n := n) Z x (d+1))
    {Q : CMfd.{u} n} (R : BlowupTower Y Q)
    (h1 : IsGeoTestTower (geometricTemplate Z []) R)
    (h2 : IsGeoTestTower (geometricTemplate (univ : Set Y) F) R)
    {C : Set Q}
    (hCbad : C ⊆ originalSharpBadLocus (n := n) (strictAlong R Z)
      (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E) :
    ∀ x ∈ C, ∀ k, RegularAtDim (n := n) C x k → k ≤ d := by
  obtain ⟨hN, hDen⟩ := HironakaG34SurfaceSharpCleanup.lower_dense_of_two_tests hn hZ hF hZd R h1 h2
  have hthin := HironakaG4GeneralSharpBadLocus.originalSharpBadLocus_thin hN hDen
  have hreg := HironakaG34CarrierPureDimension.actual_carrier_regularAtDim hZ d hZreg R h1
  have hNid : (geoTransformAlong (geometricTemplate Z []) R).N = strictAlong R Z :=
    N_geoTransformAlong _ R
  rw [hNid] at hreg
  have hdim : AnalyticDimensionBasics.DimLE (n := n) (strictAlong R Z) (d+1) := fun x k hx =>
    (RegularPointDimension.eq_of_regularAtDim hx (hreg x hx.2.1)).le
  intro x _hx k hk
  have hCZ : C ⊆ strictAlong R Z := fun y hy => (hCbad hy).1
  have hlt := ThinDimensionDrop.lt_of_regularAtDim_of_thin
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hCZ
    (fun O hO hOC => hthin O hO (hOC.trans hCbad)) hdim hk
  omega

/-- **Lower cleanups of surface problems are protected** (carrier pure of dimension `3`): along a tail
of the lower problem `(S_j, F_j)` with its two zero-mark tests and lower sharp centres, every centre is
certified at every point of every prepared support. -/
theorem protectedTail_of_surface_lower
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (j : Fin E.length)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hReg3 : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x 3)
    (hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T) (hj : j ∉ P) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
    let Z := A.N ∩ A.ideal.zeroLocus
    IsClosedSubmanifold n Z → IsSNCDivisor n F → Z ⊆ closure (Z \ ⋃ H ∈ F, H) →
    (∀ x ∈ Z, RegularAtDim (n := n) Z x 2) →
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate Z []) R →
      IsGeoTestTower (geometricTemplate (univ : Set Y) F) R →
      CurrentSharpCentres Z F R → ProtectedTail W E P T R := by
  intro A B F Z hZ hF hZd hZreg
  obtain ⟨_hZ, _hWhole, hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  have hRecT := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  intro Q R
  induction R with
  | refl => intro _ _ _; trivial
  | @step Q₀ Q₁ R C π hπ ih =>
    intro h1 h2 hLS
    obtain ⟨h10, hA1⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp h1
    obtain ⟨h20, -⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp h2
    obtain ⟨hLS0, hCbad⟩ := hLS
    have hProt0 : ProtectedTail W E P T R := ih h10 h20 hLS0
    refine ⟨hProt0, ?_⟩
    have hR0 := HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests Z F R h10 h20
    obtain ⟨hTR, hFullR, _hNR, hZR, hSub, hChronN, hChronI⟩ := hTails R hR0
    have hPR := actual_rows_prepared_of_protected_tail hn hW hE hdense P T hP R hTR hFullR hProt0
    have hGeoN : (geoTransformAlong (geometricTemplate W []) (T.append R)).N = strictAlong R A.N :=
      (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j))
        (T.append R)).1.symm.trans hChronN
    have hSupp : (geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus =
        strictAlong R Z := by
      rw [hGeoN, hChronI, BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hZR.1]
      exact inter_eq_right.mpr hSub
    have hLowE : (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E =
        (E.map (strictAlong (T.append R))).eraseIdx j.val ++
          (geoTransformAlong (geometricTemplate W []) (T.append R)).E := by
      rw [← actual_remaining_boundary_dictionary W E j.val T Z R,
        HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
          (geometricTemplate Z F) (geometricTemplate (univ : Set Y) []) rfl R,
        HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
          (geometricTemplate (univ : Set Y) F) (geometricTemplate (univ : Set Y) []) rfl R]
      rfl
    have hCB : C ⊆ originalSharpBadLocus (n := n)
        ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus)
        ((E.map (strictAlong (T.append R))).eraseIdx j.val ++
          (geoTransformAlong (geometricTemplate W []) (T.append R)).E) := by
      rw [hSupp, ← hLowE]
      exact hCbad
    have hCdim := regularAtDim_le_of_subset_sharpBad hn 1 hZ hF hZd hZreg R h10 h20 hCbad
    have hReg3R : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) (T.append R)).N x 3 := by
      have hTail : IsGeoTestTower (geoTransformAlong (geometricTemplate W []) T) R :=
        ((isGeoTestTower_append_iff (geometricTemplate W []) T R).mp hTR).2
      have h := (HironakaG34CarrierPureDimension.geoTransformAlong_N_regularAtDim
        (geoTransformAlong (geometricTemplate W []) T) hRecT.1.1 hReg3 R hTail).2
      rw [← geoTransformAlong_append (geometricTemplate W []) T R] at h
      exact h
    intro i hi x hx
    have hne : j ≠ i := fun h => hj (h ▸ hi)
    exact protectedWindowAt_of_surface_bad hn hW hE hdense (T.append R) hTR hFullR hReg3R i
      (hPR i hi) j hne hA1.1 hCdim hCB hx

/-- **The named statement of route (L) for `d = 2`** (`W` pure of dimension `3`), PROVED: the
unconditional surface cleanup of each lower problem is a certified lower cleanup. -/
theorem certifiedLowerCleanupsExist_two (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    CertifiedLowerCleanupsExist W E 2 := by
  intro Y T hT hFull hSharp hOrd hReg hDistinct P hP j hj
  obtain ⟨hL, hLreg, hLF, -, -⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd 2 hReg hDistinct j
  obtain ⟨-, hFj, hKj, -, -⟩ :=
    HironakaActualSharpBadFirstMaximumBlowup.actual_compact_sharp_bad_source
      hn hW hE hdense hK T hT hFull hSharp hOrd 2 hReg hDistinct j
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  rw [← hNj] at hL hLreg hLF hKj
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hOrd y hy j
  obtain ⟨Q, U, h1, h2, hS, -, -, -, hNC, -, -⟩ :=
    HironakaG34SurfaceSharpCleanup.exists_actual_sharp_cleanup_dim_two hn hL hFj hLF hLreg hKj
  obtain ⟨-, hDen⟩ := HironakaG34SurfaceSharpCleanup.lower_dense_of_two_tests hn hL hFj hLF U h1 h2
  have hLT := HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests _ _ U h1 h2
  obtain ⟨hNC', hDen'⟩ := HironakaG34SurfaceSharpCleanup.lower_nc_dense_of_two_template _ _ U hNC hDen
  exact ⟨Q, U, hLT, hS, hNC', hDen',
    protectedTail_of_surface_lower hn hW hE hdense j T hT hFull hReg hOrdj P hP hj hL hFj hLF hLreg
      U h1 h2 hS⟩

/-- **Threefolds, unconditional**: the sharp cleanup of every `(W, E)` with `W` pure of dimension `3`. -/
theorem exists_actual_sharp_cleanup_dim_three
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x 3)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ :=
  exists_actual_sharp_cleanup_of_certified_lower_cleanups hn hW hE hdense 2 hRegW hK
    (certifiedLowerCleanupsExist_two hn hW hE hdense hK)

open HironakaG34FoldRecords HironakaActualProcessedMaskFiniteBlock HironakaG4MonomialFamilyInvariant in
/-- **Threefolds, with full records** (fold with persistent preparedness and per-prefix records, then K3
with full readback), unconditional. -/
theorem exists_actual_sharp_cleanup_records_dim_three
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x 3)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      (∀ i : Fin E.length, ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (R : BlowupTower Y' Y),
        T'.append R = T ∧ PreparedAlong W E i T' R) ∧
      (∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head T k)) ∧
      ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
        let U := T.append R
        let A := geoTransformAlong (geometricTemplate W []) U
        let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N, tauD (factorMatrix W E U x) = 0) ∧
        IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
        IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ ∧
        ∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head U k) :=
  exists_actual_sharp_cleanup_records hn hW hE hdense 2 hRegW hK
    (certifiedLowerCleanupsExist_two hn hW hE hdense hK)

end Tower

end
end Hironaka.HironakaG34SurfaceProtection
