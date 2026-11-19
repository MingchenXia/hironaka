import Hironaka.Resolution.HironakaActualNativeSectionControlledTransform
import Hironaka.Blowup.SimultaneousNormalCrossings

/-! Actual adapted-coordinate geometry preserves each old boundary trace and the entire ordered old/born list on the same strict section. No canonical-value or intrinsic-descent conclusion is asserted. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualNativeSectionBoundaryTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupFibreDirection
  BlowupStrictSubmanifold BlowupStrictIdeal NormalCrossings BlowupSNCTransform
  SimultaneousNormalCrossings

theorem strict_inter_old_member
    {n : ℕ} (hn : 0 < n)
    {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {C N : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hNc : IsClosed N) (hCN : C ⊆ N)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hnc : HasNormalCrossings n C E) (i : Fin E.length) :
    geoStrictTransform π C (N ∩ E.get i) =
      geoStrictTransform π C N ∩ geoStrictTransform π C (E.get i) := by
  classical
  have hmono (A B : Set X) (hAB : A ⊆ B) :
      geoStrictTransform π C A ⊆ geoStrictTransform π C B := by
    apply closure_mono
    intro y hy
    exact ⟨hAB hy.1,hy.2⟩
  apply le_antisymm
  · intro y hy
    exact ⟨hmono _ _ inter_subset_left hy,hmono _ _ inter_subset_right hy⟩
  · rintro y ⟨hyN,hyH⟩
    have hEc : ∀ H ∈ E, IsClosed H := hE.1
    have hxH : π y ∈ E.get i :=
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hEc _ (List.get_mem _ _)) hyH
    by_cases hyC : π y ∈ C
    · have had := isAdaptedAt_of_hasNormalCrossings hn hCN hE hT hnc hyC
      obtain ⟨kC,kN,Φ,s,hΦt,hslt,hsinj,hflat⟩ := had
      have hx' : π y ∈ flatDomain Φ := ⟨mem_chart_source _ (π y),Φ.center_mem_source⟩
      have hflatC : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) (π y)).source →
          chartAt (ComplexModel n) (π y) x ∈ Φ.source →
          (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x) ∈
            complexCoordinatePlane n kC) := fun hx hxΦ => (hflat hx hxΦ).1
      let T : Finset (Fin n) := Finset.univ.filter (fun t => kN ≤ t.1)
      have hflatN : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) (π y)).source →
          chartAt (ComplexModel n) (π y) x ∈ Φ.source →
          (x ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x) ∈ coordSubspace T) := by
        intro x hx hxΦ
        rw [show T = Finset.univ.filter (fun t : Fin n => kN ≤ t.1) from rfl,
          coordSubspace_eq_complexCoordinatePlane]
        exact (hflat hx hxΦ).2.1
      have hflatH : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) (π y)).source →
          chartAt (ComplexModel n) (π y) x ∈ Φ.source →
          (x ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x) ∈ coordSubspace {s i}) := by
        intro x hx hxΦ
        rw [mem_coordSubspace_singleton]
        exact (hflat hx hxΦ).2.2 i hxH
      have hflatNH : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) (π y)).source →
          chartAt (ComplexModel n) (π y) x ∈ Φ.source →
          (x ∈ N ∩ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x) ∈
            coordSubspace (T ∪ {s i})) := by
        intro x hx hxΦ
        rw [Set.mem_inter_iff,hflatN hx hxΦ,hflatH hx hxΦ]
        change ((∀ t ∈ T, _ = 0) ∧ (∀ t ∈ ({s i} : Finset (Fin n)), _ = 0)) ↔
          ∀ t ∈ T ∪ {s i}, _ = 0
        constructor
        · rintro ⟨h1,h2⟩ t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact h1 t ht
          · exact h2 t ht
        · intro h
          exact ⟨fun t ht => h t (Finset.mem_union_left _ ht),
            fun t ht => h t (Finset.mem_union_right _ ht)⟩
      obtain ⟨j,hj,O,hO,hyO,W,hWs,hWeq,hℓ,_⟩ :=
        exists_monomialLocalInverse hπ hΦt hflatC hx'
      have hNu := (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatN
        hj hO hWs hWeq hℓ hyO).mp hyN
      have hHu := (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatH
        hj hO hWs hWeq hℓ hyO).mp hyH
      apply (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatNH
        hj hO hWs hWeq hℓ hyO).mpr
      refine ⟨?_,?_⟩
      · intro hjT
        rcases Finset.mem_union.mp hjT with ht | ht
        · exact hNu.1 ht
        · exact hHu.1 ht
      · intro t ht
        rcases Finset.mem_union.mp ht with ht | ht
        · exact hNu.2 t ht
        · exact hHu.2 t ht
    · apply subset_closure
      exact ⟨⟨geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hyN,hxH⟩,hyC⟩

theorem native_old_member_preimage
    {n : ℕ} (hn : 0 < n)
    {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {W : Set X} (hWc : IsClosed W) (D : Set W)
    {π : Y → X} (hπ : IsBlowupAlong n ((Subtype.val : W → X) '' D) π)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n W E)
    (hnc : HasNormalCrossings n ((Subtype.val : W → X) '' D) E) (i : Fin E.length) :
    let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
    let σ := HironakaActualClosedContactBlowupRestriction.restrictedProjection hWc D hπ
    (Subtype.val : S → Y) ⁻¹' geoStrictTransform π ((Subtype.val : W → X) '' D) (E.get i) =
      geoStrictTransform σ D ((Subtype.val : W → X) ⁻¹' E.get i) := by
  let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
  let σ := HironakaActualClosedContactBlowupRestriction.restrictedProjection hWc D hπ
  let H := (Subtype.val : W → X) ⁻¹' E.get i
  have himage : (Subtype.val : W → X) '' H = W ∩ E.get i := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  have hCN : (Subtype.val : W → X) '' D ⊆ W := by
    rintro _ ⟨x,_hx,rfl⟩
    exact x.property
  have ht := HironakaActualClosedContactBlowupRestriction.strictTransform_image hWc hπ H
  rw [himage,strict_inter_old_member hn hπ hWc hCN hE hT hnc i] at ht
  calc
    _ = (Subtype.val : S → Y) ⁻¹' (S ∩
        geoStrictTransform π ((Subtype.val : W → X) '' D) (E.get i)) := by
      ext y
      exact ⟨fun hy => ⟨y.property,hy⟩,fun hy => hy.2⟩
    _ = (Subtype.val : S → Y) ⁻¹' ((Subtype.val : S → Y) '' geoStrictTransform σ D H) :=
      congrArg (fun A : Set Y => (Subtype.val : S → Y) ⁻¹' A) ht.symm
    _ = geoStrictTransform σ D H := Set.preimage_image_eq _ Subtype.val_injective

theorem whole_ordered_boundary_preimage
    {n : ℕ} (hn : 0 < n)
    {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {W : Set X} (hWc : IsClosed W) (D : Set W)
    {π : Y → X} (hπ : IsBlowupAlong n ((Subtype.val : W → X) '' D) π)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n W E)
    (hnc : HasNormalCrossings n ((Subtype.val : W → X) '' D) E) :
    let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
    let σ := HironakaActualClosedContactBlowupRestriction.restrictedProjection hWc D hπ
    (E.map (geoStrictTransform π ((Subtype.val : W → X) '' D)) ++
        [π ⁻¹' ((Subtype.val : W → X) '' D)]).map ((Subtype.val : S → Y) ⁻¹' ·) =
      (E.map ((Subtype.val : W → X) ⁻¹' ·)).map (geoStrictTransform σ D) ++ [σ ⁻¹' D] := by
  let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
  let σ := HironakaActualClosedContactBlowupRestriction.restrictedProjection hWc D hπ
  have hborn : (Subtype.val : S → Y) ⁻¹' (π ⁻¹' ((Subtype.val : W → X) '' D)) =
      σ ⁻¹' D := by
    ext y
    constructor
    · rintro ⟨x,hxD,he⟩
      have hx : x = σ y := Subtype.ext he
      change σ y ∈ D
      exact hx ▸ hxD
    · intro hy
      exact ⟨σ y,hy,rfl⟩
  simp only [List.map_append,List.map_singleton,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact native_old_member_preimage hn hWc D hπ hE hT hnc i
  · exact congrArg List.singleton hborn

open SubmanifoldChartedSpace HironakaActualClosedContactBlowupRestriction
  HironakaActualNativeSectionControlledTransform HironakaSmoothSubmersionCoefficientIdeals

theorem markedPullback_actual_restricted_geoTransform
    {n k : ℕ} (hn : 0 < n) {X Y : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {W : Set X} (hk : k ≤ n) (hWc : IsClosed W)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (D A : Set W) (J : GermIdeal n X)
    (hJ : ∀ x g, J.mem x g → HolomorphicAt n g x) (d : ℕ)
    {π : Y → X} (hπ : IsBlowupAlong n ((Subtype.val : W → X) '' D) π)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n W E)
    (hnc : HasNormalCrossings n ((Subtype.val : W → X) '' D) E) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    letI := strictChartedSpace hk hWc hW hπ
    letI := strict_isComplexManifold hk hWc hW hπ
    let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
    let σ := restrictedProjection hWc D hπ
    let M : MarkedIdeals.MarkedIdeal n X := ⟨(Subtype.val : W → X) '' A,E,J,d⟩
    let B : MarkedIdeals.MarkedIdeal k W :=
      ⟨A,E.map ((Subtype.val : W → X) ⁻¹' ·),
        GermIdeal.pullback (m := k) (Subtype.val : W → X) J,d⟩
    markedPullback (m := k) (Subtype.val : S → Y)
      (M.geoTransform ((Subtype.val : W → X) '' D) π) = B.geoTransform D σ := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := strictChartedSpace hk hWc hW hπ
  have := strict_isComplexManifold hk hWc hW hπ
  let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
  let σ := restrictedProjection hWc D hπ
  have hN : (Subtype.val : S → Y) ⁻¹'
      geoStrictTransform π ((Subtype.val : W → X) '' D) ((Subtype.val : W → X) '' A) =
        geoStrictTransform σ D A := by
    rw [← strictTransform_image hWc hπ A]
    exact Set.preimage_image_eq _ Subtype.val_injective
  have hIdeal := pullback_actual_restricted_geoTransform_ideal hk hWc hW D A J hJ d hπ
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hN
  · exact whole_ordered_boundary_preimage hn hWc D hπ hE hT hnc
  · exact hIdeal
  · rfl

end
end Hironaka.HironakaActualNativeSectionBoundaryTrace
