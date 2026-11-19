import Hironaka.Resolution.HironakaG8RankSortedSpatialChart
import Hironaka.Resolution.HironakaG8SingularTestCompression
import Hironaka.Resolution.HironakaG8RankedTestCompression
import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence
import Mathlib.Data.List.FinRange
import Hironaka.Resolution.HironakaG8SpatialGeometricWord

/-! Spatial ranking on an original finite TEST with its real empty slots. -/
set_option autoImplicit false
open Set Function
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8RankSortedRawChart

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8RankedTestCompression HironakaG8SingularTestCompression
  HironakaG8RankSortedSpatialChart HironakaG8SpatialCofinalPrecedence HironakaG3RTowerClass
  HironakaG8SpatialGeometricWord HironakaG8GeometricIndexedWord HironakaG8NestedVisibleWordLift
  HironakaG3EmptyAwareHistory HironakaG8FirstFootprintOrder

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Retain the exact TEST compression and every actual geometric
move from that same compressed history to the ranked output. -/
theorem exists_key_sorted_raw_singular_test_geometry {κ : Type*} [LinearOrder κ]
    (fallback : κ) (T : BlowupTower X Y) (rank : {k // Occupied T k} → κ) (hInjective : Injective rank)
    (hRank : ∀ a b, a.val < b.val →
      (slotFootprint T a.val ∩ slotFootprint T b.val).Nonempty → rank a < rank b)
    (W : Set X) (hW : IsClosed W) (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ target : List {k // Occupied T k}, target.Nodup ∧ (∀ a, a ∈ target) ∧
      target.Pairwise (fun a b => rank a < rank b) ∧
      ∃ (B : CMfd.{0} n) (Q : BlowupTower X B)
        (χ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
        (cmp : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ),
        IsGeoTestTower M Q ∧
        ∃ hQocc : StageCentres (fun _ C => C.Nonempty) Q,
          IntrinsicStage W ⟨B,Q⟩ ∧
          (∀ z, T.proj (χ z) = Q.proj z) ∧
          (∀ i : Fin Q.length,
            slotFootprint Q i.val = slotFootprint T (compressedRawOccupiedIso hQocc cmp i).val) ∧
          ∃ (word : List ℕ) (Z : CMfd.{0} n) (R : BlowupTower X Z)
            (e : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z),
            RealizedWord (GeometricIndexedMove W M) word ⟨B,Q⟩ ⟨Z,R⟩ ∧
            IsGeoTestTower M R ∧ R.proj ∘ e = Q.proj ∧ IntrinsicStage W ⟨Z,R⟩ ∧
            footprints (⟨Z,R⟩ : TowerAt X) = target.map (fun a => slotFootprint T a.val) ∧
            (∀ j a, target[j]? = some a → slotFootprint R j = slotFootprint T a.val) ∧
            ∀ j, (slotFootprint R j).Nonempty ↔ j < target.length := by
  obtain ⟨B,Q,χ,cmp,hQtest,hQocc,hQstage,_,hQproj,_,_⟩ :=
    exists_empty_free_singular_test_compression M hM W hW T hTest hStage
  let original := compressedRawOccupiedIso hQocc cmp
  have hFoot (i : Fin Q.length) : slotFootprint Q i.val = slotFootprint T (original i).val :=
    slotFootprint_compressedRawOccupiedIso hQocc cmp i
  let rankAt (i : ℕ) := if hi : i < Q.length then rank (original ⟨i,hi⟩) else fallback
  have hRankAt (i : Fin Q.length) : rankAt i.val = rank (original i) := dif_pos i.isLt
  have hRankAtInj : InjOn rankAt {i | i < Q.length} := by
    intro a ha b hb hab
    exact congrArg Fin.val (original.injective (hInjective
      (((hRankAt ⟨a,ha⟩).symm.trans hab).trans (hRankAt ⟨b,hb⟩))))
  have hOccAt (i : ℕ) (hi : i < Q.length) : (slotFootprint Q i).Nonempty :=
    (slotFootprint_nonempty_iff Q i).mpr (occupied_of_empty_free Q hQocc ⟨i,hi⟩)
  have hOrder i j (hij : i < j) (hj : j < Q.length)
      (hMeet : (slotFootprint Q i ∩ slotFootprint Q j).Nonempty) : rankAt i < rankAt j := by
    let a : Fin Q.length := ⟨i,hij.trans hj⟩
    let b : Fin Q.length := ⟨j,hj⟩
    rw [hRankAt a,hRankAt b]
    exact hRank _ _ (original.strictMono hij) (by rwa [← hFoot a,← hFoot b])
  obtain ⟨order,hPerm,hSorted,hIdx⟩ := exists_key_sorted_spatial_target Q.length rankAt hRankAtInj
  obtain ⟨word,⟨Z,R⟩,_,hWord,hRtest,hRstage,hROcc,hRfoot,hRawOrder,e,hRproj⟩ :=
    realize_spatial_target_geometrically ⟨B,Q⟩ order hPerm hOccAt
      (fun i j hij hj hMeet => hIdx i j hij hj (hOrder i j hij hj hMeet))
      W M hM hN hQtest hQstage
  have hBound (j : Fin order.length) : order.get j < Q.length :=
    List.mem_range.mp (hPerm.mem_iff.mpr (List.get_mem order j))
  let label (j : Fin order.length) := original ⟨order.get j,hBound j⟩
  let target := List.ofFn label
  have hLen : target.length = order.length := List.length_ofFn
  have hLabels (j : Fin order.length) : rank (label j) = rankAt (order.get j) :=
    (hRankAt ⟨order.get j,hBound j⟩).symm
  have hNodup : target.Nodup := by
    apply List.nodup_ofFn_ofInjective
    have hOrderNodup : order.Nodup := hPerm.nodup_iff.mp List.nodup_range
    intro i j hij
    exact hOrderNodup.injective_get (congrArg Fin.val (original.injective hij))
  have hContains (a : {k // Occupied T k}) : a ∈ target := by
    obtain ⟨q,hq⟩ := original.surjective a
    have hMem : q.val ∈ order := hPerm.mem_iff.mp (List.mem_range.mpr q.isLt)
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hMem
    exact List.mem_ofFn.mpr ⟨j, (congrArg original (Fin.ext hj)).trans hq⟩
  have hTargetSorted : target.Pairwise (fun a b => rank a < rank b) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    rw [List.getElem_ofFn, List.getElem_ofFn, hLabels, hLabels]
    exact List.pairwise_iff_getElem.mp hSorted i j (hLen ▸ hi) (hLen ▸ hj) hij
  have hOrdered : footprints (⟨Z,R⟩ : TowerAt X) =
      target.map (fun a => slotFootprint T a.val) := by
    rw [hRawOrder]
    apply List.ext_getElem
    · simpa only [List.length_map] using hLen.symm
    · intro j hj hk
      have hjOrder : j < order.length := by simpa using hj
      simp only [List.getElem_map]
      change slotFootprint Q order[j] = slotFootprint T ((List.ofFn label)[j]).val
      rw [List.getElem_ofFn]
      exact hFoot ⟨order.get ⟨j,hjOrder⟩,hBound ⟨j,hjOrder⟩⟩
  have hRlength : R.length = target.length := by
    have hh := congrArg List.length hOrdered
    simpa only [footprints,List.length_map,List.length_range] using hh
  refine ⟨target,hNodup,hContains,hTargetSorted,B,Q,χ,cmp,hQtest,hQocc,hQstage,hQproj,hFoot,
    word,Z,R,e,hWord,hRtest,hRproj,hRstage,hOrdered,?_,?_⟩
  · intro j a ha
    obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp ha
    let k : Fin order.length := ⟨j,hLen ▸ hj⟩
    have hLa : label k = a := by simpa [target,k] using he
    calc
      slotFootprint R j = slotFootprint Q (order.get k) :=
        hRfoot j _ (List.getElem?_eq_getElem k.isLt)
      _ = slotFootprint T (label k).val := hFoot ⟨order.get k,hBound k⟩
      _ = slotFootprint T a.val := by rw [hLa]
  · intro j
    rw [← hRlength]
    exact ⟨fun ⟨_,hx⟩ => hit_slot_lt_length R hx,hROcc j⟩


/-- Retained geometric sorting with natural keys. -/
theorem exists_rank_sorted_raw_singular_test_geometry
    (T : BlowupTower X Y) (rank : {k // Occupied T k} → ℕ) (hInjective : Injective rank)
    (hRank : ∀ a b, a.val < b.val →
      (slotFootprint T a.val ∩ slotFootprint T b.val).Nonempty → rank a < rank b)
    (W : Set X) (hW : IsClosed W) (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ target : List {k // Occupied T k}, target.Nodup ∧ (∀ a, a ∈ target) ∧
      target.Pairwise (fun a b => rank a < rank b) ∧
      ∃ (B : CMfd.{0} n) (Q : BlowupTower X B)
        (χ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
        (cmp : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ),
        IsGeoTestTower M Q ∧
        ∃ hQocc : StageCentres (fun _ C => C.Nonempty) Q,
          IntrinsicStage W ⟨B,Q⟩ ∧
          (∀ z, T.proj (χ z) = Q.proj z) ∧
          (∀ i : Fin Q.length,
            slotFootprint Q i.val = slotFootprint T (compressedRawOccupiedIso hQocc cmp i).val) ∧
          ∃ (word : List ℕ) (Z : CMfd.{0} n) (R : BlowupTower X Z)
            (e : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z),
            RealizedWord (GeometricIndexedMove W M) word ⟨B,Q⟩ ⟨Z,R⟩ ∧
            IsGeoTestTower M R ∧ R.proj ∘ e = Q.proj ∧ IntrinsicStage W ⟨Z,R⟩ ∧
            footprints (⟨Z,R⟩ : TowerAt X) = target.map (fun a => slotFootprint T a.val) ∧
            (∀ j a, target[j]? = some a → slotFootprint R j = slotFootprint T a.val) ∧
            ∀ j, (slotFootprint R j).Nonempty ↔ j < target.length :=
  exists_key_sorted_raw_singular_test_geometry 0 T rank hInjective hRank W hW M hM hN hTest hStage

/-- The original raw rank-sorting result, projected from its geometric witness. -/
theorem exists_rank_sorted_raw_singular_test_chart
    (T : BlowupTower X Y) (rank : {k // Occupied T k} → ℕ) (hInjective : Injective rank)
    (hRank : ∀ a b, a.val < b.val →
      (slotFootprint T a.val ∩ slotFootprint T b.val).Nonempty → rank a < rank b)
    (W : Set X) (hW : IsClosed W) (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ target : List {k // Occupied T k}, target.Nodup ∧ (∀ a, a ∈ target) ∧
      target.Pairwise (fun a b => rank a < rank b) ∧
      ∃ (Z : CMfd.{0} n) (R : BlowupTower X Z)
        (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z),
        IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
        (∀ j a, target[j]? = some a → slotFootprint R j = slotFootprint T a.val) ∧
        ∀ j, (slotFootprint R j).Nonempty ↔ j < target.length := by
  obtain ⟨target,hNo,hContains,hSorted,_,Q,χ,_,_,_,_,hQproj,_,_,Z,R,e,_,hRtest,hRproj,hRstage,
    _,hRfoot,hROcc⟩ :=
    exists_rank_sorted_raw_singular_test_geometry T rank hInjective hRank W hW M hM hN hTest hStage
  refine ⟨target,hNo,hContains,hSorted,Z,R,χ.symm.trans e,hRtest,?_,hRstage,hRfoot,hROcc⟩
  funext y
  change R.proj (e (χ.symm y)) = T.proj y
  rw [show R.proj (e (χ.symm y)) = Q.proj (χ.symm y) from congrFun hRproj _,
    ← hQproj (χ.symm y),χ.apply_symm_apply]

/-- One distinct spatial rank orders the original occupied slots of
every represented singular TEST chart under finite incoming ancestry. -/
theorem exists_rank_sorted_cofinal_singular_charts
    {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)
    (hOccurs : ∀ a, ∃ i p, E.event i p = a)
    (hWF : WellFounded (SpatialBefore E)) (hFinite : ∀ b, {a | SpatialBefore E a b}.Finite)
    (W : ∀ i, Set (c i).U) (hW : ∀ i, IsClosed (W i))
    (M : ∀ i, MarkedIdeal n (CMfd.of (n := n) (c i).U))
    (hM : ∀ i, (M i).IsWellFormed) (hN : ∀ i, (M i).N = univ)
    (hTest : ∀ i, IsGeoTestTower (M i) (c i).T)
    (hStage : ∀ i, StageCentres (fun Q C =>
      C ⊆ singularSet (n := n) (strictTransform n Q.proj (W i))) (c i).T) :
    ∃ rank : ι → ℕ, Injective rank ∧
      (∀ ⦃a b⦄, Relation.TransGen (SpatialBefore E) a b → rank a < rank b) ∧
      ∀ i, ∃ target : List {k // Occupied (c i).T k},
        target.Nodup ∧ (∀ a, a ∈ target) ∧ target.Pairwise (fun a b => rank (E.event i a) < rank (E.event i b)) ∧
        ∃ (B : CMfd.{0} n) (R : BlowupTower (CMfd.of (n := n) (c i).U) B)
          (e : (c i).Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B),
          IsGeoTestTower (M i) R ∧ R.proj ∘ e = (c i).T.proj ∧
          StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj (W i))) R ∧
          (∀ j a, target[j]? = some a → slotFootprint R j = slotFootprint (c i).T a.val) ∧
          ∀ j, (slotFootprint R j).Nonempty ↔ j < target.length := by
  obtain ⟨rank,hInj,hRank,hOrder⟩ := exists_injective_rank_of_spatial_incoming E hOccurs hWF hFinite
  refine ⟨rank,hInj,hRank,?_⟩
  intro i
  apply exists_rank_sorted_raw_singular_test_chart (c i).T (rank ∘ E.event i)
    (hInj.comp (E.injective i)) _ (W i) (hW i) (M i) (hM i) (hN i) (hTest i) (hStage i)
  rintro a b hab ⟨x,hxa,hxb⟩
  exact hOrder i a b hab ⟨x.val,mem_image_of_mem _ hxa,mem_image_of_mem _ hxb⟩

end Hironaka.HironakaG8RankSortedRawChart
