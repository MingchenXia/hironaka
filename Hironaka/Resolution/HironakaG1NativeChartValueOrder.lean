import Hironaka.Resolution.HironakaG1NativeChartCanonicalComparison
import Hironaka.Resolution.HironakaG1NativeGraphOverlapRead

/-! Exact native chart values and order transport between ambient dimensions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NativeChartValueOrder

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  NormalCrossings DivisorExponentAlong CanonicalCentres
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeInvariantDomain
  HironakaG1NativeChartCanonicalComparison
  HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG1OriginalUnequalMarkCanonical

/-- An exact strict comparison on a common point set identifies the two
attained value orders, even when the original value types differ. -/
noncomputable def attainedValueOrderIso {A V W : Type*} [LinearOrder V] [LinearOrder W]
    (f : A → V) (g : A → W) (hLt : ∀ a b, f a < f b ↔ g a < g b) :
    range f ≃o range g := by
  classical
  have hEq (a b : A) : f a = f b ↔ g a = g b := by
    rw [eq_iff_le_not_lt, eq_iff_le_not_lt, ← not_lt, ← not_lt, hLt a b, hLt b a]
  let a (v : range f) : A := Classical.choose v.property
  have ha (v : range f) : f (a v) = v.val := Classical.choose_spec v.property
  let b (w : range g) : A := Classical.choose w.property
  have hb (w : range g) : g (b w) = w.val := Classical.choose_spec w.property
  let e : range f ≃ range g :=
    ⟨fun v => ⟨g (a v), mem_range_self _⟩, fun w => ⟨f (b w), mem_range_self _⟩,
      fun v => Subtype.ext ((hEq _ _).mpr (hb ⟨g (a v), mem_range_self _⟩) |>.trans (ha v)),
      fun w => Subtype.ext ((hEq _ _).mp (ha ⟨f (b w), mem_range_self _⟩) |>.trans (hb w))⟩
  refine ⟨e, ?_⟩
  intro v w
  change g (a v) ≤ g (a w) ↔ v.val ≤ w.val
  rw [← ha v, ← ha w, ← not_lt, ← not_lt, hLt]

/-- The order isomorphism uses the actual value at the same point. -/
theorem attainedValueOrderIso_apply {A V W : Type*} [LinearOrder V] [LinearOrder W]
    (f : A → V) (g : A → W) (hLt : ∀ a b, f a < f b ↔ g a < g b) (a : A) :
    (attainedValueOrderIso f g hLt ⟨f a, mem_range_self a⟩ : W) = g a := by
  classical
  let p : A := Classical.choose (show f a ∈ range f from mem_range_self a)
  have hp : f p = f a := Classical.choose_spec (show f a ∈ range f from mem_range_self a)
  change g p = g a
  apply le_antisymm
  · exact le_of_not_gt (fun h => (ne_of_lt ((hLt a p).mpr h)) hp.symm)
  · exact le_of_not_gt (fun h => (ne_of_lt ((hLt p a).mpr h)) hp)

/-- The exact dimension maps induce the canonical order isomorphism of
their images, with the same native recursive value on both sides. -/
noncomputable def nativeDimensionImageOrderIso (a b q : ℕ) :
    range (familyDimensionMap a q) ≃o range (familyDimensionMap b q) :=
  attainedValueOrderIso _ _ fun x y =>
    (familyDimensionMap_comparisons a q x y).1.trans
      (familyDimensionMap_comparisons b q x y).1.symm

theorem nativeDimensionImageOrderIso_apply (a b q : ℕ) (v : ValTy q) :
    (nativeDimensionImageOrderIso a b q ⟨familyDimensionMap a q v, mem_range_self v⟩ :
      ValTy (b + q)) = familyDimensionMap b q v :=
  attainedValueOrderIso_apply _ _ _ _

open MonomialInvariantEmptyMember HironakaOriginalInvariantEmptyInsertion
  HironakaOriginalBoundaryEmptyFilterComparison

private theorem append_insert_empty {X : Type*} (A B : List (Set X)) :
    (A ++ B).insertIdx A.length ∅ = A ++ ∅ :: B := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    simpa only [List.cons_append, List.length_cons, List.insertIdx_succ_cons] using
      (congrArg (List.cons x) ih)

/-- The original empty positions contribute an exact composite of the
literal insertion maps. It is an order embedding and is independent of
the chosen canonical history and the endpoint. -/
theorem exists_original_empty_boundary_value_embedding {n k : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (P : MarkedIdeal n X) :
    ∃ e : ValTy k ↪o ValTy k, ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y) (z : Y),
      (invFamily hn k).inv P T z = e ((invFamily hn k).inv (nonemptyBoundary P) T z) := by
  classical
  let M (E : List (Set X)) : MarkedIdeal n X := {P with E := E}
  have aux : ∀ (B A : List (Set X)), ∃ e : ValTy k ↪o ValTy k,
      ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y) (z : Y),
      (invFamily hn k).inv (M (A ++ B)) T z =
        e ((invFamily hn k).inv (M (A ++ B.filter (fun H => decide H.Nonempty))) T z) := by
    intro B
    induction B with
    | nil => intro A; exact ⟨OrderEmbedding.ofStrictMono id strictMono_id, fun _ _ => rfl⟩
    | cons H B ih =>
      intro A
      by_cases hH : H.Nonempty
      · simpa only [List.filter_cons, decide_eq_true hH, reduceIte, List.append_assoc,
          List.singleton_append] using ih (A ++ [H])
      · obtain rfl := Set.not_nonempty_iff_eq_empty.mp hH
        obtain ⟨e, he⟩ := ih A
        refine ⟨e.trans (shiftFamilyEmbedding k A.length), fun T z => ?_⟩
        have hM : insertEmpty A.length (M (A ++ B)) = M (A ++ ∅ :: B) := by
          change M ((A ++ B).insertIdx A.length ∅) = _
          rw [append_insert_empty]
        have hVal := invFamily_insertEmpty hn k (M (A ++ B)) A.length (by simp [M]) T z
        rw [hM, he T z] at hVal
        simp only [List.filter_cons, Set.not_nonempty_empty, decide_false, Bool.false_eq_true,
          reduceIte]
        exact hVal
  obtain ⟨e, he⟩ := aux P.E []
  exact ⟨e, fun T z => he T z⟩

set_option maxHeartbeats 1600000 in
/-- Independent native charts of two genuine lifts can be compared on their
common native presentation. Each ambient read has its own exact dimension
shift. Weak normalized exponent comparison identifies the attained orders
and does not require the two native values to be equal. -/
theorem cross_ambient_native_chart_value_read
    {m₁ m₂ d q : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hd : 0 < d)
    {X₁ Y₁ : CMfd.{0} m₁} {X₂ Y₂ : CMfd.{0} m₂} {A Z : CMfd.{0} d}
    {hk₁ : d ≤ m₁} {hk₂ : d ≤ m₂}
    {W₁ : Set X₁} {V₁ : Set Y₁} {W₂ : Set X₂} {V₂ : Set Y₂}
    {hWc₁ : IsClosed W₁} {hVc₁ : IsClosed V₁} {hWc₂ : IsClosed W₂} {hVc₂ : IsClosed V₂}
    {hW₁ : ∀ x ∈ W₁, RegularAtDim (n := m₁) W₁ x d}
    {hV₁ : ∀ x ∈ V₁, RegularAtDim (n := m₁) V₁ x d}
    {hW₂ : ∀ x ∈ W₂, RegularAtDim (n := m₂) W₂ x d}
    {hV₂ : ∀ x ∈ V₂, RegularAtDim (n := m₂) V₂ x d}
    (M₁ : MarkedIdeal m₁ X₁) (M₂ : MarkedIdeal m₂ X₂)
    (hM₁ : IsInvDomain q M₁) (hM₂ : IsInvDomain q M₂)
    (hMN₁ : M₁.N ⊆ W₁) (hMN₂ : M₂.N ⊆ W₂)
    (hTrans₁ : IsTransverse m₁ W₁ M₁.E) (hTrans₂ : IsTransverse m₂ W₂ M₂.E)
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {N₁ : BlowupTower (nativeManifold hk₁ W₁ hW₁) (nativeManifold hk₁ V₁ hV₁)}
    {N₂ : BlowupTower (nativeManifold hk₂ W₂ hW₂) (nativeManifold hk₂ V₂ hV₂)}
    (hLift₁ : Lift hk₁ W₁ hWc₁ hW₁ M₁.E T₁ V₁ hVc₁ hV₁ N₁)
    (hLift₂ : Lift hk₂ W₂ hWc₂ hW₂ M₂.E T₂ V₂ hVc₂ hV₂ N₂)
    (e₁ : A ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ nativeManifold hk₁ W₁ hW₁)
    (e₂ : A ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ nativeManifold hk₂ W₂ hW₂)
    (S : BlowupTower A Z)
    (χ₁ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ nativeManifold hk₁ V₁ hV₁)
    (χ₂ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ nativeManifold hk₂ V₂ hV₂)
    (hIso₁ : IsTowerIso e₁ S N₁ χ₁) (hIso₂ : IsTowerIso e₂ S N₂ χ₂) :
    let C₁ := MarkedIdeal.pullback e₁ (nativePullback hk₁ W₁ hW₁ M₁)
    let C₂ := MarkedIdeal.pullback e₂ (nativePullback hk₂ W₂ hW₂ M₂)
    let f₁ := (invFamily hm₁ ((m₁ - d) + q)).inv M₁ T₁
    let f₂ := (invFamily hm₂ ((m₂ - d) + q)).inv M₂ T₂
    let g₁ := (invFamily hd q).inv C₁ S
    let g₂ := (invFamily hd q).inv C₂ S
    let E := (geoTransformAlong C₁ S).cosupp
    LocWPEquiv C₁ C₂ → SameCarrierDim C₁ C₂ →
    (∀ F ∈ C₁.E, ∀ x ∈ C₁.cosupp, x ∈ F →
      C₂.d * divExpAlong d C₁.N C₁.ideal F x = C₁.d * divExpAlong d C₂.N C₂.ideal F x) →
    (IsCanonical M₁ ((invFamily hm₁ ((m₁ - d) + q)).inv M₁) T₁ ↔
      IsCanonical M₂ ((invFamily hm₂ ((m₂ - d) + q)).inv M₂) T₂) ∧
    (IsCanonical M₁ ((invFamily hm₁ ((m₁ - d) + q)).inv M₁) T₁ →
      (∀ z ∈ E, f₁ (χ₁ z).val = familyDimensionMap (m₁ - d) q (g₁ z) ∧
        f₂ (χ₂ z).val = familyDimensionMap (m₂ - d) q (g₂ z)) ∧
      (∀ z ∈ E, ∀ w ∈ E, f₁ (χ₁ z).val < f₁ (χ₁ w).val ↔
        f₂ (χ₂ z).val < f₂ (χ₂ w).val) ∧
      ∃ e : range (fun z : E => f₁ (χ₁ z.val).val) ≃o range (fun z : E => f₂ (χ₂ z.val).val),
        ∀ z : E, (e ⟨f₁ (χ₁ z.val).val, mem_range_self z⟩ : ValTy ((m₂ - d) + q)) =
          f₂ (χ₂ z.val).val) := by
  intro C₁ C₂ f₁ f₂ g₁ g₂ E hClass hDim hExp
  obtain ⟨hC₁, hCan₁, hRead₁⟩ := original_native_chart_comparison hm₁ hd M₁ hM₁ hMN₁ hTrans₁
    hLift₁ e₁ S χ₁ hIso₁
  obtain ⟨hC₂, hCan₂, hRead₂⟩ := original_native_chart_comparison hm₂ hd M₂ hM₂ hMN₂ hTrans₂
    hLift₂ e₂ S χ₂ hIso₂
  have hCan := invFamily_isCanonical_iff_of_local hd C₁ C₂ hC₁ hC₂ hClass hDim hExp S
  refine ⟨hCan₁.symm.trans (hCan.trans hCan₂), fun hAmb₁ => ?_⟩
  have hSC₁ := hCan₁.mpr hAmb₁
  have hSC₂ := hCan.mp hSC₁
  have hAmb₂ := hCan₂.mp hSC₂
  have hST := (invFamily hd q).isInvValue.isGeoTestTower_of_isCanonical hC₁ S hSC₁
  have hCos := (hClass.wEquiv.2 S).2 hST
  obtain ⟨hPre₁, _, hVal₁, _, _⟩ := hRead₁ hAmb₁
  obtain ⟨hPre₂, _, hVal₂, _, _⟩ := hRead₂ hAmb₂
  have hBoth (z : Z) (hz : z ∈ E) :
      f₁ (χ₁ z).val = familyDimensionMap (m₁ - d) q (g₁ z) ∧
      f₂ (χ₂ z).val = familyDimensionMap (m₂ - d) q (g₂ z) :=
    by
      have hz₁ : z ∈ (fun z : Z => (χ₁ z).val) ⁻¹' (geoTransformAlong M₁ T₁).cosupp := hPre₁ ▸ hz
      have hz₂ : z ∈ (fun z : Z => (χ₂ z).val) ⁻¹' (geoTransformAlong M₂ T₂).cosupp :=
        hPre₂ ▸ (hCos ▸ hz)
      exact ⟨hVal₁ z hz₁, hVal₂ z hz₂⟩
  have hOrder (z : Z) (hz : z ∈ E) (w : Z) (hw : w ∈ E) :
      f₁ (χ₁ z).val < f₁ (χ₁ w).val ↔ f₂ (χ₂ z).val < f₂ (χ₂ w).val := by
    have hLt := canonicalTwoPairCuts_invFamily hd q C₁ C₂ C₁ C₂ hC₁ hC₂ hC₁ hC₂
      hClass hDim hExp hClass hDim hExp rfl rfl trivial trivial trivial trivial S S hSC₁ hSC₂ hSC₁ hSC₂ z hz w hw
    rw [(hBoth z hz).1, (hBoth w hw).1, (hBoth z hz).2, (hBoth w hw).2]
    exact (familyDimensionMap_comparisons (m₁ - d) q _ _).1.trans
      (hLt.trans (familyDimensionMap_comparisons (m₂ - d) q _ _).1.symm)
  let a₁ (z : E) := f₁ (χ₁ z.val).val
  let a₂ (z : E) := f₂ (χ₂ z.val).val
  have hEmb (z w : E) : a₁ z < a₁ w ↔ a₂ z < a₂ w :=
    hOrder z.val z.property w.val w.property
  exact ⟨hBoth, hOrder, attainedValueOrderIso a₁ a₂ hEmb, attainedValueOrderIso_apply a₁ a₂ hEmb⟩

open HironakaG1NativeGraphOverlapRead HironakaG1NativeBoundaryTrace
  HironakaG11PresLineState HironakaG11PresLineStable
open scoped Topology
open Filter

set_option maxHeartbeats 1300000 in
/-- Surviving-slot agreement and the native trace condition compare the
attained orders of the original graph records on a successful common
refinement, including differences in the empty chronological positions. -/
theorem native_graph_overlap_attained_order {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {P Q : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hQ : NativeHSState Q D h)
    (hPD : IsInvDomain n P) (hQD : IsInvDomain n Q) (U : Opens X)
    (hGood : ∀ F ∈ P.E, ∀ x ∈ P.cosupp, x ∈ U → x ∈ F →
      (∀ᶠ y in 𝓝 x, y ∈ F → y ∈ D) →
      ∀ᶠ y in 𝓝 x, y ∈ F → y ∈ P.cosupp) :
    let A := CMfd.of (n := n) U
    let L := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) P
    let R := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) Q
    (nonemptyBoundary R).E = (nonemptyBoundary L).E →
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      IsCanonical L ((invFamily hn n).inv L) T →
      let E := (geoTransformAlong L T).cosupp
      let f := fun z : E => (invFamily hn n).inv L T z.val
      let g := fun z : E => (invFamily hn n).inv R T z.val
      ∃ e : range f ≃o range g, ∀ z : E, (e ⟨f z, mem_range_self z⟩ : ValTy n) = g z := by
  intro A L R hE Y T hCan E f g
  let F := nonemptyBoundary L
  let G := nonemptyBoundary R
  have hFS : NativeHSState (X := A) F ((Subtype.val : U → X) ⁻¹' D) h := hP.restrict U
  have hGS : NativeHSState (X := A) G ((Subtype.val : U → X) ⁻¹' D) h := hQ.restrict U
  have hFD := isInvDomain_nonemptyBoundary L (InvDomainTowerAlong.isInvDomain_pullback_val U hPD)
  have hGD := isInvDomain_nonemptyBoundary R (InvDomainTowerAlong.isInvDomain_pullback_val U hQD)
  have hClass := locWPEquiv_native hFS hGS hE
  have hDim := SameCarrierDim.of_N_eq (hFS.2.2.1.trans hGS.2.2.1.symm)
  have hExp := normalized_native_boundary_exponents_of_trace hn hFS hGS hFD hGD hE
    (native_graph_trace_on_refinement P hPD.isWellFormed.isCoherent D U hGood)
  have hFam : canonicalInvariant n = invFamily hn n := by cases n with
    | zero => omega
    | succ n => rfl
  have hFilt := isCanonical_nonemptyBoundary_iff L T
  rw [hFam] at hFilt
  have hFC := hFilt.mpr hCan
  have hGC := (invFamily_isCanonical_iff_of_local hn F G hFD hGD hClass hDim hExp T).mp hFC
  obtain ⟨eL, hL⟩ := exists_original_empty_boundary_value_embedding (k := n) hn L
  obtain ⟨eR, hR⟩ := exists_original_empty_boundary_value_embedding (k := n) hn R
  have hLt (z w : E) : f z < f w ↔ g z < g w := by
    have hz : z.val ∈ (geoTransformAlong F T).cosupp :=
      (cosupp_nonemptyBoundary_along L T).symm ▸ z.property
    have hw : w.val ∈ (geoTransformAlong F T).cosupp :=
      (cosupp_nonemptyBoundary_along L T).symm ▸ w.property
    have h := canonicalTwoPairCuts_invFamily hn n F G F G hFD hGD hFD hGD hClass hDim hExp
      hClass hDim hExp rfl rfl trivial trivial trivial trivial T T hFC hGC hFC hGC z.val hz w.val hw
    change (invFamily hn n).inv L T z.val < (invFamily hn n).inv L T w.val ↔
      (invFamily hn n).inv R T z.val < (invFamily hn n).inv R T w.val
    rw [hL T z.val, hL T w.val, hR T z.val, hR T w.val]
    exact eL.strictMono.lt_iff_lt.trans (h.trans eR.strictMono.lt_iff_lt.symm)
  exact ⟨attainedValueOrderIso f g hLt, attainedValueOrderIso_apply f g hLt⟩

end Hironaka.HironakaG1NativeChartValueOrder
