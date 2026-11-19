import Hironaka.Resolution.HironakaOriginalFamilyDepthStability

/-!
# Same-bound maximum loci and canonical centres on actual native lifts

The whole current cosupport lies in the transformed section, and the same-bound
value map is strictly monotone there. This transports the maximum locus on
each canonical prefix, including stages with empty cosupport. The geometric
lift gives a literal image description of each ambient centre, so the
maximum-locus comparison also detects ambient canonicality from the native tower.
In native dimension zero, discreteness forces all centres to be empty.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NormalCentreTransport

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver ResolutionInvariantExt CanonicalCentres
  NormalCrossings RelativePrincipalizationSpan
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualSectionBoundaryDimension HironakaOriginalFamilyDepthStability

variable {n k q : ℕ} {X : CMfd.{0} n} {hk : k ≤ n}
  {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

set_option backward.isDefEq.respectTransparency false in
/-- A strictly monotone value comparison on the whole supported cosupport
identifies the maximum loci in both directions along the actual inclusion. -/
theorem Lift.max_loci_of_value_comparison {Λ Γ : Type*} [LinearOrder Λ] [LinearOrder Γ]
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (f : Y → Λ) (g : nativeManifold hk V hV → Γ) (δ : Γ → Λ) (hδ : StrictMono δ)
    (hValue : ∀ z : nativeManifold hk V hV, z.val ∈ (geoTransformAlong M T).cosupp →
      f z.val = δ (g z)) :
    let i : nativeManifold hk V hV → Y := Subtype.val
    let C := maxLocus f (geoTransformAlong M T).cosupp
    let D := maxLocus g (geoTransformAlong (nativePullback hk W hW M) Q).cosupp
    D = i ⁻¹' C ∧ i '' D = C := by
  intro i C D
  let B := nativePullback hk W hW M
  have hHol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent hg
  have hCos : (geoTransformAlong B Q).cosupp = i ⁻¹' (geoTransformAlong M T).cosupp :=
    HironakaActualNativeSectionOrderHistory.Lift.current_cosupport
      h hn hM.isSNCDivisor hTrans M rfl hMN hHol
  have hRange : (geoTransformAlong M T).cosupp ⊆ V :=
    (geoTransformAlong M T).cosupp_subset_N.trans
      (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h M hMN)
  have hOrder (a b : nativeManifold hk V hV)
      (ha : i a ∈ (geoTransformAlong M T).cosupp) (hb : i b ∈ (geoTransformAlong M T).cosupp) :
      f (i a) ≤ f (i b) ↔ g a ≤ g b := by
    rw [hValue a ha, hValue b hb]
    exact hδ.le_iff_le
  have hPre : D = i ⁻¹' C := by
    ext z
    change (z ∈ (geoTransformAlong B Q).cosupp ∧
      ∀ x ∈ (geoTransformAlong B Q).cosupp, g x ≤ g z) ↔
      (i z ∈ (geoTransformAlong M T).cosupp ∧
        ∀ y ∈ (geoTransformAlong M T).cosupp, f y ≤ f (i z))
    rw [hCos]
    constructor
    · rintro ⟨hz, hmax⟩
      refine ⟨hz, fun y hy => ?_⟩
      let x : nativeManifold hk V hV := ⟨y, hRange hy⟩
      exact (hOrder x z hy hz).mpr (hmax x hy)
    · rintro ⟨hz, hmax⟩
      exact ⟨hz, fun x hx => (hOrder x z hx hz).mp (hmax (i x) hx)⟩
  refine ⟨hPre, ?_⟩
  have hCRange : C ⊆ range i := fun y hy => ⟨⟨y, hRange hy.1⟩, rfl⟩
  rw [hPre, image_preimage_eq_inter_range]
  exact inter_eq_left.mpr hCRange

set_option backward.isDefEq.respectTransparency false in
/-- Exact preimage and image descriptions of the original same-bound maximum loci. -/
theorem Lift.original_same_bound_max_loci
    (hn : 0 < n) (hkpos : 0 < k) (M : MarkedIdeal n X) (hM : IsInvDomain q M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M ((invFamily hn q).inv M) T) :
    let B := nativePullback hk W hW M
    let i : nativeManifold hk V hV → Y := Subtype.val
    let C := maxLocus ((invFamily hn q).inv M T) (geoTransformAlong M T).cosupp
    let D := maxLocus ((invFamily hkpos q).inv B Q) (geoTransformAlong B Q).cosupp
    D = i ⁻¹' C ∧ i '' D = C := by
  intro B _ _ _
  obtain ⟨_, hVal⟩ := HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    hn hkpos M hM hMN hTrans h hCan
  exact Lift.max_loci_of_value_comparison hn M hM.isWellFormed hMN hTrans h
    ((invFamily hn q).inv M T) ((invFamily hkpos q).inv B Q)
    (sameIndexMap (n - k) q) (strictMono_sameIndexMap (n - k) q) hVal

set_option backward.isDefEq.respectTransparency false in
/-- An actual whole-record native lift is canonical at the same bound exactly
when its ambient tower is canonical. Empty centres follow the same chronological
steps in both towers. -/
theorem Lift.original_same_bound_canonical_iff
    (hn : 0 < n) (hkpos : 0 < k) (M : MarkedIdeal n X) (hM : IsInvDomain q M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (h : Lift hk W hWc hW M.E T V hVc hV Q) :
    IsCanonical (nativePullback hk W hW M)
        ((invFamily hkpos q).inv (nativePullback hk W hW M)) Q ↔
      IsCanonical M ((invFamily hn q).inv M) T := by
  refine ⟨?_, fun hCan => (HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    hn hkpos M hM hMN hTrans h hCan).1⟩
  induction h with
  | refl => intro _; trivial
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    rintro ⟨hNative, hCentre | hCentre⟩
    · exact ⟨ih hNative, Or.inl (by rw [hCentre, image_empty])⟩
    · have hCan := ih hNative
      have hImage := (Lift.original_same_bound_max_loci hn hkpos M hM hMN hTrans h hCan).2
      exact ⟨hCan, Or.inr (hCentre ▸ hImage)⟩

section ZeroNativeDimension

variable {E : List (Set X)} {hk₀ : 0 ≤ n}
  {hW₀ : ∀ x ∈ W, RegularAtDim (n := n) W x 0}
  {hV₀ : ∀ y ∈ V, RegularAtDim (n := n) V y 0}
  {Q₀ : BlowupTower (nativeManifold hk₀ W hW₀) (nativeManifold hk₀ V hV₀)}

set_option backward.isDefEq.respectTransparency false in
/-- Every centre in a zero-dimensional native lift is empty, on both sides.
The thinness field of the lift suffices at each native stage. -/
theorem Lift.zero_native_isEmptyTowers (h : Lift hk₀ W hWc hW₀ E T V hVc hV₀ Q₀) :
    IsEmptyTower T ∧ IsEmptyTower Q₀ := by
  have hNative : IsEmptyTower Q₀ := by
    induction h with
    | refl => trivial
    | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
      let : DiscreteTopology (nativeManifold hk₀ V hV) :=
        ChartedSpace.discreteTopology (ComplexModel 0) (nativeManifold hk₀ V hV)
      exact ⟨ih, (isOpen_discrete D).interior_eq.symm.trans hint⟩
  exact ⟨(HironakaActualNativeZeroDimensionalHistory.Lift.isEmptyTower_iff h).mpr hNative, hNative⟩

/-- Both chronological towers in a zero-dimensional native lift are canonical
for arbitrary ambient and native invariant functions. -/
theorem Lift.zero_native_canonical {Λ Λ₀ : Type*} [LinearOrder Λ] [LinearOrder Λ₀]
    (h : Lift hk₀ W hWc hW₀ E T V hVc hV₀ Q₀)
    (M : MarkedIdeal n X) (B : MarkedIdeal 0 (nativeManifold hk₀ W hW₀))
    (f : ∀ {Y' : CMfd.{0} n}, BlowupTower X Y' → Y' → Λ)
    (g : ∀ {V' : CMfd.{0} 0}, BlowupTower (nativeManifold hk₀ W hW₀) V' → V' → Λ₀) :
    IsCanonical M f T ∧ IsCanonical B g Q₀ := by
  obtain ⟨hAmbient, hNative⟩ := Lift.zero_native_isEmptyTowers h
  exact ⟨isCanonical_of_isEmptyTower M f T hAmbient, isCanonical_of_isEmptyTower B g Q₀ hNative⟩

set_option backward.isDefEq.respectTransparency false in
/-- The whole current cosupport vanishes on both sides of a zero-dimensional
native lift of an invariant-domain record supported on the section. -/
theorem Lift.zero_native_cosupports (hn : 0 < n)
    (M : MarkedIdeal n X) (hM : IsInvDomain q M) (hMN : M.N ⊆ W)
    (hTrans : IsTransverse n W M.E)
    (h : Lift hk₀ W hWc hW₀ M.E T V hVc hV₀ Q₀) :
    (geoTransformAlong M T).cosupp = ∅ ∧
      (geoTransformAlong (nativePullback hk₀ W hW₀ M) Q₀).cosupp = ∅ := by
  have hTest := isGeoTestTower_of_isEmptyTower M T (Lift.zero_native_isEmptyTowers h).1
  have hAmbient := (HironakaActualNativeZeroDimensionalHistory.original_zero_support_test_resolution
    hW₀ M hM hMN T hTest).2.2
  have hNative := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport
    h hn hM.isWellFormed.isSNCDivisor hTrans M rfl hMN
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)
  rw [hAmbient, preimage_empty] at hNative
  exact ⟨hAmbient, hNative⟩

/-- At native dimension zero both maximum loci are empty for any current
value functions on the lifted records. -/
theorem Lift.zero_native_max_loci {Λ Λ₀ : Type*} [LinearOrder Λ] [LinearOrder Λ₀]
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain q M) (hMN : M.N ⊆ W)
    (hTrans : IsTransverse n W M.E)
    (h : Lift hk₀ W hWc hW₀ M.E T V hVc hV₀ Q₀)
    (f : Y → Λ) (g : nativeManifold hk₀ V hV₀ → Λ₀) :
    maxLocus f (geoTransformAlong M T).cosupp = ∅ ∧
      maxLocus g (geoTransformAlong (nativePullback hk₀ W hW₀ M) Q₀).cosupp = ∅ := by
  obtain ⟨hAmbient, hNative⟩ := Lift.zero_native_cosupports hn M hM hMN hTrans h
  simp [maxLocus, hAmbient, hNative]

end ZeroNativeDimension

end

end Hironaka.HironakaG1NormalCentreTransport
