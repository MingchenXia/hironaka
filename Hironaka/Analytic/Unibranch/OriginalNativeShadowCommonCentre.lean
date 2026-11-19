import Hironaka.Analytic.Unibranch.HironakaG1CanonicalStageChoiceIndependence
import Hironaka.Analytic.Unibranch.HironakaG1NativeWindowInitialClass
import Hironaka.Analytic.Unibranch.OriginalNativeProperFibreShrink

/-! Actual current-prefix values and whole common level centres near ONE
compact shadow. No whole-cosupport footprint cover or powered native
compression is assumed. Blueprint FIRST: original-native-shadow-common-centre.tex.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowCommonCentre
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG1CanonicalStageCentreIdeal
  HironakaG1CanonicalStageChoiceIndependence ResolutionInvariantOrder
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaIntrinsicReducedCentreIdealSheaf
  HironakaIntrinsicReducedCentreOpenPullback HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealStalk
open ResolutionInvariantSpec (IsInvDomain)

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*}
  [LinearOrder Λ] [Nonempty Λ] {ι κ ν : Type*}
  (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)

/-- The actual image of current cosupports, without a global cover premise. -/
def valueDomain : Set xs.Y.obj.left :=
  {y | ∃ i, ∃ c : xs.carrier i,
    (xs.map i).hom.left.base c = y ∧ c.val ∈ rcos M s.T i}

/-- Choose an actual current representative; values outside its domain are unused. -/
def currentValue (y : xs.Y.obj.left) : Λ := by
  classical
  exact if h : y ∈ valueDomain w M B s xs then
    rvalue B.toResolutionInvariant M s.T h.choose h.choose_spec.choose.val
  else Classical.choice inferInstance

variable (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)

include hD hClass in
/-- Exact original current value, derived from actual prefix class transport. -/
theorem currentValue_window (i : ι) (c : xs.carrier i) (hc : c.val ∈ rcos M s.T i) :
    currentValue w M B s xs ((xs.map i).hom.left.base c) =
      rvalue B.toResolutionInvariant M s.T i c.val := by
  have h : (xs.map i).hom.left.base c ∈ valueDomain w M B s xs := ⟨i, c, rfl, hc⟩
  rw [currentValue, dif_pos h]
  exact (cosupp_value_of_map_eq w M B hD hClass s xs c h.choose_spec.choose
    h.choose_spec.choose_spec.1.symm).2 hc

include hD hClass in
/-- Upper semicontinuity is descended through the actual native window OIs. -/
theorem currentValue_usc :
    IsInvUSCOn (currentValue w M B s xs) (valueDomain w M B s xs) := by
  intro y hy
  obtain ⟨i, c, rfl, hc⟩ := hy
  have hu := (B.toResolutionInvariant.isInvValue.usc (M i) (hD i)
    (s.T i).2 (s.canonical i)).comp
    (continuous_subtype_val : Continuous (Subtype.val : xs.carrier i → (s.T i).1))
  have huc : ∀ᶠ z in 𝓝 c, z.val ∈ rcos M s.T i →
      rvalue B.toResolutionInvariant M s.T i z.val ≤
        rvalue B.toResolutionInvariant M s.T i c.val := hu c hc
  have him : Topology.IsOpenEmbedding
      (fun z : xs.carrier i => (xs.map i).hom.left.base z) :=
    (xs.isOpenImmersion i).base_open
  rw [← him.map_nhds_eq c]
  change ∀ᶠ z in 𝓝 c, (xs.map i).hom.left.base z ∈ valueDomain w M B s xs →
    currentValue w M B s xs ((xs.map i).hom.left.base z) ≤
      currentValue w M B s xs ((xs.map i).hom.left.base c)
  filter_upwards [huc] with z hz hzD
  obtain ⟨j, a, ha, hca⟩ := hzD
  have hcz := (cosupp_value_of_map_eq w M B hD hClass s xs z a ha.symm).1.mpr hca
  rw [currentValue_window w M B s xs hD hClass i z hcz,
    currentValue_window w M B s xs hD hClass i c hc]
  exact hz hcz

variable {Z : SourceReducedComplexSpace} (q : xs.Y ⟶ Z)
  (hq : IsProperMap q.hom.left.base) (K : Set Z.obj.left) (hK : IsCompact K)
  (C : Set xs.Y.obj.left) (hC : IsClosed C)
  (hTrace : ∀ i (c : xs.carrier i),
    (xs.map i).hom.left.base c ∈ C ↔ c.val ∈ rcos M s.T i)

include hD hClass hq hK hC hTrace in
/-- An attained maximum on the actual compact inverse threshold shadow. -/
theorem exists_shadow_maximum
    (hcover : C ∩ q.hom.left.base ⁻¹' K ⊆ ⋃ i, range (xs.map i).hom.left.base)
    (hne : (C ∩ q.hom.left.base ⁻¹' K).Nonempty) :
    ∃ y ∈ C ∩ q.hom.left.base ⁻¹' K,
      ∀ z ∈ C ∩ q.hom.left.base ⁻¹' K,
        currentValue w M B s xs z ≤ currentValue w M B s xs y := by
  have hsub : C ∩ q.hom.left.base ⁻¹' K ⊆ valueDomain w M B s xs := by
    intro y hy
    obtain ⟨i, c, rfl⟩ := mem_iUnion.mp (hcover hy)
    exact ⟨i, c, rfl, (hTrace i c).mp hy.1⟩
  exact ((currentValue_usc w M B s xs hD hClass).mono hsub).exists_isMaxOn
    ((hq.isCompact_preimage hK).inter_left hC) hne

/-- The literal open union of one selected current chart family. -/
def chartOpen (f : κ → ι) : Opens xs.Y.obj.left :=
  ⟨⋃ j, range (xs.map (f j)).hom.left.base,
    isOpen_iUnion (fun j => (xs.isOpenImmersion (f j)).base_open.isOpen_range)⟩

include hD hClass hq hK hC hTrace in
/-- An ACTUAL maximizing representative in any family covering only the shadow. -/
theorem exists_selected_shadow_maximum (f : κ → ι)
    (hcover : C ∩ q.hom.left.base ⁻¹' K ⊆ chartOpen w M B s xs f)
    (hne : (C ∩ q.hom.left.base ⁻¹' K).Nonempty) :
    ∃ j, ∃ c : xs.carrier (f j),
      (xs.map (f j)).hom.left.base c ∈ C ∩ q.hom.left.base ⁻¹' K ∧
      c.val ∈ rcos M s.T (f j) ∧
      ∀ i (z : xs.carrier i), (xs.map i).hom.left.base z ∈ C ∩ q.hom.left.base ⁻¹' K →
        z.val ∈ rcos M s.T i →
        rvalue B.toResolutionInvariant M s.T i z.val ≤
          rvalue B.toResolutionInvariant M s.T (f j) c.val := by
  have hall : C ∩ q.hom.left.base ⁻¹' K ⊆ ⋃ i, range (xs.map i).hom.left.base := by
    intro y hy
    obtain ⟨j, c, hcy⟩ := mem_iUnion.mp (hcover hy)
    exact mem_iUnion.mpr ⟨f j, c, hcy⟩
  obtain ⟨y, hy, hmax⟩ := exists_shadow_maximum w M B s xs hD hClass q hq K hK C hC
    hTrace hall hne
  obtain ⟨j, c, rfl⟩ := mem_iUnion.mp (hcover hy)
  have hc := (hTrace (f j) c).mp hy.1
  refine ⟨j, c, hy, hc, fun i z hz hcz => ?_⟩
  have h := hmax _ hz
  rwa [currentValue_window w M B s xs hD hClass i z hcz,
    currentValue_window w M B s xs hD hClass (f j) c hc] at h

variable (f : κ → ι) (g : ν → ι)
  (hP : C ∩ q.hom.left.base ⁻¹' K ⊆ chartOpen w M B s xs f)
  (hQ : C ∩ q.hom.left.base ⁻¹' K ⊆ chartOpen w M B s xs g)

/-- The actual common good open contains the WHOLE compact inverse fibre. -/
def commonGoodOpen : Opens xs.Y.obj.left :=
  ⟨Cᶜ ∪ ((chartOpen w M B s xs f : Set xs.Y.obj.left) ∩ chartOpen w M B s xs g),
    hC.isOpen_compl.union ((chartOpen w M B s xs f).isOpen.inter
      (chartOpen w M B s xs g).isOpen)⟩

include hP hQ in
omit [Nonempty Λ] in
theorem shadow_subset_commonGoodOpen : q.hom.left.base ⁻¹' K ⊆
    (commonGoodOpen w M B s xs C hC f g : Set xs.Y.obj.left) := by
  intro y hy
  by_cases hyC : y ∈ C
  · exact Or.inr ⟨hP ⟨hyC, hy⟩, hQ ⟨hyC, hy⟩⟩
  · exact Or.inl hyC

/-- One internally derived actual precompact base shared by both chart families. -/
def commonNeighbourhood :=
  OriginalNativeProperFibreShrink.neighbourhood q hq
    (commonGoodOpen w M B s xs C hC f g) K hK
    (shadow_subset_commonGoodOpen w M B s xs q K C hC f g hP hQ)

/-- The SAME literal native inverse-open source of that common target. -/
def commonSource : SourceReducedComplexSpace :=
  OriginalNativeProperFibreShrink.source q hq
    (commonGoodOpen w M B s xs C hC f g) K hK
    (shadow_subset_commonGoodOpen w M B s xs q K C hC f g hP hQ)

def commonInclusion : commonSource w M B s xs q hq K hK C hC f g hP hQ ⟶ xs.Y :=
  OriginalNativeProperFibreShrink.sourceInclusion q hq
    (commonGoodOpen w M B s xs C hC f g) K hK
    (shadow_subset_commonGoodOpen w M B s xs q K C hC f g hP hQ)

instance commonInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (commonInclusion w M B s xs q hq K hK C hC f g hP hQ).hom.left :=
  OriginalNativeProperFibreShrink.sourceInclusion_isOpenImmersion _ _ _ _ _ _

/-- The actual restricted map is to the SAME common target. -/
def commonProjection : commonSource w M B s xs q hq K hK C hC f g hP hQ ⟶
    (commonNeighbourhood w M B s xs q hq K hK C hC f g hP hQ).source :=
  OriginalNativeProperFibreShrink.projection q hq
    (commonGoodOpen w M B s xs C hC f g) K hK
    (shadow_subset_commonGoodOpen w M B s xs q K C hC f g hP hQ)

omit [Nonempty Λ] in
theorem commonProjection_square :
    commonProjection w M B s xs q hq K hK C hC f g hP hQ ≫
        (commonNeighbourhood w M B s xs q hq K hK C hC f g hP hQ).inclusion =
      commonInclusion w M B s xs q hq K hK C hC f g hP hQ ≫ q :=
  OriginalNativeProperFibreShrink.projection_inclusion _ _ _ _ _ _

omit [Nonempty Λ] in
theorem commonProjection_scalar :
    (commonProjection w M B s xs q hq K hK C hC f g hP hQ).hom.left ≫
        (commonNeighbourhood w M B s xs q hq K hK C hC f g hP hQ).source.obj.hom =
      (commonSource w M B s xs q hq K hK C hC f g hP hQ).obj.hom :=
  Over.w (commonProjection w M B s xs q hq K hK C hC f g hP hQ).hom

omit [Nonempty Λ] in
theorem commonProjection_isProperMap : IsProperMap
    (commonProjection w M B s xs q hq K hK C hC f g hP hQ).hom.left.base :=
  OriginalNativeProperFibreShrink.projection_isProperMap _ _ _ _ _ _

omit [Nonempty Λ] in
/-- EVERY threshold point over the common target belongs to BOTH actual chart unions. -/
theorem threshold_in_both_covers
    (y : (commonSource w M B s xs q hq K hK C hC f g hP hQ).obj.left)
    (hy : (commonInclusion w M B s xs q hq K hK C hC f g hP hQ).hom.left.base y ∈ C) :
    (commonInclusion w M B s xs q hq K hK C hC f g hP hQ).hom.left.base y ∈
      (chartOpen w M B s xs f : Set xs.Y.obj.left) ∩ chartOpen w M B s xs g := by
  have h := OriginalNativeProperFibreShrink.source_in_goodOpen q hq
    (commonGoodOpen w M B s xs C hC f g) K hK
    (shadow_subset_commonGoodOpen w M B s xs q K C hC f g hP hQ) ⟨y, rfl⟩
  exact h.resolve_left (fun hnot => hnot hy)

/-- Actual selected current level support, using the original retained prefixes. -/
def levelSupport (a : κ → ι) (l : Λ) : Set xs.Y.obj.left :=
  ⋃ j, (xs.map (a j)).hom.left.base ''
    {c : xs.carrier (a j) | c.val ∈ rcos M s.T (a j) ∧
      rvalue B.toResolutionInvariant M s.T (a j) c.val = l}

include hD hClass hTrace in
private theorem levelSupport_trace {W : SourceReducedComplexSpace} (j : W ⟶ xs.Y)
    {μ : Type*} (a : μ → ι) (l : Λ)
    (hc : ∀ y : W.obj.left, j.hom.left.base y ∈ C →
      j.hom.left.base y ∈ chartOpen w M B s xs a) :
    j.hom.left.base ⁻¹' levelSupport w M B s xs a l =
      {y | j.hom.left.base y ∈ C ∧ currentValue w M B s xs (j.hom.left.base y) = l} := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, c, ⟨hcos, hv⟩, hcy⟩ := mem_iUnion.mp hy
    constructor
    · rw [← hcy]
      exact (hTrace (a i) c).mpr hcos
    · rw [← hcy, currentValue_window w M B s xs hD hClass (a i) c hcos]
      exact hv
  · rintro ⟨hyC, hyv⟩
    obtain ⟨i, c, hcy⟩ := mem_iUnion.mp (hc y hyC)
    have hcos : c.val ∈ rcos M s.T (a i) :=
      (hTrace (a i) c).mp (hcy.symm ▸ hyC)
    have hv : rvalue B.toResolutionInvariant M s.T (a i) c.val = l := by
      rw [← currentValue_window w M B s xs hD hClass (a i) c hcos, hcy]
      exact hyv
    exact mem_iUnion.mpr ⟨i, c, ⟨hcos, hv⟩, hcy⟩

local notation "jN" => commonInclusion w M B s xs q hq K hK C hC f g hP hQ

include hD hClass hTrace in
/-- Both actual level centres have the literal same trace on the SAME inverse-open source. -/
theorem levelSupport_preimage_eq (l : Λ) :
    ((jN).hom.left.base ⁻¹' levelSupport w M B s xs f l =
      {y | (jN).hom.left.base y ∈ C ∧ currentValue w M B s xs ((jN).hom.left.base y) = l}) ∧
    ((jN).hom.left.base ⁻¹' levelSupport w M B s xs g l =
      {y | (jN).hom.left.base y ∈ C ∧ currentValue w M B s xs ((jN).hom.left.base y) = l}) := by
  exact ⟨levelSupport_trace w M B s xs hD hClass C hTrace jN f l
      (fun y hy => (threshold_in_both_covers w M B s xs q hq K hK C hC f g hP hQ y hy).1),
    levelSupport_trace w M B s xs hD hClass C hTrace jN g l
      (fun y hy => (threshold_in_both_covers w M B s xs q hq K hK C hC f g hP hQ y hy).2)⟩

include hD hClass hTrace in
theorem levelSupport_preimage_eq_each_other (l : Λ) :
    (jN).hom.left.base ⁻¹' levelSupport w M B s xs f l =
      (jN).hom.left.base ⁻¹' levelSupport w M B s xs g l :=
  (levelSupport_preimage_eq w M B s xs hD hClass q hq K hK C hC hTrace f g hP hQ l).1.trans
    (levelSupport_preimage_eq w M B s xs hD hClass q hq K hK C hC hTrace f g hP hQ l).2.symm

include hD hClass hTrace in
/-- Equality of ENTIRE pulled unit submodules on the SAME original scalar sheaf. -/
theorem wholeSubmodule_eq (l : Λ) :
    nativePulledIdealSubmodule (jN).hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left (levelSupport w M B s xs f l))
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (levelSupport w M B s xs f l)) =
    nativePulledIdealSubmodule (jN).hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left (levelSupport w M B s xs g l))
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (levelSupport w M B s xs g l)) := by
  rw [openImmersion_pulled_submodule_eq, openImmersion_pulled_submodule_eq,
    levelSupport_preimage_eq_each_other w M B s xs hD hClass q hq K hK C hC hTrace f g hP hQ l]

include hD hClass hTrace in
theorem wholeSectionIdeal_eq (l : Λ)
    (V : Opens (commonSource w M B s xs q hq K hK C hC f g hP hQ).obj.left.toTopCat) :
    nativePulledIdealSectionIdeal (jN).hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left (levelSupport w M B s xs f l))
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (levelSupport w M B s xs f l)) V =
    nativePulledIdealSectionIdeal (jN).hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left (levelSupport w M B s xs g l))
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (levelSupport w M B s xs g l)) V := by
  rw [openImmersion_pulled_sectionIdeal_eq, openImmersion_pulled_sectionIdeal_eq,
    levelSupport_preimage_eq_each_other w M B s xs hD hClass q hq K hK C hC hTrace f g hP hQ l]

include hD hClass hTrace in
theorem wholeStalkIdeal_eq (l : Λ)
    (y : (commonSource w M B s xs q hq K hK C hC f g hP hQ).obj.left) :
    nativePulledIdealStalkIdeal (jN).hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left (levelSupport w M B s xs f l))
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (levelSupport w M B s xs f l)) y =
    nativePulledIdealStalkIdeal (jN).hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left (levelSupport w M B s xs g l))
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (levelSupport w M B s xs g l)) y := by
  rw [openImmersion_pulled_stalkIdeal_eq, openImmersion_pulled_stalkIdeal_eq,
    levelSupport_preimage_eq_each_other w M B s xs hD hClass q hq K hK C hC hTrace f g hP hQ l]

/-- Ordinary RAW native powers derive all initial class fields internally. -/
theorem native_powers_shadow_maximum {X₀ Z₀ : SourceReducedComplexSpace} {n : ℕ}
    {Λ₀ : Type*} [LinearOrder Λ₀] [Nonempty Λ₀] {η : Type*}
    (w₀ : η → DimEmbedding X₀ n) (raw : ∀ i, MarkedIdeal n (Amb w₀ i))
    (H : ℕ → ℕ) (hrec : ∀ i, HironakaG11PresReduction.IsNativeWindowRecord (w₀ i) (raw i) H)
    (e : η → ℕ) (he : ∀ i, 1 ≤ e i)
    (hd : ∀ i j, (HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)).d =
      (HironakaActualPowerBoundaryExponents.powerMarked (raw j) (e j)).d)
    (B₀ : BMInvariant n (fun {Y} A A' => LocWPEquiv (X := Y) A A') n Λ₀)
    {r : ℕ} (s₀ : GStage B₀.toResolutionInvariant
      (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) (mapAdm w₀) r)
    (xs₀ : XStage w₀ s₀.T) (q₀ : xs₀.Y ⟶ Z₀) (hq₀ : IsProperMap q₀.hom.left.base)
    (K₀ : Set Z₀.obj.left) (hK₀ : IsCompact K₀) (C₀ : Set xs₀.Y.obj.left) (hC₀ : IsClosed C₀)
    (hTrace₀ : ∀ i (c : xs₀.carrier i), (xs₀.map i).hom.left.base c ∈ C₀ ↔
      c.val ∈ rcos (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) s₀.T i)
    (hcover : C₀ ∩ q₀.hom.left.base ⁻¹' K₀ ⊆ ⋃ i, range (xs₀.map i).hom.left.base)
    (hne : (C₀ ∩ q₀.hom.left.base ⁻¹' K₀).Nonempty) :
    ∃ y ∈ C₀ ∩ q₀.hom.left.base ⁻¹' K₀, ∀ z ∈ C₀ ∩ q₀.hom.left.base ⁻¹' K₀,
      currentValue w₀ (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i))
        B₀ s₀ xs₀ z ≤
      currentValue w₀ (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i))
        B₀ s₀ xs₀ y := by
  exact exists_shadow_maximum w₀
    (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) B₀ s₀ xs₀
    (fun i => HironakaActualPowerBoundaryExponents.powerMarked_isInvDomain (raw i) (hrec i).1 (he i))
    (HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers w₀ raw H hrec e he hd)
    q₀ hq₀ K₀ hK₀ C₀ hC₀ hTrace₀ hcover hne

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowCommonCentre
