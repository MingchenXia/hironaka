import Hironaka.Analytic.Unibranch.OriginalNativeShadowCommonCentre

/-! ONE actual proper-fibre base shrink gives a uniform ORIGINAL-prefix
bound in EVERY current window. The actual compact shadow maximum, chart
USC neighbourhoods and empty-shadow branch are constructed internally.
Blueprint FIRST: original-native-shadow-uniform-bound.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowUniformBound
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG1CanonicalStageCentreIdeal
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain)

variable {X Z : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*}
  [LinearOrder Λ] [Nonempty Λ] {ι : Type*}
  (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (q : xs.Y ⟶ Z) (hq : IsProperMap q.hom.left.base)
  (K : Set Z.obj.left) (hK : IsCompact K) (C : Set xs.Y.obj.left) (hC : IsClosed C)
  (hTrace : ∀ i (c : xs.carrier i),
    (xs.map i).hom.left.base c ∈ C ↔ c.val ∈ rcos M s.T i)
  (hcover : C ∩ q.hom.left.base ⁻¹' K ⊆ ⋃ i, range (xs.map i).hom.left.base)
  (hne : (C ∩ q.hom.left.base ⁻¹' K).Nonempty)

local notation "S" => (C ∩ q.hom.left.base ⁻¹' K)
local notation "D" => OriginalNativeShadowCommonCentre.valueDomain w M B s xs
local notation "v" => OriginalNativeShadowCommonCentre.currentValue w M B s xs

/-- An actual attained compact-shadow maximizing point, never a caller input. -/
def anchor : xs.Y.obj.left :=
  (OriginalNativeShadowCommonCentre.exists_shadow_maximum w M B s xs hD hClass
    q hq K hK C hC hTrace hcover hne).choose

theorem anchor_mem : anchor w M B s xs hD hClass q hq K hK C hC hTrace hcover hne ∈ S :=
  (OriginalNativeShadowCommonCentre.exists_shadow_maximum w M B s xs hD hClass
    q hq K hK C hC hTrace hcover hne).choose_spec.1

def level : Λ := v (anchor w M B s xs hD hClass q hq K hK C hC hTrace hcover hne)

theorem level_bounds_shadow (x : xs.Y.obj.left) (hx : x ∈ S) :
    v x ≤ level w M B s xs hD hClass q hq K hK C hC hTrace hcover hne :=
  (OriginalNativeShadowCommonCentre.exists_shadow_maximum w M B s xs hD hClass
    q hq K hK C hC hTrace hcover hne).choose_spec.2 x hx

private def representative (x : {y : xs.Y.obj.left // y ∈ C ∩ q.hom.left.base ⁻¹' K}) : Σ i, xs.carrier i :=
  let p := mem_iUnion.mp (hcover x.property)
  ⟨p.choose, p.choose_spec.choose⟩

omit [Nonempty Λ] in
private theorem representative_square (x : {y : xs.Y.obj.left // y ∈ C ∩ q.hom.left.base ⁻¹' K}) :
    (xs.map (representative w M B s xs q K C hcover x).1).hom.left.base
      (representative w M B s xs q K C hcover x).2 = x.val :=
  (mem_iUnion.mp (hcover x.property)).choose_spec.choose_spec

/-- A genuine chart RANGE is intersected with the USC-good neighbourhood. -/
def goodChart (x : {y : xs.Y.obj.left // y ∈ C ∩ q.hom.left.base ⁻¹' K}) : Opens xs.Y.obj.left :=
  ⟨range (xs.map (representative w M B s xs q K C hcover x).1).hom.left.base ∩
      interior {y | y ∈ D → v y ≤ v x.val},
    (xs.isOpenImmersion (representative w M B s xs q K C hcover x).1).base_open.isOpen_range.inter
      isOpen_interior⟩

include hD hClass hTrace in
theorem mem_goodChart (x : {y : xs.Y.obj.left // y ∈ C ∩ q.hom.left.base ⁻¹' K}) : x.val ∈ goodChart w M B s xs q K C hcover x := by
  have hs := representative_square w M B s xs q K C hcover x
  have hcos := (hTrace (representative w M B s xs q K C hcover x).1
    (representative w M B s xs q K C hcover x).2).mp (hs.symm ▸ x.property.1)
  have hxD : x.val ∈ D :=
    ⟨_, (representative w M B s xs q K C hcover x).2, hs, hcos⟩
  refine ⟨⟨_, hs⟩, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact OriginalNativeShadowCommonCentre.currentValue_usc w M B s xs hD hClass x.val hxD

/-- An actual open containing the WHOLE inverse shadow, not only threshold points. -/
def goodOpen : Opens xs.Y.obj.left :=
  ⟨Cᶜ ∪ ⋃ x : {y : xs.Y.obj.left // y ∈ C ∩ q.hom.left.base ⁻¹' K}, (goodChart w M B s xs q K C hcover x : Set xs.Y.obj.left),
    hC.isOpen_compl.union (isOpen_iUnion fun x => (goodChart w M B s xs q K C hcover x).isOpen)⟩

include hD hClass hTrace in
theorem whole_shadow_subset_goodOpen : q.hom.left.base ⁻¹' K ⊆
    (goodOpen w M B s xs q K C hC hcover : Set xs.Y.obj.left) := by
  intro y hy
  by_cases hyC : y ∈ C
  · exact Or.inr (mem_iUnion.mpr ⟨⟨y, hyC, hy⟩,
      mem_goodChart w M B s xs hD hClass q K C hTrace hcover ⟨y, hyC, hy⟩⟩)
  · exact Or.inl hyC

include hD hClass hTrace in
theorem goodOpen_bound (y : xs.Y.obj.left) (hyC : y ∈ C)
    (hy : y ∈ goodOpen w M B s xs q K C hC hcover) :
    y ∈ D ∧ v y ≤ level w M B s xs hD hClass q hq K hK C hC hTrace hcover hne := by
  rcases hy with hyNot | hyChart
  · exact (hyNot hyC).elim
  · obtain ⟨x, hyRange, hyBound⟩ := mem_iUnion.mp hyChart
    obtain ⟨c, hcy⟩ := hyRange
    have hcos := (hTrace (representative w M B s xs q K C hcover x).1 c).mp (hcy.symm ▸ hyC)
    have hyD : y ∈ D := ⟨_, c, hcy, hcos⟩
    exact ⟨hyD, (interior_subset hyBound hyD).trans
      (level_bounds_shadow w M B s xs hD hClass q hq K hK C hC hTrace hcover hne x.val x.property)⟩

local notation "Ω" => goodOpen w M B s xs q K C hC hcover
local notation "hΩ" => whole_shadow_subset_goodOpen w M B s xs hD hClass q K C hC hTrace hcover

/-- ONE actual precompact base is derived from the whole-fibre good open. -/
def neighbourhood := OriginalNativeProperFibreShrink.neighbourhood q hq Ω K hK hΩ

def source : SourceReducedComplexSpace := OriginalNativeProperFibreShrink.source q hq Ω K hK hΩ

def inclusion : source w M B s xs hD hClass q hq K hK C hC hTrace hcover ⟶ xs.Y :=
  OriginalNativeProperFibreShrink.sourceInclusion q hq Ω K hK hΩ

local notation "nU" => neighbourhood w M B s xs hD hClass q hq K hK C hC hTrace hcover
local notation "aU" => anchor w M B s xs hD hClass q hq K hK C hC hTrace hcover hne
local notation "λU" => level w M B s xs hD hClass q hq K hK C hC hTrace hcover hne

theorem uniform_native_bound (y : xs.Y.obj.left) (hyC : y ∈ C)
    (hyN : q.hom.left.base y ∈ range (nU).inclusion.hom.left.base) :
    y ∈ D ∧ v y ≤ λU := by
  have hyO : q.hom.left.base y ∈ (nU).openSet := by
    rwa [(nU).inclusion_range] at hyN
  exact goodOpen_bound w M B s xs hD hClass q hq K hK C hC hTrace hcover hne y hyC
    (OriginalNativeProperFibreShrink.preimage_neighbourhood_subset q hq Ω K hK hΩ hyO)

/-- EVERY original-prefix current value is bounded after the SAME base restriction. -/
theorem uniform_window_bound (i : ι) (c : xs.carrier i)
    (hOver : q.hom.left.base ((xs.map i).hom.left.base c) ∈ range (nU).inclusion.hom.left.base)
    (hc : c.val ∈ rcos M s.T i) : rvalue B.toResolutionInvariant M s.T i c.val ≤ λU := by
  have h := (uniform_native_bound w M B s xs hD hClass q hq K hK C hC hTrace hcover hne
    ((xs.map i).hom.left.base c) ((hTrace i c).mpr hc) hOver).2
  rwa [OriginalNativeShadowCommonCentre.currentValue_window w M B s xs hD hClass i c hc] at h

/-- The SAME actual maximizing point lies in the literal inverse-open native source. -/
def restrictedAnchor : (source w M B s xs hD hClass q hq K hK C hC hTrace hcover).obj.left :=
  ⟨aU, (nU).contains (anchor_mem w M B s xs hD hClass q hq K hK C hC hTrace hcover hne).2⟩

theorem restrictedAnchor_image :
    (inclusion w M B s xs hD hClass q hq K hK C hC hTrace hcover).hom.left.base
      (restrictedAnchor w M B s xs hD hClass q hq K hK C hC hTrace hcover hne) = aU := rfl

def shadow : Set (source w M B s xs hD hClass q hq K hK C hC hTrace hcover).obj.left :=
  OriginalNativeProperFibreShrink.shadow q hq Ω K hK hΩ

theorem shadow_compact : IsCompact (shadow w M B s xs hD hClass q hq K hK C hC hTrace hcover) :=
  OriginalNativeProperFibreShrink.shadow_compact q hq Ω K hK hΩ

theorem shadow_image :
    (inclusion w M B s xs hD hClass q hq K hK C hC hTrace hcover).hom.left.base ''
      shadow w M B s xs hD hClass q hq K hK C hC hTrace hcover = q.hom.left.base ⁻¹' K :=
  OriginalNativeProperFibreShrink.shadow_image q hq Ω K hK hΩ

theorem maximizing_window : ∃ i, ∃ c : xs.carrier i,
    (xs.map i).hom.left.base c = aU ∧ c.val ∈ rcos M s.T i ∧
      rvalue B.toResolutionInvariant M s.T i c.val = λU ∧
      q.hom.left.base ((xs.map i).hom.left.base c) ∈ range (nU).inclusion.hom.left.base := by
  obtain ⟨i, c, hca⟩ := mem_iUnion.mp (hcover (anchor_mem w M B s xs hD hClass q hq K hK C hC hTrace hcover hne))
  have hc : c.val ∈ rcos M s.T i :=
    (hTrace i c).mp (hca.symm ▸ (anchor_mem w M B s xs hD hClass q hq K hK C hC hTrace hcover hne).1)
  refine ⟨i, c, hca, hc, ?_, ?_⟩
  · rw [← OriginalNativeShadowCommonCentre.currentValue_window w M B s xs hD hClass i c hc, hca]
    rfl
  · rw [hca, (nU).inclusion_range]
    exact (nU).contains (anchor_mem w M B s xs hD hClass q hq K hK C hC hTrace hcover hne).2

/-- Ordinary raw native powers derive domains/class and produce the actual all-window bound. -/
theorem native_powers_uniform_bound {X₀ Z₀ : SourceReducedComplexSpace} {n : ℕ}
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
    (ht : ∀ i (c : xs₀.carrier i), (xs₀.map i).hom.left.base c ∈ C₀ ↔
      c.val ∈ rcos (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) s₀.T i)
    (hcov : C₀ ∩ q₀.hom.left.base ⁻¹' K₀ ⊆ ⋃ i, range (xs₀.map i).hom.left.base)
    (hne₀ : (C₀ ∩ q₀.hom.left.base ⁻¹' K₀).Nonempty) :
    ∃ V : OriginalNativePrecompactNeighbourhood.Neighbourhood Z₀ K₀ ⊤,
    ∃ l : Λ₀, ∃ i, ∃ c : xs₀.carrier i,
      (xs₀.map i).hom.left.base c ∈ C₀ ∩ q₀.hom.left.base ⁻¹' K₀ ∧
      c.val ∈ rcos (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) s₀.T i ∧
      rvalue B₀.toResolutionInvariant (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) s₀.T i c.val = l ∧
      q₀.hom.left.base ((xs₀.map i).hom.left.base c) ∈ range V.inclusion.hom.left.base ∧
      ∀ j (z : xs₀.carrier j),
        q₀.hom.left.base ((xs₀.map j).hom.left.base z) ∈ range V.inclusion.hom.left.base →
        z.val ∈ rcos (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) s₀.T j →
        rvalue B₀.toResolutionInvariant (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) s₀.T j z.val ≤ l := by
  let P := fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)
  let hD₀ : ∀ i, IsInvDomain n (P i) :=
    fun i => HironakaActualPowerBoundaryExponents.powerMarked_isInvDomain (raw i) (hrec i).1 (he i)
  have hClass₀ := HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers w₀ raw H hrec e he hd
  let A := neighbourhood w₀ P B₀ s₀ xs₀ hD₀ hClass₀ q₀ hq₀ K₀ hK₀ C₀ hC₀ ht hcov
  let V : OriginalNativePrecompactNeighbourhood.Neighbourhood Z₀ K₀ ⊤ :=
    ⟨A.openSet, A.compactClosure, A.contains, fun _ _ => trivial⟩
  obtain ⟨i, c, hca, hc, hv, hOver⟩ := maximizing_window w₀ P B₀ s₀ xs₀ hD₀ hClass₀
    q₀ hq₀ K₀ hK₀ C₀ hC₀ ht hcov hne₀
  refine ⟨V, level w₀ P B₀ s₀ xs₀ hD₀ hClass₀ q₀ hq₀ K₀ hK₀ C₀ hC₀ ht hcov hne₀,
    i, c, ?_, hc, hv, hOver, ?_⟩
  · rw [hca]
    exact anchor_mem w₀ P B₀ s₀ xs₀ hD₀ hClass₀ q₀ hq₀ K₀ hK₀ C₀ hC₀ ht hcov hne₀
  · exact uniform_window_bound w₀ P B₀ s₀ xs₀ hD₀ hClass₀ q₀ hq₀ K₀ hK₀ C₀ hC₀ ht hcov hne₀

private theorem empty_good {Y₀ Z₀ : SourceReducedComplexSpace} (p : Y₀ ⟶ Z₀)
    (L : Set Z₀.obj.left) (T : Set Y₀.obj.left)
    (hEmpty : T ∩ p.hom.left.base ⁻¹' L = ∅) : p.hom.left.base ⁻¹' L ⊆ Tᶜ := by
  intro y hy hyT
  have h : y ∈ T ∩ p.hom.left.base ⁻¹' L := ⟨hyT, hy⟩
  rw [hEmpty] at h
  exact h

def emptyNeighbourhood {Y₀ Z₀ : SourceReducedComplexSpace} (p : Y₀ ⟶ Z₀)
    (hp : IsProperMap p.hom.left.base) (L : Set Z₀.obj.left) (hL : IsCompact L)
    (T : Set Y₀.obj.left) (hT : IsClosed T) (hEmpty : T ∩ p.hom.left.base ⁻¹' L = ∅) :=
  OriginalNativeProperFibreShrink.neighbourhood p hp ⟨Tᶜ, hT.isOpen_compl⟩ L hL
    (empty_good p L T hEmpty)

theorem empty_threshold_preimage {Y₀ Z₀ : SourceReducedComplexSpace} (p : Y₀ ⟶ Z₀)
    (hp : IsProperMap p.hom.left.base) (L : Set Z₀.obj.left) (hL : IsCompact L)
    (T : Set Y₀.obj.left) (hT : IsClosed T) (hEmpty : T ∩ p.hom.left.base ⁻¹' L = ∅) :
    p.hom.left.base ⁻¹' range (emptyNeighbourhood p hp L hL T hT hEmpty).inclusion.hom.left.base ∩ T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro y ⟨hyN, hyT⟩
  rw [(emptyNeighbourhood p hp L hL T hT hEmpty).inclusion_range] at hyN
  exact OriginalNativeProperFibreShrink.preimage_neighbourhood_subset p hp
    ⟨Tᶜ, hT.isOpen_compl⟩ L hL (empty_good p L T hEmpty) hyN hyT

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowUniformBound
