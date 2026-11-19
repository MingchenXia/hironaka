import Hironaka.Resolution.HironakaG1RatioGraphSupportedComparison
import Hironaka.Resolution.HironakaG1CrossAmbientNativeClassComparison
import Hironaka.Resolution.HironakaG1CodimensionTwoChartTransport

/-! Reflected endpoint alignment on the supported branch. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG1RatioGraphEndpointAlignment
noncomputable section
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaG1CrossAmbientNativeComparison HironakaG1CrossAmbientNativeClassComparison
  HironakaG1RatioGraphSupportedComparison HironakaG1NativeChartValueOrder

/-- The strict-order alignment premise on a common supported endpoint
is equivalent to strict-order agreement on paired native endpoints.
The surjectivity premises hold for the actual strict graph reads. -/
theorem supportedEndpoint_alignment_iff
    {A B Y L R L' R' : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder L'] [LinearOrder R']
    {D : Set Y} {i : A → Y} {j : B → Y}
    (f : A → L) (g : B → R) (F : Y → L') (G : Y → R')
    (l : L → L') (r : R → R') (hl : StrictMono l) (hr : StrictMono r)
    (hi : D ⊆ range i) (hj : D ⊆ range j)
    (hF : ∀ x, i x ∈ D → F (i x) = l (f x))
    (hG : ∀ x, j x ∈ D → G (j x) = r (g x)) :
    (∀ y ∈ D, ∀ z ∈ D, F y < F z ↔ G y < G z) ↔
      (∀ x x' : A, ∀ y y' : B, i x ∈ D → i x' ∈ D →
        j y = i x → j y' = i x' → (f x < f x' ↔ g y < g y')) := by
  constructor
  · intro h x x' y y' hx hx' hpair hpair'
    exact supportedEndpoint_order_iff f g F G l r hl hr hF hG h hx hx' hpair hpair'
  · intro h u hu v hv
    obtain ⟨x,hx⟩ := hi hu
    obtain ⟨x',hx'⟩ := hi hv
    obtain ⟨y,hy⟩ := hj hu
    obtain ⟨y',hy'⟩ := hj hv
    have hxu : i x ∈ D := hx.symm ▸ hu
    have hxv : i x' ∈ D := hx'.symm ▸ hv
    have hyu : j y ∈ D := hy.symm ▸ hu
    have hyv : j y' ∈ D := hy'.symm ▸ hv
    have hLu : F u = l (f x) := hx ▸ hF x hxu
    have hLv : F v = l (f x') := hx' ▸ hF x' hxv
    have hRu : G u = r (g y) := hy ▸ hG y hyu
    have hRv : G v = r (g y') := hy' ▸ hG y' hyv
    rw [hLu,hLv,hRu,hRv,hl.lt_iff_lt,hr.lt_iff_lt]
    exact h x x' y y' hxu hxv (hy.trans hx.symm) (hy'.trans hx'.symm)

/-- When the strict lifts are realized on a single actual native chart
tower, the native source weak class, carrier dimension and normalized
endpoint input exponents derive supported alignment for independent true
marks. Both supported ambient endpoints map to the same clock points. -/
theorem supported_alignment_of_shared_native_tower
    {m₁ m₂ k q : ℕ} {A Z : CMfd.{0} k} {C₁ C₂ : MarkedIdeal k A} {S : BlowupTower A Z}
    (R₁ : NativeChartRealization C₁ S m₁ q) (R₂ : NativeChartRealization C₂ S m₂ q)
    (hk : 0 < k) (hClass : LocWPEquiv C₁ C₂) (hDim : SameCarrierDim C₁ C₂)
    (hExp : ∀ H ∈ C₁.E, ∀ x ∈ C₁.cosupp, x ∈ H →
      C₂.d * divExpAlong k C₁.N C₁.ideal H x = C₁.d * divExpAlong k C₂.N C₂.ideal H x)
    (hCan : IsCanonical R₁.record (R₁.ambientInvariant hk) R₁.tower) :
    let D := (geoTransformAlong C₁ S).cosupp
    let f₁ := R₁.ambientInvariant hk R₁.tower
    let f₂ := R₂.ambientInvariant hk R₂.tower
    IsCanonical R₂.record (R₂.ambientInvariant hk) R₂.tower ∧
    R₁.endpointMap '' D = (geoTransformAlong R₁.record R₁.tower).cosupp ∧
    R₂.endpointMap '' D = (geoTransformAlong R₂.record R₂.tower).cosupp ∧
    (∀ x ∈ D, ∀ y ∈ D, f₁ (R₁.endpointMap x) < f₁ (R₁.endpointMap y) ↔
      f₂ (R₂.endpointMap x) < f₂ (R₂.endpointMap y)) ∧
    let a := fun x : D => f₁ (R₁.endpointMap x.val)
    let b := fun x : D => f₂ (R₂.endpointMap x.val)
    ∃ o : range a ≃o range b, ∀ x, (o ⟨a x,mem_range_self x⟩).val = b x := by
  intro D f₁ f₂
  obtain ⟨hCanIff,hCompare⟩ := cross_ambient_native_comparison_of_class R₁ R₂ hk hClass hDim hExp
  obtain ⟨hImage₁,hImage₂,hOrder,_,_,_⟩ := hCompare hCan
  refine ⟨hCanIff.mp hCan,hImage₁,hImage₂,hOrder,?_⟩
  let a := fun x : D => f₁ (R₁.endpointMap x.val)
  let b := fun x : D => f₂ (R₂.endpointMap x.val)
  have hLt (x y : D) : a x < a y ↔ b x < b y := hOrder x.val x.property y.val y.property
  exact ⟨attainedValueOrderIso a b hLt,attainedValueOrderIso_apply a b hLt⟩


open HironakaG11PresLineState HironakaG1CodimensionTwoChartTransport AnalyticDimensionBasics

/-- On a shared native chart clock, actual same-profile states and their
identical ordered boundary derive the comparison hypotheses at
codimension two. A common real canonical history then gives aligned
supported orders, even for unequal marks. -/
theorem supported_alignment_of_native_states
    {m₁ m₂ k q : ℕ} {A Z : CMfd.{0} k} {C₁ C₂ : MarkedIdeal k A} {S : BlowupTower A Z}
    (R₁ : NativeChartRealization C₁ S m₁ q) (R₂ : NativeChartRealization C₂ S m₂ q)
    (hk : 0 < k) {K : Set A} {H : ℕ → ℕ}
    (h₁ : NativeHSState C₁ K H) (h₂ : NativeHSState C₂ K H)
    (hD₁ : IsInvDomain q C₁) (hD₂ : IsInvDomain q C₂) (hE : C₂.E = C₁.E)
    (hCodim : ∀ x ∈ C₁.cosupp, ∃ p, p + 2 ≤ k ∧ LocDimLE (n := k) K x p)
    (hCan : IsCanonical R₁.record (R₁.ambientInvariant hk) R₁.tower) :
    let D := (geoTransformAlong C₁ S).cosupp
    let f₁ := R₁.ambientInvariant hk R₁.tower
    let f₂ := R₂.ambientInvariant hk R₂.tower
    IsCanonical R₂.record (R₂.ambientInvariant hk) R₂.tower ∧
    (∀ x ∈ D, ∀ y ∈ D, f₁ (R₁.endpointMap x) < f₁ (R₁.endpointMap y) ↔
      f₂ (R₂.endpointMap x) < f₂ (R₂.endpointMap y)) := by
  intro D f₁ f₂
  obtain ⟨hClass,hDim,hExp⟩ := native_codimension_two_zero_normalized h₁ h₂ hD₁ hD₂ hE hCodim
  obtain ⟨hCan₂,_,_,hOrder,_⟩ := supported_alignment_of_shared_native_tower R₁ R₂ hk hClass hDim hExp hCan
  exact ⟨hCan₂,hOrder⟩

end
end Hironaka.HironakaG1RatioGraphEndpointAlignment
