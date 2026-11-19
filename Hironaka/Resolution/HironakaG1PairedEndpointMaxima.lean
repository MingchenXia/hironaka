import Hironaka.Resolution.HironakaG1PairedLiftCompanionValues
import Hironaka.Resolution.HironakaG1NormalCentreTransport

/-! # Exact maximum and canonicality guards on paired realized endpoints -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace

namespace Hironaka.HironakaG1PairedEndpointMaxima
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong NormalCrossings SubmanifoldChartedSpace GeneralValue StepOneRegime HironakaHolomorphicJetChartInvariance
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime CompanionRebase
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualSectionBoundaryDimension HironakaOriginalFamilyDepthStability
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaG1NormalValueMaps
  HironakaG1LiteralRatioPointProfiles HironakaG1NativeOrderDispatcher
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveSuccessorRead
  HironakaG8LocalHistory

open ResolutionDriver HironakaG1NormalCentreTransport HironakaG1PairedLiftCompanionValues

variable {d k₁ k₂ q : ℕ} {X Y : CMfd.{0} d}
  {hk₁ : k₁ ≤ d} {hk₂ : k₂ ≤ d}
  {W₁ W₂ : Set X} {hwc₁ : IsClosed W₁} {hwc₂ : IsClosed W₂}
  {hw₁ : ∀ x ∈ W₁, RegularAtDim (n := d) W₁ x k₁}
  {hw₂ : ∀ x ∈ W₂, RegularAtDim (n := d) W₂ x k₂}
  {V₁ V₂ : Set Y} {hvc₁ : IsClosed V₁} {hvc₂ : IsClosed V₂}
  {hv₁ : ∀ y ∈ V₁, RegularAtDim (n := d) V₁ y k₁}
  {hv₂ : ∀ y ∈ V₂, RegularAtDim (n := d) V₂ y k₂}
  {T : BlowupTower X Y}
  {B₁ : BlowupTower (nativeManifold hk₁ W₁ hw₁) (nativeManifold hk₁ V₁ hv₁)}
  {B₂ : BlowupTower (nativeManifold hk₂ W₂ hw₂) (nativeManifold hk₂ V₂ hv₂)}
  {P Q : MarkedIdeal d X}


set_option maxHeartbeats 2000000 in
/-- Two lifts of one supported marked history, even to different native
dimensions, have equivalent canonicality and identical images of their
maximum loci. The attained values at paired points satisfy the literal
relative recursive dimension shift. -/
theorem paired_same_record_canonical_max_and_values
    (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hk : k₁ ≤ k₂) (hPD : IsInvDomain q P)
    (hP : P.N ⊆ W₁) (hQ : P.N ⊆ W₂)
    (hTr₁ : IsTransverse d W₁ P.E) (hTr₂ : IsTransverse d W₂ P.E)
    (L₁ : Lift hk₁ W₁ hwc₁ hw₁ P.E T V₁ hvc₁ hv₁ B₁)
    (L₂ : Lift hk₂ W₂ hwc₂ hw₂ P.E T V₂ hvc₂ hv₂ B₂) :
    let M := nativePullback hk₁ W₁ hw₁ P
    let N := nativePullback hk₂ W₂ hw₂ P
    let f := (invFamily h₁ q).inv M B₁
    let g := (invFamily h₂ q).inv N B₂
    let C := maxLocus f (geoTransformAlong M B₁).cosupp
    let D := maxLocus g (geoTransformAlong N B₂).cosupp
    (IsCanonical M ((invFamily h₁ q).inv M) B₁ ↔ IsCanonical N ((invFamily h₂ q).inv N) B₂) ∧
    (IsCanonical M ((invFamily h₁ q).inv M) B₁ →
      (Subtype.val : V₁ → Y) '' C = (Subtype.val : V₂ → Y) '' D ∧
      ∀ (x : nativeManifold hk₁ V₁ hv₁) (y : nativeManifold hk₂ V₂ hv₂),
        x.val ∈ (geoTransformAlong P T).cosupp → x.val = y.val →
          g y = sameIndexMap (k₂-k₁) q (f x) ∧ (x ∈ C ↔ y ∈ D)) := by
  intro M N f g C D
  let hd := h₁.trans_le hk₁
  have hCan₁ := Lift.original_same_bound_canonical_iff hd h₁ P hPD hP hTr₁ L₁
  have hCan₂ := Lift.original_same_bound_canonical_iff hd h₂ P hPD hQ hTr₂ L₂
  have hA : IsCanonical M ((invFamily h₁ q).inv M) B₁ ↔
      IsCanonical P ((invFamily hd q).inv P) T := hCan₁
  have hB : IsCanonical P ((invFamily hd q).inv P) T ↔
      IsCanonical N ((invFamily h₂ q).inv N) B₂ := hCan₂.symm
  refine ⟨hA.trans hB, fun h => ?_⟩
  have hAmbient := hA.mp h
  obtain ⟨hPre₁,hIm₁⟩ := Lift.original_same_bound_max_loci hd h₁ P hPD hP hTr₁ L₁ hAmbient
  obtain ⟨hPre₂,hIm₂⟩ := Lift.original_same_bound_max_loci hd h₂ P hPD hQ hTr₂ L₂ hAmbient
  refine ⟨hIm₁.trans hIm₂.symm, fun x y hx hxy => ⟨?_,?_⟩⟩
  · exact paired_lift_value_of_ambient_value h₁ h₂ hk hPD hPD hP hQ hTr₁ hTr₂
      L₁ L₂ hAmbient hAmbient x y hx (hxy ▸ hx)
      (congrArg ((invFamily hd q).inv P T) hxy)
  · rw [show C = _ from hPre₁, show D = _ from hPre₂]
    change x.val ∈ maxLocus ((invFamily hd q).inv P T) (geoTransformAlong P T).cosupp ↔
      y.val ∈ maxLocus ((invFamily hd q).inv P T) (geoTransformAlong P T).cosupp
    rw [hxy]

section ActivePoints
variable {Z A B L R : Type*} [LinearOrder L] [LinearOrder R]
  {i : Z → A} {j : Z → B} {S : Set Z} {D : Set A} {E : Set B}
  (f : A → L) (g : B → R)

/-- For independently presented endpoints covered by the active pairing,
it suffices to test order against one attained maximizer. The guard is
also necessary: the same paired anchor must maximize the other side and
its ties must be precisely the same active points. -/
theorem paired_maximum_anchor_guard
    (hi : i '' S = D) (hj : j '' S = E)
    {z₀ : Z} (hz₀ : z₀ ∈ S) (hm : i z₀ ∈ maxLocus f D) :
    (∀ z ∈ S, i z ∈ maxLocus f D ↔ j z ∈ maxLocus g E) ↔
      (∀ z ∈ S, g (j z) ≤ g (j z₀)) ∧
      (∀ z ∈ S, f (i z) = f (i z₀) ↔ g (j z) = g (j z₀)) := by
  have hiS : ∀ z ∈ S, i z ∈ D := fun z hz => hi ▸ mem_image_of_mem i hz
  have hjS : ∀ z ∈ S, j z ∈ E := fun z hz => hj ▸ mem_image_of_mem j hz
  have hF (z : Z) (hz : z ∈ S) : i z ∈ maxLocus f D ↔ f (i z) = f (i z₀) := by
    constructor
    · intro h
      exact le_antisymm (hm.2 _ (hiS z hz)) (h.2 _ hm.1)
    · intro h
      exact ⟨hiS z hz, fun w hw => h.symm ▸ hm.2 w hw⟩
  have hG (h : ∀ z ∈ S, g (j z) ≤ g (j z₀)) (z : Z) (hz : z ∈ S) :
      j z ∈ maxLocus g E ↔ g (j z) = g (j z₀) := by
    constructor
    · intro hmax
      exact le_antisymm (h z hz) (hmax.2 _ (hjS z₀ hz₀))
    · intro he
      refine ⟨hjS z hz, fun w hw => ?_⟩
      have hw' : w ∈ j '' S := hj.symm ▸ hw
      obtain ⟨w',hw',rfl⟩ := hw'
      exact he.symm ▸ h w' hw'
  constructor
  · intro H
    have hMaxG := (H z₀ hz₀).mp hm
    have h : ∀ z ∈ S, g (j z) ≤ g (j z₀) := fun z hz => hMaxG.2 _ (hjS z hz)
    exact ⟨h,fun z hz => (hF z hz).symm.trans ((H z hz).trans (hG h z hz))⟩
  · rintro ⟨h,he⟩ z hz
    exact (hF z hz).trans ((he z hz).trans (hG h z hz).symm)

/-- The exact guard when the first active endpoint has no attained
maximum, including the case of an empty active domain. -/
theorem paired_maximum_no_anchor_guard
    (hj : j '' S = E) (hNo : maxLocus f D = ∅) :
    (∀ z ∈ S, i z ∈ maxLocus f D ↔ j z ∈ maxLocus g E) ↔
      ∀ z ∈ S, ∃ w ∈ S, g (j z) < g (j w) := by
  have hB : ∀ z ∈ S, j z ∈ E := fun z hz => hj ▸ mem_image_of_mem j hz
  rw [hNo]
  constructor
  · intro h z hz
    by_contra hn
    have hMax : j z ∈ maxLocus g E := by
      refine ⟨hB z hz,fun w hw => ?_⟩
      have hw' : w ∈ j '' S := hj.symm ▸ hw
      obtain ⟨a,ha,rfl⟩ := hw'
      exact le_of_not_gt (fun ht => hn ⟨a,ha,ht⟩)
    exact (h z hz).mpr hMax
  · intro h z hz
    refine iff_of_false (notMem_empty _) ?_
    intro hMax
    obtain ⟨w,hw,ht⟩ := h z hz
    exact not_lt_of_ge (hMax.2 _ (hB w hw)) ht

end ActivePoints

section Extensions

variable {n₁ n₂ : ℕ} {X₁ Y₁ Z₁ : CMfd.{0} n₁} {X₂ Y₂ Z₂ : CMfd.{0} n₂}
  {A B : Type*} [LinearOrder A] [LinearOrder B] {U : Type*}
  {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
  {M₁ : MarkedIdeal n₁ X₁} {M₂ : MarkedIdeal n₂ X₂}
  {f : ∀ {V : CMfd.{0} n₁}, BlowupTower X₁ V → V → A}
  {g : ∀ {V : CMfd.{0} n₂}, BlowupTower X₂ V → V → B}
  {i : U → Y₁} {j : U → Y₂} {S : Set U}

/-- An occupied canonical step on the first history transfers to the
second given genuine corresponding blowups, exactly under the active
anchor guard. The endpoints and invariant types may have different
dimensions and the clocks and marks of their records may be independent. -/
theorem paired_occupied_canonical_extension_guard
    (hi : i '' S = (geoTransformAlong M₁ T₁).cosupp)
    (hj : j '' S = (geoTransformAlong M₂ T₂).cosupp)
    (hInjective : Function.Injective j)
    (D : Set Y₁) (π₁ : Z₁ → Y₁) (hπ₁ : IsBlowupAlong n₁ D π₁)
    (π₂ : Z₂ → Y₂) (hπ₂ : IsBlowupAlong n₂ (j '' (S ∩ i ⁻¹' D)) π₂)
    (hCan₁ : IsCanonical M₁ f (.step T₁ D π₁ hπ₁))
    (hCan₂ : IsCanonical M₂ g T₂)
    (z₀ : U) (hz₀ : z₀ ∈ S) (hD : i z₀ ∈ D) :
    IsCanonical M₂ g (.step T₂ (j '' (S ∩ i ⁻¹' D)) π₂ hπ₂) ↔
      (∀ z ∈ S, g T₂ (j z) ≤ g T₂ (j z₀)) ∧
      (∀ z ∈ S, f T₁ (i z) = f T₁ (i z₀) ↔ g T₂ (j z) = g T₂ (j z₀)) := by
  have hFirst := hCan₁.2.resolve_left (Set.Nonempty.ne_empty ⟨i z₀,hD⟩)
  have hSecond : (j '' (S ∩ i ⁻¹' D)).Nonempty := ⟨j z₀,⟨z₀,⟨hz₀,hD⟩,rfl⟩⟩
  have hAt : i z₀ ∈ maxLocus (f T₁) (geoTransformAlong M₁ T₁).cosupp := hFirst ▸ hD
  refine Iff.trans ?_ (paired_maximum_anchor_guard (f T₁) (g T₂) hi hj hz₀ hAt)
  constructor
  · intro hc z hz
    have hCentre := hc.2.resolve_left hSecond.ne_empty
    rw [← hCentre, ← hFirst]
    constructor
    · intro h
      exact ⟨z,⟨hz,h⟩,rfl⟩
    · rintro ⟨w,⟨_,hw⟩,hEq⟩
      exact (hInjective hEq) ▸ hw
  · intro h
    refine ⟨hCan₂,Or.inr ?_⟩
    ext z
    constructor
    · rintro ⟨w,⟨hw,hwd⟩,rfl⟩
      exact (h w hw).mp (hFirst ▸ hwd)
    · intro hz
      have hz' : z ∈ j '' S := hj.symm ▸ hz.1
      obtain ⟨w,hw,rfl⟩ := hz'
      exact ⟨w,⟨hw,hFirst.symm ▸ (h w hw).mpr hz⟩,rfl⟩

end Extensions
end
end Hironaka.HironakaG1PairedEndpointMaxima
