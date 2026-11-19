import Hironaka.Resolution.HironakaActualNativeInvariantDomain

/-! The actual zero-native-dimensional branch uses empty cosupport and
empty SAME history centres. It never instantiates invFamily with 0<0. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeZeroDimensionalHistory
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec ResolutionInvariantExt NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionOrderHistory HironakaActualNativeHistoryExistence
  RelativePrincipalizationSpan

/-- The ORIGINAL carrier dimension is forced to zero by actual native support;
source domain-zero and native positivity are not assumed. -/
theorem isInvDomain_zero_of_native_support {n r : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : ∀x∈W,RegularAtDim (n:=n) W x 0)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W) : IsInvDomain 0 M := by
  let hk : 0≤n:=Nat.zero_le n
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let A : Set W:=(Subtype.val : W→X) ⁻¹' M.N
  have hImage : (Subtype.val : W→X) '' A=M.N:=by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hx;exact ⟨⟨x,hMN hx⟩,hx,rfl⟩
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,_hjr,hj⟩:=hM.dimLE x hx
  let p : W:=⟨x,hMN hx⟩
  have hReg:=regularAtDim_native_image_iff hk hW A p j
  rw [hImage] at hReg
  have hjNative : RegularAtDim (n:=0) A p j:=hReg.mp hj
  have hj0 : j=0:=Nat.eq_zero_of_le_zero hjNative.1
  exact ⟨0,le_rfl,hj0 ▸ hj⟩

private theorem empty_of_zero_domain_test {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain 0 M) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower M T → IsEmptyTower T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hT => by
      obtain ⟨hPrefix,hC⟩:=(isGeoTestTower_step_iff M T C π hπ).mp hT
      have hEmpty:=cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T hPrefix
      refine ⟨empty_of_zero_domain_test M hM T hPrefix,?_⟩
      exact eq_empty_of_subset_empty (hC.2.1.trans hEmpty.subset)

/-- EVERY actual original TEST on the derived zero-dimensional support has
empty centres and empty current cosupport, retaining every chronological step. -/
theorem original_zero_support_test_resolution {n r : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : ∀x∈W,RegularAtDim (n:=n) W x 0)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower M T) :
    IsEmptyTower T ∧ IsGeoResolution M T := by
  have hM0:=isInvDomain_zero_of_native_support hW M hM hMN
  exact ⟨empty_of_zero_domain_test M hM0 T hT,
    hT,cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM0 T hT⟩

/-- Ambient and native centres are empty on EXACTLY the SAME geometry Lift. -/
theorem Lift.isEmptyTower_iff {n k : ℕ} {X : CMfd.{0} n} {hk : k≤n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    {E : List (Set X)} {Y : CMfd.{0} n} {T : BlowupTower X Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q) : IsEmptyTower T ↔ IsEmptyTower Q := by
  induction h with
  | refl => exact Iff.rfl
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    change (IsEmptyTower T ∧ (Subtype.val : V→Y) '' D=∅) ↔ (IsEmptyTower Q ∧ D=∅)
    exact and_congr ih image_eq_empty

/-- The zero-dimensional native branch constructs SAME actual empty-centre
resolution histories. Native invFamily, Lift, TEST and empty-centre outputs
are never inputs, and every prescribed ambient π is retained. -/
theorem exists_zero_native_resolution_history {n r : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x 0)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    ∃(V : Set Y)(hVc : IsClosed V)(hV : ∀y∈V,RegularAtDim (n:=n) V y 0)
      (Q : BlowupTower (nativeManifold (Nat.zero_le n) W hW) (nativeManifold (Nat.zero_le n) V hV)),
      Lift (Nat.zero_le n) W hWc hW M.E T V hVc hV Q ∧ IsEmptyTower T ∧ IsEmptyTower Q ∧
      IsGeoResolution M T ∧ IsGeoResolution (nativePullback (Nat.zero_le n) W hW M) Q := by
  obtain ⟨hEmptyAmbient,hAmbientResolution⟩:=original_zero_support_test_resolution hW M hM hMN T hT
  have hAmbientCos:=hAmbientResolution.2
  obtain ⟨V,hVc,hV,Q,hLift,hNativeTest⟩:=exists_native_history_of_original_test hn
    (Nat.zero_le n) W hWc hW M hM hMN hTrans T hT
  have hEmptyNative:=(HironakaActualNativeZeroDimensionalHistory.Lift.isEmptyTower_iff hLift).mp hEmptyAmbient
  have hNativeCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift hn hM.isWellFormed.isSNCDivisor hTrans M rfl hMN
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)
  rw [hAmbientCos,preimage_empty] at hNativeCos
  exact ⟨V,hVc,hV,Q,hLift,hEmptyAmbient,hEmptyNative,⟨hT,hAmbientCos⟩,⟨hNativeTest,hNativeCos⟩⟩

end
end Hironaka.HironakaActualNativeZeroDimensionalHistory
