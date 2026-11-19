import Hironaka.Resolution.HironakaActualGlobalTopOrderBlock

/-! Exact SAME-original chronological product order outside the actual
original centre footprint. Global canonicality and current restarts are
absent. This is a genuine off-centre induction on the actual source tower. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalOrderOffFootprint
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open RelativePrincipalizationSpan RestrictedIdealExtension NormalCrossings
open NonmonomialOrderLocal NonmonomialOrderCanonical InvDomainTowerAlong
open HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
open HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteChronologicalHistory
open HironakaSharpActualOriginalDynamicStep HironakaSharpActualDynamicDistinctCentre
open HironakaSharpActualFiniteMemberProduct RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n k : ℕ} {X : CMfd.{u} n}

/-- Exact initial order off an ORIGINAL footprint containing every actual
centre, without source canonicality. Empty steps are retained. -/
theorem nmOrd_eq_initial_off_footprint
 (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain k M) (D : Set X) :
 ∀{Y : CMfd.{u} n}(S : BlowupTower X Y),IsGeoTestTower M S → CentresOver D S →
 ∀y : Y,S.proj y∉D → nmOrd (geoTransformAlong M S) y=nmOrd M (S.proj y)
 | _,.refl,_hS,_hOver,y,_hy => rfl
 | _,.step S C π hπ,hS,hOver,y,hy => by
   have hyC : π y∉C := fun hc => hy (hOver.2 hc)
   have hCur := isInvDomain_geoTransformAlong hM S hS.1
   exact (nmOrd_geoTransform_of_notMem hn hCur hS.2 hπ hyC).trans
     (nmOrd_eq_initial_off_footprint hn M hM D S hS.1 hOver.1 (π y) hy)

/-- The actual chronological ORIGINAL member product has exactly its
original initial ordinary order off the true original centre footprint. -/
theorem original_product_order_eq_initial_off_footprint
 (hn : 0<n) {W : Set X} {E : List (Set X)}
 (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
 (hdense : W⊆closure (W \ ⋃H∈E,H)) {q : ℕ} (hq : 1≤q)
 (D : Set X) {Y : CMfd.{u} n} (S : BlowupTower X Y)
 (hS : IsGeoTestTower (originalMemberProductMarked W E q) S)
 (hGeom : IsGeoTestTower (geometricTemplate W []) S) (hOver : CentresOver D S)
 (y : Y) (hy : S.proj y∉D) :
 ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) S).N
   (chronologicalMemberProduct W E S) y=
   ordinaryTraceOrder W (originalMemberProduct E) (S.proj y) := by
 have hM : IsInvDomain (n+1) (originalMemberProductMarked W E q) :=
   ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
       isTransverse_nil_of_isClosedSubmanifold hW⟩,
     (by intro x hx;obtain ⟨j,hj⟩ := hW.2 x hx;exact ⟨j,hj.1.trans (Nat.le_succ n),hj⟩),
     hq,(fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx)⟩
 have hCurrent := (original_product_nmOrd_eq_current hn hW hE hdense q S hS y).trans
   (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense S hGeom y)
 have hInitial := nmOrd_eq_initial_off_footprint hn _ hM D S hS hOver y hy
 exact hCurrent.symm.trans hInitial

end
end Hironaka.HironakaActualOriginalOrderOffFootprint
