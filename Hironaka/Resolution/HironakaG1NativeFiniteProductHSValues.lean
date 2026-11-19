import Hironaka.Resolution.HironakaG1NativeFiniteProductState
import Hironaka.Resolution.HironakaActualReferenceHSSingularCentre

/-! Actual finite-product HS zero/one values and the SAME whole product-point profile.
Blueprint FIRST: hironaka-g1-native-finite-product-hs-values.tex. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NativeFiniteProductHSValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG1NativeFiniteProductState HironakaG11PresLineState HironakaG11PresLineStable
  HironakaActualReferenceHSSingularCentre HironakaHilbertSamuelTangentValue
  HironakaSmoothSubmersionOrder HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedAnalytic GermIdealOrder
open scoped ProductComplexManifold

theorem finiteProductHS_zero (r : ℕ) (H : ℕ→ℕ) : finiteProductHS r H 0=H 0 := by
  induction r with
  | zero=>rfl
  | succ r ih=>simpa only [finiteProductHS,lineHS,Nat.zero_add,Finset.sum_range_one] using ih

theorem finiteProductHS_one (r : ℕ) (H : ℕ→ℕ) :
    finiteProductHS r H 1=H 1+r*H 0 := by
  induction r with
  | zero=>simp only [finiteProductHS,zero_mul,add_zero]
  | succ r ih=>
    change lineHS (finiteProductHS r H) (0+1)=_
    rw [lineHS_succ]
    have hzero : lineHS (finiteProductHS r H) 0=H 0 := by
      simpa only [lineHS,Nat.zero_add,Finset.sum_range_one] using finiteProductHS_zero r H
    rw [hzero,ih,Nat.succ_mul]
    omega

/-- Normalization comes from the ACTUAL singular local ring. -/
theorem singularHS_zero_one {H : ℕ→ℕ} (hH : IsSingularHSValue H) :
    H 0=1 ∧ 1≤H 1 := by
  obtain ⟨m,X,W,a,hW,ha,rfl⟩:=hH
  have haW: a∈W := (mem_singularSet_iff.mp ha).1
  have hz:=BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := m) hW.isClosed
  have hzero:=hilbertSamuelAt_zero_eq_support (vanishingIdeal (n := m) W)
    (CartanIrreducible.cartanCoherence W hW) a
  have hzmem : a∈(vanishingIdeal (n := m) W).zeroLocus := hz.symm ▸ haW
  refine ⟨?_,?_⟩
  · simpa only [if_pos hzmem] using hzero
  · rw [hilbertSamuelAt_vanishing_one_eq_embeddingDimension_add_one hW haW]
    omega

/-- The actual minimal target dimension gives the true product dimension. -/
theorem finiteProductHS_minimal_dimension (r : ℕ) {H : ℕ→ℕ}
    (hH : IsSingularHSValue H) {n : ℕ} (hn : n=H 1-1) :
    n+r=finiteProductHS r H 1-1 := by
  obtain ⟨hzero,hone⟩:=singularHS_zero_one hH
  rw [finiteProductHS_one,hzero,mul_one,hn]
  omega

variable {n : ℕ} {X : CMfd.{0} n} {Q : MarkedIdeal n X}
  {W : Set X} {H : ℕ→ℕ}

/-- Actual fst and the ENTIRE original ideal, at the TRUE original mark. -/
theorem finiteProductRecord_cosupp (r : ℕ) (hState : NativeHSState Q W H) :
    (finiteProductRecord r Q).cosupp=
      (Prod.fst : finiteProductAmbient X r→X) ⁻¹' Q.cosupp := by
  have hf:=HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := r)
    (X := X) (Y := ComplexModel r)
  have hN:=hState.2.2.1
  change cosupport (n+r) (Prod.fst ⁻¹' Q.N)
    (GermIdeal.pullback (m := n+r) Prod.fst Q.ideal) Q.d =
      Prod.fst ⁻¹' cosupport n Q.N Q.ideal Q.d
  rw [hN,preimage_univ]
  exact cosupport_pullback_eq hf hState.2.2.2.1 Q.d

/-- Equality of EVERY genuine HS order at the SAME actual product point. -/
theorem native_product_point_profile (r : ℕ) (hState : NativeHSState Q W H)
    (hE : Q.E=[]) (p : finiteProductAmbient X r) (hp : p.1∈Q.cosupp) :
    hilbertSamuelAt (vanishingIdeal (n := n+r)
      ((Prod.fst : finiteProductAmbient X r→X) ⁻¹' W)) p=finiteProductHS r H := by
  have hProduct:=native_state_finiteProduct r hState hE
  have hpProduct : p∈(finiteProductRecord r Q).cosupp := by
    rw [finiteProductRecord_cosupp r hState]
    exact hp
  exact funext ((Set.ext_iff.mp hProduct.cosupp_eq p).mp hpProduct)

end
end Hironaka.HironakaG1NativeFiniteProductHSValues
