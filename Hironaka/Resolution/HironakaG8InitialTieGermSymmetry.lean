import Hironaka.Resolution.HironakaG8ProperEmbeddedOriginalOverlap
import Hironaka.Resolution.HironakaG8InitialWholeCosupportOrder

/-! Exact equality in the original tie coordinate from marked germ symmetry. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8InitialTieGermSymmetry

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HironakaEmbeddedBoundary HironakaG8ProperEmbeddedOriginalOverlap
  HironakaG3UniverseMonomialVanishing HironakaG8InitialWholeCosupportOrder
  HironakaG8NativePhaseCertificate HironakaEmbeddedAnalytic RestrictEmptyTower
  HironakaHolomorphicJetChartInvariance NonmonomialOrderLocal

/-- A pointed ambient analytic isomorphism identifying the actual reduced
carrier gives an exact equality of original initial values. -/
theorem original_initial_tie_of_pointed_carrier_iso {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hInt : interior W = ∅)
    (U V : Opens X) (x y : X) (hx : x ∈ W) (hy : y ∈ W)
    (hxU : x ∈ U) (hyV : y ∈ V)
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V)
    (hPoint : φ ⟨x, hxU⟩ = (⟨y, hyV⟩ : V))
    (hCarrier : (Subtype.val : U → X) ⁻¹' W = φ ⁻¹' ((Subtype.val : V → X) ⁻¹' W)) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
    (canonicalInvariant n).inv M (.refl : BlowupTower X X) x =
      (canonicalInvariant n).inv M (.refl : BlowupTower X X) y := by
  intro M
  let R := canonicalInvariant n
  have hdom : IsInvDomain n M := isInvDomain_boundary hW hInt NormalCrossings.isSNCDivisor_nil
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let MV := MarkedIdeal.pullback (Subtype.val : V → X) M
  have hU : MU = ⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' W), 1⟩ :=
    pullback_val_mk_vanishingIdeal U [] W
  have hV : MV = ⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : V → X) ⁻¹' W), 1⟩ :=
    pullback_val_mk_vanishingIdeal V [] W
  have hRec : MU = MarkedIdeal.pullback φ MV := by
    rw [hU, hV]
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact preimage_univ.symm
    · rfl
    · change vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' W) =
        GermIdeal.pullback (m := n) φ (vanishingIdeal (n := n) ((Subtype.val : V → X) ⁻¹' W))
      have hWU := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW U
      have hI := CartanIrreducible.cartanCoherence _ hWU
      rw [hCarrier] at hI ⊢
      exact (pullback_vanishingIdeal_diffeo φ ((Subtype.val : V → X) ⁻¹' W) hI).symm
    · rfl
  have hCos : M.cosupp = W := cosupp_mk_vanishingIdeal hW.isClosed []
  have h₁ := R.isInvValue.restrictOpen M hdom U (.refl : BlowupTower X X) trivial ⟨x,hxU⟩ (hCos.symm ▸ hx)
  have h₂ := R.isInvValue.restrictOpen M hdom V (.refl : BlowupTower X X) trivial ⟨y,hyV⟩ (hCos.symm ▸ hy)
  have hDomV := InvDomainTowerAlong.isInvDomain_pullback_val V hdom
  have hCosV : (⟨y,hyV⟩ : V) ∈ MV.cosupp := by
    rw [hV, cosupp_mk_vanishingIdeal (hW.isClosed.preimage continuous_subtype_val) []]
    exact hy
  have h₃ := R.isInvValue.towerIso φ MV hDomV .refl .refl φ IsTowerIso.refl trivial ⟨x,hxU⟩
    (show φ ⟨x,hxU⟩ ∈ MV.cosupp from hPoint.symm ▸ hCosV)
  rw [← hRec, hPoint] at h₃
  exact h₁.symm.trans (h₃.trans h₂)

/-- A retained first centre is original-canonical if its embedded carrier
germs are pointed-isomorphic along the centre and every whole-cosupport
point of its maximal ordinary order is already on the centre. -/
theorem native_first_canonical_of_germ_symmetry_and_top_order {n : ℕ} {X Y Z : CMfd.{0} (n+1)}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W) (hInt : interior W = ∅)
    (H : ℕ → ℕ)
    (D : Set X) (c : X) (hc : c ∈ D) (π : Y → X)
    (hπ : IsBlowupAlong (n+1) D π) (S : BlowupTower Y Z)
    (hPhase : ActualNativePhase W [] H ((BlowupTower.step .refl D π hπ).append S))
    (hUpper : ∀ x ∈ singularSet (n := n+1) W,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) W) x) ≤ toLex H)
    (hGerms : ∀ x ∈ D, ∃ (U V : Opens X) (hxU : x ∈ U) (hcV : c ∈ V)
      (φ : CMfd.of (n := n+1) U ≃ₘ⟮𝓘(ℂ, ComplexModel (n+1)), 𝓘(ℂ, ComplexModel (n+1))⟯
        CMfd.of (n := n+1) V),
      φ ⟨x,hxU⟩ = (⟨c,hcV⟩ : V) ∧
      (Subtype.val : U → X) ⁻¹' W = φ ⁻¹' ((Subtype.val : V → X) ⁻¹' W)) :
    let M : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, 1⟩
    (∀ x ∈ M.cosupp, nmOrd M x = nmOrd M c → x ∈ D) →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (.step .refl D π hπ) := by
  intro M hTop
  have hDLevel : D ⊆ phaseLevel W H :=
    ((centresOver_append_iff _ (.step .refl D π hπ) S).mp hPhase.supports).1.2
  have hDW : D ⊆ W :=
    fun x hx => (mem_singularSet_iff.mp (hPhase.level_subset_singular (hDLevel hx))).1
  apply (native_first_canonical_iff_original_ties W hW hInt H D c hc π hπ S hPhase hUpper).mpr
  refine ⟨?_, fun x hx hxD hEq => (hxD (hTop x hx hEq)).elim⟩
  intro x hx
  obtain ⟨U,V,hxU,hcV,φ,hPoint,hCarrier⟩ := hGerms x hx
  exact original_initial_tie_of_pointed_carrier_iso W hW hInt U V x c
    (hDW hx) (hDW hc) hxU hcV φ hPoint hCarrier


end Hironaka.HironakaG8InitialTieGermSymmetry
