import Hironaka.Resolution.HironakaCompactFootprintOpenTowerExtension
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixTests

set_option autoImplicit false

/-! Genuine original marked tests on the SAME compact-footprint extension.
The existing dimension-general open-cover descent engine is reused.
Blueprint: hironaka-compact-footprint-joint-tests.tex. -/

open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaCompactFootprintJointTests

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen GermIdealPullbackCalculus

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual tower transport over the original open and the genuinely empty
restriction away from the original support derive the ENTIRE original test. -/
theorem isGeoTestTower_of_supported_open_iso (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (Q : BlowupTower X Y) (hQ : CentresOver K Q)
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T) :
    IsGeoTestTower M Q := by
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : U → X) M).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hIU : (MarkedIdeal.pullback (Subtype.val : U → X) M).ideal.IsCoherent :=
    isCoherent_pullback contMDiff_subtype_val hI
  have hU : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U Q) := by
    apply (IsTowerIso.isGeoTestTower_iff
      (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) U)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) M)
      (T' := T) (T := restrict U Q) (χ := e)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) hNU hIU he).mp
    change IsGeoTestTower (MarkedIdeal.pullback (id : U → U)
      (MarkedIdeal.pullback (Subtype.val : U → X) M)) T
    rw [ContactCanonicalAlong.pullback_id _ hIU]
    exact hT
  let V : Opens X := ⟨Kᶜ, hK.isOpen_compl⟩
  have hVK : Disjoint (V : Set X) K := Set.disjoint_left.mpr (fun _ hv hk => hv hk)
  have hV : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V Q) :=
    ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower _ _
      (isEmptyTower_restrict_of_centresOver V hVK Q hQ)
  let cover : ULift.{u} Bool → Opens X := fun b => if b.down then U else V
  apply HironakaSharpActualCurveGlobalPrefixTests.isGeoTestTower_of_open_cover
    M hN hI cover (fun x => ?_) Q (fun b => ?_)
  · by_cases hx : x ∈ K
    · exact ⟨ULift.up true, hKU hx⟩
    · exact ⟨ULift.up false, hx⟩
  · rcases b with ⟨b⟩
    cases b
    · exact hV
    · exact hU

/-- One prescribed actual source-open history internally gives ONE original
ambient extension retaining BOTH independent original marked tests. -/
theorem exists_joint_test_extension (A B : MarkedIdeal n X)
    (hNA : IsClosedSubmanifold n A.N) (hIA : A.ideal.IsCoherent)
    (hNB : IsClosedSubmanifold n B.N) (hIB : B.ideal.IsCoherent)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : CentresOver ((Subtype.val : U → X) ⁻¹' K) T)
    (hTA : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) A) T)
    (hTB : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) B) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
      IsGeoTestTower A Q ∧ IsGeoTestTower B Q ∧ CentresOver K Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val := by
  obtain ⟨Y, Q, hQ, e, he, hLength, hProj⟩ :=
    HironakaCompactFootprintOpenTowerExtension.exists_compact_footprint_extension U K hK hKU T hT
  exact ⟨Y, Q,
    isGeoTestTower_of_supported_open_iso A hNA hIA U K hK.isClosed hKU Q hQ T e he hTA,
    isGeoTestTower_of_supported_open_iso B hNB hIB U K hK.isClosed hKU Q hQ T e he hTB,
    hQ, e, he, hLength, hProj⟩

end
end Hironaka.HironakaCompactFootprintJointTests
