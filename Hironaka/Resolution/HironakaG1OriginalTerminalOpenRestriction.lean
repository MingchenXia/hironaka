import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFunctor
import Hironaka.Resolution.HironakaOriginalTerminalFiniteIdentification
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedGlobalTrace

/-! # Literal open restrictions and compact finite realizations of the original terminal

The actual Cartesian smooth arrow supplies the inverse on the literal open.
Actual compact canonical histories are internally constructed and identified
with that SAME terminal restriction. No native finite-modification predicate
or initial intrinsic resolution assignment is inferred. Blueprint first.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG1OriginalTerminalOpenRestriction

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalFiniteIdentification HironakaEmbeddedResolutionLocal
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionOriginalGlobalMap HironakaSmoothSubmersionOriginalSourceChartMap
  HironakaSmoothSubmersionOrderedGlobalTrace CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- The LITERAL inverse open of the SAME actual original terminal projection. -/
def terminalPreimageOpen (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X) :
    Opens (originalTerminalManifold M hM) :=
  ⟨(originalTerminalGluedProjection M hM) ⁻¹' (U : Set X),
    U.isOpen.preimage (originalTerminalGluedProjection_contMDiff M hM).continuous⟩

/-- The actual HELD Cartesian arrow is biholomorphic onto its literal inverse open. -/
def originalTerminalOpenBiholomorphism (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X) :
    originalTerminalManifold (X := CMfd.of (n := n) U) (markedPullback (m := n) (Subtype.val : U → X) M)
        (original_ambient_domain_pullback (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) (isSubmersion_val U) M hM)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (terminalPreimageOpen M hM U) := by
  let hf := isSubmersion_val U
  let N := markedPullback (m := n) (Subtype.val : U → X) M
  let hN := original_ambient_domain_pullback (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) hf M hM
  let G := originalGlobalSmoothMap (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) hf M hM
  let W := terminalPreimageOpen M hM U
  have hG := originalGlobalSmoothMap_contMDiff (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) hf M hM
  have hp := originalGlobalSmoothMap_proj (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) hf M hM
  have hcart := originalGlobalSmoothMap_cartesian (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) hf M hM
  have hmem (z : originalTerminalManifold (X := CMfd.of (n := n) U) N hN) : G z ∈ W := by
    change originalTerminalGluedProjection M hM (G z) ∈ U
    rw [hp]
    exact (originalTerminalGluedProjection (X := CMfd.of (n := n) U) N hN z).property
  let a : W → U := fun z => ⟨originalTerminalGluedProjection M hM z.val, z.property⟩
  have ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a :=
    BlowupRestrictOpen.contMDiff_opens_mk
      ((originalTerminalGluedProjection_contMDiff M hM).comp contMDiff_subtype_val) (fun z => z.property)
  let hex := (hcart n (CMfd.of (n := n) W) a (Subtype.val : W → originalTerminalManifold M hM)
    ha contMDiff_subtype_val (fun _ => rfl)).exists
  let H := Classical.choose hex
  have hH := Classical.choose_spec hex
  have hleft (z : originalTerminalManifold (X := CMfd.of (n := n) U) N hN) : H ⟨G z, hmem z⟩ = z := by
    apply holomorphicSquarePullback_jointInjective hcart hp
    · apply Subtype.ext
      exact (congrArg Subtype.val (hH.2.1 ⟨G z, hmem z⟩)).trans (hp z)
    · exact hH.2.2 ⟨G z, hmem z⟩
  exact
    { toEquiv := ⟨fun z => ⟨G z, hmem z⟩, H, hleft, fun z => Subtype.ext (hH.2.2 z)⟩
      contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk hG hmem
      contMDiff_invFun := hH.1 }

/-- No different forward comparison was chosen: this is the actual HELD arrow. -/
theorem originalTerminalOpenBiholomorphism_point
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X)
    (z : originalTerminalManifold (X := CMfd.of (n := n) U) (markedPullback (m := n) (Subtype.val : U → X) M)
      (original_ambient_domain_pullback (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) (isSubmersion_val U) M hM)) :
    (originalTerminalOpenBiholomorphism M hM U z).val =
      originalGlobalSmoothMap (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) (isSubmersion_val U) M hM z := rfl

/-- The SAME original base projection, with no replacement of the marked data. -/
theorem originalTerminalOpenBiholomorphism_proj
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X)
    (z : originalTerminalManifold (X := CMfd.of (n := n) U) (markedPullback (m := n) (Subtype.val : U → X) M)
      (original_ambient_domain_pullback (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) (isSubmersion_val U) M hM)) :
    originalTerminalGluedProjection M hM (originalTerminalOpenBiholomorphism M hM U z).val =
      (originalTerminalGluedProjection (X := CMfd.of (n := n) U) (markedPullback (m := n) (Subtype.val : U → X) M)
        (original_ambient_domain_pullback (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) (isSubmersion_val U) M hM) z).val :=
  originalGlobalSmoothMap_proj (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) (isSubmersion_val U) M hM z

/-- Ordinary compact K INTERNALLY produces a finite canonical history on the SAME global inverse open. -/
theorem exists_compact_window_finite_realization (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {K : Set X} (hK : IsCompact K) :
    ∃ (U : Opens X), K ⊆ U ∧ ∃ (D : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) D),
      IsCanonical (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)
        ((canonicalInvariant n).inv (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)) T ∧
      IsGeoResolution (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) T ∧
      ∃ e : D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          CMfd.of (n := n) (terminalPreimageOpen M hM U),
        ∀ z, originalTerminalGluedProjection M hM (e z).val = (T.proj z).val := by
  obtain ⟨U, hKU, D, T, hc, hr⟩ := exists_local_resolution_isCanonical (canonicalInvariant n) hM hK
  let N := markedPullback (m := n) (Subtype.val : U → X) M
  let hN := original_ambient_domain_pullback (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X)) (isSubmersion_val U) M hM
  let η := originalTerminalFiniteBiholomorphism N hN T hc hr
  let e := η.symm.trans (originalTerminalOpenBiholomorphism M hM U)
  refine ⟨U, hKU, D, T, hc, hr, e, ?_⟩
  intro z
  have hη := originalTerminalFiniteBiholomorphism_proj N hN T hc hr (η.symm z)
  rw [η.apply_symm_apply] at hη
  exact (originalTerminalOpenBiholomorphism_proj M hM U (η.symm z)).trans
    (congrArg Subtype.val hη.symm)

end
end Hironaka.HironakaG1OriginalTerminalOpenRestriction
