import Hironaka.Resolution.HironakaG1IndependentFiniteNormalNative
import Hironaka.Resolution.HironakaActualIntrinsicIsoCommonGraphSquare
import Hironaka.Resolution.HironakaActualOpenEmbeddingCanonicalExtension

/-! Exact restriction of an actual native source to the original
coordinate windows of an intrinsic common graph. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NativeCoordinateWindow

noncomputable section

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec HironakaG11PresLineState HironakaBaseChange
  HironakaActualOpenEmbeddingCanonicalExtension HironakaActualIntrinsicIsoCommonGraphSquare
  HironakaActualIntrinsicIsoPairedWindows HironakaG1IndependentFiniteNormalNative MaxLocusLocal

variable {n : ℕ} {U A : Opens (ComplexModel n)}

/-- The literal coordinate inclusion is a holomorphic open embedding,
with the inverse of the nested-open chart onto its range. -/
theorem coordinateWindow_isOpenHoloEmbedding (hAU : A ≤ U) :
    IsOpenHoloEmbedding (B := CMfd.of (n := n) A) (A := CMfd.of (n := n) U) n
      (Opens.inclusion hAU) :=
  ⟨nestedOpens U A, (nestedOpensDiffeo (n := n) hAU).symm, fun _ => rfl⟩

/-- The actual carrier restriction is exactly the coordinate-window
carrier used in the intrinsic comparison, including its given embedding. -/
theorem coordinateWindow_preimage (W : Set U) (hAU : A ≤ U) :
    Opens.inclusion hAU ⁻¹' W = coordinateWindowSubset W A := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨Opens.inclusion hAU z, hz, rfl⟩, z.property⟩
  · rintro ⟨⟨x, hx, he⟩, _⟩
    have h : x = Opens.inclusion hAU z := Subtype.ext he
    change Opens.inclusion hAU z ∈ W
    rwa [← h]

/-- Restricting the original record to the actual coordinate window
retains its ordinary domain and native state with the true window cut. -/
theorem nativeHSState_coordinateWindow {W : Set U} {Q : MarkedIdeal n U} {H : ℕ → ℕ}
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H) (hDom : IsInvDomain n Q)
    (hAU : A ≤ U) :
    let R := MarkedIdeal.pullback (Opens.inclusion hAU) Q
    IsInvDomain n R ∧ NativeHSState (X := CMfd.of (n := n) A) R (coordinateWindowSubset W A) H := by
  intro R
  have he := coordinateWindow_isOpenHoloEmbedding hAU
  have hN := nativeHSState_pullback_openEmbedding (Z := CMfd.of (n := n) A)
    hQ (Opens.inclusion hAU) he
  rw [coordinateWindow_preimage W hAU] at hN
  have hD : IsInvDomain n R := isInvDomain_pullback_of_isOpenHoloEmbedding
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) A) (M := Q)
    (Opens.inclusion hAU) he hDom
  exact ⟨hD, hN⟩

end

end Hironaka.HironakaG1NativeCoordinateWindow
