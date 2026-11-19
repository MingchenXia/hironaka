import Hironaka.Resolution.HironakaG1IteratedProperNormalNativeState
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! Comparing independent original native states after actual finite closed padding. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1IndependentFiniteNormalNative
noncomputable section

open BlowupTowers MarkedIdeals MarkedIdealBiholomorphism ResolutionInvariantSpec
  HironakaG1IteratedProperNormalNativeState HironakaG11PresLineState HironakaG11PresLineStable
  HironakaG8LocalHistory HironakaBaseChange HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace

variable {n d : ℕ} {U : Opens (ComplexModel n)}

def normalAmbient (U : Opens (ComplexModel n)) (t : ℕ) (h : n+t = d) : CMfd.{0} d :=
  h ▸ CMfd.of (n := n+t) (iteratedNormalOpen U t)

def normalMarked (Q : MarkedIdeal n U) (t : ℕ) (h : n+t = d) :
    MarkedIdeal d (normalAmbient U t h) := by
  subst d
  exact iteratedNormalMarked Q t

def normalCarrier (W : Set U) (t : ℕ) (h : n+t = d) : Set (normalAmbient U t h) := by
  subst d
  exact iteratedNormalCarrier W t

def normalProjection (U : Opens (ComplexModel n)) (t : ℕ) (h : n+t = d) :
    normalAmbient U t h → U := by
  subst d
  exact iteratedNormalProjection U t

theorem normalMarked_data (Q : MarkedIdeal n U) (t : ℕ) (h : n+t = d) :
    (normalMarked Q t h).d = Q.d ∧
      (normalMarked Q t h).E = Q.E.map (normalProjection U t h ⁻¹' ·) := by
  subst d
  exact iteratedNormalMarked_data Q t

private theorem nativeHSState_normalMarked {W : Set U} {Q : MarkedIdeal n U} {H : ℕ → ℕ}
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H)
    (hQD : IsInvDomain n Q) (t : ℕ) (h : n+t = d) :
    NativeHSState (normalMarked Q t h) (normalCarrier W t h) H := by
  subst d
  exact (iteratedNormalMarked_nativeHSState H hQ hQD t).2

/-- The entire actual padded record transports natively into a genuine
ambient chart, even when its dimension is indexed by a different expression. -/
theorem nativeHSState_onNormalChart {W : Set U} {Q : MarkedIdeal n U} {H : ℕ → ℕ}
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H)
    (hQD : IsInvDomain n Q) (t : ℕ) (h : n+t = d)
    {Z : CMfd.{0} d}
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ normalAmbient U t h) :
    NativeHSState (MarkedIdeal.pullback e (normalMarked Q t h)) (e ⁻¹' normalCarrier W t h) H := by
  exact (nativeHSState_normalMarked hQ hQD t h).pullback e

theorem normalMarked_boundary_on_chart (Q : MarkedIdeal n U) (t : ℕ) (h : n+t = d)
    {Z : CMfd.{0} d} (e : Z → normalAmbient U t h) :
    (MarkedIdeal.pullback e (normalMarked Q t h)).E =
      Q.E.map ((normalProjection U t h ∘ e) ⁻¹' ·) := by
  change (normalMarked Q t h).E.map (e ⁻¹' ·) = _
  rw [(normalMarked_data Q t h).2, List.map_map]
  rfl

/-- Two actual original native states, in possibly unequal ambient dimensions,
retain the same weak class after arbitrary finite closed padding and transport
to a common ambient with the same actual graph and complete ordered boundary. -/
theorem locWPEquiv_independent_finiteNormal
    {m : ℕ} {V : Opens (ComplexModel m)} {W : Set U} {D : Set V}
    (P : MarkedIdeal n U) (Q : MarkedIdeal m V) (H : ℕ → ℕ)
    (hP : NativeHSState (X := CMfd.of (n := n) U) P W H) (hPD : IsInvDomain n P)
    (hQ : NativeHSState (X := CMfd.of (n := m) V) Q D H) (hQD : IsInvDomain m Q)
    (s t : ℕ) (hs : n+s = d) (ht : m+t = d) {Z : CMfd.{0} d}
    (eU : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ normalAmbient U s hs)
    (eV : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ normalAmbient V t ht)
    (hCarrier : eU ⁻¹' normalCarrier W s hs = eV ⁻¹' normalCarrier D t ht)
    (hE : Q.E.map ((normalProjection V t ht ∘ eV) ⁻¹' ·) =
      P.E.map ((normalProjection U s hs ∘ eU) ⁻¹' ·)) :
    LocWPEquiv (MarkedIdeal.pullback eU (normalMarked P s hs))
      (MarkedIdeal.pullback eV (normalMarked Q t ht)) := by
  have h1 := nativeHSState_onNormalChart hP hPD s hs eU
  have h2 := nativeHSState_onNormalChart hQ hQD t ht eV
  rw [← hCarrier] at h2
  apply locWPEquiv_native h1 h2
  simpa only [normalMarked_boundary_on_chart] using hE

/-- Restriction and true biholomorphic transport in one step, including the
whole pulled marked ideal and its entire ordered boundary. -/
theorem nativeHSState_pullback_openEmbedding {X Z : CMfd.{0} d} {Q : MarkedIdeal d X}
    {W : Set X} {H : ℕ → ℕ} (hQ : NativeHSState Q W H)
    (e : Z → X) (he : IsOpenHoloEmbedding d e) :
    NativeHSState (MarkedIdeal.pullback e Q) (e ⁻¹' W) H := by
  obtain ⟨O,b,hb⟩ := he
  have heq : e = Subtype.val ∘ b := funext hb
  have ht := (hQ.restrict O).pullback (X' := Z) b
  have hWhole : MarkedIdeal.pullback e Q =
      MarkedIdeal.pullback b (MarkedIdeal.pullback (Subtype.val : O → X) Q) := by
    rw [heq]
    exact whole_markedPullback_comp contMDiff_subtype_val b.contMDiff Q hQ.2.2.2.1
  rw [hWhole, heq]
  exact ht

/-- Arbitrary finite closed padding and actual open chart restrictions yield
the two native records on the common ambient. The boundary premise is the
equality of the original lists after transporting every subset in order. -/
theorem locWPEquiv_independent_finiteNormal_open
    {m : ℕ} {V : Opens (ComplexModel m)} {W : Set U} {D : Set V}
    (P : MarkedIdeal n U) (Q : MarkedIdeal m V) (H : ℕ → ℕ)
    (hP : NativeHSState (X := CMfd.of (n := n) U) P W H) (hPD : IsInvDomain n P)
    (hQ : NativeHSState (X := CMfd.of (n := m) V) Q D H) (hQD : IsInvDomain m Q)
    (s t : ℕ) (hs : n+s = d) (ht : m+t = d) {Z : CMfd.{0} d}
    (eU : Z → normalAmbient U s hs) (heU : IsOpenHoloEmbedding d eU)
    (eV : Z → normalAmbient V t ht) (heV : IsOpenHoloEmbedding d eV)
    (hCarrier : eU ⁻¹' normalCarrier W s hs = eV ⁻¹' normalCarrier D t ht)
    (hE : Q.E.map ((normalProjection V t ht ∘ eV) ⁻¹' ·) =
      P.E.map ((normalProjection U s hs ∘ eU) ⁻¹' ·)) :
    LocWPEquiv (MarkedIdeal.pullback eU (normalMarked P s hs))
      (MarkedIdeal.pullback eV (normalMarked Q t ht)) := by
  have h1 := nativeHSState_pullback_openEmbedding (nativeHSState_normalMarked hP hPD s hs) eU heU
  have h2 := nativeHSState_pullback_openEmbedding (nativeHSState_normalMarked hQ hQD t ht) eV heV
  rw [← hCarrier] at h2
  apply locWPEquiv_native h1 h2
  simpa only [normalMarked_boundary_on_chart] using hE

#print axioms locWPEquiv_independent_finiteNormal
#print axioms locWPEquiv_independent_finiteNormal_open

end
end Hironaka.HironakaG1IndependentFiniteNormalNative
