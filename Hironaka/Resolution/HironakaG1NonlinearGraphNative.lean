import Hironaka.Resolution.HironakaG1ProperNormalNativeState
import Hironaka.Resolution.HironakaG1NormalSelectorGraph
import Hironaka.Resolution.HironakaG11PresLineStable

/-! Genuine native records in nonlinear graph charts and their common native class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NonlinearGraphNative
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaActualOpenZeroSectionDifferentials HironakaActualCentreJointJets
  HironakaActualRelativeNormalGeometry HironakaActualZeroCoordinateContactSeed HironakaActualGraphFunctionalIdeal
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualCoherentWeightedCoefficientMarked
  GermIdealPullbackCalculus RestrictedIdealExtension
  HironakaG1ProperNormalNativeState HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1NormalSelectorGraph HironakaG11PresLineState HironakaG11PresLineStable
  HironakaActualPowerBoundaryExponents ResolutionInvariantSpec

variable {n : ℕ}

private abbrev ambient (U : Opens (ComplexModel n)) :=
  CMfd.of (n := n+1) (productOpen U)

/-- The full ambient weighted graph record, retaining its actual ideal, mark
and ordered boundary. The analytic subset tracked by the native state is
the closed selector graph. -/
def selectorAmbientMarked {U : Opens (ComplexModel n)} (f : U → ComplexModel 1)
    (Q : MarkedIdeal n U) (F : List (Set (productOpen U))) :
    MarkedIdeal (n+1) (ambient U) :=
  { selectorMarked f Q F with N := univ }

private theorem selector_coherent {U : Opens (ComplexModel n)} {f : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 1) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (F : List (Set (productOpen U))) :
    (selectorMarked f Q F).ideal.IsCoherent := by
  have hcd : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) ∞
      (fun z : productOpen U => (actualJointNormalProjection n 1 z.val - f (projection U z)) 0) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contMDiff.comp
      (((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val).sub
        (hf.comp (projection_contMDiff U)))
  exact isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hQ)
    (isCoherent_finiteFunctionIdeal _ (fun _ => (hcd.mdifferentiable (by simp)).pow Q.d))

private theorem power_one {U : Opens (ComplexModel n)} (P : MarkedIdeal (n+1) (ambient U))
    (hP : P.ideal.IsCoherent) : powerMarked P 1 = P :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
    (FactorizationFromResolution.idealPow_one_of_isCoherent hP) (Nat.mul_one _)

private theorem selector_zero_ideal {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) :
    (selectorMarked (fun _ : U => (0 : ComplexModel 1)) Q []).ideal = (properNormalMarked Q).ideal := by
  change sumIdeal _ (finiteFunctionIdeal (fun _ : Unit => fun z : productOpen U =>
    (actualJointNormalProjection n 1 z.val - (0 : ComplexModel 1)) 0 ^ Q.d)) =
    sumIdeal _ (finiteFunctionIdeal (fun _ : Unit => fun z : productOpen U =>
      relativeNormalCoordinate U z ^ Q.d))
  congr 2

private theorem pullback_zero_graph {U : Opens (ComplexModel n)} (f : U → ComplexModel 1)
    (W : Set U) :
    graphShift f (fun _ : U => (0 : ComplexModel 1)) ⁻¹' liftedCarrier W = selectorCarrier f W := by
  have h : liftedCarrier W = selectorCarrier (fun _ : U => (0 : ComplexModel 1)) W := rfl
  rw [h, graphShift_preimage_selectorCarrier]

/-- Pullback from the zero graph gives the literal nonlinear graph record,
including every ordered boundary subset and the unchanged mark. -/
theorem pullback_properNormalMarked_graphShift {U : Opens (ComplexModel n)}
    (f : U → ComplexModel 1) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 1) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hN : Q.N = univ) :
    MarkedIdeal.pullback (M := ambient U) (M' := ambient U)
      (graphShift f (fun _ : U => (0 : ComplexModel 1))) (properNormalMarked Q) =
      selectorAmbientMarked f Q [] := by
  have hz : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 1) ∞ (fun _ : U => (0 : ComplexModel 1)) := contMDiff_const
  have hp := pullback_power_selectorMarked hf hz Q hQ [] 1
  simp only [List.map_nil] at hp
  rw [power_one _ (selector_coherent hz Q hQ []), power_one _ (selector_coherent hf Q hQ [])] at hp
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change graphShift f (fun _ : U => (0 : ComplexModel 1)) ⁻¹' (projection U ⁻¹' Q.N) = univ
    rw [hN, preimage_univ, preimage_univ]
  · change (Q.E.map (projection U ⁻¹' ·)).map (graphShift f (fun _ : U => (0 : ComplexModel 1)) ⁻¹' ·) =
      Q.E.map (projection U ⁻¹' ·)
    rw [List.map_map]
    simp only [preimage_preimage, Function.comp_def, projection_graphShift]
  · exact (congrArg (GermIdeal.pullback (m := n+1) (graphShift f (fun _ : U => (0 : ComplexModel 1))))
        (selector_zero_ideal Q).symm).trans (congrArg MarkedIdeal.ideal hp)
  · rfl

private theorem native_replace_boundary {d : ℕ} {X : CMfd.{0} d}
    {Q : MarkedIdeal d X} {W : Set X} {H : ℕ → ℕ}
    (hQ : NativeHSState Q W H) (E : List (Set X)) :
    NativeHSState { Q with E := E } W H := by
  obtain ⟨hH,hW,hN,hI,V,S,k,a,w,hw,hPos,hOwn,hMark,hCut,hUpper,hAt⟩ := hQ
  exact ⟨hH,hW,hN,hI,V,S,k,a,w,hw,hPos,hOwn,hMark,hCut,hUpper,hAt⟩

/-- Native state for the actual nonlinear, closed selector graph. -/
theorem selectorAmbientMarked_native {U : Opens (ComplexModel n)} {W : Set U}
    (f : U → ComplexModel 1) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 1) ∞ f)
    (Q : MarkedIdeal n U) (F : List (Set (productOpen U))) (H : ℕ → ℕ)
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H) (hDomain : IsInvDomain n Q) :
    NativeHSState (X := ambient U) (selectorAmbientMarked f Q F) (selectorCarrier f W) H := by
  let e := graphShiftEquiv f (fun _ : U => (0 : ComplexModel 1)) hf contMDiff_const
  have h := (properNormalMarked_nativeHSState H hQ hDomain).pullback (X' := ambient U) e
  change NativeHSState (X := ambient U) (MarkedIdeal.pullback (M := ambient U) (M' := ambient U)
    (graphShift f (fun _ : U => (0 : ComplexModel 1))) (properNormalMarked Q))
    (graphShift f (fun _ : U => (0 : ComplexModel 1)) ⁻¹' liftedCarrier W) H at h
  rw [pullback_properNormalMarked_graphShift f hf Q hQ.2.2.2.1 hQ.2.2.1, pullback_zero_graph] at h
  exact native_replace_boundary h (F ++ Q.E.map (projection U ⁻¹' ·))

/-- Two independently embedded original native records have the same weak
class in a common actual ambient chart when the transported analytic graph
and the full ordered boundary agree there. Either source mark may differ. -/
theorem locWPEquiv_independent_selectorAmbient
    {U V : Opens (ComplexModel n)} {W : Set U} {D : Set V}
    {Z : CMfd.{0} (n+1)}
    (eU : Z ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)), 𝓘(ℂ,ComplexModel (n+1))⟯ ambient U)
    (eV : Z ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)), 𝓘(ℂ,ComplexModel (n+1))⟯ ambient V)
    (f : U → ComplexModel 1) (g : V → ComplexModel 1)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 1) ∞ g)
    (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (F : List (Set (productOpen U))) (G : List (Set (productOpen V))) (H : ℕ → ℕ)
    (hP : NativeHSState (X := CMfd.of (n := n) U) P W H) (hPD : IsInvDomain n P)
    (hQ : NativeHSState (X := CMfd.of (n := n) V) Q D H) (hQD : IsInvDomain n Q)
    (hGraph : eU ⁻¹' selectorCarrier f W = eV ⁻¹' selectorCarrier g D)
    (hE : (MarkedIdeal.pullback eV (selectorAmbientMarked g Q G)).E =
      (MarkedIdeal.pullback eU (selectorAmbientMarked f P F)).E) :
    HironakaG8LocalHistory.LocWPEquiv
      (MarkedIdeal.pullback eU (selectorAmbientMarked f P F))
      (MarkedIdeal.pullback eV (selectorAmbientMarked g Q G)) := by
  have hPU := (selectorAmbientMarked_native f hf P F H hP hPD).pullback eU
  have hQV := (selectorAmbientMarked_native g hg Q G H hQ hQD).pullback eV
  rw [← hGraph] at hQV
  exact locWPEquiv_native hPU hQV hE

#print axioms selectorAmbientMarked_native
#print axioms locWPEquiv_independent_selectorAmbient

end
end Hironaka.HironakaG1NonlinearGraphNative
