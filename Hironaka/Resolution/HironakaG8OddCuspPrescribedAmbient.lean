import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial
import Hironaka.Resolution.HironakaG8OddCuspPrescribedNative
import Hironaka.Resolution.HironakaG11PresLineStable

/-! The polynomial cusp state on a single physical ambient open. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8OddCuspPrescribedAmbient
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdealBiholomorphism ResolutionInvariantSpec
  HironakaBaseChange HironakaG8OpenHoloEmbeddingComposition
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG8LocalHistory
  HironakaActualWeightedNormalPadding HironakaActualWeightedCoefficientCompression
  HironakaActualCoherentWeightedCoefficientMarked HironakaRelativeNormalMonomialBasis
  HironakaG8OddCuspPrescribedFamily HironakaG8OddCuspPrescribedNative
  HironakaG8OddCuspVanishingStalk HironakaHolomorphicJetChartInvariance
  HironakaActualVanishingIntrinsicHSTransport

private theorem polynomialCuspRecord_pullback
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 3) X] [IsComplexManifold 3 X]
    [ChartedSpace (ComplexModel 3) Y] [IsComplexManifold 3 Y]
    (p : ℕ) (g : X → ComplexModel 3) (f : Y → X)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 3) ∞ g)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 3) ∞ f) :
    MarkedIdeal.pullback f (polynomialCuspRecord p g) =
      polynomialCuspRecord p (g ∘ f) := by
  let μ := fun a : cuspV p => normalExponentDegree a.val
  let c := fun (a : cuspV p) (z : X) =>
    cuspRepresentative p a (g z) ^ (weightedCommonMark μ / μ a)
  have hc (a : cuspV p) : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ) (c a) :=
    ((cuspRepresentative_differentiable p a).mdifferentiable.comp
      (hg.mdifferentiable (by simp))).pow _
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
    (finiteFunctionIdeal_pullback c hc f hf) rfl

/-- Genuine history on the literal ambient open rather than an abstract
chart or a chosen equivalent native representative. -/
theorem exists_prescribed_polynomial_cusp_on_ambient_open (p : ℕ) (hp : Odd p) (hp2 : 2 < p)
    (B : Opens (ComplexModel 3)) (hB : (0 : ComplexModel 3) ∈ B) :
    ∃ (D : Opens (ComplexModel 3)) (hD : (0 : ComplexModel 3) ∈ D), D ≤ B ∧
      let Q := polynomialCuspRecord p (Subtype.val : D → ComplexModel 3)
      IsInvDomain 3 Q ∧ NativeHSState (X := CMfd.of (n := 3) D) Q
        ((Subtype.val : D → ComplexModel 3) ⁻¹' embeddedCuspSet p)
        (hilbertSamuelAt (vanishingIdeal (n := 3) (embeddedCuspSet p)) 0) ∧
      (⟨0,hD⟩ : D) ∈ Q.cosupp := by
  obtain ⟨U,O,x,hx,hInside,hDom,hState,_hCos⟩ := exists_prescribed_polynomial_cusp_native p hp hp2 B hB
  let f : O → ComplexModel 3 := fun z => z.val.val
  obtain ⟨D,e,he⟩ := isOpenHoloEmbedding_comp
    (A := CMfd.of (n := 3) (ComplexModel 3)) (B := CMfd.of (n := 3) U)
    (C := CMfd.of (n := 3) O) (isOpenHoloEmbedding_val U) (isOpenHoloEmbedding_val O)
  have he' (z : O) : f z = (e z : ComplexModel 3) := he z
  have hD : (0 : ComplexModel 3) ∈ D := by
    rw [← hx]
    change f x ∈ D
    rw [he' x]
    exact (e x).property
  refine ⟨D,hD, ?_,?_⟩
  · intro z hz
    let y := e.symm ⟨z,hz⟩
    have hfy : f y = z := by rw [he',e.apply_symm_apply]
    rw [← hfy]
    exact hInside y
  let Q := polynomialCuspRecord p (Subtype.val : D → ComplexModel 3)
  have hf : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 3) ∞ f :=
    (contMDiff_subtype_val (U := U)).comp (contMDiff_subtype_val (U := O))
  have hBack : MarkedIdeal.pullback e.symm (polynomialCuspRecord p f) = Q := by
    rw [polynomialCuspRecord_pullback p f e.symm hf e.symm.contMDiff]
    congr 1
    funext z
    exact (he' (e.symm z)).trans (congrArg Subtype.val (e.apply_symm_apply z))
  have hSet : e.symm ⁻¹' (f ⁻¹' embeddedCuspSet p) =
      (Subtype.val : D → ComplexModel 3) ⁻¹' embeddedCuspSet p := by
    ext z
    change f (e.symm z) ∈ embeddedCuspSet p ↔ z.val ∈ embeddedCuspSet p
    rw [he',e.apply_symm_apply]
  have hDom' := InvDomainTowerAlong.isInvDomain_pullback e.symm hDom
  rw [hBack] at hDom'
  have hState' := NativeHSState.pullback (X' := CMfd.of (n := 3) D) e.symm hState
  rw [hBack,hSet] at hState'
  refine ⟨hDom',hState',?_⟩
  change (⟨0,hD⟩ : D) ∈ Q.cosupp
  rw [hState'.cosupp_eq]
  intro l
  exact hilbertSamuelAt_vanishing_actual_open_any D (embeddedCuspSet p) ⟨0,hD⟩ l


open CanonicalCentres HironakaG11InvBMClass HironakaG1OriginalInvariantClassFunctorial

/-- Any native provider for the same geometric cusp on the same open has
the polynomial record's actual initial value whenever its mark is two. -/
theorem native_cusp_initial_value_eq_polynomial
    {X : CMfd.{0} 3} (p : ℕ) (f : X → ComplexModel 3)
    (Q : MarkedIdeal 3 X) (hDom : IsInvDomain 3 Q) (hMark : Q.d = 2) (hE : Q.E = [])
    (hPoly : IsInvDomain 3 (polynomialCuspRecord p f))
    (hQ : NativeHSState Q (f ⁻¹' embeddedCuspSet p)
      (hilbertSamuelAt (vanishingIdeal (n := 3) (embeddedCuspSet p)) 0))
    (hP : NativeHSState (polynomialCuspRecord p f) (f ⁻¹' embeddedCuspSet p)
      (hilbertSamuelAt (vanishingIdeal (n := 3) (embeddedCuspSet p)) 0))
    (x : X) (hx : x ∈ Q.cosupp) :
    (canonicalInvariant 3).inv Q (.refl : BlowupTower X X) x =
      (canonicalInvariant 3).inv (polynomialCuspRecord p f) (.refl : BlowupTower X X) x := by
  let P := polynomialCuspRecord p f
  have hEq : LocWPEquiv Q P := locWPEquiv_native hQ hP hE.symm
  have hN : Q.N = P.N := hQ.2.2.1
  exact (classFunctorialFor_canonicalInvariant 3).inv_eq Q P hDom hPoly hEq hMark hE
    (SameCarrierDim.of_N_eq hN) (expAgree_of_nil hE) .refl trivial x hx

end
end Hironaka.HironakaG8OddCuspPrescribedAmbient
