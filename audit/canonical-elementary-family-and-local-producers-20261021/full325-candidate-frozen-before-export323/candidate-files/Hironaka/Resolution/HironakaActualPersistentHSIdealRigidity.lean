/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHSConstantCentreBennett
import Hironaka.Resolution.HironakaActualWeightedGeneratorTransformJets
/-!
# Whole strict ideals at actual persistent Hilbert--Samuel points

The original germ-ring ideal-rigidity theorem, genuine normalized/geometric
inclusion and actual Bennett sandwich identify the entire ideals at persistent
points. The same chosen target flattening and analytic vertex family then
produce actual strict generators and every literal weighted exceptional jet.
Normal codimension is at least two; no terminating phase is asserted.

Blueprint: `hironaka-actual-persistent-hs-ideal-rigidity-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPersistentHSIdealRigidity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett
  HironakaActualFixedFlatteningHSComparison HironakaSmoothCentreCoherentDomain
  HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientPresentationCentrePower
  HironakaActualNormalBlowupExceptionalLocus HironakaActualAnalyticStrictGenerators
  HironakaActualAnalyticVertexCoefficientData HironakaActualNormalAxisDehomogenization
  HironakaActualTranslatedNormalVertexHS HironakaActualWholeIdealJetDetection
  HironakaActualWeightedGeneratorTransformJets HironakaActualFormalInitialDiagram
  HironakaActualFormalCoordinatePowerDivision HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaActualPointInitialIdealInclusion
  HironakaActualCoefficientAnalyticBlowup

section Model
variable {n : ℕ}

theorem originalVanishingOriginIdeal_eq_of_eventually_eq (A B : Set (ComplexModel n))
    (hAB : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ A ↔ z ∈ B) :
    originalCoherentOriginIdeal (vanishingIdeal (n := n) A) =
      originalCoherentOriginIdeal (vanishingIdeal (n := n) B) := by
  ext g
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
  rw [mk_mem_original_vanishing_origin_ideal_iff,mk_mem_original_vanishing_origin_ideal_iff]
  constructor
  · intro h
    filter_upwards [hAB,h] with z hABz hz hBz
    exact hz (hABz.mpr hBz)
  · intro h
    filter_upwards [hAB,h] with z hABz hz hAz
    exact hz (hABz.mp hAz)

end Model

section FixedSquare
variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

theorem originalFlattenedStrictOriginIdeal_eq_model {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (z : Y) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (j : Fin n) (b : Fin n → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
    (hnormal : ∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
      π y ∈ BlowupFlatCoordinates.flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
        actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b (Θ.toFun (chartAt (ComplexModel n) z y)))
    (W : Set X) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) (strictTransform n π W)) z Θ) 0) =
    originalCoherentOriginIdeal (vanishingIdeal (n := n)
      (strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b)
        (actualFixedFlatteningSet (π z) Φ W))) := by
  rw [originalFlattenedVanishingOriginIdeal_eq_model z Θ hΘsrc hΘ0]
  apply originalVanishingOriginIdeal_eq_of_eventually_eq
  let U : TopologicalSpace.Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
  have h0T : (0 : ComplexModel n) ∈ Θ.target := actualFlattening_target_zero_mem z Θ hΘ0
  have hs := strictTransform_eq_fixedFlattening_preimage hπ z k Φ hΦsrc j b Θ hΘsrc hnormal W
  filter_upwards [Θ.isOpen_target.mem_nhds h0T] with v hv
  change (v ∈ Θ.target ∧ actualFlatteningInverseMap z Θ v ∈ strictTransform n π W) ↔ _
  have he := (Set.ext_iff.mp hs) (⟨v,hv⟩ : U)
  exact (and_iff_right hv).trans he

end FixedSquare

theorem actual_normalized_ideal_eq_geometric_of_persistent_hs (d t : ℕ) (ht : 2 ≤ t)
    (W : Set (ComplexModel (d+t))) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : I=originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
    (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hP : ∀ a, P.generator a ∈ normalIdeal d t^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (j : Fin t) (b : Fin (d+t) → ℂ)
    (hHS : ∀ ℓ : ℕ, hilbertSamuelAt (vanishingIdeal (n := d+t)
        (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ =
      hilbertSamuelValue I ℓ) :
    actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b =
      originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
        (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) := by
  let N := actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b
  let J := originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
    (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W))
  have hinc : N ≤ J := by
    dsimp only [N,J]
    rw [hI]
    exact actual_normal_normalized_ideal_le_geometric_strict_vanishing d t ht j b W
  change N=J
  apply (original_ideal_eq_iff_entire_hs_eq_of_le N J hinc).mpr
  intro ℓ
  have hnorm := hilbertSamuelValue_actual_normal_normalized_le_translated d t I P.generator
    (fun a => Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    P.member hP j b ℓ
  have hb : hilbertSamuelValue N ℓ ≤ hilbertSamuelValue I ℓ :=
    hnorm.trans (hilbertSamuelValue_actualTranslatedNormalVertexIdeal_le d t I P _ ℓ)
  have he : hilbertSamuelValue J ℓ = hilbertSamuelValue I ℓ := by
    simpa only [hilbertSamuelAt_model_zero] using hHS ℓ
  exact le_antisymm (hb.trans_eq he.symm) (hilbertSamuelValue_antitone_original_ideal N J hinc ℓ)

section SuppliedFamily
variable (d t : ℕ) {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]

theorem exists_actual_persistent_fixed_family_strict_jets (ht : 2 ≤ t)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (d+t) C π) (z : Y)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π z) (π z)))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) (π z)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π z))=0)
    (hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel (d+t)) (π z)).source →
      chartAt (ComplexModel (d+t)) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π z) y) ∈ complexCoordinatePlane (d+t) d))
    (W : Set X)
    (P : ActualAnalyticVertexCoefficientData d 0 t
      (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) W) (π z) Φ) 0)))
    (hP : ∀ a, P.generator a ∈ normalIdeal d t^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (hPersist : ∀ ℓ : ℕ,
      hilbertSamuelAt (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n := d+t) W) (π z) ℓ) :
    let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) W) (π z) Φ) 0)
    ∃ (j : Fin t) (b : Fin (d+t) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) z z)),
      Θ.source ⊆ (chartAt (ComplexModel (d+t)) z).target ∧
      Θ.toFun (chartAt (ComplexModel (d+t)) z z)=0 ∧
      (∀ y : Y, y ∈ (chartAt (ComplexModel (d+t)) z).source →
        chartAt (ComplexModel (d+t)) z y ∈ Θ.source →
        π y ∈ BlowupFlatCoordinates.flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π y))=
          actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
            (Θ.toFun (chartAt (ComplexModel (d+t)) z y))) ∧
      let I1 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z Θ) 0)
      ∃ H : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) → HolGerm (ComplexModel (d+t)),
        (∀ a, (coordinateGerm (j.natAdd d))^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val * H a =
          actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (P.generator a)) ∧
        I1=actualAnalyticNormalizedMemberIdeal I0 (actualTangentCentreVariables d t) (j.natAdd d) b ∧
        I1=Ideal.span (range H) ∧
        (∀ a q, Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}) (H a) =
          Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
            (weightedTransformJet d t j b
              (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) ∧
        ∀ q : ℕ,
          Ideal.map (Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})) I1 =
          Ideal.span (range fun a => Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
            (weightedTransformJet d t j b
              (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) := by
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) W) (π z) Φ) 0)
  let A := actualFixedFlatteningSet (π z) Φ W
  obtain ⟨J,b,Θ,hΘsrc,hΘ0,hJd,_hbt,_hbj,hsquare,hI,hHS⟩ :=
    exists_actual_fixed_flattening_blowup_hs_comparisons hπ z d Φ hsrc h0 hflat W
  let j : Fin t := ⟨J.val-d,by have hjlt := J.isLt; omega⟩
  have hJ : j.natAdd d=J := by
    apply Fin.ext
    change d+(J.val-d)=J.val
    omega
  have hsq : ∀ y : Y, y ∈ (chartAt (ComplexModel (d+t)) z).source →
      chartAt (ComplexModel (d+t)) z y ∈ Θ.source →
      π y ∈ BlowupFlatCoordinates.flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π y))=
        actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
          (Θ.toFun (chartAt (ComplexModel (d+t)) z y)) := by
    simpa only [actualTangentCentreVariables_eq_tail,hJ] using hsquare
  have hModelHS : ∀ ℓ : ℕ, hilbertSamuelAt (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) A)) 0 ℓ =
        hilbertSamuelValue I0 ℓ := by
    intro ℓ
    calc
      _ = hilbertSamuelAt (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z ℓ := by
        simpa only [actualTangentCentreVariables_eq_tail,hJ] using ((hHS ℓ).2).symm
      _ = hilbertSamuelAt (vanishingIdeal (n := d+t) W) (π z) ℓ := hPersist ℓ
      _ = hilbertSamuelAt (vanishingIdeal (n := d+t) A) 0 ℓ := (hHS ℓ).1
      _ = hilbertSamuelValue I0 ℓ := by rw [hilbertSamuelAt_model_zero,← hI]
  have hn := actual_normalized_ideal_eq_geometric_of_persistent_hs d t ht A I0 hI P hP j b hModelHS
  have hSource := originalFlattenedStrictOriginIdeal_eq_model hπ.contMDiff z d Φ hsrc J b Θ hΘsrc hΘ0 hsquare W
  have hSourceN : originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z Θ) 0)=
      actualAnalyticNormalizedMemberIdeal I0 (actualTangentCentreVariables d t) (j.natAdd d) b := by
    apply Eq.trans _ hn.symm
    simpa only [actualTangentCentreVariables_eq_tail,hJ] using hSource
  obtain ⟨H,hprod,hspan,hclasses,himages⟩ :=
    exists_actual_weighted_transform_jets_of_vertex_data d t I0 P hP j b
  refine ⟨j,b,Θ,hΘsrc,hΘ0,hsq,H,hprod,hSourceN,hSourceN.trans hspan,hclasses,?_⟩
  intro q
  rw [hSourceN]
  exact himages q

end SuppliedFamily

section OriginalCentre
variable {d t : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]

theorem exists_original_hs_constant_centre_persistent_strict_jets (ht : 2 ≤ t)
    {C W : Set X} {π : Y → X} (hπ : IsBlowupAlong (d+t) C π) (z : Y)
    (hreg : RegularAtDim (n := d+t) C (π z) d)
    (hW : IsComplexAnalyticSubset (n := d+t) W)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ,
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) y ℓ=
        hilbertSamuelAt (vanishingIdeal (n := d+t) W) (π z) ℓ)
    (hPersist : ∀ ℓ : ℕ,
      hilbertSamuelAt (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n := d+t) W) (π z) ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π z) (π z)),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) (π z)).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π z))=0,
      (∀ {y : X}, y ∈ (chartAt (ComplexModel (d+t)) (π z)).source →
        chartAt (ComplexModel (d+t)) (π z) y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π z) y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) W) (π z) Φ) 0)
      ∃ P : ActualAnalyticVertexCoefficientData d 0 t I0,
        (∀ a, P.generator a ∈ normalIdeal d t^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) ∧
        ∃ (j : Fin t) (b : Fin (d+t) → ℂ)
          (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) z z)),
          Θ.source ⊆ (chartAt (ComplexModel (d+t)) z).target ∧
          Θ.toFun (chartAt (ComplexModel (d+t)) z z)=0 ∧
          (∀ y : Y, y ∈ (chartAt (ComplexModel (d+t)) z).source →
            chartAt (ComplexModel (d+t)) z y ∈ Θ.source →
            π y ∈ BlowupFlatCoordinates.flatDomain Φ ∧
            Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π y))=
              actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
                (Θ.toFun (chartAt (ComplexModel (d+t)) z y))) ∧
          let I1 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z Θ) 0)
          ∃ H : actualInitialVertices MonomialOrder.degLex
              (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) → HolGerm (ComplexModel (d+t)),
            (∀ a, (coordinateGerm (j.natAdd d))^
                Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val * H a =
              actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (P.generator a)) ∧
            I1=actualAnalyticNormalizedMemberIdeal I0 (actualTangentCentreVariables d t) (j.natAdd d) b ∧
            I1=Ideal.span (range H) ∧
            (∀ a q, Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}) (H a) =
              Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
                (weightedTransformJet d t j b
                  (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) ∧
            ∀ q : ℕ,
              Ideal.map (Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})) I1 =
              Ideal.span (range fun a => Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
                (weightedTransformJet d t j b
                  (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) := by
  obtain ⟨Φ,hsrc,h0,hflat,P,hP,_hjets⟩ :=
    exists_original_hs_constant_centre_weighted_transform_jets C (π z) hreg
      (vanishingIdeal (n := d+t) W) (CartanIrreducible.cartanCoherence W hW) hhs
  refine ⟨Φ,hsrc,h0,hflat,P,hP,?_⟩
  exact exists_actual_persistent_fixed_family_strict_jets d t ht hπ z Φ hsrc h0 hflat W P hP hPersist

end OriginalCentre

end
end Hironaka.HironakaActualPersistentHSIdealRigidity
