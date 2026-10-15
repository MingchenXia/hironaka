/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalFiniteJetSplitting
import Hironaka.Resolution.HironakaRelativeNormalCoherentSaturation
import Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.HironakaRelativeNormalOriginalFiniteJetGenerators
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaIdealOperations OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalFiniteJetSplitting

/-- Actual original coherence chooses its common functions and entire origin ideal dictionary. -/
theorem exists_original_whole_generator_dictionary {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
      ∃ (μ : Type) (_hμ : Fintype μ) (s : μ → ComplexModel n → ℂ),
        (∀ i, DifferentiableOn ℂ (s i) U) ∧
        (∀ y ∈ U, ∀ f, I.mem y f ↔ InSpanAt s y f) ∧
        ∃ hs0 : ∀ i, HolAt (s i) 0,
          originalCoherentOriginIdeal I = Ideal.span (range fun i => HolGerm.mk (s i) (hs0 i)) := by
  classical
  obtain ⟨U,hU,h0,μ,hμ,s,hs,hsI⟩ := germIdeal_actual_finitely_generated I hI
  let := hμ
  have hs0 : ∀ i, HolAt (s i) 0 := fun i => holAt_of_differentiableOn hU (hs i) h0
  refine ⟨U,hU,h0,μ,hμ,s,hs,hsI,hs0,?_⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨a,ha,hIa,rfl⟩
    exact (inSpanAt_zero_iff_mem_origin_span s hs0 ha).mp ((hsI 0 h0 a).mp hIa)
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    apply Ideal.subset_span
    exact ⟨s i,hs0 i,(hsI 0 h0 _).mpr (inSpanAt_self hs0 i),rfl⟩

def finiteGeneratorColumn (d t q : ℕ) {μ : Type} (G : μ → HolGerm (ComplexModel (d+t)))
    (k : μ × normalExponentIndex t q) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    ambientNormalJet d t q :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  normalMonomialBasis d t q k.2 * Ideal.Quotient.mk (normalIdeal d t ^ q) (G k.1)

theorem finiteGeneratorColumn_mem_original_image (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) {μ : Type} (G : μ → HolGerm (ComplexModel (d+t)))
    (hG : ∀ i, G i ∈ I) (k : μ × normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    finiteGeneratorColumn d t q G k ∈ LinearMap.range (actualIdealJetMap d t I q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  refine ⟨⟨normalExponentMonomial d t k.2.val * G k.1,I.mul_mem_left _ (hG k.1)⟩,?_⟩
  change Ideal.Quotient.mk (normalIdeal d t ^ q) (normalExponentMonomial d t k.2.val * G k.1) = _
  rw [map_mul]
  exact congrArg (· * Ideal.Quotient.mk (normalIdeal d t ^ q) (G k.1))
    (normalMonomialBasis_apply d t q k.2).symm

private theorem original_ideal_image_eq_finite_columns (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) {μ : Type} [Fintype μ]
    (G : μ → HolGerm (ComplexModel (d+t))) (hgen : I = Ideal.span (range G)) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    LinearMap.range (actualIdealJetMap d t I q) =
      Submodule.span (HolGerm (ComplexModel d)) (range (finiteGeneratorColumn d t q G)) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  apply le_antisymm
  · rintro y ⟨a,rfl⟩
    have ha : a.val ∈ Ideal.span (range G) := by rw [← hgen]; exact a.property
    obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
    change Ideal.Quotient.mk (normalIdeal d t ^ q) a.val ∈ _
    rw [← hc,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_mul,← (normalMonomialBasis d t q).sum_repr (Ideal.Quotient.mk (normalIdeal d t ^ q) (c i)),Finset.sum_mul]
    apply Submodule.sum_mem
    intro α _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,α),rfl⟩)
  · apply Submodule.span_le.mpr
    rintro y ⟨k,rfl⟩
    exact finiteGeneratorColumn_mem_original_image d t q I G
      (fun i => by rw [hgen]; exact Ideal.subset_span ⟨i,rfl⟩) k

theorem exists_original_finiteJet_entire_image (d t q : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ (μ : Type) (hμ : Fintype μ) (G : μ → HolGerm (ComplexModel (d+t))),
      let := hμ
      let := tangentAlgebra d t
      let := normalExponentFintype t q
      originalCoherentOriginIdeal I = Ideal.span (range G) ∧
      LinearMap.range (actualIdealJetMap d t (originalCoherentOriginIdeal I) q) =
        Submodule.span (HolGerm (ComplexModel d)) (range (finiteGeneratorColumn d t q G)) ∧
      ∀ y : ambientNormalJet d t q,
        y ∈ LinearMap.range (actualIdealJetMap d t (originalCoherentOriginIdeal I) q) ↔
          ∃ c : μ × normalExponentIndex t q → HolGerm (ComplexModel d),
            ∑ k, c k • finiteGeneratorColumn d t q G k = y := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  obtain ⟨_U,_hU,_h0,μ,hμ,s,_hs,_hsI,hs0,hgen⟩ := exists_original_whole_generator_dictionary I hI
  let := hμ
  let G := fun i => HolGerm.mk (s i) (hs0 i)
  have himage := original_ideal_image_eq_finite_columns d t q (originalCoherentOriginIdeal I) G hgen
  refine ⟨μ,hμ,G,hgen,himage,?_⟩
  intro y
  rw [himage]
  exact Submodule.mem_span_range_iff_exists_fun (HolGerm (ComplexModel d))

theorem exists_original_coherent_finiteJet_generator_dictionary (d t q : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
      ∃ (μ : Type) (hμ : Fintype μ) (s : μ → ComplexModel (d+t) → ℂ),
        let := hμ
        let := tangentAlgebra d t
        let := normalExponentFintype t q
        (∀ i, DifferentiableOn ℂ (s i) U) ∧
        (∀ y ∈ U, ∀ f, I.mem y f ↔ InSpanAt s y f) ∧
        ∃ hs0 : ∀ i, HolAt (s i) 0,
          let G := fun i => HolGerm.mk (s i) (hs0 i)
          originalCoherentOriginIdeal I = Ideal.span (range G) ∧
          (∀ k, finiteGeneratorColumn d t q G k ∈ LinearMap.range
            (actualIdealJetMap d t (originalCoherentOriginIdeal I) q)) ∧
          LinearMap.range (actualIdealJetMap d t (originalCoherentOriginIdeal I) q) =
            Submodule.span (HolGerm (ComplexModel d)) (range (finiteGeneratorColumn d t q G)) ∧
          ∀ y : ambientNormalJet d t q,
            y ∈ LinearMap.range (actualIdealJetMap d t (originalCoherentOriginIdeal I) q) ↔
              ∃ c : μ × normalExponentIndex t q → HolGerm (ComplexModel d),
                ∑ k, c k • finiteGeneratorColumn d t q G k = y := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  obtain ⟨U,hU,h0,μ,hμ,s,hs,hsI,hs0,hgen⟩ := exists_original_whole_generator_dictionary I hI
  let := hμ
  let G := fun i => HolGerm.mk (s i) (hs0 i)
  have himage := original_ideal_image_eq_finite_columns d t q (originalCoherentOriginIdeal I) G hgen
  have hG : ∀ i, G i ∈ originalCoherentOriginIdeal I := by
    intro i
    rw [hgen]
    exact Ideal.subset_span ⟨i,rfl⟩
  refine ⟨U,hU,h0,μ,hμ,s,hs,hsI,hs0,hgen,
    finiteGeneratorColumn_mem_original_image d t q (originalCoherentOriginIdeal I) G hG,himage,?_⟩
  intro y
  rw [himage]
  exact Submodule.mem_span_range_iff_exists_fun (HolGerm (ComplexModel d))

end
end Hironaka.HironakaRelativeNormalOriginalFiniteJetGenerators
