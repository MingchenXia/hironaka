import Hironaka.Geometry.CurveFibrationBaseChangeSections

/-!
# Actual4.16 section production with every original4.15 property retained

One internally constructed finite normal projective base alteration gives
closed sections of the SAME literal whole reduction. Every fibration and
boundary property is proved for this very same object and its projections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S : Scheme.{u}}

/-- Source4.16: construct sections on the SAME whole model while retaining ALL original4.15 data. -/
theorem exists_wholeReduction_with_boundary_and_sections [IsIntegral X] [IsIntegral S]
    (p : S ⟶ Spec (.of k)) (hpS : IsProjectiveOver p)
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (hpX : IsProjectiveOver (f ≫ p))
    [GeometricallyConnected f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hsm : ∀ s : S, Dense ((f.fiberι s) ⁻¹' (f.smoothLocus : Set X)))
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤)
    [IsFinite (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f)]
    (hDGE : IsGenericallyEtale (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f))
    (hthree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback f a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst f a (v i) ∈ f.smoothLocus ∧
          pullback.fst f a (v i) ∈ D.support) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (hg : IsAlteration g)
      (κ : Type u) (_ : Finite κ) (σ : κ → (Y ⟶ reducedPullback f g))
      (n : ℕ) (e : Y ⟶ relativeSpace S n) (_ : IsClosedImmersion e)
      (heq : e ≫ relativeStructure S n = g),
      IsFinite g ∧ IsGenericallyEtale g ∧ IsNormalScheme Y ∧
      letI : IsProper p := hpS.isProper
      letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
      letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
      letI : IsIntegral Y := hg.sourceIntegral
      let q := reductionι f g ≫ pullback.snd f g
      let φ := reductionι f g ≫ pullback.fst f g
      let E := D.comap φ
      ((IsIntegral (reducedPullback f g) ∧
      IsVariety (q ≫ g ≫ p) ∧ IsProjectiveOver (q ≫ g ≫ p) ∧
      IsVariety (g ≫ p) ∧ IsProjectiveOver (g ≫ p) ∧
      IsAlteration φ ∧ IsGenericallyEtale φ ∧ GeometricallyConnected q ∧
      (∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y)
        (C : Set (pullback q a : Scheme.{u})),
        C ∈ irreducibleComponents (pullback q a : Scheme.{u}) → topologicalKrullDim C = 1) ∧
      (∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y),
        Dense ((pullback.fst q a) ⁻¹' (q.smoothLocus : Set (reducedPullback f g)))) ∧
      Smooth (q.fiberToSpecResidueField (genericPoint Y)) ∧ IsProper q ∧
      (∃ (m : ℕ) (j : reducedPullback f g ⟶ relativeSpace Y m),
        IsClosedImmersion j ∧ j ≫ relativeStructure Y m = q) ∧
      IsClosedImmersion (reductionProjectiveEmbedding f g e heq) ∧
      reductionProjectiveEmbedding f g e heq ≫ relativeStructure X n = φ ∧
      φ ≫ f = q ≫ g) ∧
      IsEffectiveCartierDivisor E ∧ E.support ≠ ⊤ ∧
      E.support = D.support.preimage φ.continuous ∧
      IsReduced E.radical.subscheme ∧ E.radical.support = D.support.preimage φ.continuous ∧
      IsFinite (CartierBoundaryDominance.reducedBoundaryInclusion E ≫ q) ∧
      IsGenericallyEtale (CartierBoundaryDominance.reducedBoundaryInclusion E ≫ q) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Y)
        (C : Set (pullback q a : Scheme.{u})),
        C ∈ irreducibleComponents (pullback q a : Scheme.{u}) →
        ∃ v : Fin 3 → (pullback q a : Scheme.{u}), Function.Injective v ∧ ∀ i,
          v i ∈ C ∧ pullback.fst q a (v i) ∈ q.smoothLocus ∧
            pullback.fst q a (v i) ∈ E.support)) ∧
        (∀ a, σ a ≫ q = 𝟙 Y ∧ IsClosedImmersion (σ a)) ∧
        ⋃ a, Set.range (σ a) = (E.support : Set (reducedPullback f g)) := by
  let : IsProper p := hpS.isProper
  let : IsProper (f ≫ p) := hpX.isProper
  let : IsProper f := IsProper.of_comp f p
  let : IsVariety p := .mk
  let : IsVariety (f ≫ p) := .mk
  obtain ⟨Y, g, κ, hκ, σ, hfin, halt, hget, hN, hvar, hproj, _hT, hσ, hcover⟩ :=
    exists_wholeReduction_boundary_sections p hpS f hsm hd D hD hDGE
  let : IsAlteration g := halt
  let : IsFinite g := hfin
  obtain ⟨n, e, he, heq⟩ := exists_relativeEmbedding_of_isProjective p g hproj
  let := he
  have hdata := wholeReduction_with_boundary_of_native_fibre_density p hpS f hpX
    hsm hd D hD hproper hDGE hthree g hget e heq
  exact ⟨Y, g, halt, κ, hκ, σ, n, e, he, heq, hfin, hget, hN, hdata, hσ, hcover⟩

end Hironaka.Geometry.CurveFibrationBaseChange
