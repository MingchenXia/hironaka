/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualControlledAccumulatedResidual

/-! Genuine common-coordinate products of actual relative monomial factors.
This supplies true factor algebra for composite raw TOTAL transport, not a
certificate of its endpoint or of original modified-history decrease. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualRelativeMonomialProduct
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
  MonomialCaseAlong NonmonomialStepAlong BlowupFlatCoordinates
variable {n : ℕ} {X : CMfd.{u} n}

/-- Real SAME adapted coordinates and actual factor exponents construct true
principal-monomial product geometry before any product-monomial conclusion. -/
theorem actual_monomial_product_principal_at (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ x ∈ N,IsNonzeroAlongAt N I x) (hj : ∀ x ∈ N,IsNonzeroAlongAt N J x)
    (hmI : IsMonomialAlong n N I E) (hmJ : IsMonomialAlong n N J E)
    {x : X} (hx : x ∈ N) : IsPrincipalMonomialAlongAt n N (I.mul J) E x := by
  obtain ⟨_kC,kN,Φ,σ,hsrc,hσk,hinj,hflat⟩ :=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hT hT.hasNormalCrossings hx
  have hNflat : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kN) :=
    fun hy1 hy2 => (hflat hy1 hy2).2.1
  have hA : ∀ i,x ∈ E.get i → ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0) :=
    fun i hi _ hy1 hy2 => (hflat hy1 hy2).2.2 i hi
  have hgenI := isInSpanOnAt_iff_generator_of_isMonomialAlong hsrc hNflat hA hn hN hE hT hI hi hmI hx hσk hinj
  have hgenJ := isInSpanOnAt_iff_generator_of_isMonomialAlong hsrc hNflat hA hn hN hE hT hJ hj hmJ hx hσk hinj
  let eI : Fin E.length → ℕ := fun i => divExpAlong n N I (E.get i) x
  let eJ : Fin E.length → ℕ := fun i => divExpAlong n N J (E.get i) x
  let F : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i
  have hmul : (fun y => (∏ i ∈ F,flatCoord Φ (σ i) y^eI i)*(∏ i ∈ F,flatCoord Φ (σ i) y^eJ i))=
      fun y => ∏ i ∈ F,flatCoord Φ (σ i) y^(eI i+eJ i) := by
    funext y
    simp_rw [pow_add]
    exact (Finset.prod_mul_distrib).symm
  refine ⟨kN,Φ,σ,(fun i => eI i+eJ i),hsrc,hNflat,hσk,hinj,hA,?_⟩
  intro g
  have hh := isInSpanOnAt_mul_iff_of_generators
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) hgenI hgenJ g
  change IsInSpanOnAt (n := n) N ((I.mul J).mem x) x g ↔
    IsInSpanOnAt (n := n) N (·=fun y => ∏ i ∈ F,flatCoord Φ (σ i) y^(eI i+eJ i)) x g
  rw [← hmul]
  exact hh

/-- Actual coherence and constructed local geometry supply TRUE nonzero and
monomial product on the same carrier and ENTIRE boundary. -/
theorem actual_relative_monomial_product_geometry (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ x ∈ N,IsNonzeroAlongAt N I x) (hj : ∀ x ∈ N,IsNonzeroAlongAt N J x)
    (hmI : IsMonomialAlong n N I E) (hmJ : IsMonomialAlong n N J E) :
    (I.mul J).IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N (I.mul J) x) ∧ IsMonomialAlong n N (I.mul J) E := by
  have hc := isCoherent_mul hI hJ
  exact ⟨hc,isNonzeroAlongAt_and_isMonomialAlong_of_principal hn hN hE hT hc
    (fun _ hx => actual_monomial_product_principal_at hn hN hE hT hI hJ hi hj hmI hmJ hx)⟩

/-- Independently ACTUAL original monomial parts supply every factor input
before genuine product closure, without model/principal/product certificates. -/
theorem actual_original_monomial_parts_product_geometry (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ x ∈ N,IsNonzeroAlongAt N I x) (hj : ∀ x ∈ N,IsNonzeroAlongAt N J x) :
    let P := (monomialPartAlong n N I E).mul (monomialPartAlong n N J E)
    P.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N P x) ∧ IsMonomialAlong n N P E := by
  obtain ⟨_hcI,hMI,hnzMI,hmI,_hndI,_hnzNI,_heqI⟩ :=
    NonmonomialTransformAlong.parts_hypotheses hn (⟨N,E,I,0⟩ : MarkedIdeal n X) ⟨hN,hI,hE,hT⟩ hi
  obtain ⟨_hcJ,hMJ,hnzMJ,hmJ,_hndJ,_hnzNJ,_heqJ⟩ :=
    NonmonomialTransformAlong.parts_hypotheses hn (⟨N,E,J,0⟩ : MarkedIdeal n X) ⟨hN,hJ,hE,hT⟩ hj
  exact actual_relative_monomial_product_geometry hn hN hE hT hMI hMJ hnzMI hnzMJ hmI hmJ

end
end Hironaka.HironakaSharpActualRelativeMonomialProduct
