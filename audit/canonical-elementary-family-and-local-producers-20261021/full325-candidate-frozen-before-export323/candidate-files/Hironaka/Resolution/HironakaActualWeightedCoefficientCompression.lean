/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticVertexCoefficientData
import Hironaka.Resolution.HironakaActualCoefficientAnalyticBlowup
import Mathlib.RingTheory.Ideal.Colon

/-!
# Actual finite weighted coefficient compression

Positive low-coefficient weights of a genuine original analytic vertex family
are compressed to a common positive mark. Actual coordinate-centre division
constructs analytic quotient coefficients and proves the whole compressed ideal
image and exceptional-colon identities. This is a bounded weighted-presentation
prerequisite, not an assertion identifying its cosupport with an HS locus.
Blueprint: `hironaka-actual-weighted-coefficient-compression-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWeightedCoefficientCompression
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm GermIdealOrder
  HironakaActualAnalyticVertexCoefficientData HironakaActualFiniteCoefficientIdeals
  HironakaActualCoefficientPresentationCentrePower HironakaActualCoefficientReducedStrictGenerators
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientAnalyticBlowup
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualLocalCoefficientStrictGenerators HironakaActualFormalInitialDiagram
  HironakaHolomorphicJetMonomialSpan

section FiniteWeights
variable {ι : Type*} [Fintype ι]

/-- The literal common mark, including the empty product. -/
def weightedCommonMark (w : ι → ℕ) : ℕ := ∏ i, w i

/-- Every genuine positive individual weight gives a positive common mark. -/
theorem weightedCommonMark_pos (w : ι → ℕ) (hw : ∀ i, 0 < w i) :
    0 < weightedCommonMark w := by
  exact Finset.prod_pos fun i _ => hw i

/-- The actual compression exponent retains precisely the original mark. -/
theorem weight_mul_compressionExponent (w : ι → ℕ) (i : ι) :
    w i * (weightedCommonMark w / w i)=weightedCommonMark w := by
  exact Nat.mul_div_cancel' (Finset.dvd_prod_of_mem w (Finset.mem_univ i))

/-- Every retained coefficient has a genuinely positive compression exponent. -/
theorem compressionExponent_pos (w : ι → ℕ) (hw : ∀ i, 0 < w i) (i : ι) :
    0 < weightedCommonMark w / w i := by
  exact Nat.div_pos
    (Nat.le_of_dvd (weightedCommonMark_pos w hw) (Finset.dvd_prod_of_mem w (Finset.mem_univ i))) (hw i)

/-- The actual entire compressed ideal, using only literal powered original coefficients. -/
def weightedCompression {R : Type*} [CommRing R] (w : ι → ℕ) (c : ι → R) : Ideal R :=
  Ideal.span (range (fun i => c i ^ (weightedCommonMark w / w i)))

omit [Fintype ι] in
private theorem span_singleton_mul_span_range {R : Type*} [CommRing R]
    (x : R) (g : ι → R) :
    Ideal.span {x} * Ideal.span (range g)=Ideal.span (range (fun i => x*g i)) := by
  rw [Ideal.span_mul_span']
  congr 1
  ext y
  simp only [Set.mem_mul,Set.mem_singleton_iff,Set.mem_range]
  constructor
  · rintro ⟨a,rfl,b,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨x,rfl,g i,⟨i,rfl⟩,rfl⟩

private theorem map_weightedCompression_factor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : ι → ℕ) (c : ι → R) (x : S) (g : ι → S)
    (hg : ∀ i, x^(w i)*g i=f (c i)) :
    Ideal.map f (weightedCompression w c)=
      Ideal.span {x^weightedCommonMark w} * weightedCompression w g := by
  rw [weightedCompression,Ideal.map_span,weightedCompression,span_singleton_mul_span_range]
  have he : f '' range (fun i => c i^(weightedCommonMark w/w i))=
      range (fun i => x^weightedCommonMark w*g i^(weightedCommonMark w/w i)) := by
    rw [← range_comp]
    congr 1
    funext i
    change f (c i ^ (weightedCommonMark w / w i))=_
    rw [map_pow,← hg i,mul_pow,← pow_mul,weight_mul_compressionExponent]
  rw [he]

private theorem colon_principal_product {R : Type*} [CommRing R] [IsDomain R]
    (x : R) (hx : x ≠ 0) (J : Ideal R) : (Ideal.span {x}*J).colon {x}=J := by
  ext y
  rw [Submodule.mem_colon_singleton]
  change y*x ∈ Ideal.span {x}*J ↔ y ∈ J
  rw [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨z,hz,he⟩
    have hzy : z=y := mul_left_cancel₀ hx (he.trans (mul_comm y x))
    simpa only [hzy] using hz
  · intro hy
    exact ⟨y,hy,mul_comm x y⟩

end FiniteWeights

/-- Actual centre-power membership internally constructs all coefficients and the entire controlled ideal. -/
theorem exists_actual_weighted_compression_blowup {n : ℕ} {ι : Type*} [Fintype ι]
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (c : ι → HolGerm (ComplexModel n))
    (hc : ∀ i, c i ∈ actualAnalyticCoordinateIdeal A ^ w i) :
    0 < weightedCommonMark w ∧
      ∃ g : ι → HolGerm (ComplexModel n),
        (∀ i, (coordinateGerm e)^(w i)*g i=actualAnalyticBlowupPullback A e b (c i)) ∧
        (∀ i, actualUnshiftedTaylorAlgHom n (g i)=
          actualNormalizedFormalMember A e he b (w i)
            (actualUnshiftedTaylorAlgHom n (c i)) (actualTaylor_mem_coordinateCentre_pow A (w i) (c i) (hc i))) ∧
        Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (weightedCompression w c)=
          Ideal.span {(coordinateGerm e)^weightedCommonMark w}*weightedCompression w g ∧
        (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
          (weightedCompression w c)).colon {(coordinateGerm e)^weightedCommonMark w}=
            weightedCompression w g := by
  choose g hg hT using fun i => exists_actualAnalyticBlowup_quotient A e he b (w i) (c i) (hc i)
  have hmap := map_weightedCompression_factor (actualAnalyticBlowupPullback A e b).toRingHom
    w c (coordinateGerm e) g hg
  refine ⟨weightedCommonMark_pos w hw,g,hg,hT,hmap,?_⟩
  rw [hmap]
  exact colon_principal_product _ (pow_ne_zero _
    (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e)) _

local instance (t q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q

/-- Actual finite low normal coefficient positions, retaining every original vertex label. -/
abbrev weightedCoefficientIndex (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) :=
  (a : actualInitialVertices MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I)) ×
      normalExponentIndex t (actualCoefficientCentreVertexWeight k s t a.val)

/-- The genuine positive difference mark of the same original coefficient. -/
def coefficientWeight {k s t : ℕ} {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (i : weightedCoefficientIndex k s t I) : ℕ :=
  actualCoefficientCentreVertexWeight k s t i.1.val-actualNormalDegree i.2.val

/-- The original exponent bound proves positivity, without an input marking certificate. -/
theorem coefficientWeight_pos {k s t : ℕ} {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (i : weightedCoefficientIndex k s t I) : 0 < coefficientWeight i := by
  exact Nat.sub_pos_of_lt i.2.property

/-- The literal entire analytic coefficient germ supplied by the same original vertex family. -/
def vertexCoefficientGerm {k s t : ℕ} {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (P : ActualAnalyticVertexCoefficientData k s t I) (i : weightedCoefficientIndex k s t I) :
    HolGerm (ComplexModel (k+s)) :=
  HolGerm.mk (P.coefficient i.1 i.2.val) (P.holomorphic i.1 i.2.val)

/-- Original analytic data internally supplies the entire weighted family before any actual transformation. -/
theorem exists_original_weighted_coefficient_compression (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) :
    ∃ P : ActualAnalyticVertexCoefficientData k s t I,
      0 < weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I)) ∧
      ∀ (e : Fin (k+s)) (_he : e ∈ actualTangentCentreVariables k s) (b : Fin (k+s) → ℂ),
        (∀ i : weightedCoefficientIndex k s t I,
          P.domain ∩ complexCoordinatePlane (k+s) k ⊆
            cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val))
              (coefficientWeight i)) →
        ∃ g : weightedCoefficientIndex k s t I → HolGerm (ComplexModel (k+s)),
          (∀ i, (coordinateGerm e)^(coefficientWeight i)*g i=
            actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b (vertexCoefficientGerm P i)) ∧
          Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b).toRingHom
              (weightedCompression coefficientWeight (vertexCoefficientGerm P))=
            Ideal.span {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I))}*
              weightedCompression coefficientWeight g ∧
          (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b).toRingHom
              (weightedCompression coefficientWeight (vertexCoefficientGerm P))).colon
                {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I))}=
            weightedCompression coefficientWeight g := by
  obtain ⟨P⟩ := nonempty_actualAnalyticVertexCoefficientData k s t I
  refine ⟨P,weightedCommonMark_pos _ coefficientWeight_pos,?_⟩
  intro e he b hcosupp
  have hmem (i : weightedCoefficientIndex k s t I) :
      vertexCoefficientGerm P i ∈ actualAnalyticCoordinateIdeal (actualTangentCentreVariables k s)^
        coefficientWeight i := by
    rw [actualAnalyticCoordinateIdeal_normal]
    exact mk_mem_normalIdeal_pow_of_local_cosupport k s (coefficientWeight i)
      (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val))
      P.domain P.isOpen_domain P.zero_mem_domain (P.coherent i.1 i.2.val i.2.property)
      (hcosupp i) (P.holomorphic i.1 i.2.val) (P.coefficient_member i.1 i.2.val i.2.property)
  obtain ⟨_,g,hg,_hT,hmap,hcolon⟩ := exists_actual_weighted_compression_blowup
    (actualTangentCentreVariables k s) e he b coefficientWeight coefficientWeight_pos
      (vertexCoefficientGerm P) hmem
  exact ⟨g,hg,hmap,hcolon⟩

end
end Hironaka.HironakaActualWeightedCoefficientCompression
