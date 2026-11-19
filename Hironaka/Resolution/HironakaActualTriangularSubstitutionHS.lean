/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCoordinateSpecializationHS

/-! Actual polynomial triangular substitution and its genuine local inverse geometry. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTriangularSubstitutionHS
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaActualHolomorphicFibreHS HironakaActualCoordinateSpecializationHS
  HironakaSmoothCentreRealDomainActualAmbientHS

private def first (n : ℕ) : Fin (2+n) := ⟨0,by omega⟩
private def second (n : ℕ) : Fin (2+n) := ⟨1,by omega⟩
private theorem first_ne_second (n : ℕ) : first n ≠ second n := by
  intro h
  have h' := congrArg Fin.val h
  simp [first,second] at h'

private def replaceSecond (n : ℕ) (z : ComplexModel (2+n)) (a : ℂ) : ComplexModel (2+n) :=
  z+(a-z (second n)) • (EuclideanSpace.basisFun (Fin (2+n)) ℂ) (second n)

private theorem replaceSecond_second (n : ℕ) (z : ComplexModel (2+n)) (a : ℂ) :
    replaceSecond n z a (second n)=a := by
  simp [replaceSecond]

private theorem replaceSecond_other (n : ℕ) (z : ComplexModel (2+n)) (a : ℂ)
    (i : Fin (2+n)) (hi : i ≠ second n) : replaceSecond n z a i=z i := by
  simp [replaceSecond,hi]

/-- The actual jointly polynomial deformation, with every other original coordinate retained. -/
def actualTriangularDeformation (n : ℕ) (b t : ℂ) (z : ComplexModel (2+n)) : ComplexModel (2+n) :=
  replaceSecond n z (t*z (second n)+(1-t)*z (first n)*(b+z (second n)))

/-- The literal elementary triangular blowup substitution before exceptional division. -/
def actualTriangularSubstitution (n : ℕ) (b : ℂ) : ComplexModel (2+n) → ComplexModel (2+n) :=
  actualTriangularDeformation n b 0

/-- The genuine rational inverse on the true denominator-nonzero open. -/
def actualTriangularInverse (n : ℕ) (b t : ℂ) (w : ComplexModel (2+n)) : ComplexModel (2+n) :=
  replaceSecond n w ((w (second n)-(1-t)*b*w (first n))/(t+(1-t)*w (first n)))

/-- The real source and target of the genuine local inverse. -/
def actualTriangularInverseDomain (n : ℕ) (t : ℂ) : Set (ComplexModel (2+n)) :=
  {z | t+(1-t)*z (first n) ≠ 0}

private theorem deformation_first (n : ℕ) (b t : ℂ) (z : ComplexModel (2+n)) :
    actualTriangularDeformation n b t z (first n)=z (first n) :=
  replaceSecond_other n z _ _ (first_ne_second n)
private theorem deformation_second (n : ℕ) (b t : ℂ) (z : ComplexModel (2+n)) :
    actualTriangularDeformation n b t z (second n)=
      t*z (second n)+(1-t)*z (first n)*(b+z (second n)) :=
  replaceSecond_second n z _
private theorem inverse_first (n : ℕ) (b t : ℂ) (z : ComplexModel (2+n)) :
    actualTriangularInverse n b t z (first n)=z (first n) :=
  replaceSecond_other n z _ _ (first_ne_second n)
private theorem inverse_second (n : ℕ) (b t : ℂ) (z : ComplexModel (2+n)) :
    actualTriangularInverse n b t z (second n)=
      (z (second n)-(1-t)*b*z (first n))/(t+(1-t)*z (first n)) :=
  replaceSecond_second n z _

/-- Each true polynomial deformation fixes the actual original germ centre. -/
theorem actualTriangularDeformation_zero (n : ℕ) (b t : ℂ) :
    actualTriangularDeformation n b t 0=0 := by
  simp [actualTriangularDeformation,replaceSecond]

/-- The displayed forward map is genuinely holomorphic jointly in parameter and original coordinates. -/
theorem actualTriangularJoint_contDiff (n : ℕ) (b : ℂ) :
    ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (2+n) =>
      actualTriangularDeformation n b (u.1 0) u.2) := by
  have hp : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (2+n) => u.1 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.comp contDiff_fst
  have h1 : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (2+n) => u.2 (first n)) :=
    (EuclideanSpace.proj (first n) : ComplexModel (2+n) →L[ℂ] ℂ).contDiff.comp contDiff_snd
  have h2 : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (2+n) => u.2 (second n)) :=
    (EuclideanSpace.proj (second n) : ComplexModel (2+n) →L[ℂ] ℂ).contDiff.comp contDiff_snd
  exact contDiff_snd.add
    ((((hp.mul h2).add (((contDiff_const.sub hp).mul h1).mul (contDiff_const.add h2))).sub h2).smul contDiff_const)

/-- Each fixed-parameter actual map is holomorphic everywhere. -/
theorem actualTriangularDeformation_contDiff (n : ℕ) (b t : ℂ) :
    ContDiff ℂ ∞ (actualTriangularDeformation n b t) := by
  have h1 : ContDiff ℂ ∞ (fun z : ComplexModel (2+n) => z (first n)) :=
    (EuclideanSpace.proj (first n) : ComplexModel (2+n) →L[ℂ] ℂ).contDiff
  have h2 : ContDiff ℂ ∞ (fun z : ComplexModel (2+n) => z (second n)) :=
    (EuclideanSpace.proj (second n) : ComplexModel (2+n) →L[ℂ] ℂ).contDiff
  exact contDiff_id.add
    ((((contDiff_const.mul h2).add ((contDiff_const.mul h1).mul (contDiff_const.add h2))).sub h2).smul contDiff_const)

/-- The actual inverse domain is genuinely open in the original ambient space. -/
theorem isOpen_actualTriangularInverseDomain (n : ℕ) (t : ℂ) :
    IsOpen (actualTriangularInverseDomain n t) :=
  isOpen_ne_fun (continuous_const.add (continuous_const.mul
    (EuclideanSpace.proj (first n) : ComplexModel (2+n) →L[ℂ] ℂ).continuous)) continuous_const

/-- The real inverse formula is holomorphic on precisely the true denominator-nonzero open. -/
theorem differentiableOn_actualTriangularInverse (n : ℕ) (b t : ℂ) :
    DifferentiableOn ℂ (actualTriangularInverse n b t) (actualTriangularInverseDomain n t) := by
  intro z hz
  have h1 : DifferentiableAt ℂ (fun w : ComplexModel (2+n) => w (first n)) z :=
    (EuclideanSpace.proj (first n) : ComplexModel (2+n) →L[ℂ] ℂ).differentiableAt
  have h2 : DifferentiableAt ℂ (fun w : ComplexModel (2+n) => w (second n)) z :=
    (EuclideanSpace.proj (second n) : ComplexModel (2+n) →L[ℂ] ℂ).differentiableAt
  have hnum : DifferentiableAt ℂ (fun w : ComplexModel (2+n) =>
      w (second n)-(1-t)*b*w (first n)) z :=
    h2.sub ((differentiableAt_const _).mul h1)
  have hden : DifferentiableAt ℂ (fun w : ComplexModel (2+n) => t+(1-t)*w (first n)) z :=
    (differentiableAt_const _).add ((differentiableAt_const _).mul h1)
  have hquot : DifferentiableAt ℂ (fun w : ComplexModel (2+n) =>
      (w (second n)-(1-t)*b*w (first n))/(t+(1-t)*w (first n))) z := by
    simpa only [div_eq_mul_inv] using hnum.fun_mul (hden.fun_inv hz)
  exact (differentiableAt_id.add
    ((hquot.sub h2).smul (differentiableAt_const _))).differentiableWithinAt

/-- Genuine cancellation gives the actual left inverse on the real source. -/
theorem actualTriangularInverse_left (n : ℕ) (b t : ℂ) (z : ComplexModel (2+n))
    (hz : z ∈ actualTriangularInverseDomain n t) :
    actualTriangularInverse n b t (actualTriangularDeformation n b t z)=z := by
  ext i
  by_cases hi : i=second n
  · subst i
    rw [inverse_second,deformation_first,deformation_second]
    change t+(1-t)*z (first n) ≠ 0 at hz
    field_simp
    ring
  · rw [actualTriangularInverse,replaceSecond_other n _ _ i hi,
      actualTriangularDeformation,replaceSecond_other n _ _ i hi]

/-- Genuine cancellation also gives the actual right inverse on the same real target. -/
theorem actualTriangularInverse_right (n : ℕ) (b t : ℂ) (z : ComplexModel (2+n))
    (hz : z ∈ actualTriangularInverseDomain n t) :
    actualTriangularDeformation n b t (actualTriangularInverse n b t z)=z := by
  ext i
  by_cases hi : i=second n
  · subst i
    rw [deformation_second,inverse_first,inverse_second]
    change t+(1-t)*z (first n) ≠ 0 at hz
    field_simp
    ring
  · rw [actualTriangularDeformation,replaceSecond_other n _ _ i hi,
      actualTriangularInverse,replaceSecond_other n _ _ i hi]

/-- Explicit two-sided actual inverse geometry, built only from the original nonzero parameter. -/
def actualTriangularLocalEquiv (n : ℕ) (b t : ℂ) (ht : t ≠ 0) :
    LocalHolomorphicEquivAt (n := 2+n) (0 : ComplexModel (2+n)) where
  source := actualTriangularInverseDomain n t
  target := actualTriangularInverseDomain n t
  isOpen_source := isOpen_actualTriangularInverseDomain n t
  isOpen_target := isOpen_actualTriangularInverseDomain n t
  center_mem_source := by simpa [actualTriangularInverseDomain] using ht
  toFun := actualTriangularDeformation n b t
  invFun := actualTriangularInverse n b t
  toFun_holomorphic := ((actualTriangularDeformation_contDiff n b t).differentiable (by simp)).differentiableOn
  invFun_holomorphic := differentiableOn_actualTriangularInverse n b t
  mapsTo_toFun := by intro z hz; simpa only [actualTriangularInverseDomain,mem_ofPred_eq,deformation_first] using hz
  mapsTo_invFun := by intro z hz; simpa only [actualTriangularInverseDomain,mem_ofPred_eq,inverse_first] using hz
  left_inv := fun z hz => actualTriangularInverse_left n b t z hz
  right_inv := fun z hz => actualTriangularInverse_right n b t z hz

/-- The actual whole germ pullback of the true original polynomial map. -/
def actualTriangularGerm (n : ℕ) (b t : ℂ) :
    HolGerm (ComplexModel (2+n)) →ₐ[ℂ] HolGerm (ComplexModel (2+n)) :=
  compAlgHom (actualTriangularDeformation n b t)
    (Eventually.of_forall fun _ => ((actualTriangularDeformation_contDiff n b t).differentiable (by simp)).differentiableAt)
    (actualTriangularDeformation_zero n b t)

/-- EVERY original numerator has its literal original composed representative. -/
theorem actualTriangularGerm_mk (n : ℕ) (b t : ℂ) (F : ComplexModel (2+n) → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (2+n)), DifferentiableAt ℂ F z) :
    actualTriangularGerm n b t (HolGerm.mk F hF) =
      HolGerm.mk (F ∘ actualTriangularDeformation n b t)
        (holomorphic_comp _ (Eventually.of_forall fun _ =>
          ((actualTriangularDeformation_contDiff n b t).differentiable (by simp)).differentiableAt)
          (actualTriangularDeformation_zero n b t) hF) := rfl

/-- The actual local inverse produces the genuine algebra equivalence off zero. -/
def actualTriangularGermEquiv (n : ℕ) (b t : ℂ) (ht : t ≠ 0) :
    HolGerm (ComplexModel (2+n)) ≃ₐ[ℂ] HolGerm (ComplexModel (2+n)) :=
  localGermAlgEquiv (actualTriangularLocalEquiv n b t ht) (actualTriangularDeformation_zero n b t)

/-- The inverse-derived equivalence acts by precisely the same true forward polynomial. -/
theorem actualTriangularGermEquiv_apply (n : ℕ) (b t : ℂ) (ht : t ≠ 0)
    (g : HolGerm (ComplexModel (2+n))) :
    actualTriangularGermEquiv n b t ht g=actualTriangularGerm n b t g := rfl

/-- Actual nonzero parameters preserve EVERY existing original whole-ideal HS value. -/
theorem hilbertSamuelValue_actual_triangular_nonzero (n : ℕ) (b t : ℂ) (ht : t ≠ 0)
    (I : Ideal (HolGerm (ComplexModel (2+n)))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map (actualTriangularGerm n b t).toRingHom I) ℓ =
      hilbertSamuelValue I ℓ :=
  actualAmbientHS_eq_of_genuineAlgEquiv (actualTriangularGermEquiv n b t ht) I ℓ

/-- The REAL joint domain uses only the common original holomorphic neighbourhood. -/
def actualTriangularDomain (n : ℕ) (b : ℂ) (U : Set (ComplexModel (2+n))) :
    Set (ComplexModel 1 × ComplexModel (2+n)) :=
  (fun u => actualTriangularDeformation n b (u.1 0) u.2) ⁻¹' U

/-- The actual joint polynomial map gives true openness of that same original domain. -/
theorem isOpen_actualTriangularDomain (n : ℕ) (b : ℂ) {U : Set (ComplexModel (2+n))} (hU : IsOpen U) :
    IsOpen (actualTriangularDomain n b U) := hU.preimage (actualTriangularJoint_contDiff n b).continuous

/-- EVERY original parameter-axis point lies in the SAME genuine joint domain. -/
theorem axis_mem_actualTriangularDomain (n : ℕ) (b : ℂ) {U : Set (ComplexModel (2+n))}
    (h0 : (0 : ComplexModel (2+n)) ∈ U) (p : ComplexModel 1) :
    (p,0) ∈ actualTriangularDomain n b U := by
  change actualTriangularDeformation n b (p 0) 0 ∈ U
  rwa [actualTriangularDeformation_zero]

/-- The actual original finite generators composed with the true jointly varying coordinate map. -/
def actualTriangularFamily (n : ℕ) (b : ℂ) {s : ℕ} (G : Fin s → ComplexModel (2+n) → ℂ)
    (i : Fin s) (u : ComplexModel 1 × ComplexModel (2+n)) : ℂ :=
  G i (actualTriangularDeformation n b (u.1 0) u.2)

/-- Original holomorphicity on ONE original neighbourhood gives the real joint holomorphic family. -/
theorem differentiableOn_actualTriangularFamily (n : ℕ) (b : ℂ) {U : Set (ComplexModel (2+n))}
    (hU : IsOpen U) {s : ℕ} (G : Fin s → ComplexModel (2+n) → ℂ)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) (i : Fin s) :
    DifferentiableOn ℂ (actualTriangularFamily n b G i) (actualTriangularDomain n b U) := by
  intro u hu
  exact (((hG i).differentiableAt (hU.mem_nhds hu)).comp u
    ((actualTriangularJoint_contDiff n b).differentiable (by simp)).differentiableAt).differentiableWithinAt

private theorem originalGenerator_holomorphic {a : ℕ} {U : Set (ComplexModel a)}
    (hU : IsOpen U) (h0 : (0 : ComplexModel a) ∈ U) {F : ComplexModel a → ℂ}
    (hF : DifferentiableOn ℂ F U) : ∀ᶠ z in 𝓝 (0 : ComplexModel a), DifferentiableAt ℂ F z := by
  filter_upwards [hU.mem_nhds h0] with z hz
  exact hF.differentiableAt (hU.mem_nhds hz)

/-- BOTH ENTIRE fibre-ideal directions retain the image of the SAME original finite ideal span. -/
theorem actualTriangularFibreIdeal_eq_map_original_span (n : ℕ) (b : ℂ) {U : Set (ComplexModel (2+n))}
    (hU : IsOpen U) (h0 : (0 : ComplexModel (2+n)) ∈ U) {s : ℕ}
    (G : Fin s → ComplexModel (2+n) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U) (p : ComplexModel 1) :
    actualFibreIdeal (isOpen_actualTriangularDomain n b hU) (actualTriangularFamily n b G)
      (differentiableOn_actualTriangularFamily n b hU G hG) p (axis_mem_actualTriangularDomain n b h0 p) =
      Ideal.map (actualTriangularGerm n b (p 0)).toRingHom
        (Ideal.span (range fun i => HolGerm.mk (G i) (originalGenerator_holomorphic hU h0 (hG i)))) := by
  rw [actualFibreIdeal_eq_original_span,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  rw [Function.comp_apply]
  change _ = actualTriangularGerm n b (p 0)
    (HolGerm.mk (G i) (originalGenerator_holomorphic hU h0 (hG i)))
  rw [actualTriangularGerm_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => rfl


private def triangularParameterPoint (c : ℂ) : ComplexModel 1 :=
  c • (EuclideanSpace.basisFun (Fin 1) ℂ) 0

private theorem triangularParameterPoint_coordinate (c : ℂ) : triangularParameterPoint c 0=c := by
  simp [triangularParameterPoint]

private theorem continuous_triangularParameterPoint : Continuous triangularParameterPoint :=
  continuous_id.smul continuous_const

/-- EVERY original ideal has every actual HS value bounded by the TRUE triangular substitution. -/
theorem hilbertSamuelValue_actual_triangular_substitution (n : ℕ) (b : ℂ)
    (I : Ideal (HolGerm (ComplexModel (2+n)))) (ℓ : ℕ) :
    hilbertSamuelValue I ℓ ≤
      hilbertSamuelValue (Ideal.map (actualTriangularGerm n b 0).toRingHom I) ℓ := by
  obtain ⟨U,hU,h0,s,G,hG,hI⟩ := exists_original_contraction_generators 2 n I
  let D := actualTriangularDomain n b U
  have hD : IsOpen D := isOpen_actualTriangularDomain n b hU
  let F := actualTriangularFamily n b G
  have hF : ∀ i, DifferentiableOn ℂ (F i) D := differentiableOn_actualTriangularFamily n b hU G hG
  have haxis (p : ComplexModel 1) : (p,0) ∈ D := axis_mem_actualTriangularDomain n b h0 p
  let J (c : ℂ) := actualFibreIdeal hD F hF (triangularParameterPoint c) (haxis (triangularParameterPoint c))
  have hdict (c : ℂ) : J c=Ideal.map (actualTriangularGerm n b c).toRingHom I := by
    have h := actualTriangularFibreIdeal_eq_map_original_span n b hU h0 G hG (triangularParameterPoint c)
    rw [hI,triangularParameterPoint_coordinate] at h
    exact h
  let P : ℂ → (⊤ : TopologicalSpace.Opens (ComplexModel 1)) :=
    fun c => ⟨triangularParameterPoint c,mem_univ _⟩
  have hP : Continuous P := by
    apply Continuous.subtype_mk
    exact continuous_triangularParameterPoint
  have hclosed : IsClosed {c : ℂ | hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    exact (isClosed_actualFibreHS_superlevel hD F hF ⊤ (fun p _ => haxis p) ℓ
      (hilbertSamuelValue I ℓ)).preimage hP
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {c : ℂ | hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    intro c hc
    have hc0 : c ≠ 0 := by simpa using hc
    change hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ
    rw [hdict c,hilbertSamuelValue_actual_triangular_nonzero n b c hc0]
  have hz := closure_minimal hsub hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  change hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J 0) ℓ at hz
  rwa [hdict 0] at hz
end
end Hironaka.HironakaActualTriangularSubstitutionHS
