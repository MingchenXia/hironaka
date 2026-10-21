/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalIdeal
import Hironaka.Resolution.HironakaActualCentreJointJets
import Hironaka.Analytic.AnalyticGermDecomposition

/-!
# The entire independently defined actual holomorphic graph vanishing ideal

Genuine original triangular shears, actual whole Hadamard trace kernel and
literal graph parametrization give the entire graph ideal as the base ideal
extension plus actual graph equations. No geometric ideal equality or
canonical marked invariance under added equations is assumed.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualHolomorphicGraphIdeal
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
variable {d t : ℕ}

/-- The literal actual graph section, before taking germs or ideals. -/
def graphSection (f : ComplexModel d → ComplexModel t) (x : ComplexModel d) : ComplexModel (d+t) :=
  tangentInclusion d t x + actualJointNormalInclusion d t (f x)

/-- The independent original graph subset, using its actual two block relations. -/
def graphCarrier (f : ComplexModel d → ComplexModel t) (W : Set (ComplexModel d)) : Set (ComplexModel (d+t)) :=
  {z | tangentProjection d t z ∈ W ∧ actualJointNormalProjection d t z = f (tangentProjection d t z)}

/-- Genuine subtraction of the actual normal graph value. -/
def graphShearMinus (f : ComplexModel d → ComplexModel t) (z : ComplexModel (d+t)) : ComplexModel (d+t) :=
  z - actualJointNormalInclusion d t (f (tangentProjection d t z))

/-- Genuine addition of the actual normal graph value. -/
def graphShearPlus (f : ComplexModel d → ComplexModel t) (z : ComplexModel (d+t)) : ComplexModel (d+t) :=
  z + actualJointNormalInclusion d t (f (tangentProjection d t z))

@[simp] theorem projection_graphSection (f : ComplexModel d → ComplexModel t) (x : ComplexModel d) :
    tangentProjection d t (graphSection f x) = x := by simp [graphSection,tangentProjection_tangentInclusion]

@[simp] theorem normalProjection_graphSection (f : ComplexModel d → ComplexModel t) (x : ComplexModel d) :
    actualJointNormalProjection d t (graphSection f x) = f x := by simp [graphSection]

@[simp] theorem projection_graphShearMinus (f : ComplexModel d → ComplexModel t) (z : ComplexModel (d+t)) :
    tangentProjection d t (graphShearMinus f z) = tangentProjection d t z := by simp [graphShearMinus]

@[simp] theorem projection_graphShearPlus (f : ComplexModel d → ComplexModel t) (z : ComplexModel (d+t)) :
    tangentProjection d t (graphShearPlus f z) = tangentProjection d t z := by simp [graphShearPlus]

@[simp] theorem graphShearMinus_plus (f : ComplexModel d → ComplexModel t) (z : ComplexModel (d+t)) :
    graphShearMinus f (graphShearPlus f z) = z := by
  unfold graphShearMinus
  rw [projection_graphShearPlus]
  exact add_sub_cancel_right _ _

@[simp] theorem graphShearPlus_minus (f : ComplexModel d → ComplexModel t) (z : ComplexModel (d+t)) :
    graphShearPlus f (graphShearMinus f z) = z := by
  unfold graphShearPlus
  rw [projection_graphShearMinus]
  exact sub_add_cancel _ _

private theorem holomorphic_normal_increment (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) :
    ∀ᶠ z in nhds (0 : ComplexModel (d+t)),DifferentiableAt ℂ
      (fun z => actualJointNormalInclusion d t (f (tangentProjection d t z))) z := by
  have hp : Tendsto (tangentProjection d t) (nhds 0) (nhds 0) := by
    simpa using (tangentProjection d t).continuous.tendsto 0
  exact (hp.eventually hf).mono fun z hz => (actualJointNormalInclusion d t).differentiableAt.comp z
    (hz.comp z (tangentProjection d t).differentiableAt)

private theorem holomorphic_graphSection (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) :
    ∀ᶠ x in nhds (0 : ComplexModel d),DifferentiableAt ℂ (graphSection f) x :=
  hf.mono fun x hx => (tangentInclusion d t).differentiableAt.add
    ((actualJointNormalInclusion d t).differentiableAt.comp x hx)

private theorem holomorphic_graphShearMinus (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) :
    ∀ᶠ z in nhds (0 : ComplexModel (d+t)),DifferentiableAt ℂ (graphShearMinus f) z :=
  (holomorphic_normal_increment f hf).mono fun _ hz => differentiableAt_id.sub hz

private theorem holomorphic_graphShearPlus (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) :
    ∀ᶠ z in nhds (0 : ComplexModel (d+t)),DifferentiableAt ℂ (graphShearPlus f) z :=
  (holomorphic_normal_increment f hf).mono fun _ hz => differentiableAt_id.add hz

variable (f : ComplexModel d → ComplexModel t)
  (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) (h0 : f 0 = 0)

/-- Whole original graph restriction, by the literal true graph section. -/
def graphTrace : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel d) :=
  compAlgHom (graphSection f) (holomorphic_graphSection f hf) (by simp [graphSection,h0])

/-- Actual triangular original shears induce inverse whole complex germ algebra maps. -/
def graphShearAlgEquiv : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)) := by
  let a := compAlgHom (graphShearMinus f) (holomorphic_graphShearMinus f hf) (by simp [graphShearMinus,h0])
  let b := compAlgHom (graphShearPlus f) (holomorphic_graphShearPlus f hf) (by simp [graphShearPlus,h0])
  apply AlgEquiv.ofAlgHom a b
  · apply AlgHom.ext
    intro g
    induction g using HolGerm.induction_on with
    | h F hF =>
      change a (b (HolGerm.mk F hF)) = HolGerm.mk F hF
      dsimp only [a,b]
      rw [compAlgHom_mk,compAlgHom_mk]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => congrArg F (graphShearPlus_minus f z)
  · apply AlgHom.ext
    intro g
    induction g using HolGerm.induction_on with
    | h F hF =>
      change b (a (HolGerm.mk F hF)) = HolGerm.mk F hF
      dsimp only [a,b]
      rw [compAlgHom_mk,compAlgHom_mk]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => congrArg F (graphShearMinus_plus f z)

/-- Genuine whole graph restriction and original projection pullback form an actual retraction. -/
theorem graphTrace_tangentPullback (g : HolGerm (ComplexModel d)) :
    graphTrace f hf h0 (tangentPullback d t g) = g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold graphTrace tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (projection_graphSection f z)

/-- The true graph shear identifies WHOLE graph trace with actual Hadamard plane trace. -/
theorem graphTrace_graphShearAlgEquiv (g : HolGerm (ComplexModel (d+t))) :
    graphTrace f hf h0 (graphShearAlgEquiv f hf h0 g) = planeTrace d t g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold graphShearAlgEquiv graphTrace planeTrace
    change compAlgHom (graphSection f) (holomorphic_graphSection f hf) (by simp [graphSection,h0])
      (compAlgHom (graphShearMinus f) (holomorphic_graphShearMinus f hf)
        (by simp [graphShearMinus,h0]) (HolGerm.mk F hF)) = _
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg F
    simp [graphShearMinus,graphSection,tangentProjection_tangentInclusion]

include hf in
private theorem holomorphic_base_component (i : Fin t) :
    ∀ᶠ z in nhds (0 : ComplexModel (d+t)),DifferentiableAt ℂ
      (fun z => f (tangentProjection d t z) i) z := by
  have hp : Tendsto (tangentProjection d t) (nhds 0) (nhds 0) := by
    simpa using (tangentProjection d t).continuous.tendsto 0
  exact (hp.eventually hf).mono fun z hz =>
    (EuclideanSpace.proj i : ComplexModel t →L[ℂ] ℂ).differentiableAt.comp z
      (hz.comp z (tangentProjection d t).differentiableAt)

/-- A literal original graph equation, represented by the SAME original coordinate function. -/
def graphRelation (i : Fin t) : HolGerm (ComplexModel (d+t)) :=
  HolGerm.mk (fun z => z (i.natAdd d) - f (tangentProjection d t z) i)
    ((holomorphic_base_component f hf i).mono fun _ hz =>
      (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.sub hz)

/-- The genuine entire finite graph-equation ideal, defined by its literal original functions. -/
def graphRelations : Ideal (HolGerm (ComplexModel (d+t))) := Ideal.span (range (graphRelation f hf))

private theorem graphShearAlgEquiv_normalCoordinate (i : Fin t) :
    graphShearAlgEquiv f hf h0 (normalCoordinate d t i) = graphRelation f hf i := by
  unfold graphShearAlgEquiv normalCoordinate coordinateGerm graphRelation
  change compAlgHom (graphShearMinus f) (holomorphic_graphShearMinus f hf)
    (by simp [graphShearMinus,h0]) (HolGerm.mk _ _) = _
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp [graphShearMinus]

private theorem map_shear_normalIdeal :
    Ideal.map (graphShearAlgEquiv f hf h0).toRingHom (normalIdeal d t) = graphRelations f hf := by
  unfold normalIdeal graphRelations
  rw [Ideal.map_span,← Set.range_comp]
  apply congrArg (fun g : Fin t → HolGerm (ComplexModel (d+t)) => Ideal.span (range g))
  funext i
  exact graphShearAlgEquiv_normalCoordinate f hf h0 i

/-- The actual whole graph kernel consists exactly of the literal finite original graph equations. -/
theorem ker_graphTrace_eq_graphRelations :
    RingHom.ker (graphTrace f hf h0).toRingHom = graphRelations f hf := by
  let E := graphShearAlgEquiv f hf h0
  rw [← map_shear_normalIdeal f hf h0]
  apply le_antisymm
  · intro g hg
    have htrace : planeTrace d t (E.symm g) = 0 := by
      rw [← graphTrace_graphShearAlgEquiv f hf h0]
      change graphTrace f hf h0 (E (E.symm g)) = 0
      rw [E.apply_symm_apply]
      exact hg
    have hm : E.symm g ∈ normalIdeal d t := by
      rw [normalIdeal_eq_ker_planeTrace]
      exact htrace
    have hi := Ideal.mem_map_of_mem E.toRingHom hm
    change E (E.symm g) ∈ Ideal.map E.toRingHom (normalIdeal d t) at hi
    rw [E.apply_symm_apply] at hi
    exact hi
  · apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    change graphTrace f hf h0 (graphShearAlgEquiv f hf h0 g) = 0
    rw [graphTrace_graphShearAlgEquiv]
    rw [normalIdeal_eq_ker_planeTrace] at hg
    exact hg

private theorem graphSection_projection_of_mem {W : Set (ComplexModel d)}
    {z : ComplexModel (d+t)} (hz : z ∈ graphCarrier f W) :
    graphSection f (tangentProjection d t z) = z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [graphSection]
  · have he := congrArg (fun u : ComplexModel t => u j) hz.2
    simpa [graphSection] using he.symm

/-- The literal original graph's independently defined whole vanishing ideal is PROVED to be the true trace comap. -/
theorem graph_vanishingIdeal_eq_comap (W : Set (ComplexModel d)) :
    AnalyticGermDecomposition.vanishingIdeal (graphCarrier f W) =
      Ideal.comap (graphTrace f hf h0).toRingHom (AnalyticGermDecomposition.vanishingIdeal W) := by
  ext g
  obtain ⟨F,hF,rfl⟩ := HolGerm.exists_eq_mk g
  change HolGerm.mk F hF ∈ AnalyticGermDecomposition.vanishingIdeal (graphCarrier f W) ↔
    graphTrace f hf h0 (HolGerm.mk F hF) ∈ AnalyticGermDecomposition.vanishingIdeal W
  unfold graphTrace
  rw [compAlgHom_mk,AnalyticGermDecomposition.mem_vanishingIdeal_mk,
    AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  constructor
  · intro hvan
    have hs : Tendsto (graphSection f) (nhds 0) (nhds 0) := by
      have he : graphSection f 0 = 0 := by simp [graphSection,h0]
      simpa only [he] using (holomorphic_graphSection f hf).self_of_nhds.continuousAt.tendsto
    filter_upwards [hs.eventually hvan] with x hx hxW
    exact hx ⟨by simpa using hxW,by simp⟩
  · intro hvan
    have hp : Tendsto (tangentProjection d t) (nhds 0) (nhds 0) := by
      simpa using (tangentProjection d t).continuous.tendsto 0
    filter_upwards [hp.eventually hvan] with z hz hzG
    have he := graphSection_projection_of_mem f hzG
    simpa only [Function.comp_apply,he] using hz hzG.1

private theorem comap_eq_map_sup_ker {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (s : S →+* R) (hqs : ∀ x,q (s x) = x) (I : Ideal S) :
    Ideal.comap q I = Ideal.map s I ⊔ RingHom.ker q := by
  apply le_antisymm
  · intro g hg
    have hs : s (q g) ∈ Ideal.map s I := Ideal.mem_map_of_mem s hg
    have hk : g - s (q g) ∈ RingHom.ker q := by
      change q (g - s (q g)) = 0
      rw [map_sub,hqs,sub_self]
    have ha := Ideal.add_mem (Ideal.map s I ⊔ RingHom.ker q)
      (Ideal.mem_sup_left hs) (Ideal.mem_sup_right hk)
    simpa only [add_sub_cancel] using ha
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro g hg
      change q (s g) ∈ I
      rwa [hqs]
    · intro g hg
      change q g ∈ I
      change q g = 0 at hg
      rw [hg]
      exact I.zero_mem

include h0 in
/-- The ENTIRE actual graph ideal is the genuine base extension plus literal graph relations, for ANY original W. -/
theorem graph_vanishingIdeal_eq (W : Set (ComplexModel d)) :
    AnalyticGermDecomposition.vanishingIdeal (graphCarrier f W) =
      Ideal.map (tangentPullback d t).toRingHom (AnalyticGermDecomposition.vanishingIdeal W) ⊔ graphRelations f hf := by
  rw [graph_vanishingIdeal_eq_comap f hf h0 W]
  rw [comap_eq_map_sup_ker (graphTrace f hf h0).toRingHom (tangentPullback d t).toRingHom
    (graphTrace_tangentPullback f hf h0)]
  rw [ker_graphTrace_eq_graphRelations]

private def graphQuotientMap (W : Set (ComplexModel d)) :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ]
      HolGerm (ComplexModel d) ⧸ AnalyticGermDecomposition.vanishingIdeal W :=
  (Ideal.Quotient.mkₐ ℂ (AnalyticGermDecomposition.vanishingIdeal W)).comp (graphTrace f hf h0)

private theorem graphQuotientMap_surjective (W : Set (ComplexModel d)) :
    Function.Surjective (graphQuotientMap f hf h0 W) := by
  intro x
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨tangentPullback d t g,?_⟩
  change Ideal.Quotient.mk _ (graphTrace f hf h0 (tangentPullback d t g)) = Ideal.Quotient.mk _ g
  rw [graphTrace_tangentPullback]

private theorem graphQuotientMap_kernel (W : Set (ComplexModel d)) :
    RingHom.ker (graphQuotientMap f hf h0 W).toRingHom =
      AnalyticGermDecomposition.vanishingIdeal (graphCarrier f W) := by
  rw [graph_vanishingIdeal_eq_comap f hf h0 W]
  ext g
  change Ideal.Quotient.mk (AnalyticGermDecomposition.vanishingIdeal W) (graphTrace f hf h0 g) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The independently defined ENTIRE original graph quotient is the true original base quotient. -/
def graphQuotientAlgEquiv (W : Set (ComplexModel d)) :
    (HolGerm (ComplexModel (d+t)) ⧸ AnalyticGermDecomposition.vanishingIdeal (graphCarrier f W)) ≃ₐ[ℂ]
      HolGerm (ComplexModel d) ⧸ AnalyticGermDecomposition.vanishingIdeal W :=
  (Ideal.quotientEquivAlgOfEq ℂ (graphQuotientMap_kernel f hf h0 W).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (graphQuotientMap_surjective f hf h0 W))

/-- Every actual whole graph numerator maps to its SAME literal graph restriction class. -/
theorem graphQuotientAlgEquiv_mk (W : Set (ComplexModel d)) (g : HolGerm (ComplexModel (d+t))) :
    graphQuotientAlgEquiv f hf h0 W (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (graphTrace f hf h0 g) := by
  change Ideal.quotientKerAlgEquivOfSurjective (graphQuotientMap_surjective f hf h0 W)
    (Ideal.quotientEquivAlgOfEq ℂ (graphQuotientMap_kernel f hf h0 W).symm (Ideal.Quotient.mk _ g)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (graphQuotientMap_surjective f hf h0 W) g

end
end Hironaka.HironakaActualHolomorphicGraphIdeal
