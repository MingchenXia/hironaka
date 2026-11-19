import Hironaka.Geometry.ProperSteinProjectiveCechCompletedFieldFibre
import Hironaka.Geometry.ProperSteinProjectiveCechFactorCompleteLocalConnected
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # The SAME original projective intrinsic factor is genuinely geometrically connected

Every actual complete flat Noetherian local coefficient model, its original
whole-field-fibre comparison, actual polynomial embedding and original whole
coefficient equivalence are internally produced from ORIGINAL geometry.
No field-fibre connectedness or model certificate is an input. The original
projectivity hypothesis is explicit; the general proper claim is unchanged.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.FactorGeometricallyConnected
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f] [AlgebraicGeometry.IsNoetherian X]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hf : IsProper f) (hnormal : IsNormalScheme X) (hp : IsProjectiveOver (f ≫ p))

include hf hp

/-- ONLY original projective normal proper integral geometry gives connectedness of EVERY original affine field-valued fibre, with arbitrary field and coefficient ring map. -/
theorem affineFactor_fieldFibre_connectedSpace
    (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V)
    {K : Type u} [Field K] (w : Γ(SteinCurveFactor.base f, V) →+* K) :
    ConnectedSpace (pullback (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV)
      (Spec.map (CommRingCat.ofHom w)) : Scheme.{u}) := by
  let A := Γ(SteinCurveFactor.base f, V)
  let g := SteinCurveFactor.baseMap f ≫ p
  let : IsFinite (SteinCurveFactor.baseMap f) := SteinCurveFactor.baseMap_isFinite f hdim p
  let : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  let : Algebra k A := (NormalizationFinite.affineCoefficientMap g ⟨V, hV⟩).toAlgebra
  let : Algebra.FiniteType k A := NormalizationFinite.affineSections_finiteType g ⟨V, hV⟩
  let : Algebra k K := (w.comp (algebraMap k A)).toAlgebra
  let w' : A →ₐ[k] K := { toRingHom := w, commutes' := fun _ => rfl }
  obtain ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, γ, hγs, hγk, hγw⟩ :=
    FlatLocalFieldLift.exists_noetherian_completed_flat_local_lift w'
  let := hFlat
  let := hComplete
  have hc := FactorCompleteLocalConnected.affineFlat_maximalClosedFiber_connectedSpace
    f hdim p hf hnormal hp V hV B
  let e := CompletedFieldFibre.closedFibreIso w γ hγs hγk hγw
    (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV)
  exact e.hom.homeomorph.connectedSpace_iff.mp hc

/-- The SAME actual original affine-coordinate factor satisfies STANDARD native geometric connectedness. -/
theorem affineFactor_geometricallyConnected
    (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V) :
    GeometricallyConnected (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV) := by
  constructor
  refine (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} => ConnectedSpace Y)).mpr ?_
  intro K _ _
  exact affineFactor_fieldFibre_connectedSpace f hdim p hf hnormal hp V hV
    (algebraMap Γ(SteinCurveFactor.base f, V) K)

/-- The literal SAME original affine-open restriction retains native geometric connectedness through the actual affine isomorphism square. -/
theorem affineRestriction_geometricallyConnected
    (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V) :
    GeometricallyConnected (SteinCurveFactor.factor f hdim p hnormal ∣_ V) := by
  let g := SteinCurveFactor.factor f hdim p hnormal
  let q := ProperSteinFlatSections.affineFactor f hdim p hnormal V hV
  have H : IsPullback (𝟙 ((g ⁻¹ᵁ V).toScheme)) (g ∣_ V) q hV.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [q, g, ProperSteinFlatSections.affineFactor]⟩
  exact MorphismProperty.of_isPullback H (affineFactor_geometricallyConnected f hdim p hf hnormal hp V hV)

/-- ORIGINAL projective normal proper integral geometry DERIVES STANDARD native geometric connectedness of the SAME whole original intrinsic factor. -/
theorem factor_geometricallyConnected :
    GeometricallyConnected (SteinCurveFactor.factor f hdim p hnormal) := by
  constructor
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := SteinCurveFactor.base f) (x := x) (U := ⊤) (by trivial)
  refine ⟨V, hxV, ?_⟩
  exact (affineRestriction_geometricallyConnected f hdim p hf hnormal hp V hV).geometrically_connectedSpace

/-- EVERY original field-spectrum pullback of the SAME whole original factor is an actual native connected space. -/
theorem factor_fieldFibre_connectedSpace {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ SteinCurveFactor.base f) :
    ConnectedSpace (pullback (SteinCurveFactor.factor f hdim p hnormal) y : Scheme.{u}) :=
  (factor_geometricallyConnected f hdim p hf hnormal hp).geometrically_connectedSpace
    y _ _ (.of_hasPullback _ _)

/-- EVERY native ORIGINAL point fibre of the SAME whole factor is genuinely connected. -/
theorem factor_fiber_connectedSpace (s : SteinCurveFactor.base f) :
    ConnectedSpace ((SteinCurveFactor.factor f hdim p hnormal).fiber s) := by
  let := factor_geometricallyConnected f hdim p hf hnormal hp
  infer_instance

/-- EVERY native ORIGINAL residue-field fibre of the SAME factor is geometrically connected over its OWN original residue field. -/
theorem factor_fiber_geometricallyConnected (s : SteinCurveFactor.base f) :
    GeometricallyConnected ((SteinCurveFactor.factor f hdim p hnormal).fiberToSpecResidueField s) := by
  let := factor_geometricallyConnected f hdim p hf hnormal hp
  infer_instance

end Hironaka.Geometry.ProperSteinProjectiveCech.FactorGeometricallyConnected
