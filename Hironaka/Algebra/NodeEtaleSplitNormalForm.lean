import Hironaka.Algebra.NodeEtaleSplitReindex
import Hironaka.Algebra.NodeEtaleCoefficientCollapse
import Hironaka.Algebra.NodeEtaleNonsplitNormalForm
import Hironaka.Algebra.NodeFieldIsotropicQuadratic
import Hironaka.Algebra.NodeFlatPresentation

/-! # The original completed base gives the actual split normal form

Only the native original residue bijection, the original closed-fibre model
and an actual nonzero isotropic tangent are inputs. The same constructed
coefficient ring is collapsed internally; no total-space model is assumed.
-/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleSplitNormalForm

open IsLocalRing MvPowerSeries CompletionRegularityBasics CompletionLocalMap
  NodeGeometricCompletion NodeGeometricCompletionOriginalFiberSection
  NodeEtaleCompletedClosedFiber NodeEtaleCompletedCoefficientAgreement NodeNonsplit
  NodeEtaleSplitReindex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

attribute [local instance] CompletionFlatMap.completedAlgebra baseResidueAlgebra

local notation "F" => FiberRing A B
local notation "Cf" => Completion F

local instance originalFiber_local : IsLocalRing F :=
  CompletionIdealQuotient.quotientLocalRing _ (closedFiberIdeal_le_maximalIdeal (algebraMap A B))

section Upper

variable [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

local notation "T" => CompletedCoefficientRing A B
local instance : Algebra T (Completion B) := upperCompletedAlgebra A B
local instance : IsLocalHom (algebraMap T (Completion B)) := completedCoefficientMap_local A B
local instance : Algebra (ResidueField T) (NodeFlatPresentation.ClosedFiber T (Completion B)) :=
  NodeFlatPresentation.closedFiberAlgebra T (Completion B)

variable (q : Quadratic (ResidueField B)) (v0 v1 : ResidueField B)
  (hzero : q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0)

include v0 v1 hzero hne

/-- The SAME actual upper closed fibre is split by the genuine original isotropic tangent. -/
def upperSplitModel (e : letI := pointFieldAlgebra A B
    QuadraticNode q ≃ₐ[ResidueField B] Cf) :
    NodeFlatPresentation.SplitNode (ResidueField T) ≃ₐ[ResidueField T]
      NodeFlatPresentation.ClosedFiber T (Completion B) := by
  letI := pointFieldAlgebra A B
  letI := upperResidueAlgebra A B
  let E := NodeFieldIsotropicQuadratic.quotientEquiv q v0 v1 hzero hne
  refine
    { (((splitEquiv (upperOriginalResidueEquiv A B)).trans E.symm.toRingEquiv).trans
        e.toRingEquiv).trans (upperClosedFiberEquiv A B).symm.toRingEquiv with
      commutes' := ?_ }
  intro a
  apply (upperClosedFiberEquiv A B).injective
  change upperClosedFiberEquiv A B ((upperClosedFiberEquiv A B).symm
    (e (E.symm (splitEquiv (upperOriginalResidueEquiv A B)
      (algebraMap (ResidueField T) (NodeFlatPresentation.SplitNode (ResidueField T)) a))))) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  change e (E.symm (splitEquiv (upperOriginalResidueEquiv A B)
    (Ideal.Quotient.mk _ (C a)))) = upperResidueMap A B a
  rw [splitEquiv_coefficient]
  change e (E.symm (algebraMap (ResidueField B)
    (NodeFlatPresentation.SplitNode (ResidueField B)) (upperOriginalResidueEquiv A B a))) = _
  rw [AlgEquiv.commutes, AlgEquiv.commutes]
  exact (upperResidueMap_pointFieldSection A B a).symm

variable [Module.Flat A B] [Algebra.EssFiniteType A B]

local instance : Module.Flat T (Completion B) := upperCompletedAlgebra_flat A B

/-- The actual upper split parameter is constructed by native flat presentation and Morse. -/
def upperParameter (e : letI := pointFieldAlgebra A B
    QuadraticNode q ≃ₐ[ResidueField B] Cf) : T :=
  NodeFlatPresentation.normalFormParameter T (Completion B)
    (upperSplitModel A B q v0 v1 hzero hne e)

/-- The constructed parameter is in the SAME native upper maximal ideal. -/
theorem upperParameter_mem (e : letI := pointFieldAlgebra A B
    QuadraticNode q ≃ₐ[ResidueField B] Cf) :
    upperParameter A B q v0 v1 hzero hne e ∈ maximalIdeal T :=
  NodeFlatPresentation.normalFormParameter_mem T (Completion B)
    (upperSplitModel A B q v0 v1 hzero hne e)

/-- The SAME original completed target has the actual split normal form over T. -/
def upperNormalFormEquiv (e : letI := pointFieldAlgebra A B
    QuadraticNode q ≃ₐ[ResidueField B] Cf) :
    Completion B ≃ₐ[T] ParameterNode T (upperParameter A B q v0 v1 hzero hne e) :=
  NodeFlatPresentation.normalFormEquiv T (Completion B)
    (upperSplitModel A B q v0 v1 hzero hne e)

/-- EVERY upper coefficient follows precisely the actual original Hensel map. -/
theorem upperNormalFormEquiv_coefficient (e : letI := pointFieldAlgebra A B
    QuadraticNode q ≃ₐ[ResidueField B] Cf) (t : T) :
    upperNormalFormEquiv A B q v0 v1 hzero hne e (completedCoefficientMap A B t) =
      Ideal.Quotient.mk _ (C t) :=
  (upperNormalFormEquiv A B q v0 v1 hzero hne e).commutes t

end Upper

variable [Module.Flat A B] [Algebra.EssFiniteType A B]

/-- Native ORIGINAL residue identity and actual isotropy internally give the SAME
completed target over the unchanged original completed base, with every coefficient. -/
theorem exists_split_normal_form
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    letI := NodeEtaleCoefficientCollapse.originalResidue_finite A B hκ
    letI := NodeEtaleCoefficientCollapse.originalResidue_separable A B hκ
    ∀ (q : Quadratic (ResidueField B)) (v0 v1 : ResidueField B)
      (_hzero : q.value v0 v1 = 0) (_hne : v0 ≠ 0 ∨ v1 ≠ 0)
      (_e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] Cf),
      ∃ h : Completion A, ∃ E : Completion B ≃ₐ[Completion A] ParameterNode (Completion A) h,
        h ∈ maximalIdeal (Completion A) ∧
        (∀ a : Completion A, E (completionMap (algebraMap A B) a) =
          Ideal.Quotient.mk _ (C a)) ∧
        (∀ a : A, E (algebraMap B (Completion B) (algebraMap A B a)) =
          Ideal.Quotient.mk _ (C (algebraMap A (Completion A) a))) := by
  let := NodeEtaleCoefficientCollapse.originalResidue_finite A B hκ
  let := NodeEtaleCoefficientCollapse.originalResidue_separable A B hκ
  let := upperCompletedAlgebra A B
  intro q v0 v1 hzero hne e
  let hT := upperParameter A B q v0 v1 hzero hne e
  let ET := upperNormalFormEquiv A B q v0 v1 hzero hne e
  let χ := NodeEtaleCoefficientCollapse.collapseEquiv A B hκ
  let h := χ hT
  let E := ET.toRingEquiv.trans (parameterEquiv χ.toRingEquiv hT)
  have hcoeff (a : Completion A) : E (completionMap (algebraMap A B) a) =
      Ideal.Quotient.mk _ (C a) := by
    have ha : completionMap (algebraMap A B) a = completedCoefficientMap A B
        (algebraMap (Completion A) (CompletedCoefficientRing A B) a) :=
      (completedCoefficientMap A B).commutes a |>.symm
    change parameterEquiv χ.toRingEquiv hT (ET (completionMap (algebraMap A B) a)) = _
    rw [ha, upperNormalFormEquiv_coefficient, parameterEquiv_coefficient]
    exact congrArg (fun b => Ideal.Quotient.mk _ (C b))
      (NodeEtaleCoefficientCollapse.collapseEquiv_coefficient A B hκ a)
  let EA : Completion B ≃ₐ[Completion A] ParameterNode (Completion A) h :=
    AlgEquiv.ofRingEquiv (f := E) hcoeff
  have hmem : h ∈ maximalIdeal (Completion A) := by
    let : IsLocalHom χ.toRingHom :=
      CompletionLocalMap.instIsLocalHomRingEquivToRingHom χ.toRingEquiv
    exact (map_maximalIdeal_le χ.toRingHom) (Ideal.mem_map_of_mem χ.toRingHom
      (upperParameter_mem A B q v0 v1 hzero hne e))
  refine ⟨h, EA, hmem, hcoeff, ?_⟩
  intro a
  rw [← completionMap_algebraMap (algebraMap A B) a]
  exact hcoeff _

end Hironaka.Algebra.NodeEtaleSplitNormalForm
