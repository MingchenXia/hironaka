import Hironaka.Resolution.HironakaActualIntrinsicLogQuotientDictionary
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicHS

/-! Original structural complex scalars and ALL same-ring derivations on
the TRUE native carrier colimit stalk. BP FIRST:
hironaka-actual-intrinsic-carrier-derivation-transport.tex.
The existing intrinsic stalk algebra is retained; no intrinsic sheaf,
whole-divisor logarithmic or transformation comparison is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualIntrinsicCarrierDerivationTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.RegularLocusDense
  BlowupTowers NormalCrossings BlowupFlatCoordinates GiraudAlong HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
  HironakaActualAnalyticSubspaceIntrinsicHS HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualWholeStalkHolomorphicPullback
  HironakaHolomorphicJetChartInvariance
  HironakaActualIntrinsicLogQuotientDictionary
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactParameterCoefficientIdeals

section OrdinaryDerivations
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

/-- Native complex linear conjugation of an ordinary SAME-ring derivation. -/
def derivationConjugate (e : R ≃ₐ[ℂ] S) (D : Derivation ℂ R R) : Derivation ℂ S S where
  toLinearMap := e.toLinearMap.comp (D.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by simp [LinearMap.comp_apply,Derivation.map_one_eq_zero]
  leibniz' a b := by
    change e (D (e.symm (a*b))) = a * e (D (e.symm b)) + b * e (D (e.symm a))
    rw [map_mul,Derivation.leibniz]
    simp only [smul_eq_mul,map_add,map_mul,
      e.apply_symm_apply]

/-- Conjugation retains all original complex scalars and has its true inverse. -/
def derivationConjugationEquiv (e : R ≃ₐ[ℂ] S) :
    Derivation ℂ R R ≃ₗ[ℂ] Derivation ℂ S S where
  toFun := derivationConjugate e
  invFun := derivationConjugate e.symm
  left_inv D := by
    apply Derivation.ext
    intro a
    simp [derivationConjugate,LinearMap.comp_apply]
  right_inv D := by
    apply Derivation.ext
    intro a
    simp [derivationConjugate,LinearMap.comp_apply]
  map_add' D E := by
    apply Derivation.ext
    intro a
    simp [derivationConjugate,LinearMap.comp_apply,Derivation.add_apply]
  map_smul' c D := by
    apply Derivation.ext
    intro a
    simp [derivationConjugate,LinearMap.comp_apply,Derivation.smul_apply]

/-- EVERY original numerator has the actual conjugate formula. -/
theorem derivationConjugationEquiv_apply (e : R ≃ₐ[ℂ] S) (D : Derivation ℂ R R) (f : S) :
    derivationConjugationEquiv e D f = e (D (e.symm f)) := rfl

/-- The two different ring coefficient actions are related SEMILINEARLY by e. -/
theorem derivationConjugationEquiv_coeff (e : R ≃ₐ[ℂ] S) (a : R) (D : Derivation ℂ R R) :
    derivationConjugationEquiv e (a • D) = e a • derivationConjugationEquiv e D := by
  apply Derivation.ext
  intro f
  simp [derivationConjugationEquiv_apply,Derivation.smul_apply,smul_eq_mul]

end OrdinaryDerivations

section NativeStructuralScalars
variable {n m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) P] [IsComplexManifold m P]

private theorem point_germ_pullback (p : M) (r : HolGerm (ComplexModel 0)) :
    actualHolomorphicGermPullback (n := 0) (m := n)
      (f := fun _ : M => (0 : ComplexModel 0)) contMDiff_const p r =
        HolGerm.constHom (HolGerm.eval r) := by
  induction r using HolGerm.induction_on with
  | h F hF =>
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk,HolGerm.constHom_apply,HolGerm.eval_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (Subsingleton.elim _ _)

/-- The actual native structural scalar is the SAME original chart constant. -/
theorem actual_ambient_structural_constant_chart (p : M) (c : ℂ) :
    actualStalkChartEquiv (n := n) p
      ((ambientPointMap n M).stalkMap p (actualComplexPointStalkEquiv.symm c)) =
        HolGerm.constHom c := by
  change actualStalkChartEquiv (n := n) p
    ((ChartedSpace.locallyRingedSpaceMap (fun _ : M => (0 : ComplexModel 0)) contMDiff_const).stalkMap
      p (actualComplexPointStalkEquiv.symm c)) = _
  rw [actualNativeStalk_chart_pullback,point_germ_pullback]
  have hc : HolGerm.eval (actualStalkChartEquiv (n := 0) (0 : ComplexModel 0)
      (actualComplexPointStalkEquiv.symm c)) = c := actualComplexPointStalkEquiv.apply_symm_apply c
  rw [hc]

/-- It also equals the literal actual germ of the original constant function. -/
theorem actual_ambient_structural_constant_original (p : M) (c : ℂ) :
    (ambientPointMap n M).stalkMap p (actualComplexPointStalkEquiv.symm c) =
      actualOriginalFunctionGerm p (fun _ => c) (holomorphicAt_const c) := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actual_ambient_structural_constant_chart,actualOriginalFunctionGerm_chart]
  rfl

/-- Scoped ambient action from the literal native complex-point map; no global replacement. -/
private def ambientStalkConst (p : M) : ℂ →+* actualComplexStructureStalk (n := n) p :=
  ((ambientPointMap n M).stalkMap p).hom.comp actualComplexPointStalkEquiv.symm.toRingHom

@[instance_reducible]
private def ambientStalkAlgebra (p : M) : Algebra ℂ (actualComplexStructureStalk (n := n) p) :=
  (ambientStalkConst p).toAlgebra
attribute [local instance] ambientStalkAlgebra

private theorem ambient_const_chart (p : M) (c : ℂ) :
    actualStalkChartEquiv (n := n) p (ambientStalkConst p c) = HolGerm.constHom c :=
  actual_ambient_structural_constant_chart p c

private def ambientChartAlgEquiv (p : M) :
    actualComplexStructureStalk (n := n) p ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  { actualStalkChartEquiv (n := n) p with commutes' c := ambient_const_chart p c }

private theorem inclusion_const (N : Set M) (y : N) (c : ℂ) :
    (actualSubspaceInclusion (n := n) N).stalkMap y (ambientStalkConst y.val c) =
      actualSubspaceStalkConst (n := n) N y c := by
  have h := actualSubspacePointMap_stalk_const (n := n) N y c
  change (actualSubspaceInclusion (n := n) N ≫ ambientPointMap n M).stalkMap y
    (actualComplexPointStalkEquiv.symm c) = _ at h
  rw [LocallyRingedSpace.stalkMap_comp] at h
  exact h

/-- The SAME whole native carrier quotient equivalence retains its original structural complex actions. -/
def actualCarrierWholeStalkAlgEquiv (N : Set M) (y : N) :
    ((actualSubspaceSheaf (n := n) N).presheaf.stalk y).carrier ≃ₐ[ℂ]
      (actualComplexStructureStalk (n := n) y.val ⧸
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) y.val) :=
  { actualSubspaceStalkWholeEquiv (n := n) N y with
    commutes' c := by
      change actualSubspaceStalkWholeEquiv (n := n) N y
        (actualSubspaceStalkConst (n := n) N y c) =
          Ideal.Quotient.mk _ (ambientStalkConst y.val c)
      have h := actualSubspaceInclusion_stalk (n := n) N y (ambientStalkConst y.val c)
      rw [inclusion_const] at h
      exact h }

private theorem native_stalk_const {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ) (v : P) (c : ℂ) :
    (ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap v (ambientStalkConst (σ v) c) =
      ambientStalkConst v c := by
  apply (actualStalkChartEquiv (n := m) v).injective
  rw [actualNativeStalk_chart_pullback,ambient_const_chart,ambient_const_chart]
  exact (actualHolomorphicGermPullback hσ v).commutes c

end NativeStructuralScalars

attribute [local instance] ambientStalkAlgebra

section OriginalParameter
variable {n : ℕ} {X : CMfd.{0} n} {x : X}

private def parameterQuotientAlgEquiv
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (k : ℕ)
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) (N : Set X)
    (v : parameterOpen Φ k)
    (e : (actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v)) ≃+*
        actualComplexStructureStalk (n := k) v)
    (he : ∀ r, e (Ideal.Quotient.mk _ r) = parameterStalkMap Φ k hsrc v r) :
    (actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v)) ≃ₐ[ℂ]
        actualComplexStructureStalk (n := k) v :=
  { e with
    commutes' c := by
      change e (Ideal.Quotient.mk _ (ambientStalkConst (parameterMapOn Φ k v) c)) =
        ambientStalkConst v c
      rw [he]
      exact native_stalk_const (parameterMapOn_contMDiff Φ k hsrc) v c }

/-- Only original geometry chooses the SAME actual native carrier-stalk algebra dictionary. -/
theorem exists_actual_intrinsic_carrier_algebra_dictionary
    {N : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (x : X) (hx : x ∈ N) :
    ∃ k ≤ n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n)) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target),
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i j, κ i = some j → j.val < k) ∧ Set.InjOn κ {i | x ∈ E.get i} ∧
      (∀ p ∈ flatDomain Φ,
        (p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k) ∧
        ∀ i, p ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j p = 0) ∧
      (ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hsrc) ≫
        ambientPointMap n X = ambientPointMap k (parameterOpen Φ k)) ∧
      ∀ v : parameterOpen Φ k,
        ∃ hp : parameterMapOn Φ k v ∈ N,
          ∃ e : ((actualSubspaceSheaf (n := n) N).presheaf.stalk ⟨parameterMapOn Φ k v,hp⟩).carrier ≃ₐ[ℂ]
              HolGerm (ComplexModel k),
            ∀ r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v),
              e ((actualSubspaceInclusion (n := n) N).stalkMap ⟨parameterMapOn Φ k v,hp⟩ r) =
                parameterGermPullback Φ k hsrc v r := by
  obtain ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,hpoint,hall⟩ :=
    exists_actual_carrier_quotient_dictionary hE hT x hx
  refine ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,hpoint,?_⟩
  intro v
  have hd := parameterMap_flat_dictionary Φ k hsrc v.val v.property
  have hp : parameterMapOn Φ k v ∈ N := by
    apply ((hcharts _ hd.1).1).mpr
    rw [hd.2]
    exact coordinateInclusion_mem_complexCoordinatePlane v.val
  obtain ⟨_hsurj,_hker,e,he⟩ := hall v
  let eA := actualCarrierWholeStalkAlgEquiv (n := n) N ⟨parameterMapOn Φ k v,hp⟩
  let eB := parameterQuotientAlgEquiv Φ k hsrc N v e he
  let eC := ambientChartAlgEquiv (n := k) v
  refine ⟨hp,eA.trans (eB.trans eC),?_⟩
  intro r
  change actualStalkChartEquiv (n := k) v
    (e (actualSubspaceStalkWholeEquiv (n := n) N ⟨parameterMapOn Φ k v,hp⟩
      ((actualSubspaceInclusion (n := n) N).stalkMap ⟨parameterMapOn Φ k v,hp⟩ r))) = _
  rw [actualSubspaceInclusion_stalk,he]
  rfl

/-- The internally derived ACTUAL native carrier AlgEquiv transports ALL same-ring derivations. -/
theorem exists_actual_intrinsic_carrier_derivation_dictionary
    {N : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (x : X) (hx : x ∈ N) :
    ∃ k ≤ n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n)) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target),
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i j, κ i = some j → j.val < k) ∧ Set.InjOn κ {i | x ∈ E.get i} ∧
      (∀ p ∈ flatDomain Φ,
        (p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k) ∧
        ∀ i, p ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j p = 0) ∧
      (ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hsrc) ≫
        ambientPointMap n X = ambientPointMap k (parameterOpen Φ k)) ∧
      ∀ v : parameterOpen Φ k,
        ∃ hp : parameterMapOn Φ k v ∈ N,
          ∃ e : ((actualSubspaceSheaf (n := n) N).presheaf.stalk ⟨parameterMapOn Φ k v,hp⟩).carrier ≃ₐ[ℂ]
              HolGerm (ComplexModel k),
            (∀ r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v),
              e ((actualSubspaceInclusion (n := n) N).stalkMap ⟨parameterMapOn Φ k v,hp⟩ r) =
                parameterGermPullback Φ k hsrc v r) ∧
            let R := ((actualSubspaceSheaf (n := n) N).presheaf.stalk ⟨parameterMapOn Φ k v,hp⟩).carrier
            ∃ T : Derivation ℂ R R ≃ₗ[ℂ]
                Derivation ℂ (HolGerm (ComplexModel k)) (HolGerm (ComplexModel k)),
              (∀ D f, T D f = e (D (e.symm f))) ∧
              (∀ D a, T D (e a) = e (D a)) ∧
              (∀ δ a, T.symm δ a = e.symm (δ (e a))) ∧
              ∀ a D, T (a • D) = e a • T D := by
  obtain ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,hpoint,hall⟩ :=
    exists_actual_intrinsic_carrier_algebra_dictionary hE hT x hx
  refine ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,hpoint,?_⟩
  intro v
  obtain ⟨hp,e,he⟩ := hall v
  refine ⟨hp,e,he,derivationConjugationEquiv e,?_,?_,?_,?_⟩
  · intro D f
    rfl
  · intro D a
    change e (D (e.symm (e a))) = e (D a)
    rw [e.symm_apply_apply]
  · intro δ a
    rfl
  · exact derivationConjugationEquiv_coeff e

end OriginalParameter
end
end Hironaka.HironakaActualIntrinsicCarrierDerivationTransport
