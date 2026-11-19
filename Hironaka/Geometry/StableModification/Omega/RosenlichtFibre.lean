/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.StableModification.Omega.RosenlichtEtale

/-!
# The geometric fibre of an étale node chart

Let `R → O` be étale, `c ∈ O`, `N = O[u,v]/(uv - c)` (`Node O c`) and `N → A` étale: an étale
node chart of a nodal curve (`Omega.EtaleNodeChart`, with `R = Γ(S, V)`, `A = Γ(X, W)`). For a
ring map `R → K` the fibre chart is `K ⊗_R A`. This file shows that the fibre chart is again
étale over a node, namely over `Node P c̄` with `P = K ⊗_R O` and `c̄ = 1 ⊗ c`:

* `fibreNodeEquiv : Node P c̄ ≃+* K ⊗_R N` (base change of the node; the coordinates go to
  `1 ⊗ xᵢ`, `fibreNodeEquiv_coordinate`);
* `etale_tensorNode`: `K ⊗_R N → K ⊗_R A` is étale (the square `N → A`, `K ⊗_R N → K ⊗_R A` is a
  pushout, `isPushout_tensorNode`, via `Algebra.IsPushout.comp_iff`);
* `fibreNodeHom : Node P c̄ →+* K ⊗_R A`, `etale_fibreNodeHom`, `fibreNodeHom_coordinate`,
  `fibreNodeHom_cbar` (`c̄ ↦ ū v̄`);
* `exists_mul_cbar_eq_zero`: if `K` is an algebraically closed field and `R → O` is étale, then
  for every prime `𝔔` of `K ⊗_R A` containing `ū v̄` (`ū = 1 ⊗ u`, `v̄ = 1 ⊗ v`) there is `s ∈ P`
  killing `c̄` whose image in `K ⊗_R A` is not in `𝔔` (`P_𝔮` is a field);
* on the localization `A'` of `K ⊗_R A` at the image of `s` (section `Localized`), `c̄` vanishes
  and `A'` is étale over `Node P c̄` (`localizedNode_cbar`, `localizedNode_etale`), so Rosenlicht's
  description applies near every node of the geometric fibre: `isNodeBranching_localized`,
  `smul_D_bijective_localized`, `span_D_branch_localized`, `rosenlicht_injective_localized`,
  `residue₁_eq_zero_iff_localized`.

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2,
properties (a), (b) (`semi-stable.tex`, T:1700–1704). Blueprint `sm-omega-base-change.tex`,
`lem:sm-node-base-change`, `lem:sm-fibre-chart-etale`, `lem:sm-kill-node-parameter`,
`thm:sm-rosenlicht-fibre`.
-/

noncomputable section

universe u

namespace Hironaka.StableModification.Omega.Rosenlicht

open Hironaka.Algebra Hironaka.Algebra.NodeBlowupChart
open MvPolynomial TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section NodeBaseChange

variable {R O : Type u} [CommRing R] [CommRing O] [Algebra R O] (c : O)
  (K : Type u) [CommRing K] [Algebra R K]

/-- The node parameter `c̄ = 1 ⊗ c` of the base change `P = K ⊗_R O`. -/
abbrev cbar : K ⊗[R] O := algebraMap O (K ⊗[R] O) c

/-- `O → K ⊗_R O → Node P c̄` on the node: `N = O[u,v]/(uv - c) → P[u,v]/(uv - c̄)`. -/
def baseNode : Node O c →+* Node (K ⊗[R] O) (cbar c K) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap O (K ⊗[R] O)))) (by
      intro a ha
      rw [NodeChart.uChartIdeal] at ha
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [NodeChart.uChartIdeal]
      simp only [map_sub, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
      exact Ideal.mem_span_singleton_self _)

theorem baseNode_mk (p : MvPolynomial (Fin 2) O) :
    baseNode c K (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap O (K ⊗[R] O)) p) :=
  rfl

/-- `K ⊗_R O → K ⊗_R N`. -/
def tensorCoeff : K ⊗[R] O →+* K ⊗[R] Node O c :=
  (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R O (Node O c))).toRingHom

theorem tensorCoeff_tmul (k : K) (o : O) :
    tensorCoeff c K (k ⊗ₜ[R] o) = k ⊗ₜ[R] algebraMap O (Node O c) o :=
  rfl

/-- `P[u,v]/(uv - c̄) → K ⊗_R N`, `xᵢ ↦ 1 ⊗ xᵢ`. -/
def fibreNodeToTensor : Node (K ⊗[R] O) (cbar c K) →+* K ⊗[R] Node O c :=
  Ideal.Quotient.lift (NodeChart.uChartIdeal (K ⊗[R] O) (cbar c K))
    (MvPolynomial.eval₂Hom (tensorCoeff c K) (fun i => (1 : K) ⊗ₜ[R] coordinate c i)) (by
      intro a ha
      change a ∈ Ideal.span _ at ha
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have hprod : coordinate c 0 * coordinate c 1 = algebraMap O (Node O c) c :=
        NodeDomain.nodeCoordinateProduct c
      rw [map_mul, map_sub, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_C, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hprod]
      rw [show cbar c K = (1 : K) ⊗ₜ[R] c from rfl, tensorCoeff_tmul, sub_self]
      exact mul_zero (M₀ := K ⊗[R] Node O c) _)

/-- `K ⊗_R N → P[u,v]/(uv - c̄)`. -/
def tensorToFibreNode : K ⊗[R] Node O c →+* Node (K ⊗[R] O) (cbar c K) :=
  (Algebra.TensorProduct.lift (Algebra.ofId K (Node (K ⊗[R] O) (cbar c K)))
    { (baseNode c K) with
      commutes' := fun r => by
        change baseNode c K (algebraMap R (Node O c) r) = _
        rw [IsScalarTower.algebraMap_apply R O (Node O c), show algebraMap O (Node O c) =
          (Ideal.Quotient.mk _).comp MvPolynomial.C from rfl, RingHom.comp_apply, baseNode_mk,
          MvPolynomial.map_C, ← IsScalarTower.algebraMap_apply R O (K ⊗[R] O)]
        rfl }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tensorToFibreNode_tmul (k : K) (n : Node O c) :
    tensorToFibreNode c K (k ⊗ₜ[R] n) =
      algebraMap K (Node (K ⊗[R] O) (cbar c K)) k * baseNode c K n := by
  simp only [tensorToFibreNode, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul]
  rfl

theorem fibreNodeToTensor_mk (p : MvPolynomial (Fin 2) (K ⊗[R] O)) :
    fibreNodeToTensor c K (Ideal.Quotient.mk _ p) =
      MvPolynomial.eval₂Hom (tensorCoeff c K) (fun i => (1 : K) ⊗ₜ[R] coordinate c i) p :=
  rfl

theorem fibreNodeToTensor_coordinate (i : Fin 2) :
    fibreNodeToTensor c K (coordinate (cbar c K) i) = (1 : K) ⊗ₜ[R] coordinate c i := by
  change fibreNodeToTensor c K (Ideal.Quotient.mk _ (X i)) = _
  rw [fibreNodeToTensor_mk, MvPolynomial.eval₂Hom_X']

theorem fibreNodeToTensor_baseNode (n : Node O c) :
    fibreNodeToTensor c K (baseNode c K n) = (1 : K) ⊗ₜ[R] n := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective n
  induction p using MvPolynomial.induction_on with
  | C o =>
    rw [baseNode_mk, MvPolynomial.map_C, fibreNodeToTensor_mk, MvPolynomial.eval₂Hom_C,
      show algebraMap O (K ⊗[R] O) o = (1 : K) ⊗ₜ[R] o from rfl, tensorCoeff_tmul]
    rfl
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq, TensorProduct.tmul_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, baseNode_mk, MvPolynomial.map_X, fibreNodeToTensor_mk,
      MvPolynomial.eval₂Hom_X', Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl

theorem fibreNodeToTensor_algebraMap (k : K) :
    fibreNodeToTensor c K (algebraMap K (Node (K ⊗[R] O) (cbar c K)) k) =
      k ⊗ₜ[R] (1 : Node O c) := by
  change fibreNodeToTensor c K (Ideal.Quotient.mk _ (MvPolynomial.C (k ⊗ₜ[R] (1 : O)))) = _
  rw [fibreNodeToTensor_mk, MvPolynomial.eval₂Hom_C, tensorCoeff_tmul, map_one]

theorem fibreNodeToTensor_tensorToFibreNode (x : K ⊗[R] Node O c) :
    fibreNodeToTensor c K (tensorToFibreNode c K x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul k n =>
    rw [tensorToFibreNode_tmul, map_mul, fibreNodeToTensor_algebraMap, fibreNodeToTensor_baseNode,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tensorToFibreNode_tensorCoeff (p : K ⊗[R] O) :
    tensorToFibreNode c K (tensorCoeff c K p) =
      Ideal.Quotient.mk (NodeChart.uChartIdeal (K ⊗[R] O) (cbar c K)) (MvPolynomial.C p) := by
  induction p using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul k o =>
    rw [tensorCoeff_tmul, tensorToFibreNode_tmul,
      show algebraMap O (Node O c) o = Ideal.Quotient.mk _ (MvPolynomial.C o) from rfl,
      baseNode_mk, MvPolynomial.map_C]
    change Ideal.Quotient.mk _ (MvPolynomial.C (k ⊗ₜ[R] (1 : O))) *
      Ideal.Quotient.mk _ (MvPolynomial.C ((1 : K) ⊗ₜ[R] o)) = _
    rw [← map_mul, ← MvPolynomial.C_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem tensorToFibreNode_fibreNodeToTensor (x : Node (K ⊗[R] O) (cbar c K)) :
    tensorToFibreNode c K (fibreNodeToTensor c K x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C p =>
    rw [fibreNodeToTensor_mk, MvPolynomial.eval₂Hom_C, tensorToFibreNode_tensorCoeff]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, fibreNodeToTensor_mk, MvPolynomial.eval₂Hom_X',
      tensorToFibreNode_tmul, map_one, one_mul,
      show coordinate c i = Ideal.Quotient.mk (NodeChart.uChartIdeal O c) (X i) from rfl,
      baseNode_mk, MvPolynomial.map_X]

/-- **Base change of the node**: `P[u,v]/(uv - c̄) ≅ K ⊗_R O[u,v]/(uv - c)`, `P = K ⊗_R O`. -/
def fibreNodeEquiv : Node (K ⊗[R] O) (cbar c K) ≃+* K ⊗[R] Node O c :=
  RingEquiv.ofRingHom (fibreNodeToTensor c K) (tensorToFibreNode c K)
    (RingHom.ext (fibreNodeToTensor_tensorToFibreNode c K))
    (RingHom.ext (tensorToFibreNode_fibreNodeToTensor c K))

theorem fibreNodeEquiv_coordinate (i : Fin 2) :
    fibreNodeEquiv c K (coordinate (cbar c K) i) = (1 : K) ⊗ₜ[R] coordinate c i :=
  fibreNodeToTensor_coordinate c K i

end NodeBaseChange

section FibreChart

variable (R : Type u) {O : Type u} [CommRing R] [CommRing O] [Algebra R O] (c : O)
  (K : Type u) [CommRing K] [Algebra R K]
  (A : Type u) [CommRing A] [Algebra (Node O c) A] [Algebra R A] [IsScalarTower R (Node O c) A]

/-- `K ⊗_R N → K ⊗_R A`. -/
def tensorNodeMap : K ⊗[R] Node O c →ₐ[K] K ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R (Node O c) A)

/-- The algebra `K ⊗_R N → K ⊗_R A`. -/
abbrev tensorNodeAlgebra : Algebra (K ⊗[R] Node O c) (K ⊗[R] A) :=
  (tensorNodeMap R c K A).toRingHom.toAlgebra

/-- `N → A → K ⊗_R A`. -/
abbrev nodeTensorAlgebra : Algebra (Node O c) (K ⊗[R] A) :=
  ((algebraMap A (K ⊗[R] A)).comp (algebraMap (Node O c) A)).toAlgebra

/-- **The fibre chart is a base change of the node chart**: for algebra structures compatible
with `tensorNodeMap`, the square `N → A`, `K ⊗_R N → K ⊗_R A` is a pushout. -/
theorem isPushout_tensorNode [Algebra (K ⊗[R] Node O c) (K ⊗[R] A)]
    [Algebra (Node O c) (K ⊗[R] A)] [IsScalarTower (Node O c) A (K ⊗[R] A)]
    [IsScalarTower (Node O c) (K ⊗[R] Node O c) (K ⊗[R] A)]
    [IsScalarTower R (K ⊗[R] Node O c) (K ⊗[R] A)] [IsScalarTower K (K ⊗[R] Node O c) (K ⊗[R] A)] :
    Algebra.IsPushout (Node O c) A (K ⊗[R] Node O c) (K ⊗[R] A) :=
  (Algebra.IsPushout.comp_iff R (Node O c) K (K ⊗[R] Node O c) (T := A)
    (T' := K ⊗[R] A)).mp inferInstance

/-- **Étaleness ascends to the fibre chart**: `K ⊗_R N → K ⊗_R A` is étale (hence flat and
formally étale). -/
theorem etale_tensorNode [Algebra.Etale (Node O c) A] :
    letI := tensorNodeAlgebra R c K A
    Algebra.Etale (K ⊗[R] Node O c) (K ⊗[R] A) := by
  let := tensorNodeAlgebra R c K A
  let := nodeTensorAlgebra R c K A
  have : IsScalarTower (Node O c) A (K ⊗[R] A) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (Node O c) (K ⊗[R] Node O c) (K ⊗[R] A) :=
    IsScalarTower.of_algebraMap_eq (S := K ⊗[R] Node O c) (A := K ⊗[R] A) fun n => by
      change (1 : K) ⊗ₜ[R] algebraMap (Node O c) A n =
        tensorNodeMap R c K A ((1 : K) ⊗ₜ[R] n)
      rw [tensorNodeMap, Algebra.TensorProduct.map_tmul]
      rfl
  have : IsScalarTower R (K ⊗[R] Node O c) (K ⊗[R] A) :=
    IsScalarTower.of_algebraMap_eq (S := K ⊗[R] Node O c) (A := K ⊗[R] A) fun r =>
      (((tensorNodeMap R c K A).restrictScalars R).commutes r).symm
  have : IsScalarTower K (K ⊗[R] Node O c) (K ⊗[R] A) :=
    IsScalarTower.of_algebraMap_eq (S := K ⊗[R] Node O c) (A := K ⊗[R] A) fun k =>
      ((tensorNodeMap R c K A).commutes k).symm
  have := isPushout_tensorNode R c K A
  have h := RingHom.Etale.isStableUnderBaseChange (Node O c) A (K ⊗[R] Node O c) (K ⊗[R] A)
    (RingHom.etale_algebraMap.mpr inferInstance)
  exact RingHom.etale_algebraMap.mp h

end FibreChart

section FibreNode

variable (R : Type u) {O : Type u} [CommRing R] [CommRing O] [Algebra R O] (c : O)
  (K : Type u) [CommRing K] [Algebra R K]
  (A : Type u) [CommRing A] [Algebra (Node O c) A] [Algebra R A] [IsScalarTower R (Node O c) A]

/-- **The node structure of the fibre chart**: `P[u,v]/(uv - c̄) → K ⊗_R A`, `P = K ⊗_R O`,
`c̄ = 1 ⊗ c`. -/
def fibreNodeHom : Node (K ⊗[R] O) (cbar c K) →+* K ⊗[R] A :=
  (tensorNodeMap R c K A).toRingHom.comp (fibreNodeToTensor c K)

theorem fibreNodeHom_coordinate (i : Fin 2) :
    fibreNodeHom R c K A (coordinate (cbar c K) i) =
      (1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c i) := by
  change tensorNodeMap R c K A (fibreNodeToTensor c K (coordinate (cbar c K) i)) = _
  rw [fibreNodeToTensor_coordinate, tensorNodeMap, Algebra.TensorProduct.map_tmul]
  rfl

theorem fibreNodeHom_algebraMap (k : K) :
    fibreNodeHom R c K A (algebraMap K (Node (K ⊗[R] O) (cbar c K)) k) =
      algebraMap K (K ⊗[R] A) k := by
  change tensorNodeMap R c K A (fibreNodeToTensor c K (algebraMap K _ k)) = _
  rw [fibreNodeToTensor_algebraMap, tensorNodeMap, Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- **The fibre chart is étale over `P[u,v]/(uv - c̄)`.** -/
theorem etale_fibreNodeHom [Algebra.Etale (Node O c) A] : (fibreNodeHom R c K A).Etale := by
  have hinj : Function.Injective (fibreNodeToTensor (R := R) c K) :=
    Function.LeftInverse.injective (g := tensorToFibreNode (R := R) c K)
      (tensorToFibreNode_fibreNodeToTensor (R := R) c K)
  have hsurj : Function.Surjective (fibreNodeToTensor (R := R) c K) :=
    Function.RightInverse.surjective (g := tensorToFibreNode (R := R) c K)
      (fibreNodeToTensor_tensorToFibreNode (R := R) c K)
  have h1 : RingHom.Etale (R := Node (K ⊗[R] O) (cbar c K)) (S := K ⊗[R] Node O c)
      (fibreNodeToTensor c K) :=
    RingHom.Etale.of_bijective ⟨hinj, hsurj⟩
  have h2 : RingHom.Etale (R := K ⊗[R] Node O c) (S := K ⊗[R] A)
      (tensorNodeMap R c K A).toRingHom := by
    let := tensorNodeAlgebra R c K A
    exact RingHom.etale_algebraMap.mpr (etale_tensorNode R c K A)
  exact RingHom.Etale.stableUnderComposition _ _ h1 h2

/-- The image of `c̄` in the fibre chart is `ū v̄`. -/
theorem fibreNodeHom_cbar :
    fibreNodeHom R c K A (algebraMap (K ⊗[R] O) (Node (K ⊗[R] O) (cbar c K)) (cbar c K)) =
      ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0)) *
        ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 1)) := by
  rw [← coordinate_mul_coordinate, map_mul, fibreNodeHom_coordinate, fibreNodeHom_coordinate]

/-- **Killing the node parameter near a node of the geometric fibre.** Let `K` be an
algebraically closed field and `R → O` étale. For every prime `𝔔` of `K ⊗_R A` containing
`ū v̄` (`ū = 1 ⊗ u`, `v̄ = 1 ⊗ v`; e.g. a node of the geometric fibre) there is `s ∈ P = K ⊗_R O` with `s c̄ = 0` whose image in `K ⊗_R A`
is not in `𝔔`. (The local ring of `P` at `𝔮 = 𝔔 ∩ P` is a field, `P` being étale over `K = K̄`.) -/
theorem exists_mul_cbar_eq_zero {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
    [Algebra.Etale R O] (𝔔 : Ideal (K ⊗[R] A)) [𝔔.IsPrime]
    (huv : ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0)) *
      ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 1)) ∈ 𝔔) :
    ∃ s : K ⊗[R] O, s * cbar c K = 0 ∧
      fibreNodeHom R c K A (algebraMap (K ⊗[R] O) (Node (K ⊗[R] O) (cbar c K)) s) ∉ 𝔔 := by
  set φ : K ⊗[R] O →+* K ⊗[R] A :=
    (fibreNodeHom R c K A).comp (algebraMap (K ⊗[R] O) (Node (K ⊗[R] O) (cbar c K)))
  let 𝔮 : Ideal (K ⊗[R] O) := 𝔔.comap φ
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime φ 𝔔
  have hc : cbar c K ∈ 𝔮 := by
    change φ (cbar c K) ∈ 𝔔
    change fibreNodeHom R c K A _ ∈ 𝔔
    rw [fibreNodeHom_cbar]
    exact huv
  have : Algebra.FormallyUnramified K (Localization.AtPrime 𝔮) :=
    Algebra.FormallyUnramified.comp K (K ⊗[R] O) (Localization.AtPrime 𝔮)
  have : Algebra.EssFiniteType K (Localization.AtPrime 𝔮) :=
    Algebra.EssFiniteType.comp K (K ⊗[R] O) (Localization.AtPrime 𝔮)
  have hfield : IsField (Localization.AtPrime 𝔮) :=
    Algebra.FormallyUnramified.isField_of_isAlgClosed_of_isLocalRing K _
  have hmax := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔮) 𝔮
    (cbar c K)).mpr hc
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield, Ideal.mem_bot] at hmax
  obtain ⟨⟨s, hs⟩, hsc⟩ :=
    (IsLocalization.map_eq_zero_iff 𝔮.primeCompl (Localization.AtPrime 𝔮) (cbar c K)).mp hmax
  exact ⟨s, hsc, hs⟩

end FibreNode

section Localized

/-! ### Rosenlicht's description near a node of the geometric fibre

Let `s ∈ P = K ⊗_R O` kill `c̄` (`exists_mul_cbar_eq_zero`) and `A'` the localization of `K ⊗_R A`
at the image `t` of `s`. Then `A'` is étale over `P[u,v]/(uv - c̄)` and `c̄` vanishes on `A'`, so
the results of `Omega/RosenlichtEtale.lean` apply to `ū, v̄ ∈ A'`. -/

variable (R : Type u) {O : Type u} [CommRing R] [CommRing O] [Algebra R O] (c : O)
  (K : Type u) [CommRing K] [Algebra R K]
  (A : Type u) [CommRing A] [Algebra (Node O c) A] [Algebra R A] [IsScalarTower R (Node O c) A]
  (s : K ⊗[R] O) (A' : Type u) [CommRing A'] [Algebra (K ⊗[R] A) A']
  [hA' : IsLocalization.Away (fibreNodeHom R c K A (algebraMap _ (Node (K ⊗[R] O) (cbar c K)) s)) A']

/-- The node structure `P[u,v]/(uv - c̄) → A'` of the localized fibre chart. -/
abbrev localizedNodeAlgebra : Algebra (Node (K ⊗[R] O) (cbar c K)) A' :=
  ((algebraMap (K ⊗[R] A) A').comp (fibreNodeHom R c K A)).toAlgebra

theorem localizedNode_coordinate (i : Fin 2) :
    letI := localizedNodeAlgebra R c K A A'
    algebraMap (Node (K ⊗[R] O) (cbar c K)) A' (coordinate (cbar c K) i) =
      algebraMap (K ⊗[R] A) A' ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c i)) := by
  let := localizedNodeAlgebra R c K A A'
  change algebraMap (K ⊗[R] A) A' (fibreNodeHom R c K A _) = _
  rw [fibreNodeHom_coordinate]

include hA'

/-- The node parameter vanishes on the localized fibre chart. -/
theorem localizedNode_cbar (hs : s * cbar c K = 0) :
    letI := localizedNodeAlgebra R c K A A'
    algebraMap (Node (K ⊗[R] O) (cbar c K)) A'
      (algebraMap (K ⊗[R] O) (Node (K ⊗[R] O) (cbar c K)) (cbar c K)) = 0 := by
  let := localizedNodeAlgebra R c K A A'
  have hu := IsLocalization.Away.algebraMap_isUnit (S := A')
    (fibreNodeHom R c K A (algebraMap _ (Node (K ⊗[R] O) (cbar c K)) s))
  have h0 : algebraMap (K ⊗[R] A) A' (fibreNodeHom R c K A (algebraMap _ _ s)) *
      algebraMap (Node (K ⊗[R] O) (cbar c K)) A'
        (algebraMap (K ⊗[R] O) (Node (K ⊗[R] O) (cbar c K)) (cbar c K)) = 0 := by
    change algebraMap (K ⊗[R] A) A' _ * algebraMap (K ⊗[R] A) A' (fibreNodeHom R c K A _) = 0
    rw [← map_mul, ← map_mul, ← map_mul, hs, map_zero, map_zero, map_zero]
  exact hu.mul_right_eq_zero.mp h0

/-- The localized fibre chart is étale over `P[u,v]/(uv - c̄)`. -/
theorem localizedNode_etale [Algebra.Etale (Node O c) A] :
    letI := localizedNodeAlgebra R c K A A'
    Algebra.Etale (Node (K ⊗[R] O) (cbar c K)) A' := by
  let := localizedNodeAlgebra R c K A A'
  have h1 := etale_fibreNodeHom R c K A
  have h2 : RingHom.Etale (R := K ⊗[R] A) (S := A') (algebraMap (K ⊗[R] A) A') :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway
      (fibreNodeHom R c K A (algebraMap _ (Node (K ⊗[R] O) (cbar c K)) s)))
  exact RingHom.etale_algebraMap.mp (RingHom.Etale.stableUnderComposition _ _ h1 h2)

/-- **Near a node of the geometric fibre, `ū, v̄` branch like a node**: on the localized fibre
chart `A'`, `ū v̄ = 0`, `ū` is a non-zero-divisor modulo `v̄` and `v̄` modulo `ū`. -/
theorem isNodeBranching_localized [Algebra.Etale (Node O c) A] (hs : s * cbar c K = 0) :
    IsNodeBranching
      (algebraMap (K ⊗[R] A) A' ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0)))
      (algebraMap (K ⊗[R] A) A' ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 1))) := by
  let := localizedNodeAlgebra R c K A A'
  have := localizedNode_etale R c K A s A'
  have h := isNodeBranching_of_flat (A := A') (localizedNode_cbar R c K A s A' hs)
  rwa [localizedNode_coordinate, localizedNode_coordinate] at h

variable [Algebra K A'] [IsScalarTower K (K ⊗[R] A) A']

omit hA' in
theorem localizedNode_isScalarTower :
    letI := localizedNodeAlgebra R c K A A'
    IsScalarTower K (Node (K ⊗[R] O) (cbar c K)) A' := by
  let := localizedNodeAlgebra R c K A A'
  refine IsScalarTower.of_algebraMap_eq (S := Node (K ⊗[R] O) (cbar c K)) (A := A') fun k => ?_
  change algebraMap K A' k = algebraMap (K ⊗[R] A) A' (fibreNodeHom R c K A _)
  rw [fibreNodeHom_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **`Ω` near a node of the geometric fibre**: on a localization `A'_x` of the localized fibre
chart at `x = ū` (`i = 0`) or `x = v̄` (`i = 1`), `Ω[A'_x/K]` is free on `dx`. -/
theorem smul_D_bijective_localized [Algebra.Etale R O] [Algebra.Etale (Node O c) A] (i : Fin 2)
    (Aₓ : Type u) [CommRing Aₓ] [Algebra A' Aₓ]
    [IsLocalization.Away (algebraMap (K ⊗[R] A) A'
      ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c i))) Aₓ]
    [Algebra K Aₓ] [IsScalarTower K A' Aₓ] :
    Function.Bijective fun x : Aₓ => x • KaehlerDifferential.D K Aₓ (algebraMap A' Aₓ
      (algebraMap (K ⊗[R] A) A' ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c i)))) := by
  let := localizedNodeAlgebra R c K A A'
  have := localizedNode_etale R c K A s A'
  have := localizedNode_isScalarTower R c K A A'
  have hx := localizedNode_coordinate R c K A A' i
  have : IsLocalization.Away
      (algebraMap (Node (K ⊗[R] O) (cbar c K)) A' (coordinate (cbar c K) i)) Aₓ := by
    rw [hx]; infer_instance
  have h := smul_D_bijective_away (K := K) (O := K ⊗[R] O) (c := cbar c K) (A := A') i Aₓ
  rwa [hx] at h

/-- **Differentials on a branch near a node of the geometric fibre**: `Ω[(A'/(x_j))/K]` is spanned
by `dx_i`, `{i, j} = {0, 1}`. -/
theorem span_D_branch_localized [Algebra.Etale R O] [Algebra.Etale (Node O c) A] {i j : Fin 2}
    (hij : i ≠ j) :
    Submodule.span (A' ⧸ Ideal.span {algebraMap (K ⊗[R] A) A'
        ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c j))})
      {KaehlerDifferential.D K _ (Ideal.Quotient.mk (Ideal.span {algebraMap (K ⊗[R] A) A'
          ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c j))}) (algebraMap (K ⊗[R] A) A'
        ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c i))))} = ⊤ := by
  let := localizedNodeAlgebra R c K A A'
  have := localizedNode_etale R c K A s A'
  have := localizedNode_isScalarTower R c K A A'
  have h := span_D_branch (K := K) (O := K ⊗[R] O) (c := cbar c K) (A := A') hij
  rwa [localizedNode_coordinate, localizedNode_coordinate] at h

/-- **Rosenlicht's module near a node of the geometric fibre is free of rank one** on
`(dū/ū, -dv̄/v̄)`: `c ↦ (c·dū/ū, -c·dv̄/v̄)` is injective on the localized fibre chart `A'`. With
`isRosenlicht_iff` (which needs only `ū v̄ = 0`), the pairs of forms with simple poles on the two
branches and opposite residues are exactly the images of `A' · σ`. -/
theorem rosenlicht_injective_localized [Algebra.Etale R O] [Algebra.Etale (Node O c) A]
    (hs : s * cbar c K = 0) (Aᵤ Aᵥ : Type u) [CommRing Aᵤ] [CommRing Aᵥ] [Algebra A' Aᵤ]
    [Algebra A' Aᵥ]
    [IsLocalization.Away (algebraMap (K ⊗[R] A) A'
      ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0))) Aᵤ]
    [IsLocalization.Away (algebraMap (K ⊗[R] A) A'
      ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 1))) Aᵥ]
    [Algebra K Aᵤ] [Algebra K Aᵥ] [IsScalarTower K A' Aᵤ] [IsScalarTower K A' Aᵥ] :
    Function.Injective (rosenlicht K
      (algebraMap (K ⊗[R] A) A' ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0)))
      (algebraMap (K ⊗[R] A) A' ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 1)))
      Aᵤ Aᵥ) :=
  rosenlicht_injective K Aᵤ Aᵥ (isNodeBranching_localized R c K A s A' hs)
    (smul_D_bijective_localized R c K A s A' 0 Aᵤ).1
    (smul_D_bijective_localized R c K A s A' 1 Aᵥ).1

/-- **Regular forms on a branch near a node of the geometric fibre**: on the branch
`B₁ = A'/(v̄)`, a form `a·dū/ū` comes from `Ω[B₁/K]` iff its residue `a|_E` on the node locus
vanishes. Hence `Ω_{B₁}(E₁)/Ω_{B₁} ≅ 𝒪_E`. -/
theorem residue₁_eq_zero_iff_localized [Algebra.Etale R O] [Algebra.Etale (Node O c) A]
    (hs : s * cbar c K = 0) (Aᵤ : Type u) [CommRing Aᵤ] [Algebra A' Aᵤ]
    [IsLocalization.Away (algebraMap (K ⊗[R] A) A'
      ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0))) Aᵤ]
    [Algebra K Aᵤ] [IsScalarTower K A' Aᵤ]
    (a : A' ⧸ Ideal.span {algebraMap (K ⊗[R] A) A'
      ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 1))}) :
    residue₁ (algebraMap (K ⊗[R] A) A' ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0)))
        _ a = 0 ↔
      branchMap Aᵤ (isNodeBranching_localized R c K A s A' hs).mul_eq_zero a •
          logForm K (algebraMap (K ⊗[R] A) A'
            ((1 : K) ⊗ₜ[R] algebraMap (Node O c) A (coordinate c 0))) Aᵤ ∈
        Set.range (kaehlerMap₁ K (isNodeBranching_localized R c K A s A' hs) Aᵤ) :=
  residue₁_eq_zero_iff (isNodeBranching_localized R c K A s A' hs) Aᵤ
    (span_D_branch_localized R c K A s A' (by decide : (0 : Fin 2) ≠ 1))
    (smul_D_bijective_localized R c K A s A' 0 Aᵤ).1 a

end Localized

end Hironaka.StableModification.Omega.Rosenlicht
