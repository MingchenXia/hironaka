import DeJongAlterations.Algebra.SteinTensorReduced
import DeJongAlterations.Algebra.SteinTensorSpecialization

/-!
# Genuine tensor domains of a finitely generated regular field extension

Finite residue-field specialization internally produces the scalar
extensions used to contradict a purported pair of zero divisors.
-/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.SteinTensorDomain

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K F E : Type u} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra.EssFiniteType K F]
  {ι : Type u} {v : ι → F} (hv : AlgebraicIndependent K v)
  [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F]

include hv in
/-- No separability assumption on the actual finite scalar extension is required. -/
theorem isField_tensorProduct [FiniteDimensional K E] (h : integralClosure K F = ⊥) :
    IsField (E ⊗[K] F) := by
  let : IsReduced (F ⊗[K] E) := SteinTensorReduced.isReduced_tensorProduct hv
  let : IsReduced (E ⊗[K] F) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K E F)
      (Algebra.TensorProduct.comm K E F).injective
  let : Algebra F (E ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite F (E ⊗[K] F) :=
    Module.Finite.of_surjective (Algebra.TensorProduct.commRight K F E).toLinearMap
      (Algebra.TensorProduct.commRight K F E).surjective
  let : IsArtinianRing (E ⊗[K] F) := .of_finite F _
  exact SteinTensor.isField_of_idempotents_trivial _ (SteinTensorConnected.idempotent_trivial h)

include hv in
/-- Every actual scalar tensor is a domain; the finite scalar stage is produced internally. -/
theorem isDomain_tensorProduct (h : integralClosure K F = ⊥) : IsDomain (E ⊗[K] F) := by
  let : NoZeroDivisors (E ⊗[K] F) := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra! hn
    obtain ⟨B, hB, q, hq, hL, xB, yB, hx, hy, hxq, hyq⟩ :=
      SteinTensorSpecialization.exists_finite_specialization x y hn.1 hn.2
    let := hB
    let := hq
    let L := B ⧸ q
    let : Field L := Ideal.Quotient.field q
    let : Module.Finite K L := hL
    let hdom : IsDomain (L ⊗[K] F) := (isField_tensorProduct (E := L) hv h).isDomain
    have hnd : NoZeroDivisors (L ⊗[K] F) := @IsDomain.to_noZeroDivisors _ _ hdom
    let m := Algebra.TensorProduct.map B.val (AlgHom.id K F)
    have hm : Function.Injective m :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := F) B.val.toLinearMap
        Subtype.val_injective
    change m xB = x at hx
    change m yB = y at hy
    have hp : xB * yB = 0 := hm (by simpa only [map_mul, hx, hy, map_zero] using hxy)
    let n := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K q) (AlgHom.id K F)
    have hnp : n xB * n yB = 0 := by rw [← map_mul, hp, map_zero]
    rcases @eq_zero_or_eq_zero_of_mul_eq_zero (L ⊗[K] F) _ _ hnd _ _ hnp with hz | hz
    · exact hxq hz
    · exact hyq hz
  exact NoZeroDivisors.to_isDomain _

end DeJongAlterations.Algebra.SteinTensorDomain
