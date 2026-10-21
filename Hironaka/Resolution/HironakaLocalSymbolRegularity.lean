/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaStrictFilteredGradedQuotient
import Mathlib.RingTheory.LocalRing.Module

set_option autoImplicit false
namespace Hironaka.HironakaLocalSymbolRegularity
open HironakaStrictFilteredGradedQuotient
variable {B R : Type*} [CommRing B] [IsLocalRing B] [CommRing R] [Algebra B R]
noncomputable section

theorem adicSymbolMul_split_of_residue_injective
    (I N : Ideal R) (v : R) (hv : v ∈ N) (q : ℕ)
    [Module.Finite B (adicLayer I N q)]
    [Module.Finite B (adicLayer I N (q+1))] [Module.Free B (adicLayer I N (q+1))]
    (hf : Function.Injective
      (((adicSymbolMul I N v hv q).restrictScalars B).lTensor (IsLocalRing.ResidueField B))) :
    ∃ r : adicLayer I N (q+1) →ₗ[B] adicLayer I N q,
      r.comp ((adicSymbolMul I N v hv q).restrictScalars B)=LinearMap.id :=
  (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    ((adicSymbolMul I N v hv q).restrictScalars B)).mpr hf

theorem regular_symbol_of_residue_injective
    (I N : Ideal R) (v : R) (hv : v ∈ N) (q : ℕ)
    [Module.Finite B (adicLayer I N q)]
    [Module.Finite B (adicLayer I N (q+1))] [Module.Free B (adicLayer I N (q+1))]
    (hf : Function.Injective
      (((adicSymbolMul I N v hv q).restrictScalars B).lTensor (IsLocalRing.ResidueField B)))
    (b : R) (hb : b ∈ N^q) (hvb : v*b ∈ I ⊔ N^(q+2)) : b ∈ I ⊔ N^(q+1) := by
  obtain ⟨r,hr⟩ := adicSymbolMul_split_of_residue_injective I N v hv q hf
  let x : adicLayer I N q := ⟨Ideal.Quotient.mk (I ⊔ N^(q+1)) b,⟨b,hb,rfl⟩⟩
  have hz : adicSymbolMul I N v hv q x=0 := by
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hvb
  have hx : x=0 := by
    have he := LinearMap.congr_fun hr x
    change r (adicSymbolMul I N v hv q x)=x at he
    rw [hz,map_zero] at he
    exact he.symm
  exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hx)

theorem adicLayer_after_parameter_finite_free
    (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hfinite : ∀ q : ℕ, Module.Finite B (adicLayer I N q))
    (hfree : ∀ q : ℕ, Module.Free B (adicLayer I N q))
    (hfibre : ∀ q : ℕ, Function.Injective
      (((adicSymbolMul I N v hv q).restrictScalars B).lTensor (IsLocalRing.ResidueField B)))
    (q : ℕ) :
    Module.Finite B (adicLayer (I ⊔ Ideal.span ({v} : Set R)) N q) ∧
      Module.Free B (adicLayer (I ⊔ Ideal.span ({v} : Set R)) N q) := by
  have hreg (r : ℕ) (b : R) (hb : b ∈ N^r) (hvb : v*b ∈ I ⊔ N^(r+2)) :
      b ∈ I ⊔ N^(r+1) := by
    let :=  hfinite r
    let :=  hfinite (r+1)
    let :=  hfree (r+1)
    exact regular_symbol_of_residue_injective I N v hv r (hfibre r) b hb hvb
  let :=  hfinite q
  let g := (adicLayerMap I N v q).restrictScalars B
  have hsurj : Function.Surjective g := adicLayerMap_surjective I N v q
  refine ⟨Module.Finite.of_surjective g hsurj,?_⟩
  cases q with
  | zero =>
      let :=  hfree 0
      exact Module.Free.of_equiv
        (LinearEquiv.ofBijective g ⟨adicLayerMap_zero_injective I N v hv,hsurj⟩)
  | succ r =>
      let :=  hfinite r
      let :=  hfree (r+1)
      let f := (adicSymbolMul I N v hv r).restrictScalars B
      have hexact : Function.Exact f g := by
        apply LinearMap.exact_iff.mpr
        change LinearMap.ker ((adicLayerMap I N v (r+1)).restrictScalars B) =
          LinearMap.range ((adicSymbolMul I N v hv r).restrictScalars B)
        rw [LinearMap.ker_restrictScalars,LinearMap.range_restrictScalars,
          ker_adicLayerMap_eq_range_adicSymbolMul I N v hv hreg r]
      exact Module.free_of_lTensor_residueField_injective f g hsurj hexact (hfibre r)

end
end Hironaka.HironakaLocalSymbolRegularity
