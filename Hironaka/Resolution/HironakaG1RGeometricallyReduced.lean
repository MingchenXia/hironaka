import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.TensorProduct.Quotient
import Hironaka.Resolution.HironakaG1RReducedBaseChange

/-!
# Reduced base change over perfect fields: ideal and scheme forms (ALG14 input D1)

Two consequences of `HironakaG1RReducedBaseChange.isReduced_tensorProduct_of_perfectField`
(`L ⊗[k] A` is reduced for a perfect field `k`, a field extension `L` and a reduced `A`):

* **ideal form** (`map_radical_includeRight`): extension of ideals along `A → L ⊗[k] A` commutes
  with radicals, `(√I)·(L ⊗ A) = √(I·(L ⊗ A))`; in particular the extension of a radical ideal is
  radical (`isRadical_map_includeRight`).  Geometrically: for a reduced closed subscheme `Z = V(I)`
  of `Spec A`, the scheme-theoretic preimage of `Z` in `Spec (L ⊗ A)` is reduced, i.e. the vanishing
  ideal of `Z` pulls back to the vanishing ideal of its preimage (the affine form of the "reduced
  preimage" input D1 of lane G1's ALG14 note, §3);
* **scheme form** (`geometricallyReduced_of_perfectField`): every reduced scheme over a perfect
  field `k` is geometrically reduced over `k` (for every field `K` over `k`, `X ×_k Spec K` is
  reduced); `isReduced_pullback_of_perfectField` states it for one field.

Only Mathlib and `HironakaG1RReducedBaseChange` are imported; no named input.
Blueprint: `hironaka-g1-r-reduced-base-change.tex` (nodes `g1r:reduced-base-change-ideal`,
`g1r:geometrically-reduced`).
-/

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory Limits

namespace Hironaka.HironakaG1RGeometricallyReduced

open HironakaG1RReducedBaseChange

universe u v w

/-! ### Ideal form -/

section Ideal

variable (k : Type u) (L : Type w) {A : Type v} [Field k] [PerfectField k] [Field L] [Algebra k L]
  [CommRing A] [Algebra k A]

/-- **The extension of a radical ideal is radical** along `A → L ⊗[k] A`, `k` perfect. -/
theorem isRadical_map_includeRight {I : Ideal A} (hI : I.IsRadical) :
    (I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A)).IsRadical := by
  have : IsReduced (A ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  have h1 : IsReduced (L ⊗[k] (A ⧸ I)) := isReduced_tensorProduct_of_perfectField k L (A ⧸ I)
  have h2 : IsReduced ((L ⊗[k] A) ⧸
      I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A)) :=
    isReduced_of_injective (Algebra.TensorProduct.tensorQuotientEquiv (R := k) k A L I).symm
      (AlgEquiv.injective _)
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr h2

/-- **Extension commutes with radicals** along `A → L ⊗[k] A`, `k` perfect:
`(√I)·(L ⊗ A) = √(I·(L ⊗ A))`. -/
theorem map_radical_includeRight (I : Ideal A) :
    I.radical.map (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) =
      (I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A)).radical := by
  refine le_antisymm (Ideal.map_radical_le _) ?_
  rw [(isRadical_map_includeRight k L (Ideal.radical_isRadical I)).radical_le_iff]
  exact Ideal.map_mono Ideal.le_radical

end Ideal

/-! ### Scheme form -/

section Scheme

open AlgebraicGeometry

/-- **A reduced scheme over a perfect field stays reduced after any field extension**:
`X ×_{Spec k} Spec K` is reduced. -/
theorem isReduced_pullback_of_perfectField {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsReduced X] (K : Type u) [Field K] [Algebra k K] :
    IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  refine @IsReduced.of_openCover _
    (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f _) fun i => ?_
  change IsReduced (pullback (X.affineOpenCover.f i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  set R : CommRingCat := X.affineOpenCover.X i
  have : IsOpenImmersion (X.affineOpenCover.f i) := X.affineOpenCover.map_prop i
  have hRs : IsReduced (Spec R) := isReduced_of_isOpenImmersion (X.affineOpenCover.f i)
  have hR : _root_.IsReduced R := (affine_isReduced_iff R).mp hRs
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
  let _inst : Algebra k R := φ.hom.toAlgebra
  have h1 : _root_.IsReduced (K ⊗[k] R) := isReduced_tensorProduct_of_perfectField k K R
  have h2 : _root_.IsReduced (R ⊗[k] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k R K) (AlgEquiv.injective _)
  have hφ' : X.affineOpenCover.f i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k R)) := hφ.symm
  let e := pullback.congrHom hφ' rfl ≪≫ pullbackSpecIso k R K
  exact isReduced_of_isOpenImmersion e.hom

/-- **Over a perfect field every reduced scheme is geometrically reduced** (scheme form of ALG14
input D1; in particular in characteristic zero). -/
theorem geometricallyReduced_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsReduced X] : GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  exact isReduced_pullback_of_perfectField f K

end Scheme

end Hironaka.HironakaG1RGeometricallyReduced
