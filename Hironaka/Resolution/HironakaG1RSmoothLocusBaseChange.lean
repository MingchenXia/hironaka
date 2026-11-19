import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.Module

/-!
# The smooth locus under flat base change, pointwise (ALG14 input D3)

**Main result** (`mem_smoothLocus_tensorProduct_iff`): let `R → T` be a flat ring map and `A` an
`R`-algebra essentially of finite type.  For every prime `q` of `B = T ⊗[R] A`, lying over the prime
`p` of `A`,

  `B` is smooth over `T` at `q`  ↔  `A` is smooth over `R` at `p`.

Equivalently the smooth locus of `B / T` is the preimage of the smooth locus of `A / R`
(`smoothLocus_tensorProduct`).  The field case (`mem_smoothLocus_tensorProduct_iff_of_field`) is the
pointwise smooth-locus comparison under an ARBITRARY field extension `L / k` (input D3 of lane G1's
ALG14 note, `work/hironaka-resume-20261111/G1/ALG14-R02-FINITE-GENERATION-DESCENT.md`, §3); Mathlib
has only the global statement (`Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`).

Proof (Stacks 00TB, 07BT-style descent at points):
* `Algebra.smoothLocus_eq_compl_support_inter`: smooth at `p` ↔ `p ∉ Supp H¹(L_{A/R})` and
  `p ∈ freeLocus Ω[A/R]`;
* flat base change identifies `H¹(L_{B/T}) ≅ B ⊗[A] H¹(L_{A/R})` (`tensorH1CotangentEquiv`, built
  from Mathlib's `T`-linear `Algebra.tensorH1CotangentOfFlat`, here made `B`-linear) and
  `Ω[B/T] ≅ B ⊗[A] Ω[A/R]` (`KaehlerDifferential.tensorKaehlerEquiv`);
* for a ring map `A → B` and a prime `q` of `B` with `B_q` flat over `A`, the local map
  `A_p → B_q` is flat and local, hence faithfully flat (`faithfullyFlat_localRingHom`); so support
  (`mem_support_tensorProduct_iff`) and, for finite modules, the free locus
  (`mem_freeLocus_tensorProduct_iff`; flatness descends, finite flat over a local ring is free) of
  `B ⊗[A] M` at `q` are those of `M` at `p`.

Only Mathlib is imported; no named input.  Blueprint: `hironaka-g1-r-smooth-locus-base-change.tex`.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Hironaka.HironakaG1RSmoothLocusBaseChange

/-! ### Support and free locus along a flat local map -/

section LocalDescent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- `p ∉ Supp M` iff `A_p ⊗[A] M = 0`. -/
theorem notMem_support_iff_subsingleton_tensor (M : Type*) [AddCommGroup M] [Module A M]
    (p : PrimeSpectrum A) :
    p ∉ Module.support A M ↔ Subsingleton (Localization.AtPrime p.asIdeal ⊗[A] M) := by
  rw [Module.notMem_support_iff]
  exact (IsLocalizedModule.iso p.asIdeal.primeCompl
    (TensorProduct.mk A (Localization.AtPrime p.asIdeal) M 1)).subsingleton_congr

/-- **Flat local maps of local rings are faithfully flat**: if `B_q` is flat over `A`, then the
local map `A_p → B_q` (`p` the contraction of `q`) is faithfully flat. -/
theorem faithfullyFlat_localRingHom (q : PrimeSpectrum B)
    [Module.Flat A (Localization.AtPrime q.asIdeal)] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)).asIdeal q.asIdeal
    Module.FaithfullyFlat (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  let _ := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)).asIdeal q.asIdeal
  have : Module.Flat (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal)
      (Localization.AtPrime q.asIdeal) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal)
      (q.comap (algebraMap A B)).asIdeal.primeCompl _).mpr inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal)
      (Localization.AtPrime q.asIdeal)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- **Support descends along flat maps, pointwise.** If `B_q` is flat over `A`, then `q` lies in
the support of `B ⊗[A] M` iff its contraction lies in the support of `M`. -/
theorem mem_support_tensorProduct_iff (M : Type*) [AddCommGroup M] [Module A M]
    (q : PrimeSpectrum B) [Module.Flat A (Localization.AtPrime q.asIdeal)] :
    q ∈ Module.support B (B ⊗[A] M) ↔ q.comap (algebraMap A B) ∈ Module.support A M := by
  rw [← not_iff_not, notMem_support_iff_subsingleton_tensor,
    notMem_support_iff_subsingleton_tensor]
  let _ := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)).asIdeal q.asIdeal
  have := faithfullyFlat_localRingHom (A := A) q
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) M ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A
      (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal) (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) M).symm
  rw [e.subsingleton_congr]
  constructor
  · intro h
    exact Module.FaithfullyFlat.lTensor_reflects_triviality
      (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal) (Localization.AtPrime q.asIdeal) _
  · intro h
    infer_instance

/-- **The free locus descends along flat maps, pointwise, for finite modules.** If `B_q` is flat
over `A` and `M` is a finite `A`-module, then `(B ⊗[A] M)_q` is free iff `M_p` is free. -/
theorem mem_freeLocus_tensorProduct_iff (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (q : PrimeSpectrum B) [Module.Flat A (Localization.AtPrime q.asIdeal)] :
    q ∈ Module.freeLocus B (B ⊗[A] M) ↔ q.comap (algebraMap A B) ∈ Module.freeLocus A M := by
  refine ⟨fun h ↦ ?_, fun h ↦ Module.comap_freeLocus_le h⟩
  let _ := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)).asIdeal q.asIdeal
  have := faithfullyFlat_localRingHom (A := A) q
  rw [Module.mem_freeLocus_iff_tensor _ (Localization.AtPrime q.asIdeal)] at h
  rw [Module.mem_freeLocus_iff_tensor _ (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal)]
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) M ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A
      (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal) (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) M).symm
  have : Module.Free (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[Localization.AtPrime (q.comap (algebraMap A B)).asIdeal]
        (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal ⊗[A] M)) := .of_equiv e
  have : Module.Flat (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal)
      (Localization.AtPrime (q.comap (algebraMap A B)).asIdeal ⊗[A] M) :=
    Module.Flat.of_flat_tensorProduct _ _ (Localization.AtPrime q.asIdeal)
  exact Module.free_of_flat_of_isLocalRing

end LocalDescent

/-! ### `H¹` of the cotangent complex under flat base change, `B`-linearly -/

section H1

variable (R T A : Type*) [CommRing R] [CommRing T] [CommRing A] [Algebra R T] [Algebra R A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The canonical `B`-linear map `B ⊗[A] H¹(L_{A/R}) → H¹(L_{B/T})`, `B = T ⊗[R] A`. -/
noncomputable def tensorToH1Cotangent :
    (T ⊗[R] A) ⊗[A] Algebra.H1Cotangent R A →ₗ[T ⊗[R] A] Algebra.H1Cotangent T (T ⊗[R] A) :=
  (Algebra.H1Cotangent.map R T A (T ⊗[R] A)).liftBaseChange (T ⊗[R] A)

theorem tensorToH1Cotangent_cancelBaseChange_symm [Module.Flat R T]
    (y : T ⊗[R] Algebra.H1Cotangent R A) :
    tensorToH1Cotangent R T A
        ((Algebra.IsPushout.cancelBaseChange R T A (T ⊗[R] A) (Algebra.H1Cotangent R A)).symm y) =
      Algebra.tensorH1CotangentOfFlat R A T y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul t x =>
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, Algebra.tensorH1CotangentOfFlat_tmul]
    simp only [tensorToH1Cotangent, LinearMap.liftBaseChange_tmul, algebraMap_smul]

/-- **Flat base change of `H¹` of the cotangent complex, `B`-linearly**:
`(T ⊗[R] A) ⊗[A] H¹(L_{A/R}) ≃ H¹(L_{(T ⊗[R] A)/T})` for `T` flat over `R`. -/
noncomputable def tensorH1CotangentEquiv [Module.Flat R T] :
    (T ⊗[R] A) ⊗[A] Algebra.H1Cotangent R A ≃ₗ[T ⊗[R] A] Algebra.H1Cotangent T (T ⊗[R] A) :=
  LinearEquiv.ofBijective (tensorToH1Cotangent R T A) <| by
    have h : ⇑(tensorToH1Cotangent R T A) = ⇑(Algebra.tensorH1CotangentOfFlat R A T) ∘
        ⇑(Algebra.IsPushout.cancelBaseChange R T A (T ⊗[R] A) (Algebra.H1Cotangent R A)) := by
      funext x
      obtain ⟨y, rfl⟩ :=
        (Algebra.IsPushout.cancelBaseChange R T A (T ⊗[R] A) (Algebra.H1Cotangent R A)).symm.surjective x
      simp [tensorToH1Cotangent_cancelBaseChange_symm]
    rw [h]
    exact (Algebra.tensorH1CotangentOfFlat R A T).bijective.comp (LinearEquiv.bijective _)

end H1

/-! ### The smooth locus -/

section SmoothLocus

variable {R T A : Type*} [CommRing R] [CommRing T] [CommRing A] [Algebra R T] [Algebra R A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The base change `T ⊗[R] A` is flat over `A` when `T` is flat over `R`, and so are its
localizations at primes. -/
theorem flat_localization_tensorProduct [Module.Flat R T] (q : PrimeSpectrum (T ⊗[R] A)) :
    Module.Flat A (Localization.AtPrime q.asIdeal) := by
  have : Module.Flat A (T ⊗[R] A) :=
    Module.Flat.isBaseChange R A T (T ⊗[R] A)
      (inferInstance : Algebra.IsPushout R A T (T ⊗[R] A)).out
  exact Module.Flat.trans A (T ⊗[R] A) _

/-- **The smooth locus under flat base change, pointwise (ALG14 D3).**  For `R → T` flat and `A`
essentially of finite type over `R`, `T ⊗[R] A` is smooth over `T` at a prime `q` iff `A` is smooth
over `R` at the contraction of `q`. -/
theorem mem_smoothLocus_tensorProduct_iff [Module.Flat R T] [Algebra.EssFiniteType R A]
    (q : PrimeSpectrum (T ⊗[R] A)) :
    q ∈ Algebra.smoothLocus T (T ⊗[R] A) ↔
      q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom ∈
        Algebra.smoothLocus R A := by
  have := flat_localization_tensorProduct (R := R) (T := T) (A := A) q
  rw [Algebra.smoothLocus_eq_compl_support_inter, Algebra.smoothLocus_eq_compl_support_inter]
  simp only [Set.mem_inter_iff, Set.mem_compl_iff]
  rw [← (tensorH1CotangentEquiv R T A).support_eq,
    ← Module.freeLocus_congr (KaehlerDifferential.tensorKaehlerEquiv R T A (T ⊗[R] A)),
    mem_support_tensorProduct_iff, mem_freeLocus_tensorProduct_iff]
  rfl

/-- **The smooth locus of a flat base change is the preimage of the smooth locus.** -/
theorem smoothLocus_tensorProduct [Module.Flat R T] [Algebra.EssFiniteType R A] :
    Algebra.smoothLocus T (T ⊗[R] A) =
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom ⁻¹'
        Algebra.smoothLocus R A := by
  ext q
  exact mem_smoothLocus_tensorProduct_iff q

end SmoothLocus

/-! ### Field extensions -/

section Field

variable (k L A : Type*) [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]
  [Algebra.EssFiniteType k A]

/-- **Pointwise smooth locus under an arbitrary field extension (ALG14 D3).**  For `A` essentially
of finite type over a field `k` and any field extension `L / k`, `L ⊗[k] A` is smooth over `L` at
`q` iff `A` is smooth over `k` at the contraction of `q`. -/
theorem mem_smoothLocus_tensorProduct_iff_of_field (q : PrimeSpectrum (L ⊗[k] A)) :
    q ∈ Algebra.smoothLocus L (L ⊗[k] A) ↔
      q.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom ∈
        Algebra.smoothLocus k A :=
  mem_smoothLocus_tensorProduct_iff q

/-- Set form of `mem_smoothLocus_tensorProduct_iff_of_field`. -/
theorem smoothLocus_tensorProduct_of_field :
    Algebra.smoothLocus L (L ⊗[k] A) =
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom ⁻¹'
        Algebra.smoothLocus k A :=
  smoothLocus_tensorProduct

end Field

end Hironaka.HironakaG1RSmoothLocusBaseChange
