import Hironaka.Resolution.HironakaNativeSameMapKernelComparison
import Hironaka.Resolution.HironakaNativePrimeTargetRestriction
import Hironaka.Resolution.HironakaChowNativeStalkPrimeFiltration

/-! Public generic downward prime-layer step on an original open (lane G10P, run 0079).
Blueprint: `hironaka-g10-pn-downward-layers.tex`.

The accepted module `HironakaNativeFirstPrimeKernel` proves the TOP step of the fixed original prime
series with private helpers only.  This module re-proves those helpers as PUBLIC declarations (same
proofs, from the same public mothers) and states the step for ARBITRARY adjacent original submodules
`N₀ ≤ N₁`, not only `N₁ = ⊤`.  The proofs are those of the accepted private helpers, unchanged;
only names and visibility differ. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaG10PNLayerStep

open HironakaChowNativeFreePartContinuation
  HironakaChowNativePrimeSupportContinuation HironakaSingularModuleSheafStalk
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeLocalOverStalkTransport
  HironakaChowNativeLocalOverFiniteDataTransport HironakaNativeCanonicalSupportRestriction
  HironakaNativeCyclicCokernelRestriction HironakaChowNativeModuleStalkExact
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaSingularLocallyFreeStalk

noncomputable section

theorem quotient_iso_of_exact_kernel
    {A : Type} [CommRing A] (C : ModuleCat.{0} A)
    (v : ModuleCat.of A A ⟶ C) (hv : Function.Surjective v)
    (P : Ideal A) (hP : ∀ a : A, v a = 0 ↔ a ∈ P) :
    ∃ θ : C ≅ ModuleCat.of A (A ⧸ P),
      (∀ a : A, θ.hom (v a) = Submodule.Quotient.mk a) ∧
      (∀ a : A, θ.inv (Submodule.Quotient.mk a) = v a) := by
  have hker : v.hom.ker = P := by
    ext a
    exact hP a
  let e : (A ⧸ P) ≃ₗ[A] C :=
    (Submodule.quotEquivOfEq P v.hom.ker hker.symm).trans
      (v.hom.quotKerEquivOfSurjective hv)
  have he (a : A) : e (Submodule.Quotient.mk a) = v a := by
    simp only [e, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
    rfl
  refine ⟨e.symm.toModuleIso, ?_, ?_⟩
  · intro a
    change e.symm (v a) = _
    rw [← he a, e.symm_apply_apply]
  · exact he

theorem layer_factor_kernel
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (T C : ModuleCat.{0} A) (η : T ≅ ModuleCat.of A N₁)
    (θ : C ≅ ModuleCat.of A (A ⧸ P)) :
    let ψ : T ⟶ C := η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫
      e.toModuleIso.hom ≫ θ.inv
    Function.Surjective ψ ∧
    ∃ k : ModuleCat.of A ψ.hom.ker ≅ ModuleCat.of A N₀,
      k.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
        ModuleCat.ofHom ψ.hom.ker.subtype ≫ η.hom := by
  dsimp only
  let ψ : T ⟶ C := η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫
    e.toModuleIso.hom ≫ θ.inv
  have hsurj : Function.Surjective ψ :=
    θ.toLinearEquiv.symm.surjective.comp
      (e.surjective.comp ((N₀.submoduleOf N₁).mkQ_surjective.comp
        η.toLinearEquiv.surjective))
  have hmem (x : T) : ψ x = 0 ↔ (η.hom x : M) ∈ N₀ := by
    change θ.toLinearEquiv.symm (e (Submodule.Quotient.mk (η.hom x))) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff,
      Submodule.Quotient.mk_eq_zero]
    rfl
  let f : ψ.hom.ker →ₗ[A] N₀ :=
    { toFun := fun x => ⟨η.hom x, (hmem x).mp x.property⟩
      map_add' := fun x y => Subtype.ext (by
        change (η.hom.hom (x.val + y.val) : M) =
          (η.hom.hom x.val : M) + (η.hom.hom y.val : M)
        exact congrArg (fun z : N₁ => (z : M)) (map_add η.hom.hom x.val y.val))
      map_smul' := fun a x => Subtype.ext (by
        change (η.hom.hom (a • x.val) : M) = a • (η.hom.hom x.val : M)
        exact congrArg (fun z : N₁ => (z : M)) (map_smul η.hom.hom a x.val)) }
  let g : N₀ →ₗ[A] ψ.hom.ker :=
    { toFun := fun y => ⟨η.inv (Submodule.inclusion hle y),
        (hmem _).mpr (by
          rw [Iso.inv_hom_id_apply]
          exact y.property)⟩
      map_add' := fun x y => Subtype.ext (by
        change η.inv.hom ((Submodule.inclusion hle) (x + y)) =
          η.inv.hom ((Submodule.inclusion hle) x) +
            η.inv.hom ((Submodule.inclusion hle) y)
        rw [map_add, map_add])
      map_smul' := fun a x => Subtype.ext (by
        change η.inv.hom ((Submodule.inclusion hle) (a • x)) =
          a • η.inv.hom ((Submodule.inclusion hle) x)
        rw [map_smul, map_smul]) }
  let k : ψ.hom.ker ≃ₗ[A] N₀ :=
    { f with
      invFun := g
      left_inv := fun x => Subtype.ext (by
        change η.inv (Submodule.inclusion hle (f x)) = x.val
        change η.inv (η.hom x.val) = x.val
        exact Iso.hom_inv_id_apply η x.val)
      right_inv := fun y => Subtype.ext (by
        change (η.hom (η.inv (Submodule.inclusion hle y)) : M) = y.val
        exact congrArg Subtype.val (Iso.inv_hom_id_apply η (Submodule.inclusion hle y))) }
  refine ⟨hsurj, k.toModuleIso, ?_⟩
  ext x
  rfl

theorem scalar_restricted_quotient
    {A R : Type} [CommRing A] [CommRing R] (α : R ≃+* A)
    (C : ModuleCat.{0} R) (κ : ModuleCat.of R R ⟶ C)
    (hκ : Function.Surjective κ) (P : Ideal A)
    (hP : ∀ r : R, κ r = 0 ↔ α r ∈ P) :
    let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
    ∃ θ : S.obj C ≅ ModuleCat.of A (A ⧸ P),
      (∀ r : R, θ.hom (κ r) = Submodule.Quotient.mk (α r)) ∧
      (∀ r : R, θ.inv (Submodule.Quotient.mk (α r)) = κ r) := by
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
  let β := ModuleCat.restrictScalarsIsoOfEquiv α.symm
  let v : ModuleCat.of A A ⟶ S.obj C := β.inv ≫ S.map κ
  have hv (a : A) : v a = κ (α.symm a) := rfl
  have hsurj : Function.Surjective v := by
    intro c
    obtain ⟨r, hr⟩ := hκ (show C from c)
    refine ⟨α r, ?_⟩
    change κ (α.symm (α r)) = (show C from c)
    rw [α.symm_apply_apply]
    exact hr
  have hker (a : A) : v a = 0 ↔ a ∈ P := by
    change κ (α.symm a) = (0 : C) ↔ a ∈ P
    rw [hP, α.apply_symm_apply]
  obtain ⟨θ, hforward, hinverse⟩ := quotient_iso_of_exact_kernel (S.obj C) v hsurj P hker
  refine ⟨θ, ?_, ?_⟩
  · intro r
    have h := hforward (α r)
    simpa only [hv, α.symm_apply_apply] using h
  · intro r
    have h := hinverse (α r)
    simpa only [hv, α.symm_apply_apply] using h

theorem ideal_membership_of_eq
    {R : Type} [CommRing R] {I J : Ideal R} (h : I = J) (r : R) :
    r ∈ I ↔ r ∈ J := by
  rw [h]

theorem equiv_zero_test
    {R S N : Type} [Zero N] (e : R ≃ S) (f : S → N) (test : R → Prop)
    (h : ∀ r : R, f (e r) = 0 ↔ test r) (s : S) :
    f s = 0 ↔ test (e.symm s) :=
  (Iff.of_eq (congrArg (fun t => f t = 0) (e.apply_symm_apply s).symm)).trans
    (h (e.symm s))

theorem ideal_equiv_membership
    {R S : Type} [CommRing R] [CommRing S] (ell : R ≃+* S)
    (I : Ideal R) (r : S) : r ∈ Ideal.map ell.toRingHom I ↔ ell.symm r ∈ I := by
  rw [Ideal.mem_map_iff_of_surjective ell.toRingHom ell.surjective]
  constructor
  · rintro ⟨x, hx, hxr⟩
    have h : x = ell.symm r := ell.injective (hxr.trans (ell.apply_symm_apply r).symm)
    exact h ▸ hx
  · intro h
    exact ⟨ell.symm r, h, ell.apply_symm_apply r⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem restricted_prime_kernel_readback
    {n : ℕ} {p : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p)}
    (B : NativePrimeAllOpenCokernelData p P) (D : Opens B.old.U)
    (b : originalImageOpen B.old.U D)
    (r : OriginalRingStalk (originalImageOpen B.old.U D) b) :
    originalUnitDomainStalkMap (originalImageOpen B.old.U D)
      (cokernel.π (originalRestrictedCyclicRelation B.old.U D B.old.δ)) b r = 0 ↔
    originalUnitDomainStalkMap B.old.U B.old.κ (originalImageInclusion B.old.U D b)
      ((originalImageStalkRingEquiv B.old.U D b).symm r) = 0 := by
  exact ((B.all_opens D).kernel b r).trans
    ((ideal_membership_of_eq ((B.all_opens D).ideal_map b) r).trans
      ((ideal_equiv_membership (originalImageStalkRingEquiv B.old.U D b)
        (originalGeneratorIdeal B.old.U B.old.g (originalImageInclusion B.old.U D b)) r).trans
        (B.old.kernel (originalImageInclusion B.old.U D b)
          ((originalImageStalkRingEquiv B.old.U D b).symm r)).symm))

set_option backward.isDefEq.respectTransparency.types false in
theorem restricted_prime_original_quotient
    {n : ℕ} (p : ComplexModel n) {A : Type} [CommRing A]
    (a₀ : HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p ≃+* A) (P : Ideal A)
    (B : NativePrimeAllOpenCokernelData p (Ideal.comap a₀.toRingHom P))
    (D : Opens B.old.U) (hpD : (⟨p, B.old.hpU⟩ : B.old.U) ∈ D) :
    let W := originalImageOpen B.old.U D
    let pW : W := ⟨p, ⟨⟨p, B.old.hpU⟩, hpD, rfl⟩⟩
    let C : OriginalModules W := cokernel (originalRestrictedCyclicRelation B.old.U D B.old.δ)
    let κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf W)) ⟶ C :=
      cokernel.π (originalRestrictedCyclicRelation B.old.U D B.old.δ)
    let α := (originalImageStalkRingEquiv B.old.U D pW).symm.trans
      ((originalRestrictionStalkEquiv B.old.U ⟨p, B.old.hpU⟩).symm.trans a₀)
    let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
    C.IsFinitePresentation ∧
    ∃ θ : S.obj ((nativeStalkFunctor (originalOpenStructureSheaf W) pW).obj C) ≅
        ModuleCat.of A (A ⧸ P),
      (∀ r : OriginalRingStalk W pW,
        θ.hom (originalUnitDomainStalkMap W κ pW r) = Submodule.Quotient.mk (α r)) ∧
      (∀ r : OriginalRingStalk W pW,
        θ.inv (Submodule.Quotient.mk (α r)) = originalUnitDomainStalkMap W κ pW r) := by
  let W := originalImageOpen B.old.U D
  let pW : W := ⟨p, ⟨⟨p, B.old.hpU⟩, hpD, rfl⟩⟩
  let C : OriginalModules W := cokernel (originalRestrictedCyclicRelation B.old.U D B.old.δ)
  let κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf W)) ⟶ C :=
    cokernel.π (originalRestrictedCyclicRelation B.old.U D B.old.δ)
  let ell := originalImageStalkRingEquiv B.old.U D pW
  let aOld := originalRestrictionStalkEquiv B.old.U (⟨p, B.old.hpU⟩ : B.old.U)
  let α := ell.symm.trans (aOld.symm.trans a₀)
  let st := nativeStalkFunctor (originalOpenStructureSheaf W) pW
  let u : ModuleCat.of (OriginalRingStalk W pW) (OriginalRingStalk W pW) ⟶ st.obj C :=
    ModuleCat.ofHom (originalUnitDomainStalkMap W κ pW)
  have hsurj : Function.Surjective u := by
    intro m
    let e := (B.all_opens D).quotient pW
    obtain ⟨z, hz⟩ := e.toLinearEquiv.surjective m
    obtain ⟨r, hr⟩ := Submodule.mkQ_surjective _ z
    refine ⟨r, ?_⟩
    exact ((B.all_opens D).quotient_mk pW r).symm.trans
      ((congrArg (fun z => e.hom z) hr).trans hz)
  have hkernel (r : OriginalRingStalk W pW) : u r = 0 ↔ α r ∈ P := by
    apply (restricted_prime_kernel_readback B D pW r).trans
    exact equiv_zero_test aOld.toEquiv
      (originalUnitDomainStalkMap B.old.U B.old.κ ⟨p, B.old.hpU⟩)
      (fun s => a₀ s ∈ P) B.old.prime_at_p (ell.symm r)
  refine ⟨(B.all_opens D).finitePresentation, ?_⟩
  exact scalar_restricted_quotient α (st.obj C) u hsurj P hkernel

theorem ringEquiv_cancel_original
    {B R S : Type} [CommRing B] [CommRing R] [CommRing S]
    (ell : R ≃+* S) (aR : B ≃+* R) (aS : B ≃+* S)
    (h : ∀ r : R, ell r = aS (aR.symm r)) :
    ell.symm.trans aR.symm = aS.symm := by
  ext s
  apply aS.injective
  exact ((h (ell.symm s)).symm.trans (ell.apply_symm_apply s)).trans
    (aS.apply_symm_apply s).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem original_image_stalk_back
    {n : ℕ} (U : Opens (ComplexModel n)) (D : Opens U)
    (b : originalImageOpen U D) :
    (originalImageStalkRingEquiv U D b).symm.trans
        (originalRestrictionStalkEquiv U (originalImageInclusion U D b)).symm =
      (originalRestrictionStalkEquiv (originalImageOpen U D) b).symm := by
  exact ringEquiv_cancel_original (originalImageStalkRingEquiv U D b)
    (originalRestrictionStalkEquiv U (originalImageInclusion U D b))
    (originalRestrictionStalkEquiv (originalImageOpen U D) b)
    (originalImageStalkRingEquiv_original U D b)

set_option backward.isDefEq.respectTransparency.types false in
def native_original_stalk_iso
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    (F : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) :
    (ModuleCat.restrictScalars.{0} (localOverRingStalkEquiv X U V p hpV).symm.toRingHom).obj
      ((nativeStalkFunctor
          (X.restrict (U.overEquivalence.inverse.obj V).left.isOpenEmbedding).𝒪
          (⟨p.val, ⟨p, hpV, rfl⟩⟩ : (U.overEquivalence.inverse.obj V).left)).obj
        ((localOverTransport X U V).obj (F.over V))) ≅
      (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj F :=
  localOverModuleStalkIso X U V F p hpV

set_option backward.isDefEq.respectTransparency.types false in
theorem local_original_finitePresentation
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (F : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    [hF : F.IsFinitePresentation] (V : Opens (TopCat.of U)) :
    ((localOverTransport X U V).obj (F.over V)).IsFinitePresentation := by
  have hOver : (F.over V).IsFinitePresentation :=
    HironakaChowNativeLocalOverFiniteDataTransport.over_isFinitePresentation
      (X.restrict U.isOpenEmbedding).𝒪 F V
  have hInv : ((localModuleEquivalence X U V).inverse.obj (F.over V)).IsFinitePresentation :=
    @local_inverse_isFinitePresentation X U V (F.over V) hOver
  exact @HironakaChowNativeLocalOverFiniteDataTransport.realization_isFinitePresentation
    X (U.overEquivalence.inverse.obj V).left
    ((localModuleEquivalence X U V).inverse.obj (F.over V)) hInv

theorem local_original_ring_comparison
    {n : ℕ} (U : Opens (ComplexModel n)) (V : Opens U) (p : U) (hpV : p ∈ V) :
    localOverRingStalkEquiv (originalSpace n) U V p hpV =
      (originalRestrictionStalkEquiv (originalImageOpen U V)
        (⟨p.val, ⟨p, hpV, rfl⟩⟩ : originalImageOpen U V)).symm.trans
          (originalRestrictionStalkEquiv U p) := by
  rfl

def inverseImageOpen {X : Type} [TopologicalSpace X]
    (U D : Opens X) : Opens U :=
  (Opens.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
    TopCat.of U ⟶ TopCat.of X)).obj D

theorem original_image_inverseImage
    {n : ℕ} (U D : Opens (ComplexModel n)) (hDU : D ≤ U) :
    originalImageOpen U (inverseImageOpen U D) = D := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change u.val ∈ D at hu
    exact hu
  · intro hx
    exact ⟨⟨x, hDU hx⟩, (show x ∈ D from hx), rfl⟩

theorem mem_finset_open_inf
    {X I : Type} [TopologicalSpace X] [DecidableEq I]
    (B : I → Opens X) (J : Finset I) (x : X) :
    x ∈ J.inf B ↔ ∀ i ∈ J, x ∈ B i := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.inf_empty, Opens.mem_top, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  | @insert i J hi ih =>
    simp only [Finset.inf_insert, Opens.mem_inf, ih, Finset.mem_insert, forall_eq_or_imp]

theorem scalar_quotient_congr
    {A R : Type} [CommRing A] [CommRing R] {α β : R ≃+* A} (h : α = β)
    (C : ModuleCat.{0} R) (κ : ModuleCat.of R R ⟶ C) (P : Ideal A) :
    (∃ θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj C ≅
        ModuleCat.of A (A ⧸ P),
      (∀ r : R, θ.hom (κ r) = Submodule.Quotient.mk (α r)) ∧
      (∀ r : R, θ.inv (Submodule.Quotient.mk (α r)) = κ r)) →
    (∃ θ : (ModuleCat.restrictScalars.{0} β.symm.toRingHom).obj C ≅
        ModuleCat.of A (A ⧸ P),
      (∀ r : R, θ.hom (κ r) = Submodule.Quotient.mk (β r)) ∧
      (∀ r : R, θ.inv (Submodule.Quotient.mk (β r)) = κ r)) := by
  cases h
  exact id

def primeTargetProperty
    {n : ℕ} (p : ComplexModel n) {A : Type} [CommRing A]
    (a₀ : HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p ≃+* A) (P : Ideal A)
    (W : Opens (ComplexModel n)) (hpW : p ∈ W) (C : OriginalModules W)
    (κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf W)) ⟶ C) : Prop :=
  let pW : W := ⟨p, hpW⟩
  let α := (originalRestrictionStalkEquiv W pW).symm.trans a₀
  C.IsFinitePresentation ∧
  ∃ θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor (originalOpenStructureSheaf W) pW).obj C) ≅
      ModuleCat.of A (A ⧸ P),
    (∀ r : OriginalRingStalk W pW,
      θ.hom (originalUnitDomainStalkMap W κ pW r) = Submodule.Quotient.mk (α r)) ∧
    (∀ r : OriginalRingStalk W pW,
      θ.inv (Submodule.Quotient.mk (α r)) = originalUnitDomainStalkMap W κ pW r)

set_option backward.isDefEq.respectTransparency.types false in
theorem native_prime_target_property
    {n : ℕ} (p : ComplexModel n) {A : Type} [CommRing A]
    (a₀ : HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p ≃+* A) (P : Ideal A)
    (B : NativePrimeAllOpenCokernelData p (Ideal.comap a₀.toRingHom P))
    (D : Opens B.old.U) (hpD : (⟨p, B.old.hpU⟩ : B.old.U) ∈ D) :
    primeTargetProperty p a₀ P (originalImageOpen B.old.U D)
      ⟨⟨p, B.old.hpU⟩, hpD, rfl⟩
      (cokernel (originalRestrictedCyclicRelation B.old.U D B.old.δ))
      (cokernel.π (originalRestrictedCyclicRelation B.old.U D B.old.δ)) := by
  let pW : originalImageOpen B.old.U D := ⟨p, ⟨⟨p, B.old.hpU⟩, hpD, rfl⟩⟩
  have hα : (originalImageStalkRingEquiv B.old.U D pW).symm.trans
      ((originalRestrictionStalkEquiv B.old.U ⟨p, B.old.hpU⟩).symm.trans a₀) =
      (originalRestrictionStalkEquiv (originalImageOpen B.old.U D) pW).symm.trans a₀ :=
    congrArg (fun e => e.trans a₀) (original_image_stalk_back B.old.U D pW)
  have h := restricted_prime_original_quotient p a₀ P B D hpD
  refine ⟨h.1, ?_⟩
  exact scalar_quotient_congr hα
    ((nativeStalkFunctor (originalOpenStructureSheaf (originalImageOpen B.old.U D)) pW).obj
      (cokernel (originalRestrictedCyclicRelation B.old.U D B.old.δ)))
    (ModuleCat.ofHom (originalUnitDomainStalkMap (originalImageOpen B.old.U D)
      (cokernel.π (originalRestrictedCyclicRelation B.old.U D B.old.δ)) pW)) P h.2

def castOriginalModule
    {n : ℕ} {W Z : Opens (ComplexModel n)} (h : W = Z) (C : OriginalModules W) :
    OriginalModules Z := by
  cases h
  exact C

def castOriginalQuotient
    {n : ℕ} {W Z : Opens (ComplexModel n)} (h : W = Z) {C : OriginalModules W}
    (κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf W)) ⟶ C) :
    SheafOfModules.unit (forgetRing (originalOpenStructureSheaf Z)) ⟶ castOriginalModule h C := by
  cases h
  exact κ

theorem cast_prime_target_property
    {n : ℕ} (p : ComplexModel n) {A : Type} [CommRing A]
    (a₀ : HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p ≃+* A) (P : Ideal A)
    {W Z : Opens (ComplexModel n)} (h : W = Z) (hpW : p ∈ W) (hpZ : p ∈ Z)
    (C : OriginalModules W)
    (κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf W)) ⟶ C)
    (hC : primeTargetProperty p a₀ P W hpW C κ) :
    primeTargetProperty p a₀ P Z hpZ (castOriginalModule h C) (castOriginalQuotient h κ) := by
  cases h
  exact hC

def primeTargetOnDomain
    {n : ℕ} {p : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p)}
    (B : NativePrimeAllOpenCokernelData p P) (W : Opens (ComplexModel n)) (hWB : W ≤ B.old.U) :
    OriginalModules W :=
  castOriginalModule (original_image_inverseImage B.old.U W hWB)
    (cokernel (originalRestrictedCyclicRelation B.old.U (inverseImageOpen B.old.U W) B.old.δ))

def primeQuotientOnDomain
    {n : ℕ} {p : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p)}
    (B : NativePrimeAllOpenCokernelData p P) (W : Opens (ComplexModel n)) (hWB : W ≤ B.old.U) :
    SheafOfModules.unit (forgetRing (originalOpenStructureSheaf W)) ⟶ primeTargetOnDomain B W hWB :=
  castOriginalQuotient (original_image_inverseImage B.old.U W hWB)
    (cokernel.π (originalRestrictedCyclicRelation B.old.U (inverseImageOpen B.old.U W) B.old.δ))

theorem prime_target_on_domain_property
    {n : ℕ} (p : ComplexModel n) {A : Type} [CommRing A]
    (a₀ : HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) p ≃+* A) (P : Ideal A)
    (B : NativePrimeAllOpenCokernelData p (Ideal.comap a₀.toRingHom P))
    (W : Opens (ComplexModel n)) (hpW : p ∈ W) (hWB : W ≤ B.old.U) :
    primeTargetProperty p a₀ P W hpW (primeTargetOnDomain B W hWB)
      (primeQuotientOnDomain B W hWB) := by
  exact cast_prime_target_property p a₀ P
    (original_image_inverseImage B.old.U W hWB) _ hpW _ _
    (native_prime_target_property p a₀ P B (inverseImageOpen B.old.U W) hpW)

def scalar_kernel_iso
    {A R : Type} [CommRing A] [CommRing R] (α : R ≃+* A)
    {M N : ModuleCat.{0} R} (φ : M ⟶ N) :
    (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj (ModuleCat.of R φ.hom.ker) ≅
      ModuleCat.of A ((ModuleCat.restrictScalars.{0} α.symm.toRingHom).map φ).hom.ker := by
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
  let f : S.obj (ModuleCat.of R φ.hom.ker) →ₗ[A] (S.map φ).hom.ker :=
    { toFun := fun x => ⟨x.val, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearEquiv.ofBijective f ⟨
    fun x y h => Subtype.ext (congrArg Subtype.val h),
    fun y => ⟨⟨y.val, y.property⟩, rfl⟩⟩).toModuleIso

theorem kernel_change_map
    {A : Type} [CommRing A] {T C : ModuleCat.{0} A}
    {f g : T ⟶ C} (h : f = g) :
    ∃ e : ModuleCat.of A f.hom.ker ≅ ModuleCat.of A g.hom.ker,
      e.hom ≫ ModuleCat.ofHom g.hom.ker.subtype = ModuleCat.ofHom f.hom.ker.subtype := by
  cases h
  exact ⟨Iso.refl _, rfl⟩

theorem lift_layer_factor
    {A R M : Type} [CommRing A] [CommRing R] [AddCommGroup M] [Module A M]
    (α : R ≃+* A) (T C : ModuleCat.{0} R)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj T ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj C ≅ ModuleCat.of A (A ⧸ P)) :
    let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
    let ψ := η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv
    ∃ (φ : T ⟶ C), Function.Surjective φ ∧ S.map φ = ψ ∧
      ∃ k : S.obj (ModuleCat.of R φ.hom.ker) ≅ ModuleCat.of A N₀,
        k.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
          S.map (ModuleCat.ofHom φ.hom.ker.subtype) ≫ η.hom := by
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
  let ψ := η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv
  let : S.IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{0, 0, 0} α.symm).isEquivalence_functor
  let φ := S.preimage ψ
  have hmap : S.map φ = ψ := S.map_preimage ψ
  obtain ⟨hsurj, k, hk⟩ := layer_factor_kernel N₀ N₁ hle P e (S.obj T) (S.obj C) η θ
  have hφ : Function.Surjective φ := by
    intro c
    obtain ⟨t, ht⟩ := hsurj (show S.obj C from c)
    refine ⟨t, ?_⟩
    have h := congrArg (fun f : S.obj T ⟶ S.obj C => f t) hmap
    exact h.trans ht
  have hdata : ∃ k : S.obj (ModuleCat.of R φ.hom.ker) ≅ ModuleCat.of A N₀,
      k.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
        S.map (ModuleCat.ofHom φ.hom.ker.subtype) ≫ η.hom := by
    obtain ⟨eEq, heEq⟩ := kernel_change_map hmap
    refine ⟨scalar_kernel_iso α φ ≪≫ eEq ≪≫ k, ?_⟩
    calc
      _ = (scalar_kernel_iso α φ).hom ≫ eEq.hom ≫
          ModuleCat.ofHom ψ.hom.ker.subtype ≫ η.hom := by
        simp only [Iso.trans_hom, Category.assoc, hk]
      _ = (scalar_kernel_iso α φ).hom ≫ ModuleCat.ofHom (S.map φ).hom.ker.subtype ≫ η.hom := by
        rw [← Category.assoc eEq.hom, heEq]
      _ = _ := rfl
  exact ⟨φ, hφ, hmap, hdata⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem zero_stalk_native_neighborhood
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (F : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    [F.IsFinitePresentation] (p : U)
    (hzero : Subsingleton ((nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj F)) :
    ∃ (V : Opens (TopCat.of U)) (_hpV : p ∈ V),
      IsZero ((localOverTransport X U V).obj (F.over V)) := by
  let R := (X.restrict U.isOpenEmbedding).𝒪
  let : Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf p) := hzero
  have hstalk : stalkLinearMapOfOver R ⊤ (𝟙 (F.over ⊤)) p (by trivial) =
      stalkLinearMapOfOver R ⊤ (0 : F.over ⊤ ⟶ F.over ⊤) p (by trivial) := by
    ext m
    exact Subsingleton.elim _ _
  obtain ⟨V, hV, hpV, h⟩ := exists_restriction_eq_of_isFiniteType R ⊤
    (𝟙 (F.over ⊤)) 0 p (by trivial) hstalk
  have hid : 𝟙 (F.over V) = (0 : F.over V ⟶ F.over V) := by
    calc
      _ = HironakaChowNativeFinitePresentationSpreading.restrictOverHom R ⊤ V hV
          (𝟙 (F.over ⊤)) := by ext B m; rfl
      _ = HironakaChowNativeFinitePresentationSpreading.restrictOverHom R ⊤ V hV 0 := h
      _ = 0 := by ext B m; rfl
  refine ⟨V, hpV, (IsZero.iff_id_eq_zero _).mpr ?_⟩
  let T := localOverTransport X U V
  calc
    𝟙 (T.obj (F.over V)) = T.map (𝟙 (F.over V)) := (T.map_id _).symm
    _ = T.map 0 := congrArg T.map hid
    _ = 0 := by ext B m; rfl


theorem assembled_original_layer
    {A R M : Type} [CommRing A] [CommRing R] [AddCommGroup M] [Module A M]
    (α : R ≃+* A) (P₀ P₁ : ModuleCat.{0} R)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj P₀ ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj P₁ ≅ ModuleCat.of A (A ⧸ P))
    (φ : P₀ ⟶ P₁)
    (hφ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map φ =
      η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv)
    (k : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj (ModuleCat.of R φ.hom.ker) ≅
      ModuleCat.of A N₀)
    (hk : k.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
      (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map
        (ModuleCat.ofHom φ.hom.ker.subtype) ≫ η.hom)
    {𝒞 : Type 1} [Category.{0} 𝒞] (F : 𝒞 ⥤ ModuleCat.{0} R)
    {T C K : 𝒞} (q : T ⟶ C) (j : K ⟶ T)
    (ρT : F.obj T ≅ P₀) (ρC : F.obj C ≅ P₁)
    (hSquare : F.map q ≫ ρC.hom = ρT.hom ≫ φ)
    (eK : F.obj K ≅ ModuleCat.of R φ.hom.ker)
    (hK : eK.hom ≫ ModuleCat.ofHom φ.hom.ker.subtype = F.map j ≫ ρT.hom) :
    let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
    let η' := S.mapIso ρT ≪≫ η
    let θ' := S.mapIso ρC ≪≫ θ
    ∃ η₀ : (F ⋙ S).obj K ≅ ModuleCat.of A N₀,
      η₀.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) = (F ⋙ S).map j ≫ η'.hom ∧
      (F ⋙ S).map q ≫ θ'.hom =
        η'.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom := by
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
  have hKS : S.map eK.hom ≫ S.map (ModuleCat.ofHom φ.hom.ker.subtype) =
      S.map (F.map j) ≫ S.map ρT.hom := by
    simpa only [Functor.map_comp] using congrArg (fun f => S.map f) hK
  have hQS : S.map (F.map q) ≫ S.map ρC.hom = S.map ρT.hom ≫ S.map φ := by
    simpa only [Functor.map_comp] using congrArg (fun f => S.map f) hSquare
  refine ⟨S.mapIso eK ≪≫ k, ?_, ?_⟩
  · change (S.map eK.hom ≫ k.hom) ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
      S.map (F.map j) ≫ (S.map ρT.hom ≫ η.hom)
    rw [Category.assoc, hk, ← Category.assoc, hKS, Category.assoc]
  · change S.map (F.map q) ≫ (S.map ρC.hom ≫ θ.hom) =
      (S.map ρT.hom ≫ η.hom) ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom
    rw [← Category.assoc, hQS, Category.assoc, hφ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

def originalTransportedStalk
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (p : U) (hpV : p ∈ V) :
    SheafOfModules.{0}
        (forgetRing (X.restrict (U.overEquivalence.inverse.obj V).left.isOpenEmbedding).𝒪) ⥤
      ModuleCat.{0} ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) :=
  nativeStalkFunctor
      (X.restrict (U.overEquivalence.inverse.obj V).left.isOpenEmbedding).𝒪
      (⟨p.val, ⟨p, hpV, rfl⟩⟩ : (U.overEquivalence.inverse.obj V).left) ⋙
    ModuleCat.restrictScalars.{0} (localOverRingStalkEquiv X U V p hpV).symm.toRingHom

theorem inverse_inclusion_square
    {𝒞 : Type 1} [Category.{0} 𝒞] {K T N₀ N₁ : 𝒞}
    (η₀ : K ≅ N₀) (η₁ : T ≅ N₁) (j : K ⟶ T) (inc : N₀ ⟶ N₁)
    (h : η₀.hom ≫ inc = j ≫ η₁.hom) : η₀.inv ≫ j = inc ≫ η₁.inv := by
  calc
    _ = η₀.inv ≫ j ≫ η₁.hom ≫ η₁.inv := by simp only [Iso.hom_inv_id, Category.comp_id]
    _ = η₀.inv ≫ (η₀.hom ≫ inc) ≫ η₁.inv := by rw [h]; simp only [Category.assoc]
    _ = _ := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem quotient_numerator_squares
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (N₀ N₁ : Submodule A M) (P : Ideal A)
    (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    {T C : ModuleCat.{0} A} (q : T ⟶ C)
    (η : T ≅ ModuleCat.of A N₁) (θ : C ≅ ModuleCat.of A (A ⧸ P))
    (h : q ≫ θ.hom = η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom) :
    (∀ x : T, θ.hom (q x) = e (Submodule.Quotient.mk (η.hom x))) ∧
    (∀ z : N₁, θ.inv (e (Submodule.Quotient.mk z)) = q (η.inv z)) := by
  have hf (x : T) : θ.hom (q x) = e (Submodule.Quotient.mk (η.hom x)) :=
    congrArg (fun f : T ⟶ ModuleCat.of A (A ⧸ P) => f x) h
  refine ⟨hf, ?_⟩
  intro z
  apply θ.toLinearEquiv.injective
  exact (Iso.inv_hom_id_apply θ _).trans
    ((congrArg (fun t => e (Submodule.Quotient.mk t)) (Iso.inv_hom_id_apply η z)).symm.trans
      (hf (η.inv z)).symm)

set_option backward.isDefEq.respectTransparency.types false in
def nativeKernelOnOpen
    (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat)
    (M N : SheafOfModules.{0}
      (forgetRing ((X).restrict U.isOpenEmbedding).𝒪))
    (p : U)
    (φ : (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj M ⟶
      (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj N)
    (hφ : Function.Surjective φ)     (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : M.over V ⟶ N.over V) : Prop :=
      let W : Opens X.toTopCat := (U.overEquivalence.inverse.obj V).left
      let Y : LocallyRingedSpace.{0} := X.restrict W.isOpenEmbedding
      let T : SheafOfModules.{0}
        (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
        ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V) ⥤
          SheafOfModules.{0} (forgetRing Y.𝒪) := localOverTransport X U V
      let M' : SheafOfModules.{0} (forgetRing Y.𝒪) := T.obj (M.over V)
      let N' : SheafOfModules.{0} (forgetRing Y.𝒪) := T.obj (N.over V)
      let q : M' ⟶ N' := T.map b
      let K : SheafOfModules.{0} (forgetRing Y.𝒪) := kernel q
      let i : K ⟶ M' := kernel.ι q
      let C : SheafOfModules.{0} (forgetRing Y.𝒪) := cokernel i
      let π : M' ⟶ C := cokernel.π i
      let A := ↑(TopCat.Presheaf.stalk
        ((X.restrict U.isOpenEmbedding).𝒪.obj) p)
      let F := originalTransportedStalk X U V p hpV
      let ρM := native_original_stalk_iso X U V M p hpV
      let ρN := native_original_stalk_iso X U V N p hpV
      Epi q ∧ M'.IsFinitePresentation ∧ N'.IsFinitePresentation ∧
      K.IsFinitePresentation ∧
      F.map q ≫ ρN.hom = ρM.hom ≫ φ ∧
      ∃ (_hK : IsLimit (KernelFork.ofι i (kernel.condition q)))
        (_hC : IsColimit (CokernelCofork.ofπ q (kernel.condition q)))
        (eK : F.obj K ≅ ModuleCat.of A φ.hom.ker)
        (eC : C ≅ N'),
        eK.hom ≫ ModuleCat.ofHom φ.hom.ker.subtype = F.map i ≫ ρM.hom ∧
        eK.inv ≫ F.map i = ModuleCat.ofHom φ.hom.ker.subtype ≫ ρM.inv ∧
        π ≫ eC.hom = q ∧ q ≫ eC.inv = π ∧
        (∀ (B : Opens Y.toTopCat) (m : M'.val.obj (op B)),
          eC.hom.val.app (op B) (π.val.app (op B) m) = q.val.app (op B) m) ∧
        (∀ (B : Opens Y.toTopCat) (m : M'.val.obj (op B)),
          eC.inv.val.app (op B) (q.val.app (op B) m) = π.val.app (op B) m) ∧
        let σ := F.mapIso eC ≪≫ ρN
        let eQ := φ.hom.quotKerEquivOfSurjective hφ
        F.map π ≫ σ.hom = ρM.hom ≫ φ ∧
        φ ≫ σ.inv = ρM.inv ≫ F.map π ∧
        (∀ x : F.obj M',
          σ.hom (F.map π x) = eQ (Submodule.Quotient.mk (ρM.hom x))) ∧
        (∀ m : (nativeStalkFunctor
            ((X.restrict U.isOpenEmbedding).𝒪) p).obj M,
          σ.inv (φ m) = F.map π (ρM.inv m))

set_option backward.isDefEq.respectTransparency.types false in
def layerStepOnOpen
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (T C : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪)) (p : U)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (α : ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) ≃+* A)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj T) ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj C) ≅ ModuleCat.of A (A ⧸ P))
    (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : T.over V ⟶ C.over V) : Prop :=
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
    let W : Opens X.toTopCat := (U.overEquivalence.inverse.obj V).left
    let Y := X.restrict W.isOpenEmbedding
    let L := localOverTransport X U V
    let T' := L.obj (T.over V)
    let C' := L.obj (C.over V)
    let q := L.map b
    let K := kernel q
    let j := kernel.ι q
    let Z := cokernel j
    let π := cokernel.π j
    let F := originalTransportedStalk X U V p hpV
    let H := F ⋙ S
    let ρT := native_original_stalk_iso X U V T p hpV
    let ρC := native_original_stalk_iso X U V C p hpV
    let η' := S.mapIso ρT ≪≫ η
    let θ' := S.mapIso ρC ≪≫ θ
    Epi q ∧ T'.IsFinitePresentation ∧ C'.IsFinitePresentation ∧ K.IsFinitePresentation ∧
    ∃ (_hK : IsLimit (KernelFork.ofι j (kernel.condition q)))
      (_hC : IsColimit (CokernelCofork.ofπ q (kernel.condition q)))
      (eC : Z ≅ C') (η₀ : H.obj K ≅ ModuleCat.of A N₀),
      π ≫ eC.hom = q ∧ q ≫ eC.inv = π ∧
      (∀ (B : Opens Y.toTopCat) (m : T'.val.obj (op B)),
        eC.hom.val.app (op B) (π.val.app (op B) m) = q.val.app (op B) m) ∧
      (∀ (B : Opens Y.toTopCat) (m : T'.val.obj (op B)),
        eC.inv.val.app (op B) (q.val.app (op B) m) = π.val.app (op B) m) ∧
      η₀.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) = H.map j ≫ η'.hom ∧
      η₀.inv ≫ H.map j = ModuleCat.ofHom (Submodule.inclusion hle) ≫ η'.inv ∧
      H.map q ≫ θ'.hom = η'.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ∧
      (∀ x : H.obj T', θ'.hom (H.map q x) = e (Submodule.Quotient.mk (η'.hom x))) ∧
      (∀ z : N₁, θ'.inv (e (Submodule.Quotient.mk z)) = H.map q (η'.inv z)) ∧
      let σ := H.mapIso eC ≪≫ θ'
      H.map π ≫ σ.hom = η'.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ∧
      (∀ x : H.obj T', σ.hom (H.map π x) = e (Submodule.Quotient.mk (η'.hom x))) ∧
      (∀ z : N₁, σ.inv (e (Submodule.Quotient.mk z)) = H.map π (η'.inv z))



set_option backward.isDefEq.respectTransparency.types false in
def nativeLayerStep
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (T C : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪)) (p : U)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (α : ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) ≃+* A)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj T) ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj C) ≅ ModuleCat.of A (A ⧸ P)) : Prop :=
  let st := nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
  ∃ (φ : st.obj T ⟶ st.obj C), Function.Surjective φ ∧
    S.map φ = η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv ∧
  ∃ (V : Opens U) (hpV : p ∈ V) (b : T.over V ⟶ C.over V),
    Epi b ∧ ModuleCat.ofHom (stalkLinearMapOfOver ((X.restrict U.isOpenEmbedding).𝒪) V b p hpV) = φ ∧
    layerStepOnOpen X U T C p α N₀ N₁ hle P e η θ V hpV b

set_option backward.isDefEq.respectTransparency.types false in
theorem step_on_open_from_native_kernel
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (T C : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (α : ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) ≃+* A)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj T) ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj C) ≅ ModuleCat.of A (A ⧸ P))
    (φ : (nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj T ⟶
      (nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj C)
    (hφ : Function.Surjective φ)
    (hmap : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map φ =
      η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv)
    (k : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      (ModuleCat.of (↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p)) φ.hom.ker) ≅ ModuleCat.of A N₀)
    (hk : k.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
      (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map
        (ModuleCat.ofHom φ.hom.ker.subtype) ≫ η.hom)
    (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : T.over V ⟶ C.over V)
    (hProperties : nativeKernelOnOpen X U T C p φ hφ V hpV b) :
    layerStepOnOpen X U T C p α N₀ N₁ hle P e η θ V hpV b := by
  let st := nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
  obtain ⟨hq, hTfp, hCfp, hKfp, hSquare, hKernel, hCokernel, eK, eC,
    heK, _, heC, heCinv, hSection, hSectionInv, _, _, _, _⟩ := hProperties
  let W : Opens X.toTopCat := (U.overEquivalence.inverse.obj V).left
  let L := localOverTransport X U V
  let q := L.map b
  let K := kernel q
  let j := kernel.ι q
  let π := cokernel.π j
  let F := originalTransportedStalk X U V p hpV
  let H := F ⋙ S
  let ρT := native_original_stalk_iso X U V T p hpV
  let ρC := native_original_stalk_iso X U V C p hpV
  let η' := S.mapIso ρT ≪≫ η
  let θ' := S.mapIso ρC ≪≫ θ
  obtain ⟨η₀, hInc, hQuot⟩ := assembled_original_layer α (st.obj T) (st.obj C)
    N₀ N₁ hle P e η θ φ hmap k hk F q j ρT ρC hSquare eK heK
  have hInv := inverse_inclusion_square η₀ η' (H.map j) (ModuleCat.ofHom (Submodule.inclusion hle)) hInc
  have hNums := quotient_numerator_squares N₀ N₁ P e (H.map q) η' θ' hQuot
  let σ := H.mapIso eC ≪≫ θ'
  have hProj : H.map π ≫ σ.hom =
      η'.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom := by
    calc
      _ = H.map (π ≫ eC.hom) ≫ θ'.hom := by
        simp only [σ, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      _ = H.map q ≫ θ'.hom := by rw [heC]
      _ = _ := hQuot
  have hProjNums := quotient_numerator_squares N₀ N₁ P e (H.map π) η' σ hProj
  exact ⟨hq, hTfp, hCfp, hKfp, hKernel, hCokernel, eC, η₀,
    heC, heCinv, hSection, hSectionInv, hInc, hInv, hQuot, hNums.1, hNums.2,
    hProj, hProjNums.1, hProjNums.2⟩






set_option backward.isDefEq.respectTransparency.types false in
theorem native_layer_step_from_chosen_kernel
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (T C : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (α : ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) ≃+* A)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj T) ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj C) ≅ ModuleCat.of A (A ⧸ P))
    (φ : (nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj T ⟶
      (nativeStalkFunctor ((X.restrict U.isOpenEmbedding).𝒪) p).obj C)
    (hφ : Function.Surjective φ)
    (hmap : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map φ =
      η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv)
    (k : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      (ModuleCat.of (↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p)) φ.hom.ker) ≅ ModuleCat.of A N₀)
    (hk : k.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
      (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map
        (ModuleCat.ofHom φ.hom.ker.subtype) ≫ η.hom)
    (hChosen : ∃ (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : T.over V ⟶ C.over V),
      Epi b ∧ ModuleCat.ofHom (stalkLinearMapOfOver (X.restrict U.isOpenEmbedding).𝒪
        V b p hpV) = φ ∧ nativeKernelOnOpen X U T C p φ hφ V hpV b) :
    nativeLayerStep X U T C p α N₀ N₁ hle P e η θ := by
  obtain ⟨V, hpV, b, hb, hbφ, hProperties⟩ := hChosen
  refine ⟨φ, hφ, hmap, V, hpV, b, hb, hbφ, ?_⟩
  exact step_on_open_from_native_kernel X U T C p α N₀ N₁ hle P e η θ
    φ hφ hmap k hk V hpV b hProperties


set_option backward.isDefEq.respectTransparency.types false in
theorem native_layer_step_of_phi
    (n : ℕ) (U : Opens (ComplexModel n)) (T C : OriginalModules U)
    [hT : T.IsFinitePresentation] [hC : C.IsFinitePresentation] (p : U)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (α : OriginalRingStalk U p ≃+* A)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj T) ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj C) ≅ ModuleCat.of A (A ⧸ P))
    (φ : (nativeStalkFunctor (originalOpenStructureSheaf U) p).obj T ⟶
      (nativeStalkFunctor (originalOpenStructureSheaf U) p).obj C)
    (hφ : Function.Surjective φ)
    (hmap : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map φ =
      η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv)
    (k : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      (ModuleCat.of (OriginalRingStalk U p) φ.hom.ker) ≅ ModuleCat.of A N₀)
    (hk : k.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
      (ModuleCat.restrictScalars.{0} α.symm.toRingHom).map
        (ModuleCat.ofHom φ.hom.ker.subtype) ≫ η.hom) :
    nativeLayerStep (originalSpace n) U T C p α N₀ N₁ hle P e η θ := by
  apply native_layer_step_from_chosen_kernel (originalSpace n) U T C p α N₀ N₁ hle P e η θ
    φ hφ hmap k hk
  exact @HironakaNativeSameMapKernelComparison.exists_original_same_stalk_kernel n U T C hT hC p φ hφ


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_native_layer_step
    (n : ℕ) (U : Opens (ComplexModel n)) (T C : OriginalModules U)
    [hT : T.IsFinitePresentation] [hC : C.IsFinitePresentation] (p : U)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (α : OriginalRingStalk U p ≃+* A)
    (N₀ N₁ : Submodule A M) (hle : N₀ ≤ N₁)
    (P : Ideal A) (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[A] A ⧸ P)
    (η : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj T) ≅ ModuleCat.of A N₁)
    (θ : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).obj
      ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj C) ≅ ModuleCat.of A (A ⧸ P)) :
    nativeLayerStep (originalSpace n) U T C p α N₀ N₁ hle P e η θ := by
  let st := nativeStalkFunctor (originalOpenStructureSheaf U) p
  obtain ⟨φ, hφ, hmap, k, hk⟩ := lift_layer_factor α (st.obj T) (st.obj C) N₀ N₁ hle P e η θ
  exact native_layer_step_of_phi n U T C p α N₀ N₁ hle P e η θ φ hφ hmap k hk

structure SelectedPrimeSeries (A : Type) [CommRing A] (M : ModuleCat.{0} A) where
  s : RelSeries {(N₀, N₁) |
    Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M) N₀ N₁}
  P : Fin s.length → PrimeSpectrum A
  e : ∀ i : Fin s.length,
    (↥(s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[A] A ⧸ (P i).1
  head : s.head = ⊥
  last : s.last = ⊤
  mono : ∀ i : Fin s.length, s i.castSucc ≤ s i.succ
  zeroLength : Subsingleton M → s.length = 0

theorem series_zero_subsingleton
    {A : Type} [CommRing A] {M : ModuleCat.{0} A} (d : SelectedPrimeSeries A M)
    (h : d.s.length = 0) : Subsingleton M := by
  have hi : (0 : Fin (d.s.length + 1)) = Fin.last d.s.length :=
    Fin.ext (by simp only [Fin.val_zero, Fin.val_last, h])
  have hsame : d.s.head = d.s.last := congrArg d.s hi
  have hbt : (⊥ : Submodule A M) = ⊤ := d.head.symm.trans (hsame.trans d.last)
  have hm (m : M) : m = 0 := by
    have hmem : m ∈ (⊥ : Submodule A M) := hbt.symm ▸ Submodule.mem_top
    exact hmem
  exact ⟨fun x y => (hm x).trans (hm y).symm⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem selected_original_series
    (n : ℕ) (U : Opens (ComplexModel n)) (F : OriginalModules U)
    [F.IsFinitePresentation] (p : U) :
    Nonempty (SelectedPrimeSeries (OriginalRingStalk U p)
      ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F)) := by
  obtain ⟨_, _, s, P, e, hhead, hlast, hmono, hz⟩ :=
    HironakaChowNativeStalkPrimeFiltration.exists_original_stalk_prime_filtration n U F p
  exact ⟨⟨s, P, e, hhead, hlast, hmono, hz⟩⟩

def submodule_top_iso
    {A : Type} [CommRing A] (M : ModuleCat.{0} A) (N : Submodule A M) (h : N = ⊤) :
    M ≅ ModuleCat.of A N := by
  cases h
  exact Submodule.topEquiv.symm.toModuleIso

theorem source_image_le_domain
    {n : ℕ} (U D : Opens (ComplexModel n)) :
    originalImageOpen U (inverseImageOpen U D) ≤ D := by
  rintro x ⟨u, hu, rfl⟩
  exact hu

end

end Hironaka.HironakaG10PNLayerStep
