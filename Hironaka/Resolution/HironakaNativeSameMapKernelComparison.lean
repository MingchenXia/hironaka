import Hironaka.Resolution.HironakaChowNativeSameStalkEpimorphism
import Hironaka.Resolution.HironakaChowNativeFinitePresentationKernelCoherence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! The literal kernel and quotient of the same original epimorphic lift.
Blueprint first: `hironaka-native-same-map-kernel-comparison.tex`.
The original stalk map is an independent input; its local lift is chosen once.
No replacement module action, comparison packet or section-surjectivity premise.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaNativeSameMapKernelComparison

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeModuleStalkExact HironakaChowNativeLocalOverStalkTransport
  HironakaChowNativeFreePartContinuation
  HironakaChowNativeFinitePresentationKernelCoherence

set_option backward.isDefEq.respectTransparency.types false in
private def originalLocalStalkIso
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) :
    (ModuleCat.restrictScalars.{0} (localOverRingStalkEquiv X U V p hpV).symm.toRingHom).obj
      ((nativeStalkFunctor
          (X.restrict (U.overEquivalence.inverse.obj V).left.isOpenEmbedding).𝒪
          (⟨p.val, ⟨p, hpV, rfl⟩⟩ : (U.overEquivalence.inverse.obj V).left)).obj
        ((localOverTransport X U V).obj (M.over V))) ≅
      (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj M :=
  localOverModuleStalkIso X U V M p hpV

private def transportedStalkFunctor
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (p : U) (hpV : p ∈ V) :
    SheafOfModules.{0}
        (forgetRing (X.restrict (U.overEquivalence.inverse.obj V).left.isOpenEmbedding).𝒪) ⥤
      ModuleCat.{0} ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) :=
  nativeStalkFunctor
      (X.restrict (U.overEquivalence.inverse.obj V).left.isOpenEmbedding).𝒪
      (⟨p.val, ⟨p, hpV, rfl⟩⟩ : (U.overEquivalence.inverse.obj V).left) ⋙
    ModuleCat.restrictScalars.{0} (localOverRingStalkEquiv X U V p hpV).symm.toRingHom

private theorem transportedStalkFunctor_preservesFiniteLimits
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (p : U) (hpV : p ∈ V) :
    PreservesFiniteLimits (transportedStalkFunctor X U V p hpV) := by
  let W : Opens X.toTopCat := (U.overEquivalence.inverse.obj V).left
  let pW : W := ⟨p.val, ⟨p, hpV, rfl⟩⟩
  let α := localOverRingStalkEquiv X U V p hpV
  change PreservesFiniteLimits
    (nativeStalkFunctor (X.restrict W.isOpenEmbedding).𝒪 pW ⋙
      ModuleCat.restrictScalars.{0} α.symm.toRingHom)
  have hF : PreservesFiniteLimits (nativeStalkFunctor (X.restrict W.isOpenEmbedding).𝒪 pW) :=
    nativeStalkFunctor_preservesFiniteLimits (X.restrict W.isOpenEmbedding).𝒪 pW
  let : (ModuleCat.restrictScalars.{0} α.symm.toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{0, 0, 0} α.symm).isEquivalence_functor
  let : PreservesLimitsOfSize.{0, 0} (ModuleCat.restrictScalars.{0} α.symm.toRingHom) :=
    inferInstance
  have hS : PreservesFiniteLimits (ModuleCat.restrictScalars.{0} α.symm.toRingHom) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hF hS

private theorem transportedStalkFunctor_preservesZeroMorphisms
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (p : U) (hpV : p ∈ V) :
    (transportedStalkFunctor X U V p hpV).PreservesZeroMorphisms := by
  let : PreservesFiniteLimits (transportedStalkFunctor X U V p hpV) :=
    transportedStalkFunctor_preservesFiniteLimits X U V p hpV
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private def nativeOriginalRho
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) :
    (transportedStalkFunctor X U V p hpV).obj
        ((localOverTransport X U V).obj (M.over V)) ≅
      (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj M :=
  originalLocalStalkIso X U V M p hpV

private theorem kernelQuotientComparison
    {𝒞 : Type 1} [Category.{0} 𝒞] [Abelian 𝒞]
    {A : Type} [Ring A] (F : 𝒞 ⥤ ModuleCat.{0} A)
    [PreservesFiniteLimits F] [F.PreservesZeroMorphisms]
    {M' N' : 𝒞} (q : M' ⟶ N') [Epi q]
    {P Q : ModuleCat.{0} A} (φ : P ⟶ Q) (hφ : Function.Surjective φ)
    (ρM : F.obj M' ≅ P) (ρN : F.obj N' ≅ Q)
    (hSquare : F.map q ≫ ρN.hom = ρM.hom ≫ φ) :
    let K := kernel q
    let i : K ⟶ M' := kernel.ι q
    let C := cokernel i
    let π : M' ⟶ C := cokernel.π i
    ∃ (_hK : IsLimit (KernelFork.ofι i (kernel.condition q)))
      (_hC : IsColimit (CokernelCofork.ofπ q (kernel.condition q)))
      (eK : F.obj K ≅ ModuleCat.of A φ.hom.ker) (eC : C ≅ N'),
      eK.hom ≫ ModuleCat.ofHom φ.hom.ker.subtype = F.map i ≫ ρM.hom ∧
      eK.inv ≫ F.map i = ModuleCat.ofHom φ.hom.ker.subtype ≫ ρM.inv ∧
      π ≫ eC.hom = q ∧ q ≫ eC.inv = π ∧
      let σ := F.mapIso eC ≪≫ ρN
      let eQ := φ.hom.quotKerEquivOfSurjective hφ
      F.map π ≫ σ.hom = ρM.hom ≫ φ ∧
      φ ≫ σ.inv = ρM.inv ≫ F.map π ∧
      (∀ x : F.obj M',
        σ.hom (F.map π x) = eQ (Submodule.Quotient.mk (ρM.hom x))) ∧
      (∀ m : P, σ.inv (φ m) = F.map π (ρM.inv m)) := by
  let K := kernel q
  let i : K ⟶ M' := kernel.ι q
  let C := cokernel i
  let π : M' ⟶ C := cokernel.π i
  let eK : F.obj K ≅ ModuleCat.of A φ.hom.ker :=
    PreservesKernel.iso F q ≪≫
      kernel.mapIso (F.map q) φ ρM ρN hSquare ≪≫ ModuleCat.kernelIsoKer φ
  have heK : eK.hom ≫ ModuleCat.ofHom φ.hom.ker.subtype =
      F.map i ≫ ρM.hom := by
    dsimp only [eK, Iso.trans_hom]
    simp only [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype]
    change (PreservesKernel.iso F q).hom ≫
      (kernel.map (F.map q) φ ρM.hom ρN.hom hSquare ≫ kernel.ι φ) =
        F.map i ≫ ρM.hom
    rw [kernel.map, kernel.lift_ι, ← Category.assoc,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  have heKinv : eK.inv ≫ F.map i =
      ModuleCat.ofHom φ.hom.ker.subtype ≫ ρM.inv := by
    have h := congrArg (fun f => eK.inv ≫ f ≫ ρM.inv) heK
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  let cHom : C ⟶ N' := cokernel.desc i q (kernel.condition q)
  let cInv : N' ⟶ C := Abelian.epiDesc q π (cokernel.condition i)
  have hHom : π ≫ cHom = q := cokernel.π_desc i q (kernel.condition q)
  have hInv : q ≫ cInv = π := Abelian.comp_epiDesc q π (cokernel.condition i)
  let eC : C ≅ N' := {
    hom := cHom
    inv := cInv
    hom_inv_id := by
      apply (cancel_epi π).mp
      rw [← Category.assoc, hHom, hInv, Category.comp_id]
    inv_hom_id := by
      apply (cancel_epi q).mp
      rw [← Category.assoc, hInv, hHom, Category.comp_id] }
  let σ : F.obj C ≅ Q := F.mapIso eC ≪≫ ρN
  have hσ : F.map π ≫ σ.hom = ρM.hom ≫ φ := by
    change F.map π ≫ (F.map cHom ≫ ρN.hom) = _
    rw [← Category.assoc, ← F.map_comp, hHom, hSquare]
  have hσinv : φ ≫ σ.inv = ρM.inv ≫ F.map π := by
    have h := congrArg (fun f => ρM.inv ≫ f ≫ σ.inv) hσ
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  refine ⟨kernelIsKernel q,
    Abelian.epiIsCokernelOfKernel (KernelFork.ofι i (kernel.condition q))
      (kernelIsKernel q), eK, eC, heK, heKinv, hHom, hInv, hσ, hσinv, ?_, ?_⟩
  · intro x
    have h := congrArg (fun (f : F.obj M' ⟶ Q) => f x) hσ
    simpa only [ConcreteCategory.comp_apply,
      LinearMap.quotKerEquivOfSurjective_apply_mk] using h
  · intro m
    have h := congrArg (fun (f : P ⟶ F.obj C) => f m) hσinv
    exact h

set_option backward.isDefEq.respectTransparency.types false in
private def sameLiftNativeProperties
    (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat)
    (M N : SheafOfModules.{0}
      (forgetRing ((X).restrict U.isOpenEmbedding).𝒪))
    (p : U)
    (φ : (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj M ⟶
      (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj N)
    (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : M.over V ⟶ N.over V) : Prop :=
  let T := localOverTransport X U V
  let M' := T.obj (M.over V)
  let N' := T.obj (N.over V)
  let q : M' ⟶ N' := T.map b
  let F := transportedStalkFunctor X U V p hpV
  let ρM := nativeOriginalRho X U V M p hpV
  let ρN := nativeOriginalRho X U V N p hpV
  Epi q ∧ M'.IsFinitePresentation ∧ N'.IsFinitePresentation ∧
    F.map q ≫ ρN.hom = ρM.hom ≫ φ

set_option backward.isDefEq.respectTransparency.types false in
private def sameLiftKernelData
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
      let F := transportedStalkFunctor X U V p hpV
      let ρM := nativeOriginalRho X U V M p hpV
      let ρN := nativeOriginalRho X U V N p hpV
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
private def sameMapKernelOutput
    (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat)
    (M N : SheafOfModules.{0}
      (forgetRing ((X).restrict U.isOpenEmbedding).𝒪))
    (p : U)
    (φ : (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj M ⟶
      (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj N)
    (hφ : Function.Surjective φ) : Prop :=
    ∃ (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : M.over V ⟶ N.over V),
      Epi b ∧
      ModuleCat.ofHom (stalkLinearMapOfOver
        ((X).restrict U.isOpenEmbedding).𝒪 V b p hpV) = φ ∧
      sameLiftKernelData X U M N p φ hφ V hpV b

set_option backward.isDefEq.respectTransparency.types false in
private theorem kernelData_of_same_native_properties
    (X : LocallyRingedSpace.{0})
    (hKernel : ∀ (W : Opens X.toTopCat)
      {P Q : SheafOfModules.{0} (forgetRing (X.restrict W.isOpenEmbedding).𝒪)}
      [P.IsFinitePresentation] [Q.IsFinitePresentation] (f : P ⟶ Q),
        (kernel f).IsFinitePresentation)
    (U : Opens X.toTopCat)
    (M N : SheafOfModules.{0}
      (forgetRing ((X).restrict U.isOpenEmbedding).𝒪))
    (p : U)
    (φ : (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj M ⟶
      (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj N)
    (hφ : Function.Surjective φ) 
    (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : M.over V ⟶ N.over V)
    (hProperties : sameLiftNativeProperties X U M N p φ V hpV b) :
    sameLiftKernelData X U M N p φ hφ V hpV b := by
  let R := (X.restrict U.isOpenEmbedding).𝒪
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
  let A := ↑(TopCat.Presheaf.stalk R.obj p)
  let F := transportedStalkFunctor X U V p hpV
  let ρM := nativeOriginalRho X U V M p hpV
  let ρN := nativeOriginalRho X U V N p hpV
  have hMother' : Epi q ∧ M'.IsFinitePresentation ∧ N'.IsFinitePresentation ∧
      F.map q ≫ ρN.hom = ρM.hom ≫ φ := hProperties
  obtain ⟨hq, hM, hN, hs⟩ := hMother'
  let : Epi q := hq
  let : M'.IsFinitePresentation := hM
  let : N'.IsFinitePresentation := hN
  have hKfp : K.IsFinitePresentation := @hKernel W M' N' hM hN q
  have hSquare : F.map q ≫ ρN.hom = ρM.hom ≫ φ := hs
  have hFL : PreservesFiniteLimits F :=
    transportedStalkFunctor_preservesFiniteLimits X U V p hpV
  have hFZ : F.PreservesZeroMorphisms :=
    transportedStalkFunctor_preservesZeroMorphisms X U V p hpV
  obtain ⟨hK, hC, eK, eC, heK, heKinv, hHom, hInv, hσ, hσinv, hNum, hInvNum⟩ :=
    @kernelQuotientComparison _ _ _ A _ F hFL hFZ M' N' q hq _ _ φ hφ ρM ρN hSquare
  refine ⟨hq, hM, hN, hKfp, hSquare, hK, hC, eK, eC,
    heK, heKinv, hHom, hInv, ?_, ?_, hσ, hσinv, hNum, hInvNum⟩
  · intro B m
    exact congrArg (fun (f : M' ⟶ N') => f.val.app (op B) m) hHom
  · intro B m
    exact congrArg (fun (f : M' ⟶ C) => f.val.app (op B) m) hInv


set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_same_stalk_kernel_of_open_kernel_coherence
    (X : LocallyRingedSpace.{0})
    (hKernel : ∀ (W : Opens X.toTopCat)
      {P Q : SheafOfModules.{0} (forgetRing (X.restrict W.isOpenEmbedding).𝒪)}
      [P.IsFinitePresentation] [Q.IsFinitePresentation] (f : P ⟶ Q),
        (kernel f).IsFinitePresentation)
    (U : Opens X.toTopCat)
    (M N : SheafOfModules.{0}
      (forgetRing ((X).restrict U.isOpenEmbedding).𝒪))
    [hMfp : M.IsFinitePresentation] [hNfp : N.IsFinitePresentation] (p : U)
    (φ : (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj M ⟶
      (nativeStalkFunctor ((X).restrict U.isOpenEmbedding).𝒪 p).obj N)
    (hφ : Function.Surjective φ) :
    sameMapKernelOutput X U M N p φ hφ := by
  obtain ⟨V, hpV, b, hb, hbφ, hProperties⟩ :=
    @HironakaChowNativeSameStalkEpimorphism.exists_original_same_stalk_epimorphism
      X U M N hMfp hNfp p φ hφ
  refine ⟨V, hpV, b, hb, hbφ, ?_⟩
  exact kernelData_of_same_native_properties X hKernel U M N p φ hφ V hpV b hProperties

set_option backward.isDefEq.respectTransparency.types false in
/-- The same original surjective stalk map internally produces its literal
native kernel and whole cokernel, including both original numerator squares. -/
theorem exists_original_same_stalk_kernel
    (n : ℕ) (U : Opens (originalSpace n).toTopCat)
    (M N : SheafOfModules.{0}
      (forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪))
    [hMfp : M.IsFinitePresentation] [hNfp : N.IsFinitePresentation] (p : U)
    (φ : (nativeStalkFunctor ((originalSpace n).restrict U.isOpenEmbedding).𝒪 p).obj M ⟶
      (nativeStalkFunctor ((originalSpace n).restrict U.isOpenEmbedding).𝒪 p).obj N)
    (hφ : Function.Surjective φ) :
    ∃ (V : Opens (TopCat.of U)) (hpV : p ∈ V) (b : M.over V ⟶ N.over V),
      Epi b ∧
      ModuleCat.ofHom (stalkLinearMapOfOver
        ((originalSpace n).restrict U.isOpenEmbedding).𝒪 V b p hpV) = φ ∧
      let X : LocallyRingedSpace.{0} := originalSpace n
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
      let F := transportedStalkFunctor X U V p hpV
      let ρM := nativeOriginalRho X U V M p hpV
      let ρN := nativeOriginalRho X U V N p hpV
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
          σ.inv (φ m) = F.map π (ρM.inv m)) := by
  exact @exists_same_stalk_kernel_of_open_kernel_coherence (originalSpace n)
    (fun W P Q hP hQ f =>
      @original_open_kernel_isFinitePresentation n W P Q hP hQ f)
    U M N hMfp hNfp p φ hφ

end Hironaka.HironakaNativeSameMapKernelComparison
