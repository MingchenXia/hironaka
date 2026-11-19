import Hironaka.Geometry.ProperSteinProjectiveCechSheafEqualizer
import Hironaka.Geometry.ProperSteinProjectiveCechFiniteGraded
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual ORIGINAL sheaf restriction diagram and native H0

Adapted from the generic native portion of same-workspace
`BingWangEntropy/SchemeSubsetCechSections.lean`,
SHA256 9b7114f1534982972f546921517bad31d6c34949b16f1f26eda5c26cb213c213.
Only Mathlib and owned Hironaka modules are imported.
No represented-module diagram is supplied as a premise.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace Hironaka.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section SingletonCocycles

variable {K I : Type u} [CommRing K] [LinearOrder I]
  (F : Finset I ⥤ ModuleCat.{u} K)

private def singletonIndex (S : Finset I) (hS : S.card = 1) : I :=
  (Finset.card_eq_one.mp hS).choose

omit [LinearOrder I] in
private theorem singletonIndex_eq (S : Finset I) (hS : S.card = 1) :
    S = {singletonIndex S hS} :=
  (Finset.card_eq_one.mp hS).choose_spec

omit [LinearOrder I] in
private theorem singletonTransport (a : ∀ i : I, F.obj {i}) {i j : I} (h : i = j) :
    F.map (eqToHom (congrArg (fun t => ({t} : Finset I)) h)) (a i) = a j := by
  subst j
  simp

/-- The true singleton cardinal term is the true family of singleton diagram values. -/
def subsetCechSingletonPieceEquiv :
    subsetCechCardPiece F 1 ≃ₗ[K] (∀ i : I, F.obj {i}) := by
  classical
  let assemble : (∀ i : I, F.obj {i}) →ₗ[K] subsetCechCardPiece F 1 := {
    toFun := fun a => ⟨fun S => if hS : S.card = 1 then
      F.map (eqToHom (singletonIndex_eq S hS).symm) (a (singletonIndex S hS)) else 0,
      by intro S hS; simp [hS]⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      funext S
      by_cases hS : S.card = 1 <;> simp [hS, map_add]
    map_smul' := by
      intro r a
      apply Subtype.ext
      funext S
      by_cases hS : S.card = 1 <;> simp [hS] }
  let evaluate : subsetCechCardPiece F 1 →ₗ[K] (∀ i : I, F.obj {i}) := {
    toFun := fun c i => c.val {i}
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  refine { evaluate with invFun := assemble, left_inv := ?_, right_inv := ?_ }
  · intro c
    apply Subtype.ext
    funext S
    by_cases hS : S.card = 1
    · have heq := singletonIndex_eq S hS
      change (if h : S.card = 1 then _ else 0) = c.val S
      rw [dif_pos hS]
      have hvalue := subsetCechRestriction_value_congr F c.val
        (show {singletonIndex S hS} ⊆ S by rw [← heq]) (Finset.Subset.refl S) heq.symm
      have harrow : eqToHom (singletonIndex_eq S hS).symm =
          homOfLE (show {singletonIndex S hS} ⊆ S by rw [← heq]) := Subsingleton.elim _ _
      simpa [subsetCechRestriction, harrow, evaluate] using hvalue
    · change (if h : S.card = 1 then _ else 0) = c.val S
      rw [dif_neg hS, c.property S hS]
  · intro a
    funext i
    change (if h : ({i} : Finset I).card = 1 then
      F.map (eqToHom (singletonIndex_eq {i} h).symm) (a (singletonIndex {i} h)) else 0) = a i
    rw [dif_pos (Finset.card_singleton i)]
    have heq : singletonIndex {i} (Finset.card_singleton i) = i := by
      have h := singletonIndex_eq {i} (Finset.card_singleton i)
      exact (Finset.singleton_inj.mp h).symm
    exact singletonTransport F a heq

/-- True singleton values are compatible exactly when their genuine overlap restrictions agree. -/
def actualSubsetSingletonCompatible : Submodule K (∀ i : I, F.obj {i}) where
  carrier := {a | ∀ i j, subsetCechRestriction F (by simp : ({i} : Finset I) ⊆ {i, j}) (a i) =
    subsetCechRestriction F (by simp : ({j} : Finset I) ⊆ {i, j}) (a j)}
  zero_mem' := by intro i j; simp
  add_mem' := by intro a b ha hb i j; simp only [Pi.add_apply, map_add, ha i j, hb i j]
  smul_mem' := by intro r a ha i j; simp only [Pi.smul_apply, map_smul, ha i j]

/-- The literal two-vertex differential is the difference of the two true overlap restrictions. -/
theorem subsetCechDifferential_pair (c : subsetCechCube F) (i j : I) (hij : i < j) :
    subsetCechDifferential F c {i, j} =
      subsetCechRestriction F (by simp : ({j} : Finset I) ⊆ {i, j}) (c {j}) -
      subsetCechRestriction F (by simp : ({i} : Finset I) ⊆ {i, j}) (c {i}) := by
  classical
  simp [subsetCechDifferential, subsetCechSign, Finset.filter_insert, Finset.filter_singleton,
    ne_of_lt hij, hij,
    not_lt_of_ge (le_of_lt hij), sub_eq_add_neg]
  exact congrArg₂ (fun a b => a + -b)
    (subsetCechRestriction_value_congr F c (Finset.erase_subset i {i, j})
      (by simp : ({j} : Finset I) ⊆ {i, j}) (Finset.erase_insert (by simp [ne_of_lt hij])))
    (subsetCechRestriction_value_congr F c (Finset.erase_subset j {i, j})
      (by simp : ({i} : Finset I) ⊆ {i, j})
      (by rw [Finset.erase_insert_of_ne (ne_of_lt hij), Finset.erase_singleton]; rfl))

/-- Vanishing of the literal first differential is exactly actual overlap agreement. -/
theorem subsetCechSingletonPiece_mem_kernel_iff (c : subsetCechCardPiece F 1) :
    c ∈ LinearMap.ker (subsetCechCardDifferential F 1) ↔
      subsetCechSingletonPieceEquiv F c ∈ actualSubsetSingletonCompatible F := by
  classical
  constructor
  · intro hc i j
    have hordered : ∀ i j : I, i < j →
        subsetCechRestriction F (by simp : ({i} : Finset I) ⊆ {i, j}) (c.val {i}) =
          subsetCechRestriction F (by simp : ({j} : Finset I) ⊆ {i, j}) (c.val {j}) := by
      intro i j hij
      have hz := congrArg (fun a : subsetCechCardPiece F 2 => a.val {i, j})
        (LinearMap.mem_ker.mp hc)
      change subsetCechDifferential F c.val {i, j} = 0 at hz
      rw [subsetCechDifferential_pair F c.val i j hij] at hz
      exact (sub_eq_zero.mp hz).symm
    change subsetCechRestriction F _ (c.val {i}) = subsetCechRestriction F _ (c.val {j})
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hordered i j hij
    · rfl
    · have hh := hordered j i hji
      have hh' := congrArg
        (subsetCechRestriction F (show ({j, i} : Finset I) ⊆ {i, j} by rw [Finset.pair_comm j i])) hh
      simpa only [subsetCechRestriction_comp] using hh'.symm
  · intro hc
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    funext S
    change subsetCechDifferential F c.val S = 0
    by_cases hS : S.card = 2
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hS
      rcases lt_or_gt_of_ne hij with hij | hji
      · rw [subsetCechDifferential_pair F c.val i j hij]
        exact sub_eq_zero.mpr (hc i j).symm
      · have hz : subsetCechDifferential F c.val {j, i} = 0 := by
          rw [subsetCechDifferential_pair F c.val j i hji]
          exact sub_eq_zero.mpr (hc j i).symm
        have hz' : ∀ S : Finset I, S = {j, i} → subsetCechDifferential F c.val S = 0 := by
          intro S hS
          subst S
          exact hz
        exact hz' {i, j} (Finset.pair_comm i j)
    · exact (subsetCechCardDifferential F 1 c).property S hS

/-- The literal native first-differential kernel is the true compatible singleton-family module. -/
def actualSubsetCechZeroCocyclesCompatibleEquiv :
    LinearMap.ker (subsetCechCardDifferential F 1) ≃ₗ[K] actualSubsetSingletonCompatible F := by
  let e := subsetCechSingletonPieceEquiv F
  exact {
    toFun := fun c => ⟨e c.val, (subsetCechSingletonPiece_mem_kernel_iff F c.val).mp c.property⟩
    invFun := fun a => ⟨e.symm a.val, (subsetCechSingletonPiece_mem_kernel_iff F (e.symm a.val)).mpr
      (by simpa only [e, LinearEquiv.apply_symm_apply] using a.property)⟩
    left_inv := by intro c; apply Subtype.ext; exact e.symm_apply_apply c.val
    right_inv := by intro a; apply Subtype.ext; exact e.apply_symm_apply a.val
    map_add' := by intro c d; apply Subtype.ext; exact e.map_add c.val d.val
    map_smul' := by intro r c; apply Subtype.ext; exact e.map_smul r c.val }

end SingletonCocycles

section RestrictScalarsCocycles

variable {K A I : Type u} [CommRing K] [CommRing A] [LinearOrder I]
  (F : Finset I ⥤ ModuleCat.{u} A) (c : K →+* A)

/-- The literal Čech cocycle kernel commutes with the true structural restriction of scalars. -/
def actualSubsetCechRestrictScalarsZeroCocyclesEquiv :
    (ModuleCat.restrictScalars c).obj
        (ModuleCat.of A (LinearMap.ker (subsetCechCardDifferential F 1))) ≃ₗ[K]
      LinearMap.ker (subsetCechCardDifferential (F ⋙ ModuleCat.restrictScalars c) 1) := by
  exact {
    toFun := fun a => ⟨⟨a.val.val, a.val.property⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact congrArg Subtype.val (LinearMap.mem_ker.mp a.property)⟩
    invFun := fun a => ⟨⟨a.val.val, a.val.property⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact congrArg Subtype.val (LinearMap.mem_ker.mp a.property)⟩
    left_inv := by intro a; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro a; apply Subtype.ext; apply Subtype.ext; rfl
    map_add' := by intro a b; apply Subtype.ext; apply Subtype.ext; rfl
    map_smul' := by intro r a; apply Subtype.ext; apply Subtype.ext; rfl }

end RestrictScalarsCocycles

section SchemeRestrictionDiagram

variable {X : Scheme.{u}} (L : X.Modules) {I : Type u} [LinearOrder I]
  (U : I → X.Opens)

/-- Actual finite intersections of the actual coordinate opens. -/
def actualSchemeSubsetOpen (S : Finset I) : X.Opens := S.inf U

omit [LinearOrder I] in
/-- A larger coordinate subset gives a smaller actual intersection open. -/
theorem actualSchemeSubsetOpen_antitone {S T : Finset I} (hST : S ⊆ T) :
    actualSchemeSubsetOpen U T ≤ actualSchemeSubsetOpen U S :=
  Finset.inf_mono hST

/-- Native sheaf restriction is linear for the true global regular-function action. -/
def actualSchemeModuleRestriction {V W : X.Opens} (hVW : V ≤ W) :
    letI := localSectionsGlobalModule L W
    letI := localSectionsGlobalModule L V
    bundleSections L W →ₗ[Γ(X, ⊤)] bundleSections L V := by
  letI := localSectionsGlobalModule L W
  letI := localSectionsGlobalModule L V
  exact {
    toFun := L.val.map (homOfLE hVW).op
    map_add' := (L.val.map (homOfLE hVW).op).hom.map_add
    map_smul' := by
      intro r s
      change L.val.map (homOfLE hVW).op (X.presheaf.map W.leTop.op r • s) =
        X.presheaf.map V.leTop.op r • L.val.map (homOfLE hVW).op s
      rw [L.val.map_smul (homOfLE hVW).op]
      congr 1
      change X.presheaf.map (homOfLE hVW).op (X.presheaf.map W.leTop.op r) =
        X.presheaf.map V.leTop.op r
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl }

/-- The native subset diagram of actual sheaf sections on actual finite intersections. -/
def actualSchemeModuleSubsetDiagram : Finset I ⥤ ModuleCat.{u} Γ(X, ⊤) := by
  letI : ∀ V : X.Opens, Module Γ(X, ⊤) (bundleSections L V) :=
    fun V => localSectionsGlobalModule L V
  exact {
    obj := fun S => ModuleCat.of Γ(X, ⊤) (bundleSections L (actualSchemeSubsetOpen U S))
    map := fun h => ModuleCat.ofHom
      (actualSchemeModuleRestriction L (actualSchemeSubsetOpen_antitone U (leOfHom h)))
    map_id := by
      intro S
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change L.presheaf.map (𝟙 _).op s = s
      rw [op_id, L.presheaf.map_id]
      rfl
    map_comp := by
      intro S T V hST hTV
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change L.presheaf.map _ s = L.presheaf.map _ (L.presheaf.map _ s)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl }

/-- Equality of actual opens transports actual sections by native restriction in both directions. -/
def actualSchemeModuleOpenIso {V W : X.Opens} (hVW : V = W) :
    letI := localSectionsGlobalModule L V
    letI := localSectionsGlobalModule L W
    ModuleCat.of Γ(X, ⊤) (bundleSections L V) ≅
      ModuleCat.of Γ(X, ⊤) (bundleSections L W) := by
  letI := localSectionsGlobalModule L V
  letI := localSectionsGlobalModule L W
  refine {
    hom := ModuleCat.ofHom (actualSchemeModuleRestriction L (le_of_eq hVW.symm))
    inv := ModuleCat.ofHom (actualSchemeModuleRestriction L (le_of_eq hVW))
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  all_goals
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change L.presheaf.map _ (L.presheaf.map _ s) = s
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    have hid : (homOfLE (le_of_eq hVW) ≫ homOfLE (le_of_eq hVW.symm)) = 𝟙 _ :=
      Subsingleton.elim _ _
    have hid' : (homOfLE (le_of_eq hVW.symm) ≫ homOfLE (le_of_eq hVW)) = 𝟙 _ :=
      Subsingleton.elim _ _
    simp [hid, hid']

/-- The actual singleton-intersection section module is the actual coordinate-open section module. -/
def actualSchemeModuleSingletonIso (i : I) :
    letI := localSectionsGlobalModule L (U i)
    (actualSchemeModuleSubsetDiagram L U).obj {i} ≅
      ModuleCat.of Γ(X, ⊤) (bundleSections L (U i)) :=
  actualSchemeModuleOpenIso L (Finset.inf_singleton (f := U))

/-- The actual two-coordinate intersection section module is the true overlap section module. -/
def actualSchemeModulePairIso (i j : I) :
    letI := localSectionsGlobalModule L (U i ⊓ U j)
    (actualSchemeModuleSubsetDiagram L U).obj {i, j} ≅
      ModuleCat.of Γ(X, ⊤) (bundleSections L (U i ⊓ U j)) :=
  actualSchemeModuleOpenIso L (by simp [actualSchemeSubsetOpen, Finset.inf_insert])

/-- Singleton sheaf diagram values identify with their true local-section family. -/
def actualSchemeModuleSingletonSectionsEquiv :
    letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
      fun i => localSectionsGlobalModule L (U i)
    (∀ i : I, (actualSchemeModuleSubsetDiagram L U).obj {i}) ≃ₗ[Γ(X, ⊤)]
      (∀ i, bundleSections L (U i)) := by
  letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
    fun i => localSectionsGlobalModule L (U i)
  exact LinearEquiv.piCongrRight (fun i => (actualSchemeModuleSingletonIso L U i).toLinearEquiv)

/-- Actual singleton and pair identifications commute with the true left overlap restriction. -/
theorem actualSchemeModuleSingleton_left_restrict (i j : I)
    (a : (actualSchemeModuleSubsetDiagram L U).obj {i}) :
    (actualSchemeModulePairIso L U i j).hom
      (subsetCechRestriction (actualSchemeModuleSubsetDiagram L U)
        (by simp : ({i} : Finset I) ⊆ {i, j}) a) =
    L.val.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
      ((actualSchemeModuleSingletonIso L U i).hom a) := by
  change L.presheaf.map _ (L.presheaf.map _ a) = L.presheaf.map _ (L.presheaf.map _ a)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Actual singleton and pair identifications commute with the true right overlap restriction. -/
theorem actualSchemeModuleSingleton_right_restrict (i j : I)
    (a : (actualSchemeModuleSubsetDiagram L U).obj {j}) :
    (actualSchemeModulePairIso L U i j).hom
      (subsetCechRestriction (actualSchemeModuleSubsetDiagram L U)
        (by simp : ({j} : Finset I) ⊆ {i, j}) a) =
    L.val.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
      ((actualSchemeModuleSingletonIso L U j).hom a) := by
  change L.presheaf.map _ (L.presheaf.map _ a) = L.presheaf.map _ (L.presheaf.map _ a)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- True singleton diagram compatibility is exactly the genuine sheaf overlap compatibility. -/
theorem actualSchemeModuleSingletonSections_memCompatible_iff
    (a : ∀ i : I, (actualSchemeModuleSubsetDiagram L U).obj {i}) :
    a ∈ actualSubsetSingletonCompatible (actualSchemeModuleSubsetDiagram L U) ↔
      actualSchemeModuleSingletonSectionsEquiv L U a ∈ bundleCechSections L U := by
  constructor
  · intro ha i j
    have hh := congrArg (actualSchemeModulePairIso L U i j).hom (ha i j)
    rw [actualSchemeModuleSingleton_left_restrict,
      actualSchemeModuleSingleton_right_restrict] at hh
    exact hh
  · intro ha i j
    apply (actualSchemeModulePairIso L U i j).toLinearEquiv.injective
    change (actualSchemeModulePairIso L U i j).hom _ = (actualSchemeModulePairIso L U i j).hom _
    rw [actualSchemeModuleSingleton_left_restrict, actualSchemeModuleSingleton_right_restrict]
    exact ha i j

/-- The actual compatible singleton diagram module is the actual native sheaf Čech equalizer. -/
def actualSchemeModuleCompatibleEquiv :
    actualSubsetSingletonCompatible (actualSchemeModuleSubsetDiagram L U) ≃ₗ[Γ(X, ⊤)]
      bundleCechSections L U := by
  let e := actualSchemeModuleSingletonSectionsEquiv L U
  exact {
    toFun := fun a => ⟨e a.val, (actualSchemeModuleSingletonSections_memCompatible_iff L U a.val).mp a.property⟩
    invFun := fun b => ⟨e.symm b.val,
      (actualSchemeModuleSingletonSections_memCompatible_iff L U (e.symm b.val)).mpr
        (by simpa only [e, LinearEquiv.apply_symm_apply] using b.property)⟩
    left_inv := by intro a; apply Subtype.ext; exact e.symm_apply_apply a.val
    right_inv := by intro b; apply Subtype.ext; exact e.apply_symm_apply b.val
    map_add' := by intro a b; apply Subtype.ext; exact e.map_add a.val b.val
    map_smul' := by intro r a; apply Subtype.ext; exact e.map_smul r a.val }

/-- The true sheaf gluing axiom identifies actual global sections with the native zero-cocycle kernel. -/
def actualSchemeModuleGlobalZeroCocyclesEquiv (hU : iSup U = ⊤) :
    bundleSections L ⊤ ≃ₗ[Γ(X, ⊤)]
      LinearMap.ker (subsetCechCardDifferential (actualSchemeModuleSubsetDiagram L U) 1) :=
  (bundleGlobalCechEquiv L U hU).trans
    ((actualSchemeModuleCompatibleEquiv L U).symm.trans
      (actualSubsetCechZeroCocyclesCompatibleEquiv (actualSchemeModuleSubsetDiagram L U)).symm)

variable {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤))

/-- The true structural base action on actual global sheaf sections. -/
def actualSchemeModuleBaseGlobalSections : ModuleCat.{u} K :=
  (ModuleCat.restrictScalars c).obj (ModuleCat.of Γ(X, ⊤) (bundleSections L ⊤))

/-- The actual restriction diagram retains its true structural base-field action. -/
def actualSchemeModuleBaseSubsetDiagram : Finset I ⥤ ModuleCat.{u} K :=
  actualSchemeModuleSubsetDiagram L U ⋙ ModuleCat.restrictScalars c

/-- True sheaf gluing identifies actual base-linear global sections with the actual cocycle kernel. -/
def actualSchemeModuleBaseGlobalZeroCocyclesIso (hU : iSup U = ⊤) :
    actualSchemeModuleBaseGlobalSections L c ≅
      ModuleCat.of K (LinearMap.ker
        (subsetCechCardDifferential (actualSchemeModuleBaseSubsetDiagram L U c) 1)) :=
  (ModuleCat.restrictScalars c).mapIso
      (actualSchemeModuleGlobalZeroCocyclesEquiv L U hU).toModuleIso ≪≫
    (actualSubsetCechRestrictScalarsZeroCocyclesEquiv
      (actualSchemeModuleSubsetDiagram L U) c).toModuleIso

/-- The actual sheaf global-section module is native degree-zero cohomology of its actual cover diagram. -/
def actualSchemeModuleBaseGlobalHomologyIso (hU : iSup U = ⊤) :
    actualSchemeModuleBaseGlobalSections L c ≅
      (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L U c)).homology 0 :=
  actualSchemeModuleBaseGlobalZeroCocyclesIso L U c hU ≪≫
    actualSubsetCechZeroCocyclesIso (actualSchemeModuleBaseSubsetDiagram L U c)

end SchemeRestrictionDiagram

end

end Hironaka.Geometry.ProperSteinProjectiveCech
