import Hironaka.Analytic.Unibranch.HironakaG10ChowTowerDomination
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatBimeromorphicIso

/-!
# Hironaka's Chow lemma for manifolds from the flattening theorem

The third step of the assembly of goal G10a (blueprint
`hironaka-g10-chowside-flattening-reduction.tex`).  Hironaka's flattening theorem is stated
for ARBITRARY proper morphisms `f : Y ⟶ X` of reduced complex spaces with compact `X`, in
the native category: there are a finite tower of native blowups `σ : X' ⟶ X` of finite-type
ideals with dense unit loci, a closed set `E ⊆ X'` with empty interior off which `σ` is an
open immersion, and a strict transform `(Y', p, q)` of `Y` relative to `E`, described by
properties of the actual strict transform (a closed subspace of `Y ×_X X'`, proper over
`X'`, containing the fibre product over `X' \ E` as a dense open subspace mapped
isomorphically into `Y`), with `p` flat.

For a proper modification `f` of a compact complex manifold, the strict transform is then
proper bimeromorphic and flat, hence an isomorphism (from the two classical named inputs
`FlatMorphismsAreOpen` and `FiniteMappingTheorem`), so the tower dominates `f` natively and
`HironakaG10ChowTowerDomination` gives stable domination by blowup sequences.

Main declarations:

* `IsOpenImmersionOn`, `IsStrictTransform` — the strict-transform datum.
* `HironakaFlattening` — the named classical input (Hironaka 1975), not proved here.
* `isIso_of_isStrictTransform_of_flat` — a flat strict transform of a proper modification
  is an isomorphism.
* `hasStableBlowupDomination_of_flattening`, `hironakaChowLemmaManifold_of_flattening` —
  goal G10a from flattening and the two classical inputs.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaG10ChowStrictSquare HironakaChowLemma
  AnalyticModificationLocalDiscrepancy SourceReducedComplexSpace OriginalNativeModification
  HironakaG10ChowNativeIsoCriterion HironakaG10ChowFlatBimeromorphicIso
  HironakaG10ChowTowerDomination

noncomputable section

/-! ### The strict-transform datum -/

/-- `q` restricts to an open immersion on `S`: some open immersion `j` onto `S` composes with
`q` to an open immersion. -/
def IsOpenImmersionOn {Y X : SourceReducedComplexSpace} (q : Y ⟶ X) (S : Set Y.obj.left) :
    Prop :=
  ∃ (V : LocallyRingedSpace) (j : V ⟶ Y.obj.left), LocallyRingedSpace.IsOpenImmersion j ∧
    range j.base = S ∧ LocallyRingedSpace.IsOpenImmersion (j ≫ q.hom.left)

/-- **Strict transform.**  `(Y', p, q)` is a strict transform of `f : Y ⟶ X` under
`σ : X' ⟶ X` relative to `E ⊆ X'`: the square commutes, `p` is proper, `Y'` maps
injectively into the fibre product `Y ×_X X'` and contains its part over `X' \ E`, which
is dense in `Y'` and mapped by `q` by an open immersion.  These are properties of the actual
strict transform, the closure in `Y ×_X X'` of the fibre product over `X' \ E`, when `σ` is
an isomorphism off `E`. -/
structure IsStrictTransform {X X' Y Y' : SourceReducedComplexSpace} (f : Y ⟶ X) (σ : X' ⟶ X)
    (E : Set X'.obj.left) (p : Y' ⟶ X') (q : Y' ⟶ Y) : Prop where
  comm : q ≫ f = p ≫ σ
  proper : IsProperMap p.hom.left.base
  pair_injective : ∀ a b : Y'.obj.left, p.hom.left.base a = p.hom.left.base b →
    q.hom.left.base a = q.hom.left.base b → a = b
  covers : ∀ (y : Y.obj.left) (x' : X'.obj.left), x' ∉ E →
    f.hom.left.base y = σ.hom.left.base x' →
      ∃ y' : Y'.obj.left, p.hom.left.base y' = x' ∧ q.hom.left.base y' = y
  dense : Dense (p.hom.left.base ⁻¹' Eᶜ)
  openImmersionOn : IsOpenImmersionOn q (p.hom.left.base ⁻¹' Eᶜ)

/-- **Named classical input: Hironaka's flattening theorem** for a compact base
(H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975),
503–547; blueprint `chow:flattening`).  For every proper morphism `f : Y ⟶ X` of reduced
complex spaces with `X` compact there are a finite tower of blowups `σ : X' ⟶ X` along
coherent ideals with nowhere dense zero loci, a closed nowhere dense `E ⊆ X'` off which `σ`
is an open immersion (the preimage of the union of the images of the centres), and a strict
transform of `Y` relative to `E` which is flat over `X'`.  Not an axiom; not proved here. -/
def HironakaFlattening : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (f : Y ⟶ X), CompactSpace X.obj.left →
    IsProperMap f.hom.left.base →
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ X) (E : Set X'.obj.left),
      IsNativeBlowupTower X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ Y),
        IsStrictTransform f σ E p q ∧ IsFlatMorphism p

/-! ### A flat strict transform of a modification is an isomorphism -/

section Iso

variable {X Y : SourceReducedComplexSpace}

/-- An open immersion on `S` maps open subsets of `S` to open sets. -/
theorem isOpen_image_of_isOpenImmersionOn {q : Y ⟶ X} {S : Set Y.obj.left}
    (h : IsOpenImmersionOn q S) (U : Set Y.obj.left) (hU : IsOpen U) (hUS : U ⊆ S) :
    IsOpen (q.hom.left.base '' U) := by
  obtain ⟨V, j, hj, hr, hjq⟩ := h
  have hU' : U = j.base '' (j.base ⁻¹' U) := by
    rw [image_preimage_eq_of_subset (hr ▸ hUS)]
  have himg : q.hom.left.base '' U = (j ≫ q.hom.left).base '' (j.base ⁻¹' U) := by
    conv_lhs => rw [hU']
    rw [image_image]
    rfl
  rw [himg]
  exact hjq.base_open.isOpenMap _ (hU.preimage j.base.hom.continuous)

/-- The stalk maps of an open immersion on `S` at points of `S` are isomorphisms. -/
theorem isIso_stalkMap_of_isOpenImmersionOn {q : Y ⟶ X} {S : Set Y.obj.left}
    (h : IsOpenImmersionOn q S) (y : Y.obj.left) (hy : y ∈ S) :
    IsIso (q.hom.left.stalkMap y) := by
  obtain ⟨V, j, hj, hr, hjq⟩ := h
  have hy' : y ∈ range j.base := by
    rw [hr]
    exact hy
  obtain ⟨v, rfl⟩ := hy'
  have hcomp : IsIso ((j ≫ q.hom.left).stalkMap v) := inferInstance
  rw [LocallyRingedSpace.stalkMap_comp] at hcomp
  have hjs : IsIso (j.stalkMap v) := inferInstance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (q.hom.left.stalkMap (j.base v)) (j.stalkMap v)
    hjs hcomp

/-- **A flat strict transform of a proper modification is an isomorphism.**  Let
`f : Y ⟶ X` be an isomorphism over the complement of a set `T` with empty interior, `σ`
an open immersion off a closed set `E` with empty interior, and `(Y', p, q)` a strict
transform of `f` under `σ` relative to `E` with `p` flat.  Then `p` is an isomorphism,
given the two classical inputs. -/
theorem isIso_of_isStrictTransform_of_flat (H₁ : FlatMorphismsAreOpen)
    (H₂ : FiniteMappingTheorem) {X' Y' : SourceReducedComplexSpace} {f : Y ⟶ X}
    {σ : X' ⟶ X} {E : Set X'.obj.left} {p : Y' ⟶ X'} {q : Y' ⟶ Y}
    (hst : IsStrictTransform f σ E p q) (hEc : IsClosed E) (hEi : interior E = ∅)
    (hσ : IsOpenImmersionOn σ Eᶜ) {T : Set X.obj.left} (hTi : interior T = ∅)
    (hf : IsIsoOver f Tᶜ) (hflat : IsFlatMorphism p) : IsIso p := by
  have hσopen : ∀ U : Set X'.obj.left, IsOpen U → U ⊆ Eᶜ → IsOpen (σ.hom.left.base '' U) :=
    isOpen_image_of_isOpenImmersionOn hσ
  have hsq : ∀ y' : Y'.obj.left,
      f.hom.left.base (q.hom.left.base y') = σ.hom.left.base (p.hom.left.base y') := fun y' =>
    congrArg (fun H : Y' ⟶ X => H.hom.left.base y') hst.comm
  have hsqL : q.hom.left ≫ f.hom.left = p.hom.left ≫ σ.hom.left :=
    congrArg (fun H : Y' ⟶ X => H.hom.left) hst.comm
  refine isIso_of_flat_of_dense_stalk_iso H₁ H₂ hst.proper hflat
    (V := Eᶜ ∩ σ.hom.left.base ⁻¹' Tᶜ)
    (dense_compl_inter_preimage_compl hEc hEi hσopen hTi) ?_ ?_ ?_
  · exact (injOn_of_square hsq hst.pair_injective (injOn_of_isIsoOver hf)).mono
      (fun y' hy' => hy'.2)
  · exact subset_range_of_square (subset_range_of_isIsoOver hf) hst.covers
  · intro y' hy'
    exact isIso_stalkMap_of_square hsqL y'
      (isIso_stalkMap_of_isOpenImmersionOn hst.openImmersionOn y' hy'.1)
      (isIso_stalkMap_of_isIsoOver hf _ (by rw [hsq y']; exact hy'.2))
      (isIso_stalkMap_of_isOpenImmersionOn hσ _ hy'.1)

end Iso

/-! ### Goal G10a from flattening -/

section ChowLemma

variable {n : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Flattening dominates modifications natively.**  From flattening and the two classical
inputs, every proper modification `f` of a compact complex manifold is dominated by a tower of
native ideal blowups of the whole model of `X`. -/
theorem exists_nativeBlowupTower_of_flattening (H₀ : HironakaFlattening)
    (H₁ : FlatMorphismsAreOpen) (H₂ : FiniteMappingTheorem) [CompactSpace X] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) :
    ∃ (Z : SourceReducedComplexSpace) (p : Z ⟶ wholeModel (n := n) X)
      (β : Z ⟶ wholeModel (n := n) Y),
      IsNativeBlowupTower (wholeModel (n := n) X) Z p ∧ β ≫ nativeMorphism hf.1 = p := by
  obtain ⟨hFproper, T, -, hTi, -, hFiso⟩ := nativeMorphism_isProperBimeromorphic hf
  have hcpt : CompactSpace (wholeModel (n := n) X).obj.left :=
    (Homeomorph.Set.univ X).symm.compactSpace
  obtain ⟨X', σ, E, hσ, hEc, hEi, hσE, Y', p, q, hst, hflat⟩ :=
    H₀ _ _ (nativeMorphism hf.1) hcpt hFproper
  have hp : IsIso p := isIso_of_isStrictTransform_of_flat H₁ H₂ hst hEc hEi hσE hTi hFiso hflat
  refine ⟨X', σ, inv p ≫ q, hσ, ?_⟩
  rw [Category.assoc, hst.comm, IsIso.inv_hom_id_assoc]

/-- **Stable domination from flattening.** -/
theorem hasStableBlowupDomination_of_flattening (H₀ : HironakaFlattening)
    (H₁ : FlatMorphismsAreOpen) (H₂ : FiniteMappingTheorem) [CompactSpace X] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) : HasStableBlowupDomination n f := by
  obtain ⟨Z, p, β, hp, hβ⟩ := exists_nativeBlowupTower_of_flattening H₀ H₁ H₂ hf
  exact hasStableBlowupDomination_of_isNativeBlowupTower hf.1 hp β hβ

end ChowLemma

/-- **Goal G10a from flattening.**  Hironaka's flattening theorem for compact bases and the two
classical inputs (flat morphisms are open; the finite mapping theorem) imply Hironaka's Chow
lemma for compact complex manifolds.  Neither `HironakaDominatingIdealManifold` nor a
composite-blowup theorem is used. -/
theorem hironakaChowLemmaManifold_of_flattening (H₀ : HironakaFlattening)
    (H₁ : FlatMorphismsAreOpen) (H₂ : FiniteMappingTheorem) : HironakaChowLemmaManifold.{0} := by
  intro n X _ _ _ _ Y _ _ _ f hf
  exact (hasStableBlowupDomination_of_flattening H₀ H₁ H₂ hf).hasBlowupDomination

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
