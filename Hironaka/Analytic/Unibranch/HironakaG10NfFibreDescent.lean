import Hironaka.Analytic.Unibranch.HironakaG10NfChartStalk
import Hironaka.Analytic.Unibranch.HironakaG10NfJointLocal
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
import Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare

/-!
# H3.4 (fibre conjunct, generic): from the ambient fibre identity to the native fibre ideals

Lane G10H3, run 0081.  G10FI's fibre identity (`HironakaG10NfFibreIdentityCanonical.FibreIdentityAt`) is stated on
ambient stalks: `proj^♯ h ∈ joint + f^♯ 𝔪 ⟹ h ∈ I(Γ) + Π^♯ 𝔪`.  The `strict` field needs it on native stalks:
`β r ∈ ψ(𝔪)·B ⟹ r ∈ F^♯(𝔪)·𝒪_X`.  Two generic steps:

* `map_targetStalkToJoint_comp_le_ambient` — `ψ(𝔪) ⊆ mk(f^♯ 𝔪)` for `ψ = targetStalkToJoint ∘ φ`, `φ` local;
* **`mem_map_of_graph_descent`** — descent along graph charts: if `χ_X^♯ r` is the class of an ambient germ in
  `I(W) + Π^♯ 𝔪`, where `χ_X : W → X`, `χ_Y : W_T → Y` are open immersions with `χ_X ≫ F = N ≫ χ_Y`
  (`N` induced by `Π`), then `r ∈ F^♯(𝔪)`.

No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreDescent

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaRealOpenGeometricStrictSaturation
  HironakaG10RealOpenStrictTorsionKernel HironakaG10JointStrictTorsion HironakaG10JointNativeScalar

section Target

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
  (hV : IsComplexAnalyticSubset (n := n) V)

/-- **`targetStalkToJoint ∘ φ` sends the maximal ideal into the image of the ambient maximal ideal.** -/
theorem map_targetStalkToJoint_comp_le_ambient {A : Type*} [CommRing A] [IsLocalRing A]
    (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V)
    (φ : A →+* TargetStalk (n := n) d t j b U f V y hyV) [IsLocalHom φ] :
    Ideal.map ((targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV).comp φ) (IsLocalRing.maximalIdeal A) ≤
      Ideal.map (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y))
        (Ideal.map ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom
          (IsLocalRing.maximalIdeal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) Y).presheaf.stalk (f y)))) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  have hz : ¬ IsUnit (φ x) := fun hu => (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_map_unit φ x hu)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y, hyV⟩ (φ x))
  have hna : ¬ IsUnit a := fun hu => hz (by
    have h1 := hu.map (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)))
    rw [ha] at h1
    have h2 := h1.map (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y, hyV⟩).symm
    rwa [RingEquiv.symm_apply_apply] at h2)
  have hz' : (targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV).comp φ x =
      Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)
        (((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom a) := by
    change targetQuotientToJoint (n := n) d t j b U W f V hf hV y
      (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y, hyV⟩ (φ x)) = _
    rw [← ha]
    rfl
  rw [hz']
  have hmem : a ∈ IsLocalRing.maximalIdeal
      ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) Y).presheaf.stalk (f y)) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hna
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hmem)

end Target

section Descent

variable {k k' : ℕ} {M MT : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
  [TopologicalSpace MT] [ChartedSpace (ComplexModel k') MT] [IsComplexManifold k' MT]
  {Pm : M → MT} (hPm : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k') ∞ Pm)
  {W : Set M} {WT : Set MT} (hmaps : ∀ x ∈ W, Pm x ∈ WT)
  {Xc Yc : LocallyRingedSpace.{0}}
  (chartX : actualSubspaceLocallyRingedSpace (n := k) W ⟶ Xc)
  (chartY : actualSubspaceLocallyRingedSpace (n := k') WT ⟶ Yc)
  [LocallyRingedSpace.IsOpenImmersion chartX] [LocallyRingedSpace.IsOpenImmersion chartY]
  (Fm : Xc ⟶ Yc) (hsq : actualSubspaceMap hPm hmaps ≫ chartY = chartX ≫ Fm)

include hsq in
/-- **Descent of the fibre ideal along graph charts.** -/
theorem mem_map_of_graph_descent (γ : W) (r : Xc.presheaf.stalk (chartX.base γ))
    (h : actualComplexStructureStalk (n := k) γ.val)
    (hr : (chartX.stalkMap γ).hom r = (actualSubspaceInclusion (n := k) W).stalkMap γ h)
    (hh : h ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := k) W) γ.val ⊔
      Ideal.map ((ChartedSpace.locallyRingedSpaceMap Pm hPm).stalkMap γ.val).hom
        (IsLocalRing.maximalIdeal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel k') MT).presheaf.stalk (Pm γ.val)))) :
    r ∈ Ideal.map (Fm.stalkMap (chartX.base γ)).hom (IsLocalRing.maximalIdeal _) := by
  set N := actualSubspaceMap hPm hmaps
  -- the stalk square of `N` with the inclusions
  have hNsq : ∀ a, (N.stalkMap γ).hom ((actualSubspaceInclusion (n := k') WT).stalkMap (N.base γ) a) =
      (actualSubspaceInclusion (n := k) W).stalkMap γ
        (((ChartedSpace.locallyRingedSpaceMap Pm hPm).stalkMap γ.val).hom a) := fun a => by
    have e := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hPm hmaps γ) a
    simp only [ConcreteCategory.comp_apply] at e
    exact e
  -- the square on stalks
  have hb : (chartX ≫ Fm).base γ = (N ≫ chartY).base γ := congrArg (fun k => k.base γ) hsq.symm
  have hcomp : ∀ s : Yc.presheaf.stalk (chartY.base (N.base γ)),
      (N.stalkMap γ).hom ((chartY.stalkMap (N.base γ)).hom s) =
        (chartX.stalkMap γ).hom ((Fm.stalkMap (chartX.base γ)).hom
          ((eqToHom (congrArg Yc.presheaf.stalk hb.symm)).hom s)) := fun s => by
    have c1 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp N chartY γ) s
    have c2 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp chartX Fm γ)
      ((eqToHom (congrArg Yc.presheaf.stalk hb.symm)).hom s)
    have e := Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease.stalkMap_eq_of_eq _ _ hsq γ hb s
    exact c1.symm.trans (e.trans c2)
  -- the maximal ideal of the graph stalk is the image of that of `Yc`
  have hchY : Function.Surjective (chartY.stalkMap (N.base γ)).hom :=
    (Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv chartY (N.base γ)).surjective
  have hmY := IsLocalRing.map_maximalIdeal_of_surjective _ hchY
  have hbijX : Function.Bijective (chartX.stalkMap γ).hom :=
    (Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv chartX γ).bijective
  have heq : Function.Surjective (eqToHom (congrArg Yc.presheaf.stalk hb.symm)).hom := fun s =>
    ⟨(Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport.stalkEquivOfEq hb).symm s,
      (Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport.stalkEquivOfEq hb).apply_symm_apply s⟩
  have hmE := IsLocalRing.map_maximalIdeal_of_surjective _ heq
  -- the target of `r`
  set K := Ideal.map (Fm.stalkMap (chartX.base γ)).hom (IsLocalRing.maximalIdeal _)
  have key : (chartX.stalkMap γ).hom r ∈ Ideal.map (chartX.stalkMap γ).hom K := by
    rw [hr]
    obtain ⟨i, hi, p, hp, rfl⟩ := Submodule.mem_sup.mp hh
    rw [map_add]
    have hi0 : (actualSubspaceInclusion (n := k) W).stalkMap γ i = 0 := by
      have := actualSubspaceInclusion_stalk_kernel (n := k) W γ
      rw [← this] at hi
      exact hi
    rw [hi0, zero_add]
    have hp' : (actualSubspaceInclusion (n := k) W).stalkMap γ p ∈
        Ideal.map (N.stalkMap γ).hom (IsLocalRing.maximalIdeal _) := by
      have h1 : Ideal.map ((actualSubspaceInclusion (n := k) W).stalkMap γ).hom
          (Ideal.map ((ChartedSpace.locallyRingedSpaceMap Pm hPm).stalkMap γ.val).hom
            (IsLocalRing.maximalIdeal _)) ≤ Ideal.map (N.stalkMap γ).hom (IsLocalRing.maximalIdeal _) := by
        rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap]
        change (actualSubspaceInclusion (n := k) W).stalkMap γ
          (((ChartedSpace.locallyRingedSpaceMap Pm hPm).stalkMap γ.val).hom a) ∈ _
        rw [← hNsq a]
        refine Ideal.mem_map_of_mem _ ?_
        exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu => (IsLocalRing.mem_maximalIdeal _).mp ha
          ((AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap (actualSubspaceInclusion (n := k') WT)
            (N.base γ)).map_nonunit a hu)
      exact h1 (Ideal.mem_map_of_mem _ hp)
    have h2 : Ideal.map (N.stalkMap γ).hom (IsLocalRing.maximalIdeal _) ≤
        Ideal.map (chartX.stalkMap γ).hom K := by
      rw [← hmY, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro s hs
      rw [Ideal.mem_comap]
      change (N.stalkMap γ).hom ((chartY.stalkMap (N.base γ)).hom s) ∈ _
      rw [hcomp s]
      refine Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ?_)
      exact hmE ▸ Ideal.mem_map_of_mem (eqToHom (congrArg Yc.presheaf.stalk hb.symm)).hom hs
    exact h2 hp'
  have := Ideal.mem_comap.mpr key
  rwa [Ideal.comap_map_of_bijective _ hbijX] at this

end Descent

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreDescent
