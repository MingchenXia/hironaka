import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The literal finite native free sheaf at the original module stalk

Native coproduct inclusions/projections and the native original stalk action
construct the actual finite free-stalk equivalence, with exact original germs.
No new module action, module category, free sheaf or supplied dictionary.
Blueprint: `hironaka-g10-native-finite-free-stalk.tex`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

namespace Hironaka.HironakaChowNativeFiniteFreeStalk

open HironakaSingularModuleSheafStalk

universe u
variable {X : TopCat.{u}} {R₀ : X.Presheaf CommRingCat.{u}}
  {M₀ N₀ : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)}

/-- The original native stalk maps preserve zero. -/
theorem stalkLinearMap_zero (x : X) :
    stalkLinearMap (0 : M₀ ⟶ N₀) x = 0 := by
  ext m
  obtain ⟨V,hx,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq M₀.presheaf m
  erw [stalkLinearMap_germ]
  exact (TopCat.Presheaf.germ N₀.presheaf V x hx).hom.map_zero

private theorem stalkLinearMap_add (f g : M₀ ⟶ N₀) (x : X) :
    stalkLinearMap (f+g) x = stalkLinearMap f x + stalkLinearMap g x := by
  ext m
  obtain ⟨V,hx,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq M₀.presheaf m
  change stalkLinearMap (f+g) x _ = stalkLinearMap f x _ + stalkLinearMap g x _
  erw [stalkLinearMap_germ, stalkLinearMap_germ, stalkLinearMap_germ]
  exact (TopCat.Presheaf.germ N₀.presheaf V x hx).hom.map_add _ _

/-- The original native stalk maps preserve finite sums. -/
theorem stalkLinearMap_sum {J : Type*} (s : Finset J) (f : J → (M₀ ⟶ N₀)) (x : X) :
    stalkLinearMap (∑ i ∈ s, f i) x = ∑ i ∈ s, stalkLinearMap (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, stalkLinearMap_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, stalkLinearMap_add, ih]

variable (R : X.Sheaf CommRingCat.{u}) (I : Type u) [Fintype I] [DecidableEq I]

private abbrev U := SheafOfModules.unit (forgetRing R)
private abbrev F := SheafOfModules.free (R := forgetRing R) I
private abbrev p (i : I) : F R I ⟶ U R := Sigma.π (fun _ : I => U R) i
private abbrev j (i : I) : U R ⟶ F R I := SheafOfModules.ιFree i

private theorem jp (i k : I) : j R I i ≫ p R I k = if i=k then 𝟙 (U R) else 0 := by
  by_cases h : i=k
  · subst k
    rw [if_pos rfl]
    exact Sigma.ι_π_eq_id (fun _ : I => U R) i
  · exact (Sigma.ι_π_of_ne (fun _ : I => U R) h).trans (if_neg h).symm

private theorem total : ∑ i : I, p R I i ≫ j R I i = 𝟙 (F R I) := by
  apply Sigma.hom_ext
  intro k
  change j R I k ≫ (∑ i : I, p R I i ≫ j R I i) = j R I k
  simp only [Preadditive.comp_sum, ← Category.assoc, jp, ite_comp, Category.id_comp, zero_comp]
  simp

private def toCoordinates (x : X) :
    ↑(TopCat.Presheaf.stalk (F R I).val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      (I → ↑(TopCat.Presheaf.stalk R.obj x)) :=
  LinearMap.pi fun i => (unitStalkLinearEquiv R x).toLinearMap.comp
    (stalkLinearMap (p R I i).val x)

private def fromCoordinates (x : X) :
    (I → ↑(TopCat.Presheaf.stalk R.obj x)) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk (F R I).val.presheaf x) :=
  ∑ i : I, (stalkLinearMap (j R I i).val x).comp
    ((unitStalkLinearEquiv R x).symm.toLinearMap.comp (LinearMap.proj i))

private theorem projection_inclusion (x : X) (i k : I)
    (a : ↑(TopCat.Presheaf.stalk (U R).val.presheaf x)) :
    stalkLinearMap (p R I k).val x (stalkLinearMap (j R I i).val x a) =
      if i=k then a else 0 := by
  change ((stalkLinearMap (p R I k).val x).comp
    (stalkLinearMap (j R I i).val x)) a = _
  rw [← stalkLinearMap_comp]
  change stalkLinearMap ((j R I i ≫ p R I k).val) x a = _
  rw [jp]
  split_ifs with h
  · exact LinearMap.congr_fun (stalkLinearMap_id _ x) a
  · exact LinearMap.congr_fun (stalkLinearMap_zero x) a

/-- The actual native finite free-sheaf stalk equivalence, on the literal
original neighbourhood-colimit stalk and the SAME native scalar action. -/
def finiteFreeStalkLinearEquiv (x : X) :
    ↑(TopCat.Presheaf.stalk (SheafOfModules.free (R := forgetRing R) I).val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk R.obj x)] (I → ↑(TopCat.Presheaf.stalk R.obj x)) :=
  LinearEquiv.ofLinearMap (toCoordinates R I x) (fromCoordinates R I x)
    (by
      apply LinearMap.ext
      intro v
      funext k
      simp only [toCoordinates, fromCoordinates, LinearMap.comp_apply, LinearMap.pi_apply,
        LinearMap.sum_apply, LinearMap.proj_apply, LinearEquiv.coe_coe, map_sum]
      simp_rw [projection_inclusion R I x, apply_ite]
      simp)
    (by
      apply LinearMap.ext
      intro m
      have h := congrArg (fun f : F R I ⟶ F R I => stalkLinearMap f.val x)
        (total R I)
      have hv : (∑ i : I, (p R I i ≫ j R I i)).val =
          ∑ i : I, (p R I i ≫ j R I i).val :=
        (SheafOfModules.forget (forgetRing R)).map_sum _ _
      change stalkLinearMap (∑ i : I, (p R I i ≫ j R I i)).val x =
        stalkLinearMap (𝟙 (F R I).val) x at h
      rw [hv, stalkLinearMap_sum, stalkLinearMap_id] at h
      have hh := LinearMap.congr_fun h m
      simpa [toCoordinates, fromCoordinates, stalkLinearMap_comp] using hh)

/-- Each ORIGINAL native coproduct inclusion retains its literal coordinate. -/
theorem finiteFreeStalkLinearEquiv_ι (x : X) (i : I)
    (a : ↑(TopCat.Presheaf.stalk R.obj x)) :
    finiteFreeStalkLinearEquiv R I x
      (stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
        ((unitStalkLinearEquiv R x).symm a)) = Pi.single i a := by
  funext k
  rw [Pi.single_apply]
  change (unitStalkLinearEquiv R x)
    (stalkLinearMap (p R I k).val x (stalkLinearMap (j R I i).val x
      ((unitStalkLinearEquiv R x).symm a))) = if k=i then a else 0
  rw [projection_inclusion]
  by_cases h : i=k
  · subst k
    simp
  · simp [h, Ne.symm h]

/-- The germ of the SAME original tautological native free section has its
original standard coordinate, not a chosen replacement basis. -/
theorem finiteFreeStalkLinearEquiv_freeSection_germ (x : X) (V : Opens X) (hx : x ∈ V) (i : I) :
    finiteFreeStalkLinearEquiv R I x
      (TopCat.Presheaf.germ (F R I).val.presheaf V x hx
        ((SheafOfModules.freeSection (R := forgetRing R) i).val (op V))) = Pi.single i 1 := by
  have h := finiteFreeStalkLinearEquiv_ι R I x i (1 : ↑(TopCat.Presheaf.stalk R.obj x))
  have hone : unitStalkLinearEquiv R x
      (TopCat.Presheaf.germ (U R).val.presheaf V x hx (1 : R.obj.obj (op V))) = 1 := by
    rw [unitStalkLinearEquiv_germ]
    exact map_one _
  have hinv := (unitStalkLinearEquiv R x).symm_apply_eq.mpr hone.symm
  rw [hinv, stalkLinearMap_germ] at h
  exact h

end Hironaka.HironakaChowNativeFiniteFreeStalk
