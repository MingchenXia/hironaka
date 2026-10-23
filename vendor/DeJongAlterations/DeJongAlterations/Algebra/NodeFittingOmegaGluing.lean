import DeJongAlterations.Algebra.NodeFittingOmegaStalk
import DeJongAlterations.Algebra.NodeFittingIdealSheafGluing

/-! # The original intrinsic differential Fitting ideal sheaf over an arbitrary base

All original affine source--base charts and their entire ideals are retained.
This constructs intrinsic Fitting data; geometric nonsmooth-locus identification
and the unramifiedness of its structural morphism remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Algebra.NodeFittingOmegaGluing

open NodeFittingOmegaCharts NodeFittingIdealSheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- The actual cover by ALL original affine source--base charts. -/
def chartCover : X.OpenCover.{u} where
  I₀ := Chart f
  X C := C.source.1.toScheme
  f C := C.source.1.ι
  mem₀ := (Scheme.Cover.mkOfCovers (Chart f) (fun C => C.source.1.toScheme)
    (fun C => C.source.1.ι) (fun x => by
      obtain ⟨C, hx⟩ := NodeFittingOmegaStalk.exists_chart_mem f x
      exact ⟨C, ⟨x, hx⟩, rfl⟩)).mem₀

/-- The actual whole chart Fitting ideal sheaf on the original affine source open. -/
def localIdeal (i : ℕ) (C : Chart f) : C.source.1.toScheme.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop ((C.ideal f i).map C.source.1.topIso.inv.hom)

/-- The actual open-section and open-stalk isomorphisms retain the ORIGINAL whole germ map. -/
theorem topIso_germ_stalkIso (U : X.Opens) (y : U) :
    U.topIso.inv ≫ U.toScheme.presheaf.germ ⊤ y (Set.mem_univ y) ≫
      (U.stalkIso y).hom = X.presheaf.germ U y.1 y.2 := by
  rw [Scheme.Opens.germ_stalkIso_hom, Scheme.Opens.topIso_inv,
    TopCat.Presheaf.germ_res]

/-- The entire original local chart ideal at the SAME original local ring and coefficient map. -/
theorem localIdeal_stalk_original (i : ℕ) (C : Chart f) (y : C.source.1) :
    (stalkIdeal (localIdeal f i C) y).map (C.source.1.stalkIso y).hom.hom =
      NodeFittingOmegaStalk.ideal f i y.1 := by
  rw [stalkIdeal_eq_map_germ (localIdeal f i C)
    ⟨⊤, isAffineOpen_top C.source.1.toScheme⟩ (Set.mem_univ y)]
  have ht : (localIdeal f i C).ideal ⟨⊤, isAffineOpen_top C.source.1.toScheme⟩ =
      (C.ideal f i).map C.source.1.topIso.inv.hom := by
    simp [localIdeal, Scheme.IdealSheafData.ofIdealTop_ideal]
    change Ideal.map (RingHom.id _) _ = _
    rw [Ideal.map_id]
  rw [ht]
  rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    topIso_germ_stalkIso]
  exact NodeFittingOmegaStalk.chart_ideal_stalk f C i y.2

/-- The inverse actual open-stalk map expresses the local chart ideal by the same intrinsic original ideal. -/
theorem localIdeal_stalk (i : ℕ) (C : Chart f) (y : C.source.1) :
    stalkIdeal (localIdeal f i C) y =
      (NodeFittingOmegaStalk.ideal f i (C.source.1.ι y)).map
        (C.source.1.ι.stalkMap y).hom := by
  have h := localIdeal_stalk_original f i C y
  apply_fun Ideal.map (C.source.1.stalkIso y).inv.hom at h
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id] at h
  simpa only [Scheme.Opens.stalkIso_inv, Scheme.Opens.ι_apply] using h

/-- The entire original local ideal extended along the actual original map to this point. -/
def pointPullbackIdeal {Z : Scheme.{u}} (i : ℕ) (g : Z ⟶ X) (z : Z) :
    Ideal (Z.presheaf.stalk z) :=
  (NodeFittingOmegaStalk.ideal f i (g z)).map (g.stalkMap z).hom

/-- Whole stalk pullback follows the actual composite map into the SAME original X. -/
theorem localIdeal_pullback_stalk {Z : Scheme.{u}} (i : ℕ) (C : Chart f)
    (g : Z ⟶ C.source.1.toScheme) (z : Z) :
    stalkIdeal ((localIdeal f i C).comap g) z =
      pointPullbackIdeal f i (g ≫ C.source.1.ι) z := by
  rw [stalkIdeal_comap, localIdeal_stalk, Ideal.map_map]
  simp only [pointPullbackIdeal, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  rfl

/-- Full original chart ideals have equal ENTIRE native pullbacks on every ACTUAL overlap. -/
theorem localIdeal_compatible (i : ℕ) :
    GlueCompat (chartCover f) (localIdeal f i) := by
  intro C D
  apply ext_stalkIdeal
  intro z
  rw [localIdeal_pullback_stalk, localIdeal_pullback_stalk]
  exact congrArg (fun g => pointPullbackIdeal f i g z)
    (pullback.condition (f := C.source.1.ι) (g := D.source.1.ι))

/-- Actual native intrinsic differential Fitting ideal SHEAF, over the SAME arbitrary original base. -/
def idealSheaf (i : ℕ) : X.IdealSheafData :=
  glue (𝒰 := chartCover f) (localIdeal f i) (localIdeal_compatible f i)

/-- The native glued datum restricts to the ENTIRE original local chart ideal. -/
theorem idealSheaf_comap (i : ℕ) (C : Chart f) :
    (idealSheaf f i).comap C.source.1.ι = localIdeal f i C :=
  glue_comap (𝒰 := chartCover f) (localIdeal f i) (localIdeal_compatible f i) C

/-- The whole glued stalk ideal equals the intrinsic Fitting ideal of the ORIGINAL relative local differential module. -/
theorem idealSheaf_stalk (i : ℕ) (x : X) :
    stalkIdeal (idealSheaf f i) x = NodeFittingOmegaStalk.ideal f i x := by
  obtain ⟨C, hx⟩ := NodeFittingOmegaStalk.exists_chart_mem f x
  let y : C.source.1 := ⟨x, hx⟩
  have h := congrArg (fun J => stalkIdeal J y) (idealSheaf_comap f i C)
  rw [stalkIdeal_comap] at h
  apply_fun Ideal.map (C.source.1.stalkIso y).hom.hom at h
  rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Scheme.Opens.stalkIso_inv,
    Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id] at h
  exact h.trans (localIdeal_stalk_original f i C y)

/-- EVERY original affine source--base chart computes the exact ENTIRE glued intrinsic ideal. -/
theorem idealSheaf_chart_ideal (i : ℕ) (C : Chart f) :
    (idealSheaf f i).ideal C.source = C.ideal f i := by
  rw [C.source.2.ideal_ext_iff]
  intro x hx
  rw [← stalkIdeal_eq_map_germ (idealSheaf f i) C.source hx]
  exact (idealSheaf_stalk f i x).trans (NodeFittingOmegaStalk.chart_ideal_stalk f C i hx).symm

/-- The actual native Fitting closed subscheme's structural morphism to the ORIGINAL base. -/
def fittingMorphism (i : ℕ) : (idealSheaf f i).subscheme ⟶ Y :=
  (idealSheaf f i).subschemeι ≫ f

end DeJongAlterations.Algebra.NodeFittingOmegaGluing
