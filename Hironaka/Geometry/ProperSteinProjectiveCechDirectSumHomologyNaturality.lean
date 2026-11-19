/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechDirectSumHomology

/-! # Original summand inclusions in the actual direct-sum homology comparison

Closed native argument adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FormalFunctionsDirectSumNaturality.lean`,
SHA256 baa127feea2156f120ea354d4da6244c6267f08acb76b19e8edd42bfa076648d.
Only native Mathlib through the owned direct-sum helper is imported.
-/

open CategoryTheory Limits
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.DirectSumHomologyNaturality

variable {R : Type u} [Ring R]
variable (S : ℕ → ShortComplex (ModuleCat.{u} R))

/-- The actual canonical original-diagram coordinate inclusion into its colimit. -/
def inclusionTransformation (d : ℕ) :
    (evaluation (Discrete ℕ) (ModuleCat.{u} R)).obj ⟨d⟩ ⟶
      colim (J := Discrete ℕ) (C := ModuleCat.{u} R) where
  app F := colimit.ι F ⟨d⟩
  naturality _F _G φ := (colimit.ι_map φ ⟨d⟩).symm

/-- The original short complex maps into its actual categorical direct sum. -/
def categoricalInclusion (d : ℕ) : S d ⟶ DirectSumHomology.categoricalSum S :=
  (DirectSumHomology.diagram S).mapNatTrans (inclusionTransformation d)

/-- The original summand inclusion into the literal coordinatewise direct sum. -/
def inclusion (d : ℕ) : S d ⟶ DirectSumHomology.directSum S :=
  categoricalInclusion S d ≫ (DirectSumHomology.categoricalSumIso S).hom

/-- The literal left component of the original summand inclusion. -/
theorem inclusion_left (d : ℕ) :
    (inclusion S d).τ₁ =
      ModuleCat.ofHom (DirectSum.lof R ℕ (fun e => (S e).X₁) d) :=
  ModuleCat.ι_coprodIsoDirectSum_hom (fun e => (S e).X₁) d

/-- The literal middle component of the original summand inclusion. -/
theorem inclusion_middle (d : ℕ) :
    (inclusion S d).τ₂ =
      ModuleCat.ofHom (DirectSum.lof R ℕ (fun e => (S e).X₂) d) :=
  ModuleCat.ι_coprodIsoDirectSum_hom (fun e => (S e).X₂) d

/-- The literal right component of the original summand inclusion. -/
theorem inclusion_right (d : ℕ) :
    (inclusion S d).τ₃ =
      ModuleCat.ofHom (DirectSum.lof R ℕ (fun e => (S e).X₃) d) :=
  ModuleCat.ι_coprodIsoDirectSum_hom (fun e => (S e).X₃) d

private theorem from_inverse_square {C : Type*} [Category C]
    {A B D E : C} (e : A ≅ B) (h : A ⟶ D) (q : D ⟶ E) (t : B ⟶ E)
    (ht : t = e.inv ≫ h ≫ q) : h ≫ q = e.hom ≫ t := by
  rw [ht, Iso.hom_inv_id_assoc]

private theorem inclusion_comparison {C : Type*} [Category C]
    {A B D E F G : C} (e : A ≅ B) (h : A ⟶ D) (q : D ⟶ E)
    (t : B ⟶ E) (w : E ⟶ F) (z : A ⟶ F) (v : F ⟶ G)
    (hq : h ≫ q = e.hom ≫ t) (ht : t ≫ w = e.inv ≫ z) :
    h ≫ q ≫ w ≫ v = z ≫ v := by
  have h1 : (h ≫ q) ≫ w = z := by
    rw [hq, Category.assoc, ht, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg (fun b => b ≫ v) h1

private theorem inclusion_iso_cancel {C : Type*} [Category C]
    {A B D E : C} (h : A ⟶ B) (e : B ≅ D) (q : B ⟶ E) :
    (h ≫ e.hom) ≫ e.inv ≫ q = h ≫ q := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The exact categorical homology comparison retains every original summand. -/
theorem categoricalInclusion_homology (d : ℕ) :
    ShortComplex.homologyMap (categoricalInclusion S d) ≫
      (DirectSumHomology.categoricalSumHomologyIso S).hom =
        ModuleCat.ofHom (DirectSum.lof R ℕ (fun e => (S e).homology) d) := by
  let T := DirectSumHomology.diagram S
  let E := (evaluation (Discrete ℕ) (ModuleCat.{u} R)).obj ⟨d⟩
  let L := colim (J := Discrete ℕ) (C := ModuleCat.{u} R)
  let τ := inclusionTransformation (R := R) d
  have h : ShortComplex.homologyMap (categoricalInclusion S d) ≫
      (T.mapHomologyIso L).hom = (T.mapHomologyIso E).hom ≫ τ.app T.homology :=
    from_inverse_square (T.mapHomologyIso E) _ _ _ (τ.app_homology T)
  have ht : τ.app T.homology ≫ L.map (DirectSumHomology.diagramHomologyIso S).hom =
      (T.mapHomologyIso E).inv ≫ Sigma.ι (fun e => (S e).homology) d :=
    (τ.naturality (DirectSumHomology.diagramHomologyIso S).hom).symm
  exact (inclusion_comparison (T.mapHomologyIso E) _ _ _ _ _ _ h ht).trans
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun e => (S e).homology) d)

/-- The genuine homology isomorphism of the literal direct sum sends every
original summand's actual homology inclusion to its literal direct-sum inclusion. -/
theorem inclusion_homology (d : ℕ) :
    ShortComplex.homologyMap (inclusion S d) ≫
      (DirectSumHomology.homologyIso S).hom =
        ModuleCat.ofHom (DirectSum.lof R ℕ (fun e => (S e).homology) d) := by
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let e := H.mapIso (DirectSumHomology.categoricalSumIso S)
  have h := H.map_comp (categoricalInclusion S d)
    (DirectSumHomology.categoricalSumIso S).hom
  change H.map (categoricalInclusion S d ≫ (DirectSumHomology.categoricalSumIso S).hom) ≫
    e.inv ≫ (DirectSumHomology.categoricalSumHomologyIso S).hom = _
  exact (congrArg (fun b => b ≫ e.inv ≫
    (DirectSumHomology.categoricalSumHomologyIso S).hom) h).trans
      ((inclusion_iso_cancel _ e _).trans (categoricalInclusion_homology S d))

end Hironaka.Geometry.ProperSteinProjectiveCech.DirectSumHomologyNaturality
