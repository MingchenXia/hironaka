/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.Functor

/-!
Closed native proof adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FormalFunctionsDirectSum.lean`,
SHA256 5cc12d2db008bd2b40d45e8a9a9c8ecfecdecbd89417de78d62b20c97a45f54e.
Only the original four native Mathlib imports are retained. Genuine original
Rees-degree complexes and their whole comparison remain separate producers.

 # Genuine homology comparison for direct sums of module complexes -/

open CategoryTheory Limits
open scoped DirectSum
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.DirectSumHomology

variable {R : Type u} [Ring R]
variable (S : ℕ → ShortComplex (ModuleCat.{u} R))

/-- The actual family viewed as a short complex in the category of diagrams. -/
def diagram : ShortComplex (Discrete ℕ ⥤ ModuleCat.{u} R) where
  X₁ := Discrete.functor (fun d => (S d).X₁)
  X₂ := Discrete.functor (fun d => (S d).X₂)
  X₃ := Discrete.functor (fun d => (S d).X₃)
  f := Discrete.natTrans (fun d => (S d.as).f)
  g := Discrete.natTrans (fun d => (S d.as).g)
  zero := by
    apply NatTrans.ext
    funext d
    exact (S d.as).zero

/-- Homology of the original diagram is its coordinatewise original homology. -/
def diagramHomologyIso :
    (diagram S).homology ≅ Discrete.functor (fun d => (S d).homology) :=
  Discrete.natIso (fun d =>
    ((diagram S).mapHomologyIso ((evaluation (Discrete ℕ) (ModuleCat.{u} R)).obj d)).symm)

/-- The actual categorical direct sum of the original three-term complexes. -/
def categoricalSum : ShortComplex (ModuleCat.{u} R) :=
  (diagram S).map (colim (J := Discrete ℕ) (C := ModuleCat.{u} R))

/-- Exactness of direct sums of modules identifies the genuine original
homology with the direct sum of the original homologies. -/
def categoricalSumHomologyIso :
    (categoricalSum S).homology ≅ ModuleCat.of R (⨁ d : ℕ, (S d).homology) :=
  (diagram S).mapHomologyIso (colim (J := Discrete ℕ) (C := ModuleCat.{u} R)) ≪≫
    (colim (J := Discrete ℕ) (C := ModuleCat.{u} R)).mapIso (diagramHomologyIso S) ≪≫
    ModuleCat.coprodIsoDirectSum (fun d => (S d).homology)

/-- The literal direct-sum complex, with coordinatewise original differentials. -/
def directSum : ShortComplex (ModuleCat.{u} R) where
  X₁ := ModuleCat.of R (⨁ d : ℕ, (S d).X₁)
  X₂ := ModuleCat.of R (⨁ d : ℕ, (S d).X₂)
  X₃ := ModuleCat.of R (⨁ d : ℕ, (S d).X₃)
  f := ModuleCat.ofHom (DirectSum.lmap fun d => (S d).f.hom)
  g := ModuleCat.ofHom (DirectSum.lmap fun d => (S d).g.hom)
  zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro d
    exact congrArg (fun h => h.hom (x d)) (S d).zero

private theorem coprodIso_naturality (A B : ℕ → ModuleCat.{u} R)
    (φ : ∀ d, A d ⟶ B d) :
    (colim (J := Discrete ℕ) (C := ModuleCat.{u} R)).map (Discrete.natTrans fun d => φ d.as) ≫
        (ModuleCat.coprodIsoDirectSum B).hom =
      (ModuleCat.coprodIsoDirectSum A).hom ≫
        ModuleCat.ofHom (DirectSum.lmap fun d => (φ d).hom) := by
  apply colimit.hom_ext
  intro d
  rw [← Category.assoc, colimit.ι_map]
  change φ d.as ≫ Sigma.ι B d.as ≫ (ModuleCat.coprodIsoDirectSum B).hom =
    Sigma.ι A d.as ≫ (ModuleCat.coprodIsoDirectSum A).hom ≫ _
  rw [ModuleCat.ι_coprodIsoDirectSum_hom, ← Category.assoc,
    ModuleCat.ι_coprodIsoDirectSum_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, DirectSum.lmap_lof]

/-- The categorical direct sum is the literal original coordinatewise direct sum. -/
def categoricalSumIso : categoricalSum S ≅ directSum S :=
  ShortComplex.isoMk
    (ModuleCat.coprodIsoDirectSum fun d => (S d).X₁)
    (ModuleCat.coprodIsoDirectSum fun d => (S d).X₂)
    (ModuleCat.coprodIsoDirectSum fun d => (S d).X₃)
    (coprodIso_naturality _ _ (fun d => (S d).f)).symm
    (coprodIso_naturality _ _ (fun d => (S d).g)).symm

/-- Genuine homology of the literal direct sum is the direct sum of the
original homologies, with no finiteness assumption on the individual modules. -/
def homologyIso :
    (directSum S).homology ≅ ModuleCat.of R (⨁ d : ℕ, (S d).homology) :=
  (ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso (categoricalSumIso S).symm ≪≫
    categoricalSumHomologyIso S

end Hironaka.Geometry.ProperSteinProjectiveCech.DirectSumHomology
