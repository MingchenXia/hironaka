import Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality
import Hironaka.Analytic.Unibranch.SourceMorphismExt

/-!
# Gluing morphisms of reduced complex spaces from local pieces

Morphisms of reduced complex spaces are determined by their point maps, also on open pieces
which are not themselves known to be paracompact (`lrs_hom_eq_of_base_eq`).  Hence a point map
which is, near every point, the point map of a morphism defined on an open piece is the point map
of a global morphism (`exists_hom_of_local`): the local morphisms agree on overlaps and glue
(`HironakaIntrinsicMorphismGluing.exists_unique_over`).  This is used to assemble the morphism
of Hironaka's Chow lemma from local Riemann extensions and from its restrictions to finitely
many open and closed pieces (`exists_hom_of_cover`).

Blueprint: `hironaka-g10-gen-chow-general.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GenGluing

open Hironaka HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace

noncomputable section

/-- **Morphisms from an open piece are determined by their point maps.**  Two morphisms over the
complex point from a locally ringed space with an open immersion into a reduced complex space `A`
to a reduced complex space `B`, with the same point map, are equal. -/
theorem lrs_hom_eq_of_base_eq {A B : SourceReducedComplexSpace} {T : LocallyRingedSpace.{0}}
    (k : T ⟶ A.obj.left) [LocallyRingedSpace.IsOpenImmersion k]
    (F G : T ⟶ B.obj.left) (hF : F ≫ B.obj.hom = k ≫ A.obj.hom)
    (hG : G ≫ B.obj.hom = k ≫ A.obj.hom) (hbase : F.base = G.base) : F = G := by
  classical
  have hT := HironakaG11BlowupLocality.charts_of_openImmersion (k ≫ A.obj.hom) A.obj.hom
    A.property.2.2 k rfl
  choose d U C hC i hi hip hx using hT
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (i x) := hi
  have hcover : ∀ t : T, ∃ (x : T) (c : C x), (i x).base c = t := by
    intro t
    obtain ⟨c, hc⟩ := hx t
    exact ⟨t, c, hc⟩
  apply HironakaIntrinsicMorphismGluing.hom_ext (fun x => (modelOver (U x) (C x)).left) i hcover
  intro x
  let M := sourceReducedComplexSpaceModel (U x) (C x) (hC x)
  have hFp : (i x ≫ F) ≫ B.obj.hom = M.obj.hom := by
    rw [Category.assoc, hF]
    exact hip x
  have hGp : (i x ≫ G) ≫ B.obj.hom = M.obj.hom := by
    rw [Category.assoc, hG]
    exact hip x
  let F' : M ⟶ B := ObjectProperty.homMk (Over.homMk (i x ≫ F) hFp)
  let G' : M ⟶ B := ObjectProperty.homMk (Over.homMk (i x ≫ G) hGp)
  have h := morphism_eq_of_base_eq F' G' (by
    change (i x ≫ F).base = (i x ≫ G).base
    simp only [LocallyRingedSpace.comp_base, hbase])
  exact congrArg (fun H : M ⟶ B => H.hom.left) h

/-- **Gluing from local pieces.**  A point map `φ : A → B` of reduced complex spaces which near
every point is the point map of a morphism over the complex point defined on an open piece of `A`
is the point map of a morphism `A ⟶ B`. -/
theorem exists_hom_of_local {A B : SourceReducedComplexSpace} (φ : A.obj.left → B.obj.left)
    (h : ∀ a : A.obj.left, ∃ (T : LocallyRingedSpace.{0}) (k : T ⟶ A.obj.left)
      (F : T ⟶ B.obj.left), LocallyRingedSpace.IsOpenImmersion k ∧ a ∈ range k.base ∧
      F ≫ B.obj.hom = k ≫ A.obj.hom ∧ ∀ t, F.base t = φ (k.base t)) :
    ∃ G : A ⟶ B, ∀ a, G.hom.left.base a = φ a := by
  classical
  choose T k F hk hx hF hFφ using h
  let : ∀ a, LocallyRingedSpace.IsOpenImmersion (k a) := hk
  have hcover : ∀ t : A.obj.left, ∃ (a : A.obj.left) (u : T a), (k a).base u = t := by
    intro t
    obtain ⟨u, hu⟩ := hx t
    exact ⟨t, u, hu⟩
  have hcompat : ∀ a b, pullback.fst (k a) (k b) ≫ F a = pullback.snd (k a) (k b) ≫ F b := by
    intro a b
    apply lrs_hom_eq_of_base_eq (A := A) (B := B) (pullback.fst (k a) (k b) ≫ k a)
    · rw [Category.assoc, hF a, Category.assoc]
    · rw [Category.assoc, hF b, ← Category.assoc, ← pullback.condition, Category.assoc]
    · ext p
      have hc := congrArg (fun H => H.base p) (pullback.condition (f := k a) (g := k b))
      simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hc ⊢
      rw [hFφ a, hFφ b, hc]
  obtain ⟨G, hG, -⟩ := HironakaIntrinsicMorphismGluing.exists_unique_over T k hcover A.obj.hom
    B.obj.hom F hcompat hF
  refine ⟨ObjectProperty.homMk G, ?_⟩
  intro t
  obtain ⟨a, u, rfl⟩ := hcover t
  have h1 := congrArg (fun H => H.base u) (hG a)
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at h1
  change G.left.base ((k a).base u) = φ ((k a).base u)
  rw [h1, hFφ a]

/-- Gluing from local pieces which are reduced complex spaces. -/
theorem exists_hom_of_local' {A B : SourceReducedComplexSpace} (φ : A.obj.left → B.obj.left)
    (h : ∀ a : A.obj.left, ∃ (U : SourceReducedComplexSpace) (k : U ⟶ A) (F : U ⟶ B),
      LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ a ∈ range k.hom.left.base ∧
      ∀ u, F.hom.left.base u = φ (k.hom.left.base u)) :
    ∃ G : A ⟶ B, ∀ a, G.hom.left.base a = φ a := by
  apply exists_hom_of_local φ
  intro a
  obtain ⟨U, k, F, hk, ha, hF⟩ := h a
  refine ⟨U.obj.left, k.hom.left, F.hom.left, hk, ha, ?_, hF⟩
  rw [Over.w F.hom, Over.w k.hom]

/-- **Gluing over a cover by open pieces.**  Morphisms `g i : A' i ⟶ B` on open pieces
`L i : A' i ⟶ A` covering `A`, which agree at points with the same image, glue to a morphism
`G : A ⟶ B` with `L i ≫ G = g i`. -/
theorem exists_hom_of_cover {ι : Type*} {A B : SourceReducedComplexSpace}
    {A' : ι → SourceReducedComplexSpace} (L : ∀ i, A' i ⟶ A)
    (hL : ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left)
    (hcov : ∀ a, ∃ i, a ∈ range (L i).hom.left.base) (g : ∀ i, A' i ⟶ B)
    (hg : ∀ i k (u : (A' i).obj.left) (v : (A' k).obj.left),
      (L i).hom.left.base u = (L k).hom.left.base v →
        (g i).hom.left.base u = (g k).hom.left.base v) :
    ∃ G : A ⟶ B, ∀ i, L i ≫ G = g i := by
  classical
  choose ia ua hua using fun a => hcov a
  let φ : A.obj.left → B.obj.left := fun a => (g (ia a)).hom.left.base (ua a)
  have hφ : ∀ i u, (g i).hom.left.base u = φ ((L i).hom.left.base u) := by
    intro i u
    exact hg i (ia _) u (ua _) (hua _).symm
  obtain ⟨G, hG⟩ := exists_hom_of_local' φ (fun a =>
    ⟨A' (ia a), L (ia a), g (ia a), hL _, ⟨ua a, hua a⟩, hφ _⟩)
  refine ⟨G, fun i => morphism_eq_of_pointwise_eq _ _ (fun u => ?_)⟩
  change G.hom.left.base ((L i).hom.left.base u) = _
  rw [hG, ← hφ]

end

end Hironaka.Analytic.Unibranch.HironakaG10GenGluing
