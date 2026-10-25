/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechCover

/-!
# Čech complexes of pushforwards

For a morphism `π : X ⟶ Y`, a module `G` on `X` and a family `V` of opens of `Y`, the sections of
`π_* G` over `V_T` are the sections of `G` over `π⁻¹(V_T)`, so the Čech complex of `π_* G` for `V`
is isomorphic to the Čech complex of `G` for the family `π⁻¹ V`
(`cechComplexPushforwardIso`). For an affine morphism `π` between quasi-compact schemes with affine
diagonal and quasi-coherent `G`, this gives `H^p(Y, π_* G) ≅ H^p(X, G)`
(`cohomologyPushforwardIso`). This is the dévissage tool for finite morphisms used by the later
cohomology lanes (finite maps of curves to `ℙ¹`, normalizations). Blueprint:
`sm-cohomology-cech.tex`, `lem:sm-cech-pushforward`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section SubsetCechFunctor

variable {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι]
  {D D' D'' : Finset ι ⥤ ModuleCat.{u} R}

lemma subsetCechComplexMap_id : subsetCechComplexMap (𝟙 D) = 𝟙 _ := by
  ext p x
  apply Subtype.ext
  funext T
  rfl

lemma subsetCechComplexMap_comp (α : D ⟶ D') (β : D' ⟶ D'') :
    subsetCechComplexMap (α ≫ β) = subsetCechComplexMap α ≫ subsetCechComplexMap β := by
  ext p x
  apply Subtype.ext
  funext T
  rfl

/-- An isomorphism of subset diagrams induces an isomorphism of Čech complexes. -/
def subsetCechComplexIso (e : D ≅ D') : subsetCechComplex D ≅ subsetCechComplex D' where
  hom := subsetCechComplexMap e.hom
  inv := subsetCechComplexMap e.inv
  hom_inv_id := by rw [← subsetCechComplexMap_comp, e.hom_inv_id, subsetCechComplexMap_id]
  inv_hom_id := by rw [← subsetCechComplexMap_comp, e.inv_hom_id, subsetCechComplexMap_id]

end SubsetCechFunctor

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (G : X.Modules) {R : Type u} [CommRing R]
  (c : R →+* Γ(Y, ⊤)) {ι : Type u} [LinearOrder ι] (V : ι → Y.Opens)

lemma preimage_finsetInf (T : Finset ι) : π ⁻¹ᵁ (T.inf V) = T.inf (fun i => π ⁻¹ᵁ V i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T _ ih => rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

/-- The comparison `Γ(π_* G, V_T) ≅ Γ(G, (π⁻¹V)_T)`, restriction along an equality of opens. -/
def cechPushforwardEquiv (T : Finset ι) :
    (cechDiagram ((Scheme.Modules.pushforward π).obj G) V c).obj T ≃ₗ[R]
      (cechDiagram G (fun i => π ⁻¹ᵁ V i) (π.appTop.hom.comp c)).obj T where
  toFun s := G.presheaf.map (homOfLE (preimage_finsetInf π V T).ge).op
    (show Γ(G, π ⁻¹ᵁ (T.inf V)) from s)
  invFun t := (G.presheaf.map (homOfLE (preimage_finsetInf π V T).le).op
    (show Γ(G, T.inf (fun i => π ⁻¹ᵁ V i)) from t) : Γ(G, π ⁻¹ᵁ (T.inf V)))
  left_inv s := presheaf_map_map_self G _ _ _
  right_inv t := presheaf_map_map_self G _ _ _
  map_add' s t := map_add _ _ _
  map_smul' r s := by
    change G.presheaf.map (homOfLE (preimage_finsetInf π V T).ge).op
        (π.app (T.inf V) (Y.presheaf.map (homOfLE le_top).op (c r)) •
          (show Γ(G, π ⁻¹ᵁ (T.inf V)) from s)) =
      X.presheaf.map (homOfLE (le_top : T.inf (fun i => π ⁻¹ᵁ V i) ≤ ⊤)).op (π.app ⊤ (c r)) •
        G.presheaf.map (homOfLE (preimage_finsetInf π V T).ge).op
          (show Γ(G, π ⁻¹ᵁ (T.inf V)) from s)
    rw [Scheme.Modules.map_smul]
    congr 1
    have h := ConcreteCategory.congr_hom (π.naturality (homOfLE (le_top : T.inf V ≤ ⊤)).op) (c r)
    change π.app (T.inf V) (Y.presheaf.map (homOfLE le_top).op (c r)) =
      X.presheaf.map _ (π.app ⊤ (c r)) at h
    rw [h]
    exact ring_presheaf_map_map (V₁ := π ⁻¹ᵁ ⊤) _ _
      ((le_top : T.inf (fun i => π ⁻¹ᵁ V i) ≤ ⊤).trans (π.preimage_top).ge) _

/-- The Čech diagram of `π_* G` for `V` is the Čech diagram of `G` for `π⁻¹ V`. -/
def cechDiagramPushforwardIso :
    cechDiagram ((Scheme.Modules.pushforward π).obj G) V c ≅
      cechDiagram G (fun i => π ⁻¹ᵁ V i) (π.appTop.hom.comp c) :=
  NatIso.ofComponents (fun T => (cechPushforwardEquiv π G c V T).toModuleIso) (by
    intro S T h
    ext s
    exact (presheaf_map_map G _ _ ((Finset.inf_mono (leOfHom h)).trans
      (preimage_finsetInf π V S).ge) _).trans (presheaf_map_map G _ _ _ _).symm)

/-- **Čech complexes of pushforwards** (blueprint `lem:sm-cech-pushforward`). -/
def cechComplexPushforwardIso :
    cechComplex ((Scheme.Modules.pushforward π).obj G) V c ≅
      cechComplex G (fun i => π ⁻¹ᵁ V i) (π.appTop.hom.comp c) :=
  subsetCechComplexIso (cechDiagramPushforwardIso π G c V)

/-- `Ȟ^p(V, π_* G) ≅ Ȟ^p(π⁻¹V, G)`. -/
def cechCohomologyPushforwardIso (p : ℕ) :
    cechCohomology ((Scheme.Modules.pushforward π).obj G) V c p ≅
      cechCohomology G (fun i => π ⁻¹ᵁ V i) (π.appTop.hom.comp c) p :=
  (HomologicalComplex.homologyFunctor _ _ p).mapIso (cechComplexPushforwardIso π G c V)

variable {π} in
/-- The preimage of a finite affine cover under an affine morphism. -/
def FiniteAffineCover.comap [IsAffineHom π] (𝒰 : FiniteAffineCover Y) : FiniteAffineCover X where
  ι := 𝒰.ι
  U i := π ⁻¹ᵁ 𝒰.U i
  iSup_eq_top := by rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_eq_top, Scheme.Hom.preimage_top]
  isAffineOpen_inf T hT := by
    rw [← preimage_finsetInf]
    exact (𝒰.isAffineOpen_inf T hT).preimage π

/-- **Cohomology of a pushforward along an affine morphism**: `H^p(Y, π_* G) ≅ H^p(X, G)` for
quasi-coherent `G`. -/
def cohomologyPushforwardIso [IsAffineHom π] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))] [G.IsQuasicoherent]
    (p : ℕ) :
    cohomology ((Scheme.Modules.pushforward π).obj G) c p ≅
      cohomology G (π.appTop.hom.comp c) p :=
  cechCohomologyPushforwardIso π G c (FiniteAffineCover.choose Y).U p ≪≫
    (cohomologyIsoCech G (π.appTop.hom.comp c) ((FiniteAffineCover.choose Y).comap) p).symm

end

end DeJongAlterations.StableModification.Cohomology
