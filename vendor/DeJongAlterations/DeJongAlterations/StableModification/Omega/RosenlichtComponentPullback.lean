/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.BaseChange
import DeJongAlterations.StableModification.Omega.Invertible
import DeJongAlterations.StableModification.Cohomology.PullbackQcoh
import DeJongAlterations.StableModification.Cohomology.BaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Pulling back an invertible module, and lifting along injective morphisms

Sheaf-level tools for computing the pullback `ν^* ω` of the relative dualizing sheaf of a nodal
curve to a curve `ν : Z̃ ⟶ X` over a geometric point (blueprint `sm-omega-base-change-fibre.tex`,
`lem:sm-omega-bcf-invertible-local`, `lem:sm-omega-bcf-pullback-generator`, `lem:sm-omega-bcf-lift`).

* `isQuasicoherent_of_isInvertibleModule`: an invertible module (locally isomorphic to `𝒪` on
  affine charts, `Omega.IsInvertibleModule`) is quasi-coherent.
* `exists_generator`: an invertible module has, near every point and inside every open
  neighbourhood, an affine open `W` and a section `σ ∈ Γ(W, M)` with `Γ(W, 𝒪) ≅ Γ(W, M)`,
  `c ↦ c σ`.
* `bijective_smul_pullbackSectionLE`: if `σ` freely generates `Γ(W, M)` (`W` affine, `M`
  quasi-coherent), then for every affine `V ⊆ ν⁻¹ W` the pullback `ν^* σ|_V` freely generates
  `Γ(V, ν^* M)` (base change of sections, `Cohomology.isBaseChange_pullbackSectionLinear`).
* `exists_lift`: a morphism `ι : F ⟶ N` lifts along a morphism `Θ : G ⟶ N` which is injective on
  sections over every open, provided the sections of `F` land locally in the image of `Θ` (gluing in
  the sheaf `G`).

These are the general inputs of the comparison `Ω¹_{Z̃/K} ⊆ ν^* ω_{X/S}` in the proof of
`cor:sm-omega-restriction-component` (`sm-omega-base-change.tex`), M. Temkin, *Stable modification
of relative curves*, J. Algebraic Geom. 19 (2010), §1.2, properties (a), (b) (`semi-stable.tex`,
T:1700–1704).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open DeJongAlterations.StableModification.Cohomology

universe u

namespace DeJongAlterations.StableModification.Omega.RosenlichtComponent

section Invertible

variable {Y : Scheme.{u}} (M : Y.Modules)

set_option backward.isDefEq.respectTransparency false in
/-- The structure sheaf of an affine scheme has a presentation (it is `tilde` of the ring). -/
def presentationUnitSpec (R : CommRingCat.{u}) :
    (SheafOfModules.unit (Spec R).ringCatSheaf).Presentation :=
  presentationTilde.{u} (M := ModuleCat.of R R) Set.univ (by simp) _ (Submodule.span_eq _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A module isomorphic to `𝒪` on the spectrum of an affine open `W` has a presentation on `W`. -/
def presentationRestrictOfIso {W : Y.Opens} (hW : IsAffineOpen W)
    (e : M.restrict hW.fromSpec ≅ SheafOfModules.unit _) : (M.restrict W.ι).Presentation :=
  let P₁ : (M.restrict hW.fromSpec).Presentation :=
    (presentationUnitSpec Γ(Y, W)).ofIsIso e.inv
  let P₂ : ((M.restrict hW.fromSpec).restrict hW.isoSpec.hom).Presentation :=
    (presentationPullback hW.isoSpec.hom P₁).ofIsIso
      ((Scheme.Modules.restrictFunctorIsoPullback hW.isoSpec.hom).inv.app _)
  let e₂ : (M.restrict hW.fromSpec).restrict hW.isoSpec.hom ≅ M.restrict W.ι :=
    ((Scheme.Modules.restrictFunctorComp hW.isoSpec.hom hW.fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hW.isoSpec_hom_fromSpec).app M
  P₂.ofIsIso e₂.hom

/-- **Invertible modules are quasi-coherent.** -/
theorem isQuasicoherent_of_isInvertibleModule (h : IsInvertibleModule M) : M.IsQuasicoherent := by
  choose W hW hyW e using h
  refine isQuasicoherent_of_presentation_restrict M W ?_ fun y =>
    presentationRestrictOfIso M (hW y) (e y).some
  refine eq_top_iff.mpr fun y _ => Opens.mem_iSup.mpr ⟨y, hyW y⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Local generators of an invertible module**: near every point `y`, inside any open
neighbourhood `O` of `y`, there is an affine open `W ∋ y` and `σ ∈ Γ(W, M)` such that
`c ↦ c σ` is a bijection `Γ(W, 𝒪) → Γ(W, M)`. -/
theorem exists_generator {y : Y} (h : IsInvertibleAt M y) {O : Y.Opens} (hyO : y ∈ O) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ O ∧
      ∃ σ : Γ(M, W), Function.Bijective (fun c : Γ(Y, W) => c • σ) := by
  obtain ⟨W₀, hW₀, hy, ⟨e⟩⟩ := h
  obtain ⟨g, hgO, hyg⟩ := hW₀.exists_basicOpen_le (V := W₀ ⊓ O) ⟨y, ⟨hy, hyO⟩⟩ hy
  let U : (Spec Γ(Y, W₀)).Opens := PrimeSpectrum.basicOpen g
  let σ₀ : Γ(M, hW₀.fromSpec ''ᵁ U) := e.inv.app U (1 : Γ(Spec Γ(Y, W₀), U))
  have hbij₀ : Function.Bijective (fun c : Γ(Y, hW₀.fromSpec ''ᵁ U) => c • σ₀) := by
    have hcomp : (fun c : Γ(Y, hW₀.fromSpec ''ᵁ U) => c • σ₀) =
        (e.inv.app U) ∘ (hW₀.fromSpec.appIso U).hom := by
      funext c
      change c • σ₀ = e.inv.app U ((hW₀.fromSpec.appIso U).hom c)
      have h1 : ((hW₀.fromSpec.appIso U).hom c : Γ(Spec Γ(Y, W₀), U)) =
          ((hW₀.fromSpec.appIso U).hom c) • (1 : Γ(Spec Γ(Y, W₀), U)) :=
        (mul_one _).symm
      rw [h1, Scheme.Modules.Hom.app_smul]
      change c • σ₀ = (hW₀.fromSpec.appIso U).inv ((hW₀.fromSpec.appIso U).hom c) • σ₀
      rw [Iso.hom_inv_id_apply]
    rw [hcomp]
    exact (bijective_app_of_iso _ e.symm U).comp
      (ConcreteCategory.bijective_of_isIso (hW₀.fromSpec.appIso U).hom)
  have hU : hW₀.fromSpec ''ᵁ U = Y.basicOpen g := hW₀.fromSpec_image_basicOpen g
  have key : ∀ V : Y.Opens, V = Y.basicOpen g → ∃ σ : Γ(M, V),
      Function.Bijective (fun c : Γ(Y, V) => c • σ) := by
    rintro V rfl
    rw [← hU]
    exact ⟨σ₀, hbij₀⟩
  obtain ⟨σ, hσ⟩ := key _ rfl
  exact ⟨Y.basicOpen g, hW₀.basicOpen g, hyg, hgO.trans inf_le_right, σ, hσ⟩

end Invertible

section BasicOpen

variable {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency false in
/-- **Generators restrict to generators on basic opens**: if `β` freely generates the sections of
a quasi-coherent module over an affine open `V`, its restriction freely generates the sections over
every basic open `D(g) ⊆ V` (localization of sections, `Cohomology.isLocalizedModule_restrictLinearNative`). -/
theorem bijective_smul_restrict_basicOpen {V : Y.Opens} (hV : IsAffineOpen V) (β : Γ(F, V))
    (hβ : Function.Bijective (fun c : Γ(Y, V) => c • β)) (g : Γ(Y, V)) :
    Function.Bijective (fun c : Γ(Y, Y.basicOpen g) =>
      c • F.presheaf.map (homOfLE (Y.basicOpen_le g)).op β) := by
  let ρ := (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom
  let _ : Algebra Γ(Y, V) Γ(Y, Y.basicOpen g) := ρ.toAlgebra
  have hloc : IsLocalization.Away g Γ(Y, Y.basicOpen g) := hV.isLocalization_basicOpen g
  let _ : Module Γ(Y, V) Γ(F, Y.basicOpen g) := Module.compHom _ ρ
  have hM := isLocalizedModule_restrictLinearNative F hV g
  set res := restrictLinearNative F (Y.basicOpen_le g)
  have hres : ∀ m : Γ(F, V), res m = F.presheaf.map (homOfLE (Y.basicOpen_le g)).op m :=
    fun m => rfl
  have hsmul : ∀ (a : Γ(Y, V)) (n : Γ(F, Y.basicOpen g)), a • n = ρ a • n := fun _ _ => rfl
  constructor
  · intro c c' hcc'
    rw [← sub_eq_zero]
    have h0 : (c - c') • F.presheaf.map (homOfLE (Y.basicOpen_le g)).op β = 0 := by
      rw [sub_smul]; exact sub_eq_zero.mpr hcc'
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) (c - c')
    simp only at ha
    -- `(c - c') * g^n = a`
    have h1 : res (a • β) = 0 := by
      rw [map_smul, hres, hsmul]
      change (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen g) a) • _ = 0
      rw [← ha, mul_comm, mul_smul, h0, smul_zero]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) res).mp h1
    have h2 : (g ^ k * a) • β = 0 := by rw [mul_smul]; exact hk
    have h3 : g ^ k * a = 0 := hβ.injective (h2.trans (zero_smul _ β).symm)
    have hu : IsUnit (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen g) (g ^ (k + n))) :=
      IsLocalization.map_units Γ(Y, Y.basicOpen g) (⟨g ^ (k + n), n + k, by ring⟩ :
        Submonoid.powers g)
    apply hu.mul_left_cancel
    rw [mul_zero, pow_add, map_mul, mul_assoc, mul_comm _ (c - c'), ha, ← map_mul, h3,
      map_zero]
  · intro m
    obtain ⟨⟨m₀, ⟨_, n, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers g) res m
    obtain ⟨a, rfl⟩ := hβ.surjective m₀
    simp only at hm
    have hu : IsUnit (ρ (g ^ n)) :=
      IsLocalization.map_units Γ(Y, Y.basicOpen g) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    refine ⟨((hu.unit⁻¹ : Γ(Y, Y.basicOpen g)ˣ) : Γ(Y, Y.basicOpen g)) * ρ a, ?_⟩
    have e1 : ρ a • F.presheaf.map (homOfLE (Y.basicOpen_le g)).op β = res (a • β) := by
      rw [map_smul]; rfl
    change (((hu.unit⁻¹ : Γ(Y, Y.basicOpen g)ˣ) : Γ(Y, Y.basicOpen g)) * ρ a) •
      F.presheaf.map (homOfLE (Y.basicOpen_le g)).op β = m
    rw [mul_smul, e1, ← hm]
    change ((hu.unit⁻¹ : Γ(Y, Y.basicOpen g)ˣ) : Γ(Y, Y.basicOpen g)) • (ρ (g ^ n) • m) = m
    rw [← mul_smul, hu.val_inv_mul, one_smul]

end BasicOpen

section PullbackGenerator

variable {X Y : Scheme.{u}} (ν : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]

/-- **Pulled-back generators generate**: if `σ` freely generates `Γ(W, M)` over `Γ(W, 𝒪_X)`
(`W` affine, `M` quasi-coherent) and `V ⊆ ν⁻¹ W` is affine, then `ν^* σ|_V` freely generates
`Γ(V, ν^* M)` over `Γ(V, 𝒪_Y)`. -/
theorem bijective_smul_pullbackSectionLE {W : X.Opens} (hW : IsAffineOpen W) {V : Y.Opens}
    (hV : IsAffineOpen V) (hVW : V ≤ ν ⁻¹ᵁ W) (σ : Γ(M, W))
    (hσ : Function.Bijective (fun c : Γ(X, W) => c • σ)) :
    Function.Bijective (fun c : Γ(Y, V) => c • pullbackSectionLE ν M hVW σ) := by
  let _ : Algebra Γ(X, W) Γ(Y, V) := (ν.appLE W V hVW).hom.toAlgebra
  let _ : Module Γ(X, W) Γ((Scheme.Modules.pullback ν).obj M, V) :=
    Module.compHom _ (ν.appLE W V hVW).hom
  have : IsScalarTower Γ(X, W) Γ(Y, V) Γ((Scheme.Modules.pullback ν).obj M, V) :=
    ⟨fun r t m => mul_smul ((ν.appLE W V hVW).hom r) t m⟩
  have hbc := isBaseChange_pullbackSectionLinear ν M hW hV hVW (hθ := rfl)
  let e : Γ(X, W) ≃ₗ[Γ(X, W)] Γ(M, W) := LinearEquiv.ofBijective
    { toFun := fun c => c • σ
      map_add' := fun a b => add_smul a b σ
      map_smul' := fun a b => mul_smul a b σ } hσ
  let b : Module.Basis Unit Γ(X, W) Γ(M, W) := (Module.Basis.singleton Unit Γ(X, W)).map e
  let b' := hbc.basis b
  have hb' : b' () = pullbackSectionLE ν M hVW σ := by
    rw [IsBaseChange.basis_apply]
    change pullbackSectionLE ν M hVW (b ()) = _
    congr 1
    rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
    exact one_smul _ σ
  constructor
  · intro c c' hcc'
    have h1 := congrArg (fun n => b'.repr n ()) hcc'
    simp only [← hb', map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] at h1
    exact h1
  · intro n
    refine ⟨b'.repr n (), ?_⟩
    simp only
    rw [← hb']
    have := b'.sum_repr n
    simpa using this

end PullbackGenerator

section Lift

variable {Y : Scheme.{u}} {F G N : Y.Modules} (Θ : G ⟶ N) (ι : F ⟶ N)

/-- Injectivity of a morphism of modules on the sections over every open follows from injectivity
over a basis of opens below every open (here: every point has, inside every open
neighbourhood, an open on which the morphism is injective). -/
theorem injective_app_of_local
    (hloc : ∀ (W : Y.Opens) (y : Y), y ∈ W → ∃ W' : Y.Opens, W' ≤ W ∧ y ∈ W' ∧
      Function.Injective (Θ.app W')) (W : Y.Opens) : Function.Injective (Θ.app W) := by
  intro s t hst
  choose V hVW hyV hVinj using fun y : W => hloc W y.1 y.2
  refine Scheme.Modules.eq_of_restrict_eq G V (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩,
    hyV ⟨y, hy⟩⟩) hVW s t fun y => hVinj y ?_
  rw [Scheme.Modules.Hom.app_map, Scheme.Modules.Hom.app_map, hst]

variable (hΘ : ∀ W : Y.Opens, Function.Injective (Θ.app W))
  (hloc : ∀ (W : Y.Opens) (s : Γ(F, W)) (y : Y), y ∈ W → ∃ W' : Y.Opens, ∃ (h : W' ≤ W), y ∈ W' ∧
    ι.app W' (F.presheaf.map (homOfLE h).op s) ∈ Set.range (Θ.app W'))

include hΘ hloc in
/-- The sections of `F` lift through `Θ` (gluing in `G`). -/
theorem exists_app_eq (W : Y.Opens) (s : Γ(F, W)) : ∃ t : Γ(G, W), Θ.app W t = ι.app W s := by
  choose V hVW hyV t ht using fun y : W => hloc W s y.1 y.2
  have hcov : W ≤ ⨆ y : W, V y := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  obtain ⟨t₀, ht₀⟩ := Scheme.Modules.exists_glue G V hcov hVW t (fun y z => by
    apply hΘ
    rw [Scheme.Modules.Hom.app_map, Scheme.Modules.Hom.app_map, ht, ht,
      ← Scheme.Modules.Hom.app_map, ← Scheme.Modules.Hom.app_map]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl)
  refine ⟨t₀, Scheme.Modules.eq_of_restrict_eq N V hcov hVW _ _ fun y => ?_⟩
  rw [← Scheme.Modules.Hom.app_map, ← Scheme.Modules.Hom.app_map, ht₀, ht]

/-- The lift of a section (chosen; unique by injectivity of `Θ`). -/
def liftApp (W : Y.Opens) (s : Γ(F, W)) : Γ(G, W) :=
  (exists_app_eq Θ ι hΘ hloc W s).choose

theorem liftApp_spec (W : Y.Opens) (s : Γ(F, W)) : Θ.app W (liftApp Θ ι hΘ hloc W s) = ι.app W s :=
  (exists_app_eq Θ ι hΘ hloc W s).choose_spec

set_option backward.isDefEq.respectTransparency false in
/-- **Lifting along an injective morphism**: if `Θ : G ⟶ N` is injective on the sections over
every open and the sections of `F` land locally in the image of `Θ` under `ι : F ⟶ N`, then `ι`
factors uniquely as `α ≫ Θ`. -/
def lift : F ⟶ G where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := liftApp Θ ι hΘ hloc W.unop
          map_zero' := hΘ _ (by rw [liftApp_spec, map_zero, map_zero])
          map_add' := fun s s' => hΘ _ (by
            rw [map_add, liftApp_spec, liftApp_spec, liftApp_spec, map_add]) }
      naturality := fun {W W'} i => by
        ext s
        apply hΘ
        change Θ.app W'.unop (liftApp Θ ι hΘ hloc W'.unop (F.presheaf.map i s)) =
          Θ.app W'.unop (G.presheaf.map i (liftApp Θ ι hΘ hloc W.unop s))
        rw [liftApp_spec, show i = (homOfLE (leOfHom i.unop)).op from rfl,
          Scheme.Modules.Hom.app_map, Scheme.Modules.Hom.app_map, liftApp_spec] }
    (fun W r s => by
      apply hΘ W.unop
      have h1 := liftApp_spec Θ ι hΘ hloc W.unop (r • s)
      have h2 := Scheme.Modules.Hom.app_smul Θ (U := W.unop) r (liftApp Θ ι hΘ hloc W.unop s)
      have h3 := Scheme.Modules.Hom.app_smul ι (U := W.unop) r s
      rw [liftApp_spec Θ ι hΘ hloc W.unop s] at h2
      exact h1.trans (h3.trans h2.symm))

theorem lift_app (W : Y.Opens) (s : Γ(F, W)) :
    (lift Θ ι hΘ hloc).app W s = liftApp Θ ι hΘ hloc W s := rfl

theorem lift_app_spec (W : Y.Opens) (s : Γ(F, W)) :
    Θ.app W ((lift Θ ι hΘ hloc).app W s) = ι.app W s :=
  liftApp_spec Θ ι hΘ hloc W s

end Lift

section Comparison

variable {X S Y T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (q : Y ⟶ T)
  (ν : Y ⟶ X) (h : T ⟶ S) (sq : ν ≫ f = q ≫ h)

/-- The preimage `ν⁻¹ Sm(f)` of the smooth locus of `f`. -/
abbrev fibreLocus : Y.Opens := ν ⁻¹ᵁ f.smoothLocus

/-- The sheaf `j_* (Ω¹_{Y/T}|_{ν⁻¹ Sm(f)})` of differentials on `ν⁻¹ Sm(f)`, `j` its inclusion
(meromorphic differentials with poles along the preimage of the non-smooth locus). -/
def logDifferentials : Y.Modules :=
  (Scheme.Modules.pushforward (fibreLocus f ν).ι).obj
    ((relativeDifferentials q).restrict (fibreLocus f ν).ι)

/-- The restriction map `Ω¹_{Y/T} ⟶ j_* (Ω¹_{Y/T}|_{ν⁻¹ Sm(f)})`. -/
def toLogDifferentials : relativeDifferentials q ⟶ logDifferentials f q ν :=
  (Scheme.Modules.restrictAdjunction (fibreLocus f ν).ι).unit.app _

theorem toLogDifferentials_app (W : Y.Opens) (s : Γ(relativeDifferentials q, W)) :
    (toLogDifferentials f q ν).app W s = (relativeDifferentials q).presheaf.map
      (homOfLE ((fibreLocus f ν).ι.image_preimage_le W)).op s :=
  rfl

theorem image_preimage_le_preimage (W : X.Opens) :
    (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ W)) ≤
      ν ⁻¹ᵁ (f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W)) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
  intro y hy
  exact hy

include sq in
/-- The comparison map on sections over `W`: base change of differentials on `W ∩ Sm(f)`,
followed by restriction to `ν⁻¹ W ∩ ν⁻¹ Sm(f)`. -/
def comparisonApp (W : X.Opens) :
    Γ(dualizingSheaf f, W) ⟶ Γ((Scheme.Modules.pushforward ν).obj (logDifferentials f q ν), W) :=
  (baseChangeDifferentials f q ν h sq).app (f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W)) ≫
    (relativeDifferentials q).presheaf.map (homOfLE (image_preimage_le_preimage f ν W)).op

include sq in
set_option backward.isDefEq.respectTransparency false in
/-- **The comparison map** `ω_{X/S} ⟶ ν_* j_* (Ω¹_{Y/T}|_{ν⁻¹ Sm(f)})`, induced by the base change
map of differentials `ds ↦ d(ν^♯ s)` on the smooth locus. -/
def dualizingComparison :
    dualizingSheaf f ⟶ (Scheme.Modules.pushforward ν).obj (logDifferentials f q ν) where
  val := PresheafOfModules.homMk
    { app := fun W => comparisonApp f q ν h sq W.unop
      naturality := fun {W W'} i => by
        ext s
        have hWW : W'.unop ≤ W.unop := leOfHom i.unop
        have hO : f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W'.unop) ≤
            f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W.unop) :=
          f.smoothLocus.ι.image_mono (f.smoothLocus.ι.preimage_mono hWW)
        have hP : (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ W'.unop)) ≤
            (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ W.unop)) :=
          (fibreLocus f ν).ι.image_mono ((fibreLocus f ν).ι.preimage_mono (ν.preimage_mono hWW))
        change (relativeDifferentials q).presheaf.map
            (homOfLE (image_preimage_le_preimage f ν W'.unop)).op
            ((baseChangeDifferentials f q ν h sq).app _
              ((relativeDifferentials f).presheaf.map (homOfLE hO).op s)) =
          (relativeDifferentials q).presheaf.map (homOfLE hP).op
            ((relativeDifferentials q).presheaf.map
              (homOfLE (image_preimage_le_preimage f ν W.unop)).op
              ((baseChangeDifferentials f q ν h sq).app _ s))
        rw [Scheme.Modules.Hom.app_map]
        change (relativeDifferentials q).presheaf.map _
            ((relativeDifferentials q).presheaf.map _
              ((baseChangeDifferentials f q ν h sq).app _ s)) = _
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl }
    (fun W r s => by
      have hPO := image_preimage_le_preimage f ν W.unop
      let O := f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W.unop)
      let r' : Γ(X, W.unop) := r
      let s' : Γ(relativeDifferentials f, O) := s
      let θ := baseChangeDifferentials f q ν h sq
      let a : Γ(X, O) :=
        (f.smoothLocus.ι.appIso (f.smoothLocus.ι ⁻¹ᵁ W.unop)).inv (f.smoothLocus.ι.app W.unop r')
      have e1 : θ.app O (a • s') =
          (show Γ(relativeDifferentials q, ν ⁻¹ᵁ O) from
            ν.app O a • (show Γ(relativeDifferentials q, ν ⁻¹ᵁ O) from θ.app O s')) :=
        Scheme.Modules.Hom.app_smul θ a s'
      have e2 := Scheme.Modules.map_smul (relativeDifferentials q) (homOfLE hPO) (ν.app O a)
        (show Γ(relativeDifferentials q, ν ⁻¹ᵁ O) from θ.app O s')
      have e3 : Y.presheaf.map (homOfLE hPO).op (ν.app O a) =
          ((fibreLocus f ν).ι.appIso ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ W.unop))).inv
            ((fibreLocus f ν).ι.app (ν ⁻¹ᵁ W.unop) (ν.app W.unop r')) := by
        have hOW : O ≤ W.unop := f.smoothLocus.ι.image_preimage_le W.unop
        have nat : ν.app O (X.presheaf.map (homOfLE hOW).op r') =
            Y.presheaf.map (homOfLE (ν.preimage_mono hOW)).op (ν.app W.unop r') := by
          have := ConcreteCategory.congr_hom (ν.naturality (homOfLE hOW).op) r'
          simp only [CommRingCat.comp_apply] at this
          exact this
        simp only [a, Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Opens.ι_app]
        change Y.presheaf.map _ (ν.app O (X.presheaf.map (homOfLE hOW).op r')) =
          Y.presheaf.map _ (ν.app W.unop r')
        rw [nat, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
      change (relativeDifferentials q).presheaf.map (homOfLE hPO).op (θ.app O (a • s')) =
        ((fibreLocus f ν).ι.appIso ((fibreLocus f ν).ι ⁻¹ᵁ (ν ⁻¹ᵁ W.unop))).inv
            ((fibreLocus f ν).ι.app (ν ⁻¹ᵁ W.unop) (ν.app W.unop r')) •
          (relativeDifferentials q).presheaf.map (homOfLE hPO).op (θ.app O s')
      rw [e1, e2, e3])

include sq in
theorem dualizingComparison_app (W : X.Opens) (s : Γ(dualizingSheaf f, W)) :
    (dualizingComparison f q ν h sq).app W s = comparisonApp f q ν h sq W s := rfl

include sq in
/-- **The comparison map** `Θ : ν^* ω_{X/S} ⟶ j_* (Ω¹_{Y/T}|_{ν⁻¹ Sm(f)})`, adjoint to
`dualizingComparison` (blueprint `def:sm-omega-bcf-comparison`). -/
def pullbackComparison :
    (Scheme.Modules.pullback ν).obj (dualizingSheaf f) ⟶ logDifferentials f q ν :=
  ((Scheme.Modules.pullbackPushforwardAdjunction ν).homEquiv _ _).symm
    (dualizingComparison f q ν h sq)

include sq in
/-- `Θ(ν^* s|_V) = (comparison of s)|_V`. -/
theorem pullbackComparison_app_pullbackSectionLE {W : X.Opens} {V : Y.Opens}
    (hVW : V ≤ ν ⁻¹ᵁ W) (s : Γ(dualizingSheaf f, W)) :
    (pullbackComparison f q ν h sq).app V (pullbackSectionLE ν (dualizingSheaf f) hVW s) =
      (logDifferentials f q ν).presheaf.map (homOfLE hVW).op
        ((dualizingComparison f q ν h sq).app W s) := by
  rw [pullbackSectionLE_apply, Scheme.Modules.Hom.app_map]
  congr 1
  have h1 := (Scheme.Modules.pullbackPushforwardAdjunction ν).homEquiv_unit
    (dualizingSheaf f) (logDifferentials f q ν) (pullbackComparison f q ν h sq)
  rw [pullbackComparison, Equiv.apply_symm_apply] at h1
  rw [h1]
  rfl

end Comparison

end DeJongAlterations.StableModification.Omega.RosenlichtComponent
