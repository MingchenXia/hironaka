import Hironaka.Analytic.Unibranch.HironakaG11WindowTowers

/-!
# Uniqueness of lifts through glued blowup steps (goal G11, route step 5)

Tools for identifying window points of later stages of the glued G11 sequence: two continuous maps
into a stage `Y` over `X` (`p : Y ⟶ X` an isomorphism over `U`) which agree after `p` and send a
dense set into `p⁻¹ U` are equal (`eq_of_comp_eq_of_dense`; `p` is injective over `U`,
`injOn_of_isIsoOver`, and `Y` is Hausdorff); the points of a strict transform off the exceptional
locus are dense in it (`dense_strictTransform_diff`). When one map is open and the preimage of the
complement of `U` has empty interior (a singular-centre modification off its centre), density is
automatic: `eq_of_comp_eq_of_isOpenMap`, `eq_of_comp_eq_of_singularCentre`. Along the glued sequence these identify the
window maps of a later stage once they agree after projection to the previous stage. No named
proposition; nothing proves or assumes G11. Blueprint: `hironaka-g11-resume-lift-uniqueness.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold

namespace Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness

open Hironaka Hironaka.BlowupSequences
  SourceReducedComplexSpace

universe u

noncomputable section

/-- **A morphism which is an isomorphism over `U` is injective over `U`.** -/
theorem injOn_of_isIsoOver {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} {U : Set X.obj.left}
    (h : IsIsoOver p U) : InjOn p.hom.left.base (p.hom.left.base ⁻¹' U) := by
  obtain ⟨V, j, -, hjr, hjp, -⟩ := h
  intro y₁ hy₁ y₂ hy₂ hy
  rw [← hjr] at hy₁ hy₂
  obtain ⟨v₁, rfl⟩ := hy₁
  obtain ⟨v₂, rfl⟩ := hy₂
  have hinj : Function.Injective (j ≫ p.hom.left).base := hjp.base_open.injective
  have : (j ≫ p.hom.left).base v₁ = (j ≫ p.hom.left).base v₂ := by
    simpa using hy
  rw [hinj this]

/-- **Lifts agreeing after an isomorphism over `U` on a dense set are equal**: continuous maps `a`,
`b` into `Y` with `p ∘ a = p ∘ b`, where `p` is an isomorphism over `U` and `a` sends a dense set
into `p⁻¹ U`, are equal (`Y` is Hausdorff). -/
theorem eq_of_comp_eq_of_dense {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} {U : Set X.obj.left}
    (h : IsIsoOver p U) {A : Type*} [TopologicalSpace A] {a b : A → Y.obj.left} (ha : Continuous a)
    (hb : Continuous b) (hab : ∀ x, p.hom.left.base (a x) = p.hom.left.base (b x)) {D : Set A}
    (hD : Dense D) (hDU : ∀ x ∈ D, p.hom.left.base (a x) ∈ U) : a = b := by
  let : T2Space Y.obj.left := Y.property.1
  refine Continuous.ext_on hD ha hb fun x hx => injOn_of_isIsoOver h (hDU x hx) ?_ (hab x)
  show p.hom.left.base (b x) ∈ U
  rw [← hab x]
  exact hDU x hx

/-- **Lifts through an isomorphism over `U` whose complement has thin preimage** are determined by
their projections when one of them is an open map: continuous `a`, `b` into `Y` with
`p ∘ a = p ∘ b`, `b` open, `p` an isomorphism over `U` and `p⁻¹ (Uᶜ)` with empty interior. -/
theorem eq_of_comp_eq_of_isOpenMap {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} {U : Set X.obj.left}
    (h : IsIsoOver p U) (hint : interior (p.hom.left.base ⁻¹' Uᶜ) = ∅) {A : Type*} [TopologicalSpace A]
    {a b : A → Y.obj.left} (ha : Continuous a) (hb : Continuous b) (hbo : IsOpenMap b)
    (hab : ∀ x, p.hom.left.base (a x) = p.hom.left.base (b x)) : a = b := by
  have hD' : interior (b ⁻¹' (p.hom.left.base ⁻¹' U))ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hsub : b '' interior (b ⁻¹' (p.hom.left.base ⁻¹' U))ᶜ ⊆ p.hom.left.base ⁻¹' Uᶜ := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ (b ⁻¹' (p.hom.left.base ⁻¹' U))ᶜ := interior_subset hz
      exact hz'
    have hmem : b x ∈ interior (p.hom.left.base ⁻¹' Uᶜ) :=
      interior_maximal hsub (hbo _ isOpen_interior) ⟨x, hx, rfl⟩
    rw [hint] at hmem
    exact hmem
  have hD : Dense (b ⁻¹' (p.hom.left.base ⁻¹' U)) := by
    simpa using interior_eq_empty_iff_dense_compl.mp hD'
  exact eq_of_comp_eq_of_dense h ha hb hab hD fun x hx => by rw [hab x]; exact hx

/-- **Lifts through a singular-centre blowup are determined by their projections** (one of them an
open map): for `p` a singular-centre modification which is an isomorphism off `S ⊆ Sing X`. -/
theorem eq_of_comp_eq_of_singularCentre {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : HironakaG11SingularCentreModification.IsSingularCentreModification p) {S : Set X.obj.left}
    (hiso : IsIsoOver p Sᶜ)
    (hS : S ⊆ Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
      X.obj)
    {A : Type*} [TopologicalSpace A] {a b : A → Y.obj.left} (ha : Continuous a) (hb : Continuous b)
    (hbo : IsOpenMap b) (hab : ∀ x, p.hom.left.base (a x) = p.hom.left.base (b x)) : a = b := by
  refine eq_of_comp_eq_of_isOpenMap hiso ?_ ha hb hbo hab
  rw [compl_compl]
  exact eq_empty_of_subset_empty ((interior_mono (preimage_mono hS)).trans
    hp.interior_preimage_intrinsicSingularLocus.subset)

/-- **Window maps through a singular-centre blowup step are determined by the squares**: let `p` be
a singular-centre modification which is an isomorphism off `S ⊆ Sing X`, and `L₁ : W₁ ⟶ Y`,
`L₂ : W₂ ⟶ Y` morphisms with `L₁ ≫ p = q₁`, `L₂ ≫ p = q₂`, `L₂` an open immersion (e.g. the
blown-up windows of `exists_singularCentreBlowup_windows`). For continuous `φ : A → W₁` and a
continuous open `e : A → W₂` with `q₁ ∘ φ = q₂ ∘ e`, also `L₁ ∘ φ = L₂ ∘ e`. Along the glued G11
sequence this identifies window points of stage `k + 1` from an identification at stage `k`. -/
theorem lift_eq_of_squares {X Y W₁ W₂ : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : HironakaG11SingularCentreModification.IsSingularCentreModification p) {S : Set X.obj.left}
    (hiso : IsIsoOver p Sᶜ)
    (hS : S ⊆ Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
      X.obj)
    {L₁ : W₁ ⟶ Y} {L₂ : W₂ ⟶ Y} {q₁ : W₁ ⟶ X} {q₂ : W₂ ⟶ X} (h₁ : L₁ ≫ p = q₁) (h₂ : L₂ ≫ p = q₂)
    (hL₂ : LocallyRingedSpace.IsOpenImmersion L₂.hom.left) {A : Type*} [TopologicalSpace A]
    {φ : A → W₁.obj.left} {e : A → W₂.obj.left} (hφ : Continuous φ) (he : Continuous e)
    (heo : IsOpenMap e) (hbase : ∀ x, q₁.hom.left.base (φ x) = q₂.hom.left.base (e x)) (x : A) :
    L₁.hom.left.base (φ x) = L₂.hom.left.base (e x) := by
  subst h₁ h₂
  have hL₂o : Topology.IsOpenEmbedding L₂.hom.left.base := hL₂.base_open
  have hfun := eq_of_comp_eq_of_singularCentre hp hiso hS (a := fun x => L₁.hom.left.base (φ x))
    (b := fun x => L₂.hom.left.base (e x)) (L₁.hom.left.base.hom.continuous.comp hφ)
    (hL₂o.continuous.comp he) (hL₂o.isOpenMap.comp heo) (fun x => hbase x)
  exact congrFun hfun x

/-- **The points of a strict transform off the exceptional locus are dense in it.** -/
theorem dense_strictTransform_diff {n : ℕ} {M Z : Type u} [TopologicalSpace M] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] (π : Z → M) (A : Set M) :
    Dense ((Subtype.val : strictTransform n π A → Z) ⁻¹' (π ⁻¹' A \ exceptionalLocus n π)) := by
  rw [Subtype.dense_iff]
  apply closure_mono
  intro y hy
  exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩

end

end Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness
