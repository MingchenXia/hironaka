import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticSubsets
import Hironaka.Analytic.PotentialTheory.HolomorphicPullback
import Hironaka.Analytic.PshDiscLocalGlobal

/-!
# Plurisubharmonic functions on complex spaces

Source `def:unibranch:L105` (first part). A function `φ : X → [-∞, ∞)` on a
complex space `X` is plurisubharmonic if

1. `φ` is not identically `-∞` on any irreducible component of `X`, and
2. for every `x ∈ X` there are an open neighbourhood `V` of `x`, a domain
   `Ω ⊆ ℂ^N`, a closed immersion `V ↪ Ω` and `ψ ∈ PSH(Ω)` with
   `φ|_V = ψ|_V` under the immersion.

Closed immersions of open subspaces into domains are the local embeddings of
`ComplexSpaceLocalEmbedding.lean` whose ambient open set is connected; `PSH(Ω)`
is the book's `def:psh` (`Hironaka.Analytic.PotentialTheory.PSHOn`, which includes `ψ ≢ -∞`); irreducible
components are those of `ComplexSpaceAnalyticSubsets.lean`.

Main results:

* `SourceReducedComplexSpace.IsPSH`: the definition, and `PSHSet` (`PSH(X)`).
* `IsPSH.ne_top`, `IsPSH.upperSemicontinuous`: psh functions take values in
  `[-∞, ∞)` and are upper semicontinuous.
* `exists_ambient_of_morphism`, `exists_ambient`: independence of the
  embedding. Near every point of every local embedding (and along every
  morphism from an embedded model), a psh function is the restriction of an
  ambient function satisfying the disc criterion.
* `isPSH_model_univ_iff`: on a domain `U ⊆ ℂ^n`, viewed as a complex space,
  `PSH` in the sense of complex spaces is exactly the book's `PSH(U)`.
* `IsPSH.fornaessNarasimhan_forward`: the implication (1) ⇒ (2) of
  `thm:FN`: a psh function is upper semicontinuous and its pull-back by every
  holomorphic disc `f : Δ → X` with `f^*φ ≢ -∞` is subharmonic.

Original source: Appendix B (`appendix_unibranch.tex`), `def:unibranch:L105`,
`thm:FN`. Blueprint: `claude-unibranch.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology Manifold ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces

namespace Hironaka.Analytic.Unibranch

noncomputable section

namespace SourceReducedComplexSpace

variable (X : SourceReducedComplexSpace)

/-- Condition 2 of `def:unibranch:L105` at `x`: in some local embedding of an
open neighbourhood of `x` into a domain `Ω`, the function is the restriction of
an element of `PSH(Ω)`. -/
def IsLocallyAmbientPSHAt (φ : X.obj.left → EReal) (x : X.obj.left) : Prop :=
  ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    IsConnected (e.ambient : Set (ComplexModel e.dim)) ∧
    ∃ ψ : ComplexModel e.dim → EReal, Hironaka.Analytic.PotentialTheory.PSHOn ψ e.ambient ∧
      ∀ c : e.carrier, φ (e.toPoint c) = ψ c.val.val

/-- Source `def:unibranch:L105`: plurisubharmonic functions on a complex space. -/
def IsPSH (φ : X.obj.left → EReal) : Prop :=
  (∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥) ∧
    ∀ x : X.obj.left, X.IsLocallyAmbientPSHAt φ x

/-- `PSH(X)`, the set of plurisubharmonic functions on the complex space `X`. -/
def PSHSet : Set (X.obj.left → EReal) := {φ | X.IsPSH φ}

variable {X}

theorem IsLocallyAmbientPSHAt.ne_top {φ : X.obj.left → EReal} {x : X.obj.left}
    (h : X.IsLocallyAmbientPSHAt φ x) : φ x ≠ ⊤ := by
  obtain ⟨e, ⟨c, rfl⟩, -, ψ, hψ, hφ⟩ := h
  rw [hφ]
  exact hψ.disc.ne_top _ c.val.property

theorem IsLocallyAmbientPSHAt.upperSemicontinuousAt {φ : X.obj.left → EReal}
    {x : X.obj.left} (h : X.IsLocallyAmbientPSHAt φ x) : UpperSemicontinuousAt φ x := by
  obtain ⟨e, ⟨c, rfl⟩, -, ψ, hψ, hφ⟩ := h
  intro y hy
  rw [hφ] at hy
  have hψc : ∀ᶠ w in 𝓝 c.val.val, ψ w < y := by
    have h := hψ.disc.upperSemicontinuousOn _ c.val.property y hy
    rwa [nhdsWithin_eq_nhds.mpr (e.ambient.isOpen.mem_nhds c.val.property)] at h
  have h2 : ∀ᶠ c' in 𝓝 c, ψ c'.val.val < y :=
    ((continuous_subtype_val.comp continuous_subtype_val).continuousAt
      (x := c)).tendsto.eventually hψc
  rw [← e.isOpenEmbedding_toPoint.map_nhds_eq c]
  exact eventually_map.mpr (h2.mono fun c' hc' => by
    show φ (e.toPoint c') < y
    rw [hφ]
    exact hc')

/-- Plurisubharmonic functions take values in `[-∞, ∞)`. -/
theorem IsPSH.ne_top {φ : X.obj.left → EReal} (hφ : X.IsPSH φ) (x : X.obj.left) :
    φ x ≠ ⊤ :=
  (hφ.2 x).ne_top

/-- Plurisubharmonic functions are upper semicontinuous. -/
theorem IsPSH.upperSemicontinuous {φ : X.obj.left → EReal} (hφ : X.IsPSH φ) :
    UpperSemicontinuous φ :=
  fun x => (hφ.2 x).upperSemicontinuousAt

/-- Independence of the embedding, along an arbitrary morphism from an embedded
model `(U, C)`: if condition 2 of `def:unibranch:L105` holds at every point, then
near every point of `C` the pull-back of `φ` is the restriction of an ambient
function satisfying the disc criterion (plurisubharmonic or identically `-∞` on
the components). -/
theorem exists_ambient_of_morphism {φ : X.obj.left → EReal}
    (hφ : ∀ x : X.obj.left, X.IsLocallyAmbientPSHAt φ x)
    {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (F : (modelOver U C).left ⟶ X.obj.left) (hF : F ≫ X.obj.hom = (modelOver U C).hom)
    (c : C) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ U ∧
      ∃ ψ : ComplexModel n → EReal, Hironaka.DiscPshOn ψ W ∧
        ∀ y : C, y.val.val ∈ W → φ (F.base y) = ψ y.val.val := by
  obtain ⟨e₂, hc, -, ψ, hψ, hφ₂⟩ := hφ (F.base c)
  obtain ⟨W, hW, hcW, hWU, G, hG, hGmaps, hfac⟩ :=
    LocalEmbedding.exists_differentiableOn_factor F hF e₂ c hc
  refine ⟨W, hW, hcW, hWU, fun z => ψ (G z),
    Hironaka.Analytic.PotentialTheory.discPshOn_comp_holomorphic hW e₂.ambient.isOpen hG hGmaps hψ, ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hfac y hy
  rw [← hzy, hφ₂ z, hz]

/-- Independence of the embedding: near every point of every local embedding, a
function satisfying condition 2 of `def:unibranch:L105` everywhere is the
restriction of an ambient function satisfying the disc criterion. -/
theorem exists_ambient {φ : X.obj.left → EReal}
    (hφ : ∀ x : X.obj.left, X.IsLocallyAmbientPSHAt φ x) (e : LocalEmbedding X)
    (c : e.carrier) :
    ∃ W : Set (ComplexModel e.dim), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ e.ambient ∧
      ∃ ψ : ComplexModel e.dim → EReal, Hironaka.DiscPshOn ψ W ∧
        ∀ y : e.carrier, y.val.val ∈ W → φ (e.toPoint y) = ψ y.val.val :=
  exists_ambient_of_morphism hφ e.map e.overPoint c

/-- On a domain `U ⊆ ℂ^n`, viewed as a complex space, plurisubharmonicity in the
sense of complex spaces (`def:unibranch:L105`) is exactly the book's `PSH(U)`
(`def:psh`). -/
theorem isPSH_model_univ_iff {n : ℕ} {U : Opens (ComplexModel n)}
    (hU : IsConnected (U : Set (ComplexModel n))) (u : ComplexModel n → EReal) :
    (sourceReducedComplexSpaceModel U (univ : Set U) isComplexAnalyticSubset_univ).IsPSH
        (fun p : (univ : Set U) => u p.val.val) ↔ Hironaka.Analytic.PotentialTheory.PSHOn u U := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · apply _root_.Hironaka.PlurisubharmonicOn.discPshOn
      intro z hz
      obtain ⟨W, hW, hzW, hWU, ψ, hψ, hφ⟩ :=
        exists_ambient h2 (LocalEmbedding.model U (univ : Set U) isComplexAnalyticSubset_univ)
          ⟨⟨z, hz⟩, trivial⟩
      refine ⟨W, hW, hzW, hψ.congr ?_⟩
      intro w hw
      exact (hφ ⟨⟨w, hWU hw⟩, trivial⟩ hw).symm
    · obtain ⟨z, -, hz⟩ := h1 univ ((isIrreducibleComponent_model_univ_iff hU univ).mpr rfl)
      exact ⟨z.val.val, z.val.property, hz⟩
  · intro hu
    refine ⟨?_, ?_⟩
    · intro Z hZ
      rw [isIrreducibleComponent_model_univ_iff hU] at hZ
      subst hZ
      obtain ⟨z, hz, hz'⟩ := hu.nontrivial
      exact ⟨⟨⟨z, hz⟩, trivial⟩, trivial, hz'⟩
    · intro x
      exact ⟨LocalEmbedding.model U (univ : Set U) isComplexAnalyticSubset_univ, ⟨x, rfl⟩, hU,
        u, hu, fun c => rfl⟩

/-! ### Holomorphic discs: the forward implication of the Fornæss--Narasimhan theorem -/

/-- The open unit disc `Δ`, as an open subset of `ℂ^1`. -/
def unitDiscOpens : Opens (ComplexModel 1) := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The open unit disc `Δ` as a complex space. -/
abbrev unitDisc : SourceReducedComplexSpace :=
  sourceReducedComplexSpaceModel unitDiscOpens (univ : Set unitDiscOpens)
    isComplexAnalyticSubset_univ

/-- The standard linear isometry `ℂ ≅ ℂ^1`. -/
def discCoordinate : ℂ →L[ℂ] ComplexModel 1 :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))

theorem norm_discCoordinate (t : ℂ) : ‖discCoordinate t‖ = ‖t‖ := by
  simp [discCoordinate, norm_smul]

open Classical in
/-- The function on `ℂ^n` given by the pull-back of `φ` along a morphism from
the domain `U` (extended by `-∞` outside `U`). -/
def modelPullback {n : ℕ} {U : Opens (ComplexModel n)}
    (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left) (φ : X.obj.left → EReal) :
    ComplexModel n → EReal := fun z =>
  if h : z ∈ U then φ (F.base (⟨⟨z, h⟩, trivial⟩ : (univ : Set U))) else ⊥

/-- The pull-back `f^*φ` of `φ` by a holomorphic disc `f : Δ → X`, as a function
on `ℂ` (`-∞` outside `Δ`). -/
def discPullback (f : unitDisc ⟶ X) (φ : X.obj.left → EReal) : ℂ → EReal :=
  fun t => modelPullback f.hom.left φ (discCoordinate t)

theorem discCoordinate_preimage :
    (fun t : ℂ => 0 + discCoordinate t) ⁻¹' (unitDiscOpens : Set (ComplexModel 1)) =
      Metric.ball (0 : ℂ) 1 := by
  ext t
  simp [unitDiscOpens, norm_discCoordinate]

/-- Along an arbitrary morphism from a domain, the pull-back of a function
satisfying condition 2 of `def:unibranch:L105` satisfies the disc criterion. -/
theorem discPshOn_modelPullback {φ : X.obj.left → EReal}
    (hφ : ∀ x : X.obj.left, X.IsLocallyAmbientPSHAt φ x)
    {n : ℕ} {U : Opens (ComplexModel n)}
    (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hF : F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) :
    Hironaka.DiscPshOn (modelPullback F φ) U := by
  apply _root_.Hironaka.PlurisubharmonicOn.discPshOn
  intro z hz
  obtain ⟨W, hW, hzW, hWU, ψ, hψ, hφW⟩ :=
    exists_ambient_of_morphism hφ F hF ⟨⟨z, hz⟩, trivial⟩
  refine ⟨W, hW, hzW, hψ.congr ?_⟩
  intro w hw
  simp only [modelPullback]
  split_ifs with h
  · exact (hφW ⟨⟨w, h⟩, trivial⟩ hw).symm
  · exact absurd (hWU hw) h

/-- Source `thm:FN`, implication (1) ⇒ (2): a plurisubharmonic function on a
complex space is upper semicontinuous, and for every holomorphic disc
`f : Δ → X` with `f^*φ ≢ -∞` the pull-back `f^*φ` is subharmonic on `Δ`. -/
theorem IsPSH.fornaessNarasimhan_forward {φ : X.obj.left → EReal} (hφ : X.IsPSH φ) :
    UpperSemicontinuous φ ∧
      ∀ f : unitDisc ⟶ X, (∃ t ∈ Metric.ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
        Hironaka.Analytic.PotentialTheory.SubharmonicOn (discPullback f φ) (Metric.ball (0 : ℂ) 1) := by
  refine ⟨hφ.upperSemicontinuous, fun f hne => ?_⟩
  have hD := discPshOn_modelPullback hφ.2 f.hom.left (Over.w f.hom)
  have hL := hD.comp_affine discCoordinate 0
  rw [discCoordinate_preimage] at hL
  have heq : (fun t : ℂ => modelPullback f.hom.left φ (0 + discCoordinate t)) =
      discPullback f φ := by
    funext t
    simp [discPullback]
  rw [heq] at hL
  exact Hironaka.Analytic.PotentialTheory.subharmonicOn_of_disc hL hne

end SourceReducedComplexSpace

end

end Hironaka.Analytic.Unibranch
