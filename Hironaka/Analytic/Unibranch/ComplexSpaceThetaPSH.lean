import Hironaka.Analytic.Unibranch.ComplexSpacePSH
import Hironaka.Analytic.PotentialTheory.GlobalPotentialsBasic
import Hironaka.Analytic.HolomorphicDDC

/-!
# Smooth forms and `θ`-plurisubharmonic functions on complex spaces

Source `def:unibranch:L105` (second part). A smooth real form on a complex space
`X` is locally the restriction of a smooth form on the ambient space of a local
embedding (footnote of `def:unibranch:L105`: "closed means that locally `θ` is
defined by a closed form under a local embedding"). We make this precise as
follows.

* An ambient form `v` on `Ω ⊇ C` *vanishes on* `X` over `W ⊆ Ω`
  (`LocalEmbedding.VanishesOn`) if its pull-back along every holomorphic map from
  an open subset of some `ℂ^m` into `C ∩ W` vanishes. On the smooth locus this is
  vanishing of the restriction to the tangent spaces.
* A smooth real `k`-form on `X` (`SpaceForm`) is a family of local embeddings
  covering `X` with smooth ambient representatives whose differences, pulled back
  along every holomorphic transition map, vanish on `X`.
* `θ` *restricts to* an ambient form `v` on a local embedding
  (`SpaceForm.RestrictsTo`) if `v` and the representatives of `θ` agree on `X`
  along every holomorphic transition; this is the meaning of `θ = (ddᶜ g)|_V`.
* `θ` is closed (`SpaceForm.IsClosed`) if locally it restricts to a closed
  ambient form, and of type `(1,1)` (`SpaceForm.IsOneOne`) if locally it
  restricts to a `J`-invariant ambient form.
* `φ` is `θ`-psh (`SourceReducedComplexSpace.IsThetaPSH`) if near every point
  there are a local embedding of a neighbourhood `V` into a domain `Ω` and a
  smooth `g` on `Ω` with `θ = (ddᶜ g)|_V` and `g|_V + φ|_V ∈ PSH(V)`; here
  `PSH(V)` is `def:unibranch:L105` (first part) on the complex space `V`, which
  the local embedding identifies with the embedded model `(Ω, C)`.

Sanity checks on a domain `U ⊆ ℂ^n` with the form `θ₀` of `U`
(`SpaceForm.ofDomain`): restriction to the identity embedding is equality of
ambient forms (`SpaceForm.restrictsTo_ofDomain_model_iff`), and local smooth
potentials `g` with `ddᶜ g = θ₀` and `g + u ∈ PSH` give `θ₀`-psh functions in the
sense of complex spaces (`isThetaPSH_ofDomain_of_local_potentials`).

Original source: Appendix B (`appendix_unibranch.tex`), `def:unibranch:L105`.
Blueprint: `claude-unibranch.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology Manifold ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces

namespace Hironaka.Analytic.Unibranch

noncomputable section

/-- Smooth real `k`-forms on (an open subset of) `ℂ^N`, as coefficient fields. -/
abbrev AmbientForm (N k : ℕ) : Type :=
  ComplexModel N → (ComplexModel N) [⋀^Fin k]→L[ℝ] ℝ

/-- Pull-back of an ambient form along a map `G : ℂ^m → ℂ^N`. -/
def pullbackForm {m N k : ℕ} (G : ComplexModel m → ComplexModel N) (v : AmbientForm N k) :
    AmbientForm m k :=
  fun z => (v (G z)).compContinuousLinearMap (fderiv ℝ G z)

namespace LocalEmbedding

variable {X : SourceReducedComplexSpace}

/-- An ambient form `v` vanishes on `X` over `W ⊆ Ω`: its pull-back along every
holomorphic map from an open subset of some `ℂ^m` with values in `C ∩ W` is zero. -/
def VanishesOn (e : LocalEmbedding X) {k : ℕ} (W : Set (ComplexModel e.dim))
    (v : AmbientForm e.dim k) : Prop :=
  ∀ (m : ℕ) (D : Set (ComplexModel m)) (h : ComplexModel m → ComplexModel e.dim),
    IsOpen D → DifferentiableOn ℂ h D →
    (∀ z ∈ D, h z ∈ W ∧ ∃ c : e.carrier, c.val.val = h z) →
    ∀ z ∈ D, pullbackForm h v z = 0

/-- `G : W → Ω₂` is a holomorphic transition map from `e₁` to `e₂` over the open
set `W ⊆ Ω₁`: it carries `C₁ ∩ W` into `C₂`, compatibly with the maps to `X`. -/
def IsTransition (e₁ e₂ : LocalEmbedding X) (W : Set (ComplexModel e₁.dim))
    (G : ComplexModel e₁.dim → ComplexModel e₂.dim) : Prop :=
  IsOpen W ∧ W ⊆ e₁.ambient ∧ DifferentiableOn ℂ G W ∧ MapsTo G W e₂.ambient ∧
    ∀ y : e₁.carrier, y.val.val ∈ W → ∃ z : e₂.carrier, z.val.val = G y.val.val ∧
      e₂.toPoint z = e₁.toPoint y

/-- Holomorphic transition maps exist near every point of the overlap. -/
theorem exists_isTransition (e₁ e₂ : LocalEmbedding X) (c : e₁.carrier)
    (hc : e₁.toPoint c ∈ range e₂.toPoint) :
    ∃ W G, c.val.val ∈ W ∧ e₁.IsTransition e₂ W G := by
  obtain ⟨W, hW, hcW, hWU, G, hG, hGmaps, hfac⟩ := e₁.exists_transition e₂ c hc
  exact ⟨W, G, hcW, hW, hWU, hG, hGmaps, hfac⟩

end LocalEmbedding

/-- Smooth real `k`-forms on a complex space: local embeddings covering `X`, with
smooth ambient representatives which agree on `X` along every holomorphic
transition map. -/
structure SpaceForm (X : SourceReducedComplexSpace) (k : ℕ) where
  /-- Index set of the covering family of local embeddings. -/
  ι : Type
  /-- The covering family of local embeddings. -/
  chart : ι → LocalEmbedding X
  covers : ∀ x : X.obj.left, ∃ i, x ∈ range (chart i).toPoint
  /-- The smooth ambient representatives. -/
  rep : (i : ι) → AmbientForm (chart i).dim k
  smooth : ∀ i, ContDiffOn ℝ ∞ (rep i) (chart i).ambient
  compatible : ∀ (i j : ι) (W : Set (ComplexModel (chart i).dim))
    (G : ComplexModel (chart i).dim → ComplexModel (chart j).dim),
    (chart i).IsTransition (chart j) W G →
      (chart i).VanishesOn W (rep i - pullbackForm G (rep j))

namespace SpaceForm

variable {X : SourceReducedComplexSpace} {k : ℕ}

/-- The restriction of `θ` to the image of a local embedding `e` is given by the
ambient form `v`: they agree on `X` along every holomorphic transition map to the
charts of `θ`. -/
def RestrictsTo (θ : SpaceForm X k) (e : LocalEmbedding X) (v : AmbientForm e.dim k) : Prop :=
  ∀ (i : θ.ι) (W : Set (ComplexModel e.dim)) (G : ComplexModel e.dim → ComplexModel (θ.chart i).dim),
    e.IsTransition (θ.chart i) W G → e.VanishesOn W (v - pullbackForm G (θ.rep i))

/-- Closedness: locally `θ` is the restriction of a closed ambient form. -/
def IsClosed (θ : SpaceForm X k) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ v : AmbientForm e.dim k, ContDiffOn ℝ ∞ v e.ambient ∧
      (∀ z ∈ e.ambient, extDeriv v z = 0) ∧ θ.RestrictsTo e v

/-- Type `(1,1)`: locally `θ` is the restriction of a real two-form invariant
under the complex structure. -/
def IsOneOne (θ : SpaceForm X 2) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ v : AmbientForm e.dim 2, ContDiffOn ℝ ∞ v e.ambient ∧
      (∀ z ∈ e.ambient, ∀ a b : ComplexModel e.dim,
        v z ![Complex.I • a, Complex.I • b] = v z ![a, b]) ∧ θ.RestrictsTo e v

end SpaceForm

namespace SourceReducedComplexSpace

variable (X : SourceReducedComplexSpace)

/-- Source `def:unibranch:L105` (second part): `θ`-plurisubharmonic functions.
Near every point there are a local embedding of a neighbourhood `V` into a domain
`Ω`, and a smooth `g` on `Ω`, with `θ = (ddᶜ g)|_V` and `g|_V + φ|_V ∈ PSH(V)`. -/
def IsThetaPSH (θ : SpaceForm X 2) (φ : X.obj.left → EReal) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    IsConnected (e.ambient : Set (ComplexModel e.dim)) ∧
    ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
      θ.RestrictsTo e (smoothDDC g) ∧
      (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).IsPSH
        (fun c : e.carrier => (g c.val.val : EReal) + φ (e.toPoint c))

end SourceReducedComplexSpace

/-! ### Sanity checks on a domain -/

section Domain

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- A domain `U ⊆ ℂ^n` as a complex space. -/
abbrev domainSpace (U : Opens (ComplexModel n)) : SourceReducedComplexSpace :=
  sourceReducedComplexSpaceModel U (univ : Set U) isComplexAnalyticSubset_univ

/-- The tautological embedding of a domain. -/
abbrev domainChart (U : Opens (ComplexModel n)) : LocalEmbedding (domainSpace U) :=
  LocalEmbedding.model U (univ : Set U) isComplexAnalyticSubset_univ

/-- The restriction of the tautological embedding of a domain to a smaller open set. -/
abbrev domainSubchart (U B : Opens (ComplexModel n)) (hB : B ≤ U) :
    LocalEmbedding (domainSpace U) :=
  (domainChart U).restrictWith B hB (univ : Set B) (fun _ => by simp)

/-- On a domain, every transition map from a subchart to the tautological chart is
the identity on its domain. -/
theorem domainSubchart_transition_eq {B : Opens (ComplexModel n)} (hB : B ≤ U)
    {W : Set (ComplexModel n)} {G : ComplexModel n → ComplexModel n}
    (hG : (domainSubchart U B hB).IsTransition (domainChart U) W G) :
    ∀ y ∈ W, G y = y := by
  intro y hy
  have hyB : y ∈ B := hG.2.1 hy
  obtain ⟨z, hz, hzy⟩ := hG.2.2.2.2 ⟨⟨y, hyB⟩, trivial⟩ hy
  rw [LocalEmbedding.restrictWith_toPoint, LocalEmbedding.model_toPoint,
    LocalEmbedding.model_toPoint] at hzy
  rw [← hz, hzy]

theorem domainChart_transition_eq {W : Set (ComplexModel n)} {G : ComplexModel n → ComplexModel n}
    (hG : (domainChart U).IsTransition (domainChart U) W G) : ∀ y ∈ W, G y = y := by
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hG.2.2.2.2 ⟨⟨y, hG.2.1 hy⟩, trivial⟩ hy
  rw [LocalEmbedding.model_toPoint, LocalEmbedding.model_toPoint] at hzy
  rw [← hz, hzy]

/-- Pull-back along a map which is the identity near a point. -/
theorem pullbackForm_eq_of_eqOn_id {k : ℕ} {W : Set (ComplexModel n)} (hW : IsOpen W)
    {G : ComplexModel n → ComplexModel n} (hGW : ∀ y ∈ W, G y = y) (v : AmbientForm n k)
    {z : ComplexModel n} (hz : z ∈ W) : pullbackForm G v z = v z := by
  have hev : G =ᶠ[𝓝 z] id := by
    filter_upwards [hW.mem_nhds hz] with y hy
    exact hGW y hy
  have hd : fderiv ℝ G z = ContinuousLinearMap.id ℝ (ComplexModel n) := by
    rw [hev.fderiv_eq, fderiv_id]
  ext a
  simp [pullbackForm, hd, hGW z hz]

@[simp] theorem pullbackForm_id {k : ℕ} (v : AmbientForm n k) :
    pullbackForm (id : ComplexModel n → ComplexModel n) v = v := by
  funext z
  exact pullbackForm_eq_of_eqOn_id isOpen_univ (fun _ _ => rfl) v (mem_univ z)

theorem sub_pullbackForm_eq_zero {k : ℕ} {W : Set (ComplexModel n)} (hW : IsOpen W)
    {G : ComplexModel n → ComplexModel n} (hGW : ∀ y ∈ W, G y = y) {v θ₀ : AmbientForm n k}
    {z : ComplexModel n} (hz : z ∈ W) (hvz : v z = θ₀ z) :
    v z - pullbackForm G θ₀ z = 0 := by
  rw [pullbackForm_eq_of_eqOn_id hW hGW θ₀ hz, hvz, sub_self]

/-- An ambient form which is zero on `W` vanishes on `X` over `W`. -/
theorem vanishesOn_of_eqOn_zero {X : SourceReducedComplexSpace} (e : LocalEmbedding X) {k : ℕ}
    {W : Set (ComplexModel e.dim)} {v : AmbientForm e.dim k} (hv : ∀ z ∈ W, v z = 0) :
    e.VanishesOn W v := by
  intro m D h _ _ hDW z hz
  ext a
  simp [pullbackForm, hv (h z) (hDW z hz).1]

/-- The smooth form of a domain, as a form on the domain viewed as a complex space. -/
def SpaceForm.ofDomain {k : ℕ} (U : Opens (ComplexModel n)) (θ₀ : AmbientForm n k)
    (hθ₀ : ContDiffOn ℝ ∞ θ₀ U) : SpaceForm (domainSpace U) k where
  ι := Unit
  chart _ := domainChart U
  covers x := ⟨(), x, rfl⟩
  rep _ := θ₀
  smooth _ := hθ₀
  compatible := by
    rintro - - W G hG
    apply vanishesOn_of_eqOn_zero
    intro z hz
    exact sub_pullbackForm_eq_zero hG.1 (domainChart_transition_eq hG) hz rfl

/-- Restriction to the tautological chart of a domain is equality of ambient forms. -/
theorem SpaceForm.restrictsTo_ofDomain_model_iff {k : ℕ} (θ₀ : AmbientForm n k)
    (hθ₀ : ContDiffOn ℝ ∞ θ₀ U) (v : AmbientForm n k) :
    (SpaceForm.ofDomain U θ₀ hθ₀).RestrictsTo (domainChart U) v ↔ ∀ z ∈ U, v z = θ₀ z := by
  constructor
  · intro h z hz
    have htr : (domainChart U).IsTransition ((SpaceForm.ofDomain U θ₀ hθ₀).chart ()) U id := by
      refine ⟨U.isOpen, subset_rfl, differentiableOn_id, fun y hy => hy, ?_⟩
      intro y _
      exact ⟨y, rfl, rfl⟩
    have hvan : pullbackForm (id : ComplexModel n → ComplexModel n)
        (v - pullbackForm id θ₀) z = 0 :=
      h () U id htr n U id U.isOpen differentiableOn_id
        (fun y hy => ⟨hy, ⟨⟨y, hy⟩, trivial⟩, rfl⟩) z hz
    rw [pullbackForm_id, pullbackForm_id, Pi.sub_apply] at hvan
    exact sub_eq_zero.mp hvan
  · intro h i W G hG
    apply vanishesOn_of_eqOn_zero
    intro z hz
    have hzU : z ∈ U := hG.2.1 hz
    exact sub_pullbackForm_eq_zero hG.1 (domainChart_transition_eq hG) hz (h z hzU)

/-- Local smooth potentials on a domain give `θ₀`-psh functions in the sense of
complex spaces: if near every point of `U` there are a ball `B` and a smooth `g`
on `B` with `ddᶜ g = θ₀` and `g + u ∈ PSH(B)`, then `u` is `θ₀`-psh on `U` viewed
as a complex space. -/
theorem isThetaPSH_ofDomain_of_local_potentials (θ₀ : AmbientForm n 2)
    (hθ₀ : ContDiffOn ℝ ∞ θ₀ U) (u : ComplexModel n → EReal)
    (hloc : ∀ x ∈ U, ∃ B : Opens (ComplexModel n), x ∈ B ∧ B ≤ U ∧
      IsConnected (B : Set (ComplexModel n)) ∧
      ∃ g : ComplexModel n → ℝ, ContDiffOn ℝ ∞ g B ∧ (∀ z ∈ B, smoothDDC g z = θ₀ z) ∧
        Hironaka.Analytic.PotentialTheory.PSHOn (fun z => (g z : EReal) + u z) B) :
    (domainSpace U).IsThetaPSH (SpaceForm.ofDomain U θ₀ hθ₀)
      (fun p : (univ : Set U) => u p.val.val) := by
  intro x
  obtain ⟨B, hxB, hB, hBc, g, hg, hddc, hpsh⟩ := hloc x.val.val x.val.property
  refine ⟨domainSubchart U B hB, ⟨⟨⟨x.val.val, hxB⟩, trivial⟩, rfl⟩, hBc, g, hg, ?_, ?_⟩
  · intro i W G hG
    apply vanishesOn_of_eqOn_zero
    intro z hz
    have hzB : z ∈ B := hG.2.1 hz
    exact sub_pullbackForm_eq_zero hG.1 (domainSubchart_transition_eq hB hG) hz (hddc z hzB)
  · exact (SourceReducedComplexSpace.isPSH_model_univ_iff hBc
      (fun z => (g z : EReal) + u z)).mpr hpsh

/-- Pull-back of forms is additive. -/
theorem pullbackForm_sub {m N k : ℕ} (G : ComplexModel m → ComplexModel N)
    (v w : AmbientForm N k) :
    pullbackForm G (v - w) = pullbackForm G v - pullbackForm G w := by
  funext z
  ext a
  simp [pullbackForm]

/-- The chain rule for pull-backs of forms. -/
theorem pullbackForm_comp {l m N k : ℕ} {F : ComplexModel l → ComplexModel m}
    {G : ComplexModel m → ComplexModel N} {z : ComplexModel l}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G (F z)) (v : AmbientForm N k) :
    pullbackForm F (pullbackForm G v) z = pullbackForm (G ∘ F) v z := by
  simp only [pullbackForm, Function.comp_apply]
  rw [fderiv_comp z hG hF]
  ext a
  simp [Function.comp_def]

/-- Converse sanity check on a domain: a `θ₀`-psh function in the sense of
complex spaces has, near every point, a smooth local potential `ρ` of `θ₀`
(`ddᶜ ρ = θ₀`) with `ρ + u` plurisubharmonic or identically `-∞` (the disc
criterion). This is the local-potential criterion for `θ₀`-psh functions on
manifolds. -/
theorem local_potentials_of_isThetaPSH_ofDomain (θ₀ : AmbientForm n 2)
    (hθ₀ : ContDiffOn ℝ ∞ θ₀ U) (u : ComplexModel n → EReal)
    (h : (domainSpace U).IsThetaPSH (SpaceForm.ofDomain U θ₀ hθ₀)
      (fun p : (univ : Set U) => u p.val.val)) :
    ∀ x ∈ U, ∃ W : Set (ComplexModel n), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ ρ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ρ W ∧ (∀ z ∈ W, smoothDDC ρ z = θ₀ z) ∧
        Hironaka.DiscPshOn (fun z => (ρ z : EReal) + u z) W := by
  intro x hx
  let p : (univ : Set U) := ⟨⟨x, hx⟩, trivial⟩
  obtain ⟨e, hpe, -, g, hg, hres, hpsh⟩ := h p
  obtain ⟨W₁, hW₁, hxW₁, hW₁U, G', hG', hG'maps, hfac'⟩ :=
    (domainChart U).exists_contDiff_transition e p hpe
  obtain ⟨c, hcG', hcp⟩ := hfac' p hxW₁
  obtain ⟨W₂, G, hcW₂, hGtr⟩ := e.exists_isTransition (domainChart U) c ⟨p, hcp.symm⟩
  have hvan := hres () W₂ G hGtr
  obtain ⟨W₃, hW₃, hcW₃, -, ψ, hψ, hψeq⟩ :=
    SourceReducedComplexSpace.exists_ambient hpsh.2
      (LocalEmbedding.model e.ambient e.carrier e.analytic) c
  let W : Set (ComplexModel n) := W₁ ∩ G' ⁻¹' (W₂ ∩ W₃)
  have hWopen : IsOpen W := hG'.continuousOn.isOpen_inter_preimage hW₁ (hGtr.1.inter hW₃)
  have hWW₁ : W ⊆ W₁ := inter_subset_left
  have hxW : x ∈ W := by
    refine ⟨hxW₁, ?_, ?_⟩
    · rw [← hcG']
      exact hcW₂
    · change G' x ∈ W₃
      rw [← hcG']
      exact hcW₃
  -- the points of `e` over the points of `W`
  have hpt : ∀ z (hz : z ∈ W), ∃ c' : e.carrier, c'.val.val = G' z ∧
      e.toPoint c' = (⟨⟨z, hW₁U (hWW₁ hz)⟩, trivial⟩ : (univ : Set U)) := by
    intro z hz
    exact hfac' ⟨⟨z, hW₁U hz.1⟩, trivial⟩ hz.1
  have hGG' : ∀ z ∈ W, G (G' z) = z := by
    intro z hz
    obtain ⟨c', hc', hc'z⟩ := hpt z hz
    have hc'W₂ : c'.val.val ∈ W₂ := hc' ▸ hz.2.1
    obtain ⟨z', hz', hz'c'⟩ := hGtr.2.2.2.2 c' hc'W₂
    rw [LocalEmbedding.model_toPoint, hc'z] at hz'c'
    rw [← hc', ← hz', hz'c']
  have hG'diff : DifferentiableOn ℂ G' W :=
    (hG'.differentiableOn (by simp)).mono hWW₁
  refine ⟨W, hWopen, hxW, fun z hz => hW₁U hz.1, fun z => g (G' z), ?_, ?_, ?_⟩
  · exact hg.comp ((hG'.restrict_scalars ℝ).mono hWW₁) (fun z hz => hG'maps hz.1)
  · intro z hz
    have hcomp := HolomorphicDDC.smoothDDC_comp hWopen e.ambient.isOpen (hG'.mono hWW₁) hg
      (fun y hy => hG'maps hy.1) hz
    have hzero := hvan n W G' hWopen hG'diff (fun y hy => by
      obtain ⟨c', hc', -⟩ := hpt y hy
      exact ⟨hy.2.1, c', hc'⟩) z hz
    rw [pullbackForm_sub, Pi.sub_apply, sub_eq_zero] at hzero
    have hG'z : DifferentiableAt ℝ G' z :=
      (((hG'.contDiffAt (hW₁.mem_nhds hz.1)).differentiableAt (by simp)).restrictScalars ℝ)
    have hGz : DifferentiableAt ℝ G (G' z) :=
      ((hGtr.2.2.1.differentiableAt (hGtr.1.mem_nhds hz.2.1)).restrictScalars ℝ)
    rw [hcomp]
    change pullbackForm G' (smoothDDC g) z = θ₀ z
    rw [hzero]
    exact (pullbackForm_comp hG'z hGz θ₀).trans (pullbackForm_eq_of_eqOn_id hWopen hGG' θ₀ hz)
  · have hψG' : Hironaka.DiscPshOn (fun z => ψ (G' z)) W :=
      (Hironaka.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
        hWopen hG'diff (fun y hy => hy.2.2) (hψ.plurisubharmonicOn hW₃)).discPshOn
    refine hψG'.congr ?_
    intro z hz
    obtain ⟨c', hc', hc'z⟩ := hpt z hz
    have hc'W₃ : c'.val.val ∈ W₃ := hc' ▸ hz.2.2
    have := hψeq c' hc'W₃
    simp only [LocalEmbedding.model_toPoint] at this
    change ψ (G' z) = (g (G' z) : EReal) + u z
    rw [← hc', ← this, hc'z]

end Domain

end

end Hironaka.Analytic.Unibranch
