import Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingIso
import Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingStalkHS
import Hironaka.Resolution.HironakaG11InvTangentBridge
import Hironaka.Resolution.HironakaActualAnalyticSubspacePresentationIndependence

/-!
# Minimal local embeddings of a complex space (embedding dimension `HS(1) − 1`)

Lane G11B (run 0080, round 3), G11 route step 4 for the Hilbert--Samuel records (`work/hironaka-resume-20261111/G11B/
REPORT-r2.md` §6.1); blueprint `hironaka-g11-inv-local-embedding-iso.tex` (Hironaka).  Source: every germ of complex space
embeds in its Zariski tangent space, of dimension `embdim = HS(1) − 1` (Grauert--Remmert; Bierstone--Milman 1997 §1).

The Hilbert--Samuel records of G11 are not stable under products with a line, so the windows of one HS phase must have
ONE ambient dimension, the minimal one `H(1) − 1`.  For a local embedding `e` of `X` and a carrier point `c`, the flattening
`HironakaG11InvMinimalWindow.exists_flattening` straightens the carrier near `c` into `ℂ^k × 0`, `k` the dimension of the
coordinate tangent space; the first `k` coordinates then embed a neighbourhood of `c` into `ℂ^k`
(`HironakaActualAnalyticSubspacePresentationIndependence.actualSubspaceMutualRestrictionIso`).

* `firstCoords`, `padZero`: the coordinate projection `ℂ^n → ℂ^k` and the zero padding `ℂ^k → ℂ^n` (`k ≤ n`);
* **`exists_minimal_localEmbedding`**: a local embedding through `e.toPoint c`, inside the image of `e`, of ambient dimension
  `k = finrank (vanishingTangent (coordinateCarrier e.carrier) c)`, and `k + 1 = HS_{X, e.toPoint c}(1)` (the intrinsic
  `OriginalLocalEmbeddingStalkHS.originalStalkHS`, via `HironakaG11InvTangentBridge`);
* **`exists_minimal_localEmbedding_at`**: through every point `x` of `X`, inside every open neighbourhood, a local embedding
  of dimension `HS_{X,x}(1) − 1`;
* **`dim_eq_of_originalStalkHS_eq`**, **`exists_ambient_biholomorphism_of_minimal`**: two minimal local embeddings anchored
  at points with the same `HS(1)` have the same dimension, hence are ambient-biholomorphic near every common point
  (`HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism`) -- the overlap input of the Hilbert--Samuel windows.

Sorry-free.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11InvMinimalLocalEmbedding

open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
open Hironaka.HironakaActualAnalyticSubspace
open Hironaka.HironakaActualAnalyticSubspaceMaps
open Hironaka.HironakaActualAnalyticSubspacePresentationIndependence
open Hironaka.HironakaActualIntrinsicIsoPairedWindows (coordinateCarrier)
open Hironaka.HironakaG11InvAmbientIso (vanishingTangent)
open Hironaka.HironakaG11InvMinimalWindow (exists_flattening)
open Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingStalkHS (originalStalkHS originalStalkHS_localEmbedding_eq)

noncomputable section

/-! ### Coordinate projection and zero padding -/

section Coords

variable {k n : ℕ}

/-- **The first `k` coordinates** `ℂ^n → ℂ^k` (`k ≤ n`). -/
def firstCoords (hk : k ≤ n) : ComplexModel n →L[ℂ] ComplexModel k :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin k => EuclideanSpace.proj (Fin.castLE hk i))

@[simp] theorem firstCoords_apply (hk : k ≤ n) (x : ComplexModel n) (i : Fin k) :
    firstCoords hk x i = x (Fin.castLE hk i) := rfl

/-- **The zero padding** `ℂ^k → ℂ^n` (`k ≤ n`). -/
def padZero (_hk : k ≤ n) : ComplexModel k →L[ℂ] ComplexModel n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin n =>
      if h : j.val < k then EuclideanSpace.proj (⟨j.val, h⟩ : Fin k) else 0)

theorem padZero_apply (hk : k ≤ n) (y : ComplexModel k) (j : Fin n) :
    padZero hk y j = if h : j.val < k then y ⟨j.val, h⟩ else 0 := by
  show (if h : j.val < k then EuclideanSpace.proj (⟨j.val, h⟩ : Fin k) else 0) y = _
  split_ifs <;> rfl

/-- The projection undoes the padding. -/
theorem firstCoords_padZero (hk : k ≤ n) (y : ComplexModel k) : firstCoords hk (padZero hk y) = y := by
  ext i
  rw [firstCoords_apply, padZero_apply, dif_pos (show (Fin.castLE hk i).val < k from i.isLt)]
  rfl

/-- The padding undoes the projection on the points whose coordinates `j ≥ k` vanish. -/
theorem padZero_firstCoords (hk : k ≤ n) (x : ComplexModel n) (hx : ∀ j : Fin n, k ≤ j.val → x j = 0) :
    padZero hk (firstCoords hk x) = x := by
  ext j
  rw [padZero_apply]
  split_ifs with h
  · rw [firstCoords_apply]
    rfl
  · exact (hx j (not_lt.mp h)).symm

end Coords

/-! ### Holomorphic maps between open sets -/

section Opens

variable {n m : ℕ}

private theorem opens_contMDiff (A : Opens (ComplexModel n)) (f : ComplexModel n → ComplexModel m)
    (hf : ContDiffOn ℂ ∞ f A) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ (fun x : A => f x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hf.contDiffAt (A.isOpen.mem_nhds x.property)).contMDiffAt)

/-- A holomorphic map between open sets of coordinate spaces, given by a map holomorphic on the source. -/
private theorem opens_restrict_contMDiff (A : Opens (ComplexModel n)) (B : Opens (ComplexModel m))
    (f : ComplexModel n → ComplexModel m) (hf : ContDiffOn ℂ ∞ f A) (hAB : ∀ x ∈ A, f x ∈ B) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞
      (fun x : A => (⟨f x.val, hAB x.val x.property⟩ : B)) :=
  (ContMDiff.subtypeVal_comp_iff B _).mp (opens_contMDiff A f hf)

end Opens

/-! ### The minimal local embedding -/

section Minimal

variable {X : SourceReducedComplexSpace}

/-- **A minimal local embedding through a carrier point**: for a local embedding `e` of `X` and `c` in its carrier there is
a local embedding `e'` of ambient dimension `k = dim T_c` (the coordinate tangent space of the carrier at `c`), through
`e.toPoint c`, with image inside that of `e`. -/
theorem exists_minimal_localEmbedding_tangent (e : LocalEmbedding X) (c : e.carrier) :
    ∃ e' : LocalEmbedding X,
      e'.dim = Module.finrank ℂ (vanishingTangent (coordinateCarrier e.carrier) (c.val : ComplexModel e.dim)) ∧
      (∃ c' : e'.carrier, e'.toPoint c' = e.toPoint c) ∧ range e'.toPoint ⊆ range e.toPoint := by
  classical
  set S := coordinateCarrier e.carrier with hSdef
  set c₀ : ComplexModel e.dim := (c.val : ComplexModel e.dim) with hc₀def
  set k := Module.finrank ℂ (vanishingTangent S c₀) with hkdef
  have hk : k ≤ e.dim := by
    have := Submodule.finrank_le (vanishingTangent S c₀)
    rwa [finrank_euclideanSpace_fin] at this
  obtain ⟨Φ, hΦsrc, hflat⟩ := exists_flattening S e.ambient.isOpen c.val.property
  have hΦcont : ContinuousOn Φ.toFun Φ.source := Φ.toFun_holomorphic.continuousOn
  have hinvcont : ContinuousOn Φ.invFun Φ.target := Φ.invFun_holomorphic.continuousOn
  -- the maps
  let P : ComplexModel e.dim → ComplexModel k := fun x => firstCoords hk (Φ.toFun x)
  let Sg : ComplexModel k → ComplexModel e.dim := fun y => Φ.invFun (padZero hk y)
  let g : ComplexModel e.dim → ComplexModel e.dim := fun x => padZero hk (P x)
  have hgcont : ContinuousOn g Φ.source :=
    ((padZero hk).continuous.comp (firstCoords hk).continuous).comp_continuousOn hΦcont
  -- the source open `T`
  let T₁ : Set (ComplexModel e.dim) := Φ.source ∩ g ⁻¹' Φ.target
  have hT₁ : IsOpen T₁ := hgcont.isOpen_inter_preimage Φ.isOpen_source Φ.isOpen_target
  let Tset : Set (ComplexModel e.dim) := T₁ ∩ (fun x => Φ.invFun (g x)) ⁻¹' Φ.source
  have hTopen : IsOpen Tset :=
    (hinvcont.comp (hgcont.mono inter_subset_left) (fun x hx => hx.2)).isOpen_inter_preimage hT₁ Φ.isOpen_source
  let T : Opens (ComplexModel e.dim) := ⟨Tset, hTopen⟩
  have hT : T ≤ e.ambient := fun x hx => hΦsrc hx.1.1
  -- the target open `Ω'`
  let O₁ : Set (ComplexModel k) := padZero hk ⁻¹' Φ.target
  have hO₁ : IsOpen O₁ := Φ.isOpen_target.preimage (padZero hk).continuous
  let Oset : Set (ComplexModel k) := O₁ ∩ Sg ⁻¹' Φ.source
  have hOopen : IsOpen Oset :=
    (hinvcont.comp (padZero hk).continuous.continuousOn (fun y hy => hy)).isOpen_inter_preimage hO₁
      Φ.isOpen_source
  let Ω' : Opens (ComplexModel k) := ⟨Oset, hOopen⟩
  -- identities
  have hgS : ∀ x ∈ Φ.source, x ∈ S → g x = Φ.toFun x := fun x hx hxS =>
    padZero_firstCoords hk _ (fun j hj => hflat x hx hxS j hj)
  have hPSg : ∀ y ∈ O₁, P (Sg y) = y := fun y hy => by
    show firstCoords hk (Φ.toFun (Φ.invFun (padZero hk y))) = y
    rw [Φ.right_inv _ hy, firstCoords_padZero]
  have hSgT : ∀ y ∈ Oset, Sg y ∈ Tset := fun y hy => by
    have hg : g (Sg y) = padZero hk y := by
      show padZero hk (P (Sg y)) = padZero hk y
      rw [hPSg y hy.1]
    refine ⟨⟨hy.2, ?_⟩, ?_⟩
    · show g (Sg y) ∈ Φ.target
      rw [hg]; exact hy.1
    · show Φ.invFun (g (Sg y)) ∈ Φ.source
      rw [hg]; exact hy.2
  have hPO : ∀ x ∈ Tset, P x ∈ Oset := fun x hx => ⟨hx.1.2, hx.2⟩
  have hSgP : ∀ x ∈ Tset, x ∈ S → Sg (P x) = x := fun x hx hxS => by
    show Φ.invFun (g x) = x
    rw [hgS x hx.1.1 hxS, Φ.left_inv x hx.1.1]
  -- smoothness
  have hPsmooth : ContDiffOn ℂ ∞ P T := by
    have h1 : ContDiffOn ℂ ∞ Φ.toFun Φ.source :=
      contDiffOn_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
    exact ((firstCoords hk).contDiff.comp_contDiffOn h1).mono (fun x hx => hx.1.1)
  have hSgsmooth : ContDiffOn ℂ ∞ Sg Ω' := by
    have h1 : ContDiffOn ℂ ∞ Φ.invFun Φ.target :=
      contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target
    exact (h1.comp (padZero hk).contDiff.contDiffOn (fun y hy => hy)).mono (fun y hy => hy.1)
  let p : T → Ω' := fun x => ⟨P x.val, hPO x.val x.property⟩
  let σ : Ω' → T := fun y => ⟨Sg y.val, hSgT y.val y.property⟩
  have hp : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel k) ∞ p :=
    opens_restrict_contMDiff T Ω' P hPsmooth hPO
  have hσ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel e.dim) ∞ σ :=
    opens_restrict_contMDiff Ω' T Sg hSgsmooth hSgT
  -- carriers
  let CT : Set T := e.restrictCarrier T hT
  let C' : Set Ω' := (Opens.inclusion hT ∘ σ) ⁻¹' e.carrier
  have hC' : IsComplexAnalyticSubset (n := k) C' :=
    Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      ((contMDiff_inclusion hT).comp hσ) e.analytic
  have hmemS : ∀ z ∈ CT, (z : ComplexModel e.dim) ∈ S := fun z hz =>
    ⟨Opens.inclusion hT z, hz, rfl⟩
  have hσp : ∀ z ∈ CT, σ (p z) = z := fun z hz =>
    Subtype.ext (hSgP z.val z.property (hmemS z hz))
  have hpσ : ∀ y ∈ C', p (σ y) = y := fun y _ => Subtype.ext (hPSg y.val y.property.1)
  have hCD : ∀ z ∈ CT, p z ∈ C' := fun z hz => by
    show Opens.inclusion hT (σ (p z)) ∈ e.carrier
    rw [hσp z hz]; exact hz
  have hDC : ∀ y ∈ C', σ y ∈ CT := fun y hy => hy
  let iso := actualSubspaceMutualRestrictionIso hp hσ hCD hDC hσp hpσ
  let eT := e.restrict T hT
  let e' : LocalEmbedding X :=
    { dim := k
      ambient := Ω'
      carrier := C'
      analytic := hC'
      map := iso.inv ≫ eT.map
      isOpenImmersion := by
        let := eT.isOpenImmersion
        infer_instance
      overPoint := by
        rw [Category.assoc, eT.overPoint]
        exact actualSubspaceMap_point hσ hDC }
  -- the anchor point
  have hc₀S : c₀ ∈ S := ⟨c.val, c.property, rfl⟩
  have hc₀T : c₀ ∈ Tset := by
    have hsrc := Φ.center_mem_source
    have hg : g c₀ = Φ.toFun c₀ := hgS c₀ hsrc hc₀S
    refine ⟨⟨hsrc, ?_⟩, ?_⟩
    · show g c₀ ∈ Φ.target
      rw [hg]; exact Φ.mapsTo_toFun hsrc
    · show Φ.invFun (g c₀) ∈ Φ.source
      rw [hg, Φ.left_inv c₀ hsrc]; exact hsrc
  let cT : T := ⟨c₀, hc₀T⟩
  have hcT : cT ∈ CT := by
    show Opens.inclusion hT cT ∈ e.carrier
    have : Opens.inclusion hT cT = c.val := Subtype.ext rfl
    rw [this]; exact c.property
  have hpoint : ∀ y : C', e'.toPoint y = e.toPoint ⟨Opens.inclusion hT (σ y.val), y.property⟩ := fun _ => rfl
  refine ⟨e', rfl, ⟨⟨p cT, hCD cT hcT⟩, ?_⟩, ?_⟩
  · have key : ((σ (p cT)) : ComplexModel e.dim) = c₀ := congrArg Subtype.val (hσp cT hcT)
    rw [hpoint]
    exact congrArg e.toPoint (Subtype.ext (Subtype.ext key))
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, (hpoint y).symm⟩

/-- **The minimal local embedding has dimension `HS(1) − 1`** (intrinsic Hilbert--Samuel function of `X` at the point). -/
theorem exists_minimal_localEmbedding (e : LocalEmbedding X) (c : e.carrier) :
    ∃ e' : LocalEmbedding X, e'.dim + 1 = originalStalkHS X (e.toPoint c) 1 ∧
      (∃ c' : e'.carrier, e'.toPoint c' = e.toPoint c) ∧ range e'.toPoint ⊆ range e.toPoint := by
  obtain ⟨e', hdim, hpt, hrange⟩ := exists_minimal_localEmbedding_tangent e c
  refine ⟨e', ?_, hpt, hrange⟩
  rw [hdim, originalStalkHS_localEmbedding_eq X e c 1]
  exact Hironaka.HironakaG11InvTangentBridge.finrank_vanishingTangent_add_one_eq_hilbertSamuel
    e.analytic c.property

/-- **Minimal local embeddings exist everywhere**: through every point `x` of `X`, with image inside any open neighbourhood
of `x`, there is a local embedding of ambient dimension `HS_{X,x}(1) − 1`. -/
theorem exists_minimal_localEmbedding_at (x : X.obj.left) {N : Set X.obj.left} (hN : IsOpen N) (hx : x ∈ N) :
    ∃ e' : LocalEmbedding X, e'.dim + 1 = originalStalkHS X x 1 ∧ x ∈ range e'.toPoint ∧ range e'.toPoint ⊆ N := by
  obtain ⟨e, ⟨c, hc⟩, hrange, -⟩ := LocalEmbedding.exists_domain x hN hx
  obtain ⟨e', hdim, ⟨c', hc'⟩, hrange'⟩ := exists_minimal_localEmbedding e c
  rw [hc] at hdim hc'
  exact ⟨e', hdim, ⟨c', hc'⟩, hrange'.trans hrange⟩

/-- **Minimal local embeddings anchored at points with the same `HS(1)` have the same dimension.** -/
theorem dim_eq_of_originalStalkHS_eq (e₁ e₂ : LocalEmbedding X) {a₁ a₂ : X.obj.left}
    (h₁ : e₁.dim + 1 = originalStalkHS X a₁ 1) (h₂ : e₂.dim + 1 = originalStalkHS X a₂ 1)
    (h : originalStalkHS X a₁ 1 = originalStalkHS X a₂ 1) : e₁.dim = e₂.dim := by
  omega

/-- **Two minimal local embeddings anchored on one Hilbert--Samuel level are ambient-biholomorphic near every common
point** (compatibly with the maps to `X`): the overlap geometry of the Hilbert--Samuel windows of one phase. -/
theorem exists_ambient_biholomorphism_of_minimal (e₁ e₂ : LocalEmbedding X) {a₁ a₂ : X.obj.left}
    (h₁ : e₁.dim + 1 = originalStalkHS X a₁ 1) (h₂ : e₂.dim + 1 = originalStalkHS X a₂ 1)
    (h : originalStalkHS X a₁ 1 = originalStalkHS X a₂ 1)
    (c₁ : e₁.carrier) (c₂ : e₂.carrier) (hc : e₁.toPoint c₁ = e₂.toPoint c₂) :
    ∃ (A : Opens (ComplexModel e₁.dim)) (B : Opens (ComplexModel e₂.dim))
      (_ : A ≤ e₁.ambient) (_ : B ≤ e₂.ambient)
      (Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel e₁.dim), 𝓘(ℂ, ComplexModel e₂.dim)⟯ B) (hc₁ : c₁.val.val ∈ A),
      (Φ ⟨c₁.val.val, hc₁⟩ : ComplexModel e₂.dim) = c₂.val.val ∧
      (∀ x : A, (x : ComplexModel e₁.dim) ∈ coordinateCarrier e₁.carrier ↔
        (Φ x : ComplexModel e₂.dim) ∈ coordinateCarrier e₂.carrier) ∧
      ∀ (y : e₁.carrier) (hy : y.val.val ∈ A), ∃ z : e₂.carrier,
        z.val.val = (Φ ⟨y.val.val, hy⟩ : ComplexModel e₂.dim) ∧ e₂.toPoint z = e₁.toPoint y :=
  HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism e₁ e₂
    (dim_eq_of_originalStalkHS_eq e₁ e₂ h₁ h₂ h) c₁ c₂ hc

end Minimal

end

end Hironaka.Analytic.Unibranch.HironakaG11InvMinimalLocalEmbedding
