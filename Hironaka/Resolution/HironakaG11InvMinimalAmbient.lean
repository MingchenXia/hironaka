import Hironaka.Resolution.HironakaG11InvTransport
import Hironaka.Resolution.HironakaActualIntrinsicIsoPairedWindows
import Hironaka.Resolution.HironakaCurrentEmbeddingDimension
import Hironaka.Manifold.LocalHolomorphicInverse

/-!
# Two minimal embeddings of the same germ are ambient-biholomorphic

Lane G11B (run 0080, round 2), G11 route step 4 (`work/hironaka-resume-20261111/G11B/ROUTE-r1.md` §3, `ROUTE-r2.md`);
blueprint `hironaka-g11-inv-minimal-ambient.tex`.  Sources: the classical uniqueness of minimal embeddings of a germ of
complex space (Grauert--Remmert, *Coherent analytic sheaves*, and Bierstone--Milman 1997 §1: the class of a presentation
"depends only on the local isomorphism class of `M, X, E(a)`"); Włodarczyk 2009 (the vanishing-ideal record).

Let `C ⊆ U ⊆ ℂⁿ` and `D ⊆ V ⊆ ℂⁿ` be analytic local models (same ambient dimension `n`) with an intrinsic isomorphism
`e : C ≅ D` of the reduced complex spaces, and let `c ∈ C` be a point where the embedding is MINIMAL: the embedding dimension
of `C` at `c` is `n`, i.e. every holomorphic germ vanishing on `C` has zero differential at `c` (equivalently, by
`HironakaHilbertSamuelTangentValue.hilbertSamuelAt_vanishing_one_eq_embeddingDimension_add_one`, `HS_c(1) = n + 1`).

## Main results

* `fderiv_eq_zero_of_embeddingDimension_eq`: at a minimal point, every holomorphic function vanishing on the carrier near
  the point has zero differential there;
* **`exists_minimal_ambient_biholomorphism`**: a coordinate representative `F` of `e` (from
  `HironakaActualIntrinsicIsoPairedWindows.exists_actual_intrinsic_iso_paired_windows`) is a biholomorphism `Φ : A ≅ B` of
  open neighbourhoods of `c` and `e(c)` carrying `C ∩ A` exactly onto `D ∩ B` and extending `e` (its differential at `c`
  is injective since `G ∘ F = id` on `C` and `C` is minimal at `c`; inverse function theorem);
* **`exists_minimal_vanishing_windows`**: the same as windows of the two models, in the form consumed by
  `HironakaG11InvTransport.inv_vanishingRecord_eq_on_overlap` (values of the canonical invariants of the vanishing-ideal
  records agree on the overlap along corresponding towers);
* **`inv_vanishingRecord_refl_eq_of_minimal`**: for every route invariant (e.g. `CanonicalCentres.canonicalInvariant n`),
  the values of the vanishing-ideal records at the first stage are intrinsic near a minimal point:
  `inv (𝓘_D, 1) (e y) = inv (𝓘_C, 1) y` for `y ∈ C` near `c`.

Import discipline (Hironaka phase): this module does not import, even transitively, `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`, and uses no pluripotential / Kähler constant.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11InvMinimalAmbient

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerIsomorphism ResolutionInvariantSeq
open ResolutionInvariantSpec (IsInvDomain)
open HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces HironakaActualIntrinsicIsoPairedWindows
open RankDegeneracy HironakaCurrentEmbeddingDimension HironakaG11InvTransport

noncomputable section

variable {n : ℕ}

/-! ### Minimality in coordinates -/

section Minimal

variable {U : Opens (ComplexModel n)}

/-- A point of an open of `ℂⁿ` lies in the coordinate carrier of `C` iff it lies in `C`. -/
theorem val_mem_coordinateCarrier_iff (C : Set U) (x : U) : x.val ∈ coordinateCarrier C ↔ x ∈ C := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- **At a minimal point, functions vanishing on the carrier have zero differential**: if the embedding dimension of
`C ⊆ U` at `c` is `n`, every function holomorphic near `c` and vanishing on the carrier near `c` has zero differential at
`c` (the tangent space `tangentSpaceIn` of the vanishing ideal is everything). -/
theorem fderiv_eq_zero_of_embeddingDimension_eq {C : Set U} {c : U}
    (hmin : embeddingDimension (n := n) C c = n) {h : ComplexModel n → ℂ}
    (hh : ∀ᶠ x in 𝓝 (c : ComplexModel n), DifferentiableAt ℂ h x)
    (hzero : ∀ᶠ x in 𝓝 (c : ComplexModel n), x ∈ coordinateCarrier C → h x = 0) :
    fderiv ℂ h c = 0 := by
  have htop : tangentSpaceIn (complexChartAt (n := n) c) C c = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 : Module.finrank ℂ (tangentSpaceIn (complexChartAt (n := n) c) C c) = n := hmin
    rw [h1]
    simp
  let g : U → ℂ := fun u => h u.val
  have hcont : Tendsto (Subtype.val : U → ComplexModel n) (𝓝 c) (𝓝 (c : ComplexModel n)) :=
    continuous_subtype_val.continuousAt
  have hg : (vanishingIdeal (n := n) C).mem c g := by
    refine ⟨?_, ?_⟩
    · filter_upwards [hcont.eventually hh] with y hy
      exact hy.mdifferentiableAt.comp y
        ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    · filter_upwards [hcont.eventually hzero] with y hy hyC
      exact hy ⟨y, hyC, rfl⟩
  ext v
  have hv : v ∈ tangentSpaceIn (complexChartAt (n := n) c) C c := by rw [htop]; exact Submodule.mem_top
  have hv' := (mem_tangentSpaceIn.mp hv) g hg
  -- the chart of `U` at `c` is the identity, restricted
  let e := complexChartAt (n := n) c
  have hec : e.val c = (c : ComplexModel n) := rfl
  have hloc : (fun w => g (e.val.symm w)) =ᶠ[𝓝 (c : ComplexModel n)] h := by
    have hmem : e.val.target ∈ 𝓝 (c : ComplexModel n) := by
      rw [← hec]; exact e.val.open_target.mem_nhds (e.val.map_source (mem_complexChartAt_source c))
    filter_upwards [hmem] with w hw
    have hsymm : ((e.val.symm w : U) : ComplexModel n) = w := by
      have := (chartAt (ComplexModel n) (c : ComplexModel n)).subtypeRestr_symm_apply ⟨c⟩ hw
      exact this
    show h ((e.val.symm w : U) : ComplexModel n) = h w
    rw [hsymm]
  rw [hec, hloc.fderiv_eq] at hv'
  simpa using hv'

end Minimal

/-! ### The ambient biholomorphism -/

section Ambient

variable {U V : Opens (ComplexModel n)} {C : Set U} {D : Set V}

private theorem vector_contMDiff (A : Opens (ComplexModel n)) (f : ComplexModel n → ComplexModel n)
    (hf : ContDiffOn ℂ ∞ f A) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun x : A => f x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hf.contDiffAt (A.isOpen.mem_nhds x.property)).contMDiffAt)

/-- **Two minimal embeddings of the same germ are ambient-biholomorphic** (same ambient dimension `n`): for an intrinsic
isomorphism `e : C ≅ D` of analytic local models `C ⊆ U ⊆ ℂⁿ`, `D ⊆ V ⊆ ℂⁿ` and a point `c ∈ C` where the embedding
dimension of `C` is `n`, there are open neighbourhoods `A ⊆ U` of `c` and `B ⊆ V` of `e(c)` and a biholomorphism
`Φ : A ≅ B` carrying `C ∩ A` exactly onto `D ∩ B` and extending `e`. -/
theorem exists_minimal_ambient_biholomorphism
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := n) D)
    (he : e.hom ≫ subspacePointMap (n := n) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (c : C)
    (hmin : embeddingDimension (n := n) C c.val = n) :
    ∃ (A B : Opens (ComplexModel n)) (_ : A ≤ U) (_ : B ≤ V)
      (Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B),
      c.val.val ∈ A ∧
      (∀ x : A, (x : ComplexModel n) ∈ coordinateCarrier C ↔ (Φ x : ComplexModel n) ∈ coordinateCarrier D) ∧
      ∀ (y : C) (hy : y.val.val ∈ A), (Φ ⟨y.val.val, hy⟩ : ComplexModel n) = (e.hom.base y).val.val := by
  obtain ⟨A₀, B₀, F, G, hAU, hBV, hcA, _hdB, hF, hG, _ha, _hb, hFD, hGC, hgf, hfg, hFval, _hGval⟩ :=
    exists_actual_intrinsic_iso_paired_windows e he hC hD c
  set c₀ : ComplexModel n := c.val.val with hc₀
  have hFdiff : ∀ x ∈ (A₀ : Set (ComplexModel n)), DifferentiableAt ℂ F x := fun x hx =>
    (hF.contDiffAt (A₀.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hGdiff : ∀ y ∈ (B₀ : Set (ComplexModel n)), DifferentiableAt ℂ G y := fun y hy =>
    (hG.contDiffAt (B₀.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hc₀C : c₀ ∈ coordinateCarrier C ∩ A₀ := ⟨⟨c.val, c.property, rfl⟩, hcA⟩
  have hFc₀ : F c₀ ∈ (B₀ : Set (ComplexModel n)) := (hFD c₀ hc₀C).2
  -- the open `A₀ ∩ F⁻¹ B₀` around `c₀`
  have hOpen₁ : IsOpen ((A₀ : Set (ComplexModel n)) ∩ F ⁻¹' B₀) :=
    hF.continuousOn.isOpen_inter_preimage A₀.isOpen B₀.isOpen
  have hN₁ : (A₀ : Set (ComplexModel n)) ∩ F ⁻¹' B₀ ∈ 𝓝 c₀ := hOpen₁.mem_nhds ⟨hcA, hFc₀⟩
  -- the differential of `F` at `c₀` is injective
  have hinj : Function.Injective (fderiv ℂ F c₀) := by
    refine (injective_iff_map_eq_zero (fderiv ℂ F c₀)).mpr fun v hv' => ?_
    have hcoord : ∀ i : Fin n, v i = 0 := by
      intro i
      let ℓ : ComplexModel n →L[ℂ] ℂ := EuclideanSpace.proj i
      let h : ComplexModel n → ℂ := fun x => ℓ (G (F x)) - ℓ x
      have hHas : HasFDerivAt h (ℓ.comp ((fderiv ℂ G (F c₀)).comp (fderiv ℂ F c₀)) - ℓ) c₀ :=
        (ℓ.hasFDerivAt.comp c₀ (((hGdiff _ hFc₀).hasFDerivAt).comp c₀
          (hFdiff c₀ hcA).hasFDerivAt)).sub ℓ.hasFDerivAt
      have hzero : fderiv ℂ h c₀ = 0 := by
        apply fderiv_eq_zero_of_embeddingDimension_eq (C := C) (c := c.val) hmin
        · filter_upwards [hN₁] with x hx
          exact (ℓ.differentiableAt.comp x ((hGdiff _ hx.2).comp x (hFdiff x hx.1))).sub
            ℓ.differentiableAt
        · filter_upwards [A₀.isOpen.mem_nhds hcA] with x hx hxC
          show ℓ (G (F x)) - ℓ x = 0
          rw [hgf x ⟨hxC, hx⟩, sub_self]
      have happ := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) (hHas.fderiv.symm.trans hzero)
      simp only [sub_apply, ContinuousLinearMap.comp_apply, hv', map_zero,
        zero_apply, zero_sub, neg_eq_zero] at happ
      simpa [ℓ] using happ
    ext i
    simpa using hcoord i
  -- inverse function theorem
  obtain ⟨Φ₀, hΦsrc, hΦF, -⟩ :=
    exists_localHolomorphicEquivAt A₀.isOpen hcA (hF.differentiableOn (by simp)) hinj
  have hFinv : ∀ w ∈ Φ₀.target, F (Φ₀.invFun w) = w := fun w hw => by
    rw [← hΦF]; exact Φ₀.right_inv w hw
  have hinvF : ∀ x ∈ Φ₀.source, Φ₀.invFun (F x) = x := fun x hx => by
    rw [← hΦF]; exact Φ₀.left_inv x hx
  have hFtarget : ∀ x ∈ Φ₀.source, F x ∈ Φ₀.target := fun x hx => by
    rw [← hΦF]; exact Φ₀.mapsTo_toFun hx
  -- the target window `B` and the source window `A`
  let Wset : Set (ComplexModel n) := ((B₀ : Set (ComplexModel n)) ∩ G ⁻¹' Φ₀.source) ∩ Φ₀.target
  have hWopen : IsOpen Wset :=
    (hG.continuousOn.isOpen_inter_preimage B₀.isOpen Φ₀.isOpen_source).inter Φ₀.isOpen_target
  let B : Opens (ComplexModel n) := ⟨Wset, hWopen⟩
  have hFcont : ContinuousOn F Φ₀.source := hF.continuousOn.mono hΦsrc
  let Aset : Set (ComplexModel n) := Φ₀.source ∩ F ⁻¹' Wset
  have hAopen : IsOpen Aset := hFcont.isOpen_inter_preimage Φ₀.isOpen_source hWopen
  let A : Opens (ComplexModel n) := ⟨Aset, hAopen⟩
  have hAA₀ : A ≤ A₀ := fun x hx => hΦsrc hx.1
  have hBB₀ : B ≤ B₀ := fun y hy => hy.1.1
  have hcAset : c₀ ∈ A := by
    refine ⟨Φ₀.center_mem_source, ⟨hFc₀, ?_⟩, hFtarget c₀ Φ₀.center_mem_source⟩
    show G (F c₀) ∈ Φ₀.source
    rw [hgf c₀ hc₀C]; exact Φ₀.center_mem_source
  have hinvA : ∀ y ∈ Wset, Φ₀.invFun y ∈ Aset := fun y hy =>
    ⟨Φ₀.mapsTo_invFun hy.2, by show F (Φ₀.invFun y) ∈ Wset; rw [hFinv y hy.2]; exact hy⟩
  have hFsmooth : ContDiffOn ℂ ∞ F A := hF.mono (fun x hx => hAA₀ hx)
  have hinvSmooth : ContDiffOn ℂ ∞ Φ₀.invFun B :=
    (contDiffOn_of_differentiableOn_complex Φ₀.invFun_holomorphic Φ₀.isOpen_target).mono
      (fun y hy => hy.2)
  let Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B :=
    { toFun := fun x => ⟨F x.val, x.property.2⟩
      invFun := fun y => ⟨Φ₀.invFun y.val, hinvA y.val y.property⟩
      left_inv := fun x => Subtype.ext (hinvF x.val x.property.1)
      right_inv := fun y => Subtype.ext (hFinv y.val y.property.2)
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff B _).mp (vector_contMDiff A F hFsmooth)
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff A _).mp (vector_contMDiff B Φ₀.invFun hinvSmooth) }
  refine ⟨A, B, fun x hx => hAU (hAA₀ hx), fun y hy => hBV (hBB₀ hy), Φ, hcAset, ?_, ?_⟩
  · intro x
    change (x : ComplexModel n) ∈ coordinateCarrier C ↔ F x ∈ coordinateCarrier D
    have hxA₀ : (x : ComplexModel n) ∈ A₀ := hAA₀ x.property
    constructor
    · intro hxC
      exact (hFD x ⟨hxC, hxA₀⟩).1
    · intro hFxD
      have hy : F x ∈ coordinateCarrier D ∩ B₀ := ⟨hFxD, x.property.2.1.1⟩
      have hGy := hGC (F x) hy
      have hGsrc : G (F x) ∈ Φ₀.source := x.property.2.1.2
      have heq : G (F x) = (x : ComplexModel n) := by
        have h1 := hinvF (G (F x)) hGsrc
        rw [hfg (F x) hy] at h1
        rw [← h1, hinvF x x.property.1]
      exact heq ▸ hGy.1
  · intro y hy
    exact hFval y (hAA₀ hy)

end Ambient

/-! ### Windows of the two models and the vanishing-ideal records -/

section Windows

open MaxLocusLocal (nestedOpens nestedOpensDiffeo)

variable {U V : Opens (ComplexModel n)} {C : Set U} {D : Set V}

/-- **The minimal windows of two local models of the same germ**, in the form consumed by the transport results of
`HironakaG11InvTransport`: opens `A ∋ c` of `U` and `B ∋ e(c)` of `V`, seen as windows `A ⊆ U`, `B ⊆ V` of the two ambient
manifolds, and a biholomorphism `Ψ : B ≅ A` of the windows carrying `D` to `C` exactly and `e(y)` to `y` for `y ∈ C ∩ A`. -/
theorem exists_minimal_vanishing_windows
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := n) D)
    (he : e.hom ≫ subspacePointMap (n := n) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (c : C)
    (hmin : embeddingDimension (n := n) C c.val = n) :
    ∃ (A B : Opens (ComplexModel n)) (_ : A ≤ U) (_ : B ≤ V)
      (Ψ : CMfd.of (n := n) (nestedOpens V B) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (nestedOpens U A)),
      c.val.val ∈ A ∧
      (∀ p : nestedOpens V B, ((Ψ p : nestedOpens U A) : U) ∈ C ↔ (p : V) ∈ D) ∧
      ∀ (y : C), y.val.val ∈ A →
        ∃ p : nestedOpens V B, (p : V) = (e.hom.base y).val ∧ ((Ψ p : nestedOpens U A) : U) = y.val := by
  obtain ⟨A, B, hAU, hBV, Φ, hcA, hCD, hval⟩ := exists_minimal_ambient_biholomorphism e he hC hD c hmin
  let Ψ : CMfd.of (n := n) (nestedOpens V B) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens U A) :=
    (nestedOpensDiffeo (n := n) hBV).trans (Φ.symm.trans (nestedOpensDiffeo (n := n) hAU).symm)
  have hΨ : ∀ p : nestedOpens V B, (((Ψ p : nestedOpens U A) : U) : ComplexModel n) =
      (Φ.symm ⟨((p : V) : ComplexModel n), p.property⟩ : ComplexModel n) := fun _ => rfl
  refine ⟨A, B, hAU, hBV, Ψ, hcA, fun p => ?_, fun y hy => ?_⟩
  · rw [← val_mem_coordinateCarrier_iff C, hΨ, ← val_mem_coordinateCarrier_iff D]
    rw [hCD (Φ.symm ⟨((p : V) : ComplexModel n), p.property⟩), Φ.apply_symm_apply]
  · have hB : (e.hom.base y).val.val ∈ B := by
      rw [← hval y hy]; exact (Φ ⟨y.val.val, hy⟩).property
    refine ⟨⟨(e.hom.base y).val, hB⟩, rfl, Subtype.ext ?_⟩
    rw [hΨ]
    have h1 : (⟨((e.hom.base y).val : ComplexModel n), hB⟩ : B) = Φ ⟨y.val.val, hy⟩ :=
      Subtype.ext (hval y hy).symm
    simp only [h1, Φ.symm_apply_apply]

/-- **The first-stage values of the vanishing-ideal records are intrinsic near a minimal point**: for every route invariant
`R` (e.g. `CanonicalCentres.canonicalInvariant n`), an intrinsic isomorphism `e : C ≅ D` of analytic local models in the same
ambient dimension and a point `c` where `C` is minimally embedded, the values of `R` on the vanishing-ideal records
`(univ, [], 𝓘_C, 1)` and `(univ, [], 𝓘_D, 1)` at the first stage satisfy `inv (𝓘_D, 1) (e y) = inv (𝓘_C, 1) y` for every `y ∈ C`
in a neighbourhood of `c` (`inv_vanishingRecord_eq_on_overlap` along the windows of `exists_minimal_vanishing_windows`). -/
theorem inv_vanishingRecord_refl_eq_of_minimal {k : ℕ} {Λ : Type*} [LinearOrder Λ]
    (R : ResolutionInvariant n k Λ)
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := n) D)
    (he : e.hom ≫ subspacePointMap (n := n) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (c : C)
    (hmin : embeddingDimension (n := n) C c.val = n)
    (hDomC : IsInvDomain k (vanishingRecord n (M := CMfd.of (n := n) U) C))
    (hDomD : IsInvDomain k (vanishingRecord n (M := CMfd.of (n := n) V) D)) :
    ∃ A : Opens (ComplexModel n), c.val.val ∈ A ∧ ∀ y : C, y.val.val ∈ A →
      R.inv (X := CMfd.of (n := n) V) (vanishingRecord n D) BlowupTower.refl (e.hom.base y).val =
        R.inv (X := CMfd.of (n := n) U) (vanishingRecord n C) BlowupTower.refl y.val := by
  obtain ⟨A, B, hAU, hBV, Ψ, hcA, hCD, hpts⟩ := exists_minimal_vanishing_windows e he hC hD c hmin
  refine ⟨A, hcA, fun y hy => ?_⟩
  obtain ⟨p, hp, hΨp⟩ := hpts y hy
  have hcos : (vanishingRecord n (M := CMfd.of (n := n) U) C).cosupp = C :=
    SmoothCentreLocus.cosupp_vanishingIdeal hC.isClosed (subset_univ _)
  have hyC : ((Ψ p : nestedOpens U A) : U) ∈ (vanishingRecord n (M := CMfd.of (n := n) U) C).cosupp := by
    rw [hcos, hΨp]; exact y.property
  have h := (inv_vanishingRecord_eq_on_overlap R hDomC hDomD (nestedOpens U A) (nestedOpens V B) Ψ hCD
    (T' := .refl) (T := .refl) trivial trivial (χ := Ψ) IsTowerIso.refl p hyC).2
  rw [← hp, ← hΨp]
  exact h

end Windows

end

end Hironaka.HironakaG11InvMinimalAmbient
