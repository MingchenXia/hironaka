import Hironaka.Resolution.HironakaG11InvMinimalAmbient

/-!
# Two embeddings of the same germ in the same ambient dimension are ambient-biholomorphic

Lane G11B (run 0080, round 2), G11 route steps 3--4 (`work/hironaka-resume-20261111/G11B/ROUTE-r2.md`); blueprint
`hironaka-g11-inv-ambient-iso.tex`.  Sources: the classical uniqueness of embeddings of a germ of complex space of the same
ambient dimension up to ambient automorphism (Grauert--Remmert, *Coherent analytic sheaves*, Ch. 2--3); Bierstone--Milman
1997 §1 (the presentation depends only on the local isomorphism class of `M, X`).

This generalizes `HironakaG11InvMinimalAmbient` (minimal embeddings) to ARBITRARY embeddings of the same dimension.  Let
`C ⊆ U ⊆ ℂⁿ`, `D ⊆ V ⊆ ℂⁿ` be analytic local models with an intrinsic isomorphism `e : C ≅ D`, `c ∈ C`, and let `F`, `G`
be coordinate representatives of `e`, `e⁻¹` (`G ∘ F = id` on `C`).  The differential of `F` at `c` is injective on the
coordinate tangent space `T` of `C` at `c` (the common kernel of the differentials of the functions vanishing on `C`), but not
in general on `ℂⁿ`.  Correct it by a map vanishing on `C`: extend `dF_c|_T` to a linear automorphism `M` of `ℂⁿ`; every
coordinate of `M - dF_c` vanishes on `T`, hence (finite dimension) is the differential of a function vanishing on `C`
(`Subspace.dualCoannihilator_dualAnnihilator_eq`); so `F' = F + H` with `H|_C = 0` and `dF'_c = M` is invertible, and
`F'` still represents `e`.  The inverse function theorem and a shrinking finish.

## Main results

* `IsVanishingNear`, `vanishingDifferentials`, `vanishingTangent`: the functions vanishing on a set near a point, their
  differentials (a subspace of the dual) and the coordinate tangent space;
* `exists_vanishing_correction`: a linear map injective on the tangent space becomes injective after adding the
  differential of a map vanishing on the set;
* `exists_biholomorphism_of_local_inverse`: local inverse data with injective differential give a biholomorphism of
  neighbourhoods carrying one set exactly onto the other;
* **`exists_ambient_biholomorphism`**: for an intrinsic isomorphism `e : C ≅ D` of analytic local models in the same ambient
  dimension and any `c ∈ C`, a biholomorphism `Φ : A ≅ B` of neighbourhoods of `c`, `e(c)` with `Φ(C ∩ A) = D ∩ B` and
  `Φ|_{C ∩ A} = e`;
* **`exists_vanishing_windows`**, **`inv_vanishingRecord_refl_eq`**: the same as windows of the two ambient manifolds, and
  the first-stage values of the vanishing-ideal records of every route invariant are intrinsic near every point.

Import discipline (Hironaka phase): this module does not import, even transitively, `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`, and uses no pluripotential / Kähler constant.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11InvAmbientIso

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerIsomorphism ResolutionInvariantSeq
open ResolutionInvariantSpec (IsInvDomain)
open HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces HironakaActualIntrinsicIsoPairedWindows
open HironakaG11InvTransport HironakaG11InvMinimalAmbient

noncomputable section

variable {n : ℕ}

/-! ### Functions vanishing near a point, their differentials and the tangent space -/

section Tangent

variable (S : Set (ComplexModel n)) (c₀ : ComplexModel n)

/-- `h` is holomorphic near `c₀` and vanishes on `S` near `c₀`. -/
def IsVanishingNear (h : ComplexModel n → ℂ) : Prop :=
  (∀ᶠ x in 𝓝 c₀, DifferentiableAt ℂ h x) ∧ ∀ᶠ x in 𝓝 c₀, x ∈ S → h x = 0

/-- **The differentials at `c₀` of the functions vanishing on `S` near `c₀`**, a subspace of the dual of `ℂⁿ`. -/
def vanishingDifferentials : Submodule ℂ (Module.Dual ℂ (ComplexModel n)) where
  carrier := {φ | ∃ h, IsVanishingNear S c₀ h ∧ ∀ v, fderiv ℂ h c₀ v = φ v}
  add_mem' := by
    rintro φ₁ φ₂ ⟨h₁, ⟨hd₁, hz₁⟩, hφ₁⟩ ⟨h₂, ⟨hd₂, hz₂⟩, hφ₂⟩
    refine ⟨fun x => h₁ x + h₂ x, ⟨?_, ?_⟩, fun v => ?_⟩
    · filter_upwards [hd₁, hd₂] with x a b using a.add b
    · filter_upwards [hz₁, hz₂] with x a b hx using by rw [a hx, b hx, add_zero]
    · rw [fderiv_fun_add hd₁.self_of_nhds hd₂.self_of_nhds]
      simp only [FunLike.coe_add, Pi.add_apply, hφ₁, hφ₂, LinearMap.add_apply]
  zero_mem' := ⟨fun _ => 0, ⟨Eventually.of_forall fun _ => differentiableAt_const _,
    Eventually.of_forall fun _ _ => rfl⟩, fun v => by simp⟩
  smul_mem' := by
    rintro a φ ⟨h, ⟨hd, hz⟩, hφ⟩
    refine ⟨fun x => a * h x, ⟨?_, ?_⟩, fun v => ?_⟩
    · filter_upwards [hd] with x hx using hx.const_mul a
    · filter_upwards [hz] with x hx hxS using by rw [hx hxS, mul_zero]
    · rw [fderiv_const_mul hd.self_of_nhds]
      simp only [FunLike.coe_smul, Pi.smul_apply, hφ, LinearMap.smul_apply, smul_eq_mul]

/-- **The coordinate tangent space** of `S` at `c₀`: the common kernel of the differentials of the functions vanishing on
`S` near `c₀`. -/
def vanishingTangent : Submodule ℂ (ComplexModel n) := (vanishingDifferentials S c₀).dualCoannihilator

theorem mem_vanishingTangent_iff {v : ComplexModel n} :
    v ∈ vanishingTangent S c₀ ↔ ∀ h, IsVanishingNear S c₀ h → fderiv ℂ h c₀ v = 0 := by
  rw [vanishingTangent, Submodule.mem_dualCoannihilator]
  constructor
  · intro H h hh
    have h1 := H (fderiv ℂ h c₀ : ComplexModel n →ₗ[ℂ] ℂ) ⟨h, hh, fun w => rfl⟩
    exact h1
  · rintro H φ ⟨h, hh, hφ⟩
    rw [← hφ v]
    exact H h hh

/-- **Every functional vanishing on the tangent space is the differential of a function vanishing on `S`** (finite
dimension: the annihilator of the coannihilator of a subspace of the dual is the subspace). -/
theorem mem_vanishingDifferentials_of_forall {φ : Module.Dual ℂ (ComplexModel n)}
    (hφ : ∀ v ∈ vanishingTangent S c₀, φ v = 0) : φ ∈ vanishingDifferentials S c₀ := by
  have h1 : φ ∈ (vanishingTangent S c₀).dualAnnihilator := (Submodule.mem_dualAnnihilator φ).mpr hφ
  rwa [vanishingTangent, Subspace.dualCoannihilator_dualAnnihilator_eq] at h1

/-- **The correction**: a continuous linear map `L` injective on the tangent space of `S` at `c₀` becomes injective after
adding the differential at `c₀` of a map `H` holomorphic near `c₀` and vanishing on `S` near `c₀`. -/
theorem exists_vanishing_correction (L : ComplexModel n →L[ℂ] ComplexModel n)
    (hL : ∀ v ∈ vanishingTangent S c₀, L v = 0 → v = 0) :
    ∃ H : ComplexModel n → ComplexModel n, (∀ᶠ x in 𝓝 c₀, DifferentiableAt ℂ H x) ∧
      (∀ᶠ x in 𝓝 c₀, x ∈ S → H x = 0) ∧ Function.Injective (L + fderiv ℂ H c₀) := by
  set T := vanishingTangent S c₀
  obtain ⟨W, hTW⟩ := T.exists_isCompl
  let f : T →ₗ[ℂ] ComplexModel n := (L : ComplexModel n →ₗ[ℂ] ComplexModel n) ∘ₗ T.subtype
  have hf : Function.Injective f := by
    intro a b hab
    have h0 : L ((a : ComplexModel n) - b) = 0 := by
      have hab' : L (a : ComplexModel n) = L b := hab
      rw [map_sub, hab', sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hL _ (T.sub_mem a.2 b.2) h0))
  obtain ⟨Q, hPQ⟩ := (LinearMap.range f).exists_isCompl
  have hrank : Module.finrank ℂ W = Module.finrank ℂ Q := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hTW
    have h2 := Submodule.finrank_add_eq_of_isCompl hPQ
    have h3 := LinearMap.finrank_range_of_inj hf
    omega
  let ι : W ≃ₗ[ℂ] Q := LinearEquiv.ofFinrankEq W Q hrank
  let e₁ : T ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hf
  let M : ComplexModel n ≃ₗ[ℂ] ComplexModel n :=
    (Submodule.prodEquivOfIsCompl T W hTW).symm ≪≫ₗ
      ((e₁.prodCongr ι) ≪≫ₗ Submodule.prodEquivOfIsCompl _ Q hPQ)
  have hMT : ∀ v ∈ T, M v = L v := by
    intro v hv
    have h1 : (Submodule.prodEquivOfIsCompl T W hTW).symm v = ((⟨v, hv⟩ : T), (0 : W)) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left T W hTW ⟨v, hv⟩
    simp only [M, LinearEquiv.trans_apply, h1, LinearEquiv.prodCongr_apply, map_zero,
      Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
    rfl
  let K : ComplexModel n →ₗ[ℂ] ComplexModel n := (M : ComplexModel n →ₗ[ℂ] ComplexModel n) - L
  have hK : ∀ i : Fin n,
      ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) : ComplexModel n →ₗ[ℂ] ℂ) ∘ₗ K ∈
        vanishingDifferentials S c₀ := by
    intro i
    apply mem_vanishingDifferentials_of_forall
    intro v hv
    simp [K, hMT v hv]
  choose h hh hdh using hK
  let H : ComplexModel n → ComplexModel n := fun x => ∑ i, h i x • EuclideanSpace.single i (1 : ℂ)
  have hHas : HasFDerivAt H (∑ i, (fderiv ℂ (h i) c₀).smulRight (EuclideanSpace.single i (1 : ℂ))) c₀ :=
    HasFDerivAt.fun_sum fun i _ => ((hh i).1.self_of_nhds.hasFDerivAt).smul_const _
  have hdiff : ∀ᶠ x in 𝓝 c₀, ∀ i, DifferentiableAt ℂ (h i) x := Filter.eventually_all.mpr fun i => (hh i).1
  have hzero : ∀ᶠ x in 𝓝 c₀, ∀ i, x ∈ S → h i x = 0 := Filter.eventually_all.mpr fun i => (hh i).2
  refine ⟨H, ?_, ?_, ?_⟩
  · filter_upwards [hdiff] with x hx
    exact DifferentiableAt.fun_sum fun i _ => (hx i).smul_const _
  · filter_upwards [hzero] with x hx hxS
    simp [H, hx _ hxS]
  · rw [hHas.fderiv]
    have hEq : ∀ v, (L + ∑ i, (fderiv ℂ (h i) c₀).smulRight (EuclideanSpace.single i (1 : ℂ))) v = M v := by
      intro v
      have hsum : ∑ i, (K v) i • EuclideanSpace.single i (1 : ℂ) = K v := by
        simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
          (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (K v)
      have hterm : ∀ i, (fderiv ℂ (h i) c₀).smulRight (EuclideanSpace.single i (1 : ℂ)) v =
          (K v) i • EuclideanSpace.single i (1 : ℂ) := by
        intro i
        rw [ContinuousLinearMap.smulRight_apply, hdh i v]
        rfl
      simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_sum, Finset.sum_apply, hterm]
      rw [hsum]
      simp [K]
    intro a b hab
    apply M.injective
    rw [← hEq a, ← hEq b]
    exact hab

end Tangent

/-! ### Local inverse data give a biholomorphism carrying one set onto the other -/

section Shrink

private theorem vector_contMDiff (A : Opens (ComplexModel n)) (f : ComplexModel n → ComplexModel n)
    (hf : ContDiffOn ℂ ∞ f A) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun x : A => f x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hf.contDiffAt (A.isOpen.mem_nhds x.property)).contMDiffAt)

/-- **Local inverse data give a biholomorphism of neighbourhoods carrying `SC` exactly onto `SD`**: `F` holomorphic on an
open `N ∋ c₀` with injective differential at `c₀`, `G` holomorphic on an open `B₀`, `F(SC ∩ N) ⊆ SD ∩ B₀`,
`G(SD ∩ B₀) ⊆ SC`, `G ∘ F = id` on `SC ∩ N` and `F ∘ G = id` at the points of `SD ∩ B₀` sent into `N`.  Then `F` restricts to
a biholomorphism `Φ : A ≅ B` of open neighbourhoods `A ⊆ N` of `c₀` and `B ⊆ B₀` of `F(c₀)` with `Φ⁻¹(SD) = SC ∩ A`. -/
theorem exists_biholomorphism_of_local_inverse {SC SD N B₀ : Set (ComplexModel n)} (hN : IsOpen N) (hB₀ : IsOpen B₀)
    {F G : ComplexModel n → ComplexModel n} {c₀ : ComplexModel n}
    (hF : ∀ x ∈ N, DifferentiableAt ℂ F x) (hG : ContDiffOn ℂ ∞ G B₀) (hc₀ : c₀ ∈ SC ∩ N)
    (hinj : Function.Injective (fderiv ℂ F c₀))
    (hFD : ∀ x ∈ SC ∩ N, F x ∈ SD ∩ B₀) (hGC : ∀ y ∈ SD ∩ B₀, G y ∈ SC)
    (hgf : ∀ x ∈ SC ∩ N, G (F x) = x) (hfg : ∀ y ∈ SD ∩ B₀, G y ∈ N → F (G y) = y) :
    ∃ (A B : Opens (ComplexModel n)) (_ : (A : Set (ComplexModel n)) ⊆ N) (_ : (B : Set (ComplexModel n)) ⊆ B₀)
      (Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B),
      c₀ ∈ A ∧ (∀ x : A, (x : ComplexModel n) ∈ SC ↔ (Φ x : ComplexModel n) ∈ SD) ∧
        ∀ x : A, (Φ x : ComplexModel n) = F x := by
  have hFon : DifferentiableOn ℂ F N := fun x hx => (hF x hx).differentiableWithinAt
  obtain ⟨Φ₀, hΦsrc, hΦF, -⟩ := exists_localHolomorphicEquivAt hN hc₀.2 hFon hinj
  have hFinv : ∀ w ∈ Φ₀.target, F (Φ₀.invFun w) = w := fun w hw => by
    rw [← hΦF]; exact Φ₀.right_inv w hw
  have hinvF : ∀ x ∈ Φ₀.source, Φ₀.invFun (F x) = x := fun x hx => by
    rw [← hΦF]; exact Φ₀.left_inv x hx
  have hFtarget : ∀ x ∈ Φ₀.source, F x ∈ Φ₀.target := fun x hx => by
    rw [← hΦF]; exact Φ₀.mapsTo_toFun hx
  have hFc₀ : F c₀ ∈ B₀ := (hFD c₀ hc₀).2
  let Wset : Set (ComplexModel n) := (B₀ ∩ G ⁻¹' Φ₀.source) ∩ Φ₀.target
  have hWopen : IsOpen Wset :=
    (hG.continuousOn.isOpen_inter_preimage hB₀ Φ₀.isOpen_source).inter Φ₀.isOpen_target
  let B : Opens (ComplexModel n) := ⟨Wset, hWopen⟩
  have hFcont : ContinuousOn F Φ₀.source := (hFon.mono hΦsrc).continuousOn
  let Aset : Set (ComplexModel n) := Φ₀.source ∩ F ⁻¹' Wset
  have hAopen : IsOpen Aset := hFcont.isOpen_inter_preimage Φ₀.isOpen_source hWopen
  let A : Opens (ComplexModel n) := ⟨Aset, hAopen⟩
  have hAN : (A : Set (ComplexModel n)) ⊆ N := fun x hx => hΦsrc hx.1
  have hcA : c₀ ∈ A := by
    refine ⟨Φ₀.center_mem_source, ⟨hFc₀, ?_⟩, hFtarget c₀ Φ₀.center_mem_source⟩
    show G (F c₀) ∈ Φ₀.source
    rw [hgf c₀ hc₀]; exact Φ₀.center_mem_source
  have hinvA : ∀ y ∈ Wset, Φ₀.invFun y ∈ Aset := fun y hy =>
    ⟨Φ₀.mapsTo_invFun hy.2, by show F (Φ₀.invFun y) ∈ Wset; rw [hFinv y hy.2]; exact hy⟩
  have hFsmooth : ContDiffOn ℂ ∞ F A :=
    (contDiffOn_of_differentiableOn_complex hFon hN).mono hAN
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
  refine ⟨A, B, hAN, fun y hy => hy.1.1, Φ, hcA, fun x => ?_, fun x => rfl⟩
  change (x : ComplexModel n) ∈ SC ↔ F x ∈ SD
  constructor
  · intro hxC
    exact (hFD x ⟨hxC, hAN x.property⟩).1
  · intro hFxD
    have hy : F x ∈ SD ∩ B₀ := ⟨hFxD, x.property.2.1.1⟩
    have hGsrc : G (F x) ∈ Φ₀.source := x.property.2.1.2
    have heq : G (F x) = (x : ComplexModel n) := by
      have h1 := hinvF (G (F x)) hGsrc
      rw [hfg (F x) hy (hΦsrc hGsrc)] at h1
      rw [← h1, hinvF x x.property.1]
    exact heq ▸ hGC (F x) hy

end Shrink

/-! ### The ambient biholomorphism -/

section Ambient

variable {U V : Opens (ComplexModel n)} {C : Set U} {D : Set V}

/-- **Two embeddings of the same germ in the same ambient dimension are ambient-biholomorphic**: for an intrinsic
isomorphism `e : C ≅ D` of analytic local models `C ⊆ U ⊆ ℂⁿ`, `D ⊆ V ⊆ ℂⁿ` and any `c ∈ C`, there are open neighbourhoods
`A ⊆ U` of `c` and `B ⊆ V` of `e(c)` and a biholomorphism `Φ : A ≅ B` carrying `C ∩ A` exactly onto `D ∩ B` and extending
`e`.  (No minimality is assumed; `HironakaG11InvMinimalAmbient.exists_minimal_ambient_biholomorphism` is the minimal case.) -/
theorem exists_ambient_biholomorphism
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := n) D)
    (he : e.hom ≫ subspacePointMap (n := n) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (c : C) :
    ∃ (A B : Opens (ComplexModel n)) (_ : A ≤ U) (_ : B ≤ V)
      (Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B),
      c.val.val ∈ A ∧
      (∀ x : A, (x : ComplexModel n) ∈ coordinateCarrier C ↔ (Φ x : ComplexModel n) ∈ coordinateCarrier D) ∧
      ∀ (y : C) (hy : y.val.val ∈ A), (Φ ⟨y.val.val, hy⟩ : ComplexModel n) = (e.hom.base y).val.val := by
  obtain ⟨A₀, B₀, F, G, hAU, hBV, hcA, _hdB, hF, hG, _ha, _hb, hFD, hGC, hgf, hfg, hFval, _hGval⟩ :=
    exists_actual_intrinsic_iso_paired_windows e he hC hD c
  set c₀ : ComplexModel n := c.val.val with hc₀
  set SC := coordinateCarrier C
  set SD := coordinateCarrier D
  have hFdiff : ∀ x ∈ (A₀ : Set (ComplexModel n)), DifferentiableAt ℂ F x := fun x hx =>
    (hF.contDiffAt (A₀.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hGdiff : ∀ y ∈ (B₀ : Set (ComplexModel n)), DifferentiableAt ℂ G y := fun y hy =>
    (hG.contDiffAt (B₀.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hc₀C : c₀ ∈ SC ∩ A₀ := ⟨⟨c.val, c.property, rfl⟩, hcA⟩
  have hFc₀ : F c₀ ∈ (B₀ : Set (ComplexModel n)) := (hFD c₀ hc₀C).2
  have hOpen₁ : IsOpen ((A₀ : Set (ComplexModel n)) ∩ F ⁻¹' B₀) :=
    hF.continuousOn.isOpen_inter_preimage A₀.isOpen B₀.isOpen
  have hN₁ : (A₀ : Set (ComplexModel n)) ∩ F ⁻¹' B₀ ∈ 𝓝 c₀ := hOpen₁.mem_nhds ⟨hcA, hFc₀⟩
  -- `dF_{c₀}` is injective on the coordinate tangent space
  have hL : ∀ v ∈ vanishingTangent SC c₀, fderiv ℂ F c₀ v = 0 → v = 0 := by
    intro v hvT hv
    have hcoord : ∀ i : Fin n, v i = 0 := by
      intro i
      let ℓ : ComplexModel n →L[ℂ] ℂ := EuclideanSpace.proj i
      let h : ComplexModel n → ℂ := fun x => ℓ (G (F x)) - ℓ x
      have hHas : HasFDerivAt h (ℓ.comp ((fderiv ℂ G (F c₀)).comp (fderiv ℂ F c₀)) - ℓ) c₀ :=
        (ℓ.hasFDerivAt.comp c₀ (((hGdiff _ hFc₀).hasFDerivAt).comp c₀
          (hFdiff c₀ hcA).hasFDerivAt)).sub ℓ.hasFDerivAt
      have hvan : IsVanishingNear SC c₀ h := by
        refine ⟨?_, ?_⟩
        · filter_upwards [hN₁] with x hx
          exact (ℓ.differentiableAt.comp x ((hGdiff _ hx.2).comp x (hFdiff x hx.1))).sub
            ℓ.differentiableAt
        · filter_upwards [A₀.isOpen.mem_nhds hcA] with x hx hxC
          show ℓ (G (F x)) - ℓ x = 0
          rw [hgf x ⟨hxC, hx⟩, sub_self]
      have happ := (mem_vanishingTangent_iff SC c₀).mp hvT h hvan
      rw [hHas.fderiv] at happ
      simp only [sub_apply, ContinuousLinearMap.comp_apply, hv, map_zero,
        zero_sub, neg_eq_zero] at happ
      simpa [ℓ] using happ
    ext i
    simpa using hcoord i
  -- the correction `H`, vanishing on `C`
  obtain ⟨H, hHd, hHz, hinj⟩ := exists_vanishing_correction SC c₀ (fderiv ℂ F c₀) hL
  obtain ⟨t, ht, htopen, hc₀t⟩ := eventually_nhds_iff.mp (hHd.and hHz)
  let N : Set (ComplexModel n) := (A₀ : Set (ComplexModel n)) ∩ t
  have hNopen : IsOpen N := A₀.isOpen.inter htopen
  let F' : ComplexModel n → ComplexModel n := fun x => F x + H x
  have hF'diff : ∀ x ∈ N, DifferentiableAt ℂ F' x := fun x hx => (hFdiff x hx.1).add (ht x hx.2).1
  have hF'eq : ∀ x ∈ SC ∩ N, F' x = F x := fun x hx => by
    show F x + H x = F x
    rw [(ht x hx.2.2).2 hx.1, add_zero]
  have hF'inj : Function.Injective (fderiv ℂ F' c₀) := by
    have h1 : fderiv ℂ F' c₀ = fderiv ℂ F c₀ + fderiv ℂ H c₀ :=
      fderiv_fun_add (hFdiff c₀ hcA) (ht c₀ hc₀t).1
    rw [h1]
    exact hinj
  have hc₀N : c₀ ∈ SC ∩ N := ⟨hc₀C.1, hcA, hc₀t⟩
  obtain ⟨A, B, hAN, hBB₀, Φ, hcA', hCD, hΦval⟩ := exists_biholomorphism_of_local_inverse hNopen B₀.isOpen
    hF'diff hG hc₀N hF'inj
    (fun x hx => by rw [hF'eq x hx]; exact hFD x ⟨hx.1, hx.2.1⟩)
    (fun y hy => (hGC y hy).1)
    (fun x hx => by rw [hF'eq x hx]; exact hgf x ⟨hx.1, hx.2.1⟩)
    (fun y hy hGy => by rw [hF'eq (G y) ⟨(hGC y hy).1, hGy⟩]; exact hfg y hy)
  refine ⟨A, B, fun x hx => hAU (hAN hx).1, fun y hy => hBV (hBB₀ hy), Φ, hcA', hCD, fun y hy => ?_⟩
  rw [hΦval, hF'eq _ ⟨⟨y.val, y.property, rfl⟩, hAN hy⟩]
  exact hFval y (hAN hy).1

end Ambient

/-! ### Windows of the two models and the vanishing-ideal records -/

section Windows

open MaxLocusLocal (nestedOpens nestedOpensDiffeo)

variable {U V : Opens (ComplexModel n)} {C : Set U} {D : Set V}

/-- **The windows of two local models of the same germ in the same ambient dimension**, in the form consumed by the
transport results of `HironakaG11InvTransport`: opens `A ∋ c` of `U` and `B ∋ e(c)` of `V`, seen as windows of the two
ambient manifolds, and a biholomorphism `Ψ : B ≅ A` of the windows carrying `D` to `C` exactly and `e(y)` to `y`. -/
theorem exists_vanishing_windows
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := n) D)
    (he : e.hom ≫ subspacePointMap (n := n) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (c : C) :
    ∃ (A B : Opens (ComplexModel n)) (_ : A ≤ U) (_ : B ≤ V)
      (Ψ : CMfd.of (n := n) (nestedOpens V B) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (nestedOpens U A)),
      c.val.val ∈ A ∧
      (∀ p : nestedOpens V B, ((Ψ p : nestedOpens U A) : U) ∈ C ↔ (p : V) ∈ D) ∧
      ∀ (y : C), y.val.val ∈ A →
        ∃ p : nestedOpens V B, (p : V) = (e.hom.base y).val ∧ ((Ψ p : nestedOpens U A) : U) = y.val := by
  obtain ⟨A, B, hAU, hBV, Φ, hcA, hCD, hval⟩ := exists_ambient_biholomorphism e he hC hD c
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

/-- **The first-stage values of the vanishing-ideal records are intrinsic** (same ambient dimension, any point): for every
route invariant `R` (e.g. `CanonicalCentres.canonicalInvariant n`) and an intrinsic isomorphism `e : C ≅ D` of analytic local
models in the same ambient dimension, `inv (𝓘_D, 1) (e y) = inv (𝓘_C, 1) y` for every `y ∈ C` near any given `c ∈ C`. -/
theorem inv_vanishingRecord_refl_eq {k : ℕ} {Λ : Type*} [LinearOrder Λ]
    (R : ResolutionInvariant n k Λ)
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := n) D)
    (he : e.hom ≫ subspacePointMap (n := n) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (c : C)
    (hDomC : IsInvDomain k (vanishingRecord n (M := CMfd.of (n := n) U) C))
    (hDomD : IsInvDomain k (vanishingRecord n (M := CMfd.of (n := n) V) D)) :
    ∃ A : Opens (ComplexModel n), c.val.val ∈ A ∧ ∀ y : C, y.val.val ∈ A →
      R.inv (X := CMfd.of (n := n) V) (vanishingRecord n D) BlowupTower.refl (e.hom.base y).val =
        R.inv (X := CMfd.of (n := n) U) (vanishingRecord n C) BlowupTower.refl y.val := by
  obtain ⟨A, B, hAU, hBV, Ψ, hcA, hCD, hpts⟩ := exists_vanishing_windows e he hC hD c
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

end Hironaka.HironakaG11InvAmbientIso
