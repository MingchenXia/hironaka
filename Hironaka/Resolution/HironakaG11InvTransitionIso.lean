import Hironaka.Resolution.HironakaG11InvAmbientIso

/-!
# Ambient biholomorphisms from holomorphic transition data

Lane G11B (run 0080, round 2), G11 route steps 3--4 (`work/hironaka-resume-20261111/G11B/ROUTE-r2.md`); blueprint
`hironaka-g11-inv-ambient-iso.tex` (same section as `HironakaG11InvAmbientIso`).

The form of `HironakaG11InvAmbientIso.exists_ambient_biholomorphism` consumed by local embeddings of a complex space
(Hironaka `LocalEmbedding.exists_contDiff_transition`): two sets `SC`, `SD ⊆ ℂⁿ`, holomorphic transition maps `F` (near `SC`)
and `G` (near `SD`) mapping one set into the other and inverse to each other on the sets.  Then near any point of `SC`,
a correction of `F` by a map vanishing on `SC` is a biholomorphism of neighbourhoods carrying `SC` exactly onto `SD`, equal
to `F` on `SC`.

* **`exists_biholomorphism_of_transitions`**.

Import discipline (Hironaka phase): no `Hironaka.RelativePrincipalization`, no `Hironaka.EmbeddedResolution`, no
pluripotential / Kähler constant.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11InvTransitionIso

open HironakaG11InvAmbientIso

noncomputable section

variable {n : ℕ}

/-- **Ambient biholomorphism from holomorphic transition data**: let `F` be holomorphic on an open `W₁`, `G` on an open
`W₂`, with `F(SC ∩ W₁) ⊆ SD`, `G(SD ∩ W₂) ⊆ SC`, `G ∘ F = id` and `F ∘ G = id` at the points of the sets where the
composites are defined, and `c₀ ∈ SC ∩ W₁` with `F c₀ ∈ W₂`.  Then there are open neighbourhoods `A ⊆ W₁` of `c₀` and
`B ⊆ W₂` of `F c₀` and a biholomorphism `Φ : A ≅ B` with `Φ⁻¹(SD) = SC ∩ A` and `Φ = F` on `SC ∩ A`. -/
theorem exists_biholomorphism_of_transitions {SC SD W₁ W₂ : Set (ComplexModel n)} (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) {F G : ComplexModel n → ComplexModel n} {c₀ : ComplexModel n}
    (hF : ContDiffOn ℂ ∞ F W₁) (hG : ContDiffOn ℂ ∞ G W₂) (hc₀ : c₀ ∈ SC ∩ W₁) (hFc₀ : F c₀ ∈ W₂)
    (hFD : ∀ x ∈ SC ∩ W₁, F x ∈ SD) (hGC : ∀ y ∈ SD ∩ W₂, G y ∈ SC)
    (hgf : ∀ x ∈ SC ∩ W₁, F x ∈ W₂ → G (F x) = x) (hfg : ∀ y ∈ SD ∩ W₂, G y ∈ W₁ → F (G y) = y) :
    ∃ (A B : Opens (ComplexModel n)) (_ : (A : Set (ComplexModel n)) ⊆ W₁)
      (_ : (B : Set (ComplexModel n)) ⊆ W₂) (Φ : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B),
      c₀ ∈ A ∧ (∀ x : A, (x : ComplexModel n) ∈ SC ↔ (Φ x : ComplexModel n) ∈ SD) ∧
        ∀ x : A, (x : ComplexModel n) ∈ SC → (Φ x : ComplexModel n) = F x := by
  have hFdiff : ∀ x ∈ W₁, DifferentiableAt ℂ F x := fun x hx =>
    (hF.contDiffAt (hW₁.mem_nhds hx)).differentiableAt (by simp)
  have hGdiff : ∀ y ∈ W₂, DifferentiableAt ℂ G y := fun y hy =>
    (hG.contDiffAt (hW₂.mem_nhds hy)).differentiableAt (by simp)
  have hOpen₁ : IsOpen (W₁ ∩ F ⁻¹' W₂) := hF.continuousOn.isOpen_inter_preimage hW₁ hW₂
  have hN₁ : W₁ ∩ F ⁻¹' W₂ ∈ 𝓝 c₀ := hOpen₁.mem_nhds ⟨hc₀.2, hFc₀⟩
  -- `dF_{c₀}` is injective on the coordinate tangent space of `SC`
  have hL : ∀ v ∈ vanishingTangent SC c₀, fderiv ℂ F c₀ v = 0 → v = 0 := by
    intro v hvT hv
    have hcoord : ∀ i : Fin n, v i = 0 := by
      intro i
      let ℓ : ComplexModel n →L[ℂ] ℂ := EuclideanSpace.proj i
      let h : ComplexModel n → ℂ := fun x => ℓ (G (F x)) - ℓ x
      have hHas : HasFDerivAt h (ℓ.comp ((fderiv ℂ G (F c₀)).comp (fderiv ℂ F c₀)) - ℓ) c₀ :=
        (ℓ.hasFDerivAt.comp c₀ (((hGdiff _ hFc₀).hasFDerivAt).comp c₀
          (hFdiff c₀ hc₀.2).hasFDerivAt)).sub ℓ.hasFDerivAt
      have hvan : IsVanishingNear SC c₀ h := by
        refine ⟨?_, ?_⟩
        · filter_upwards [hN₁] with x hx
          exact (ℓ.differentiableAt.comp x ((hGdiff _ hx.2).comp x (hFdiff x hx.1))).sub
            ℓ.differentiableAt
        · filter_upwards [hN₁] with x hx hxC
          show ℓ (G (F x)) - ℓ x = 0
          rw [hgf x ⟨hxC, hx.1⟩ hx.2, sub_self]
      have happ := (mem_vanishingTangent_iff SC c₀).mp hvT h hvan
      rw [hHas.fderiv] at happ
      simp only [sub_apply, ContinuousLinearMap.comp_apply, hv, map_zero,
        zero_sub, neg_eq_zero] at happ
      simpa [ℓ] using happ
    ext i
    simpa using hcoord i
  -- the correction `H`, vanishing on `SC`
  obtain ⟨H, hHd, hHz, hinj⟩ := exists_vanishing_correction SC c₀ (fderiv ℂ F c₀) hL
  obtain ⟨t, ht, htopen, hc₀t⟩ := eventually_nhds_iff.mp (hHd.and hHz)
  let N : Set (ComplexModel n) := (W₁ ∩ F ⁻¹' W₂) ∩ t
  have hNopen : IsOpen N := hOpen₁.inter htopen
  let F' : ComplexModel n → ComplexModel n := fun x => F x + H x
  have hF'diff : ∀ x ∈ N, DifferentiableAt ℂ F' x := fun x hx => (hFdiff x hx.1.1).add (ht x hx.2).1
  have hF'eq : ∀ x ∈ SC ∩ N, F' x = F x := fun x hx => by
    show F x + H x = F x
    rw [(ht x hx.2.2).2 hx.1, add_zero]
  have hF'inj : Function.Injective (fderiv ℂ F' c₀) := by
    have h1 : fderiv ℂ F' c₀ = fderiv ℂ F c₀ + fderiv ℂ H c₀ :=
      fderiv_fun_add (hFdiff c₀ hc₀.2) (ht c₀ hc₀t).1
    rw [h1]
    exact hinj
  have hc₀N : c₀ ∈ SC ∩ N := ⟨hc₀.1, ⟨hc₀.2, hFc₀⟩, hc₀t⟩
  obtain ⟨A, B, hAN, hBW₂, Φ, hcA, hCD, hΦval⟩ := exists_biholomorphism_of_local_inverse hNopen hW₂
    hF'diff hG hc₀N hF'inj
    (fun x hx => by rw [hF'eq x hx]; exact ⟨hFD x ⟨hx.1, hx.2.1.1⟩, hx.2.1.2⟩)
    hGC
    (fun x hx => by rw [hF'eq x hx]; exact hgf x ⟨hx.1, hx.2.1.1⟩ hx.2.1.2)
    (fun y hy hGy => by rw [hF'eq (G y) ⟨hGC y hy, hGy⟩]; exact hfg y hy hGy.1.1)
  refine ⟨A, B, fun x hx => (hAN hx).1.1, hBW₂, Φ, hcA, hCD, fun x hx => ?_⟩
  rw [hΦval, hF'eq _ ⟨hx, hAN x.property⟩]

end

end Hironaka.HironakaG11InvTransitionIso
