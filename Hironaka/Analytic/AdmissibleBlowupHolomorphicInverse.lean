import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Blowup.BlowupIsomorphismOff

set_option autoImplicit false

/-! # Actual holomorphic inverse off the original centers

The original admissible sequence internally supplies a genuine section on
the actual open complement, using the single-blowup universal-property
section and real holomorphic composition. No inverse certificate is an input.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AdmissibleBlowupHolomorphicInverse

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open HironakaAdmissibleSequence

/-- The actual admissible sequence supplies both holomorphic inverse identities
on the genuine open complement of the original set of centers. -/
theorem exists_section_compl {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {E₀ : List (Set X)} {F : Set X} {f : Y → X} {E : List (Set Y)}
    (hF : IsClosed F) (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) :
    ∃ s : (⟨Fᶜ, hF.isOpen_compl⟩ : TopologicalSpace.Opens X) → Y,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s ∧
      f ∘ s = Subtype.val ∧ ∀ y (hy : f y ∈ Fᶜ), s ⟨f y, hy⟩ = y := by
  induction h with
  | refl => exact ⟨Subtype.val, contMDiff_subtype_val, rfl, fun _ _ => rfl⟩
  | step f E C π _ hπ _ hCF ih =>
    obtain ⟨sf, hsf, hfs, hsfinv⟩ := ih
    obtain ⟨sg, hsg, hπs, hsginv⟩ := BlowupIsomorphismOff.exists_section_compl hπ
    have hnot (x : (⟨Fᶜ, hF.isOpen_compl⟩ : TopologicalSpace.Opens X)) : sf x ∈ Cᶜ := by
      intro hx
      have hfx : f (sf x) = x.1 := congrFun hfs x
      exact x.2 (hfx ▸ hCF hx)
    let t : (⟨Fᶜ, hF.isOpen_compl⟩ : TopologicalSpace.Opens X) →
        (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens _) := fun x => ⟨sf x, hnot x⟩
    have ht : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ t := by
      intro x
      rw [contMDiffAt_iff_target]
      refine ⟨hsf.continuous.subtype_mk _ |>.continuousAt, ?_⟩
      exact ((contMDiffAt_iff_target.mp (hsf x)).2 : _)
    refine ⟨sg ∘ t, hsg.comp ht, ?_, ?_⟩
    · funext x
      change f (π (sg (t x))) = x.1
      rw [show π (sg (t x)) = sf x from congrFun hπs (t x)]
      exact congrFun hfs x
    · intro z hz
      have hzC : π z ∈ Cᶜ := fun hc => hz (hCF hc)
      have heq : t ⟨f (π z), hz⟩ = ⟨π z, hzC⟩ :=
        Subtype.ext (hsfinv (π z) hz)
      change sg (t ⟨f (π z), hz⟩) = z
      rw [heq]
      exact hsginv z hzC

end Hironaka.AdmissibleBlowupHolomorphicInverse
