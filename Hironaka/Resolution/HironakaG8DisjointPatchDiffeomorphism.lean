import Hironaka.Blowup.BlowupTowers
import Mathlib.Geometry.Manifold.Diffeomorph
import Hironaka.Blowup.BlowupRestrictOpen

/-! Gluing prescribed endpoint comparisons over disjoint open covers. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointPatchDiffeomorphism

open Hironaka.BlowupSequences BlowupTowers

variable {n : ℕ} {X Y : CMfd.{0} n} {ι : Type*}
local notation "𝓘c" => 𝓘(ℂ,ComplexModel n)

private theorem exists_contMDiff_of_disjoint_patches
    (U : ι → Opens X) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    (hDisjoint : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (f : ∀ i, U i → Y) (hf : ∀ i, ContMDiff 𝓘c 𝓘c ∞ (f i)) :
    ∃ F : X → Y, ContMDiff 𝓘c 𝓘c ∞ F ∧
      ∀ i (x : U i), F x.val = f i x := by
  classical
  choose index hx using hCover
  let F (x : X) := f (index x) ⟨x, hx x⟩
  have hRead (i : ι) (x : U i) : F x.val = f i x := by
    have hi : index x.val = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisjoint hne) (hx x.val) x.property
    have hVal {j : ι} (hji : j = i) (hj : x.val ∈ U j) :
        f j ⟨x.val,hj⟩ = f i x := by
      subst j
      rfl
    exact hVal hi (hx x.val)
  refine ⟨F,?_,hRead⟩
  intro x
  let i := index x
  let x₀ : U i := ⟨x,hx x⟩
  have hEq : (fun u : U i => F u.val) = f i := funext (hRead i)
  apply (contMDiffAt_subtype_iff (f := F) (x := x₀)).mp
  rw [hEq]
  exact (hf i).contMDiffAt

/-- Pairwise disjoint open covers allow the prescribed local
biholomorphisms to glue with exact forward and inverse readback. -/
theorem exists_diffeomorph_of_disjoint_open_covers
    (U : ι → Opens X) (V : ι → Opens Y)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (hUd : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (hVd : Pairwise (fun i j => Disjoint (V i : Set Y) (V j : Set Y)))
    (e : ∀ i, CMfd.of (n := n) (U i) ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (V i)) :
    ∃ E : X ≃ₘ⟮𝓘c,𝓘c⟯ Y,
      (∀ i (x : U i), E x.val = (e i x).val) ∧
      (∀ i (y : V i), E.symm y.val = ((e i).symm y).val) := by
  obtain ⟨F,hF,hReadF⟩ := exists_contMDiff_of_disjoint_patches U hU hUd
    (fun i x => (e i x).val) (fun i => contMDiff_subtype_val.comp (e i).contMDiff)
  obtain ⟨G,hG,hReadG⟩ := exists_contMDiff_of_disjoint_patches V hV hVd
    (fun i y => ((e i).symm y).val) (fun i => contMDiff_subtype_val.comp (e i).symm.contMDiff)
  refine ⟨⟨⟨F,G,?_,?_⟩,hF,hG⟩,hReadF,hReadG⟩
  · intro x
    obtain ⟨i,hi⟩ := hU x
    let u : U i := ⟨x,hi⟩
    change G (F u.val) = u.val
    rw [hReadF, hReadG, Diffeomorph.symm_apply_apply]
  · intro y
    obtain ⟨i,hi⟩ := hV y
    let v : V i := ⟨y,hi⟩
    change F (G v.val) = v.val
    rw [hReadG, hReadF, Diffeomorph.apply_symm_apply]

end Hironaka.HironakaG8DisjointPatchDiffeomorphism
