import Hironaka.Resolution.HironakaG10FlatPrivilegedAssembly
import Hironaka.Resolution.HironakaG10LocSheafExact

set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CompactWindowRestriction
open Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.HironakaG10FlatPrivilegedAssembly
  Hironaka.HironakaG10LocSheafExact
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {K₁ K₂ : Set E} [CompactSpace K₁] [CompactSpace K₂]

/-- The existing holomorphic pullback, specialized to the identity map
between nested compact windows. -/
def windowRestriction (hK : K₂ ⊆ K₁) :
    holSubalgebra K₁ →ₐ[ℂ] holSubalgebra K₂ :=
  pullbackAlg id continuous_id (fun _ => differentiableAt_id)
    (fun _ hz => hK hz)
    (fun _ hz => interior_mono hK hz)

omit [CompactSpace K₁] [CompactSpace K₂] in
@[simp] theorem windowRestriction_apply (hK : K₂ ⊆ K₁)
    (f : holSubalgebra K₁) (z : K₂) :
    ((windowRestriction hK f : holSubalgebra K₂) : C(K₂, ℂ)) z =
      (f : C(K₁, ℂ)) ⟨z, hK z.property⟩ := rfl

/-- The existing bounded pullback on the same identity map. -/
def windowRestrictionCLM (hK : K₂ ⊆ K₁) :
    holSubalgebra K₁ →L[ℂ] holSubalgebra K₂ :=
  pullbackCLM id continuous_id (fun _ => differentiableAt_id)
    (fun _ hz => hK hz)
    (fun _ hz => interior_mono hK hz)

@[simp] theorem windowRestrictionCLM_apply (hK : K₂ ⊆ K₁)
    (f : holSubalgebra K₁) : windowRestrictionCLM hK f = windowRestriction hK f := rfl

omit [CompactSpace K₁] [CompactSpace K₂] in
/-- The residue function from the large-window relation lift evaluates to
the corresponding literal restricted small-window column. -/
theorem bkFun_windowRestriction (hK : K₂ ⊆ K₁)
    {a b : Type*} (G : a → b → holSubalgebra K₁)
    (z : K₂) (i : a) (j : b) :
    bkFun K₁ G i j z =
      ((windowRestriction hK (G i j) : holSubalgebra K₂) : C(K₂, ℂ)) z := by
  rw [bkFun, extendZero_of_mem K₁ _ (hK z.property)]
  exact (windowRestriction_apply hK (G i j) z).symm

omit [CompactSpace K₁] [CompactSpace K₂] in
/-- Matrix entries and actual relation columns restrict literally, preserving
an entire matrix relation. -/
theorem restricted_matrix_relation (hK : K₂ ⊆ K₁)
    {a b c : Type*} [Fintype b] (F : a → b → holSubalgebra K₁)
    (G : b → c → holSubalgebra K₁)
    (hFG : ∀ i k, ∑ j, F i j * G j k = 0) :
    ∀ i k, ∑ j, windowRestriction hK (F i j) * windowRestriction hK (G j k) = 0 := by
  intro i k
  simpa only [map_sum, map_mul, map_zero] using congrArg (windowRestriction hK) (hFG i k)

/-- Restriction preserves continuity of the SAME finite matrix family. -/
theorem continuousAt_restrict_matrix (hK : K₂ ⊆ K₁)
    {Y a b : Type*} [TopologicalSpace Y] [Fintype a] [Fintype b]
    (G : Y → a → b → holSubalgebra K₁) {s₀ : Y} (hG : ContinuousAt G s₀) :
    ContinuousAt (fun s i j => windowRestriction hK (G s i j)) s₀ := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (windowRestrictionCLM hK).continuous.continuousAt.comp
    ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hG))


/-- In particular the SAME restricted relation columns form a holomorphic
matrix family whenever the original columns do. -/
theorem differentiableAt_restrict_matrix (hK : K₂ ⊆ K₁)
    {Y a b : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [Fintype a] [Fintype b]
    (G : Y → a → b → holSubalgebra K₁) {s₀ : Y} (hG : DifferentiableAt ℂ G s₀) :
    DifferentiableAt ℂ (fun s i j => windowRestriction hK (G s i j)) s₀ := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  exact (windowRestrictionCLM hK).differentiableAt.comp s₀
    ((differentiableAt_pi.mp (differentiableAt_pi.mp hG i)) j)



end
end Hironaka.Analytic.Unibranch.HironakaG10CompactWindowRestriction
