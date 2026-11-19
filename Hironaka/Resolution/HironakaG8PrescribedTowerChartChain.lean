import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons
import Hironaka.Resolution.HironakaG8ConsecutiveNestedReorderings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Hironaka.HironakaG8PrescribedTowerChartChain
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3RTowerClass HironakaG3RTowerGluing G3UniversePhysicalClassComparisons
  G3UniverseEmptyAwareCore HironakaOriginalTerminalOverlapComparison
  HironakaG8ConsecutiveNestedReorderings

variable {n : ℕ} {X : CMfd.{0} n}
variable (U : ℕ → Opens X) (Y : ℕ → CMfd.{0} n)
  (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))

/-- The class whose members are the prescribed towers, with all dependent
data retained by its constructor. -/
inductive Prescribed (U : ℕ → Opens X) (Y : ℕ → CMfd.{0} n)
    (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i)) : LocalTowerClass X
  | member (i : ℕ) : Prescribed U Y T (U i) (Y i) (T i)

/-- Physical comparisons on the literal restrictions of the selected family. -/
def PairPhysical : Prop :=
  ∀ i j, ∃ β : CMfd.of (n := n) (openPreimage (T i) (nestedOpens (U i) (U i ⊓ U j)))
    ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (T j) (nestedOpens (U j) (U i ⊓ U j))),
    EmptyAwareTowerIso (overlapBaseEquiv (n := n)
      (inf_le_left : U i ⊓ U j ≤ U i) inf_le_right)
      (restrict (nestedOpens (U i) (U i ⊓ U j)) (T i))
      (restrict (nestedOpens (U j) (U i ⊓ U j)) (T j)) β

theorem prescribed_hasPhysicalComparisons (h : PairPhysical U Y T) :
    HasPhysicalComparisons (Prescribed U Y T) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  cases h₁ with
  | member i =>
    cases h₂ with
    | member j => exact h i j

/-- The common glued atlas has exactly the given index, open sets, endpoints, and towers. -/
def prescribedAtlas (cover : ∀ x : X, ∃ i, x ∈ U i) (h : PairPhysical U Y T) :
    TowerAtlas X where
  J := ℕ
  U := U
  cover := cover
  Y := Y
  T := T
  compare i j := by
    obtain ⟨β, hβ⟩ := h i j
    exact ⟨β, physical_overlap_proj_comm (U i) (U j) hβ⟩

/-- The indexed chart in the actual common atlas. Its open, endpoint,
and dependent tower fields reduce to the prescribed fields. -/
def prescribedChart (cover : ∀ x : X, ∃ i, x ∈ U i) (h : PairPhysical U Y T) (i : ℕ) :
    TowerChart (Prescribed U Y T) (prescribedAtlas U Y T cover h).manifold
      (prescribedAtlas U Y T cover h).proj :=
  let A := prescribedAtlas U Y T cover h
  ⟨U i, Y i, T i, .member i, A.chartOpen i, rfl,
    A.localBiholomorphism i, A.proj_localBiholomorphism i⟩

/-- Gluing preserves the literal chart data for every index, including those
indices that are redundant as a cover. -/
theorem exists_prescribed_chart_chain
    (cover : ∀ x : X, ∃ i, x ∈ U i) (mono : Monotone U)
    (h : PairPhysical U Y T) :
    HasPhysicalComparisons (Prescribed U Y T) ∧
    ∃ (Z : CMfd.{0} n) (P : Z → X),
      IsGluedFrom (Prescribed U Y T) Z P ∧
      ∃ c : ℕ → TowerChart (Prescribed U Y T) Z P,
        (∀ i, (c i).U = U i ∧ (c i).Y = Y i ∧ HEq (c i).T (T i)) ∧
        Monotone (fun i => (c i).U) ∧ (∀ x : X, ∃ i, x ∈ (c i).U) := by
  let A := prescribedAtlas U Y T cover h
  let c := prescribedChart U Y T cover h
  have hc (x : X) : ∃ i, x ∈ (c i).U := cover x
  refine ⟨prescribed_hasPhysicalComparisons U Y T h, A.manifold, A.proj,
    ⟨A.contMDiff_proj, A.isProperMap_proj, A.surjective_proj, ?_⟩,
    c, fun _ => ⟨rfl, rfl, HEq.rfl⟩, mono, hc⟩
  intro x
  obtain ⟨i, hi⟩ := hc x
  exact ⟨c i, hi⟩

section Nested

variable {A B : CMfd.{0} n} {V W O : Opens X}
  {S : BlowupTower (CMfd.of (n := n) V) A}
  {R : BlowupTower (CMfd.of (n := n) W) B}

private def PhysicalOn (O : Opens X) (hOV : O ≤ V) (hOW : O ≤ W)
    (S : BlowupTower (CMfd.of (n := n) V) A)
    (R : BlowupTower (CMfd.of (n := n) W) B) : Prop :=
  ∃ b : CMfd.of (n := n) (openPreimage S (nestedOpens V O))
    ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage R (nestedOpens W O)),
    EmptyAwareTowerIso (overlapBaseEquiv hOV hOW)
      (restrict (nestedOpens V O) S) (restrict (nestedOpens W O) R) b

private theorem physical_on_smaller (hO : O = V) (hOV : O ≤ V) (hOW : O ≤ W)
    (h : NestedGeometry S R) : PhysicalOn O hOV hOW S R := by
  subst O
  obtain ⟨a, ha, f, hf⟩ := NestedGeometry.refl S
  obtain ⟨e, he, g, hg⟩ := h
  have hbase : a.symm.trans e = overlapBaseEquiv (n := n) hOV hOW := by
    ext x
    change (e (a.symm x)).val.val = x.val.val
    rw [he, ← ha (a.symm x), a.apply_symm_apply]
  exact ⟨f.symm.trans g, hbase ▸ G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.symm hf) hg⟩

private theorem physical_on_symm (hOV : O ≤ V) (hOW : O ≤ W)
    (h : PhysicalOn O hOV hOW S R) : PhysicalOn O hOW hOV R S := by
  obtain ⟨b, hb⟩ := h
  have hbase : (overlapBaseEquiv (n := n) hOV hOW).symm = overlapBaseEquiv hOW hOV := by
    ext x
    rfl
  exact ⟨b.symm, hbase ▸ G3UniverseEmptyAwareCore.symm hb⟩

end Nested

/-- Pairwise nested comparisons give the fully restricted physical comparison
on both sides of every actual overlap. -/
theorem pairPhysical_of_nested (mono : Monotone U)
    (h : ∀ i j : ℕ, i ≤ j → NestedGeometry (T i) (T j)) :
    PairPhysical U Y T := by
  intro i j
  change PhysicalOn (U i ⊓ U j) inf_le_left inf_le_right (T i) (T j)
  rcases le_total i j with hij | hji
  · exact physical_on_smaller (inf_eq_left.mpr (mono hij)) _ _ (h i j hij)
  · exact physical_on_symm _ _
      (physical_on_smaller (inf_eq_right.mpr (mono hji)) _ _ (h j i hji))

/-- The prescribed sequence of towers gives a common physical chart chain
from its pairwise nested geometry. -/
theorem exists_prescribed_chart_chain_of_nested
    (cover : ∀ x : X, ∃ i, x ∈ U i) (mono : Monotone U)
    (h : ∀ i j : ℕ, i ≤ j → NestedGeometry (T i) (T j)) :
    HasPhysicalComparisons (Prescribed U Y T) ∧
    ∃ (Z : CMfd.{0} n) (P : Z → X),
      IsGluedFrom (Prescribed U Y T) Z P ∧
      ∃ c : ℕ → TowerChart (Prescribed U Y T) Z P,
        (∀ i, (c i).U = U i ∧ (c i).Y = Y i ∧ HEq (c i).T (T i)) ∧
        Monotone (fun i => (c i).U) ∧ (∀ x : X, ∃ i, x ∈ (c i).U) :=
  exists_prescribed_chart_chain U Y T cover mono (pairPhysical_of_nested U Y T mono h)

/-- Consecutive genuine geometry is sufficient for the prescribed chart chain. -/
theorem exists_prescribed_chart_chain_of_succ
    (cover : ∀ x : X, ∃ i, x ∈ U i) (mono : Monotone U)
    (h : ∀ i : ℕ, NestedGeometry (T i) (T (i+1))) :
    HasPhysicalComparisons (Prescribed U Y T) ∧
    ∃ (Z : CMfd.{0} n) (P : Z → X),
      IsGluedFrom (Prescribed U Y T) Z P ∧
      ∃ c : ℕ → TowerChart (Prescribed U Y T) Z P,
        (∀ i, (c i).U = U i ∧ (c i).Y = Y i ∧ HEq (c i).T (T i)) ∧
        Monotone (fun i => (c i).U) ∧ (∀ x : X, ∃ i, x ∈ (c i).U) :=
  exists_prescribed_chart_chain_of_nested U Y T cover mono (nestedGeometry_of_succ U mono T h)

end
end Hironaka.HironakaG8PrescribedTowerChartChain
