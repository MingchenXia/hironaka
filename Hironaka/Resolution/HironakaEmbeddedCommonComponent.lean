import Hironaka.Analytic.AnalyticFibreProductProperProjections
import Hironaka.Resolution.HironakaAuxiliaryGraphGeometry
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism

/-!
# Main components over an embedded singular complex space

The target ambient manifold has arbitrary dimension `m`; the source manifolds
have dimension `n`. An ordinary biholomorphism between their original good
opens constructs the main component of their actual equalizer, with its true
dimension, graph closure and both proper projections. No manifold structure is
assumed on the common image, which may be singular.

The open-product graph argument adapts the preserved, previously uncompiled
H11b draft. The main-component construction extends the accepted regular-
component argument to unequal ambient and source dimensions. These results
do not assert smooth-centre factorization or abstract-space gluing.

Blueprint: `hironaka-embedded-common.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
  Hironaka.ProductComplexManifold

universe u

namespace Hironaka.HironakaEmbeddedCommon

open Hironaka.BlowupSequences ProductComplexManifold
  RegularLocusComponent GlobalComponents

noncomputable section

section Graph

variable {n₀ n₁ : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n₀) X] [IsComplexManifold n₀ X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n₁) Y] [IsComplexManifold n₁ Y]

private theorem regularAtDim_of_prodOpen {O : Opens Y} {F : Set (X × Y)}
    {q : X × O} {d : ℕ}
    (h : RegularAtDim (n := n₀ + n₁) {p : X × O | (p.1, p.2.val) ∈ F} q d) :
    RegularAtDim (n := n₀ + n₁) F (q.1, q.2.val) d := by
  let Q : Opens (X × Y) := ⟨Prod.snd ⁻¹' (O : Set Y), O.isOpen.preimage continuous_snd⟩
  let φ : Q → X × O := fun u => (u.val.1, ⟨u.val.2, u.property⟩)
  let ψ : X × O → Q := fun p => ⟨(p.1, p.2.val), p.2.property⟩
  have hφ : ContMDiff 𝓘(ℂ, ComplexModel (n₀ + n₁))
      𝓘(ℂ, ComplexModel (n₀ + n₁)) ∞ φ :=
    ProductComplexManifold.contMDiff_prodMk
      (ProductComplexManifold.contMDiff_fst.comp contMDiff_subtype_val)
      (BlowupRestrictOpen.contMDiff_opens_mk
        (ProductComplexManifold.contMDiff_snd.comp contMDiff_subtype_val)
        (fun u => u.property))
  have hψ : ContMDiff 𝓘(ℂ, ComplexModel (n₀ + n₁))
      𝓘(ℂ, ComplexModel (n₀ + n₁)) ∞ ψ :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (ProductComplexManifold.contMDiff_prodMk ProductComplexManifold.contMDiff_fst
        (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_snd))
      (fun p => p.2.property)
  let z : Q := ψ q
  have hz : z ∉ exceptionalLocus (n₀ + n₁) φ :=
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse hφ hψ
      (fun _ => rfl) (fun _ => rfl) z
  have hQ : RegularAtDim (n := n₀ + n₁)
      ((Subtype.val : Q → X × Y) ⁻¹' F) z d :=
    RegularAtDimTransport.regularAtDim_of_preimage (g := φ) hφ hz
      (A := {p : X × O | (p.1, p.2.val) ∈ F}) isOpen_univ (mem_univ z)
      (fun _ _ => Iff.rfl) h
  exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hQ

private theorem regularAtDim_of_eq_graph {O : Opens Y} {g : O → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n₁) 𝓘(ℂ, ComplexModel n₀) ∞ g)
    {F : Set (X × Y)}
    (hF : ∀ (p : X × Y) (hp : p.2 ∈ O), p ∈ F ↔ p.1 = g ⟨p.2, hp⟩)
    (b : O) : RegularAtDim (n := n₀ + n₁) F (g b, b.val) n₁ := by
  have hΓ := HironakaAuxiliaryGraphGeometry.regularAtDim_graph hg
    (AnalyticIrreducibleComponents.regularAtDim_univ b)
  have heq : {p : X × O | (p.1, p.2.val) ∈ F} =
      HironakaAuxiliaryGraphGeometry.graphOn g univ := by
    ext p
    change ((p.1, p.2.val) ∈ F) ↔ p.2 ∈ univ ∧ p.1 = g p.2
    simp only [mem_univ, true_and]
    exact hF (p.1, p.2.val) p.2.property
  rw [← heq] at hΓ
  exact regularAtDim_of_prodOpen (q := (g b, b)) hΓ

end Graph

section MainComponent

variable {m n : ℕ} {M Y₀ Y₁ : Type u}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  {c₀ : Y₀ → M} {c₁ : Y₁ → M} {B : Set M}

/-- The original open of a resolution lying over the complement of `B`. -/
def goodOpen (c : Y₁ → M)
    (hc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c)
    (B : Set M) (hB : IsClosed B) : Opens Y₁ :=
  ⟨c ⁻¹' Bᶜ, hB.isOpen_compl.preimage hc.continuous⟩

omit [IsComplexManifold m M] in
/-- An ordinary open transition makes the literal equalizer regular at every
point of the original good graph, even if the common image is singular. -/
theorem regularAtDim_equalizer
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₁)
    (hBc : IsClosed B)
    (e : goodOpen c₁ hc₁ B hBc ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBc)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ))
    {p : Y₀ × Y₁} (hp : c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B) :
    RegularAtDim (n := n + n) {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2} p n := by
  let g : goodOpen c₁ hc₁ B hBc → Y₀ := fun y => (e y).val
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g :=
    contMDiff_subtype_val.comp e.contMDiff
  have hF (q : Y₀ × Y₁) (hq : q.2 ∈ goodOpen c₁ hc₁ B hBc) :
      c₀ q.1 = c₁ q.2 ↔ q.1 = g ⟨q.2, hq⟩ := by
    constructor
    · intro hqF
      apply hinj
      · change c₀ q.1 ∉ B
        rwa [hqF]
      · exact (e ⟨q.2, hq⟩).property
      · exact hqF.trans (he ⟨q.2, hq⟩).symm
    · intro hqg
      rw [hqg]
      exact he ⟨q.2, hq⟩
  have hpO : p.2 ∈ goodOpen c₁ hc₁ B hBc := by
    change c₁ p.2 ∉ B
    rw [← hp.1]
    exact hp.2
  have heq : p = (g ⟨p.2, hpO⟩, p.2) := Prod.ext ((hF p hpO).mp hp.1) rfl
  rw [heq]
  exact regularAtDim_of_eq_graph hg hF ⟨p.2, hpO⟩

/-- The original holomorphic maps and their open isomorphism construct the
actual main irreducible component over their possibly singular common image. -/
theorem exists_mainComponent_of_open_transition [ConnectedSpace Y₁]
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₁)
    (hBa : IsComplexAnalyticSubset (n := m) B)
    (hthin : interior (c₁ ⁻¹' B) = ∅)
    (e : goodOpen c₁ hc₁ B hBa.isClosed ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBa.isClosed)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ)) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
      V.dim = n ∧
      V.carrier ∈ globalComponents (n := n + n) {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
      V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
      V.carrier ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
      (∀ p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B},
        RegularAtDim (n := n + n) V.carrier p n) := by
  classical
  let U := goodOpen c₁ hc₁ B hBa.isClosed
  have hEa : IsComplexAnalyticSubset (n := n) (c₁ ⁻¹' B) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hc₁ hBa
  have hUne : (c₁ ⁻¹' B)ᶜ.Nonempty :=
    (interior_eq_empty_iff_dense_compl.mp hthin).nonempty
  have hEne : c₁ ⁻¹' B ≠ univ := by
    intro h
    obtain ⟨y, hy⟩ := hUne
    exact hy (h.symm ▸ mem_univ y)
  have hUconn : IsPreconnected (U : Set Y₁) :=
    AnalyticComplementConnected.isPreconnected_compl hEa hEne
  have : PreconnectedSpace U := Subtype.preconnectedSpace hUconn
  let F : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2}
  let S : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B}
  let γ : U → Y₀ × Y₁ := fun y => ((e y).val, y.val)
  have hSimage : S = γ '' univ := by
    ext p
    constructor
    · rintro ⟨hpF, hpB⟩
      have hpO : p.2 ∈ U := by change c₁ p.2 ∉ B; rwa [← hpF]
      refine ⟨⟨p.2, hpO⟩, mem_univ _, ?_⟩
      apply Prod.ext
      · exact hinj (e ⟨p.2, hpO⟩).property hpB ((he ⟨p.2, hpO⟩).trans hpF.symm)
      · rfl
    · rintro ⟨y, -, rfl⟩
      exact ⟨he y, (e y).property⟩
  have hγ : Continuous γ :=
    (continuous_subtype_val.comp e.continuous).prodMk continuous_subtype_val
  have hSconn : IsPreconnected S := by
    rw [hSimage]
    exact isPreconnected_univ.image γ hγ.continuousOn
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hUne
    rw [hSimage]
    exact ⟨γ ⟨y, hy⟩, ⟨⟨y, hy⟩, mem_univ _, rfl⟩⟩
  have hSreg (p : Y₀ × Y₁) (hp : p ∈ S) : RegularAtDim (n := n + n) F p n :=
    regularAtDim_equalizer hc₀ hc₁ hBa.isClosed e he hinj hp
  obtain ⟨a, ha⟩ := hSne
  have hreg : RegularAtDim (n := n + n) F a n := hSreg a ha
  let C : Set (Y₀ × Y₁) := component (n := n + n) F a
  have hSC : S ⊆ C := subset_component_of_isPreconnected hSconn
    (fun p hp => ⟨n, hSreg p hp⟩) ⟨a, ha, mem_component_self hreg⟩
  have hFa : IsComplexAnalyticSubset (n := n + n) F :=
    AnalyticFibreProductCarrier.isComplexAnalyticSubset_fibreProduct hc₀ hc₁
  let T : Set (Y₀ × Y₁) := (fun p => c₀ p.1) ⁻¹' B
  have hTa : IsComplexAnalyticSubset (n := n + n) T :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (hc₀.comp ProductComplexManifold.contMDiff_fst) hBa
  have hCT : ¬ C ⊆ T := fun h => ha.2 (h (mem_component_self hreg))
  have hCS : C \ T ⊆ S := fun p hp => ⟨component_subset F a hp.1, hp.2⟩
  have hCdense := (ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
    hFa hTa hreg hCT).2
  have hclosure : closure C = closure S := by
    apply Set.Subset.antisymm
    · exact closure_minimal (hCdense.trans (closure_mono hCS)) isClosed_closure
    · exact closure_mono hSC
  let V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁) :=
    { carrier := closure C
      isClosed_carrier := isClosed_closure
      irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hFa hreg
      dim := n
      dim_le := Nat.le_add_right n n
      regularLocus_nonempty := ⟨a, regularAtDim_closure_component hreg (mem_component_self hreg)⟩ }
  exact ⟨V, rfl, closure_component_mem_globalComponents hreg, hclosure,
    closure_minimal (component_subset F a) hFa.isClosed,
    fun p hp => regularAtDim_closure_component hreg (hSC hp)⟩

/-- The same component has both proper original coordinate projections. -/
theorem exists_mainComponent_proper_projections [ConnectedSpace Y₁]
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₁)
    (hp₀ : IsProperMap c₀) (hp₁ : IsProperMap c₁)
    (hBa : IsComplexAnalyticSubset (n := m) B)
    (hthin : interior (c₁ ⁻¹' B) = ∅)
    (e : goodOpen c₁ hc₁ B hBa.isClosed ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBa.isClosed)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ)) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
      V.dim = n ∧
      V.carrier ∈ globalComponents (n := n + n) {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
      V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
      V.carrier ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
      (∀ p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B},
        RegularAtDim (n := n + n) V.carrier p n) ∧
      IsProperMap (fun p : V.carrier => p.val.1) ∧
      IsProperMap (fun p : V.carrier => p.val.2) := by
  obtain ⟨V, hdim, hglobal, hclosure, hVF, hreg⟩ :=
    exists_mainComponent_of_open_transition hc₀ hc₁ hBa hthin e he hinj
  exact ⟨V, hdim, hglobal, hclosure, hVF, hreg,
    AnalyticFibreProductProperProjections.isProperMap_fst_of_closed_fibreProduct
      hc₀.continuous hp₁ V.isClosed_carrier hVF,
    AnalyticFibreProductProperProjections.isProperMap_snd_of_closed_fibreProduct
      hp₀ hc₁.continuous V.isClosed_carrier hVF⟩

end MainComponent

end

end Hironaka.HironakaEmbeddedCommon
