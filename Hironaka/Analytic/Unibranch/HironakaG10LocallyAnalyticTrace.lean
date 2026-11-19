import Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference

/-! # Ambient traces of analytic sets defined only on an open domain -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka

namespace Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

noncomputable section

/-- A set has analytic local traces at every point of the domain. -/
def IsLocallyAnalyticOn (X : SourceReducedComplexSpace) (V A : Set X.obj.left) : Prop :=
  ∀ x ∈ V, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ A' : Set e.ambient, IsComplexAnalyticSubset (n := e.dim) A' ∧
      e.toPoint ⁻¹' A = Subtype.val ⁻¹' A'

/-- A globally analytic set is locally analytic on every domain. -/
theorem locallyAnalytic_of_analytic {X : SourceReducedComplexSpace} {A : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (V : Set X.obj.left) : IsLocallyAnalyticOn X V A :=
  fun x _ => hA x

/-- Local analyticity on the domain passes to any chart contained in it. -/
theorem exists_local_trace_on {X : SourceReducedComplexSpace} {V A : Set X.obj.left}
    (hA : IsLocallyAnalyticOn X V A) (e : LocalEmbedding X) (heV : range e.toPoint ⊆ V)
    (c : e.carrier) :
    ∃ O : Opens e.ambient, c.val ∈ O ∧ ∃ A'' : Set O,
      IsComplexAnalyticSubset (n := e.dim) A'' ∧
      ∀ (y : e.carrier) (hy : y.val ∈ O), e.toPoint y ∈ A ↔ (⟨y.val, hy⟩ : O) ∈ A'' := by
  obtain ⟨e₂, hc, A', hA', hpre⟩ := hA (e.toPoint c) (heV ⟨c,rfl⟩)
  obtain ⟨O, hcO, f, hf, hfac⟩ := LocalEmbedding.exists_contMDiff_factor e.map e.overPoint e₂ c hc
  refine ⟨O, hcO, f ⁻¹' A',
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hA', ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hfac y hy
  change e.toPoint y ∈ A ↔ f ⟨y.val, hy⟩ ∈ A'
  rw [← hz]
  change e.toPoint y ∈ A ↔ z ∈ Subtype.val ⁻¹' A'
  rw [← hpre]
  change e.toPoint y ∈ A ↔ e₂.toPoint z ∈ A
  rw [hzy]
  rfl

/-- The image of the trace is ambient analytic on any whole chart contained
  in the domain. -/
theorem analytic_image_local_trace {X : SourceReducedComplexSpace} {V A : Set X.obj.left}
    (hA : IsLocallyAnalyticOn X V A) (e : LocalEmbedding X) (heV : range e.toPoint ⊆ V) :
    IsComplexAnalyticSubset (n := e.dim)
      (Subtype.val '' (e.toPoint ⁻¹' A) : Set e.ambient) := by
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro u
  by_cases hu : u ∈ e.carrier
  · obtain ⟨O, huO, A', hA', hiff⟩ := exists_local_trace_on hA e heV ⟨u, hu⟩
    refine ⟨O, huO, ?_⟩
    have hCO : IsComplexAnalyticSubset (n := e.dim) ((↑) ⁻¹' e.carrier : Set O) :=
      AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O
    have heq : ((↑) ⁻¹' (Subtype.val '' (e.toPoint ⁻¹' A)) : Set O) =
        A' ∩ ((↑) ⁻¹' e.carrier : Set O) := by
      ext o
      constructor
      · rintro ⟨a, ha, hao⟩
        have hoC : (o : e.ambient) ∈ e.carrier := hao ▸ a.property
        refine ⟨?_, hoC⟩
        apply (hiff ⟨o.val, hoC⟩ o.property).mp
        have : (⟨o.val, hoC⟩ : e.carrier) = a := Subtype.ext hao.symm
        rw [this]
        exact ha
      · rintro ⟨ho, hoC⟩
        exact ⟨⟨o.val, hoC⟩, (hiff ⟨o.val, hoC⟩ o.property).mpr ho, rfl⟩
    rw [heq]
    exact hA'.inter hCO
  · refine ⟨⟨e.carrierᶜ, e.analytic.isClosed.isOpen_compl⟩, hu, ?_⟩
    have he : ((↑) ⁻¹' (Subtype.val '' (e.toPoint ⁻¹' A)) :
        Set (⟨e.carrierᶜ, e.analytic.isClosed.isOpen_compl⟩ : Opens e.ambient)) = ∅ := by
      ext o
      simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro a _ hao
      exact o.property (hao ▸ a.property)
    rw [he]
    exact isComplexAnalyticSubset_empty

end
end Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
