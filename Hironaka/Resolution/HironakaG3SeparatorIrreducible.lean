import Hironaka.Resolution.HironakaG3IndexedBadDense
import Hironaka.Resolution.HironakaG3IndexedSeparatedComponents
import Hironaka.Analytic.ProperMappingTheorem
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ProperDenseIrreducible
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaAdmissibleCalculus
  HironakaG3FiniteMixedBadLocus HironakaG3IndexedMixedBad HironakaG3IndexedBadDense
  HironakaG3IndexedMixedNonerasure HironakaG3IndexedMixedGluing HironakaG3RTowerClass
  HironakaG3IndexedSeparatedComponents

/-- Proper holomorphic images and injectivity on a dense good part lift
analytic irreducibility from a whole image to its actual source subset. -/
theorem analytic_irreducible_of_proper_dense_injective
    {n : ℕ} {X Y : CMfd.{0} n} (f : Y → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hproper : IsProperMap f) {A : Set Y} {C : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hproj : f '' A = C)
    (O : Set X) (hdense : A ⊆ closure (A ∩ f ⁻¹' O))
    (hinj : InjOn f (f ⁻¹' O)) : IsComplexAnalyticallyIrreducible (n := n) A := by
  obtain ⟨x,hx⟩ := hC.nonempty
  rw [← hproj] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨hA,⟨y,hy⟩,?_⟩
  intro B D hB hD hBA hDA hAB
  have hBi : IsComplexAnalyticSubset (n := n) (f '' B) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hf hB
      (fun K hK => (hproper.isCompact_preimage hK).inter_left hB.isClosed)
  have hDi : IsComplexAnalyticSubset (n := n) (f '' D) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hf hD
      (fun K hK => (hproper.isCompact_preimage hK).inter_left hD.isClosed)
  have hBC : f '' B ⊆ C := by rw [← hproj]; exact image_mono hBA
  have hDC : f '' D ⊆ C := by rw [← hproj]; exact image_mono hDA
  have hsplit : C = f '' B ∪ f '' D := by rw [← image_union,← hAB,hproj]
  have hLift {T : Set Y} (hT : IsClosed T) (hTA : T ⊆ A) (hCT : C = f '' T) : A = T := by
    apply Subset.antisymm _ hTA
    apply hdense.trans
    apply closure_minimal _ hT
    rintro z ⟨hzA,hzO⟩
    have hzC : f z ∈ C := by rw [← hproj]; exact ⟨z,hzA,rfl⟩
    rw [hCT] at hzC
    obtain ⟨w,hwT,hwz⟩ := hzC
    have hwO : f w ∈ O := hwz ▸ hzO
    have hwz' : w = z := hinj hwO hzO hwz
    exact hwz' ▸ hwT
  rcases hC.eq_left_or_eq_right hBi hDi hBC hDC hsplit with h | h
  · exact Or.inl (hLift hB.isClosed hBA h)
  · exact Or.inr (hLift hD.isClosed hDA h)

/-- Each original component is dense off the full indexed bad support. -/
theorem indexed_component_dense_off_bad {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P) (a : ι) :
    (V a).carrier ⊆ closure ((V a).carrier \ indexedMixedBad V) := by
  intro x hx
  obtain ⟨c,hc⟩ := h.2.2.2 x
  obtain ⟨s,r,Ef,hs,hr,hTree,hOver,hAdm,hSNC,hDis⟩ := c.mem
  let l := s.sort (· ≤ ·)
  let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
  have he : Injective l.get := (s.sort_nodup (· ≤ ·)).injective_get
  let e : Fin l.length ↪ ι := ⟨l.get,he⟩
  have hVis : ∀ i, ((V i).carrier ∩ (c.U : Set X)).Nonempty → i ∈ Set.range e := by
    intro i hVisible
    have hi : i ∈ l := by simpa [l] using hs i hVisible
    exact List.mem_iff_get.mp hi
  have hData := mixedBadLocus_closed_and_good W (fun i => hDim (l.get i))
    (fun i j hij => hDistinct (l.get i) (l.get j) (fun heq => hij (he heq)))
  have ha : a ∈ s := hs a ⟨x,hx,hc⟩
  have ha' : a ∈ l := by simpa [l] using ha
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha'
  have hdense : (V a).carrier ⊆ closure ((V a).carrier \ mixedBadLocus W) := by
    simpa only [W,hi] using (hData.2 i).2.2.2.2
  have hclose := c.U.isOpen.closure_inter ⟨hdense hx,hc⟩
  apply closure_mono _ hclose
  rintro q ⟨⟨hqV,hqNot⟩,hqU⟩
  refine ⟨hqV,?_⟩
  intro hq
  apply hqNot
  exact indexed_bad_on_complete_window V e c.U hVis ⟨hq,hqU⟩

/-- Density on the target lifts to the actual strict transform without a
new exceptional-image hypothesis. -/
theorem strictTransform_dense_over_dense_subset
    {n : ℕ} {X Y : CMfd.{0} n} {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    {A O : Set X} (hA : IsClosed A) (hdense : A ⊆ closure (A ∩ O)) :
    strictTransform n f A ⊆ closure (strictTransform n f A ∩ f ⁻¹' O) := by
  let Ω := (exceptionalLocus n f)ᶜ
  have hΩ : IsOpen Ω := StrictTransformComposition.isOpen_compl_exceptionalLocus hf
  have hEq : ∀ y ∈ Ω, y ∈ strictTransform n f A ↔ f y ∈ A := by
    intro y hy
    exact ⟨fun h => strictTransform_subset_preimage hf.continuous hA h,
      fun h => subset_closure ⟨h,hy⟩⟩
  apply closure_minimal _ isClosed_closure
  rintro y ⟨hyA,hyΩ⟩
  rw [mem_closure_iff_nhds]
  intro N hN
  have hNΩ : N ∩ Ω ∈ 𝓝 y := inter_mem hN (hΩ.mem_nhds hyΩ)
  have himage : f '' (N ∩ Ω) ∈ 𝓝 (f y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hf hyΩ]
    exact image_mem_map hNΩ
  obtain ⟨_,⟨u,⟨huN,huΩ⟩,rfl⟩,⟨huA,huO⟩⟩ :=
    mem_closure_iff_nhds.mp (hdense hyA) _ himage
  exact ⟨u,huN,(hEq u huΩ).mpr huA,huO⟩

/-- An original component has an irreducible strict transform on the actual
glued indexed separator. -/
theorem indexed_separator_strictTransform_irreducible {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P) (a : ι) :
    IsComplexAnalyticallyIrreducible (n := n) (strictTransform n P (V a).carrier) := by
  have hDense := indexed_component_dense_off_bad V hDim hDistinct D h a
  have hDense' : (V a).carrier ⊆ closure ((V a).carrier ∩ (indexedMixedBad V)ᶜ) := by
    simpa only [sdiff_eq] using hDense
  have hStrict := strictTransform_dense_over_dense_subset h.1 (V a).isClosed_carrier hDense'
  have hIso := glued_indexed_isIsomorphismOver V hDim hDistinct D h
  exact analytic_irreducible_of_proper_dense_injective P h.1 h.2.1
    (glued_strictTransform_analytic h (V a).irreducible_carrier.analytic)
    (V a).irreducible_carrier (glued_indexed_mixed_projects V hDim hDistinct D h a)
    (indexedMixedBad V)ᶜ hStrict hIso.1.2.1
end
end Hironaka.HironakaG3ProperDenseIrreducible
