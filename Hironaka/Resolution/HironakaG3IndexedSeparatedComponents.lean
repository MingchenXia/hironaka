import Hironaka.Resolution.HironakaG3IndexedMixedNonerasure

/-!
# Analytic pure components on the actual indexed separator

The ordinary strict transforms remain locally finite and have dense regular
loci of the original component dimensions. Their pairwise disjointness then
gives open neighbourhoods isolating each whole transformed component. These
are inputs for subsequent component resolution; endpoint smoothness is not
assumed or asserted here.

Blueprint: `hironaka-g3-indexed-separated-components.tex`.
-/

set_option autoImplicit false

open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3IndexedSeparatedComponents

noncomputable section

open Hironaka.BlowupSequences BlowupTowers HironakaAdmissibleCalculus
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3IndexedMixedGluing
  HironakaG3IndexedMixedNonerasure HironakaActualLocallyFiniteBoundary

/-- Dense regular points of one fixed dimension are preserved by the ordinary
strict transform of a closed set under any holomorphic map. -/
theorem strictTransform_subset_closure_regularLocus
    {n : ℕ} {X Y : CMfd.{0} n} {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    {A : Set X} (hA : IsClosed A) {d : ℕ}
    (hpure : A ⊆ closure (regularLocus (n := n) A d)) :
    strictTransform n f A ⊆ closure (regularLocus (n := n) (strictTransform n f A) d) := by
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
  obtain ⟨_,⟨u,⟨huN,huΩ⟩,rfl⟩,huReg⟩ :=
    mem_closure_iff_nhds.mp (hpure hyA) _ himage
  exact ⟨u,huN,RegularAtDimTransport.regularAtDim_of_preimage hf huΩ hΩ huΩ hEq huReg⟩

/-- A genuine glued tower atlas preserves analyticity of ordinary strict
transforms, even when no global finite blowup tower exists. -/
theorem glued_strictTransform_analytic
    {n : ℕ} {X Z : CMfd.{0} n} {𝒞 : LocalTowerClass X} {P : Z → X}
    (h : IsGluedFrom 𝒞 Z P) {A : Set X} (hA : IsComplexAnalyticSubset (n := n) A) :
    IsComplexAnalyticSubset (n := n) (strictTransform n P A) := by
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro z
  obtain ⟨c,hc⟩ := h.2.2.2 (P z)
  refine ⟨c.V,c.mem_V hc,?_⟩
  have hlocal := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hA c.U) c.T
  rw [strictTransform_chart c h.1] at hlocal
  have htransport := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage c.φ.symm.contMDiff hlocal
  have heq : c.φ.symm ⁻¹' (chartIncl c ⁻¹' strictTransform n P A) =
      (Subtype.val : c.V → Z) ⁻¹' strictTransform n P A := by
    ext v
    simp only [mem_preimage,chartIncl,Diffeomorph.apply_symm_apply]
  rwa [heq] at htransport

/-- Ordinary strict transforms of a locally finite closed family remain
locally finite. No properness or finite tower hypothesis is needed. -/
theorem locallyFinite_strictTransforms
    {n : ℕ} {X Y : CMfd.{0} n} {ι : Type*} (A : ι → Set X)
    (hA : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    {f : Y → X} (hf : Continuous f) :
    LocallyFinite (fun i => strictTransform n f (A i)) :=
  (hLF.preimage_continuous hf).subset (fun i => strictTransform_subset_preimage hf (hA i))

/-- Every whole member of a disjoint locally finite closed family has an
open neighbourhood avoiding all the other members. -/
theorem exists_component_isolating_open
    {X : Type*} [TopologicalSpace X] {ι : Type*} (A : ι → Set X)
    (hA : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (hDis : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (a : ι) :
    ∃ U : Opens X, A a ⊆ U ∧ ∀ i, i ≠ a → Disjoint (A i) (U : Set X) := by
  let J := {i : ι | i ≠ a}
  have hclosed : IsClosed (⋃ i : J, A i) :=
    (hLF.comp_injective Subtype.val_injective).isClosed_iUnion (fun i => hA i)
  let U : Opens X := ⟨(⋃ i : J, A i)ᶜ,hclosed.isOpen_compl⟩
  refine ⟨U,?_,?_⟩
  · intro x hx
    change x ∉ ⋃ i : J, A i
    intro hmem
    obtain ⟨i,hi⟩ := mem_iUnion.mp hmem
    exact Set.disjoint_left.mp (hDis a i i.property.symm) hx hi
  · intro i hi
    exact Set.disjoint_left.mpr (fun x hx hU => hU (mem_iUnion.mpr ⟨⟨i,hi⟩,hx⟩))

/-- The actual indexed separator produces locally finite analytic pure
components of the original dimensions, together with open windows isolating
each whole component and projection onto its entire original carrier. -/
theorem exists_indexed_separator_with_pure_component_windows
    {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (indexedMixedClass V D) Z P ∧
      (∀ a b, a ≠ b → Disjoint (strictTransform n P (V a).carrier)
        (strictTransform n P (V b).carrier)) ∧
      (∀ a, P '' strictTransform n P (V a).carrier = (V a).carrier) ∧
      (∀ a, IsComplexAnalyticSubset (n := n) (strictTransform n P (V a).carrier)) ∧
      (∀ a, strictTransform n P (V a).carrier ⊆
        closure (regularLocus (n := n) (strictTransform n P (V a).carrier) (V a).dim)) ∧
      LocallyFinite (fun a => strictTransform n P (V a).carrier) ∧
      ∀ a, ∃ U : Opens Z, strictTransform n P (V a).carrier ⊆ U ∧
        ∀ b, b ≠ a → Disjoint (strictTransform n P (V b).carrier) (U : Set Z) := by
  obtain ⟨Z,P,h,hDis,hProj⟩ := exists_glued_indexed_separator_with_nonerasure V hV hDim hDistinct D hD
  have hLF := locallyFinite_strictTransforms (fun a => (V a).carrier)
    (fun a => (V a).isClosed_carrier) hV h.1.continuous
  refine ⟨Z,P,h,hDis,hProj,?_,?_,hLF,?_⟩
  · exact fun a => glued_strictTransform_analytic h (V a).irreducible_carrier.analytic
  · exact fun a => strictTransform_subset_closure_regularLocus h.1 (V a).isClosed_carrier
      (HironakaEmbeddedReducible.subset_closure_regularLocus (V a))
  · exact fun a => exists_component_isolating_open _ (fun _ => isClosed_closure) hLF hDis a

/-- Properness and the dense regular open show that a genuine glued pure
resolution preserves the whole target under projection. -/
theorem glued_pure_strictTransform_projects
    {n : ℕ} {X Y : CMfd.{0} n} {A : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) {d : ℕ} (hd : d < n)
    (hpure : A ⊆ closure (regularLocus (n := n) A d)) {Q : Y → X}
    (hQ : IsGluedPureResolution A d Y Q) :
    Q '' strictTransform n Q A = A := by
  have hclosed : IsClosed (Q '' strictTransform n Q A) :=
    hQ.2.1.isClosedMap _ isClosed_closure
  apply Subset.antisymm
  · rintro z ⟨y,hy,rfl⟩
    exact strictTransform_subset_preimage hQ.1.continuous hA.isClosed hy
  · intro z hz
    apply closure_minimal _ hclosed (hpure hz)
    intro q hq
    obtain ⟨y,rfl⟩ := hQ.2.2.1 q
    refine ⟨y,subset_closure ⟨hq.2.1,?_⟩,rfl⟩
    intro hyExc
    rw [HironakaG3RPureEmbedded.exceptionalLocus_eq hA hd hpure hQ] at hyExc
    exact hyExc.2 hq

/-- A separated component admits an actual glued pure-dimensional resolution
which is an isomorphism over every other component. Compatibility with the
prescribed transformed boundary is a separate obligation. -/
theorem exists_resolution_of_separated_component
    {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n) (D : κ → Set X) {P : Z → X}
    (h : IsGluedFrom (indexedMixedClass V D) Z P) (a : ι) :
    ∃ (Y : CMfd.{0} n) (Q : Y → Z),
      IsGluedPureResolution (strictTransform n P (V a).carrier) (V a).dim Y Q ∧
      IsClosedSubmanifold n (strictTransform n Q (strictTransform n P (V a).carrier)) ∧
      (∀ y ∈ strictTransform n Q (strictTransform n P (V a).carrier),
        RegularAtDim (n := n) (strictTransform n Q (strictTransform n P (V a).carrier)) y (V a).dim) ∧
      Q '' strictTransform n Q (strictTransform n P (V a).carrier) = strictTransform n P (V a).carrier ∧
      ∀ b, b ≠ a → IsIsomorphismOver n Q (strictTransform n P (V b).carrier) := by
  let A := strictTransform n P (V a).carrier
  have hA : IsComplexAnalyticSubset (n := n) A :=
    glued_strictTransform_analytic h (V a).irreducible_carrier.analytic
  have hpure : A ⊆ closure (regularLocus (n := n) A (V a).dim) :=
    strictTransform_subset_closure_regularLocus h.1 (V a).isClosed_carrier
      (HironakaEmbeddedReducible.subset_closure_regularLocus (V a))
  obtain ⟨Y,Q,hQ,_hUnique⟩ := existsUnique_gluedPureResolution hA (hDim a) hpure
  have hIso := HironakaG3RPureEmbedded.isIsomorphismOver hA (hDim a) hpure hQ
  refine ⟨Y,Q,hQ,HironakaG3RPureEmbedded.strictTransform_isClosedSubmanifold hA (hDim a) hpure hQ,
    HironakaG3RPureEmbedded.regularAtDim_strictTransform hA (hDim a) hpure hQ,
    glued_pure_strictTransform_projects hA (hDim a) hpure hQ,?_⟩
  intro b hba
  have hsub : strictTransform n P (V b).carrier ⊆ (A \ regularLocus (n := n) A (V a).dim)ᶜ := by
    intro z hz hbad
    exact Set.disjoint_left.mp (glued_indexed_mixed_disjoint V D h hba) hz hbad.1
  refine ⟨⟨fun y hy => hy,?_,?_⟩,?_⟩
  · intro y hy z hz heq
    exact hIso.1.2.1 (hsub hy) (hsub hz) heq
  · intro z hz
    obtain ⟨y,rfl⟩ := hQ.2.2.1 z
    exact ⟨y,hz,rfl⟩
  · exact Set.disjoint_left.mpr (fun y hy hExc => Set.disjoint_left.mp hIso.2 (hsub hy) hExc)

end

end Hironaka.HironakaG3IndexedSeparatedComponents
