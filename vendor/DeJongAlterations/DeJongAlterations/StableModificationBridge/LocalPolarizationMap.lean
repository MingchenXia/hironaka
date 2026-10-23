import DeJongAlterations.StableModificationBridge.LocalGeneratingSections
import DeJongAlterations.StableModificationBridge.RelativeSeparatingMap

/-!
# A finite relative map from the same original positive line-bundle power

The construction retains an explicit native generating tuple. The chosen closed fibre is used
with its original residue field, including after restricting the original family to a base open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace DeJongAlterations.StableModificationBridge.LocalPolarizationMap

open StableModification.Projectivity
open Geometry.ProjectiveIdeal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- The actual relative projective map determined by an original generating tuple. -/
def sectionMap (β : X ⟶ Y) (p : Y ⟶ Spec (.of R))
    {L : LineBundleData X} {m : ℤ} {N : ℕ}
    {T : Fin (N + 1) → L.Sections m ⊤} (hT : LineBundleData.Generates T) :
    X ⟶ pullback p (projectiveSpaceStructure R N) :=
  pullback.lift β (LineBundleData.toProjectiveSpace (β ≫ p) hT)
    (LineBundleData.toProjectiveSpace_structure (β ≫ p) hT).symm

@[reassoc]
theorem sectionMap_fst (β : X ⟶ Y) (p : Y ⟶ Spec (.of R))
    {L : LineBundleData X} {m : ℤ} {N : ℕ}
    {T : Fin (N + 1) → L.Sections m ⊤} (hT : LineBundleData.Generates T) :
    sectionMap β p hT ≫ pullback.fst p (projectiveSpaceStructure R N) = β :=
  pullback.lift_fst _ _ _

/-- From the genuine original fibre section, internally construct a same-power native
generating tuple whose entire relative projective map is finite above an actual subneighborhood.
The tuple is on the original open restriction; no desired map or lifting certificate is supplied. -/
theorem exists_finite_sectionMap (β : X ⟶ Y) [IsProper β]
    (p : Y ⟶ Spec (.of R)) {L : LineBundleData X} (D : TwoAffineCover β L)
    {y : Y} (hyW : y ∈ D.W) (hy : IsClosed ({y} : Set Y))
    (hdim : topologicalKrullDim (β.fiber y) ≤ 1) (hL : FiberAmple L β y)
    {n : ℕ} (hn : 0 < n) (s : (L.pullback (β.fiberι y)).Sections n ⊤)
    (hgen : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    ∃ (O : Y.Opens) (hyO : y ∈ O), O ≤ D.W ∧ ∃ M : ℕ, 0 < M ∧
      ∃ (N : ℕ) (T : Fin (N + 1) →
        (L.pullback (β ⁻¹ᵁ O).ι).Sections (M : ℤ) ⊤)
        (hT : LineBundleData.Generates T) (E : O.toScheme.Opens),
        (⟨y, hyO⟩ : O.toScheme) ∈ E ∧
        IsFinite (sectionMap (β ∣_ O) (O.ι ≫ p) hT ∣_
          (pullback.fst (O.ι ≫ p) (projectiveSpaceStructure R N) ⁻¹ᵁ E)) := by
  classical
  obtain ⟨q, hq, K, τ, σ, O, hyO, hOW, hτ, hσ⟩ :=
    LocalGeneratingSections.exists_generating_with_lift D hyW hy hL hn s
  let U := β ⁻¹ᵁ O
  have htop : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ (β ⁻¹ᵁ D.W) := by
    intro x _
    exact hOW x.2
  let σ' : (L.pullback U.ι).Sections ((n * q : ℕ) : ℤ) ⊤ :=
    (σ.pullback U.ι).restrict htop
  let τ' : X → (L.pullback U.ι).Sections ((n * q : ℕ) : ℤ) ⊤ :=
    fun k => ((τ k).pullback U.ι).restrict htop
  let I := Option {k : X // k ∈ K}
  let family : I → (L.pullback U.ι).Sections ((n * q : ℕ) : ℤ) ⊤ :=
    fun i => i.elim σ' (fun k => τ' k.1)
  have hfamily : ∀ x : U.toScheme, ∃ i, x ∈ (family i).nonvanishingLocus := by
    intro x
    obtain ⟨k, hk, hx⟩ := hτ x.1 x.2
    refine ⟨some ⟨k, hk⟩, ?_⟩
    change x ∈ (τ' k).nonvanishingLocus
    rw [LineBundleData.Sections.nonvanishingLocus_restrict,
      LineBundleData.Sections.nonvanishingLocus_pullback]
    exact ⟨trivial, hx⟩
  let e := Fintype.equivFin I
  let N := Fintype.card I
  let T : Fin (N + 1) → (L.pullback U.ι).Sections ((n * q : ℕ) : ℤ) ⊤ := fun a =>
    if ha : (a : ℕ) < N then family (e.symm ⟨a, ha⟩) else 0
  have hTfamily : ∀ i : I, T ⟨e i, (e i).2.trans (Nat.lt_succ_self _)⟩ = family i := by
    intro i
    simp only [T, N, (e i).2, dif_pos]
    congr 1
    exact e.symm_apply_apply i
  have hT : LineBundleData.Generates T := by
    intro x
    obtain ⟨i, hi⟩ := hfamily x
    exact ⟨⟨e i, (e i).2.trans (Nat.lt_succ_self _)⟩, by rw [hTfamily]; exact hi⟩
  let βO := β ∣_ O
  let pO := O.ι ≫ p
  let h := LineBundleData.toProjectiveSpace (βO ≫ pO) hT
  let a₀ : Fin (N + 1) := ⟨e none, (e none).2.trans (Nat.lt_succ_self _)⟩
  have ha₀ : h ⁻¹ᵁ nativeCoordinateOpen a₀ = σ'.nonvanishingLocus := by
    rw [LineBundleData.toProjectiveSpace_preimage_coordinate, hTfamily]
    rfl
  have hrange : Set.range (β.fiberι y) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨β.fiberι y z, ?_⟩, rfl⟩
    change β (β.fiberι y z) ∈ O
    rw [fiberι_apply_mem]
    exact hyO
  let j := IsOpenImmersion.lift U.ι (β.fiberι y) hrange
  have hj : j ≫ U.ι = β.fiberι y := IsOpenImmersion.lift_fac _ _ _
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  let : IsClosedImmersion (β.fiberι y) := by
    change IsClosedImmersion (pullback.fst β (Y.fromSpecResidueField y))
    infer_instance
  have : IsClosedImmersion (j ≫ U.ι) := hj.symm ▸ inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j U.ι
  let yO : O.toScheme := ⟨y, hyO⟩
  have hjβ : j ≫ βO ≫ O.ι = β.fiberι y ≫ β := by
    rw [morphismRestrict_ι, ← Category.assoc, hj]
  have hjrange : Set.range j = βO ⁻¹' {yO} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      change (j ≫ βO ≫ O.ι) z = y
      rw [hjβ]
      exact fiberι_apply_mem y z
    · intro hx
      have hxβ : β (U.ι x) = y := by
        have he := congrArg (fun f => f x) (morphismRestrict_ι β O)
        exact he.symm.trans (congrArg Subtype.val hx)
      obtain ⟨z, hz⟩ : U.ι x ∈ Set.range (β.fiberι y) := by
        rw [Scheme.Hom.range_fiberι]
        exact hxβ
      refine ⟨z, U.ι.isEmbedding.injective ?_⟩
      have he := congrArg (fun f => f z) hj
      exact he.trans hz
  have hcoord : j ⁻¹ᵁ (h ⁻¹ᵁ nativeCoordinateOpen a₀) = s.nonvanishingLocus := by
    rw [ha₀, LineBundleData.Sections.nonvanishingLocus_restrict,
      LineBundleData.Sections.nonvanishingLocus_pullback, Scheme.Hom.preimage_inf,
      Scheme.Hom.preimage_top, top_inf_eq, ← Scheme.Hom.comp_preimage, hj,
      ← LineBundleData.Sections.nonvanishingLocus_pullback, hσ,
      LineBundleData.Sections.nonvanishingLocus_restrict,
      LineBundleData.Sections.nonvanishingLocus_cast,
      LineBundleData.Sections.nonvanishingLocus_npow _ hq]
    ext z
    exact ⟨fun hz => hz.2, fun hz =>
      ⟨LineBundleData.top_le_fiber_preimage β y hyW trivial, hz⟩⟩
  let : IsNoetherian (β.fiber y) := isNoetherian_fiber y
  obtain ⟨E, hyE, hqf⟩ :=
    RelativeSeparatingMap.exists_open_quasiFiniteAt_of_closed_fibre βO pO h
      (LineBundleData.toProjectiveSpace_structure (βO ≫ pO) hT) yO j hjrange hdim
      s.nonvanishingLocus a₀ hcoord hgen hzero
  refine ⟨O, hyO, hOW, n * q, Nat.mul_pos hn hq, N, T, hT, E, hyE, ?_⟩
  exact RelativeSeparatingMap.isFinite_restrict_of_quasiFiniteAt βO
    (sectionMap βO pO hT) (pullback.fst pO (projectiveSpaceStructure R N))
    (sectionMap_fst βO pO hT) E hqf

end DeJongAlterations.StableModificationBridge.LocalPolarizationMap
