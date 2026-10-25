/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OmegaDegreeSmooth
import DeJongAlterations.StableModification.CurvesField.GenusFormula

/-!
# Euler characteristic of a twist by finitely many simple points

Let `Y` be a Noetherian scheme with affine diagonal over a field `k` (through
`c : k →+* Γ(Y, ⊤)`), `E` a finite set of closed points of `Y`, and `α : F ⟶ G` a morphism of
quasi-coherent `𝒪_Y`-modules which is injective on the sections over every affine open, bijective
on the sections over every affine open missing `E`, and such that every `y ∈ E` has an affine
neighbourhood `W_y` with `W_y ∩ E = {y}` on which the cokernel `Γ(W_y, G) / α Γ(W_y, F)` is
one-dimensional. Then (`eulerCharOf_eq_add_card`)

  `χ(G) = χ(F) + #E`.

In the application `F = Ω¹_{Z̃/K}` is the sheaf of differentials of the normalization `Z̃` of a
component of a geometric fibre, `G` is the pullback of the relative dualizing sheaf `ω`, and `E`
the set of points of `Z̃` over the nodes, where `G = Ω¹(E)` (forms with simple poles along `E`).
Combined with `deg Ω¹ = 2g - 2` (`CurvesField.DualityScheme.omegaDegree_of_smooth`) this gives the
degree `χ(G) - χ(𝒪) = 2g(Z̃) - 2 + #E` of `ω` on the component (`degree_eq_of_simplePoles`), the
numerical half of `cor:sm-omega-restriction-component` (blueprint `sm-omega-base-change.tex`;
restated in `sm-omega-base-change-fibre.tex` as `lem:sm-omega-bcf-euler-twist` and
`thm:sm-omega-bcf-degree`).

## Proof

The Čech complexes are computed on a finite affine cover adapted to `E`: the neighbourhoods `W_y`
(`y ∈ E`) and finitely many affine opens of the Noetherian open `Y ∖ E`. Every nonempty
intersection other than a single `W_y` misses `E`, so `α` is bijective there; the δ-formula for
Čech complexes of diagrams (`CurvesField.Genus.sum_homology_cech_of_injective`, the termwise
cokernel replacing the skyscraper sheaf `G / F`) gives
`χ(G) = χ(F) + ∑_{T ≠ ∅} (-1)^{#T+1} dim (G(U_T) / F(U_T)) = χ(F) + #E`, and every finite affine
cover computes `χ` of a quasi-coherent module (`Cohomology.cohomologyIsoCech`).

This is the additivity of `χ` along `0 → Ω¹ → Ω¹(E) → ⊕_{y ∈ E} κ(y) → 0` in the proof of
`cor:sm-omega-restriction-component`, i.e. the "classical computation" quoted by M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of Thm 1.1
(`semi-stable.tex`, T:1735–1737).
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Module Finset
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Omega.RosenlichtComponent

noncomputable section

variable {Y : Scheme.{u}} [CompactSpace Y]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))] {k : Type u} [Field k]
  (c : k →+* Γ(Y, ⊤))

/-- The cokernel `Γ(W, G) / α Γ(W, F)` of a morphism of modules on the sections over `W`, as a
`k`-module. -/
abbrev sectionsCoker {F G : Y.Modules} (α : F ⟶ G) (W : Y.Opens) : Type u :=
  sectionsModuleCat G c W le_top ⧸ LinearMap.range (sectionsMap c α W le_top).hom

section Cover

/-- **Every finite affine cover computes `χ`** of a quasi-coherent module: `χ(F)` (defined with the
chosen cover) is the alternating sum of the dimensions of the Čech cohomology of any finite affine
cover. -/
theorem eulerCharOf_eq_sum_cover (F : Y.Modules) [F.IsQuasicoherent] (𝒰 : FiniteAffineCover Y)
    [Fintype 𝒰.ι] :
    DualityScheme.eulerCharOf F c = ∑ i ∈ range (Fintype.card 𝒰.ι), (-1 : ℤ) ^ i *
      finrank k (cechCohomology F 𝒰.U c i) := by
  unfold DualityScheme.eulerCharOf
  rw [Genus.homologyEulerChar_eq_sum _ (Fintype.card 𝒰.ι)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    exact (cohomologyIsoCech F c 𝒰 i).toLinearEquiv.finrank_eq
  · intro i hi
    have hz := isZero_cechCohomology_of_card_le F 𝒰.U c i hi
    have : Subsingleton (cechCohomology F 𝒰.U c i) := ModuleCat.subsingleton_of_isZero hz
    exact (cohomologyIsoCech F c 𝒰 i).toLinearEquiv.toEquiv.subsingleton

end Cover

section Adapted

variable [NoetherianSpace Y]

omit [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
  [NoetherianSpace Y] in
/-- A finite set of closed points is closed. -/
theorem isClosed_finset (E : Finset Y) (hEc : ∀ y ∈ E, IsClosed ({y} : Set Y)) :
    IsClosed (E : Set Y) := by
  have : (E : Set Y) = ⋃ y ∈ E, ({y} : Set Y) := by ext; simp
  rw [this]
  exact isClosed_biUnion_finset hEc

omit [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))] in
/-- The complement of a finite set of closed points is covered by finitely many affine opens
missing it. -/
theorem exists_finite_affine_cover_compl (E : Finset Y) (hEc : ∀ y ∈ E, IsClosed ({y} : Set Y)) :
    ∃ (t : Finset ↥((E : Set Y)ᶜ)) (U : ↥((E : Set Y)ᶜ) → Y.Opens),
      (∀ z, IsAffineOpen (U z)) ∧ (∀ z, (z : Y) ∈ U z) ∧ (∀ z, ∀ y ∈ E, y ∉ U z) ∧
      (E : Set Y)ᶜ ⊆ ⋃ z ∈ t, (U z : Set Y) := by
  have hopen : IsOpen ((E : Set Y)ᶜ) := (isClosed_finset E hEc).isOpen_compl
  have hex : ∀ z : ↥((E : Set Y)ᶜ), ∃ W : Y.Opens, IsAffineOpen W ∧ (z : Y) ∈ W ∧
      (W : Set Y) ⊆ (E : Set Y)ᶜ := by
    intro z
    obtain ⟨W, hW, hzW, hWE⟩ :=
      exists_isAffineOpen_mem_and_subset (x := (z : Y)) (U := ⟨_, hopen⟩) z.2
    exact ⟨W, hW, hzW, hWE⟩
  choose U hU hzU hUE using hex
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact ((E : Set Y)ᶜ)).elim_finite_subcover
    (fun z => (U z : Set Y)) (fun z => (U z).isOpen) (fun z hz =>
      Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩)
  refine ⟨t, U, hU, hzU, fun z y hy hyz => hUE z hyz hy, ?_⟩
  exact ht

/-- **`χ(G) = χ(F) + #E`** for a morphism `α : F ⟶ G` of quasi-coherent modules on a Noetherian
scheme over `k` with affine diagonal which is injective on affine opens, bijective on affine opens
missing the finite set `E` of closed points, and has one-dimensional cokernel on an affine
neighbourhood `W_y` of each `y ∈ E` with `W_y ∩ E = {y}` (blueprint
`lem:sm-omega-bcf-euler-twist`). If the cohomology of `F` is finite-dimensional, so is that
of `G`. -/
theorem eulerCharOf_eq_add_card {F G : Y.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (α : F ⟶ G) (E : Finset Y) (hEc : ∀ y ∈ E, IsClosed ({y} : Set Y))
    (hinj : ∀ W : Y.Opens, IsAffineOpen W → Function.Injective (α.app W))
    (hsurj : ∀ W : Y.Opens, IsAffineOpen W → (∀ y ∈ E, y ∉ W) → Function.Surjective (α.app W))
    (hloc : ∀ y ∈ E, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ (∀ z ∈ E, z ∈ W → z = y) ∧
      FiniteDimensional k (sectionsCoker c α W) ∧ finrank k (sectionsCoker c α W) = 1)
    (hF : ∀ i, FiniteDimensional k (cohomology F c i)) :
    (∀ i, FiniteDimensional k (cohomology G c i)) ∧
      DualityScheme.eulerCharOf G c = DualityScheme.eulerCharOf F c + E.card := by
  classical
  -- the neighbourhoods of the points of `E`
  choose! W hW hyW hWE hWfd hWrk using hloc
  obtain ⟨t, U, hU, -, hUE, hcov⟩ := exists_finite_affine_cover_compl E hEc
  -- the adapted cover
  let ι : Type u := (E : Type u) ⊕ (t : Type u)
  let lo : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let V : ι → Y.Opens := fun i => Sum.elim (fun y : E => W y.1) (fun z : t => U z.1) i
  have hVaff : ∀ i, IsAffineOpen (V i) := by
    rintro (y | z)
    · exact hW y.1 y.2
    · exact hU z.1
  have hVtop : ⨆ i, V i = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ E
    · exact Opens.mem_iSup.mpr ⟨Sum.inl ⟨x, hx⟩, hyW x hx⟩
    · obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hcov (show x ∈ (E : Set Y)ᶜ from hx))
      exact Opens.mem_iSup.mpr ⟨Sum.inr ⟨z, hz⟩, hxz⟩
  let 𝒰 : FiniteAffineCover Y := @FiniteAffineCover.mk Y ι lo inferInstance V hVtop
    (fun T hT => by
      simpa [Finset.inf_eq_iInf] using IsAffineOpen.biInf (T : Set ι) T.finite_toSet
        (Finset.coe_nonempty.mpr hT) (fun i _ => hVaff i))
  let _ : Fintype 𝒰.ι := inferInstanceAs (Fintype ι)
  -- the map of Čech diagrams
  let D₁ := cechDiagram F 𝒰.U c
  let D₂ := cechDiagram G 𝒰.U c
  let αd : D₁ ⟶ D₂ := sectionsDiagramMap c α (fun T => T.inf 𝒰.U)
    (fun _ _ h => Finset.inf_mono h) (fun _ => le_top)
  have haffT : ∀ T : Finset 𝒰.ι, T.Nonempty → IsAffineOpen (T.inf 𝒰.U) := 𝒰.isAffineOpen_inf
  -- the intersections other than a single `W_y` miss `E`
  have hmiss : ∀ T : Finset 𝒰.ι, T.Nonempty → (∀ y : E, T ≠ {Sum.inl y}) →
      ∀ y ∈ E, y ∉ T.inf 𝒰.U := by
    intro T hT hne y hy hyT
    rw [Genus.mem_finsetInf] at hyT
    apply hne ⟨y, hy⟩
    ext i
    simp only [Finset.mem_singleton]
    constructor
    · intro hi
      have := hyT i hi
      rcases i with ⟨y', hy'⟩ | ⟨z, hz⟩
      · have := hWE y' hy' y hy this
        subst this
        rfl
      · exact absurd this (hUE z y hy)
    · rintro rfl
      obtain ⟨j, hj⟩ := hT
      have := hyT j hj
      rcases j with ⟨y', hy'⟩ | ⟨z, hz⟩
      · have := hWE y' hy' y hy this
        subst this
        exact hj
      · exact absurd this (hUE z y hy)
  have hcoker0 : ∀ T : Finset 𝒰.ι, T.Nonempty → (∀ y : E, T ≠ {Sum.inl y}) →
      Subsingleton (D₂.obj T ⧸ LinearMap.range (αd.app T).hom) := by
    intro T hT hne
    have hs := hsurj _ (haffT T hT) (hmiss T hT hne)
    have hr : LinearMap.range (αd.app T).hom = ⊤ := LinearMap.range_eq_top.mpr hs
    rw [hr]
    infer_instance
  have hsing : ∀ y : E, ({Sum.inl y} : Finset 𝒰.ι).inf 𝒰.U = W y.1 := fun y => by
    simp [𝒰, V]
  have hcoker1 : ∀ y : E, FiniteDimensional k
      (D₂.obj {Sum.inl y} ⧸ LinearMap.range (αd.app {Sum.inl y}).hom) ∧
      finrank k (D₂.obj {Sum.inl y} ⧸ LinearMap.range (αd.app {Sum.inl y}).hom) = 1 := by
    intro y
    have key : ∀ W' : Y.Opens, W' = W y.1 →
        FiniteDimensional k (sectionsCoker c α W') ∧ finrank k (sectionsCoker c α W') = 1 := by
      rintro _ rfl
      exact ⟨hWfd y.1 y.2, hWrk y.1 y.2⟩
    exact key _ (hsing y)
  have hinj' : ∀ T : Finset 𝒰.ι, T.Nonempty → Function.Injective (αd.app T).hom :=
    fun T hT => hinj _ (haffT T hT)
  have hfin' : ∀ T : Finset 𝒰.ι, T.Nonempty →
      FiniteDimensional k (D₂.obj T ⧸ LinearMap.range (αd.app T).hom) := by
    intro T hT
    by_cases hne : ∀ y : E, T ≠ {Sum.inl y}
    · have := hcoker0 T hT hne
      infer_instance
    · push Not at hne
      obtain ⟨y, rfl⟩ := hne
      exact (hcoker1 y).1
  have h₁ : ∀ i, FiniteDimensional k ((subsetCechComplex.{u, u} D₁).homology i) := fun i =>
    Module.Finite.equiv (cohomologyIsoCech F c 𝒰 i).toLinearEquiv
  obtain ⟨h₂, hsum⟩ := Genus.sum_homology_cech_of_injective (α := αd) hinj' hfin'
  refine ⟨fun i => ?_, ?_⟩
  · have : FiniteDimensional k (cechCohomology G 𝒰.U c i) := h₂ i
    exact Module.Finite.equiv (cohomologyIsoCech G c 𝒰 i).toLinearEquiv.symm
  rw [eulerCharOf_eq_sum_cover c G 𝒰, eulerCharOf_eq_sum_cover c F 𝒰]
  change ∑ i ∈ range (Fintype.card 𝒰.ι), (-1 : ℤ) ^ i *
      finrank k ((subsetCechComplex.{u, u} D₂).homology i) = ∑ i ∈ range (Fintype.card 𝒰.ι),
      (-1 : ℤ) ^ i * finrank k ((subsetCechComplex.{u, u} D₁).homology i) + _
  rw [hsum]
  congr 1
  -- the cokernel sum is `#E`
  let g : E → Finset 𝒰.ι := fun y => {Sum.inl y}
  have hg : ∀ y ∈ (Finset.univ : Finset E), ∀ y' ∈ (Finset.univ : Finset E), g y = g y' →
      y = y' := fun y _ y' _ h => by simpa [g] using h
  let S : Finset (Finset 𝒰.ι) := (Finset.univ : Finset E).image g
  have hS : S ⊆ univ.filter (fun T : Finset 𝒰.ι => T.Nonempty) := by
    intro T hT
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.singleton_nonempty _⟩
  rw [← Finset.sum_subset hS]
  · rw [Finset.sum_image hg]
    have hone : ∀ y : E, (-1 : ℤ) ^ ((g y).card + 1) *
        (finrank k (D₂.obj (g y) ⧸ LinearMap.range (αd.app (g y)).hom) : ℤ) = 1 := by
      intro y
      rw [(hcoker1 y).2]
      simp [g]
    rw [Finset.sum_congr rfl fun y _ => hone y]
    simp
  · intro T hT hTS
    have hTne : T.Nonempty := (Finset.mem_filter.mp hT).2
    have hne : ∀ y : E, T ≠ {Sum.inl y} := by
      intro y hy
      apply hTS
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hy.symm⟩
    have := hcoker0 T hTne hne
    rw [finrank_zero_of_subsingleton]
    simp

end Adapted

section Degree

variable {Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (q : Y ⟶ Spec (.of K))
  [IsIntegral Y] [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
  [Smooth q] [NoetherianSpace Y]

/-- **The degree of a twist of `Ω¹` by finitely many simple points** on a smooth, normal,
projective integral curve `Y` over `K = K̄` (blueprint `thm:sm-omega-bcf-degree`): if
`α : Ω¹_{Y/K} ⟶ G` is injective on affine opens, bijective on affine opens missing the finite set
`E` of closed points, and has one-dimensional cokernel on an affine neighbourhood `W_y` of every
`y ∈ E` with `W_y ∩ E = {y}` (i.e. `G = Ω¹_{Y/K}(E)`), then
`deg G = χ(G) - χ(𝒪_Y) = 2 p_a(Y) - 2 + #E`. -/
theorem degree_eq_of_simplePoles (hp : IsProjectiveOver q) (hdim : topologicalKrullDim Y ≤ 1)
    (hpt : ∃ y : Y, y ≠ genericPoint Y) (hnormal : IsNormalScheme Y)
    {G : Y.Modules} [G.IsQuasicoherent] (α : relativeDifferentials q ⟶ G) (E : Finset Y)
    (hEc : ∀ y ∈ E, IsClosed ({y} : Set Y))
    (hinj : ∀ W : Y.Opens, IsAffineOpen W → Function.Injective (α.app W))
    (hsurj : ∀ W : Y.Opens, IsAffineOpen W → (∀ y ∈ E, y ∉ W) → Function.Surjective (α.app W))
    (hloc : ∀ y ∈ E, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ (∀ z ∈ E, z ∈ W → z = y) ∧
      FiniteDimensional K (sectionsCoker (structureCoeff q) α W) ∧
      finrank K (sectionsCoker (structureCoeff q) α W) = 1) :
    (∀ i, FiniteDimensional K (cohomology G (structureCoeff q) i)) ∧
      DualityScheme.eulerCharOf G (structureCoeff q) - Genus.eulerChar Y (structureCoeff q) =
        2 * Genus.arithmeticGenus Y (structureCoeff q) - 2 + E.card := by
  have htf := DualityScheme.isTorsionFree_sections_of_smooth' q
  have hF : ∀ i, FiniteDimensional K (cohomology (relativeDifferentials q) (structureCoeff q) i) :=
    fun i => (DualityScheme.finiteDimensional_cohomology_of_isProjectiveOver q hp hdim hpt hnormal
      htf i).2
  obtain ⟨hG, hχ⟩ := eulerCharOf_eq_add_card (structureCoeff q) α E hEc hinj hsurj hloc hF
  refine ⟨hG, ?_⟩
  have hdeg := (DualityScheme.omegaDegree_of_smooth q hp hdim hpt hnormal).2.2.2
  rw [hχ]
  linarith

omit [NoetherianSpace Y] in
/-- The genus of a smooth normal projective curve over `K = K̄` is nonnegative
(`p_a = h⁰(Ω¹)`). -/
theorem arithmeticGenus_nonneg (hp : IsProjectiveOver q) (hdim : topologicalKrullDim Y ≤ 1)
    (hpt : ∃ y : Y, y ≠ genericPoint Y) (hnormal : IsNormalScheme Y) :
    0 ≤ Genus.arithmeticGenus Y (structureCoeff q) := by
  rw [← (DualityScheme.omegaDegree_of_smooth q hp hdim hpt hnormal).2.1]
  exact Nat.cast_nonneg _

omit [IsAlgClosed K] [IsIntegral Y] [Smooth q] in
/-- **Twisting by marks** (blueprint `cor:sm-omega-bcf-degree-marks`): if `G` has degree
`2 p_a(Y) - 2 + n` and finite-dimensional cohomology, and `α' : G ⟶ G'` is a twist at a finite set
`M` of closed points (injective on affine opens, bijective on affine opens missing `M`, with
one-dimensional cokernel near each point of `M`), then `G'` has degree `2 p_a(Y) - 2 + n + #M`.
For `G = ν^* ω` and `M` the points over the marks `D`, `G' = ν^*(ω(D))`. -/
theorem degree_twist {G G' : Y.Modules} [G.IsQuasicoherent] [G'.IsQuasicoherent] (α' : G ⟶ G')
    (M : Finset Y) (hMc : ∀ y ∈ M, IsClosed ({y} : Set Y))
    (hinj : ∀ W : Y.Opens, IsAffineOpen W → Function.Injective (α'.app W))
    (hsurj : ∀ W : Y.Opens, IsAffineOpen W → (∀ y ∈ M, y ∉ W) → Function.Surjective (α'.app W))
    (hloc : ∀ y ∈ M, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ (∀ z ∈ M, z ∈ W → z = y) ∧
      FiniteDimensional K (sectionsCoker (structureCoeff q) α' W) ∧
      finrank K (sectionsCoker (structureCoeff q) α' W) = 1)
    (hG : ∀ i, FiniteDimensional K (cohomology G (structureCoeff q) i)) (n : ℤ)
    (hdeg : DualityScheme.eulerCharOf G (structureCoeff q) - Genus.eulerChar Y (structureCoeff q) =
      2 * Genus.arithmeticGenus Y (structureCoeff q) - 2 + n) :
    (∀ i, FiniteDimensional K (cohomology G' (structureCoeff q) i)) ∧
      DualityScheme.eulerCharOf G' (structureCoeff q) - Genus.eulerChar Y (structureCoeff q) =
        2 * Genus.arithmeticGenus Y (structureCoeff q) - 2 + n + M.card := by
  obtain ⟨hG', hχ⟩ := eulerCharOf_eq_add_card (structureCoeff q) α' M hMc hinj hsurj hloc hG
  exact ⟨hG', by rw [hχ]; linarith⟩

end Degree

/-- **Positivity of `2g - 2 + n`** (the stability arithmetic): for `g ≥ 0`, `2g - 2 + n > 0`
unless `g = 0` and `n ≤ 2`, or `g = 1` and `n = 0`. -/
theorem two_mul_sub_two_add_pos_iff {g : ℤ} (hg : 0 ≤ g) (n : ℕ) :
    0 < 2 * g - 2 + n ↔ ¬ (g = 0 ∧ n ≤ 2) ∧ ¬ (g = 1 ∧ n = 0) := by
  constructor
  · rintro h
    refine ⟨fun ⟨h0, hn⟩ => ?_, fun ⟨h1, hn⟩ => ?_⟩
    · subst h0; omega
    · subst h1; subst hn; omega
  · rintro ⟨h0, h1⟩
    by_cases hg0 : g = 0
    · subst hg0
      have : 2 < n := by
        by_contra hn
        exact h0 ⟨rfl, by omega⟩
      omega
    · by_cases hg1 : g = 1
      · subst hg1
        have : n ≠ 0 := fun hn => h1 ⟨rfl, hn⟩
        omega
      · omega

end

end DeJongAlterations.StableModification.Omega.RosenlichtComponent
