/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeGenerated
import DeJongAlterations.StableModification.Projectivity.RelativeSerre
import DeJongAlterations.StableModification.Projectivity.RelativeAssembly
import DeJongAlterations.StableModification.Projectivity.SectionsMap
import DeJongAlterations.StableModification.CurvesField.AmpleSection

/-!
# The local-to-global theorem, core form (`thm:sm-ltg`)

Blueprint `sm-projectivity-relative.tex`, `thm:sm-ltg` (PLAN-OM3 §3, Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), `semi-stable.tex` T:1713–1749:
"relative ampleness can be checked separately on each fiber"). Let `Y` be projective over a ring
`R`, `β : X ⟶ Y` proper and `𝓛` line-bundle data on `X`. Suppose that for every closed point
`y ∈ Y`:

* (`hcover`) `y` lies in the affine open `W` of some `TwoAffineCover β L` (`β⁻¹ W` is covered by
  two affines with affine intersection, with finite cokernels of the difference maps);
* (`hdim`) the fibre `X_y` has dimension at most one;
* (`hL`) `𝓛` is ample on `X_y` (OM3A's Serre-form `FiberAmple`);
* (`hsec`) some `𝓛^n|_{X_y}`, `n > 0`, has a section which does not vanish at the non-closed
  points of `X_y` and vanishes at a specialization of each of them.

Then `β` is projective relative to `Y ⟶ Spec R` (`isRelativelyProjective_of_twoAffineCovers`).

## Proof

Let `𝓝 = β^* 𝒪_Y(d)` (the hyperplane bundle of projective coordinates on `Y`, OM3A's
`hyperplane`). (1) Generation around each closed fibre (`TwoAffineCover.exists_generating`) and
Serre's extension lemma (`exists_extension_of_nonvanishingLocus`) give, for all exponents `M`
divisible by some `M₀` and all `E ≫ 0`, finitely many global sections of `𝓛^M ⊗ 𝓝^E` without
common zero (`GenCover.exists_generates`). (2) At a closed point `y`, a lift of a power of the
section of `hsec` (`TwoAffineCover.exists_lift`), extended by Serre's lemma, is added; the map
`h : X ⟶ ℙᴺ_R` given by these sections is constant on no one-dimensional component of `X_y`
(`finite_preimage_of_separating`), so `(β, h)` is quasi-finite over a neighbourhood of `y`
(`exists_open_quasiFiniteAt`). (3) Finitely many such maps make `β` relatively projective
(`isRelativelyProjective_of_quasiFiniteAt`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open DeJong Cohomology

variable {X Y : Scheme.{u}}

/-! ### Morphisms to projective space from finite generating families -/

section Family

variable {R : Type u} [CommRing R]

/-- A finite family of global sections without common zero gives a morphism to projective space
whose coordinate charts pull back to the non-vanishing loci of the members of the family. -/
theorem exists_toProjectiveSpace {B : LineBundleData X} (p : X ⟶ Spec (.of R)) {ι : Type u}
    [Fintype ι] (T : ι → B.Sections 1 ⊤) (hT : ∀ x, ∃ i, x ∈ (T i).nonvanishingLocus) :
    ∃ (N : ℕ) (h : X ⟶ projectiveSpace R N), h ≫ projectiveSpaceStructure R N = p ∧
      ∀ i, ∃ a : Fin (N + 1), h ⁻¹ᵁ Geometry.ProjectiveIdeal.nativeCoordinateOpen a =
        (T i).nonvanishingLocus := by
  classical
  let e := Fintype.equivFin ι
  let s : Fin (Fintype.card ι + 1) → B.Sections 1 ⊤ := fun a =>
    if h : (a : ℕ) < Fintype.card ι then T (e.symm ⟨a, h⟩) else 0
  have hs_eq : ∀ i, s ⟨e i, (e i).2.trans (Nat.lt_succ_self _)⟩ = T i := by
    intro i
    simp only [s, (e i).2, dif_pos]
    congr 1
    exact e.symm_apply_apply i
  have hs : LineBundleData.Generates s := by
    intro x
    obtain ⟨i, hi⟩ := hT x
    exact ⟨⟨e i, (e i).2.trans (Nat.lt_succ_self _)⟩, by rw [hs_eq]; exact hi⟩
  refine ⟨Fintype.card ι, LineBundleData.toProjectiveSpace p hs,
    LineBundleData.toProjectiveSpace_structure p hs, fun i =>
      ⟨⟨e i, (e i).2.trans (Nat.lt_succ_self _)⟩, ?_⟩⟩
  rw [LineBundleData.toProjectiveSpace_preimage_coordinate, hs_eq]

end Family

/-! ### Generation data -/

variable (β : X ⟶ Y) (L : LineBundleData X)

/-- **Generation data** for `β` and `𝓛` with twisting bundle `𝓝`: finitely many opens `V p`
covering `Y`, each inside the affine open of a `TwoAffineCover`, with sections `τ p k` of
`𝓛^{m p}` over `β⁻¹ W p` generating `𝓛^{m p}` over `β⁻¹ V p`, and global sections `f p` of `𝓝`
with non-vanishing locus `β⁻¹ V p`. -/
structure GenCover (N : LineBundleData X) where
  /-- The index type. -/
  P : Type u
  [fintype : Fintype P]
  /-- The two-affine data. -/
  D : P → TwoAffineCover β L
  /-- The opens of `Y`. -/
  V : P → Y.Opens
  le_W : ∀ p, V p ≤ (D p).W
  /-- The exponents. -/
  m : P → ℕ
  pos : ∀ p, 0 < m p
  /-- The finite index sets of the generating sections. -/
  K : P → Finset X
  /-- The generating sections. -/
  τ : ∀ p, X → L.Sections (m p) (β ⁻¹ᵁ (D p).W)
  gen : ∀ p x, β x ∈ V p → ∃ k ∈ K p, x ∈ (τ p k).nonvanishingLocus
  /-- The sections of `𝓝`. -/
  f : P → N.Sections 1 ⊤
  nonvanishingLocus_f : ∀ p, (f p).nonvanishingLocus = β ⁻¹ᵁ V p
  cover : ∀ y, ∃ p, y ∈ V p

attribute [instance] GenCover.fintype

namespace GenCover

variable {β L} {N : LineBundleData X} (G : GenCover β L N)

/-- The product of the exponents. -/
def M₀ : ℕ := ∏ p, G.m p

lemma M₀_pos : 0 < G.M₀ := Finset.prod_pos fun p _ => G.pos p

lemma dvd_M₀ (p : G.P) : G.m p ∣ G.M₀ := Finset.dvd_prod_of_mem _ (Finset.mem_univ p)

lemma le_f (p : G.P) : (G.f p).nonvanishingLocus ≤ β ⁻¹ᵁ (G.D p).W := by
  rw [G.nonvanishingLocus_f]
  exact β.preimage_mono (G.le_W p)

/-- A section of `𝓛^{m p}` over `β⁻¹ W p` raised to the exponent `M` (a multiple of `m p`) and
restricted to `D(f p)`, as a section of `(𝓛^M)^1`. -/
def localPow (p : G.P) {M : ℕ} (hM : G.m p ∣ M) (τ : L.Sections (G.m p) (β ⁻¹ᵁ (G.D p).W)) :
    (L.pow (M : ℤ)).Sections 1 (G.f p).nonvanishingLocus :=
  (((τ.npow (M / G.m p)).cast (by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hM])).restrict (G.le_f p)).toPowOne

lemma le_nonvanishingLocus_localPow (p : G.P) {M : ℕ} (hM : G.m p ∣ M)
    (τ : L.Sections (G.m p) (β ⁻¹ᵁ (G.D p).W)) :
    (G.f p).nonvanishingLocus ⊓ τ.nonvanishingLocus ≤ (G.localPow p hM τ).nonvanishingLocus := by
  rw [localPow, LineBundleData.Sections.nonvanishingLocus_toPowOne,
    LineBundleData.Sections.nonvanishingLocus_restrict,
    LineBundleData.Sections.nonvanishingLocus_cast]
  exact inf_le_inf_left _ (LineBundleData.Sections.nonvanishingLocus_le_npow _ _)

variable [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **Global generation** (blueprint `thm:sm-ltg`, step 3): for every exponent `M = M₀ k` and
all `E ≫ 0`, the bundle `𝓛^M ⊗ 𝓝^E` has finitely many global sections without common zero, given
global sections `e c` of `𝓝` without common zero. -/
theorem exists_generates {κ : Type u} [Fintype κ] (e : κ → N.Sections 1 ⊤)
    (he : ∀ x, ∃ c, x ∈ (e c).nonvanishingLocus) (k : ℕ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∃ (ι : Type u) (_ : Fintype ι)
      (T : ι → ((L.pow ((G.M₀ * k : ℕ) : ℤ)).mul (N.pow (E : ℤ))).Sections 1 ⊤),
        ∀ x, ∃ i, x ∈ (T i).nonvanishingLocus := by
  classical
  have hdvd : ∀ p, G.m p ∣ G.M₀ * k := fun p => (G.dvd_M₀ p).mul_right k
  have hS : ∀ (pl : Σ p, G.K p), ∃ (r : ℕ)
      (T : ((L.pow ((G.M₀ * k : ℕ) : ℤ)).mul (N.pow (r : ℤ))).Sections 1 ⊤),
      T.nonvanishingLocus ⊓ (G.f pl.1).nonvanishingLocus =
        (G.localPow pl.1 (hdvd pl.1) (G.τ pl.1 pl.2)).nonvanishingLocus := fun pl =>
    LineBundleData.exists_extension_of_nonvanishingLocus (G.f pl.1) _
  choose r T hT using hS
  refine ⟨Finset.univ.sup r, fun E hE => ?_⟩
  have hrE : ∀ pl, r pl ≤ E := fun pl => (Finset.le_sup (Finset.mem_univ pl)).trans hE
  have hcast : ∀ pl, (r pl : ℤ) + 1 * ((E - r pl : ℕ) : ℤ) = (E : ℤ) := fun pl => by
    rw [one_mul, Nat.cast_sub (hrE pl)]
    ring
  refine ⟨(Σ p, G.K p) × κ, inferInstance, fun i =>
    ((T i.1).mulPow ((e i.2).npow (E - r i.1))).castPow (hcast i.1), fun x => ?_⟩
  obtain ⟨p, hp⟩ := G.cover (β x)
  obtain ⟨l, hl, hxl⟩ := G.gen p x hp
  obtain ⟨c, hc⟩ := he x
  refine ⟨(⟨p, ⟨l, hl⟩⟩, c), ?_⟩
  rw [LineBundleData.Sections.nonvanishingLocus_castPow,
    LineBundleData.Sections.nonvanishingLocus_mulPow]
  have hxf : x ∈ (G.f p).nonvanishingLocus := by
    rw [G.nonvanishingLocus_f]
    exact hp
  refine ⟨?_, LineBundleData.Sections.nonvanishingLocus_le_npow _ _ hc⟩
  have : x ∈ (G.localPow p (hdvd p) (G.τ p l)).nonvanishingLocus :=
    G.le_nonvanishingLocus_localPow p (hdvd p) _ ⟨hxf, hxl⟩
  rw [← hT ⟨p, ⟨l, hl⟩⟩] at this
  exact this.1

end GenCover

/-! ### Existence of generation data -/

section Existence

variable {β L}

/-- In a quasi-compact scheme every point lies in every open containing some closed point of its
closure: if opens `O y` around the closed points are given, they cover. -/
lemma exists_closed_mem_of_forall [CompactSpace Y] (O : ∀ y : Y, IsClosed ({y} : Set Y) → Y.Opens)
    (hO : ∀ y hy, y ∈ O y hy) (y' : Y) : ∃ (y : Y) (hy : IsClosed ({y} : Set Y)), y' ∈ O y hy := by
  obtain ⟨y, hy, hycl⟩ := (isClosed_closure (s := {y'})).exists_closed_singleton
    ⟨y', subset_closure rfl⟩
  exact ⟨y, hycl, (specializes_iff_mem_closure.mpr hy).mem_open (O y hycl).isOpen (hO y hycl)⟩

/-- **Generation data exist** (blueprint `lem:sm-ltg-generated`, global form), with twisting bundle
`(β^* 𝓝_Y)^d` for a line bundle `𝓝_Y` on `Y` with global sections `e c` with affine
non-vanishing loci covering `Y`. -/
theorem exists_genCover [IsProper β] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (NY : LineBundleData Y) {κ : Type u}
    (e : κ → NY.Sections 1 ⊤) (he : ∀ c, IsAffineOpen (e c).nonvanishingLocus)
    (hecov : ∀ y, ∃ c, y ∈ (e c).nonvanishingLocus)
    (hcover : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ D : TwoAffineCover β L, y ∈ D.W)
    (hL : ∀ y : Y, IsClosed ({y} : Set Y) → FiberAmple L β y) :
    ∃ d : ℕ, 0 < d ∧ Nonempty (GenCover β L ((NY.pullback β).pow (d : ℤ))) := by
  classical
  have hgen : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ (D : TwoAffineCover β L) (m : ℕ)
      (K : Finset X) (τ : X → L.Sections m (β ⁻¹ᵁ D.W)) (O : Y.Opens), 0 < m ∧ y ∈ O ∧
        O ≤ D.W ∧ ∀ x, β x ∈ O → ∃ k ∈ K, x ∈ (τ k).nonvanishingLocus := by
    intro y hy
    obtain ⟨D, hyD⟩ := hcover y hy
    obtain ⟨m₀, hm₀⟩ := D.exists_generating hyD hy (hL y hy)
    obtain ⟨K, τ, O, hyO, hOW, hO⟩ := hm₀ (m₀ + 1) (Nat.le_succ m₀)
    exact ⟨D, m₀ + 1, K, τ, O, Nat.succ_pos _, hyO, hOW, hO⟩
  choose D m K τ O hm hyO hOW hO using hgen
  have hbasic : ∀ y' : Y, ∃ (y : Y) (hy : IsClosed ({y} : Set Y)) (d : ℕ)
      (F : NY.Sections (d : ℤ) ⊤), 0 < d ∧ y' ∈ F.nonvanishingLocus ∧
        F.nonvanishingLocus ≤ O y hy := by
    intro y'
    obtain ⟨y, hy, hy'⟩ := exists_closed_mem_of_forall O hyO y'
    obtain ⟨c, hc⟩ := hecov y'
    obtain ⟨d, F, hd, hF, hFO⟩ := LineBundleData.exists_section_mem_le (e c) (he c) hc hy'
    exact ⟨y, hy, d, F, hd, hF, hFO⟩
  choose yc hyc d F hd hF hFO using hbasic
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun y' => ((F y').nonvanishingLocus : Set Y))
    (fun y' => (F y').nonvanishingLocus.isOpen) (fun y' _ => Set.mem_iUnion.mpr ⟨y', hF y'⟩)
  let d₀ : ℕ := ∏ p : S, d p
  have hd₀ : 0 < d₀ := Finset.prod_pos fun p _ => hd p
  have hdvd : ∀ p : S, d p ∣ d₀ := fun p => Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
  have hcast : ∀ p : S, ((d p : ℕ) : ℤ) * ((d₀ / d p : ℕ) : ℤ) = ((d₀ : ℕ) : ℤ) := fun p => by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd p)]
  have hpos : ∀ p : S, 0 < d₀ / d p := fun p => Nat.div_pos (Nat.le_of_dvd hd₀ (hdvd p)) (hd p)
  let fs : ∀ p : S, ((NY.pullback β).pow ((d₀ : ℕ) : ℤ)).Sections 1 ⊤ := fun p =>
    ((((F p).npow (d₀ / d p)).cast (hcast p)).pullback β |>.restrict
      (le_of_eq (Scheme.Hom.preimage_top β).symm)).toPowOne
  have hfs : ∀ p : S, (fs p).nonvanishingLocus = β ⁻¹ᵁ (F p).nonvanishingLocus := fun p => by
    simp only [fs, LineBundleData.Sections.nonvanishingLocus_toPowOne,
      LineBundleData.Sections.nonvanishingLocus_restrict,
      LineBundleData.Sections.nonvanishingLocus_pullback,
      LineBundleData.Sections.nonvanishingLocus_cast,
      LineBundleData.Sections.nonvanishingLocus_npow _ (hpos p), top_inf_eq]
  refine ⟨d₀, hd₀, ⟨{
    P := S
    D := fun p => D (yc p) (hyc p)
    V := fun p => (F p).nonvanishingLocus
    le_W := fun p => (hFO p).trans (hOW _ _)
    m := fun p => m (yc p) (hyc p)
    pos := fun p => hm _ _
    K := fun p => K (yc p) (hyc p)
    τ := fun p => τ (yc p) (hyc p)
    gen := fun p x hx => hO _ _ x (hFO p hx)
    f := fs
    nonvanishingLocus_f := hfs
    cover := fun y => by
      have := hS (Set.mem_univ y)
      simp only [Set.mem_iUnion] at this
      obtain ⟨y', hy', hy⟩ := this
      exact ⟨⟨y', hy'⟩, hy⟩ }⟩⟩

end Existence

/-! ### Quasi-finiteness around a fibre -/

section Separation

variable {β L} {R : Type u} [CommRing R] (pY : Y ⟶ Spec (.of R))

set_option backward.isDefEq.respectTransparency.types false in
/-- The scheme-theoretic fibre of a proper morphism is a Noetherian scheme. -/
lemma isNoetherian_fiber [IsProper β] (y : Y) : IsNoetherian (β.fiber y) := by
  have : LocallyOfFiniteType (β.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (β.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : CompactSpace (β.fiber y) :=
    QuasiCompact.compactSpace_of_compactSpace (β.fiberToSpecResidueField y)
  have : IsLocallyNoetherian (β.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (β.fiberToSpecResidueField y)
  exact ⟨⟩

lemma fiberι_apply_mem (y : Y) (z : β.fiber y) : β (β.fiberι y z) = y := by
  have : β.fiberι y z ∈ β ⁻¹' {y} := by
    rw [← Scheme.Hom.range_fiberι]
    exact ⟨z, rfl⟩
  exact this

namespace GenCover

variable {N : LineBundleData X} (G : GenCover β L N)
variable [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]

include G in
/-- **Quasi-finiteness around a fibre** (blueprint `lem:sm-ltg-nonconstant`): at a closed point
`y` with one-dimensional fibre, fibre-ampleness and a section of some `𝓛^n|_{X_y}` vanishing at a
specialization of each non-closed point but at no non-closed point, there is an `R`-morphism
`h : X ⟶ ℙᴺ_R` with `(β, h)` quasi-finite over a neighbourhood of `y`. -/
theorem exists_quasiFiniteAt [IsProper β] [IsProper pY] {κ : Type u} [Fintype κ]
    (e : κ → N.Sections 1 ⊤) (U' : κ → Y.Opens)
    (he : ∀ c, (e c).nonvanishingLocus = β ⁻¹ᵁ U' c) (hU' : ∀ y, ∃ c, y ∈ U' c)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hdim : topologicalKrullDim (β.fiber y) ≤ 1)
    (hLy : FiberAmple L β y) {n : ℕ} (hn : 0 < n) (s : (L.pullback (β.fiberι y)).Sections n ⊤)
    (hgen : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) → x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
      ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    ∃ (Nn : ℕ) (h : X ⟶ projectiveSpace R Nn) (hh : h ≫ projectiveSpaceStructure R Nn = β ≫ pY)
      (O : Y.Opens), y ∈ O ∧ ∀ x, β x ∈ O → (pullback.lift β h hh.symm).QuasiFiniteAt x := by
  classical
  obtain ⟨p, hp⟩ := G.cover y
  have hyW : y ∈ (G.D p).W := G.le_W p hp
  obtain ⟨m₁, hlift⟩ := (G.D p).exists_lift hyW hy hLy
  set q : ℕ := G.M₀ * (m₁ + 1) with hq
  set k : ℕ := n * (m₁ + 1) with hk
  have hMq : (n : ℤ) * ((q : ℕ) : ℤ) = ((G.M₀ * k : ℕ) : ℤ) := by
    simp only [hq, hk]
    push_cast
    ring
  have hqpos : 0 < q := Nat.mul_pos G.M₀_pos (Nat.succ_pos _)
  have hM₁ : m₁ ≤ G.M₀ * k := by
    have h1 : 1 ≤ G.M₀ := G.M₀_pos
    have h2 : m₁ + 1 ≤ k := Nat.le_mul_of_pos_left _ hn
    calc m₁ ≤ m₁ + 1 := Nat.le_succ m₁
      _ ≤ k := h2
      _ ≤ G.M₀ * k := Nat.le_mul_of_pos_left _ h1
  let z : (L.pullback (β.fiberι y)).Sections ((G.M₀ * k : ℕ) : ℤ) ⊤ := (s.npow q).cast hMq
  obtain ⟨σ, hσ⟩ := hlift (G.M₀ * k) hM₁ z
  -- the separating global section
  let t : (L.pow ((G.M₀ * k : ℕ) : ℤ)).Sections 1 (G.f p).nonvanishingLocus :=
    (σ.restrict (G.le_f p)).toPowOne
  have ht : t.nonvanishingLocus = (G.f p).nonvanishingLocus ⊓ σ.nonvanishingLocus := by
    rw [LineBundleData.Sections.nonvanishingLocus_toPowOne,
      LineBundleData.Sections.nonvanishingLocus_restrict]
  obtain ⟨rs, Ts, hTs⟩ := LineBundleData.exists_extension_of_nonvanishingLocus (G.f p) t
  have he' : ∀ x, ∃ c, x ∈ (e c).nonvanishingLocus := fun x => by
    obtain ⟨c, hc⟩ := hU' (β x)
    exact ⟨c, by rw [he]; exact hc⟩
  obtain ⟨E₀, hE₀⟩ := G.exists_generates e he' k
  set E := max E₀ rs with hEdef
  obtain ⟨ι₀, _, T₀, hT₀⟩ := hE₀ E (le_max_left _ _)
  obtain ⟨c₀, hc₀⟩ := hU' y
  have hcast : (rs : ℤ) + 1 * ((E - rs : ℕ) : ℤ) = (E : ℤ) := by
    rw [one_mul, Nat.cast_sub (le_max_right _ _)]
    ring
  let Ts' := (Ts.mulPow ((e c₀).npow (E - rs))).castPow hcast
  -- on the fibre over `y`, `Ts'` vanishes exactly where `σ` does
  have hsep : ∀ x', β x' = y → (x' ∈ Ts'.nonvanishingLocus ↔ x' ∈ σ.nonvanishingLocus) := by
    intro x' hx'
    have hxf : x' ∈ (G.f p).nonvanishingLocus := by
      rw [G.nonvanishingLocus_f]
      change β x' ∈ G.V p
      rw [hx']
      exact hp
    have hxe : x' ∈ (e c₀).nonvanishingLocus := by
      rw [he]
      change β x' ∈ U' c₀
      rw [hx']
      exact hc₀
    rw [LineBundleData.Sections.nonvanishingLocus_castPow,
      LineBundleData.Sections.nonvanishingLocus_mulPow]
    constructor
    · rintro ⟨h1, -⟩
      have : x' ∈ Ts.nonvanishingLocus ⊓ (G.f p).nonvanishingLocus := ⟨h1, hxf⟩
      rw [hTs, ht] at this
      exact this.2
    · intro h1
      refine ⟨?_, LineBundleData.Sections.nonvanishingLocus_le_npow _ _ hxe⟩
      have : x' ∈ t.nonvanishingLocus := by rw [ht]; exact ⟨hxf, h1⟩
      rw [← hTs] at this
      exact this.1
  -- the morphism
  let T : Option ι₀ → ((L.pow ((G.M₀ * k : ℕ) : ℤ)).mul (N.pow (E : ℤ))).Sections 1 ⊤ :=
    fun o => o.elim Ts' T₀
  obtain ⟨Nn, h, hh, ha⟩ := exists_toProjectiveSpace (β ≫ pY) T (fun x => by
    obtain ⟨i, hi⟩ := hT₀ x
    exact ⟨some i, hi⟩)
  obtain ⟨a₀, ha₀⟩ := ha none
  refine ⟨Nn, h, hh, ?_⟩
  set Ψ := pullback.lift β h hh.symm with hΨ
  have hΨβ : Ψ ≫ pullback.fst pY (projectiveSpaceStructure R Nn) = β := pullback.lift_fst _ _ _
  have hΨh : Ψ ≫ pullback.snd pY (projectiveSpaceStructure R Nn) = h := pullback.lift_snd _ _ _
  have : LocallyOfFiniteType (Ψ ≫ pullback.fst pY (projectiveSpaceStructure R Nn)) := by
    rw [hΨβ]; infer_instance
  have : LocallyOfFiniteType Ψ := locallyOfFiniteType_of_comp Ψ (pullback.fst _ _)
  have : IsProper (h ≫ projectiveSpaceStructure R Nn) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h (projectiveSpaceStructure R Nn)
  -- the fibre
  have : IsNoetherian (β.fiber y) := isNoetherian_fiber y
  have hdim' := CurvesField.Ample.eq_or_eq_of_topologicalKrullDim_le_one hdim
  have hce : Topology.IsClosedEmbedding (β.fiberι y) :=
    ⟨(β.fiberι y).isEmbedding, by rw [Scheme.Hom.range_fiberι]; exact hy.preimage β.continuous⟩
  let g : β.fiber y → projectiveSpace R Nn := fun w => h (β.fiberι y w)
  have hg : Continuous g := h.continuous.comp (β.fiberι y).continuous
  have hgcl : ∀ w, IsClosed ({w} : Set (β.fiber y)) → IsClosed ({g w} : Set (projectiveSpace R Nn)) := by
    intro w hw
    have h1 := hce.isClosedMap _ hw
    rw [Set.image_singleton] at h1
    have h2 := h.isClosedMap _ h1
    rwa [Set.image_singleton] at h2
  let Dset : Set (β.fiber y) := β.fiberι y ⁻¹' (Ts'.nonvanishingLocus : Set X)
  have hmemD : ∀ w, w ∈ Dset ↔ g w ∈ Geometry.ProjectiveIdeal.nativeCoordinateOpen a₀ := by
    intro w
    change β.fiberι y w ∈ (T none).nonvanishingLocus ↔ _
    rw [← ha₀]
    rfl
  have hDσ : ∀ w, w ∈ Dset ↔ w ∈ s.nonvanishingLocus := by
    intro w
    change β.fiberι y w ∈ Ts'.nonvanishingLocus ↔ _
    rw [hsep _ (fiberι_apply_mem y w)]
    have h1 : w ∈ (σ.pullback (β.fiberι y)).nonvanishingLocus ↔
        β.fiberι y w ∈ σ.nonvanishingLocus := by
      rw [LineBundleData.Sections.nonvanishingLocus_pullback]
      rfl
    rw [← h1, hσ, LineBundleData.Sections.nonvanishingLocus_restrict,
      LineBundleData.Sections.nonvanishingLocus_cast,
      LineBundleData.Sections.nonvanishingLocus_npow _ hqpos]
    exact ⟨fun h2 => h2.2, fun h2 => ⟨LineBundleData.top_le_fiber_preimage β y hyW trivial, h2⟩⟩
  have hqf : ∀ x, β x = y → Ψ.QuasiFiniteAt x := by
    intro x hx
    apply quasiFiniteAt_of_finite Ψ x
    have hfin : (g ⁻¹' {h x}).Finite := finite_preimage_of_separating hdim' g hg hgcl Dset
      (fun w w' hww' => by rw [hmemD, hmemD, hww'])
      (fun w hw => (hDσ w).mpr (hgen w hw))
      (fun w hw => by
        obtain ⟨z', hwz', hz'⟩ := hzero w hw
        exact ⟨z', hwz', fun h2 => hz' ((hDσ z').mp h2)⟩) (h x)
    refine (hfin.image (β.fiberι y)).subset ?_
    intro x' hx'
    have hx'' : Ψ x' = Ψ x := hx'
    have hβ : β x' = β x := by
      rw [← hΨβ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx'']
    have hh' : h x' = h x := by
      rw [← hΨh, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx'']
    obtain ⟨w, rfl⟩ : x' ∈ Set.range (β.fiberι y) := by
      rw [Scheme.Hom.range_fiberι]
      exact hβ.trans hx
    exact ⟨w, hh', rfl⟩
  exact exists_open_quasiFiniteAt β Ψ y hqf

end GenCover

end Separation

/-! ### The local-to-global theorem -/

section Main

variable {β L} {R : Type u} [CommRing R]

/-- **The local-to-global theorem**, core form (blueprint `thm:sm-ltg`): over a projective base,
a proper morphism which is covered by two-affine data around every closed point, with fibres of
dimension at most one over the closed points, on which `𝓛` is ample and has a section of positive
degree on every one-dimensional component, is relatively projective. -/
theorem isRelativelyProjective_of_twoAffineCovers (pY : Y ⟶ Spec (.of R))
    (hY : IsProjectiveOver pY) [IsProper β]
    (hcover : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ D : TwoAffineCover β L, y ∈ D.W)
    (hdim : ∀ y : Y, IsClosed ({y} : Set Y) → topologicalKrullDim (β.fiber y) ≤ 1)
    (hL : ∀ y : Y, IsClosed ({y} : Set Y) → FiberAmple L β y)
    (hsec : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ (n : ℕ)
      (s : (L.pullback (β.fiberι y)).Sections n ⊤), 0 < n ∧
        (∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) → x ∈ s.nonvanishingLocus) ∧
        (∀ x : β.fiber y, ¬ IsClosed ({x} : Set (β.fiber y)) →
          ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus)) :
    IsRelativelyProjective pY β := by
  classical
  have : IsProper pY := hY.isProper
  have : CompactSpace Y := CurvesField.Ample.compactSpace_of_quasiCompact pY
  have : IsAffineHom (pullback.diagonal (terminal.from Y)) :=
    CurvesField.Ample.isAffineHom_diagonal_of_isSeparated pY
  have : CompactSpace X := CurvesField.Ample.compactSpace_of_quasiCompact (β ≫ pY)
  have : IsAffineHom (pullback.diagonal (terminal.from X)) :=
    CurvesField.Ample.isAffineHom_diagonal_of_isSeparated (β ≫ pY)
  obtain ⟨DY⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hY
  let NY := LineBundleData.hyperplane DY
  let eY : DY.ι → NY.Sections 1 ⊤ := LineBundleData.coordSection DY
  have heY : ∀ c, (eY c).nonvanishingLocus = DY.U c :=
    LineBundleData.nonvanishingLocus_coordSection DY
  have hU' : ∀ y, ∃ c, y ∈ DY.U c := fun y => by
    have hy : y ∈ (⊤ : Y.Opens) := trivial
    rw [← DY.iSup_eq_top] at hy
    exact Opens.mem_iSup.mp hy
  obtain ⟨d, hd, ⟨G⟩⟩ := exists_genCover NY eY (fun c => by rw [heY]; exact DY.isAffineOpen c)
    (fun y => by
      obtain ⟨c, hc⟩ := hU' y
      exact ⟨c, by rw [heY]; exact hc⟩) hcover hL
  -- coordinate sections of `𝓝 = (β^* 𝓝_Y)^d`
  let e : DY.ι → ((NY.pullback β).pow (d : ℤ)).Sections 1 ⊤ := fun c =>
    (((((eY c).npow d).cast (one_mul _)).pullback β).restrict
      (le_of_eq (Scheme.Hom.preimage_top β).symm)).toPowOne
  have he : ∀ c, (e c).nonvanishingLocus = β ⁻¹ᵁ DY.U c := fun c => by
    simp only [e, LineBundleData.Sections.nonvanishingLocus_toPowOne,
      LineBundleData.Sections.nonvanishingLocus_restrict,
      LineBundleData.Sections.nonvanishingLocus_pullback,
      LineBundleData.Sections.nonvanishingLocus_cast,
      LineBundleData.Sections.nonvanishingLocus_npow _ hd, heY, top_inf_eq]
  have he' : ∀ x, ∃ c, x ∈ (e c).nonvanishingLocus := fun x => by
    obtain ⟨c, hc⟩ := hU' (β x)
    exact ⟨c, by rw [he]; exact hc⟩
  -- one map per closed point
  have hmap : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ (Nn : ℕ) (h : X ⟶ projectiveSpace R Nn)
      (hh : h ≫ projectiveSpaceStructure R Nn = β ≫ pY) (O : Y.Opens), y ∈ O ∧
        ∀ x, β x ∈ O → (pullback.lift β h hh.symm).QuasiFiniteAt x := by
    intro y hy
    obtain ⟨n, s, hn, hgen, hzero⟩ := hsec y hy
    exact G.exists_quasiFiniteAt pY e DY.U he hU' y hy (hdim y hy) (hL y hy) hn s hgen hzero
  choose Nn h hh O hyO hO using hmap
  -- a base map
  obtain ⟨E₀, hE₀⟩ := G.exists_generates e he' 1
  obtain ⟨ι₀, _, T₀, hT₀⟩ := hE₀ E₀ le_rfl
  obtain ⟨N₀, h₀, hh₀, -⟩ := exists_toProjectiveSpace (β ≫ pY) T₀ hT₀
  -- finitely many closed points suffice
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun y : {y : Y // IsClosed ({y} : Set Y)} => (O y.1 y.2 : Set Y)) (fun _ => (O _ _).isOpen)
    (fun y' _ => by
      obtain ⟨y, hy, hy'⟩ := exists_closed_mem_of_forall O hyO y'
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hy'⟩)
  exact isRelativelyProjective_of_quasiFiniteAt pY hY β h₀ hh₀ S (fun y => Nn y.1 y.2)
    (fun y => h y.1 y.2) (fun y => hh y.1 y.2) (fun y => O y.1 y.2)
    (fun y x hx => hO y.1 y.2 x hx) (fun y _ => by
      have := hS (Set.mem_univ y)
      simp only [Set.mem_iUnion] at this
      obtain ⟨i, hi, hyi⟩ := this
      exact ⟨i, hi, hyi⟩)

end Main

end

end DeJongAlterations.StableModification.Projectivity
