/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.RosenlichtComponentPullback
import DeJongAlterations.StableModification.Omega.RosenlichtComponentDegree

/-!
# The degree of `ω` on a curve mapping to a geometric fibre

Let `f : X ⟶ S` be locally of finite presentation with invertible relative dualizing sheaf
`ω = ω_{X/S} = j_*(Ω¹_{X/S}|_{Sm f})` (for instance a nodal curve smooth over the generic point of
a normal locally Noetherian integral base, `Omega.isInvertibleModule_dualizingSheaf_of_isNodalCurve`),
let `K` be algebraically closed, and let `ν : Y ⟶ X` be a morphism from a smooth, normal,
projective integral curve `Y` over `K` with `ν ≫ f = q ≫ a` for `q : Y ⟶ Spec K`,
`a : Spec K ⟶ S` (in the application: the normalization `Z̃` of an irreducible component of the
geometric fibre `X_K`, composed with `X_K ⟶ X`). Let `E = ν⁻¹(X ∖ Sm f)`, a finite set of closed
points. This file proves

  `deg ν^* ω = χ(ν^* ω) - χ(𝒪_Y) = 2 p_a(Y) - 2 + #E`  (`degree_pullback_dualizingSheaf`),

given *comparison charts* (`CompChart`) around every point: an affine `W ⊆ X` with a generator
`σ` of `ω`, an affine `V ⊆ ν⁻¹ W` with a generator `β` of `Ω¹_{Y/K}`, and `t ∈ Γ(V, 𝒪_Y)` with
`t · θ(σ) = β`, where `θ(σ)` is the base change of `σ` to a meromorphic differential on `V`
(`dualizingComparison`); `t = 1` near the points outside `E` (`ω` restricts to `Ω¹_{Y/K}` there)
and `Γ(V, 𝒪_Y)/(t)` is one-dimensional near the points of `E` (`ν^* ω` has a simple pole there:
`ν^* ω = Ω¹_{Y/K}(E)`). These are the local generator computations of the proof of
`cor:sm-omega-restriction-component` (blueprint `sm-omega-base-change.tex`; here
`thm:sm-omega-bcf-degree-pullback` in `sm-omega-base-change-fibre.tex`).

## Proof

The comparison `Θ : ν^* ω ⟶ j_*(Ω¹_{Y/K}|_{Y ∖ E})` (`pullbackComparison`) maps the generator
`ν^* σ` of `ν^* ω` on `V` (`bijective_smul_pullbackSectionLE`) to `θ(σ)`, so it is injective, and
the restriction `ι : Ω¹_{Y/K} ⟶ j_*(Ω¹_{Y/K}|_{Y ∖ E})` lands in its image (`β = t θ(σ)`); hence
`ι` lifts to `α : Ω¹_{Y/K} ⟶ ν^* ω` (`exists_lift`), bijective over `Y ∖ E` and with cokernel
`Γ(V, 𝒪)/(t) ≅ K` near each point of `E`. The Euler characteristic formula for such twists
(`eulerCharOf_eq_add_card`) and `deg Ω¹_{Y/K} = 2g - 2` give the degree.

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2 (b) and
proof of Thm 1.1 (`semi-stable.tex`, T:1700–1704, T:1731–1737).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.StableModification.CurvesField

universe u

namespace DeJongAlterations.StableModification.Omega.RosenlichtComponent

section Charts

variable {X S Y T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (q : Y ⟶ T)
  (ν : Y ⟶ X) (h : T ⟶ S) (sq : ν ≫ f = q ≫ h)

/-- A **comparison chart**: an affine open `W ⊆ X` with a free generator `σ` of `Γ(W, ω_{X/S})`,
an affine open `V ⊆ ν⁻¹ W` with a free generator `β` of `Γ(V, Ω¹_{Y/T})`, and `t ∈ Γ(V, 𝒪_Y)`
with `t · θ(σ)|_V = β` in `j_*(Ω¹_{Y/T}|_{ν⁻¹ Sm f})` (blueprint `def:sm-omega-bcf-chart`). -/
structure CompChart where
  /-- The affine open of `X`. -/
  W : X.Opens
  isAffineOpen_W : IsAffineOpen W
  /-- The generator of `ω` on `W`. -/
  σ : Γ(dualizingSheaf f, W)
  bijective_σ : Function.Bijective (fun c : Γ(X, W) => c • σ)
  /-- The affine open of `Y`. -/
  V : Y.Opens
  isAffineOpen_V : IsAffineOpen V
  le : V ≤ ν ⁻¹ᵁ W
  /-- The generator of `Ω¹_{Y/T}` on `V`. -/
  β : Γ(relativeDifferentials q, V)
  bijective_β : Function.Bijective (fun c : Γ(Y, V) => c • β)
  /-- The local equation of the pole. -/
  t : Γ(Y, V)
  eq : t • (logDifferentials f q ν).presheaf.map (homOfLE le).op
    ((dualizingComparison f q ν h sq).app W σ) = (toLogDifferentials f q ν).app V β

namespace CompChart

variable {f q ν h sq} (C : CompChart f q ν h sq)

/-- The image `θ(σ)|_V` of the generator in `j_*(Ω¹_{Y/T}|_{ν⁻¹ Sm f})`. -/
def τ : Γ(logDifferentials f q ν, C.V) :=
  (logDifferentials f q ν).presheaf.map (homOfLE C.le).op ((dualizingComparison f q ν h sq).app C.W C.σ)

/-- The pulled-back generator `ν^* σ|_V` of `ν^* ω` on `V`. -/
def σV : Γ((Scheme.Modules.pullback ν).obj (dualizingSheaf f), C.V) :=
  pullbackSectionLE ν (dualizingSheaf f) C.le C.σ

theorem eq' : C.t • C.τ = (toLogDifferentials f q ν).app C.V C.β := C.eq

theorem pullbackComparison_σV : (pullbackComparison f q ν h sq).app C.V C.σV = C.τ :=
  pullbackComparison_app_pullbackSectionLE f q ν h sq C.le C.σ

theorem pullbackComparison_smul_σV (c : Γ(Y, C.V)) :
    (pullbackComparison f q ν h sq).app C.V (c • C.σV) = c • C.τ := by
  rw [Scheme.Modules.Hom.app_smul, pullbackComparison_σV]

variable [(dualizingSheaf f).IsQuasicoherent]

theorem bijective_σV : Function.Bijective (fun c : Γ(Y, C.V) => c • C.σV) :=
  bijective_smul_pullbackSectionLE ν (dualizingSheaf f) C.isAffineOpen_W C.isAffineOpen_V C.le
    C.σ C.bijective_σ

/-- The image of `Θ` on `V` is `Γ(V, 𝒪) · θ(σ)`. -/
theorem mem_range_pullbackComparison_iff (n : Γ(logDifferentials f q ν, C.V)) :
    n ∈ Set.range ((pullbackComparison f q ν h sq).app C.V) ↔ ∃ c : Γ(Y, C.V), c • C.τ = n := by
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨c, rfl⟩ := C.bijective_σV.surjective m
    exact ⟨c, (C.pullbackComparison_smul_σV c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • C.σV, C.pullbackComparison_smul_σV c⟩

variable [(relativeDifferentials q).IsQuasicoherent]

omit [(dualizingSheaf f).IsQuasicoherent] [(relativeDifferentials q).IsQuasicoherent] in
theorem eq_restrict (g : Γ(Y, C.V)) :
    Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op C.t •
      (logDifferentials f q ν).presheaf.map (homOfLE ((Y.basicOpen_le g).trans C.le)).op
        ((dualizingComparison f q ν h sq).app C.W C.σ) =
      (toLogDifferentials f q ν).app (Y.basicOpen g)
        ((relativeDifferentials q).presheaf.map (homOfLE (Y.basicOpen_le g)).op C.β) := by
  have e := congrArg ((logDifferentials f q ν).presheaf.map (homOfLE (Y.basicOpen_le g)).op) C.eq
  rw [Scheme.Modules.map_smul] at e
  rw [Scheme.Modules.Hom.app_map, ← e]
  congr 1
  exact (presheaf_map_map (logDifferentials f q ν) C.le (Y.basicOpen_le g)
    ((Y.basicOpen_le g).trans C.le)
    (show Γ(logDifferentials f q ν, ν ⁻¹ᵁ C.W) from
      (dualizingComparison f q ν h sq).app C.W C.σ)).symm

omit [(dualizingSheaf f).IsQuasicoherent] in
/-- **Restriction of a comparison chart** to a basic open of `V`. -/
def restrictBasicOpen (g : Γ(Y, C.V)) : CompChart f q ν h sq where
  W := C.W
  isAffineOpen_W := C.isAffineOpen_W
  σ := C.σ
  bijective_σ := C.bijective_σ
  V := Y.basicOpen g
  isAffineOpen_V := C.isAffineOpen_V.basicOpen g
  le := (Y.basicOpen_le g).trans C.le
  β := (relativeDifferentials q).presheaf.map (homOfLE (Y.basicOpen_le g)).op C.β
  bijective_β := bijective_smul_restrict_basicOpen _ C.isAffineOpen_V C.β C.bijective_β g
  t := Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op C.t
  eq := C.eq_restrict g

omit [(dualizingSheaf f).IsQuasicoherent] [(relativeDifferentials q).IsQuasicoherent] in
/-- If `V` meets `ν⁻¹ Sm f` and `Y` is integral, the restriction `ι` is injective on `V`. -/
theorem injective_toLogDifferentials [(relativeDifferentials q).IsQuasicoherent] [IsIntegral Y]
    {z : Y} (hzV : z ∈ C.V) (hzU : z ∈ fibreLocus f ν) :
    Function.Injective ((toLogDifferentials f q ν).app C.V) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨c, rfl⟩ := C.bijective_β.surjective m
  obtain ⟨g, hgle, hzg⟩ := C.isAffineOpen_V.exists_basicOpen_le (V := C.V ⊓ fibreLocus f ν)
    ⟨z, hzV, hzU⟩ hzV
  have hD : Y.basicOpen g ≤ (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ C.V) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact fun x hx => ⟨(hgle hx).2, (hgle hx).1⟩
  have h0 : (relativeDifferentials q).presheaf.map (homOfLE (Y.basicOpen_le g)).op (c • C.β) =
      0 := by
    rw [← presheaf_map_map (relativeDifferentials q)
      ((fibreLocus f ν).ι.image_preimage_le C.V) hD (Y.basicOpen_le g), ← toLogDifferentials_app,
      hm]
    exact map_zero _
  rw [Scheme.Modules.map_smul] at h0
  have h1 := (bijective_smul_restrict_basicOpen _ C.isAffineOpen_V C.β C.bijective_β g).injective
    (h0.trans (zero_smul _ _).symm)
  have : Nonempty (Y.basicOpen g) := ⟨⟨z, hzg⟩⟩
  have h2 : c = 0 := map_injective_of_isIntegral Y (homOfLE (Y.basicOpen_le g))
    (h1.trans (map_zero _).symm)
  simp only [h2, zero_smul]

omit [(dualizingSheaf f).IsQuasicoherent] [(relativeDifferentials q).IsQuasicoherent] in
/-- `c ↦ c · θ(σ)` is injective on `V` once `ι` is. -/
theorem injective_smul_τ (hι : Function.Injective ((toLogDifferentials f q ν).app C.V)) :
    Function.Injective (fun c : Γ(Y, C.V) => c • C.τ) := by
  intro c c' hcc'
  simp only at hcc'
  apply C.bijective_β.injective
  apply hι
  simp only
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ← C.eq', smul_smul, smul_smul,
    mul_comm, mul_smul, hcc', ← mul_smul, mul_comm, mul_smul]

omit [(relativeDifferentials q).IsQuasicoherent] in
/-- `Θ` is injective on `V` once `ι` is. -/
theorem injective_pullbackComparison
    (hι : Function.Injective ((toLogDifferentials f q ν).app C.V)) :
    Function.Injective ((pullbackComparison f q ν h sq).app C.V) := by
  intro m m' hmm'
  obtain ⟨c, rfl⟩ := C.bijective_σV.surjective m
  obtain ⟨c', rfl⟩ := C.bijective_σV.surjective m'
  simp only at hmm' ⊢
  rw [C.pullbackComparison_smul_σV, C.pullbackComparison_smul_σV] at hmm'
  rw [C.injective_smul_τ hι hmm']

end CompChart

end Charts


section Degree

variable {X S Y : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  {K : Type u} [Field K] [IsAlgClosed K] (q : Y ⟶ Spec (.of K)) (ν : Y ⟶ X)
  (a : Spec (.of K) ⟶ S) (sq : ν ≫ f = q ≫ a)

/-- The generic point of an integral curve with a closed point lies over the smooth locus when
`E = ν⁻¹(X ∖ Sm f)` consists of closed points. -/
theorem genericPoint_mem_fibreLocus [IsIntegral Y] (hpt : ∃ y : Y, y ≠ genericPoint Y)
    (E : Finset Y) (hE : ∀ y, y ∈ E ↔ ν y ∉ f.smoothLocus) (hEc : ∀ y ∈ E, IsClosed ({y} : Set Y)) :
    genericPoint Y ∈ fibreLocus f ν := by
  by_contra hη
  have hηE : genericPoint Y ∈ E := (hE _).mpr hη
  obtain ⟨y, hy⟩ := hpt
  apply hy
  have hcl := hEc _ hηE
  have : y ∈ closure ({genericPoint Y} : Set Y) := by
    rw [(genericPoint_spec Y).def]; trivial
  rw [hcl.closure_eq] at this
  exact this

/-- The generic point lies in every nonempty open of an integral scheme. -/
theorem genericPoint_mem_of_mem [IsIntegral Y] {V : Y.Opens} {y : Y} (hy : y ∈ V) :
    genericPoint Y ∈ V :=
  ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The degree of `ω` on a curve mapping to a geometric fibre** (blueprint
`thm:sm-omega-bcf-degree-pullback`, the numerical part of `cor:sm-omega-restriction-component`).
Let `ω = ω_{X/S}` be invertible, `ν : Y ⟶ X` with `ν ≫ f = q ≫ a` for a smooth, normal,
projective integral curve `q : Y ⟶ Spec K` over `K = K̄`, and `E = ν⁻¹(X ∖ Sm f)` a finite set of
closed points. Assume comparison charts with `t = 1` around the points outside `E` and with
`dim_K Γ(V, 𝒪)/(t) = 1`, `V ∩ E = {y}` around the points `y ∈ E`. Then
`deg ν^* ω = χ(ν^* ω) - χ(𝒪_Y) = 2 p_a(Y) - 2 + #E`. -/
theorem degree_pullback_dualizingSheaf (hω : IsInvertibleModule (dualizingSheaf f))
    [IsIntegral Y] [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
    [Smooth q] [NoetherianSpace Y] (hp : IsProjectiveOver q) (hdim : topologicalKrullDim Y ≤ 1)
    (hpt : ∃ y : Y, y ≠ genericPoint Y) (hnormal : IsNormalScheme Y)
    (E : Finset Y) (hE : ∀ y, y ∈ E ↔ ν y ∉ f.smoothLocus)
    (hEc : ∀ y ∈ E, IsClosed ({y} : Set Y))
    (hsmooth : ∀ y, y ∉ E → ∃ C : CompChart f q ν a sq, y ∈ C.V ∧ C.t = 1)
    (hpole : ∀ y ∈ E, ∃ C : CompChart f q ν a sq, y ∈ C.V ∧ (∀ z ∈ E, z ∈ C.V → z = y) ∧
      letI := (sectionsRingHom (structureCoeff q) (le_top : C.V ≤ ⊤)).toAlgebra
      FiniteDimensional K (Γ(Y, C.V) ⧸ Ideal.span {C.t}) ∧
        finrank K (Γ(Y, C.V) ⧸ Ideal.span {C.t}) = 1) :
    (∀ i, FiniteDimensional K
        (cohomology ((Scheme.Modules.pullback ν).obj (dualizingSheaf f)) (structureCoeff q) i)) ∧
      DualityScheme.eulerCharOf ((Scheme.Modules.pullback ν).obj (dualizingSheaf f))
          (structureCoeff q) - Genus.eulerChar Y (structureCoeff q) =
        2 * Genus.arithmeticGenus Y (structureCoeff q) - 2 + E.card := by
  classical
  have : (dualizingSheaf f).IsQuasicoherent := isQuasicoherent_of_isInvertibleModule _ hω
  have hη := genericPoint_mem_fibreLocus f ν hpt E hE hEc
  have hchart : ∀ y : Y, ∃ C : CompChart f q ν a sq, y ∈ C.V := by
    intro y
    by_cases hy : y ∈ E
    · obtain ⟨C, hyC, -⟩ := hpole y hy
      exact ⟨C, hyC⟩
    · obtain ⟨C, hyC, -⟩ := hsmooth y hy
      exact ⟨C, hyC⟩
  have hιC : ∀ (C : CompChart f q ν a sq) {y : Y}, y ∈ C.V → Function.Injective ((toLogDifferentials f q ν).app C.V) :=
    fun C _ hy => C.injective_toLogDifferentials (genericPoint_mem_of_mem hy) hη
  have hsmall : ∀ (W : Y.Opens) (y : Y), y ∈ W →
      ∃ C : CompChart f q ν a sq, y ∈ C.V ∧ C.V ≤ W := by
    intro W y hy
    obtain ⟨C, hyC⟩ := hchart y
    obtain ⟨g, hgle, hyg⟩ :=
      C.isAffineOpen_V.exists_basicOpen_le (V := W ⊓ C.V) ⟨y, hy, hyC⟩ hyC
    exact ⟨C.restrictBasicOpen g, hyg, hgle.trans inf_le_left⟩
  have hΘ : ∀ W : Y.Opens, Function.Injective ((pullbackComparison f q ν a sq).app W) :=
    injective_app_of_local (pullbackComparison f q ν a sq) fun W y hy => by
      obtain ⟨C, hyC, hCW⟩ := hsmall W y hy
      exact ⟨C.V, hCW, hyC, C.injective_pullbackComparison (hιC C hyC)⟩
  have hι : ∀ W : Y.Opens, Function.Injective ((toLogDifferentials f q ν).app W) :=
    injective_app_of_local (toLogDifferentials f q ν) fun W y hy => by
      obtain ⟨C, hyC, hCW⟩ := hsmall W y hy
      exact ⟨C.V, hCW, hyC, hιC C hyC⟩
  have hloc : ∀ (W : Y.Opens) (s : Γ(relativeDifferentials q, W)) (y : Y), y ∈ W →
      ∃ W' : Y.Opens, ∃ (hW' : W' ≤ W), y ∈ W' ∧
        (toLogDifferentials f q ν).app W' ((relativeDifferentials q).presheaf.map (homOfLE hW').op s) ∈
          Set.range ((pullbackComparison f q ν a sq).app W') := by
    intro W s y hy
    obtain ⟨C, hyC, hCW⟩ := hsmall W y hy
    refine ⟨C.V, hCW, hyC, ?_⟩
    obtain ⟨c, hc⟩ :=
      C.bijective_β.surjective ((relativeDifferentials q).presheaf.map (homOfLE hCW).op s)
    rw [← hc, C.mem_range_pullbackComparison_iff]
    refine ⟨c * C.t, ?_⟩
    simp only
    rw [Scheme.Modules.Hom.app_smul, ← C.eq', mul_smul]
  let α := lift (pullbackComparison f q ν a sq) (toLogDifferentials f q ν) hΘ hloc
  have hα : ∀ W s, (pullbackComparison f q ν a sq).app W (α.app W s) = (toLogDifferentials f q ν).app W s := lift_app_spec (pullbackComparison f q ν a sq) (toLogDifferentials f q ν) hΘ hloc
  have hinj : ∀ W : Y.Opens, IsAffineOpen W → Function.Injective (α.app W) := by
    intro W _ s s' hss'
    apply hι W
    rw [← hα, ← hα, hss']
  have hsurj : ∀ W : Y.Opens, IsAffineOpen W → (∀ y ∈ E, y ∉ W) →
      Function.Surjective (α.app W) := by
    intro W _ hWE m
    have hWU : W ≤ fibreLocus f ν := fun y hy => by
      by_contra hyU
      exact hWE y ((hE y).mpr hyU) hy
    have heq : (fibreLocus f ν).ι ''ᵁ ((fibreLocus f ν).ι ⁻¹ᵁ W) = W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hWU
    have hιb : Function.Bijective ((toLogDifferentials f q ν).app W) :=
      bijective_presheaf_map_of_eq (relativeDifferentials q)
        ((fibreLocus f ν).ι.image_preimage_le W) heq.ge
    obtain ⟨s, hs⟩ := hιb.surjective ((pullbackComparison f q ν a sq).app W m)
    exact ⟨s, hΘ W ((hα W s).trans hs)⟩
  have hloc3 : ∀ y ∈ E, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ (∀ z ∈ E, z ∈ W → z = y) ∧
      FiniteDimensional K (sectionsCoker (structureCoeff q) α W) ∧
      finrank K (sectionsCoker (structureCoeff q) α W) = 1 := by
    intro y hy
    obtain ⟨C, hyC, hCE, hfd, hrk⟩ := hpole y hy
    refine ⟨C.V, C.isAffineOpen_V, hyC, hCE, ?_⟩
    let _ : Algebra K Γ(Y, C.V) :=
      (sectionsRingHom (structureCoeff q) (le_top : C.V ≤ ⊤)).toAlgebra
    let L₀ : Γ(Y, C.V) →ₗ[K] sectionsModuleCat ((Scheme.Modules.pullback ν).obj (dualizingSheaf f)) (structureCoeff q) C.V le_top :=
      { toFun := fun c => (c • C.σV : Γ((Scheme.Modules.pullback ν).obj (dualizingSheaf f), C.V))
        map_add' := fun c c' => by
          change (c + c') • C.σV = c • C.σV + c' • C.σV
          exact add_smul _ _ _
        map_smul' := fun k c => by
          change (sectionsRingHom (structureCoeff q) (le_top : C.V ≤ ⊤) k * c) • C.σV =
            sectionsRingHom (structureCoeff q) (le_top : C.V ≤ ⊤) k • (c • C.σV)
          exact mul_smul _ _ _ }
    let P := LinearMap.range (sectionsMap (structureCoeff q) α C.V le_top).hom
    let L : Γ(Y, C.V) →ₗ[K] sectionsCoker (structureCoeff q) α C.V := P.mkQ ∘ₗ L₀
    have hL : Function.Surjective L :=
      (Submodule.mkQ_surjective P).comp C.bijective_σV.surjective
    have hker : LinearMap.ker L = (Ideal.span {C.t}).restrictScalars K := by
      ext c
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (p := P) (L₀ c) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
        LinearMap.mem_range]
      constructor
      · rintro ⟨s, hs⟩
        obtain ⟨b, rfl⟩ := C.bijective_β.surjective s
        refine ⟨b, ?_⟩
        apply C.injective_smul_τ (hιC C hyC)
        simp only
        have h1 := hα C.V (b • C.β)
        change α.app C.V (b • C.β) = c • C.σV at hs
        rw [hs, C.pullbackComparison_smul_σV, Scheme.Modules.Hom.app_smul, ← C.eq',
          smul_smul] at h1
        exact h1.symm
      · rintro ⟨b, rfl⟩
        refine ⟨b • C.β, ?_⟩
        change α.app C.V (b • C.β) = (b * C.t) • C.σV
        apply hΘ
        rw [hα, C.pullbackComparison_smul_σV, Scheme.Modules.Hom.app_smul, ← C.eq', mul_smul]
    let e₁ := LinearMap.quotKerEquivOfSurjective L hL
    let e₂ : (Γ(Y, C.V) ⧸ LinearMap.ker L) ≃ₗ[K] (Γ(Y, C.V) ⧸ Ideal.span {C.t}) :=
      (Submodule.quotEquivOfEq _ _ hker).trans (Submodule.Quotient.restrictScalarsEquiv K _)
    let e := e₂.symm.trans e₁
    exact ⟨Module.Finite.equiv e, by rw [← e.finrank_eq, hrk]⟩
  exact degree_eq_of_simplePoles q hp hdim hpt hnormal α E hEc hinj hsurj hloc3

end Degree

end DeJongAlterations.StableModification.Omega.RosenlichtComponent
