/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.FiniteComparison
import DeJongAlterations.StableModification.Cohomology.MumfordCorollaries
import DeJongAlterations.StableModification.Cohomology.BaseChange

/-!
# The Mumford complex of a projective scheme

Let `X` carry projective coordinates `D` over a Noetherian ring `A` (`ProjectiveCoordinates`, e.g.
a closed subscheme of `ℙⁿ_A`, `ProjectiveCoordinates.ofClosedImmersion`) and let `F` be a
quasi-coherent module with finite sections on the coordinate charts and `A`-flat sections on the
finite intersections `U_T` (e.g. `F` coherent and flat over `A`). The Čech complex `Č(U, F)` is a
bounded complex of flat `A`-modules with finite cohomology (`finite_cechCohomology`), so it has a
perfect model: a bounded complex `K` of finite projective `A`-modules with a universal
quasi-isomorphism `K → Č(U, F)` (`ProjectiveCoordinates.exists_mumfordComplex`; blueprint
`thm:sm-mumford-complex`; Mumford, *Abelian varieties*, §5; Hartshorne III.12.2; EGA III 6.10.5;
Temkin, *Stable modification of relative curves*, proof of Proposition 4.4.6).

For every `A → B` the complex `K ⊗_A B` therefore computes the cohomology of `Č(U, F) ⊗_A B`,
which is the Čech complex of `F_B` on `X_B` for the base-changed cover (blueprint
`prop:sm-cech-base-change`). The corollaries below are stated for `Č(U, F) ⊗_A B`:

* `ProjectiveCoordinates.exists_eulerChar_cech` (`cor:sm-euler-constant`): over a Noetherian local
  ring, `∑ (-1)^i dim_κ Hⁱ(Č(U, F) ⊗_A κ)` does not depend on the field `κ` over `A`;
* `ProjectiveCoordinates.isZero_cech_baseChange_of_residue` (`cor:sm-semicontinuity`, top
  degree): if the cohomology vanishes above `s + 1` and `H^{s+1}` of the closed fibre vanishes,
  then `H^{s+1}` vanishes after every base change;
* `ProjectiveCoordinates.epi_cech_toBaseChange_of_residue` (`cor:sm-base-change-onto`): under the
  same hypotheses `Hˢ` commutes with surjective base change (is onto).

When the coefficients are the structure map of `p : X → Spec A`
(`nonempty_projectiveCoordinates_of_isProjectiveOver` in `FiniteProjective.lean`), the base change
iso `cechComplexBaseChangeIso` (`BaseChange.lean`) turns these into statements about the Čech
cohomology of `F_B = q^*F` on `X_B = X ×_A Spec B` for the cover `q⁻¹U`:
`ProjectiveCoordinates.exists_mumfordComplex_baseChange`,
`ProjectiveCoordinates.exists_eulerChar_fibre`, `ProjectiveCoordinates.isZero_cech_fibre_of_residue`
and `ProjectiveCoordinates.epi_cechPullbackMap_of_residue`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section CechFlat

variable {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι] [Fintype ι]

omit [LinearOrder ι] in
/-- The cardinality-`n` part of a subset Čech complex is flat if the terms `D(S)`, `#S = n`, are
flat. -/
theorem flat_subsetCechCardPiece (D : Finset ι ⥤ ModuleCat.{u} R) (n : ℕ)
    (hD : ∀ S : Finset ι, S.card = n → Module.Flat R (D.obj S)) :
    Module.Flat R (subsetCechCardPiece D n) := by
  classical
  have : ∀ S : {S : Finset ι // S.card = n}, Module.Flat R (D.obj S.val) := fun S => hD S.1 S.2
  have : Module.Flat R (∀ S : {S : Finset ι // S.card = n}, D.obj S.val) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R _
      (fun S : {S : Finset ι // S.card = n} => D.obj S.val)).symm
  exact Module.Flat.of_linearEquiv (subsetCechCardProductEquiv D n)

/-- The Čech complex of a diagram which is flat on nonempty subsets is degreewise flat. -/
theorem flat_subsetCechComplex_X (D : Finset ι ⥤ ModuleCat.{u} R)
    (hD : ∀ S : Finset ι, S.Nonempty → Module.Flat R (D.obj S)) (p : ℕ) :
    Module.Flat R ((subsetCechComplex D).X p) :=
  flat_subsetCechCardPiece D (p + 1) fun S hS => hD S (Finset.card_pos.mp (by omega))

/-- The Čech complex vanishes in degrees `p ≥ #ι`. -/
theorem isZero_subsetCechComplex_X (D : Finset ι ⥤ ModuleCat.{u} R) (p : ℕ)
    (hp : Fintype.card ι - 1 < p) : IsZero ((subsetCechComplex D).X p) := by
  change IsZero (ModuleCat.of R (subsetCechCardPiece D (p + 1)))
  rw [subsetCechCardPiece_eq_bot _ _ (by omega)]
  exact ModuleCat.isZero_of_subsingleton _

end CechFlat

variable {X : Scheme.{u}} {A : Type u} [CommRing A] {c : A →+* Γ(X, ⊤)}

namespace ProjectiveCoordinates

variable (D : ProjectiveCoordinates X A c) (F : X.Modules)
  (hF : ∀ i, Module.Finite Γ(X, D.U i) Γ(F, D.U i))
  (hflat : ∀ T : Finset D.ι, T.Nonempty → Module.Flat A ((cechDiagram F D.U c).obj T))

include hflat in
lemma flat_cechComplex_X (p : ℕ) : Module.Flat A ((cechComplex F D.U c).X p) :=
  flat_subsetCechComplex_X _ hflat p

lemma isZero_cechComplex_X (p : ℕ) (hp : Fintype.card D.ι - 1 < p) :
    IsZero ((cechComplex F D.U c).X p) :=
  isZero_subsetCechComplex_X _ p hp

variable [F.IsQuasicoherent]

include hF hflat in
/-- **The Mumford complex** (blueprint `thm:sm-mumford-complex`): for projective coordinates over
a Noetherian ring and `F` with finite sections on the charts and `A`-flat sections on the `U_T`,
if `Ȟⁱ(U, F) = 0` for `i > q` (e.g. `q = #ι - 1`, see `exists_mumfordComplex_card`), there is a
complex `K` of finite projective `A`-modules concentrated in degrees `≤ q` with a universal
quasi-isomorphism `K → Č(U, F)`; thus `Hⁱ(K ⊗_A B) ≅ Hⁱ(Č(U, F) ⊗_A B)` for every `A → B`. -/
theorem exists_mumfordComplex [IsNoetherianRing A] (q : ℕ)
    (hvan : ∀ k, q < k → IsZero (cechCohomology F D.U c k)) :
    ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ cechComplex F D.U c),
      IsUnivQuasiIso g ∧ (∀ k, Module.Finite A (K.X k)) ∧
      (∀ k, Module.Projective A (K.X k)) ∧ ∀ k, q < k → IsZero (K.X k) :=
  exists_perfect_model_le (cechComplex F D.U c) (Fintype.card D.ι - 1) q
    (D.flat_cechComplex_X F hflat) (D.isZero_cechComplex_X F)
    (fun k => D.finite_cechCohomology F hF k) hvan

include hF hflat in
/-- The Mumford complex in degrees `< #ι`. -/
theorem exists_mumfordComplex_card [IsNoetherianRing A] :
    ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ cechComplex F D.U c),
      IsUnivQuasiIso g ∧ (∀ k, Module.Finite A (K.X k)) ∧
      (∀ k, Module.Projective A (K.X k)) ∧ ∀ k, Fintype.card D.ι - 1 < k → IsZero (K.X k) :=
  D.exists_mumfordComplex F hF hflat _ fun k hk =>
    isZero_cechCohomology_of_card_le F D.U c k (by omega)

include hF hflat in
/-- **Constancy of the Euler characteristic** (blueprint `cor:sm-euler-constant`): over a
Noetherian local ring, `∑_{i < #ι} (-1)^i dim_κ Hⁱ(Č(U, F) ⊗_A κ)` is independent of the field
`κ` over `A`. -/
theorem exists_eulerChar_cech [IsNoetherianRing A] [IsLocalRing A] :
    ∃ χ : ℤ, ∀ (κ : Type u) [Field κ] (φ : A →+* κ),
      ∑ i ∈ Finset.range (Fintype.card D.ι - 1 + 1), (-1 : ℤ) ^ i *
        (Module.finrank κ (((baseChange φ).obj (cechComplex F D.U c)).homology i) : ℤ) = χ :=
  exists_eulerChar_baseChange (cechComplex F D.U c) (Fintype.card D.ι - 1)
    (D.flat_cechComplex_X F hflat) (D.isZero_cechComplex_X F)
    (fun k => D.finite_cechCohomology F hF k)

include hF hflat in
/-- **Vanishing from the closed fibre** (blueprint `cor:sm-semicontinuity`): over a Noetherian
local ring with residue field `k`, if `Ȟⁱ(U, F) = 0` for `i > s + 1` and
`H^{s+1}(Č(U, F) ⊗_A k) = 0`, then `Ȟ^{s+1}(U, F) = 0` and `H^{s+1}(Č(U, F) ⊗_A B) = 0` for
every `A → B`. For curves (`s = 0`): `h¹(F_s) = 0` implies `h¹(F) = 0` and `h¹(F_η) = 0`. -/
theorem isZero_cech_baseChange_of_residue [IsNoetherianRing A] [IsLocalRing A] (s : ℕ)
    (hvan : ∀ k, s + 1 < k → IsZero (cechCohomology F D.U c k))
    (hk : IsZero (((baseChange (IsLocalRing.residue A)).obj (cechComplex F D.U c)).homology
      (s + 1))) :
    IsZero (cechCohomology F D.U c (s + 1)) ∧ ∀ (B : Type u) [CommRing B] (φ : A →+* B),
      IsZero (((baseChange φ).obj (cechComplex F D.U c)).homology (s + 1)) :=
  isZero_homology_baseChange_of_residue (cechComplex F D.U c) (Fintype.card D.ι - 1) s
    (D.flat_cechComplex_X F hflat) (D.isZero_cechComplex_X F)
    (fun k => D.finite_cechCohomology F hF k) hvan hk

include hF hflat in
/-- **Cohomology and base change, onto form** (blueprint `cor:sm-base-change-onto`): under the
hypotheses of `isZero_cech_baseChange_of_residue`, `Ȟˢ(U, F) → Hˢ(Č(U, F) ⊗_A B)` is surjective
for every surjective `A → B`. For curves (`s = 0`, `B = k`): `H⁰(X, F) → H⁰(X_s, F_s)` is onto. -/
theorem epi_cech_toBaseChange_of_residue [IsNoetherianRing A] [IsLocalRing A] (s : ℕ)
    (hvan : ∀ k, s + 1 < k → IsZero (cechCohomology F D.U c k))
    (hk : IsZero (((baseChange (IsLocalRing.residue A)).obj (cechComplex F D.U c)).homology
      (s + 1)))
    {B : Type u} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ) :
    Epi (HomologicalComplex.homologyMap (toBaseChange φ (cechComplex F D.U c)) s) :=
  epi_homologyMap_toBaseChange_of_residue (cechComplex F D.U c) (Fintype.card D.ι - 1) s
    (D.flat_cechComplex_X F hflat) (D.isZero_cechComplex_X F)
    (fun k => D.finite_cechCohomology F hF k) hvan hk φ hφ

end ProjectiveCoordinates

section BaseChange

variable {X : Scheme.{u}} {A : Type u} [CommRing A] {p : X ⟶ Spec (CommRingCat.of A)}

namespace ProjectiveCoordinates

variable (D : ProjectiveCoordinates X A (structureCoeff p)) (F : X.Modules) [F.IsQuasicoherent]
  (hF : ∀ i, Module.Finite Γ(X, D.U i) Γ(F, D.U i))
  (hflat : ∀ T : Finset D.ι, T.Nonempty →
    Module.Flat A ((cechDiagram F D.U (structureCoeff p)).obj T))

/-- `Č(U, F) ⊗_A B ≅ Č(q⁻¹U, q^*F)` for projective coordinates (blueprint
`prop:sm-cech-base-change`). -/
noncomputable def cechBaseChangeIso {B : Type u} [CommRing B] (φ : A →+* B) :
    (baseChange φ).obj (cechComplex F D.U (structureCoeff p)) ≅
      cechComplex ((Scheme.Modules.pullback (bcFst φ p)).obj F) (fun i => bcFst φ p ⁻¹ᵁ D.U i)
        (structureCoeff (bcSnd φ p)) :=
  cechComplexBaseChangeIso φ p F D.U fun _ hT => D.isAffineOpen_finsetInf hT

include hF hflat in
/-- **The Mumford complex computes the cohomology of all base changes** (blueprint
`thm:sm-mumford-complex`): the complex `K` of `exists_mumfordComplex` satisfies
`Hⁱ(K ⊗_A B) ≅ Ȟⁱ(q⁻¹U, q^*F)` on `X_B = X ×_A Spec B`, for every `A → B`. -/
theorem exists_mumfordComplex_baseChange [IsNoetherianRing A] (q : ℕ)
    (hvan : ∀ k, q < k → IsZero (cechCohomology F D.U (structureCoeff p) k)) :
    ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ cechComplex F D.U (structureCoeff p)),
      IsUnivQuasiIso g ∧ (∀ k, Module.Finite A (K.X k)) ∧
      (∀ k, Module.Projective A (K.X k)) ∧ (∀ k, q < k → IsZero (K.X k)) ∧
      ∀ (B : Type u) [CommRing B] (φ : A →+* B) (i : ℕ),
        Nonempty (((baseChange φ).obj K).homology i ≅
          cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
            (fun j => bcFst φ p ⁻¹ᵁ D.U j) (structureCoeff (bcSnd φ p)) i) := by
  obtain ⟨K, g, hg, hfin, hproj, hzero⟩ := D.exists_mumfordComplex F hF hflat q hvan
  refine ⟨K, g, hg, hfin, hproj, hzero, fun B _ φ i => ?_⟩
  have := hg.2 B φ
  exact ⟨isoOfQuasiIsoAt ((baseChange φ).map g) i ≪≫
    HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F φ) i⟩

include hF hflat in
/-- **Constancy of the Euler characteristic of the fibres** (blueprint `cor:sm-euler-constant`):
over a Noetherian local ring, `∑_{i < #ι} (-1)^i dim_κ Ȟⁱ(X_κ, F_κ)` is the same for all fields
`κ` over `A`. -/
theorem exists_eulerChar_fibre [IsNoetherianRing A] [IsLocalRing A] :
    ∃ χ : ℤ, ∀ (κ : Type u) [Field κ] (φ : A →+* κ),
      ∑ i ∈ Finset.range (Fintype.card D.ι - 1 + 1), (-1 : ℤ) ^ i *
        (Module.finrank κ (cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
          (fun j => bcFst φ p ⁻¹ᵁ D.U j) (structureCoeff (bcSnd φ p)) i) : ℤ) = χ := by
  obtain ⟨χ, hχ⟩ := D.exists_eulerChar_cech F hF hflat
  refine ⟨χ, fun κ _ φ => ?_⟩
  rw [← hχ κ φ]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact (LinearEquiv.finrank_eq
    (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F φ) i).toLinearEquiv).symm

include hF hflat in
/-- **Vanishing from the closed fibre** (blueprint `cor:sm-semicontinuity`): over a Noetherian
local ring with residue field `k`, if `Ȟⁱ(U, F) = 0` for `i > s + 1` and
`Ȟ^{s+1}(X_k, F_k) = 0`, then `Ȟ^{s+1}(U, F) = 0` and `Ȟ^{s+1}(X_B, F_B) = 0` for every
`A → B`. For curves (`s = 0`): `h¹(F_s) = 0` implies `h¹(F) = 0` and `h¹(F_η) = 0`. -/
theorem isZero_cech_fibre_of_residue [IsNoetherianRing A] [IsLocalRing A] (s : ℕ)
    (hvan : ∀ k, s + 1 < k → IsZero (cechCohomology F D.U (structureCoeff p) k))
    (hk : IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue A) p)).obj F)
      (fun j => bcFst (IsLocalRing.residue A) p ⁻¹ᵁ D.U j)
      (structureCoeff (bcSnd (IsLocalRing.residue A) p)) (s + 1))) :
    IsZero (cechCohomology F D.U (structureCoeff p) (s + 1)) ∧
      ∀ (B : Type u) [CommRing B] (φ : A →+* B),
        IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
          (fun j => bcFst φ p ⁻¹ᵁ D.U j) (structureCoeff (bcSnd φ p)) (s + 1)) := by
  have h := D.isZero_cech_baseChange_of_residue F hF hflat s hvan
    (hk.of_iso (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F _) (s + 1)))
  exact ⟨h.1, fun B _ φ =>
    (h.2 B φ).of_iso (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F φ) (s + 1)).symm⟩

/-- The pullback map `Č(U, F) → Č(q⁻¹U, q^*F)` of Čech complexes, `A`-linearly. -/
noncomputable def cechPullbackMap {B : Type u} [CommRing B] (φ : A →+* B) :
    cechComplex F D.U (structureCoeff p) ⟶ (restrictComplex φ).obj
      (cechComplex ((Scheme.Modules.pullback (bcFst φ p)).obj F) (fun i => bcFst φ p ⁻¹ᵁ D.U i)
        (structureCoeff (bcSnd φ p))) :=
  toBaseChange φ _ ≫ (restrictComplex φ).map (D.cechBaseChangeIso F φ).hom

include hF hflat in
/-- **Cohomology and base change, onto form** (blueprint `cor:sm-base-change-onto`): under the
hypotheses of `isZero_cech_fibre_of_residue`, the pullback map `Ȟˢ(U, F) → Ȟˢ(X_B, F_B)` is
surjective for every surjective `A → B`. For curves (`s = 0`, `B = k`):
`H⁰(X, F) → H⁰(X_s, F_s)` is onto. -/
theorem epi_cechPullbackMap_of_residue [IsNoetherianRing A] [IsLocalRing A] (s : ℕ)
    (hvan : ∀ k, s + 1 < k → IsZero (cechCohomology F D.U (structureCoeff p) k))
    (hk : IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue A) p)).obj F)
      (fun j => bcFst (IsLocalRing.residue A) p ⁻¹ᵁ D.U j)
      (structureCoeff (bcSnd (IsLocalRing.residue A) p)) (s + 1)))
    {B : Type u} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ) :
    Epi (HomologicalComplex.homologyMap (D.cechPullbackMap F φ) s) := by
  have h := D.epi_cech_toBaseChange_of_residue F hF hflat s hvan
    (hk.of_iso (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F _) (s + 1))) φ hφ
  have : IsIso ((restrictComplex φ).map (D.cechBaseChangeIso F φ).hom) := inferInstance
  rw [cechPullbackMap, HomologicalComplex.homologyMap_comp]
  infer_instance

end ProjectiveCoordinates

end BaseChange

end

end DeJongAlterations.StableModification.Cohomology
