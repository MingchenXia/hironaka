import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The sheaf of relative differentials and the relative dualizing sheaf of a curve

Let `f : X ⟶ S` be a morphism of schemes. This file defines the sheaf of relative Kähler
differentials `Ω¹_{X/S}` as an `𝒪_X`-module (`relativeDifferentials f`), its universal
derivation, and the sheaf `ω_{X/S} = j_* (Ω¹_{X/S}|_U)` of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), §1.2 (`semi-stable.tex`, T:1691–1712), defined
elementarily as in PLAN-SM-GEOM §3 Q1: `U` is the smooth locus of `f` and `j : U → X` its
inclusion (`dualizingSheaf f`).

## Construction

* `baseSubring f U ⊆ Γ(X, U)`: the sections whose germ at every point `x ∈ U` comes from the
  stalk `𝒪_{S, f x}`; these are the sections which are locally pulled back from `S`. They form
  a presheaf of rings `basePresheaf f` with an inclusion `baseInclusion f` into `𝒪_X`; this is
  the image of the presheaf inverse image `f⁻¹ 𝒪_S` in `𝒪_X`.
* `differentialsPresheaf f`: the presheaf `U ↦ Ω_{Γ(X, U) / baseSubring f U}` (Mathlib's
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`).
* `relativeDifferentials f`: its sheafification, an `𝒪_X`-module.

## Universal property

`RelDerivation f N` is the type of `f⁻¹ 𝒪_S`-linear derivations `𝒪_X → N` into an
`𝒪_X`-module `N` (compatible families of derivations `Γ(X, U) → Γ(N, U)` killing the base
subrings). `homEquiv f N : (relativeDifferentials f ⟶ N) ≃ RelDerivation f N` is the universal
property of `Ω¹_{X/S}`, and `universalDerivation f` is the universal derivation `d`.

`RelDerivation.ext_of_le_affine` (locality): two derivations which agree on the sections over an
affine open `W` agree on every open `U ≤ W`. This is the uniqueness half of the identification of
`Ω¹_{X/S}` on affine opens with Kähler differentials (`Omega/Affine.lean`).

The blueprint chapter is `sm-omega.tex` (`def:sm-omega`, `lem:sm-omega-universal`,
`lem:sm-omega-locality`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Base

/-- The sections of `𝒪_X` over `U` whose germ at every point of `U` comes from the stalk of
`𝒪_S`: the image of `(f⁻¹ 𝒪_S)(U)` in `Γ(X, U)`. -/
def baseSubring (U : X.Opens) : Subring Γ(X, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx s ∈ (f.stalkMap x).hom.range}
  mul_mem' {a b} ha hb x hx := by
    rw [map_mul]; exact Subring.mul_mem _ (ha x hx) (hb x hx)
  one_mem' x hx := by rw [map_one]; exact Subring.one_mem _
  add_mem' {a b} ha hb x hx := by
    rw [map_add]; exact Subring.add_mem _ (ha x hx) (hb x hx)
  zero_mem' x hx := by rw [map_zero]; exact Subring.zero_mem _
  neg_mem' {a} ha x hx := by rw [map_neg]; exact Subring.neg_mem _ (ha x hx)

variable {f} in
theorem mem_baseSubring_iff {U : X.Opens} (s : Γ(X, U)) :
    s ∈ baseSubring f U ↔
      ∀ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx s ∈ (f.stalkMap x).hom.range :=
  Iff.rfl

theorem map_mem_baseSubring {U V : X.Opens} (i : V ⟶ U) {s : Γ(X, U)}
    (hs : s ∈ baseSubring f U) : X.presheaf.map i.op s ∈ baseSubring f V := by
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs x (i.le hx)

/-- Pullbacks of sections of `𝒪_S` lie in the base subring. -/
theorem app_mem_baseSubring {V : S.Opens} (r : Γ(S, V)) :
    f.app V r ∈ baseSubring f (f ⁻¹ᵁ V) := by
  intro x hx
  exact ⟨S.presheaf.germ V (f x) hx r, Scheme.Hom.germ_stalkMap_apply f V x hx r⟩

/-- Restrictions of pullbacks of sections of `𝒪_S` lie in the base subring. -/
theorem appLE_mem_baseSubring {V : S.Opens} {U : X.Opens} (h : U ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    f.appLE V U h r ∈ baseSubring f U := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact map_mem_baseSubring f (homOfLE h) (app_mem_baseSubring f r)

/-- The presheaf of base subrings `U ↦ baseSubring f U`. -/
@[simps]
def basePresheaf : (X.Opens)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (baseSubring f U.unop)
  map {U V} i := CommRingCat.ofHom
    { toFun := fun s => ⟨X.presheaf.map i s.1, map_mem_baseSubring f i.unop s.2⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  map_id U := by ext s; simp
  map_comp i j := by ext s; simp

/-- The inclusion of the base subrings into `𝒪_X`. -/
def baseInclusion : basePresheaf f ⟶ X.presheaf where
  app U := CommRingCat.ofHom (baseSubring f U.unop).subtype
  naturality U V i := by ext s; rfl

end Base

section Differentials

/-- The presheaf of relative differentials `U ↦ Ω_{Γ(X, U) / baseSubring f U}`. -/
def differentialsPresheaf :
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' (baseInclusion f)

/-- The sheaf of relative differentials `Ω¹_{X/S}`, an `𝒪_X`-module: the sheafification of
`differentialsPresheaf f` (Temkin §1.2, T:1691–1712; blueprint `def:sm-omega`). -/
def relativeDifferentials : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (differentialsPresheaf f)

/-- Derivations `𝒪_X → N` relative to `f`: compatible families of additive maps
`Γ(X, U) → Γ(N, U)` satisfying the Leibniz rule and killing the base subrings. -/
abbrev RelDerivation (N : X.Modules) : Type u :=
  PresheafOfModules.Derivation'
    (show PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) from
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj N.val) (baseInclusion f)

/-- The universal property of `Ω¹_{X/S}`: morphisms `Ω¹_{X/S} ⟶ N` are the relative
derivations into `N`. -/
def homEquiv (N : X.Modules) : (relativeDifferentials f ⟶ N) ≃ RelDerivation f N :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).trans
    { toFun := fun φ =>
        (PresheafOfModules.DifferentialsConstruction.derivation' (baseInclusion f)).postcomp φ
      invFun := fun d =>
        (PresheafOfModules.DifferentialsConstruction.isUniversal' (baseInclusion f)).desc d
      left_inv := fun _ =>
        (PresheafOfModules.DifferentialsConstruction.isUniversal'
          (baseInclusion f)).postcomp_injective _ _
          ((PresheafOfModules.DifferentialsConstruction.isUniversal' (baseInclusion f)).fac _)
      right_inv := fun d =>
        (PresheafOfModules.DifferentialsConstruction.isUniversal' (baseInclusion f)).fac d }

/-- The universal derivation `d : 𝒪_X → Ω¹_{X/S}`. -/
def universalDerivation : RelDerivation f (relativeDifferentials f) :=
  homEquiv f _ (𝟙 _)

variable {f}

namespace RelDerivation

variable {N : X.Modules} (d : RelDerivation f N)

theorem d_map {U V : X.Opens} (i : V ⟶ U) (s : Γ(X, U)) :
    d.d (X.presheaf.map i.op s) = N.presheaf.map i.op (d.d s) :=
  PresheafOfModules.Derivation.d_map d i.op s

theorem d_mul {U : X.Opens} (s t : Γ(X, U)) :
    (d.d (s * t) : Γ(N, U)) = s • (d.d t : Γ(N, U)) + t • (d.d s : Γ(N, U)) :=
  PresheafOfModules.Derivation.d_mul d s t

theorem d_add {U : X.Opens} (s t : Γ(X, U)) :
    (d.d (s + t) : Γ(N, U)) = d.d s + d.d t :=
  map_add _ s t

theorem d_base {U : X.Opens} (s : Γ(X, U)) (hs : s ∈ baseSubring f U) :
    (d.d s : Γ(N, U)) = 0 :=
  PresheafOfModules.Derivation'.d_app d (X := op U) ⟨s, hs⟩

/-- A relative derivation kills the pullbacks of sections of `𝒪_S`. -/
theorem d_appLE {V : S.Opens} {U : X.Opens} (h : U ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    (d.d (f.appLE V U h r) : Γ(N, U)) = 0 :=
  d.d_base _ (appLE_mem_baseSubring f h r)

/-- Postcomposition of a derivation with a morphism of `𝒪_X`-modules. -/
def postcomp {N' : X.Modules} (φ : N ⟶ N') : RelDerivation f N' :=
  PresheafOfModules.Derivation.postcomp d ((PresheafOfModules.restrictScalars _).map φ.val)

@[simp]
theorem postcomp_d {N' : X.Modules} (φ : N ⟶ N') {U : X.Opens} (s : Γ(X, U)) :
    (d.postcomp φ).d s = φ.app U (d.d s) :=
  rfl

/-- A relative derivation on the sections over `U`, as an additive map `Γ(X, U) → Γ(N, U)`. -/
def sec (U : X.Opens) : Γ(X, U) →+ Γ(N, U) := d.d

theorem sec_apply {U : X.Opens} (s : Γ(X, U)) : d.sec U s = d.d s :=
  rfl

theorem sec_mul {U : X.Opens} (s t : Γ(X, U)) :
    d.sec U (s * t) = s • d.sec U t + t • d.sec U s :=
  d.d_mul s t

theorem sec_map {U V : X.Opens} (i : V ⟶ U) (s : Γ(X, U)) :
    d.sec V (X.presheaf.map i.op s) = N.presheaf.map i.op (d.sec U s) :=
  d.d_map i s

theorem sec_base {U : X.Opens} (s : Γ(X, U)) (hs : s ∈ baseSubring f U) : d.sec U s = 0 :=
  d.d_base s hs

theorem sec_appLE {V : S.Opens} {U : X.Opens} (h : U ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    d.sec U (f.appLE V U h r) = 0 :=
  d.d_appLE h r

@[ext]
theorem ext {d' : RelDerivation f N}
    (h : ∀ (U : X.Opens) (s : Γ(X, U)), (d.d s : Γ(N, U)) = d'.d s) : d = d' := by
  apply PresheafOfModules.Derivation.ext
  ext U s
  exact h U.unop s

end RelDerivation

theorem homEquiv_apply_d {N : X.Modules} (φ : relativeDifferentials f ⟶ N) {U : X.Opens}
    (s : Γ(X, U)) : (homEquiv f N φ).d s = φ.app U ((universalDerivation f).d s) := by
  simp only [homEquiv, universalDerivation]
  rfl

end Differentials

section Locality

variable {f}

/-- Sections of an `𝒪_X`-module over an open contained in an affine open are determined by their
restrictions to the basic opens contained in it. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.ext_of_basicOpen (N : X.Modules) {W U : X.Opens}
    (hW : IsAffineOpen W) (hU : U ≤ W) (s t : Γ(N, U))
    (h : ∀ (g : Γ(X, W)) (hg : X.basicOpen g ≤ U),
      N.presheaf.map (homOfLE hg).op s = N.presheaf.map (homOfLE hg).op t) : s = t := by
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let ι := {g : Γ(X, W) // X.basicOpen g ≤ U}
  refine F.eq_of_locally_eq' (fun i : ι => X.basicOpen i.1) U (fun i => homOfLE i.2) ?_ s t
    (fun i => h i.1 i.2)
  intro x hx
  obtain ⟨g, hgU, hxg⟩ := hW.exists_basicOpen_le ⟨x, hx⟩ (hU hx)
  exact Opens.mem_iSup.mpr ⟨⟨g, hgU⟩, hxg⟩

/-- **Locality of derivations.** Two relative derivations which agree on the sections over an
affine open `W` agree on the sections over every open `U ≤ W` (blueprint
`lem:sm-omega-locality`). -/
theorem RelDerivation.ext_of_le_affine {N : X.Modules} (d d' : RelDerivation f N) {W : X.Opens}
    (hW : IsAffineOpen W) (h : ∀ a : Γ(X, W), (d.d a : Γ(N, W)) = d'.d a) {U : X.Opens}
    (hU : U ≤ W) (s : Γ(X, U)) : (d.d s : Γ(N, U)) = d'.d s := by
  apply N.ext_of_basicOpen hW hU
  intro g hg
  rw [← RelDerivation.d_map, ← RelDerivation.d_map]
  set t := X.presheaf.map (homOfLE hg).op s
  let := (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  have hloc := hW.isLocalization_basicOpen g
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) t
  simp only [RingHom.algebraMap_toAlgebra] at ha
  have hres : ∀ b : Γ(X, W), d.d (X.presheaf.map (homOfLE (X.basicOpen_le g)).op b) =
      d'.d (X.presheaf.map (homOfLE (X.basicOpen_le g)).op b) := by
    intro b
    rw [RelDerivation.d_map, RelDerivation.d_map, h b]
  have key := congrArg (fun z => d.d z) ha
  have key' := congrArg (fun z => d'.d z) ha
  simp only at key key'
  rw [RelDerivation.d_mul, hres, hres a] at key
  rw [RelDerivation.d_mul] at key'
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n)) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen g).pow n
  have : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n) • (d.d t : Γ(N, _)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n) • (d'.d t : Γ(N, _)) :=
    add_left_cancel (key.trans key'.symm)
  exact (hu.smul_left_cancel).mp this

end Locality

end DeJongAlterations.StableModification.Omega
