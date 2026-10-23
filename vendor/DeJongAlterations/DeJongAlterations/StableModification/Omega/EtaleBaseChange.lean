import DeJongAlterations.StableModification.Omega.EtaleNode

/-!
# Flat base change of sections over finite unions of basic opens

Step 3 of `lem:sm-omega-invertible` (blueprint `sm-omega-invertible.tex`,
`lem:sm-omega-flat-base-change`): the sections of `Ω¹_{X/S}`, and hence of
`ω_{X/S} = j_*(Ω¹|_U)`, over a quasi-compact open commute with flat (in particular étale)
base change on the source. M. Temkin, *Stable modification of relative curves*, §1.2,
T:1700–1704, uses the compatibility of `ω` with base change; for the elementary
`ω = j_*(Ω¹|_U)` this is the present statement together with the étale invariance of the
smooth locus.

Let `ψ : X' ⟶ X`, `θ : F ⟶ ψ_* G` a morphism of modules, `W ⊆ X` an open and `W' ≤ ψ⁻¹ W`
with `Γ(X, W) → Γ(X', W')` flat. For `Y ≤ W` the base change map
`Γ(X', W') ⊗_{Γ(X, W)} Γ(F, Y) → Γ(G, ψ⁻¹ Y ∩ W')` (`baseChangeSec`) is bijective for
`Y = D(b₁) ∪ … ∪ D(bₙ)` as soon as it is bijective on all basic opens
(`bijective_baseChangeSec_iSup`): the Čech sequence `0 → Γ(F, Y) → ∏ Γ(F, D(bᵢ)) → ∏ Γ(F, D(bᵢbⱼ))`
is exact (sheaf property), stays exact after the flat base change, and is compared with the
Čech sequence of `G` for the cover `ψ⁻¹ D(bᵢ) ∩ W'`.

* `SecOver F hY`: `Γ(F, Y)` as a `Γ(X, W)`-module (`hY : Y ≤ W`);
* `secLinear`, `baseChangeSec`: the maps; `baseChangeSec_restrict`: naturality;
* `bijective_baseChangeSec_iSup`: the base change theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct

universe u

namespace DeJongAlterations.StableModification.Omega

section BaseChange

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) {F : X.Modules} {G : X'.Modules}
  (θ : F ⟶ (Scheme.Modules.pushforward ψ).obj G)

/-- `θ` on sections over `Y`, as a map into `Γ(G, ψ⁻¹ Y)`. -/
noncomputable def secMap₀ (Y : X.Opens) (m : Γ(F, Y)) : Γ(G, ψ ⁻¹ᵁ Y) := θ.app Y m

theorem secMap₀_add (Y : X.Opens) (m m' : Γ(F, Y)) :
    secMap₀ ψ θ Y (m + m') = secMap₀ ψ θ Y m + secMap₀ ψ θ Y m' :=
  map_add (θ.app Y).hom m m'

theorem secMap₀_smul (Y : X.Opens) (r : Γ(X, Y)) (m : Γ(F, Y)) :
    secMap₀ ψ θ Y (r • m) = ψ.app Y r • secMap₀ ψ θ Y m :=
  Scheme.Modules.Hom.app_smul θ r m

theorem secMap₀_map {Y Y' : X.Opens} (h : Y' ≤ Y) (m : Γ(F, Y)) :
    secMap₀ ψ θ Y' (F.presheaf.map (homOfLE h).op m) =
      G.presheaf.map (homOfLE (ψ.preimage_mono h)).op (secMap₀ ψ θ Y m) :=
  Scheme.Modules.Hom.app_map θ (homOfLE h) m

end BaseChange


section SecOver

variable {X : Scheme.{u}}

/-- The sections `Γ(F, Y)` of an `𝒪_X`-module over an open `Y ≤ W`, as a `Γ(X, W)`-module through
restriction. -/
def SecOver (F : X.Modules) {W Y : X.Opens} (_ : Y ≤ W) : Type u := Γ(F, Y)

variable (F : X.Modules) {W Y : X.Opens} (hY : Y ≤ W)

instance : AddCommGroup (SecOver F hY) := inferInstanceAs (AddCommGroup Γ(F, Y))

noncomputable instance : Module Γ(X, W) (SecOver F hY) :=
  Module.compHom Γ(F, Y) (res hY)

/-- The identification of `SecOver F hY` with `Γ(F, Y)`. -/
def SecOver.equiv : SecOver F hY ≃+ Γ(F, Y) := AddEquiv.refl _

variable {F hY}

theorem SecOver.smul_def (a : Γ(X, W)) (m : SecOver F hY) :
    SecOver.equiv F hY (a • m) = res hY a • SecOver.equiv F hY m := rfl

/-- Restriction of sections as a `Γ(X, W)`-linear map. -/
noncomputable def SecOver.restrict {Z : X.Opens} (h : Z ≤ Y) :
    SecOver F hY →ₗ[Γ(X, W)] SecOver F (h.trans hY) where
  toFun m := F.presheaf.map (homOfLE h).op (SecOver.equiv F hY m)
  map_add' m m' := map_add _ _ _
  map_smul' a m := by
    change F.presheaf.map (homOfLE h).op (res hY a • SecOver.equiv F hY m) =
      res (h.trans hY) a • F.presheaf.map (homOfLE h).op (SecOver.equiv F hY m)
    rw [Ω_map_res_smul, res_res]

theorem SecOver.restrict_apply {Z : X.Opens} (h : Z ≤ Y) (m : SecOver F hY) :
    SecOver.equiv F _ (SecOver.restrict h m) =
      F.presheaf.map (homOfLE h).op (SecOver.equiv F hY m) := rfl

end SecOver


section FBC

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) {F : X.Modules} {G : X'.Modules}
  (θ : F ⟶ (Scheme.Modules.pushforward ψ).obj G) {W : X.Opens} {W' : X'.Opens}
  (hWW' : W' ≤ ψ ⁻¹ᵁ W)

/-- The algebra `Γ(X, W) → Γ(X', W')` induced by `ψ`. -/
abbrev pullAlgebra : Algebra Γ(X, W) Γ(X', W') := (ψ.appLE W W' hWW').hom.toAlgebra

/-- The `Γ(X, W)`-module structure on `SecOver G hZ` (`Z ≤ W'`) through `ψ`. -/
abbrev pullModule {Z : X'.Opens} (hZ : Z ≤ W') : Module Γ(X, W) (SecOver G hZ) :=
  Module.compHom (SecOver G hZ) (ψ.appLE W W' hWW').hom

theorem pullIsScalarTower {Z : X'.Opens} (hZ : Z ≤ W') :
    letI := pullAlgebra ψ hWW'
    letI := pullModule ψ hWW' (G := G) hZ
    IsScalarTower Γ(X, W) Γ(X', W') (SecOver G hZ) := by
  let := pullAlgebra ψ hWW'
  let := pullModule ψ hWW' (G := G) hZ
  exact IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

theorem appLE_res {Y : X.Opens} (hY : Y ≤ W) (a : Γ(X, W)) :
    res (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W') (ψ.appLE W W' hWW' a) =
      res (inf_le_left : ψ ⁻¹ᵁ Y ⊓ W' ≤ ψ ⁻¹ᵁ Y) (ψ.app Y (res hY a)) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply (X.presheaf.map _), Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map]

/-- `θ` on the sections over `Y ≤ W`, restricted to `ψ⁻¹ Y ∩ W'`, as a `Γ(X, W)`-linear map. -/
noncomputable def secLinear {Y : X.Opens} (hY : Y ≤ W) :
    letI := pullModule ψ hWW' (G := G) (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W')
    SecOver F hY →ₗ[Γ(X, W)] SecOver G (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W') :=
  letI := pullModule ψ hWW' (G := G) (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W')
  { toFun := fun m => G.presheaf.map (homOfLE inf_le_left).op
      (secMap₀ ψ θ Y (SecOver.equiv F hY m))
    map_add' := fun m m' =>
      (congrArg (G.presheaf.map (homOfLE inf_le_left).op) (secMap₀_add ψ θ Y m m')).trans
        (map_add _ _ _)
    map_smul' := fun a m => by
      change G.presheaf.map (homOfLE inf_le_left : ψ ⁻¹ᵁ Y ⊓ W' ⟶ ψ ⁻¹ᵁ Y).op
          (secMap₀ ψ θ Y (res hY a • SecOver.equiv F hY m)) =
        res (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W') (ψ.appLE W W' hWW' a) •
          G.presheaf.map (homOfLE inf_le_left : ψ ⁻¹ᵁ Y ⊓ W' ⟶ ψ ⁻¹ᵁ Y).op
            (secMap₀ ψ θ Y (SecOver.equiv F hY m))
      rw [secMap₀_smul, Ω_map_res_smul, appLE_res ψ hWW' hY] }

/-- The base change map `Γ(X', W') ⊗_{Γ(X, W)} Γ(F, Y) → Γ(G, ψ⁻¹ Y ∩ W')`. -/
noncomputable def baseChangeSec {Y : X.Opens} (hY : Y ≤ W) :
    letI := pullAlgebra ψ hWW'
    Γ(X', W') ⊗[Γ(X, W)] SecOver F hY →ₗ[Γ(X', W')]
      SecOver G (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W') :=
  letI := pullAlgebra ψ hWW'
  letI := pullModule ψ hWW' (G := G) (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W')
  haveI := pullIsScalarTower ψ hWW' (G := G) (inf_le_right : ψ ⁻¹ᵁ Y ⊓ W' ≤ W')
  (secLinear ψ θ hWW' hY).liftBaseChange Γ(X', W')

end FBC


section Sheaf

variable {X : Scheme.{u}} (F : X.Modules)

theorem _root_.AlgebraicGeometry.Scheme.Modules.eq_of_restrict_eq {ι : Type*} (U : ι → X.Opens)
    {V : X.Opens}
    (hV : V ≤ ⨆ i, U i) (hU : ∀ i, U i ≤ V) (s t : Γ(F, V))
    (h : ∀ i, F.presheaf.map (homOfLE (hU i)).op s = F.presheaf.map (homOfLE (hU i)).op t) :
    s = t := by
  let F' : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  exact F'.eq_of_locally_eq' U V (fun i => homOfLE (hU i)) hV s t h

theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_glue {ι : Type*} (U : ι → X.Opens)
    {V : X.Opens}
    (hV : V ≤ ⨆ i, U i) (hU : ∀ i, U i ≤ V) (sf : ∀ i, Γ(F, U i))
    (h : ∀ i j, F.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (sf i) =
      F.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (sf j)) :
    ∃ s : Γ(F, V), ∀ i, F.presheaf.map (homOfLE (hU i)).op s = sf i := by
  let F' : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  obtain ⟨s, hs, -⟩ := F'.existsUnique_gluing' U V (fun i => homOfLE (hU i)) hV sf h
  exact ⟨s, hs⟩

end Sheaf


section TensorPi

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A] {M : Type*}
  [AddCommGroup M] [Module R M] {ι : Type*} {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

theorem piRightHom_lTensor_pi (φ : ∀ i, M →ₗ[R] N i) (t : A ⊗[R] M) (i : ι) :
    TensorProduct.piRightHom R A A N ((LinearMap.pi φ).lTensor A t) i = (φ i).lTensor A t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, Pi.add_apply, ha, hb, map_add]
  | tmul a m => rfl

end TensorPi

section FBCProof

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) {F : X.Modules} {G : X'.Modules}
  (θ : F ⟶ (Scheme.Modules.pushforward ψ).obj G) {W : X.Opens} {W' : X'.Opens}
  (hWW' : W' ≤ ψ ⁻¹ᵁ W)

theorem secLinear_restrict {Y Z : X.Opens} (hY : Y ≤ W) (h : Z ≤ Y) (m : SecOver F hY) :
    secLinear ψ θ hWW' (h.trans hY) (SecOver.restrict h m) =
      SecOver.restrict (inf_le_inf_right W' (ψ.preimage_mono h)) (secLinear ψ θ hWW' hY m) := by
  change G.presheaf.map (homOfLE inf_le_left).op
      (secMap₀ ψ θ Z (F.presheaf.map (homOfLE h).op (SecOver.equiv F hY m))) =
    G.presheaf.map (homOfLE (inf_le_inf_right W' (ψ.preimage_mono h))).op
      (G.presheaf.map (homOfLE inf_le_left).op (secMap₀ ψ θ Y (SecOver.equiv F hY m)))
  rw [secMap₀_map, map_map_eq, map_map_eq]

theorem baseChangeSec_restrict {Y Z : X.Opens} (hY : Y ≤ W) (h : Z ≤ Y)
    (t : letI := pullAlgebra ψ hWW'; Γ(X', W') ⊗[Γ(X, W)] SecOver F hY) :
    letI := pullAlgebra ψ hWW'
    baseChangeSec ψ θ hWW' (h.trans hY) ((SecOver.restrict h).lTensor Γ(X', W') t) =
      SecOver.restrict (inf_le_inf_right W' (ψ.preimage_mono h))
        (baseChangeSec ψ θ hWW' hY t) := by
  let := pullAlgebra ψ hWW'
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul a m =>
    rw [LinearMap.lTensor_tmul]
    change a • secLinear ψ θ hWW' (h.trans hY) (SecOver.restrict h m) =
      SecOver.restrict _ (a • secLinear ψ θ hWW' hY m)
    rw [LinearMap.map_smul, secLinear_restrict]

end FBCProof


section FBCMain

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) {F : X.Modules} {G : X'.Modules}
  (θ : F ⟶ (Scheme.Modules.pushforward ψ).obj G) {W : X.Opens} {W' : X'.Opens}
  (hWW' : W' ≤ ψ ⁻¹ᵁ W)

/-- **Flat base change of sections over a finite union of basic opens.** If `Γ(X, W) → Γ(X', W')`
is flat and the base change map `Γ(X', W') ⊗ Γ(F, D(b)) → Γ(G, ψ⁻¹ D(b) ∩ W')` is bijective for
every basic open `D(b) ⊆ W`, then it is bijective for every finite union of basic opens. -/
theorem bijective_baseChangeSec_iSup
    (hflat : letI := pullAlgebra ψ hWW'; Module.Flat Γ(X, W) Γ(X', W'))
    (hb : ∀ b : Γ(X, W), Function.Bijective (baseChangeSec ψ θ hWW' (X.basicOpen_le b)))
    {n : ℕ} (b : Fin n → Γ(X, W)) :
    Function.Bijective (baseChangeSec ψ θ hWW' (iSup_le fun i => X.basicOpen_le (b i))) := by
  let := pullAlgebra ψ hWW'
  set U : Fin n → X.Opens := fun i => X.basicOpen (b i)
  set Y := ⨆ i, U i
  have hY : Y ≤ W := iSup_le fun i => X.basicOpen_le (b i)
  have hUY : ∀ i, U i ≤ Y := le_iSup U
  have hUW : ∀ i, U i ≤ W := fun i => X.basicOpen_le (b i)
  have hPW : ∀ p : Fin n × Fin n, U p.1 ⊓ U p.2 ≤ W := fun p => inf_le_left.trans (hUW p.1)
  -- injectivity on the pairwise intersections
  have hpair : ∀ p : Fin n × Fin n, Function.Injective (baseChangeSec ψ θ hWW' (hPW p)) := by
    intro p
    have key : ∀ (Y₂ : X.Opens) (h₂ : Y₂ ≤ W), Y₂ = X.basicOpen (b p.1 * b p.2) →
        Function.Injective (baseChangeSec ψ θ hWW' h₂) := by
      rintro _ _ rfl
      exact (hb _).1
    exact key _ _ (X.basicOpen_mul _ _).symm
  -- the Čech maps downstairs
  let ρ : SecOver F hY →ₗ[Γ(X, W)] (∀ i, SecOver F (hUW i)) :=
    LinearMap.pi fun i => SecOver.restrict (hUY i)
  let δ : (∀ i, SecOver F (hUW i)) →ₗ[Γ(X, W)] (∀ p : Fin n × Fin n, SecOver F (hPW p)) :=
    LinearMap.pi fun p => (SecOver.restrict inf_le_left) ∘ₗ LinearMap.proj p.1 -
      (SecOver.restrict inf_le_right) ∘ₗ LinearMap.proj p.2
  have hρ : Function.Injective ρ := by
    intro m m' hmm'
    apply F.eq_of_restrict_eq U (le_refl Y) hUY
    intro i
    exact congrFun hmm' i
  have hexact : Function.Exact ρ δ := by
    intro s
    constructor
    · intro hs
      have hcompat : ∀ i j, F.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
          (SecOver.equiv F _ (s i)) = F.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op
          (SecOver.equiv F _ (s j)) := by
        intro i j
        have := congrFun hs (i, j)
        exact sub_eq_zero.mp this
      obtain ⟨m, hm⟩ := F.exists_glue U (le_refl Y) hUY (fun i => SecOver.equiv F _ (s i)) hcompat
      exact ⟨m, funext hm⟩
    · rintro ⟨m, rfl⟩
      funext p
      change F.presheaf.map _ (F.presheaf.map _ (SecOver.equiv F hY m)) -
        F.presheaf.map _ (F.presheaf.map _ (SecOver.equiv F hY m)) = 0
      rw [map_map_eq, map_map_eq, sub_self]
  have hρT : Function.Injective (ρ.lTensor Γ(X', W')) :=
    Module.Flat.lTensor_preserves_injective_linearMap ρ hρ
  have hexactT : Function.Exact (ρ.lTensor Γ(X', W')) (δ.lTensor Γ(X', W')) :=
    Module.Flat.lTensor_exact Γ(X', W') hexact
  have hpiR : Function.Injective (TensorProduct.piRightHom Γ(X, W) Γ(X', W') Γ(X', W')
      (fun p : Fin n × Fin n => SecOver F (hPW p))) := by
    intro x y hxy
    simpa only [← TensorProduct.piRight_apply] using
      (TensorProduct.piRight Γ(X, W) Γ(X', W') Γ(X', W') _).injective
        (by simpa only [TensorProduct.piRight_apply])
  -- the cover upstairs
  have hY' : ψ ⁻¹ᵁ Y ⊓ W' ≤ ⨆ i, (ψ ⁻¹ᵁ U i ⊓ W') := by
    rw [Scheme.Hom.preimage_iSup, iSup_inf_eq]
  have hU'Y' : ∀ i, ψ ⁻¹ᵁ U i ⊓ W' ≤ ψ ⁻¹ᵁ Y ⊓ W' :=
    fun i => inf_le_inf_right W' (ψ.preimage_mono (hUY i))
  constructor
  · intro t t' htt'
    apply hρT
    apply (TensorProduct.piRight Γ(X, W) Γ(X', W') Γ(X', W') _).injective
    funext i
    have hcomp : ∀ x, TensorProduct.piRightHom Γ(X, W) Γ(X', W') Γ(X', W')
        (fun i => SecOver F (hUW i)) (ρ.lTensor Γ(X', W') x) i =
        (SecOver.restrict (hUY i)).lTensor Γ(X', W') x :=
      fun x => piRightHom_lTensor_pi Γ(X', W') _ x i
    simp only [TensorProduct.piRight_apply]
    rw [hcomp, hcomp]
    apply (hb (b i)).1
    rw [baseChangeSec_restrict, baseChangeSec_restrict, htt']
  · intro g
    have hgi : ∀ i, ∃ t : Γ(X', W') ⊗[Γ(X, W)] SecOver F (hUW i),
        baseChangeSec ψ θ hWW' (hUW i) t = SecOver.restrict (hU'Y' i) g := fun i =>
      (hb (b i)).2 _
    choose t ht using hgi
    set T := (TensorProduct.piRight Γ(X, W) Γ(X', W') Γ(X', W') _).symm t
    have hTi : ∀ i,
        (LinearMap.proj (R := Γ(X, W)) (φ := fun i => SecOver F (hUW i)) i).lTensor Γ(X', W') T =
        t i := by
      intro i
      have := piRightHom_lTensor_pi Γ(X', W') (fun i => LinearMap.proj (R := Γ(X, W))
        (φ := fun i => SecOver F (hUW i)) i) T i
      rw [LinearMap.pi_proj, LinearMap.lTensor_id, LinearMap.id_apply] at this
      rw [← this, ← TensorProduct.piRight_apply, LinearEquiv.apply_symm_apply]
    have hδT : δ.lTensor Γ(X', W') T = 0 := by
      apply (TensorProduct.piRight Γ(X, W) Γ(X', W') Γ(X', W') _).injective
      funext p
      rw [map_zero, Pi.zero_apply, TensorProduct.piRight_apply, piRightHom_lTensor_pi]
      apply hpair p
      rw [map_zero, LinearMap.lTensor_sub, LinearMap.sub_apply, map_sub, LinearMap.lTensor_comp,
        LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply, hTi, hTi]
      have e1 := baseChangeSec_restrict ψ θ hWW' (hUW p.1) (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1)
        (t p.1)
      have e2 := baseChangeSec_restrict ψ θ hWW' (hUW p.2) (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2)
        (t p.2)
      rw [ht] at e1 e2
      refine (congrArg₂ (· - ·) e1 e2).trans ?_
      rw [sub_eq_zero]
      apply (SecOver.equiv G _).injective
      simp only [SecOver.restrict_apply]
      rw [map_map_eq, map_map_eq]
    obtain ⟨t0, ht0⟩ := (hexactT T).mp hδT
    refine ⟨t0, ?_⟩
    apply G.eq_of_restrict_eq (fun i => ψ ⁻¹ᵁ U i ⊓ W') hY' hU'Y'
    intro i
    have h1 := baseChangeSec_restrict ψ θ hWW' hY (hUY i) t0
    have h2 : (SecOver.restrict (hUY i)).lTensor Γ(X', W') t0 = t i := by
      rw [← hTi i, ← ht0, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      rfl
    rw [h2, ht i] at h1
    exact h1.symm

end FBCMain

end DeJongAlterations.StableModification.Omega
