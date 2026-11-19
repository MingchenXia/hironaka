import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.Topology.Sheaves.Stalks

/-! Stalk-ideal families on locally ringed spaces and the local Noether property (lane G10P,
run 0080; the generic half of `G10.FIBMOD.01` / `G10.COMPACT.01`).  Blueprint:
`hironaka-g10-pn-ideal-noether.tex`.

A (coherent) ideal sheaf of `𝒪_X` is recorded by its stalks `J x ⊆ 𝒪_{X,x}`; it is *locally
finitely generated* when near every point the SAME finitely many sections span it at every nearby
point.  An ascending chain `J 0 ≤ J 1 ≤ ⋯` is *locally stationary at `p`* when ONE open `V ∋ p` and
ONE tail `N` satisfy `J m ⊆ J N` on `V` for all `m ≥ N`.  This file proves, for arbitrary locally
ringed spaces:

* the compact assembly: local stationarity at every point of a compact `K` gives ONE tail `N` and
  ONE open `W ⊇ K` with `J m = J N` on `W` for all `m ≥ N` (finite subcover, maximum of the tails);
* transport along morphisms: pulled families `J (f y) 𝒪_{Y,y}` stay locally finitely generated and
  ascending; stationarity descends along any morphism and ascends along open immersions (the stalk
  maps are isomorphisms); so the local Noether property is local on `X` and passes from an ambient
  space to a subspace along any morphism admitting a monotone, generation-preserving push of
  ideal families whose pull returns the family (`hasLocalNoetherProperty_of_push`). -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.HironakaG10PNIdealFamily

noncomputable section

universe u

section Family

variable (X : LocallyRingedSpace.{u})

/-- An ideal family is **locally finitely generated** (a coherent ideal sheaf of `𝒪_X`): near every
point the germs of the SAME finitely many sections span it at every nearby point. -/
def IsLocallyFinitelyGenerated (J : ∀ x : X, Ideal (X.presheaf.stalk x)) : Prop :=
  ∀ x : X, ∃ (W : Opens X) (_hxW : x ∈ W) (r : ℕ) (s : Fin r → X.presheaf.obj (op W)),
    ∀ (y : X) (hy : y ∈ W), J y = Ideal.span (Set.range fun i => X.presheaf.germ W y hy (s i))

/-- An ascending chain of ideal families. -/
def IsAscending (J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)) : Prop :=
  ∀ (m : ℕ) (x : X), J m x ≤ J (m + 1) x

/-- **One neighbourhood and one tail at `p`**: an open `V ∋ p` and `N` with `J m ⊆ J N` on `V` for
every `m ≥ N`. -/
def IsLocallyStationaryAt (J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)) (p : X) : Prop :=
  ∃ (N : ℕ) (V : Opens X), p ∈ V ∧ ∀ m, N ≤ m → ∀ x : X, x ∈ V → J m x ≤ J N x

/-- **The local Noether property**: every ascending chain of locally finitely generated ideal
families is locally stationary at every point. -/
def HasLocalNoetherProperty : Prop :=
  ∀ J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x), IsAscending X J →
    (∀ m, IsLocallyFinitelyGenerated X (J m)) → ∀ p : X, IsLocallyStationaryAt X J p

variable {X}

theorem IsAscending.le {J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)} (hJ : IsAscending X J)
    {m m' : ℕ} (h : m ≤ m') (x : X) : J m x ≤ J m' x := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (hJ _ x)

/-- **Compact assembly (finite subcover, maximum of the tails).**  If an ascending chain is locally
stationary at every point of a compact `K`, there are ONE tail `N` and ONE open `W ⊇ K` with
`J m = J N` on `W` for all `m ≥ N`.  No infinitely many neighbourhoods are intersected. -/
theorem exists_stationary_nhds {J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsAscending X J) (K : Set X) (hK : IsCompact K)
    (hloc : ∀ p ∈ K, IsLocallyStationaryAt X J p) :
    ∃ (N : ℕ) (W : Opens X), K ⊆ (W : Set X) ∧
      ∀ m, N ≤ m → ∀ x : X, x ∈ W → J m x = J N x := by
  classical
  choose N V hpV hV using fun p : K => hloc p.1 p.2
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun p : K => (V p : Set X))
    (fun p => (V p).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpV ⟨x, hx⟩⟩)
  refine ⟨s.sup N, ⨆ p ∈ s, V p, ?_, ?_⟩
  · intro x hx
    have hx' := hs hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨p, hp, hxp⟩ := hx'
    change x ∈ ⨆ p ∈ s, V p
    simp only [Opens.mem_iSup]
    exact ⟨p, hp, hxp⟩
  · intro m hm x hx
    simp only [Opens.mem_iSup] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    have hNp : N p ≤ s.sup N := Finset.le_sup hp
    exact le_antisymm ((hV p m (hNp.trans hm) x hxp).trans (hJ.le hNp x)) (hJ.le hm x)

/-- **No strict increase at every step (termination form).**  In the situation of
`exists_stationary_nhds` it is impossible that at every step the chain strictly grows at some
point of `K`. -/
theorem not_forall_exists_strict {J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsAscending X J) (K : Set X) (hK : IsCompact K)
    (hloc : ∀ p ∈ K, IsLocallyStationaryAt X J p) :
    ¬ ∀ m : ℕ, ∃ x ∈ K, J m x < J (m + 1) x := by
  intro h
  obtain ⟨N, W, hKW, hW⟩ := exists_stationary_nhds hJ K hK hloc
  obtain ⟨x, hxK, hlt⟩ := h N
  have h1 := hW (N + 1) (Nat.le_succ N) x (hKW hxK)
  rw [h1] at hlt
  exact lt_irrefl _ hlt

/-- The compact form of the local Noether property. -/
theorem HasLocalNoetherProperty.exists_stationary_nhds (hX : HasLocalNoetherProperty X)
    {J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)} (hJ : IsAscending X J)
    (hfg : ∀ m, IsLocallyFinitelyGenerated X (J m)) (K : Set X) (hK : IsCompact K) :
    ∃ (N : ℕ) (W : Opens X), K ⊆ (W : Set X) ∧
      ∀ m, N ≤ m → ∀ x : X, x ∈ W → J m x = J N x :=
  HironakaG10PNIdealFamily.exists_stationary_nhds hJ K hK fun p _ => hX J hJ hfg p

end Family

section Transport

variable {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)

/-- The pulled family `J (f y) 𝒪_{Y,y}` (the ideal generated by the image under the stalk map). -/
def pullFamily (J : ∀ x : X, Ideal (X.presheaf.stalk x)) (y : Y) : Ideal (Y.presheaf.stalk y) :=
  Ideal.map (f.stalkMap y).hom (J (f.base y))

/-- Pulled families of locally finitely generated families are locally finitely generated: the
pulled sections `f.c (s i)` generate. -/
theorem isLocallyFinitelyGenerated_pull {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGenerated X J) : IsLocallyFinitelyGenerated Y (pullFamily f J) := by
  intro y
  obtain ⟨W, hyW, r, s, hs⟩ := hJ (f.base y)
  refine ⟨(Opens.map f.base).obj W, hyW, r, fun i => f.c.app (op W) (s i), ?_⟩
  intro y' hy'
  rw [pullFamily, hs (f.base y') hy', Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun i => LocallyRingedSpace.stalkMap_germ_apply f W y' hy' (s i)))

theorem IsAscending.pull {J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)} (hJ : IsAscending X J) :
    IsAscending Y (fun m => pullFamily f (J m)) :=
  fun m y => Ideal.map_mono (hJ m (f.base y))

/-- Stationarity DESCENDS along any morphism, for families that are pulled back. -/
theorem isLocallyStationaryAt_of_eq_pull {J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)}
    {J' : ℕ → ∀ y : Y, Ideal (Y.presheaf.stalk y)} (hJ' : ∀ m y, J' m y = pullFamily f (J m) y)
    (y : Y) (h : IsLocallyStationaryAt X J (f.base y)) : IsLocallyStationaryAt Y J' y := by
  obtain ⟨N, V, hyV, hV⟩ := h
  refine ⟨N, (Opens.map f.base).obj V, hyV, fun m hm y' hy' => ?_⟩
  rw [hJ', hJ']
  exact Ideal.map_mono (hV m hm (f.base y') hy')

/-- Stationarity ASCENDS along an open immersion (its stalk maps are isomorphisms and it maps opens
to opens). -/
theorem isLocallyStationaryAt_of_pull [hf : LocallyRingedSpace.IsOpenImmersion f]
    {J : ℕ → ∀ x : X, Ideal (X.presheaf.stalk x)} (y : Y)
    (h : IsLocallyStationaryAt Y (fun m => pullFamily f (J m)) y) :
    IsLocallyStationaryAt X J (f.base y) := by
  obtain ⟨N, V, hyV, hV⟩ := h
  have hopen : IsOpen (f.base '' (V : Set Y)) := hf.base_open.isOpenMap _ V.isOpen
  refine ⟨N, ⟨_, hopen⟩, ⟨y, hyV, rfl⟩, ?_⟩
  rintro m hm x ⟨y', hy', rfl⟩
  have hbij : Function.Bijective (f.stalkMap y').hom :=
    (asIso (f.stalkMap y')).commRingCatIsoToRingEquiv.bijective
  calc J m (f.base y')
      = Ideal.comap (f.stalkMap y').hom (Ideal.map (f.stalkMap y').hom (J m (f.base y'))) :=
        (Ideal.comap_map_of_bijective _ hbij).symm
    _ ≤ Ideal.comap (f.stalkMap y').hom (Ideal.map (f.stalkMap y').hom (J N (f.base y'))) :=
        Ideal.comap_mono (hV m hm y' hy')
    _ = J N (f.base y') := Ideal.comap_map_of_bijective _ hbij

/-- **The local Noether property is local**: if every point lies in the image of an open
immersion from a space with the local Noether property, the space has it. -/
theorem hasLocalNoetherProperty_of_openImmersions {X : LocallyRingedSpace.{u}}
    (h : ∀ x : X, ∃ (Y : LocallyRingedSpace.{u}) (f : Y ⟶ X),
      LocallyRingedSpace.IsOpenImmersion f ∧ HasLocalNoetherProperty Y ∧ x ∈ Set.range f.base) :
    HasLocalNoetherProperty X := by
  intro J hJ hfg p
  obtain ⟨Y, f, hf, hY, y, rfl⟩ := h p
  exact @isLocallyStationaryAt_of_pull _ _ f hf J y
    (hY _ (hJ.pull f) (fun m => isLocallyFinitelyGenerated_pull f (hfg m)) y)

/-- **The local Noether property passes to a subspace along a push of ideal families.**  For a
morphism `f : Y ⟶ X` and a monotone push `P` of ideal families from `Y` to `X` which preserves local
finite generation and whose pull returns the family, the local Noether property of `X` gives that
of `Y` (for a closed embedding with surjective stalk maps, `P J` is the preimage of `J` and the
unit ideal off the image). -/
theorem hasLocalNoetherProperty_of_push (hX : HasLocalNoetherProperty X)
    (P : (∀ y : Y, Ideal (Y.presheaf.stalk y)) → ∀ x : X, Ideal (X.presheaf.stalk x))
    (hmono : ∀ J J' : ∀ y : Y, Ideal (Y.presheaf.stalk y), (∀ y, J y ≤ J' y) → ∀ x, P J x ≤ P J' x)
    (hfg : ∀ J, IsLocallyFinitelyGenerated Y J → IsLocallyFinitelyGenerated X (P J))
    (hpull : ∀ J y, J y = pullFamily f (P J) y) : HasLocalNoetherProperty Y := by
  intro J hJ hJfg y
  have hasc : IsAscending X (fun m => P (J m)) := fun m => hmono _ _ (hJ m)
  exact isLocallyStationaryAt_of_eq_pull f (fun m y' => hpull (J m) y') y
    (hX _ hasc (fun m => hfg _ (hJfg m)) (f.base y))

end Transport

end

end Hironaka.HironakaG10PNIdealFamily
