import Hironaka.Resolution.HironakaG10PNLayerStep

/-! The internally constructed finite downward chain of actual prime-kernel layers of ONE
ordinary original finitely presented module (lane G10P, runs 0079/0080; leaf
`G10.PN.4.downward_layer`).  Blueprint: `hironaka-g10-pn-downward-layers.tex`.

Ordinary inputs of the endpoint are only `n`, `U`, `F`, `[F.IsFinitePresentation]` and `p`.  The
original stalk prime series and ALL indexed prime targets are selected once, before any shrinking.
For every index, from the top down, the next layer is the LITERAL kernel of the actual epimorphic
lift `q` of the map `φ` defined from the retained `η`, the original quotient isomorphism `e_i` and
the prime target `θ_i`; its original stalk comparison is obtained from the step itself.  At the
bottom the zero original stalk gives an actual zero object on a smaller open.  Restriction of all
earlier layers to the final open (PN.5/PN.8) is NOT done here.

Design note (run 0080): every predicate that mentions a native finite presentation, a kernel or a
stalk functor is stated GENERICALLY in the stalk module `M` and the adjacent pair `N₀ ≤ N₁`
(`LayerState`, `LevelStep`, `BottomZero`), and its proof (`levelStep_of_state`) is generic too.
Elaborating such a term in a context that contains the selected series of the stalk of a fixed `F`
was measured to cost several hundred seconds of type class inference per occurrence; the recursion
`DownChain` and the endpoint only instantiate the generic predicates. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaG10PNDownwardLayers

open HironakaChowNativeFreePartContinuation
  HironakaChowNativePrimeSupportContinuation HironakaSingularModuleSheafStalk
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeLocalOverStalkTransport
  HironakaChowNativeLocalOverFiniteDataTransport HironakaNativeCanonicalSupportRestriction
  HironakaNativeCyclicCokernelRestriction HironakaChowNativeModuleStalkExact
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaSingularLocallyFreeStalk HironakaG10PNLayerStep

noncomputable section

variable {n : ℕ}

/-- The original stalk ring of a smaller original open `W ∋ p`, compared with the stalk ring of
the fixed original open `U` through the SAME ambient original stalk. -/
def layerRingEquiv (U : Opens (ComplexModel n)) (p : U) (W : Opens (ComplexModel n))
    (hpW : p.val ∈ W) : OriginalRingStalk W ⟨p.val, hpW⟩ ≃+* OriginalRingStalk U p :=
  (originalRestrictionStalkEquiv W ⟨p.val, hpW⟩).symm.trans (originalRestrictionStalkEquiv U p)

theorem originalImageOpen_le (U : Opens (ComplexModel n)) (V : Opens U) :
    originalImageOpen U V ≤ U := by
  rintro x ⟨u, _, rfl⟩
  exact u.property

set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar comparisons compose: restricting along the nested open and then along `W₁` is the
canonical comparison of the nested image open. -/
theorem layerRingEquiv_symm_comp (U : Opens (ComplexModel n)) (p : U)
    (W₁ : Opens (ComplexModel n)) (h₁ : p.val ∈ W₁) (V : Opens W₁)
    (hpV : (⟨p.val, h₁⟩ : W₁) ∈ V) :
    (layerRingEquiv U p (originalImageOpen W₁ V) ⟨⟨p.val, h₁⟩, hpV, rfl⟩).symm.toRingHom =
      (localOverRingStalkEquiv (originalSpace n) W₁ V ⟨p.val, h₁⟩ hpV).symm.toRingHom.comp
        (layerRingEquiv U p W₁ h₁).symm.toRingHom := by
  apply RingHom.ext
  intro x
  show originalRestrictionStalkEquiv (originalImageOpen W₁ V) ⟨p.val, ⟨⟨p.val, h₁⟩, hpV, rfl⟩⟩
      ((originalRestrictionStalkEquiv U p).symm x) =
    (localOverRingStalkEquiv (originalSpace n) W₁ V ⟨p.val, h₁⟩ hpV).symm
      (originalRestrictionStalkEquiv W₁ ⟨p.val, h₁⟩ ((originalRestrictionStalkEquiv U p).symm x))
  exact (congrArg (originalRestrictionStalkEquiv (originalImageOpen W₁ V)
      ⟨p.val, ⟨⟨p.val, h₁⟩, hpV, rfl⟩⟩) (RingEquiv.symm_apply_apply
        (originalRestrictionStalkEquiv W₁ ⟨p.val, h₁⟩)
        ((originalRestrictionStalkEquiv U p).symm x))).symm

/-- One state of the downward construction: an actual original FP module on a smaller original
open `W ∋ p` inside the common domain `D`, with its original stalk identified with `N`. -/
structure LayerState (U : Opens (ComplexModel n)) (p : U) (D : Opens (ComplexModel n))
    (M : ModuleCat.{0} (OriginalRingStalk U p)) (N : Submodule (OriginalRingStalk U p) M) where
  W : Opens (ComplexModel n)
  mem : p.val ∈ W
  le : W ≤ D
  T : OriginalModules W
  fp : T.IsFinitePresentation
  η : (ModuleCat.restrictScalars.{0} (layerRingEquiv U p W mem).symm.toRingHom).obj
      ((nativeStalkFunctor (originalOpenStructureSheaf W) ⟨p.val, mem⟩).obj T) ≅
    ModuleCat.of (OriginalRingStalk U p) N

set_option backward.isDefEq.respectTransparency.types false in
/-- The next state: the LITERAL kernel of the actual lift on the nested image open, with the
stalk comparison `η₀` of the step transported along the composite scalar restriction. -/
def LayerState.next {U : Opens (ComplexModel n)} {p : U} {D : Opens (ComplexModel n)}
    {M : ModuleCat.{0} (OriginalRingStalk U p)} {N₁ : Submodule (OriginalRingStalk U p) M}
    (s : LayerState U p D M N₁) (N₀ : Submodule (OriginalRingStalk U p) M)
    (C : OriginalModules s.W) (V : Opens s.W) (hpV : (⟨p.val, s.mem⟩ : s.W) ∈ V)
    (b : s.T.over V ⟶ C.over V)
    (hK : (kernel ((localOverTransport (originalSpace n) s.W V).map b)).IsFinitePresentation)
    (η₀ : (originalTransportedStalk (originalSpace n) s.W V ⟨p.val, s.mem⟩ hpV ⋙
        ModuleCat.restrictScalars.{0} (layerRingEquiv U p s.W s.mem).symm.toRingHom).obj
      (kernel ((localOverTransport (originalSpace n) s.W V).map b)) ≅
      ModuleCat.of (OriginalRingStalk U p) N₀) :
    LayerState U p D M N₀ where
  W := originalImageOpen s.W V
  mem := ⟨⟨p.val, s.mem⟩, hpV, rfl⟩
  le := (originalImageOpen_le s.W V).trans s.le
  T := kernel ((localOverTransport (originalSpace n) s.W V).map b)
  fp := hK
  η := ModuleCat.restrictScalarsComp'App _ _ _
      (layerRingEquiv_symm_comp U p s.W s.mem V hpV) _ ≪≫ η₀

set_option backward.isDefEq.respectTransparency.types false in
/-- The bottom property of a state: an actual zero neighbourhood of `p`. -/
def BottomZero {U : Opens (ComplexModel n)} {p : U} {D : Opens (ComplexModel n)}
    {M : ModuleCat.{0} (OriginalRingStalk U p)} {N : Submodule (OriginalRingStalk U p) M}
    (s : LayerState U p D M N) : Prop :=
  ∃ (V : Opens s.W) (_hpV : (⟨p.val, s.mem⟩ : s.W) ∈ V),
    IsZero ((localOverTransport (originalSpace n) s.W V).obj (s.T.over V))

set_option backward.isDefEq.respectTransparency.types false in
/-- ONE positive level `N₁ → N₀` of the downward construction (generic, non-recursive): the prime
target `B` is restricted to the current open and is natively FP with `θ` and both numerator laws,
`φ` is the lift of `η ≫ mkQ ≫ e ≫ θ⁻¹` and is surjective, the actual epimorphic lift `b` has all
the properties of the layer step, and the next state (the LITERAL kernel of the actual lift of
`φ`, with its stalk comparison `η₀` and both inclusion squares) satisfies `next`. -/
def LevelStep {U : Opens (ComplexModel n)} {p : U} {D : Opens (ComplexModel n)}
    {M : ModuleCat.{0} (OriginalRingStalk U p)} (N₀ N₁ : Submodule (OriginalRingStalk U p) M)
    (hle : N₀ ≤ N₁) (P : Ideal (OriginalRingStalk U p))
    (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[OriginalRingStalk U p] OriginalRingStalk U p ⧸ P)
    (B : NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom P))
    (hDB : D ≤ B.old.U)
    (s : LayerState U p D M N₁) (next : LayerState U p D M N₀ → Prop) : Prop :=
  let α := layerRingEquiv U p s.W s.mem
  let pW : s.W := ⟨p.val, s.mem⟩
  let S := ModuleCat.restrictScalars.{0} α.symm.toRingHom
  let st := nativeStalkFunctor (originalOpenStructureSheaf s.W) pW
  let C := primeTargetOnDomain B s.W (s.le.trans hDB)
  let κ := primeQuotientOnDomain B s.W (s.le.trans hDB)
  C.IsFinitePresentation ∧
  ∃ θ : S.obj (st.obj C) ≅ ModuleCat.of (OriginalRingStalk U p) (OriginalRingStalk U p ⧸ P),
    (∀ r : OriginalRingStalk s.W pW,
      θ.hom (originalUnitDomainStalkMap s.W κ pW r) = Submodule.Quotient.mk (α r)) ∧
    (∀ r : OriginalRingStalk s.W pW,
      θ.inv (Submodule.Quotient.mk (α r)) = originalUnitDomainStalkMap s.W κ pW r) ∧
    ∃ φ : st.obj s.T ⟶ st.obj C, Function.Surjective φ ∧
      S.map φ = s.η.hom ≫ ModuleCat.ofHom (N₀.submoduleOf N₁).mkQ ≫ e.toModuleIso.hom ≫ θ.inv ∧
      ∃ (V : Opens s.W) (hpV : pW ∈ V) (b : s.T.over V ⟶ C.over V),
        Epi b ∧
        ModuleCat.ofHom (stalkLinearMapOfOver (originalOpenStructureSheaf s.W) V b pW hpV) = φ ∧
        layerStepOnOpen (originalSpace n) s.W s.T C pW α N₀ N₁ hle P e s.η θ V hpV b ∧
        ∃ (hK : (kernel ((localOverTransport (originalSpace n) s.W V).map b)).IsFinitePresentation)
          (η₀ : (originalTransportedStalk (originalSpace n) s.W V pW hpV ⋙ S).obj
            (kernel ((localOverTransport (originalSpace n) s.W V).map b)) ≅
            ModuleCat.of (OriginalRingStalk U p) N₀),
          η₀.hom ≫ ModuleCat.ofHom (Submodule.inclusion hle) =
            (originalTransportedStalk (originalSpace n) s.W V pW hpV ⋙ S).map
                (kernel.ι ((localOverTransport (originalSpace n) s.W V).map b)) ≫
              (S.mapIso (native_original_stalk_iso (originalSpace n) s.W V s.T pW hpV) ≪≫
                s.η).hom ∧
          η₀.inv ≫ (originalTransportedStalk (originalSpace n) s.W V pW hpV ⋙ S).map
                (kernel.ι ((localOverTransport (originalSpace n) s.W V).map b)) =
            ModuleCat.ofHom (Submodule.inclusion hle) ≫
              (S.mapIso (native_original_stalk_iso (originalSpace n) s.W V s.T pW hpV) ≪≫
                s.η).inv ∧
          next (s.next N₀ C V hpV b hK η₀)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every state at a positive level carries the level step, for any continuation that holds for
every next state. -/
theorem levelStep_of_state {U : Opens (ComplexModel n)} {p : U} {D : Opens (ComplexModel n)}
    {M : ModuleCat.{0} (OriginalRingStalk U p)} (N₀ N₁ : Submodule (OriginalRingStalk U p) M)
    (hle : N₀ ≤ N₁) (P : Ideal (OriginalRingStalk U p))
    (e : (N₁ ⧸ N₀.submoduleOf N₁) ≃ₗ[OriginalRingStalk U p] OriginalRingStalk U p ⧸ P)
    (B : NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom P))
    (hDB : D ≤ B.old.U)
    (s : LayerState U p D M N₁) (next : LayerState U p D M N₀ → Prop)
    (hnext : ∀ s' : LayerState U p D M N₀, next s') :
    LevelStep N₀ N₁ hle P e B hDB s next := by
  let α := layerRingEquiv U p s.W s.mem
  let pW : s.W := ⟨p.val, s.mem⟩
  have hWB : s.W ≤ B.old.U := s.le.trans hDB
  obtain ⟨hC, θ, hforward, hinverse⟩ := prime_target_on_domain_property p.val
    (originalRestrictionStalkEquiv U p) P B s.W s.mem hWB
  obtain ⟨φ, hφ, hmap, V, hpV, b, hb, hbφ, hstep⟩ :=
    exists_native_layer_step (hT := s.fp) (hC := hC) n s.W s.T
      (primeTargetOnDomain B s.W hWB) pW α N₀ N₁ hle P e s.η θ
  have hstep' := hstep
  obtain ⟨_, _, _, hK, _, _, _, η₀, _, _, _, _, hInc, hInv, _⟩ := hstep'
  exact ⟨hC, θ, hforward, hinverse, φ, hφ, hmap, V, hpV, b, hb, hbφ, hstep, hK, η₀, hInc, hInv,
    hnext _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A state whose submodule is zero has an actual zero neighbourhood. -/
theorem bottomZero_of_state {U : Opens (ComplexModel n)} {p : U} {D : Opens (ComplexModel n)}
    {M : ModuleCat.{0} (OriginalRingStalk U p)} {N : Submodule (OriginalRingStalk U p) M}
    (hN : N = ⊥) (s : LayerState U p D M N) : BottomZero s := by
  subst hN
  have hzero : Subsingleton
      ((nativeStalkFunctor (originalOpenStructureSheaf s.W) ⟨p.val, s.mem⟩).obj s.T) :=
    ⟨fun x y => s.η.toLinearEquiv.injective (Subsingleton.elim _ _)⟩
  exact @zero_stalk_native_neighborhood (originalSpace n) s.W s.T s.fp ⟨p.val, s.mem⟩ hzero

/-- The index of the `k`-th original submodule as an element of `Fin (length + 1)`. -/
def seriesIndex {A : Type} [CommRing A] {M : ModuleCat.{0} A} (d : SelectedPrimeSeries A M)
    (k : ℕ) (hk : k ≤ d.s.length) : Fin (d.s.length + 1) :=
  ⟨k, Nat.lt_succ_of_le hk⟩

/-- The downward chain of actual layers below a state at level `k`.  At each positive level the
SAME preselected prime target `B_i` is used (`LevelStep`); at level `0` the zero original stalk
gives an actual zero object on a smaller open (`BottomZero`). -/
def DownChain {U : Opens (ComplexModel n)} {p : U} {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (D : Opens (ComplexModel n)) (hDB : ∀ j : Fin d.s.length, D ≤ (B j).old.U) :
    (k : ℕ) → (hk : k ≤ d.s.length) → LayerState U p D M (d.s (seriesIndex d k hk)) → Prop
  | 0, _, s => BottomZero s
  | k + 1, hk, s =>
    LevelStep (d.s (⟨k, Nat.lt_of_succ_le hk⟩ : Fin d.s.length).castSucc)
      (d.s (⟨k, Nat.lt_of_succ_le hk⟩ : Fin d.s.length).succ)
      (d.mono ⟨k, Nat.lt_of_succ_le hk⟩) (d.P ⟨k, Nat.lt_of_succ_le hk⟩).1
      (d.e ⟨k, Nat.lt_of_succ_le hk⟩) (B ⟨k, Nat.lt_of_succ_le hk⟩)
      (hDB ⟨k, Nat.lt_of_succ_le hk⟩) s (DownChain d B D hDB k (Nat.le_of_succ_le hk))

/-- Every state, at every level, carries the complete downward chain. -/
theorem downChain_of_state {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (D : Opens (ComplexModel n)) (hDB : ∀ j : Fin d.s.length, D ≤ (B j).old.U) :
    ∀ (k : ℕ) (hk : k ≤ d.s.length) (s : LayerState U p D M (d.s (seriesIndex d k hk))),
      DownChain d B D hDB k hk s
  | 0, hk, s => by
    have h0 : seriesIndex d 0 hk = 0 := Fin.ext rfl
    exact bottomZero_of_state ((congrArg d.s h0).trans d.head) s
  | k + 1, hk, s =>
    levelStep_of_state _ _ _ _ _ _ _ s _ (downChain_of_state d B D hDB k (Nat.le_of_succ_le hk))

set_option backward.isDefEq.respectTransparency.types false in
/-- The top state: the actual local restriction of the ordinary original `F` to the common
domain, with its original stalk identified with a submodule `N = ⊤`. -/
def topState (U : Opens (ComplexModel n)) (p : U) (F : OriginalModules U)
    [hF : F.IsFinitePresentation] (D : Opens (ComplexModel n)) (hpD : p.val ∈ D)
    (N : Submodule (OriginalRingStalk U p)
      ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F)) (hN : N = ⊤) :
    LayerState U p D ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F) N where
  W := originalImageOpen U (inverseImageOpen U D)
  mem := ⟨p, hpD, rfl⟩
  le := source_image_le_domain U D
  T := (localOverTransport (originalSpace n) U (inverseImageOpen U D)).obj
    (F.over (inverseImageOpen U D))
  fp := @local_original_finitePresentation (originalSpace n) U F hF (inverseImageOpen U D)
  η := native_original_stalk_iso (originalSpace n) U (inverseImageOpen U D) F p hpD ≪≫
    submodule_top_iso ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F) N hN

/-- **Downward prime layers (G10.PN.4).**  From ONLY the ordinary original finitely presented
module `F` on `U` and a point `p`: the original stalk prime series `d` and ALL prime targets `B_i`
are selected once, the common domain `D ∋ p` is their intersection with `U`, the top state is the
actual restriction of `F` to `D` (on the literal open `D`), and the complete downward chain of
actual kernel layers (with every `φ_i`, its surjectivity, the literal kernel `T_i`, the original
inclusion squares and both quotient numerator squares, ending in an actual zero object) exists. -/
theorem exists_original_downward_prime_layers
    (n : ℕ) (U : Opens (ComplexModel n)) (F : OriginalModules U)
    [hF : F.IsFinitePresentation] (p : U) :
    ∃ (d : SelectedPrimeSeries (OriginalRingStalk U p)
        ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F))
      (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
        (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
      (D : Opens (ComplexModel n)) (hpD : p.val ∈ D) (_hDU : D ≤ U)
      (hDB : ∀ j : Fin d.s.length, D ≤ (B j).old.U),
      originalImageOpen U (inverseImageOpen U D) = D ∧
      DownChain d B D hDB d.s.length le_rfl
        (topState U p F D hpD (d.s (seriesIndex d d.s.length le_rfl)) d.last) := by
  obtain ⟨d⟩ := selected_original_series n U F p
  have hB (j : Fin d.s.length) : Nonempty (NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1)) := by
    have : (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1).IsPrime :=
      Ideal.comap_isPrime (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1
    exact exists_native_prime_support_with_all_open_cokernels p.val _
  let B := fun j => Classical.choice (hB j)
  let D : Opens (ComplexModel n) := U ⊓ Finset.univ.inf (fun j : Fin d.s.length => (B j).old.U)
  have hpD : p.val ∈ D := ⟨p.property, (mem_finset_open_inf _ _ _).mpr
    (fun j _ => (B j).old.hpU)⟩
  have hDB (j : Fin d.s.length) : D ≤ (B j).old.U :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ j))
  exact ⟨d, B, D, hpD, inf_le_left, hDB, original_image_inverseImage U D inf_le_left,
    downChain_of_state d B D hDB d.s.length le_rfl _⟩

end

end Hironaka.HironakaG10PNDownwardLayers
