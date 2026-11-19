import Hironaka.Resolution.HironakaG10PNLayerIso

/-! The extension induction along the restricted prime chain on one final open (lane G10P,
run 0080; the induction of `G10.PN.9`).  Blueprint: `hironaka-g10-pn-extension-induction.tex`.

Fix an original open `Ω`, a point `x ∈ Ω` and a class `𝒮` of source modules (e.g. the natively
finite-type ones).  A module `T` on `Ω` is *zero-stalk rigid* if every map `g : G ⟶ T` from a source
`G ∈ 𝒮` whose stalk map at `x` vanishes is zero.  If every prime target of the restricted chain is
zero-stalk rigid (this is the per-target continuation input, `G10.PN.7`), then so is the top of the
chain: for `f : G ⟶ G_top` with zero stalk, `f ≫ π` has zero stalk, hence is zero by rigidity of
the target; the kernel universal property factors `f = f' ≫ ι`; the stalk functor preserves finite
limits, so the stalk of `ι` is mono and the stalk of `f'` is zero; induct.  No point evaluation is
used, and every repeated layer is a separate step.  Applied to the literal `F|Ω` of PN.5/PN.8. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaG10PNExtensionInduction

open HironakaChowNativeFreePartContinuation
  HironakaChowNativePrimeSupportContinuation HironakaSingularModuleSheafStalk
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeLocalOverStalkTransport
  HironakaChowNativeLocalOverFiniteDataTransport HironakaNativeCanonicalSupportRestriction
  HironakaNativeCyclicCokernelRestriction HironakaChowNativeModuleStalkExact
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaSingularLocallyFreeStalk HironakaNativeOriginalRestrictionComparison
  HironakaG10PNLayerStep HironakaG10PNDownwardLayers HironakaG10PNRestrictionExact
  HironakaG10PNBottomRestrict HironakaG10PNLayerIso

noncomputable section

variable {n : ℕ}

/-- Zero-stalk rigidity of a native module `T` on `Ω` at `x` for the sources in `𝒮`: every map
from a source in `𝒮` to `T` whose stalk map at `x` vanishes is zero. -/
def ZeroStalkRigid (Ω : Opens (ComplexModel n)) (x : Ω) (𝒮 : OriginalModules Ω → Prop)
    (T : OriginalModules Ω) : Prop :=
  ∀ (G : OriginalModules Ω), 𝒮 G → ∀ g : G ⟶ T,
    (nativeStalkFunctor (originalOpenStructureSheaf Ω) x).map g = 0 → g = 0

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalk functor maps the inclusion of a limiting kernel fork to a monomorphism. -/
theorem stalk_mono_of_isLimit (Ω : Opens (ComplexModel n)) (x : Ω)
    {G' G Q : OriginalModules Ω} (ι : G' ⟶ G) (π : G ⟶ Q) (w : ι ≫ π = 0)
    (hl : IsLimit (KernelFork.ofι ι w)) :
    Mono ((nativeStalkFunctor (originalOpenStructureSheaf Ω) x).map ι) := by
  have : Mono ι := Fork.IsLimit.mono hl
  have : PreservesFiniteLimits (nativeStalkFunctor (originalOpenStructureSheaf Ω) x) :=
    nativeStalkFunctor_preservesFiniteLimits (originalOpenStructureSheaf Ω) x
  have : (nativeStalkFunctor (originalOpenStructureSheaf Ω) x).PreservesMonomorphisms :=
    inferInstance
  exact Functor.map_mono _ ι

/-- ONE level of the extension induction. -/
theorem rigid_of_step (Ω : Opens (ComplexModel n)) (x : Ω) (𝒮 : OriginalModules Ω → Prop)
    {G' G Q : OriginalModules Ω} (ι : G' ⟶ G) (π : G ⟶ Q) (w : ι ≫ π = 0)
    (hl : IsLimit (KernelFork.ofι ι w)) (hQ : ZeroStalkRigid Ω x 𝒮 Q)
    (hG' : ZeroStalkRigid Ω x 𝒮 G') : ZeroStalkRigid Ω x 𝒮 G := by
  intro S hS g hg
  have h1 : g ≫ π = 0 := hQ S hS (g ≫ π) (by rw [Functor.map_comp, hg, zero_comp])
  obtain ⟨g₀, hg₀⟩ := KernelFork.IsLimit.lift' hl g h1
  let g' : S ⟶ G' := g₀
  have hg' : g' ≫ ι = g := hg₀
  have hm := stalk_mono_of_isLimit Ω x ι π w hl
  have h2 : (nativeStalkFunctor (originalOpenStructureSheaf Ω) x).map g' = 0 := by
    rw [← cancel_mono ((nativeStalkFunctor (originalOpenStructureSheaf Ω) x).map ι),
      ← Functor.map_comp, hg', hg, zero_comp]
  have h3 : g' = 0 := hG' S hS g' h2
  rw [← hg', h3, zero_comp]

/-- The extension induction along the restricted chain: if every prime target of the SAME
preselected `B_i` on `Ω` is zero-stalk rigid, then so is the top of the chain. -/
theorem rigid_of_restrictedChainOn {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (Ω : Opens (ComplexModel n)) (hΩB : ∀ j : Fin d.s.length, Ω ≤ (B j).old.U) (x : Ω)
    (𝒮 : OriginalModules Ω → Prop)
    (hT : ∀ j : Fin d.s.length, ZeroStalkRigid Ω x 𝒮 (primeTargetOnDomain (B j) Ω (hΩB j))) :
    ∀ (k : ℕ) (hk : k ≤ d.s.length) (G : OriginalModules Ω),
      RestrictedChainOn d B Ω hΩB k hk G → ZeroStalkRigid Ω x 𝒮 G
  | 0, _, _, h => fun _ _ g _ => h.eq_of_tgt g 0
  | k + 1, hk, _, h => by
    obtain ⟨G', ι, π, w, ⟨hl⟩, _, hn⟩ := h
    exact rigid_of_step Ω x 𝒮 ι π w hl (hT _)
      (rigid_of_restrictedChainOn d B Ω hΩB x 𝒮 hT k (Nat.le_of_succ_le hk) G' hn)

/-- **Extension induction for the literal `F|Ω` (the induction of G10.PN.9).**  From ONLY the
ordinary original finitely presented `F` on `U` and `p`: the series, ALL models `B_i`, the domain `D`
and an open `Ω₀ ∋ p` are chosen BEFORE any source; then on EVERY original open `p ∈ Ω ⊆ Ω₀`, for
ANY class `𝒮` of sources, if the prime target of every `B_i` on `Ω` is zero-stalk rigid at `p`
(the per-target continuation input), then every map from a source in `𝒮` to the literal `F|Ω` with
zero stalk at `p` is zero. -/
theorem exists_original_rigid_of_rigid_targets
    (n : ℕ) (U : Opens (ComplexModel n)) (F : OriginalModules U)
    [hF : F.IsFinitePresentation] (p : U) :
    ∃ (d : SelectedPrimeSeries (OriginalRingStalk U p)
        ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F))
      (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
        (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
      (D : Opens (ComplexModel n)) (_hpD : p.val ∈ D) (hDU : D ≤ U)
      (hDB : ∀ j : Fin d.s.length, D ≤ (B j).old.U)
      (Ω₀ : Opens (ComplexModel n)) (_hpΩ₀ : p.val ∈ Ω₀) (hΩ₀D : Ω₀ ≤ D),
      ∀ (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ Ω₀) (hpΩ : p.val ∈ Ω)
        (𝒮 : OriginalModules Ω → Prop),
        (∀ j : Fin d.s.length, ZeroStalkRigid Ω ⟨p.val, hpΩ⟩ 𝒮
          (primeTargetOnDomain (B j) Ω (hΩ.trans (hΩ₀D.trans (hDB j))))) →
        ZeroStalkRigid Ω ⟨p.val, hpΩ⟩ 𝒮
          ((restrictTo U Ω (hΩ.trans (hΩ₀D.trans hDU))).obj F) := by
  obtain ⟨d, B, D, hpD, hDU, hDB, Ω₀, hpΩ₀, hΩ₀D, hall⟩ :=
    HironakaG10PNLayerIso.exists_original_restricted_chain_on n U F p
  exact ⟨d, B, D, hpD, hDU, hDB, Ω₀, hpΩ₀, hΩ₀D, fun Ω hΩ hpΩ 𝒮 hT =>
    rigid_of_restrictedChainOn d B Ω (fun j => hΩ.trans (hΩ₀D.trans (hDB j))) ⟨p.val, hpΩ⟩ 𝒮 hT
      d.s.length le_rfl _ (hall Ω hΩ)⟩

end

end Hironaka.HironakaG10PNExtensionInduction
