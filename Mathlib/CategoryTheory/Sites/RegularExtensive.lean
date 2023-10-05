/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Sites.Coherent
/-!

# The Regular and Extensive Coverages

This file defines two coverages on a category `C`.

The first one is called the *regular* coverage and for that to exist, the category `C` must satisfy
a condition called `Preregular C`. This means that effective epimorphisms can be "pulled back". The
covering sieves of this coverage are generated by presieves consisting of a single effective
epimorphism.

The second one is called the *extensive* coverage and for that to exist, the category `C` must
satisfy a condition called `Extensive C`. This means `C` has finite coproducts and that those
are preserved by pullbacks. The covering sieves of this coverage are generated by presieves
consisting finitely many arrows that together induce an isomorphism from the coproduct to the
target.

In `extensive_union_regular_generates_coherent`, we prove that the union of these two coverages
generates the coherent topology on `C` if `C` is precoherent, extensive and regular.

TODO: figure out under what conditions `Preregular` and `Extensive` are implied by `Precoherent` and
vice versa.

-/

universe v u w

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

/--
The condition `Preregular C` is property that effective epis can be "pulled back" along any
morphism. This is satisfied e.g. by categories that have pullbacks that preserve effective
epimorphisms (like `Profinite` and `CompHaus`), and categories where every object is projective
(like  `Stonean`).
-/
class Preregular : Prop where
  /--
  For `X`, `Y`, `Z`, `f`, `g` like in the diagram, where `g` is an effective epi, there exists
  an object `W`, an effective epi `h : W ⟶ X` and a morphism `i : W ⟶ Z` making the diagram
  commute.
  ```
  W --i-→ Z
  |       |
  h       g
  ↓       ↓
  X --f-→ Y
  ```
  -/
  exists_fac : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [EffectiveEpi g],
    (∃ (W : C) (h : W ⟶ X) (_ : EffectiveEpi h) (i : W ⟶ Z), i ≫ g = h ≫ f)

/--
Describes the property of having pullbacks of morphsims into a finite coproduct, where one
of the morphisms is an inclusion map into the coproduct (up to isomorphism).
-/
class HasPullbacksOfInclusions : Prop where
    /-- For any morphism `f : X ⟶ Z`, where `Z` is the coproduct of `i : (a : α) → Y a ⟶ Z` with
    `α` finite, the pullback of `f` and `i a` exists for every `a : α`. -/
    has_pullback : ∀ {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbacksOfInclusions C] {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :
    HasPullback f (i a) := HasPullbacksOfInclusions.has_pullback f i a

/--
If `C` has pullbacks then it has the pullbacks relevant to `HasPullbacksOfInclusions`.
-/
instance (priority := 10) [HasPullbacks C] :
  HasPullbacksOfInclusions C := ⟨fun _ _ _ => inferInstance⟩

/--
A category is *extensive* if it has all finite coproducts and those coproducts are preserved
by pullbacks (we only require the relevant pullbacks to exist, via `HasPullbacksOfInclusions`).

TODO: relate this to the class `FinitaryExtensive`
-/
class Extensive extends HasFiniteCoproducts C, HasPullbacksOfInclusions C : Prop where
  /-- Pulling back an isomorphism from a coproduct yields an isomorphism. -/
  sigma_desc_iso : ∀ {α : Type} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
    {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

/--
The regular coverage on a regular category `C`.
-/
def regularCoverage [Preregular C] : Coverage C where
  covering B := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f }
  pullback := by
    intro X Y f S ⟨Z, π, hπ, h_epi⟩
    have := Preregular.exists_fac f π
    obtain ⟨W, h, _, i, this⟩ := this
    refine ⟨Presieve.singleton h, ⟨?_, ?_⟩⟩
    · exact ⟨W, h, by {rw [Presieve.ofArrows_pUnit h]}, inferInstance⟩
    · intro W g hg
      cases hg
      refine ⟨Z, i, π, ⟨?_, this⟩⟩
      cases hπ
      rw [Presieve.ofArrows_pUnit]
      exact Presieve.singleton.mk

/--
The extensive coverage on an extensive category `C`
-/
def extensiveCoverage [Extensive C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only, Extensive.sigma_desc_iso (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      refine Presieve.ofArrows.mk a


/-- The union of the extensive and regular coverages generates the coherent topology on `C`. -/
lemma extensive_regular_generate_coherent [Preregular C] [Extensive C] [Precoherent C] :
    ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck =
    (coherentTopology C) := by
  ext B S
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · induction h with
    | of Y T hT =>
      apply Coverage.saturate.of
      simp only [Coverage.sup_covering, Set.mem_union] at hT
      exact Or.elim hT
        (fun ⟨α, x, X, π, ⟨h, _⟩⟩ ↦ ⟨α, x, X, π, ⟨h, inferInstance⟩⟩)
        (fun ⟨Z, f, ⟨h, _⟩⟩ ↦ ⟨Unit, inferInstance, fun _ ↦ Z, fun _ ↦ f, ⟨h, inferInstance⟩⟩)
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]
  · induction h with
    | of Y T hT =>
      obtain ⟨I, hI, X, f, ⟨h, hT⟩⟩ := hT
      let φ := fun (i : I) ↦ Sigma.ι X i
      let F := Sigma.desc f
      let Z := Sieve.generate T
      let Xs := (∐ fun (i : I) => X i)
      let Zf := Sieve.generate (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F))
      apply Coverage.saturate.transitive Y Zf
      · apply Coverage.saturate.of
        simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
          Set.mem_setOf_eq]
        exact Or.inr ⟨Xs, F, ⟨rfl, inferInstance⟩⟩
      · intro R g hZfg
        dsimp at hZfg
        rw [Presieve.ofArrows_pUnit] at hZfg
        obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg
        induction hW
        rw [← hW']; rw [Sieve.pullback_comp Z]
        suffices Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
          ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck R by assumption
        apply GrothendieckTopology.pullback_stable'
        suffices Coverage.saturate ((extensiveCoverage C) ⊔ (regularCoverage C)) Xs
          (Z.pullback F) by assumption
        suffices : Sieve.generate (Presieve.ofArrows X φ) ≤ Z.pullback F
        · apply Coverage.saturate_of_superset _ this
          apply Coverage.saturate.of
          simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
            Set.mem_setOf_eq]
          refine Or.inl ⟨I, hI, X, φ, ⟨rfl, ?_⟩⟩
          suffices Sigma.desc φ = 𝟙 _ by rw [this]; infer_instance
          ext
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
        intro Q q hq
        simp only [Sieve.pullback_apply, Sieve.generate_apply]
        simp only [Sieve.generate_apply] at hq
        obtain ⟨E, e, r, hq⟩ := hq
        refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩
        · rw [h]
          induction hq.1
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
          exact Presieve.ofArrows.mk _
        · rw [← hq.2]
          simp only [Category.assoc]
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]

end CategoryTheory
