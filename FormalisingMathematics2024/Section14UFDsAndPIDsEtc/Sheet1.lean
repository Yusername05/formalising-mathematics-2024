/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.PrincipalIdealDomain
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/
variable (R : Type) [CommRing R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain.
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":
variable [IsPrincipalIdealRing R] [IsDomain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.
example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b
  apply eq_zero_or_eq_zero_of_mul_eq_zero

-- typeclass inference
-- magically extracts the assumption from `IsDomain`
example : (0 : R) ≠ 1 := zero_ne_one

example (I : Ideal R) : I.IsPrincipal := IsPrincipalIdealRing.principal I

example (I : Ideal R) : ∃ j, I = Ideal.span {j} := Submodule.IsPrincipal.principal I

-- product of two PIDs isn't a PID, but only becuase it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := by
    -- if I is an ideal in (A × B), we can use the two projection homomorphisms to get the respective ideals in A and B and find the element that generates each ideal as they are both principal
    obtain ⟨a, hA : _ = Ideal.span _⟩ :=
      IsPrincipalIdealRing.principal (I.map (RingHom.fst A B)) -- a generates the ideal in A that comes from the first projection homomorphism applied to I
    obtain ⟨b, hB : _ = Ideal.span _⟩ :=
      IsPrincipalIdealRing.principal (I.map (RingHom.snd A B)) -- similarly for b in B
    use (a,b) -- we claim this pair must generate the whole ideal.
    ext x
    simp only [Ideal.submodule_span_eq] -- more convenient naming
    rw [Ideal.mem_span_singleton] -- it should be clear from the definition of a principal ideal that every element must be divisible by the generating object and vice versa
    fconstructor -- an alternate version of constructor as it doesnt rearrange goals
    · intro h
      have h1 : RingHom.fst A B x ∈ I.map (RingHom.fst A B)
      · apply Ideal.mem_map_of_mem _ h -- the first projection homomorphism at an element of I must be an element of projection applied to I
      rw [hA, Ideal.mem_span_singleton] at h1 -- this is the same rewrite as earlier which goes from being an element of a principal ideal to being divisible by the generating element
      rcases h1 with ⟨r, hr⟩ -- (a,b)|x iff x = a × r for some r ∈ A
      have h2 : RingHom.snd A B x ∈ I.map (RingHom.snd A B)
      · apply Ideal.mem_map_of_mem _ h
      rw [hB, Ideal.mem_span_singleton] at h2
      rcases h2 with ⟨s, hs⟩ -- the same operation but for B instead of A giving us x = b × s for some s ∈ R
      use(r, s) -- we claim that (r,s) is the element needed for (a,b)|x
      change x = (a * r, b * s) -- basic arithmetic in the product ring
      rw [← hr, ← hs] -- hr, hs tell us that a × r is the image of x under the projection map, so we will make this substitution and do similar for b × s
      simp only [RingHom.coe_fst, RingHom.coe_snd, Prod.mk.eta] -- if the first and second element of a product are the first and second projections at x, this element is x
    · rintro ⟨⟨r, s⟩, rfl⟩
      -- an interesting trick in lean 4, this line is the same as excecutre rintro ⟨⟨r,s⟩, h⟩; rw[h], the actual effect of this line is rewriting the divisibility as the existence of appropriate elements
      have ha : a ∈ I.map (RingHom.fst A B) := by rw [hA, Ideal.mem_span_singleton]
      have hb : b ∈ I.map (RingHom.snd A B) := by rw [hB, Ideal.mem_span_singleton] -- saying that a and b are in their respective spans, after applying the respective projections
      rw [Ideal.mem_map_iff_of_surjective] at ha hb -- if we have that elements are result of the projection map, then they must be present as their respective terms within the product
      · rcases ha with ⟨⟨a, b'⟩, haI, rfl⟩ -- essentially writing a as the projection of (a,b') for some b' and proving this works
        rcases hb with ⟨⟨a', b⟩, hbI, rfl⟩ -- same for (a',b)
        suffices (a, b) ∈ I by exact Ideal.mul_mem_right _ _ this -- we now only need to show (a,b) ∈ I as we know (a',b') ∈ I and their various additions and multiplications by assumption
        convert I.add_mem (I.mul_mem_left (1, 0) haI) (I.mul_mem_left (0, 1) hbI) <;> simp -- we state (a,b) = (1,0)×(a,b') + (0,1)×(a',b) and simp gives us that this is in the ideal
      · intro b; use (0, b); rfl -- showing the projection maps are surjective is necessary for there to exist and element in I mapping to a and b resp.
      · intro a; use (a, 0); rfl
