
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

theorem eq1 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  by
    apply Iff.intro
    · intro h1 x px
      apply h1
      exact ⟨ x , px ⟩
    · intro forallNotPx existsPx
      obtain ⟨ x, px ⟩ := existsPx
      have notPx := forallNotPx x
      contradiction
      -- ali apply notPx, potem exact px


theorem eq2 : (r → ∀ x, p x) ↔ (∀ x, r → p x) :=
  by
    apply Iff.intro
    · intro h1 x r
      have px := (h1 r) x
      exact px
    · intro h2 r x
      have px := (h2 x) r
      exact px

theorem eq3 : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) :=
  by
    apply Iff.intro
    · intro h1
      apply Exists.intro
      apply And.intro
      · intro r





theorem eq4 : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  sorry

-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical
#check Classical.byContradiction
#check Classical.em

theorem eq5 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  by
    apply Iff.intro
    · intro notForallPx

      apply Classical.byContradiction
      intro notExistsNotPx

      apply notForallPx
      intro x

      apply Classical.byContradiction
      intro notPx

      apply notExistsNotPx
      exact ⟨ x, notPx ⟩

    · intro h1 h2 --h2 je zaradi negacije h2 -> False
      obtain ⟨ x, notPx ⟩ := h1
      have h3 := h2 x
      contradiction

theorem eq6 : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  by
    apply Iff.intro
    · intro h1 x
      cases h1 with sorry
    · intro h1
      have h2 := Classical.em r
      cases h2 with
      | inl r1 => sorry
      | sorry
