inductive InX1 {X Y : Type u} (right : X → Y) (left : Y → X) : X → Prop
    | base : ∀ x : X, (∀ y : Y, x ≠ left y) → InX1 right left x
    | step : ∀ x : X, InX1 right left x → InX1 right left (left (right x))

theorem CSB {A B : Type u} (f : A → B) (g : B → A) (hf : f.Injective) (hg : g.Injective) :
    ∃ φ : A → B, φ.Injective ∧ φ.Surjective := by
/-
    A1 is everything in A that stops in A when you pull back
    same for B1 and B
-/
    let InA1 : A → Prop := InX1 f g
    let InB1 : B → Prop := InX1 g f
/-
    A2 is everything in A that stops in B
    B2 is everything in B that stops in A
    A2 = g (B1) and B2 = f (A1)
-/
    let InA2 : A → Prop := fun a ↦ ∃ b : B, InB1 b ∧ a = g b
    let InB2 : B → Prop := fun b ↦ ∃ a : A, InA1 a ∧ b = f a

/-
    A3 and B3 are everything else : infinite ascent
-/

    let InA3 : A → Prop := fun a ↦ ¬ InA1 a ∧  ¬ InA2 a
    let InB3 : B → Prop := fun b ↦ ¬ InB1 b ∧  ¬ InB2 b

/-
I need to show that each a : A lies in exactly one of A1, A2, A3. lying in A3
by definition means not being in A1 or A2; so I need to show that A1 and A2
are mutually exclusive as well (Same for B but I never use that fact)
-/

    have not_A2_of_A1 : ∀ a : A, ¬ InA1 a ∨ ¬ InA2 a := by
        simp only [Classical.or_iff_not_imp_left, Classical.not_not]
        intro z hz; induction hz with
        | base a ha =>
            unfold InA2; simp only [not_exists, not_and]
            intro b hb; exact ha b
        | step a' ha'1 ha'2 =>
            unfold InA2 at ha'2 ⊢
            simp only [not_exists, not_and] at ha'2 ⊢
            simp [Function.Injective.ne_iff hg]
            intro y hy; induction hy with
            |   base b hb =>
                apply Ne.symm; exact hb a'
            |   step b' hb'1 hb'2 =>
                simp [Function.Injective.ne_iff hf]
                exact ha'2 b' hb'1

/-
    The basic trick now is that f is a bijection from A1 to B2, and from A3 to B3,
    and g is a bijection from B1 to A2, so g⁻¹ is a bijection from A2 to B1.

    we'll define φ : A → B that equals g⁻¹ on A2 and equals f everywhere else

    just need to show each of the pieces is surjective and that each of their ranges
    are what they should be

    we have g : B1 → A2 is surjective by the definition of A2
    f : A1 → B2 is surjective as well but again we don't need it
-/

    have hg_B1_A2_surj : ∀ a : A, InA2 a → ∃ b : B, InB1 b ∧ a = g b := by
        unfold InA2; exact fun _ h ↦ h

    have hpartA : ∀ a : A, ¬ InA1 a → ¬ InA2 a → InA3 a :=
        fun _ ha1 ha2 ↦ ⟨ha1, ha2⟩

    have hpartB : ∀ b : B, ¬ InB1 b → ¬ InB2 b → InB3 b :=
        fun _ hb1 hb2 ↦ ⟨hb1, hb2⟩

/-
    f maps A2 onto B1 and A1 onto B2 (similar for g)
-/
    have hf_B1_of_A2 : ∀ a : A, InA2 a →  InB1 (f a) := by
        intro a ha; unfold InA2 at ha
        have ⟨b, hb, hb'⟩ := ha
        have h := InX1.step (right := g) (left := f) b hb
        rw [←hb'] at h; exact h

    have hg_A1_of_B2 : ∀ b : B, InB2 b → InA1 (g b) := by
        intro b hb; unfold InB2 at hb
        have ⟨a, ha, ha'⟩ := hb
        have h := InX1.step (right := f) (left := g) a ha
        rw [←ha'] at h; exact h

    have hg_A2_of_B1 : ∀ b : B, InB1 b → InA2 (g b) := fun b hb ↦ ⟨b, hb, rfl⟩
    have hf_B2_of_A1 : ∀ a : A, InA1 a → InB2 (f a) := fun a ha ↦ ⟨a, ha, rfl⟩

/-
    Anything NOT in B1 is in the range of f
-/
    have hB1_cp : ∀ b : B, ¬ InB1 b → ∃ a : A, b = f a := by
        intro b hb; apply Classical.byContradiction; intro h
        simp at h; have h' := InX1.base (right := g) (left := f) b h
        exact hb h'

    have hA1_cp : ∀ a : A, ¬ InA1 a → ∃ b : B, a = g b := by
        intro a ha; apply Classical.byContradiction; intro h
        simp at h; have h' := InX1.base (right := f) (left := g) a h
        exact ha h'

/-
    This shows that f is a bijection between A3 and B3, and similarly
    g is a bijection between B3 and A3
-/

    have hf_A3_B3_surj : ∀ b : B, InB3 b → ∃ a : A, InA3 a ∧ b = f a := by
        intro b hb; unfold InB3 at hb; obtain ⟨hb1, hb2⟩ := hb
        unfold InB2 at hb2; simp only [not_exists, not_and] at hb2
        have ⟨a, ha⟩  := hB1_cp b hb1; refine ⟨a, ?_, ha⟩
        apply hpartA a
        ·   intro ha1; exact hb2 a ha1 ha
        ·   intro ha2; rw [ha] at hb1; exact hb1 (hf_B1_of_A2 a ha2)

    have hg_B3_A3_surj : ∀ a : A, InA3 a → ∃ b : B, InB3 b ∧ a = g b := by
        intro a ha; unfold InA3 at ha; obtain ⟨ha1, ha2⟩ := ha
        unfold InA2 at ha2; simp only [not_exists, not_and] at ha2
        have ⟨b, hb⟩  := hA1_cp a ha1; refine ⟨b, ?_, hb⟩
        apply hpartB b
        ·   intro hb1; exact ha2 b hb1 hb
        ·   intro hb2; rw [hb] at ha1; exact ha1 (hg_A1_of_B2 b hb2)

    have hf_B3_of_A3 : ∀ a : A, InA3 a → InB3 (f a) := by
        intro a ha; have ⟨b, hb1, hb2⟩ := (hg_B3_A3_surj a ha)
        rw [hb2]; apply hpartB
        ·   generalize heq : f (g b) = y
            intro hb'2; cases hb'2 with
            | base z hz =>
                exact (hz (g b)) heq.symm
            | step z' hz' =>
                rw [Function.Injective.eq_iff hf, Function.Injective.eq_iff hg] at heq
                subst heq; unfold InB3 at hb1; exact hb1.1 hz'
        ·   unfold InB2; simp only [not_exists, not_and]; intro x hx
            simp only [Function.Injective.ne_iff hf]; intro hx'; subst hx'; rw [← hb2] at hx
            unfold InA3 at ha; exact ha.1 hx

    have hg_A3_of_B3 : ∀ b : B, InB3 b → InA3 (g b) := by
        intro b hb; have ⟨a, ha1, ha2⟩ := (hf_A3_B3_surj b hb)
        rw [ha2]; apply hpartA
        ·   generalize heq : g (f a) = y
            intro ha'2; cases ha'2 with
            | base z hz =>
                exact (hz (f a)) heq.symm
            | step z' hz' =>
                rw [Function.Injective.eq_iff hg, Function.Injective.eq_iff hf] at heq
                subst heq; unfold InA3 at ha1; exact ha1.1 hz'
        ·   unfold InA2; simp only [not_exists, not_and]; intro x hx
            simp only [Function.Injective.ne_iff hg]; intro hx'; subst hx'; rw [← ha2] at hx
            unfold InB3 at hb; exact hb.1 hx

/-
    f is NOT surjective from A2 onto B1; but g is bijective from B1 to A2, so I need to
    invert it; this uses the axiom of choice to construct A function that goes backwards
    then I show it's bijective by showing its composition with g gives the identity
-/


    let g_inv (a : A) (ha : InA2 a) : B := Exists.choose (hg_B1_A2_surj a ha)

    have hg_g_inv : ∀ a : A, (ha : InA2 a) → g (g_inv a ha) = a := by
        intro a ha; have ⟨_, h'⟩ := Exists.choose_spec (hg_B1_A2_surj a ha)
        unfold g_inv; symm; exact h'

/-
    this actually shows g_inv is injective
-/
    have hg_inv_g : ∀ b : B, (hb : InB1 b) → (g_inv (g b) (hg_A2_of_B1 b hb) = b) := by
        intro b hb; have ha : InA2 (g b) := hg_A2_of_B1 b hb
        have h := hg_g_inv (g b) (ha)
        rwa [Function.Injective.eq_iff hg] at h

/-
    this actually shows that g_inv is surjective
-/

    let φ : A → B := fun a ↦ by
        by_cases h : InA2 a
        ·   exact g_inv a h
        exact f a

/-
    Putting it all together
-/
    refine ⟨φ, ?injective, ?surjective⟩
    ·   intro x y hxy
        unfold φ at hxy; split at hxy <;> split at hxy
        ·   expose_names; rw [← hg_g_inv x h, ← hg_g_inv y h_1]
            rwa [Function.Injective.eq_iff hg]
        ·   expose_names; exfalso; have h' : InA1 y ∨ InA3 y := by
                rw [Classical.or_iff_not_imp_left]
                exact fun x ↦ hpartA y x h_1
            have hxy' := congrArg g hxy; rw [hg_g_inv x h] at hxy'
            subst hxy'; rcases h' with ha | ha
            ·   have hy' := hf_B2_of_A1 y ha;  have hy'' := hg_A1_of_B2 (f y) hy'
                exact (Or.neg_resolve_left (not_A2_of_A1 (g (f y))) hy'') h
            ·   have hy' := hf_B3_of_A3 y ha; have hy'' := hg_A3_of_B3 (f y) hy'
                exact hy''.2 h
        ·   expose_names; exfalso; have h' : InA1 x ∨ InA3 x := by
                rw [Classical.or_iff_not_imp_left]
                exact fun y ↦ hpartA x y h
            have hxy' := congrArg g hxy; rw [hg_g_inv y h_1] at hxy'
            subst hxy'; rcases h' with ha | ha
            ·   have hx' := hf_B2_of_A1 x ha; have hx'' := hg_A1_of_B2 (f x) hx'
                exact (Or.neg_resolve_left (not_A2_of_A1 (g (f x))) hx'') h_1
            ·   have hx' := hf_B3_of_A3 x ha; have hx'' := hg_A3_of_B3 (f x) hx'
                exact hx''.2 h_1
        ·   rwa [Function.Injective.eq_iff hf] at hxy
    ·   intro b; have hcases := hpartB b; simp [← Classical.or_iff_not_imp_left] at hcases
        rcases hcases with h | h | h
        ·   refine ⟨g b, ?_⟩
            unfold φ; split
            ·   expose_names; exact hg_inv_g b h
            ·   expose_names; exact absurd ⟨b, h, rfl⟩ h_1
        ·   obtain ⟨a, ha, ha'⟩ := h; refine ⟨a, ?_⟩
            unfold φ; split
            ·   expose_names; exact absurd h (Or.neg_resolve_left (not_A2_of_A1 a) ha)
            ·   exact ha'.symm
        ·   obtain ⟨a, ha, ha'⟩ := hf_A3_B3_surj b h; refine ⟨a, ?_⟩
            unfold φ; split
            ·   expose_names; unfold InA3 at ha; exact absurd h_1 ha.2
            ·   exact ha'.symm
