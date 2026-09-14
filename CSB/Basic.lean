/-
    There are several constructions/proofs I do twice, but with A/f and B/g swapped
    so I do them once here
-/

inductive InX1 {X Y : Type u} (right : X → Y) (left : Y → X) : X → Prop
    | base : ∀ x : X, (∀ y : Y, x ≠ left y) → InX1 right left x
    | step : ∀ x : X, InX1 right left x → InX1 right left (left (right x))

def InX2 {X Y : Type u} (right : X → Y) (left : Y → X) : X → Prop :=
    fun x ↦ ∃ y : Y, InX1 left right y ∧ x = left y

def InX3 {X Y : Type u} (right : X → Y) (left : Y → X) : X → Prop :=
    fun x ↦ ¬ InX1 right left x ∧ ¬ InX2 right left x

theorem Y1_of_X2 {X Y : Type u} (right : X → Y) (left : Y → X) :
 ∀ x : X, InX2 right left x → InX1 left right (right x) := by
        intro a ha; unfold InX2 at ha
        have ⟨b, hb, hb'⟩ := ha
        have h := InX1.step (right := left) (left := right) b hb
        rw [←hb'] at h; exact h

theorem hX1_cp {X Y : Type u} (right : X → Y) (left : Y → X)  :
    ∀ x : X, ¬ InX1 right left x → ∃ y : Y, x = left y := by
        intro b hb; apply Classical.byContradiction; intro h
        simp at h; have h' := InX1.base (right := right) (left := left) b h
        exact hb h'

theorem partX {X Y : Type u} (right : X → Y) (left : Y → X) :
    ∀ x : X, ¬ InX1 right left x → ¬ InX2 right left x → InX3 right left x :=
        fun _ ha1 ha2 ↦ ⟨ha1, ha2⟩

theorem X3_Y3_surj {X Y : Type u} (right : X → Y) (left : Y → X) :
 ∀ y : Y, InX3 left right y → ∃ x : X, InX3 right left x ∧ y = right x := by
        intro b hb; unfold InX3 at hb; obtain ⟨hb1, hb2⟩ := hb
        unfold InX2 at hb2; simp only [not_exists, not_and] at hb2
        have ⟨a, ha⟩  := hX1_cp left right b hb1; refine ⟨a, ?_, ha⟩
        apply partX right left a
        ·   intro ha1; exact hb2 a ha1 ha
        ·   intro ha2; rw [ha] at hb1; exact hb1 (Y1_of_X2 right left a ha2)

theorem Y3_of_X3 {X Y : Type u} {right : X → Y} {left : Y → X}
(hr_inj : right.Injective) (hl_inj : left.Injective) :
 ∀ x : X, InX3 right left x → InX3 left right (right x) := by
        intro a ha; have ⟨b, hb1, hb2⟩ := (X3_Y3_surj left right a ha)
        rw [hb2]; apply partX left right
        ·   generalize heq : right (left b) = y
            intro hb'2; cases hb'2 with
            | base z hz =>
                exact (hz (left b)) heq.symm
            | step z' hz' =>
                rw [Function.Injective.eq_iff hr_inj, Function.Injective.eq_iff hl_inj] at heq
                subst heq; unfold InX3 at hb1; exact hb1.1 hz'
        ·   unfold InX2; simp only [not_exists, not_and]; intro x hx
            simp only [Function.Injective.ne_iff hr_inj]; intro hx'; subst hx'; rw [← hb2] at hx
            unfold InX3 at ha; exact ha.1 hx

/- Suppose that A and B are types so that there is an injective function from A to B
and an injective function from B to A. Then there is a bijective function φ from A to B -/

theorem CSB {A B : Type u} (f : A → B) (g : B → A) (hf : f.Injective) (hg : g.Injective) :
    ∃ φ : A → B, φ.Injective ∧ φ.Surjective := by

--- A1 is everything in A that stops in A when you pull back; same for B1 and B

    let InA1 : A → Prop := InX1 f g; let InB1 : B → Prop := InX1 g f
/-
    A2 is everything in A that stops in B
    B2 is everything in B that stops in A
    A2 = g (B1) and B2 = f (A1)
-/
    let InA2 : A → Prop := InX2 f g; let InB2 : B → Prop := InX2 g f

--- A3 and B3 are everything else : infinite ascent

    let InA3 : A → Prop := InX3 f g; let InB3 : B → Prop := InX3 g f

/-  I need to show that each a : A lies in exactly one of A1, A2, A3. lying in A3
    by definition means not being in A1 or A2; so I need to show that A1 and A2
    are mutually exclusive as well (Same for B but I never use that fact) -/

    have not_A2_of_A1 : ∀ a : A, ¬ InA1 a ∨ ¬ InA2 a := by
        simp only [Classical.or_iff_not_imp_left, Classical.not_not]
        intro z hz; induction hz with
        | base a ha =>
            unfold InA2 InX2; simp only [not_exists, not_and]
            intro b hb; exact ha b
        | step a' ha'1 ha'2 =>
            unfold InA2 InX2 at ha'2 ⊢
            simp only [not_exists, not_and] at ha'2 ⊢
            simp [Function.Injective.ne_iff hg]
            intro y hy; induction hy with
            |   base b hb =>
                apply Ne.symm; exact hb a'
            |   step b' hb'1 hb'2 =>
                simp [Function.Injective.ne_iff hf]
                exact ha'2 b' hb'1

/-  The basic trick now is that f is a bijection from A1 to B2, and from A3 to B3,
    and g is a bijection from B1 to A2, so g⁻¹ is a bijection from A2 to B1.

    we'll define φ : A → B that equals g⁻¹ on A2 and equals f everywhere else

    just need to show each of the pieces is surjective and that each of their ranges
    are what they should be

    we have g : B1 → A2 is surjective by the definition of A2
    f : A1 → B2 is surjective as well but again we don't need it -/

    have hg_B1_A2_surj : ∀ a : A, InA2 a → ∃ b : B, InB1 b ∧ a = g b := by
        unfold InA2; exact fun _ h ↦ h

    have hpartA := partX f g; have hpartB := partX g f

--- f maps A2 onto B1 and A1 onto B2 (similar for g)

    have hf_B1_of_A2 := Y1_of_X2 f g; have hg_A1_of_B2 := Y1_of_X2 g f

    have hg_A2_of_B1 : ∀ b : B, InB1 b → InA2 (g b) := fun b hb ↦ ⟨b, hb, rfl⟩
    have hf_B2_of_A1 : ∀ a : A, InA1 a → InB2 (f a) := fun a ha ↦ ⟨a, ha, rfl⟩

--- Anything NOT in B1 is in the range of f and similarly for A1 and g

    have hB1_cp := hX1_cp g f; have hA1_cp := hX1_cp f g

/-  This shows that f is a bijection between A3 and B3, and similarly
    g is a bijection between B3 and A3 -/

    have hf_A3_B3_surj := X3_Y3_surj f g; have hg_B3_A3_surj := X3_Y3_surj g f
    have hf_B3_of_A3 := Y3_of_X3 hf hg; have hg_A3_of_B3 := Y3_of_X3 hg hf

/-  f is NOT surjective from A2 onto B1; but g is bijective from B1 to A2, so I need to
    invert it; this uses the axiom of choice to construct A function that goes backwards
    then I show it's bijective by showing its composition with g gives the identity -/

    let g_inv (a : A) (ha : InA2 a) : B := Exists.choose (hg_B1_A2_surj a ha)

    have hg_g_inv : ∀ a : A, (ha : InA2 a) → g (g_inv a ha) = a := by
        intro a ha; have ⟨_, h'⟩ := Exists.choose_spec (hg_B1_A2_surj a ha)
        unfold g_inv; symm; exact h'

--- this actually shows g_inv is injective

    have hg_inv_g : ∀ b : B, (hb : InB1 b) → (g_inv (g b) (hg_A2_of_B1 b hb) = b) := by
        intro b hb; have ha : InA2 (g b) := hg_A2_of_B1 b hb
        have h := hg_g_inv (g b) (ha)
        rwa [Function.Injective.eq_iff hg] at h

--- this actually shows that g_inv is surjective

    let φ : A → B := fun a ↦ by
        by_cases h : InA2 a
        ·   exact g_inv a h
        exact f a

--- Putting it all together

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
            ·   expose_names; unfold InX3 at ha; exact absurd h_1 ha.2
            ·   exact ha'.symm
