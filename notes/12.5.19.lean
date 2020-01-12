axiom person : Type
axiom Likes : person → person → Prop
-- If there is a person everyone likes, then everyone likes someone
example: 
    (∃ (p : person), ∀(q : person), Likes q p)
    → (∀(p : person), ∃(q : person), Likes p q) 
    := 
    
    λ h,
        λ p,
            match h with
            | (exists.intro w pf) := exists.intro w (pf p)
            end

-- The proof of a existentially qualified proposition is a pair

example : 
    (∃ (p : person), ∀(q : person), Likes q p)
    → (∀(p : person), ∃(q : person), Likes p q) 
    := 
    begin
        intros,
        cases a with w pf,
        exact exists.intro w (pf p),
    end


def even : nat → Prop 
| n := n % 2 = 0
 
example : exists (n : nat), even n :=
    begin 
        apply exists.intro 2 _,
        unfold even,
        exact eq.refl 0,
    end


example : ∀ (n : ℕ), (n = 0) ∨ (n ≠ 0) :=

λ n,
    match n with
    | nat.zero := or.inl (eq.refl 0) 
    | (nat.succ n') := or.inr 
        (λ h, 
            match h with
            end) 
    end
