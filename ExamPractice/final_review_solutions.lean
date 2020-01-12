/- QUICK NOTE: -/
/-
This was made by Charlie and Ben with no
consultation with Professor Sullivan.

This is just some review that we thought you should have
while Professor Sullivan is finishing HW9.

While most of these proofs were not written to be difficult,
some turned out to be particularly challenging (which I've marked below).

This is not necessarily representative of what you will see on your
exam, unlike homework 9.

As always -- if we've made any mistakes or you have any questions
please post on Piazza. :)
-/

-- For all proofs, please use provablesystems.com
-- for a reference guide on how to start these proofs

-- Also, you may see the same proofs written two different ways:
example {P : Prop} : P → P :=
begin
    assume p,
    exact p,
end

-- Prof. Sullivan likes forall more 
-- so almost all proofs onward will appear with a forall
-- like this:
example : ∀ P : Prop, P → P :=
begin
    assume P,
    assume p,
    exact p,
end

/- START OF REVIEW -/

/- IMPLICATION -/
example : ∀ P, P → P :=
begin
    assume P,
    assume p,
    exact p,
end
example : ∀ P Q, P → Q → P := 
begin
    assume P Q,
    assume p q,
    exact p,
end
example : (0 = 1) → (0 = 1) :=
begin
    assume pf,
    exact pf,
end

-- You will use implication extensively throughout
-- the remainder of this review


/- TRUE -/
-- intro
example : true :=
begin
    exact true.intro,
end
example : ∀ P Q R : Prop, true :=
begin
    assume P Q R,
    exact true.intro,
end
example : (0 = 1) → true :=
begin
    assume pf,
    exact true.intro,
end


/- FALSE -/
example : false → (0 = 1) :=
begin
    assume f,
    exact false.elim f,
end
example : ∀ P : Prop, false → P :=
begin
    assume P,
    assume f,
    exact false.elim f,
end 
example : ∀ P Q, P → Q → false → (P ∧ Q) :=
begin
    assume P Q,
    assume p q f,
    exact false.elim f,
end


/- EQUALITY -/
example : 3 = 3 :=
begin
    exact eq.refl 3,
end
example : ∀ n : nat, n = n :=
begin
    assume n,
    exact eq.refl n,
end


/- AND -/
-- intro (and.intro _ _)
example : ∀ P Q : Prop, P → Q → (P ∧ Q) :=
begin
    assume P Q,
    assume p q,
    exact and.intro p q,
end
example {P Q : Prop} : P → Q → (Q ∧ P) :=
begin
    assume p q,
    exact and.intro q p,
end
example : (0 = 0) ∧ (1 = 1) :=
begin
    apply and.intro,
    exact eq.refl 0,
    exact rfl, -- shortcut
end

-- elim (and.elim_left _ and and.right _ )
example : ∀ P Q : Prop, P ∧ Q → P :=
begin
    intros, -- shortcut for all assumptions (except negation assumptions)
    exact and.elim_left a,
end
example : ∀ P Q : Prop, P ∧ Q → Q :=
begin
    intros,
    exact and.elim_right a,
end
example : ∀ P Q R : Prop, P ∧ Q ∧ R → Q :=
begin
    intros,
    apply and.elim_left (and.elim_right a),
end

-- both
example : ∀ P Q R : Prop, P ∧ Q ∧ R → (P ∧ R) :=
begin
    intros,
    apply and.intro,
    exact and.elim_left a,
    exact and.elim_right (and.elim_right a),
end
example : ∀ P Q R : Prop, Q ∧ R ∧ P → (R ∧ P ∧ Q) :=
begin
    assume P Q R,
    assume qrp,
    apply and.intro,
    exact qrp.2.1, -- shortcut for and.elim_left (and.elim_right qrp)
    apply and.intro,
    exact qrp.2.2,
    exact qrp.1,
end


/- OR -/
-- intro (or.intro_left _ _, shortcut: or.inl _ and the associated right-side variant)
example : ∀ P Q, P → (P ∨ Q) :=
begin
    assume P Q,
    assume p,
    exact or.intro_left Q p,
end
example : ∀ P Q R, (P ∧ R) → (P ∨ Q) :=
begin
    assume P Q R,
    assume pr,
    exact or.inl (and.elim_left pr), -- or.inl shortcut for or.intro_left (doesn't require Prop argument)
end
example : (0 = 1) ∨ (1 = 1) :=
begin
    right, -- shortcut for or.inr (also left works for or.inl)
    refl, -- shortcut for apply/exact rfl,
end

--elim (or.elim _ _ _ )
--remember you can use the 'cases' keyword
example : ∀ P Q R, (P → R) → (Q → R) → (P ∨ Q) → R :=
begin
    assume P Q R,
    assume pr,
    assume qr,
    assume porq,
    exact or.elim porq pr qr,
end
example : ∀ P Q, (P → Q) → (P ∨ Q) → Q :=
begin
    intros,
    cases a_1,
        -- case 1
        apply a,
        exact a_1,
        -- case 2
        exact a_1,
end


/- BI-IMPLICATION -/
-- intro
example : ∀ P Q, (P → Q) → (Q → P) → (P ↔ Q) :=
begin
    assume P Q,
    assume pq qp,
    exact iff.intro pq qp,
end

-- elim (iff.elim _ )
example : ∀ P Q : Prop, (P ↔ Q) → (P → Q) :=
begin
    assume P Q,
    assume piffq,
    assume p,
    exact (iff.elim_left piffq) p,
end
example : ∀ P Q : Prop, (P ↔ Q) → ((P → Q) ∧ (Q → P)) :=
begin
    intros,
    apply and.intro,
    exact iff.elim_left a,
    exact iff.elim_right a,
end

-- both
-- this is a particularly challenging proof
example : ∀ P Q R : Prop, (P ↔ Q) → (Q ↔ R) → (R ↔ P) :=
begin
    intros,
    apply iff.intro,
    assume r,
    -- One line solution:
    -- exact (iff.elim_right a) ((iff.elim_right a_1) r),
    -- OR you can do it with 'have' statements
    have pimpq : Q → P := iff.elim_right a,
    have rimpq : R → Q := iff.elim_right a_1,
    exact pimpq (rimpq r),
    assume p,
    exact (iff.elim_left a_1) ((iff.elim_left a) p),
end

/- NEGATION -/
example : ∀ P : Prop, ¬ P → (P → false) :=
begin
    assume P,
    assume np,
    exact np,
end
example : ∀ P Q : Prop, (P ∧ Q) → ¬ P → false :=
begin
    intros,
    exact a_1 (and.elim_left a),
end

/- FORALL -/ -- which we've been using extensively up until this point already
example : ∀ P Q : Prop, (∀ p : P, Q) → (P → Q) :=
begin
    assume P Q,
    assume funcPtoQ,
    -- exact funcPtoQ, OR you can try...
    assumption, -- shortcut if your proof statement is in your context menu
end

/- EXISTS -/
-- intro
example : ∀ n : nat, ∃ m, n = m :=
begin
    assume n,
    apply exists.intro n,
    refl,
end

-- Below is the property isEven.
-- A natural number is even if there exists
-- another natural number k such that 2k = n

def isEven : ℕ → Prop := 
    λ n, ∃ k, 2 * k = n

-- Define isOdd below.
-- A natural number is odd if there exists
-- another natural number k such that 2k + 1 = n

def isOdd : ℕ → Prop :=
    λ n : nat, ∃ k : nat, (2 * k + 1) = n

-- elim/both
-- this is a particularly challenging proof
example : ∀ n : nat, (isEven n) → (isEven (2*n)) :=
begin
    unfold isEven, -- "desugars" isEven to its definition above
    intros,
    apply exists.elim a,
    assume witness,
    assume proof_that_n_is_even_with_witness,
    rewrite<- proof_that_n_is_even_with_witness,
    apply exists.intro (2*witness),
    refl,
end

-- Alternatively, because we know that 2*<any number> is even
-- you can shorten the proof:
example : ∀ n : nat, (isEven n) → (isEven (2*n)) :=
begin
    unfold isEven, -- "desugars" isEven to its definition above
    intros,
    apply exists.intro n,
    refl,
end