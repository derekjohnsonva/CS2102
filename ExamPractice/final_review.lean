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
        intro t,
        intro P,
        exact P,
    end
example : ∀ P Q, P → Q → P := 
    begin
        intro P,
        intro Q,
        intro p,
        intro q,
        exact p,
    end
example : (0 = 1) → (0 = 1) := 
    begin 
        intros,
        exact a,
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
        intros,
        exact true.intro,
    end

example : (0 = 1) → true :=
    begin
        intros,
        apply true.intro,
    end


/- FALSE -/
example : false → (0 = 1) := 
    begin 
        intro f,
        apply false.elim f,
    end
example : ∀ P : Prop, false → P := 
    begin 
        intro P,
        assume f,
        apply false.elim f,
    end
example : ∀ P Q, P → Q → false → (P ∧ Q) := 
    begin
        assume P Q,
        assume p,
        assume q,
        assume f,
        apply false.elim f,
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
        intros P Q,
        intros p q,
        apply and.intro p q,
    end
example {P Q : Prop} : P → Q → (Q ∧ P) := 
    begin
        intros P Q,
        apply and.intro Q P,
    end
example : (0 = 0) ∧ (1 = 1) := 
    begin
        have zero := eq.refl 0,
        have one := eq.refl 1,
        apply and.intro zero one,
    end

-- elim (and.elim_left _ and and.right _ )
example : ∀ P Q : Prop, P ∧ Q → P := 
    begin 
        intros P Q pandq,
        apply and.elim_left pandq,
    end
example : ∀ P Q : Prop, P ∧ Q → Q := 
    begin 
        intros P Q pandq,
        apply and.elim_right pandq,
    end
example : ∀ P Q R : Prop, P ∧ Q ∧ R → Q := 
    begin
        intros P Q R pnqnr,
        apply and.elim_left (and.elim_right pnqnr),
    end

-- both
example : ∀ P Q R : Prop, P ∧ Q ∧ R → (P ∧ R) := 
    begin
        intros,
        have r := and.elim_right (and.elim_right a),
        have p := and.elim_left a,
        apply and.intro p r,
    end
example : ∀ P Q R : Prop, Q ∧ R ∧ P → (R ∧ P ∧ Q) := 
    begin
        intros,
        apply and.intro,
        apply and.elim_left (and.elim_right a),
        apply and.intro,
        apply and.elim_right (and.elim_right a),
        apply and.elim_left a,
    end



/- OR -/
-- intro (or.intro_left _ _, shortcut: or.inl _ and the associated right-side variant)
example : ∀ P Q, P → (P ∨ Q) := 
    begin
        intros P Q p,
        apply or.intro_left,
        apply p,
    end
example : ∀ P Q R, (P ∧ R) → (P ∨ Q) := 
    begin
        intros,
        have p := and.elim_left a,
        apply or.intro_left,
        apply p,
    end
example : (0 = 1) ∨ (1 = 1) := 
    begin
        have one := eq.refl 1,
        apply or.intro_right,
        apply one,
    end

-- elim (or.elim _ _ _ )
-- remember you can use the 'cases' keyword
example : ∀ P Q R, (P → R) → (Q → R) → (P ∨ Q) → R := 
    begin
        assume P Q,
        intro R,
        assume pimpr,
        assume qimpr,
        assume porq,
        apply or.elim porq,
        apply pimpr,
        apply qimpr,
    end

example : ∀ P Q, (P → Q) → (P ∨ Q) → Q := 
    begin 
        intros P Q,
        intros pimpq porq,
        cases porq,
        apply pimpq porq, -- case 1
        apply porq,  -- case 2
    end


/- BI-IMPLICATION -/
-- intro
example : ∀ P Q, (P → Q) → (Q → P) → (P ↔ Q) := 
    begin
        intros P Q,
        intros pimpq qimpp,
        apply iff.intro pimpq qimpp,
    end

-- elim (iff.elim _ )
example : ∀ P Q : Prop, (P ↔ Q) → (P → Q) := 
    begin
        assume P Q,
        assume piffq,
        have pimpq := iff.elim_left piffq,
        exact pimpq,
    end
example : ∀ P Q : Prop, (P ↔ Q) → ((P → Q) ∧ (Q → P)) := 
    begin
        intros P Q,
        intros piffq,
        let pimpq := iff.elim_left piffq,
        let qimpp := iff.elim_right piffq,
        apply and.intro pimpq,
        apply qimpp,
    end

-- both
-- this is a particularly challenging proof
example : ∀ P Q R : Prop, (P ↔ Q) → (Q ↔ R) → (R ↔ P) := 
begin
    intros P Q R,
    intros piffq,
    intros qiffr,
    have pimpq := iff.elim_left piffq,
    have qimpr := iff.elim_left qiffr,
    have qimpp := iff.elim_right piffq,
    have rimpq := iff.elim_right qiffr,
    apply iff.intro,
    assume r,
    apply qimpp (rimpq r),
    assume p,
    apply qimpr (pimpq p),
end

/- NEGATION -/
example : ∀ P : Prop, ¬ P → (P → false) := 
    begin
        intros P np p,
        contradiction,
    end
example : ∀ P Q : Prop, (P ∧ Q) → ¬ P → false := 
    begin
        intros P Q pandq np,
        have p := and.elim_left pandq,
        contradiction,
    end

/- FORALL -/ -- which we've been using extensively up until this point already
example : ∀ P Q : Prop, (∀ p : P, Q) → (P → Q) := 
    begin
        intros P Q pimpq,
        apply pimpq,
    end

/- EXISTS -/
-- intro
example : ∀ n : nat, ∃ m, n = m := 
    begin
        intros n,
        have nrefl := eq.refl n,
        apply exists.intro n,
        apply nrefl,
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
    λ (n : nat), ∃ k, 2 + k =n

-- elim/both
-- this is a particularly challenging proof
example : ∀ n : nat, (isEven n) → (isEven (2*n)) :=
begin
    intros n,
    unfold isEven, -- "desugars" isEven to its definition above
    intros,
    apply exists.intro n,
    refl,
end

example : 0 ≠ 1 := 
    begin
        intro,
        contradiction,
    end


