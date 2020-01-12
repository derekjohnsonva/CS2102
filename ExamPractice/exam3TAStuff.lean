example : ∀ P Q : Prop, (∀ p : P, Q) → (P → Q) :=
begin
    assume P Q,
    assume pimpq,
    exact pimpq,
end

def isEven : ℕ → Prop :=
    λ (n : nat), ∃ k, 2*k = n

example : ∀ n : nat, (isEven n) → (isEven (2*n)) := 
begin 
    unfold isEven,
    assume n,
    assume premise,
    apply exists.intro n,
    refl,
end