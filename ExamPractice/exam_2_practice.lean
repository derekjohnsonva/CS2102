/- Implies Truth Table
    t   t   t
    t   f   f
    f   t   t
    f   f   t
-/

-- Reverse a list using recursion
def my_reverse {α : Type} : list α → list α
| list.nil := list.nil
| (list.cons h t) := list.append (my_reverse t) (list.cons h list.nil)


/- *** I. FORMAL LANGUAGES *** -/
inductive var : Type 
| mkVar : ℕ → var

inductive unOp : Type
| square

inductive binOp : Type
| powOp

inductive pExp : Type
| litExp : ℕ → pExp
| varExp : var → pExp
| unOpExp : unOp → pExp → pExp
| binOpExp : binOp → pExp → pExp → pExp

open var
open pExp
open unOp
open binOp

def pZero := litExp nat.zero
def pSquare := unOpExp square
def pPow := binOpExp powOp

def count : pExp → nat
| (litExp b) := 0
| (varExp v) := 1
| (unOpExp op e) := count e 
| (binOpExp op e1 e2) := (count e1 + count e2)

notation e1 ^ e2 :=  pPow e1 e2


def bSquare : ℕ → ℕ 
| 0 := 1
| (n + 1) := 2 * bSquare n

def bPow : ℕ → ℕ → ℕ
| m 0        := 1
| m (n + 1)  := pow m n * m 

def interpUnOp : unOp → (ℕ → ℕ) 
| squareOp := bSquare

def interpBinOp : binOp → (ℕ → ℕ → ℕ) 
| powOp := bPow

def pEval : pExp → (var → ℕ) → ℕ
| (litExp b) i := b
| (varExp v) i := i v
| (unOpExp op e) i := 
    (interpUnOp op) (pEval e i)
| (binOpExp op e1 e2) i := 
     (interpBinOp op)
        (pEval e1 i) 
        (pEval e2 i)


def var1 := mkVar 1
def var2 := mkVar 2
def var5 := mkVar 5

def X : pExp:= varExp var1



/- *** II. PREDICATE LOGIC *** -/
-- ∀ and ∃ are called quantifiers
-- ∀ (p : Person), ∃ (q : Person), likes p q
-- forall people, there exists some person such that forall people they like that person
-- eventually: everyone likes someone
-- ∃ (q : Person), ∀ (p : Person), likes p q
-- there exists someone who all people like
-- someone is liked by everybody

/-
∃ (p : Person), ∀ (q : Person), ¬ likes q p
there exists someone that nobody likes
∃ (p : Person), ∀ (q : Person), ¬ likes p q
someone likes nobody 
∀ (q : Person), ∃ (p : Person), ¬ likes q p
nobody likes everyone
everyone has someone they don't like
∀ (q : Person), ∃ (p : Person), ¬ likes p q
nobody is liked by everyone
everyone has someone that doesn't like them
¬ (∀ (q : Person), ∃ (p : Person), likes p q)
this is equivalent to: 
∃ (q : Person), ∀ (p : Person), ¬ likes p q
in english, there exists someone that nobody likes.

∀ (q : Person), ¬ (∃ (p : Person), likes p q)
this is equivalent to:
∀ (q : Person), ∀ (p : Person), ¬ likes p q
in english, nobody likes anyone 

Simpler negation example:
¬ (∀ p: Person, p has purple hair)
Wordy English: "It is not the case that everyone has purple hair"
i.e. We can disprove "everyone has purple hair" by finding someone
     that does not have purple hair
The above is equivalent to:
∃ p: Person, ¬ (p has purple hair)


∀ (p : Person), ∃ (q : Person), likes q p
everyone is liked by somebody

∀ (p : Person), ∃ (q : Person), ¬ likes p q → 
∃ (p : Person), ∀ (q : Person), ¬ likes q p
if _, then _
if everyone has someone they don't like, then noone likes someone

¬ (∃ (x : ℕ ), ∀ (y : ℕ ), x>y)
there is not a largest natural number
-/


/- *** II. PROOFS *** -/
/-
    Tactic scripts use begin and end blocks and have several keyworks including
    1) assume - Whenever you have an implication in your goal, 
    you can assume the premise and then all that's left is to 
    prove the rest of the implication. Note that something like 
    ¬P is considered an implication of type P -> false

    2) exact is the same thing as apply - only difference is 
    that you can only use it to solve a goal (e.g. if you don't
    solve the goal with your exact statement, you should be
    using apply instead)

    3) intros is a shortcut for assume - it assumes everything
    in implications for you.

    4) apply applies a function to your goal. For example, 
    if you are trying to prove A and B, you can apply and.intro 
    and then you have to prove A and B next.
-/

--TOOLS: and.intro, and.elim_left, and.elim_right, eq.refl, 
-- eq.trans, eq.symm, assume, exact, apply

example (a b : ℕ ):a = b →  b = a :=
begin
    assume aeqb,
    apply eq.symm aeqb,
end

def syllogism (P Q R : Prop): (P -> Q) -> (Q -> R) -> (P -> R) :=
begin
    intros pq qr pfP,
    apply qr,
    apply pq,
    exact pfP,
end


def and_elim_left (P Q : Prop): (P ∧ Q) -> P :=
begin
    assume pnq,
    apply and.elim_left pnq,
end

example : ∀ P Q R : Prop, (P → Q) → (P ∧ R) → (Q ∧ (1 = 1)) :=
begin
    assume (P Q R : Prop),
	intros pq,
    intros pr,
    apply and.intro _ _,
        exact pq (and.elim_left pr),
        exact eq.refl 1,
end
/- EXTRA CREDIT -/
def neg_intro (P : Prop): (P -> false) -> ¬ P :=
begin
    intro a,
    exact a,
end

variables p q : Prop

example (hpq : p → q) (hnq : ¬q) : ¬p :=
begin 
    assume hp : p,
    show false, from hnq(hpq hp),
end

/-
  Negation, ¬p, is actually defined to be p → false, 
  so we obtain ¬p by deriving a contradiction from p. 
  Similarly, the expression hnp hp produces a proof of 
  false from hp : p and hnp : ¬p. The next example uses 
  both these rules to produce a proof of (p → q) → ¬q → ¬p. 
  (The symbol ¬ is produced by typing \not or \neg.)  
-/

theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from and.intro (and.right h) (and.left h))
  (assume h : q ∧ p,
    show p ∧ q, from and.intro (and.right h) (and.left h))




def false_elim (P : Prop): false -> P :=
begin
    assume p,
    exact false.elim p,
end

def and_intro (P Q : Prop) : P -> Q -> (P ∧ Q) :=
begin
    intros p q,
    exact and.intro p q,
end

def and_elim_left' (P Q : Prop): (P ∧ Q) -> P :=
begin
    intros pq,
    exact and.elim_left pq,
end

def and_elim_right' (P Q : Prop) : (P ∧ Q) -> Q :=
begin
    intros qp,
    exact and.elim_right qp,
end

def or_intro_left (P Q : Prop): P -> (P ∨ Q) :=
begin
    intros p,
    exact or.intro_left Q p,
    -- shorthand is exact or.inl p
end

def or_intro_right (P Q : Prop): Q -> (P ∨ Q) :=
begin
    intros q,
    exact or.inr q,
end

def or_elim (P Q R : Prop) : (P ∨ Q) -> (P -> R) -> (Q -> R) -> R :=
begin
    assume porq pimpr qimpr,
    cases porq with pfP pfQ,
    exact pimpr pfP,
    exact qimpr pfQ,

end

def arrow_elim (P Q : Prop): (P -> Q) -> P -> Q :=
begin
    intros pinpq p,
    exact pinpq p,
end

def neg_intro' (P : Prop): (P -> false) -> ¬ P :=
begin
    intros,
    exact a,
end

example : 2+3 = 5 ∧ 3+7 = 10 → 2+5 = 7 :=
begin
intros premise,
apply eq.refl 7,
end

example : 0 = 1 → 3 = 1000 :=
begin
assume zeroeqone,
have zeroneqone : 0 ≠ 1 := dec_trivial,
contradiction,
end
