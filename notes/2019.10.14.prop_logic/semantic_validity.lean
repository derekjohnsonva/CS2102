import .prop_logic 

open prop_logic
open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp


def isModel (i: var → bool) (e : pExp) :=
    pEval e i = tt

def valid (e : pExp) :=
    ∀ (i : var → bool), 
        isModel i e


def unsatisfiable (e : pExp) :=
    ∀ (i : var → bool),
        ¬ isModel i e

def satisfiable (e : pExp) :=
    ∃ (i : var → bool), 
        isModel i e
/-
satisfiable if there exists a pExp e that satisfies the condition i e -> tt
-/


def satisfiable' (e : pExp) :=
    ∃ (i : var → bool), 
        isModel i e

def sat_but_not_valid (e : pExp) :=
    (satisfiable e) ∧ ¬ (valid e)