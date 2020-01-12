def my_reverse {α : Type} : list α → list α
| list.nil := list.nil
| (list.cons h t) := list.append (my_reverse t) (list.cons h list.nil)

#eval my_reverse [1,2,3]

-- Look over translating from logic to english

-- looking at pEval
/-
def pEval : pExp → (var → bool) → bool 
| (litExp b) i := b
| (varExp v) i := i v
| (unOpExp op e) i := 
    (interpUnOp op) (pEval e i)
| (binOpExp op e1 e2) i := 
     (interpBinOp op)
        (pEval e1 i) 
        (pEval e2 i)
-/

