namespace option
inductive moption (T : Type) : Type
| some : T → moption
| none : moption


def o1 := moption.some 3
def o2 := moption.none nat

def option_value {T :Type} : moption T → T → T 
| (moption.some t) d := t 
| (moption.none T) d := d

def just_zero : ℕ → moption nat
| 0 := moption.some 0
| _ := moption.none nat

#reduce option_value o1 0  --returns the value stored in o1
#reduce option_value o2 0  --returns the default value

#reduce just_zero 0
#reduce just_zero 1

end option
