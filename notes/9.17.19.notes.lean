/-
Namespaces: Declarative regions that provide scope to an identifier
-/
--First Namespace
namespace cs 

def x := 1
#check x
#eval x

end cs

--Second Namespace
namespace oc 

def x := "Hi!"
#check x
#eval x

end oc

--to evaluate variables outside of the namespace, prepend the variable with the namespace
#eval cs.x
#eval oc.x

open cs -- this opens the cs namespace until it is closed

--TYPES

#check 1 --check will return the data type
#check bool --data of type Type

--making a new data Type
inductive day : Type  
 | sun : day
 | mon : day
 | tue : day 
 | wed : day 
 | thu : day 
 | fri : day 
 | sat : day


inductive mybool : Type
    | ttt
    | fff

open day
def nextDay : day → day 
 | sun := mon
 | mon := tue
 | tue := wed 
 | wed := thu 
 | thu := fri 
 | fri := sat 
 | sat := sun