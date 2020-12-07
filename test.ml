(* #use "main.ml";; *)


print_string "Inizializzo gli insiemi di TEST";;
let e1 = Set(Next(CstInt 2 ,Next(CstInt 4, Next(CstInt 3, Next(CstInt 5 ,Empty)))),TInt);;
let e2 = Set(Next(CstInt 20 ,Next(CstInt 4, Next(CstInt 3, Next(CstInt 10 ,Empty)))),TInt);;

let e3 = Union(e2,e1);;

let e4 = Of(TInt, Exp(Times(CstInt 3,CstInt 3),Exp(Sum(CstInt 2,CstInt 10),Empty)));;



print_string "stampo le chiusure degli insiemi creati";;
eval e1 emptyEnv;;
eval e2 emptyEnv;;
eval e3 emptyEnv;;
eval e4 emptyEnv;;


print_string "Inizializzo le funzioni";;
let f1 = Fun("x",
            Mayor(Den("x"),(CstInt 0)));;

let f2 = Fun("x",
            Times(Den("x"),(CstInt 3)));;



print_string "Applicazioni delle funzioni con ForAll e Map";;

eval (For_all(f1,e3)) emptyEnv;;
eval (Map(f2,e3)) emptyEnv;;
