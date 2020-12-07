
(* The language *)

type ide = string;;

type tipo =         (* server per implementare gli insiemi, con i diversi tipi *)
  |TInt
  |TBool
  |TUnbound;;

type exp = CstInt of int
		| CstTrue 
		| CstFalse
		| Den of ide
		| Sum of exp * exp
		| Sub of exp * exp
		| Times of exp * exp
		| Ifthenelse of exp * exp * exp
		| Eq of exp * exp
		| Let of ide * exp * exp
		| Fun of ide * exp
		| Letrec of ide * ide * exp * exp
    | Apply of exp * exp

    (*Funzioni ausigliarie per test *)
    | Minor of exp * exp        (* Restituisce true se la prima exp è minore della seconda *)
    | Mayor of exp * exp

    | Set of setList * tipo    (* setList è l'insieme dei valori , tipo è il tipo dei valori  *)
    | Setempty of tipo          (* Costruttore di un Set vuoto, di tipo TIPO *)
    | SetInsert of exp * exp   (* exp = Set , exp è l'elemento da inserire        NB:deve rispettare il tipo *)
    | SetRemove of exp * exp    (* exp = Set, exp è l'elemento da rimuovere       NB:controlla il tipo prima di iniziare la rimozione *)
    | Singleton of exp * tipo
    | Of of tipo * explist      (* tipo = tipo della lista , explist = lista di espressioni da inserire nella lista    NB:controlla il tipo di ogni exp dentro explist prima di inserirlo *)
    (*Funzioni che restituiscono un valore bool relative a gli insiemi *)
    | IsEmpty of exp
    | Isin of exp * exp
    | Subset of exp * exp
    (* funzioni di Unione Intersezione Differenza fra insiemi *)
    | Union of exp * exp
    | Intersection of exp * exp
    | Diff of exp * exp
    (*Max e Min su insiemi nb:i tipi devono essere TInt *)
    | Min of exp
    | Max of exp
    (* Applicazioni di Funzioni sull'insieme *)
    | Map of exp * exp
    | Filter of exp * exp
    | Exists of exp * exp
    | For_all of exp * exp

    and explist = Empty | Exp of exp * explist
    and setList = Empty |Next of exp * setList;;

type 'v env = (string * 'v) list;;

type evT = Int of int | Bool of bool | Closure of ide * exp * evT env | RecClosure of ide * ide * exp * evT env | Unbound |SetClosure of evT list * tipo;;

let emptyEnv  = [ ("", Unbound)] ;;

let bind (s: evT env) (i:string) (x:evT) = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) = match s with
    | [] ->  Unbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;

let typecheck (x, y) = match x with	
         | "int" -> 
             (match y with 
                         | Int(u) -> true
                         | _ -> false)

        | "bool" -> 
              (match y with 
                          | Bool(u) -> true
                          | _ -> false)

        | _ -> failwith ("not a valid type");;

let newTypecheck x y  = match x with
  |Int(i) -> (match y with
              |TInt -> true
              |_ -> false)
  |Bool(i) ->(match y with
              |TBool -> true
              |_ -> false)
  | _ ->failwith("not a valid type");;

let int_minor(x,y) = 
match (typecheck("int",x),typecheck("int",y),x,y) with
  |(true,true, Int(v),Int(w)) -> if(v<w)then Bool(true)
                                  else Bool(false)
  |(_,_,_,_) -> failwith("run-time error");;

  let int_mayor(x,y) = 
    match (typecheck("int",x),typecheck("int",y),x,y) with
      |(true,true, Int(v),Int(w)) -> if(v>w)then Bool(true)
                                      else Bool(false)
      |(_,_,_,_) -> failwith("run-time error");;


let int_eq(x,y) =   
match (typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> failwith("run-time error ");;
       
 let int_plus(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_sub(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_times(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v * w)
  | (_,_,_,_) -> failwith("run-time error ");;

let rec checkIn (i: exp) (l:  setList) : bool = match l with (*controlla se i è all'interno di l*)
| Empty -> false
| Next(x,ts) -> if (i=x) then true
    else checkIn i ts;;

let rec eval  (e:exp) (s:evT env) = match e with
 | CstInt(n) -> Int(n)
 | CstTrue -> Bool(true)
 | CstFalse -> Bool(false)
 | Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
 | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
 | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
 | Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
 | Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
                (match (typecheck("bool", g), g) with
			                  | (true, Bool(true)) -> eval e2 s
                        | (true, Bool(false)) -> eval e3 s
                	      | (_, _) -> failwith ("nonboolean guard"))
| Den(i) -> lookup s i
| Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
| Fun(arg, ebody) -> Closure(arg,ebody,s)
| Letrec(f, arg, fBody, letBody) -> 
  let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
      eval letBody benv
| Apply(f, eArg) -> 
  let fclosure = eval f s in 
     (match fclosure with 
       | Closure(arg, fbody, fDecEnv) ->
         let aVal = eval eArg s in
	          let aenv = bind fDecEnv arg aVal in 
                eval fbody aenv
       | RecClosure(f, arg, fbody, fDecEnv) ->
         let aVal = eval eArg s in
         let rEnv = bind fDecEnv f fclosure in
	 let aenv = bind rEnv arg aVal in 
         eval fbody aenv
       | _ -> failwith("non functional value"))
| Set (initList, t) ->(SetClosure ((evalSetList initList s t) , t))
| Setempty (t) -> (SetClosure ((evalSetList Empty s t), t))
| SetInsert(set, e) ->
            let eSet = eval set s in
            let eValue = eval e s in
            (match eSet with
              |SetClosure(l,t) -> if (newTypecheck eValue t) && not(checkpresent eValue l ) then SetClosure(eValue::l,t)
                                  else failwith("Elementi doppi non consentiti")
                                                
              |_ -> failwith("not a Set"))
| SetRemove(set ,e)->
        let eSet = eval set s in
        let eValue = eval e s in
        (match eSet with
          |SetClosure(l,t) -> if(newTypecheck eValue t) then let newlist = remove l eValue in SetClosure(newlist,t)
                              else failwith("tipo non supportato")
          |_ ->failwith("not a Set"))
| Singleton(e,t) ->
      let eValue = eval e s in
      (
        if(newTypecheck eValue t) then SetClosure(eValue::[],t)
        else failwith("Tipo errato")
      )
| Of(t, el) -> let eList = evalExpListType el s t in 
              (
                if checkDuplicate eList then SetClosure(eList,t)
                else failwith ("Duplicati trovati")
              )
| IsEmpty(e) -> let eSet = eval e s in
              (
                match eSet with
                  |SetClosure(insieme,t) -> (match insieme with
                                              |[] -> Bool(true)
                                              |x::xs -> Bool(false))
                  | _ -> failwith("Not a Set")
              )
| Isin(set, e) -> let eValue = eval e s in
                  let eSet = eval set s in
                  (
                    match eSet with
                    |SetClosure(lis,t) -> (if(checkpresent eValue lis) then Bool(true)
                                            else Bool(false))
                    |_ -> failwith("first argument not a set")
                  )
| Subset(set1,set2) -> let eSet1 = eval set1 s in
                       let eSet2 = eval set2 s in
                       (
                         match eSet1 with
                          |SetClosure(ls,t)->
                                    (
                                      match eSet2 with
                                        |SetClosure(ls2,t2) ->
                                                    (
                                                      if not (t2=t) then Bool(false)
                                                      else Bool(subSetfun ls ls2)
                                                    )
                                        |_ -> failwith("second argument not a set")
                                    )
                          |_ -> failwith("first argument not a set")
                       )
| Union(set1,set2) -> let eSet1 = eval set1 s in
                      let eSet2 = eval set2 s in
                      (
                        match eSet1 with
                          |SetClosure(ls1, t1) ->
                                    (
                                      match eSet2 with
                                        |SetClosure(ls2,t2) -> 
                                                    (
                                                      if(t2=t1) then SetClosure(unionSetfun ls1 ls2 , t1)
                                                      else failwith("differnt Tipo of Set")
                                                    )
                                        | _ -> failwith("Second argument not a set")
                                    )
                          |_ -> failwith("first argument not a set")
                      )
| Intersection(set1,set2) -> let eSet1 = eval set1 s in
                             let eSet2 = eval set2 s in
                             (
                              match eSet1 with
                              |SetClosure(ls1, t1) ->
                                        (
                                          match eSet2 with
                                            |SetClosure(ls2,t2) -> 
                                                        (
                                                          if(t2=t1) then SetClosure(intersectionSetfun ls1 ls2 , t1)
                                                          else failwith("differnt Tipo of Set")
                                                        )
                                            | _ -> failwith("Second argument not a set")
                                        )
                              |_ -> failwith("first argument not a set")
                             )
| Diff(set1, set2) ->let eSet1 = eval set1 s in
                      let eSet2 = eval set2 s in
                      (
                      match eSet1 with
                      |SetClosure(ls1, t1) ->
                                (
                                  match eSet2 with
                                    |SetClosure(ls2,t2) -> 
                                                (
                                                  if(t2=t1) then SetClosure(diffSetfun ls1 ls2 , t1)
                                                  else failwith("differnt Tipo of Set")
                                                )
                                    | _ -> failwith("Second argument not a set")
                                )
                      |_ -> failwith("first argument not a set")
                      )
| Max(set) -> let eSet = eval set s in
              (
                match eSet with
                  |SetClosure(ls,t)->
                              (
                                if(t=TInt) then getMax ls
                                else failwith ("not a valid TIPO")
                              )
                  |_ ->failwith("not a set")
              )
| Min(set) -> let eSet = eval set s in
              (
                match eSet with
                  |SetClosure(ls,t)->
                              (
                                if(t=TInt) then getMin ls
                                else failwith ("not a valid TIPO")
                              )
                  |_ ->failwith("not a set")
              )
| For_all(f, set) -> let fclosure = eval f s in
                     let eSet = eval set s in 
                     (
                       match fclosure with
                        |Closure(arg,fbody,fDecEnv) ->
                                (
                                  match eSet with
                                    |SetClosure(ls,t)-> Bool(applyforall arg fbody fDecEnv ls)
                                    |_ -> failwith("not a set")
                                )
                        |_ -> failwith("not a function")
                     )
| Exists(f , set) ->let fclosure = eval f s in
                    let eSet = eval set s in 
                    (
                      match fclosure with
                      |Closure(arg,fbody,fDecEnv) ->
                              (
                                match eSet with
                                  |SetClosure(ls,t)-> Bool(applyexist arg fbody fDecEnv ls)
                                  |_ -> failwith("not a set")
                              )
                      |_ -> failwith("not a function")
                    )
| Filter(f , set) -> let fclosure = eval f s in
                      let eSet = eval set s in
                      (
                        match fclosure with
                          |Closure(arg,fbody,fDecEnv) ->
                                  (
                                    match eSet with
                                      |SetClosure(ls,t) -> SetClosure((applyfilter arg fbody fDecEnv ls),t)
                                      |_ -> failwith("not a set")
                                  )
                          |_ -> failwith("not a funciont")
                      )
| Map(f,set) -> let fclosure = eval f s in
                      let eSet = eval set s in
                      (
                        match fclosure with
                          |Closure(arg,fbody,fDecEnv) ->
                                  (
                                    match eSet with
                                      |SetClosure(ls,t) -> SetClosure((applymap arg fbody fDecEnv ls),t)
                                      |_ -> failwith("not a set")
                                  )
                          |_ -> failwith("not a funciont")
                      )
| Minor(e1,e2) -> int_minor( (eval e1 s) , (eval e2 s))
| Mayor(e1,e2) -> int_mayor( (eval e1 s), (eval e2 s))

| _ -> failwith("KAPPA")
and applymap (arg :ide) (fbody :exp) (fEnv: evT env) (l : evT list) = match l with
  |[]->[]
  |x::xs -> let ris = eval fbody (bind fEnv arg x) in ris::(applymap arg fbody fEnv xs)

and applyfilter (arg :ide) (fbody :exp) (fEnv: evT env) (l : evT list) = match l with
  |[]->[]
  |x::xs -> let ris = eval fbody (bind fEnv arg x) in
            (
              match ris with
               |Bool(u)-> if(u) then x::(applyfilter arg fbody fEnv xs)
                          else applyfilter arg fbody fEnv xs
               |_ ->failwith("not boolean funciont")
            )
and applyexist (arg :ide) (fbody :exp) (fEnv: evT env) (l : evT list) = match l with
  |[] -> false
  |x::xs -> let ris = eval fbody (bind fEnv arg x) in 
            (
              match ris with
                |Bool(true) -> true
                |Bool(false) -> applyexist arg fbody fEnv xs
                |_ -> failwith("not boolean funciont")
            )

and applyforall (arg :ide) (fbody :exp) (fEnv: evT env) (l : evT list) = match l with
  |[] -> true
  |x::xs -> let ris = eval fbody (bind fEnv arg x) in 
            (
              match ris with
                |Bool(u) -> u && applyforall arg fbody fEnv xs
                |_ -> failwith("not boolean funciont")
            )


and getMin (ls : evT list) = match ls with
  |[] -> Int(1000)       (* NB andrebbe messo il numero più piccolo rappresentabile *)
  |x::xs -> minInt x (getMin xs)

and getMax (ls : evT list) = match ls with
  |[] -> Int(-1000)       (* NB andrebbe messo il numero più piccolo rappresentabile *)
  |x::xs -> maxInt x (getMax xs)
and maxInt (x: evT) (y: evT) = match x with
  |Int(u) ->
          (
            match y with
              |Int(i) -> if(u>i) then Int(u)
                         else Int(i)
              |_ -> failwith("not Int type")
          )
  |_ -> failwith("not Int type")

and minInt (x: evT) (y: evT) = match x with
  |Int(u) ->
          (
            match y with
              |Int(i) -> if(u>i) then Int(i)
                          else Int(u)
              |_ -> failwith("not Int type")
          )
  |_ -> failwith("not Int type")
and diffSetfun (l1:evT list) (l2: evT list) = match l1 with 
  |[] -> l2
  |x::xs -> if(checkpresent x l2) then diffSetfun xs (remove l2 x)
            else diffSetfun xs l2
and intersectionSetfun (l1 : evT list) (l2: evT list) = match l1 with
  |[] -> []
  |x::xs -> if (checkpresent x l2) then x::(intersectionSetfun xs l2)
            else intersectionSetfun xs l2 
and unionSetfun (l1 : evT list) (l2: evT list) = match l1 with
  |[] -> l2
  |x::xs -> if not (checkpresent x l2) then x::unionSetfun xs l2
          else  unionSetfun xs l2 
and subSetfun (l1 : evT list) (l2: evT list) :bool = match l1 with
  |[] -> true (*NB: si considera l'insieme vuoto un sotto insieme di qualsiasi insieme *)
  |x::xs -> checkpresent x l2 && subSetfun xs l2
        
and evalExpListType (l : explist) (amb : evT env) (ti : tipo) = match l with
  |Empty -> []
  |Exp(e,xs) -> let eValue = eval e amb in
                (
                  if(newTypecheck eValue ti) then eValue::evalExpListType xs amb ti
                  else failwith ("Tipo non conforme")
                )
and remove (lista : evT list) (value : evT) = match lista with
  |[]->[]
  |x::xs -> if(x=value) then xs
            else x::remove xs value
and checkDuplicate (l : evT list) :bool = match l with
  |[] -> true
  |x::xs -> if not (checkpresent x xs) then true && checkDuplicate xs
          else false
and checkpresent (e:evT) (l: evT list) : bool = match l with
  |[] -> false
  |x::xs -> if(e=x) then true 
            else checkpresent e xs
and evalSetList (l : setList) (amb : evT env) (t:tipo) = match l with
  |Empty -> []
  |Next(x,ts) -> let e = eval x amb in (
                if (newTypecheck e t) then 
                    if not (checkIn x ts) then e::evalSetList ts amb t
                      else failwith("Due elementi uguali trovati")
                else failwith ("tipo di dato sbagliato") )

        
             
;;


(*
Letrec("fact", "n",   
Ifthenelse(Eq(Den("n"),CstInt(0)),
                 CstInt(1),
                 Times(Den("n"),Apply(Den("fact"),Sub(Den("n"),CstInt(1))))), Apply(Den("fact"),CstInt(3)))

*)


(* TEST*)

let e1 = Set(Next(CstInt 5,Next(CstInt 2, Empty)),TInt);;
let e2 = Set(Next(CstInt 3,Next(CstInt 2, Empty)),TInt);;
let e3 = Max(e1);;
let e = eval e3 emptyEnv;;

let e4 = Set(Next(CstInt 2,Empty),TInt);;
let f1 = Fun("x",Eq(Den("x"),CstInt 2));;
eval (Apply (f1, (CstInt 2))) emptyEnv;;
eval( Filter(f1, e1)) emptyEnv;;

let f2 = Fun("x",Sum(Den("x"),CstInt 5));;
eval (Map(f2,e1)) emptyEnv;;

let f1 = Fun("x",
            (Let("y",
              Sub(Den("x"),(CstInt 2)),
              Eq(Den("x"),Sum(Den("y"),(CstInt 2))))
              ));;