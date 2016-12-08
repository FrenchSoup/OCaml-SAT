(*********************************************************************************************)
(* Projet de Programmation Fonctionnelle Licence 2 : Evaluateur d'équations logiques         *)
(* Cyprien RUFFINO                                                                           *)
(*********************************************************************************************)

(*********************************************************************************************)
(* Définitions des types *)
(*********************************************************************************************) 
type value = True
	     | False 
	     | Undefined;;

type variable = Var of string * value;;

type formula = And of formula * formula
	       | Or of formula * formula 
	       | Impl of formula * formula 
	       | Eq of formula * formula 
	       | Not of formula 
	       | Value of value 
	       | Variable of variable
	       |Vide;;

type input=Formule
	   |Balayage
	   |Satisfable
	   |Clear
	   |Ensemble;;

exception FormuleVide;;
exception ErreurEntree;;
exception ErreurFormule of int;;
exception Exit;;

(*********************************************************************************************)
(* Quelques fonctions élémentaires utilisées plus tard *)
(*********************************************************************************************)
let string_of_value = fun x -> match x with
  |True->"Vrai"
  |False->"Faux"
  |Undefined->"Indéfini";;

let string_of_char = String.make 1 ;; (* Cette fonction devrait vraiment etre dans le module Pervasives... *)

let rec string_of_formule = fun f -> match f with
  |And(x,y)->(string_of_formule x)^"A"^(string_of_formule y)
  |Or(x,y)->(string_of_formule x)^"O"^(string_of_formule y)
  |Impl(x,y)->(string_of_formule x)^"I"^(string_of_formule y)
  |Eq(x,y)->(string_of_formule x)^"E"^(string_of_formule y)
  |Not x -> "N"^(string_of_formule x)
  |Variable (Var(x,y)) ->x
  |Value x -> string_of_value x
  |Vide->"Aucune formule";;

let rec get_keys=fun l -> match l with (* Retourne la liste des clés d'une liste d'association *)
    |[]->[]
    |h::t->(fst h)::get_keys t 

(***********************************************************************************************)
(* Fonctions d'évaluation de formules *) 
(***********************************************************************************************)

let rec sub_var = fun f rep var -> match f with (* Substitue une variable dans une formule *)
  And(x,y)->And(sub_var x rep var, sub_var y rep var)
  |Or(x,y)->Or(sub_var x rep var, sub_var y rep var)
  |Impl(x,y)->Impl(sub_var x rep var, sub_var y rep var)
  |Eq(x,y)->Eq(sub_var x rep var, sub_var y rep var)
  |Not x -> Not(sub_var x rep var)
  |Variable (Var(x,y)) -> if (Variable (Var(x,y)))=Variable var then Variable(Var(x,rep)) else Variable (Var(x,y))
  |Value x -> Value x
  |Vide -> raise FormuleVide;;

let rec elim = fun f -> match f with (* Elimine les implications et les équivalences d'une formule *)
   And(x,y)->And(elim x, elim y)
  |Or(x,y)->Or(elim x, elim y)
  |Impl(x,y)->Or(elim (Not x), elim y)
  |Eq(x,y)->And(elim (Impl(x,y)), elim (Impl(y,x)))
  |Not x -> Not(elim x)
  |Variable (Var(x,y)) -> Variable (Var(x,y))
  |Value x -> Value x
  |Vide -> raise FormuleVide;;

let comp=fun x1 x2 -> (* Fonction de comparaison pour le tri *)
  if (snd x1) > (snd x2) then -1 else
    if (snd x1) < (snd x2) then 1 else 0

let sort = fun l -> (* Trie les variables par nombre d'appartition *)
  let rec comptage=fun l acc -> match l with
    |[]->acc
    |h::t->if List.mem_assoc h acc 
      then let x=(h,(List.assoc h acc)+1) in comptage t (x::(List.remove_assoc h acc))
      else comptage t ((h,0)::acc)
  in get_keys (List.sort comp (comptage l []));;

let get_variables = fun f -> (* Donne la liste des variables (triée) d'une formule *)
  let rec aux = fun f l -> match f with 
  |Variable (Var(x,y)) -> [((Var(x,y)):variable)]
  |Value x -> []
  |Impl(x,y)->l@(aux x l)@(aux y l)
  |Eq(x,y)->l@(aux x l)@(aux y l)
  |And(x,y)->l@(aux x l)@(aux y l)
  |Or(x,y)->l@(aux x l)@(aux y l)
  |Not x -> l@(aux x l)
  |Vide -> raise FormuleVide
  in sort(aux f []);;

let rec eval = fun f -> match f with (* Evalue une formule *)
  |Value x -> x
  |Variable (Var(x,y))-> y 
  |And(x,y)->(match (eval (x), eval (y)) with
    |(True, True)->True
    |(False,_)->False
    |(_,False)->False
    |(Undefined,_)->Undefined
    |(_,Undefined)->Undefined)
  |Or(x,y)->(match (eval (x), eval (y)) with
    |(True, _)->True
    |(_,True)->True
    |(False,False)->False
    |(Undefined,_)->Undefined
    |(_,Undefined)->Undefined)
  |Not(x)->(match (eval (x)) with
    |True->False
    |False->True
    |Undefined->Undefined)
  |Eq(x,y)->(match (eval (x), eval (y)) with
    |(True, True)->True
    |(False,False)->False
    |(Undefined,_)->Undefined
    |(_,Undefined)->Undefined
    |(_,_)->False)
  |Impl(x,y)->(match (eval (x), eval (y)) with
    |(False,_)->True
    |(_,True)->True
    |(Undefined,_)->Undefined
    |(_,Undefined)->Undefined
    |(_,_)->False)
  |Vide -> raise FormuleVide;;

(***********************************************************************************************)
(* Algorithmes de balayage et de satisfabilité *)
(***********************************************************************************************)

let balayage = fun f -> (* Applique l'algorithme de balayage *)
  let rec aux = fun f v-> match v with
    []->false
    |h::t -> if(eval(And((sub_var f True h),(sub_var f False h))))=True then true 
      else if(eval(And((sub_var (Not f) True h),(sub_var (Not f) False h))))=True then false
	else aux f t
  in aux (elim f) (get_variables f);;

let satisfable = fun f -> (* Applique l'algorithme de satisfabilité *)
  let rec aux=fun form vals->match form with
    |[]-> vals
    (* Séparation en deux fonctions : une gère form et l'autre vals *)
    |h::t->aux (t@(aux1(get_variables h))) (vals@aux2 (get_variables h)) 
  and aux1=fun vars -> match vars with
    |[] -> []
    |h::t -> let f1=sub_var f True h and f2=sub_var f False h in (* Gestion des ajouts de form *)
	     (aux1 t)@(if(eval f1)=False then 
	       if(eval f2)=False then [f1;f2]
	       else [f1] 
	     else 
	       if (eval f2)=False then [f2]
	       else [])
  and aux2=fun vars ->  match vars with 
    |[] -> []
    |h::t -> let f1=(sub_var f True h) and f2=(sub_var f False h) in (* Gestion des ajouts de vals *)
	     (aux2 t)@(if(eval f1)=True then 
	       if(eval f2)=True then [(get_variables f1);(get_variables f2)]
	       else [(get_variables f1)] 
	     else 
	       if (eval f2)=True then [(get_variables f2)] 
	       else [])
  in aux [elim f] [];;

(***********************************************************************************************)
(* Fonctions de lecture d'une chaine de caractères *)
(***********************************************************************************************)

let recup_gauche = fun s i -> String.sub s 1 (i-1);; (* Récupère la partie gauche de la formule *)
let recup_droite = fun s i -> String.sub s (i+1) ((String.length s)-i-1);;
(* Récupère la partie gauche de la formule *)

let rec curseur=fun i-> (* Construit une chaine de caractère désignant l'endroit de l'erreur *)
  if i+10>0 then " "^curseur (i-1) else "^\n";;

let rec decomposition_string = fun s -> (* Décompose une chaine de caractères en paramètre en une formule *)
  let rec aux1 = fun s par i ->
    try
      if s="END" then Vide else
	match String.get s i with
	|'(' -> aux1 s (par+1) (i+1)
	|')' -> aux1 s (par-1) (i+1)
	|'N' when par=1 -> Not(aux1 (recup_droite s i) 0 0)
	|'O' when par=1 -> Or((aux1 (recup_gauche s i ) 0 0),(aux1 (recup_droite s i ) 0 0))
	|'A' when par=1 -> And((aux1 (recup_gauche s i ) 0 0),(aux1 (recup_droite s i) 0 0))
	|'I' when par=1 -> Impl((aux1 (recup_gauche s i ) 0 0),(aux1 (recup_droite s i ) 0 0))
	|'E' when par=1 -> Eq((aux1 (recup_gauche s i ) 0 0),(aux1 (recup_droite s i ) 0 0))
	| x  when par=0 -> Variable (Var((string_of_char x), Undefined))
	| _ -> aux1 s par (i+1)
    with Invalid_argument _ -> raise (ErreurFormule i)
  in aux1 s 0 0;;

let read_formule=fun () -> (* Lit une formule au clavier et appele sa décomposition *)
  begin
    print_string "\nFormule # ";
    [decomposition_string (read_line () )]
  end;;

let read_ensemble_formules=fun ()-> (* Lit un ensemble de formules au clavier et appele sa décomposition *)
  let rec aux = fun f ->
    let line=(read_formule ()) in  
    match line with
    |[Vide]->f
    |x->aux (x@f)
  in aux (read_formule ());;

(***********************************************************************************************)
(* Fonctions intermédiaires lancées par l'invite de commandes *)
(***********************************************************************************************)

let rec enum_formules= fun f-> match f with (* Affiche toutes les formules chargées une à une *)
  |[]->""
  |h::t->"\n-"^(string_of_formule h)^(enum_formules t);;

let rec print_valuations = fun (v:variable list list)-> (* Fournit un affichage des valuations du test de satisfabilité *)
  let rec aux = fun (w:variable list)->match w with
    |[]->()
    |Var(x,y)::t->(print_string("-"^(x)^" : "^(string_of_value (y))^" ");(aux t))
  in
  match v with
  |[]->print_string"\n"
  |h::t->(print_string"[";aux h;print_string "]\n";print_valuations t);;

let balayage_top=fun f -> (* Applique l'algorithme de balayage sur les formules chargées dans le prompt *)
  let rec aux=fun m->match m with
    |[]->f
    |[Vide]->(print_string "Aucune formule chargée\n";f)
    |h::t-> (if balayage h 
      then print_string ("La formule "^(string_of_formule h)^" est une tautologie\n")
      else print_string ("La formule "^(string_of_formule h)^" n'est pas une tautologie\n");(aux t))
  in aux f;;

let satisfable_top=fun f -> (* Applique l'algorithme de satisfabilité sur les formule chargée dans le prompt *)
  let rec aux = fun m ->
    match m with
    |[]->f
    |[Vide]->(print_string "Aucune formule chargée\n";f)
    |h::t-> let res=satisfable h in 
	 if res=[]
	  then (print_string ("La formule "^(string_of_formule h)^" n'a pas de solutions\n");(aux t))
	  else (print_string ("La formule "^(string_of_formule h)^" a pour valuation correcte : \n"); print_valuations res;(aux t))
  in aux f;;

let man = fun f -> (* Affiche l'aide *)
  begin 
    print_string "----------------------------------------------------------------------------------------------\n";
    print_string "Utilisation du prompt du projet : \n";
    print_string "aide : affiche ce menu \n";
    print_string "formule : charger une formule propositionnelle\n";
    print_string "ensemble : charger un ensemble de formules propositionelles(taper END pour arreter la lecture)\n";
    print_string "balayage : applique l'algorithme de balayage sur la formule chargée\n";
    print_string "satisfable : applique l'algorithme de satisfabilité sur la formule chargée\n";
    print_string "vider : efface la formule chargée\n";
    print_string "sortie : quitte ce menu\n\n";
    print_string "Syntaxe des formules : -Ou : O\n-Et : A\n-Non : N\n-Implication : I\n-Equivalence : E\n";
    print_string "Entourez la formule d'une paire de parenthèses\n";
    print_string "Les variables sont les lettres minuscules\n";
    print_string "Exemple : ((aOb)A(aOc))\n";
    print_string "----------------------------------------------------------------------------------------------\n";
    f
  end;;

let command = fun s f -> match s with (* Interprète la commande entrée dans le prompt *)
  |"aide"->man f
  |"formule"->read_formule ()
  |"balayage"->balayage_top f
  |"satisfable"->satisfable_top f
  |"sortie"->raise Exit
  |"vider"->[Vide]
  |"ensemble"->read_ensemble_formules ()
  |_->raise ErreurEntree;;



(***********************************************************************************************)
(* Invite de commandes *)
(***********************************************************************************************)

let toplevel = fun () -> (* Fonction gérant l'invite de commande *)
  let rec invite = fun f ->
    begin
      print_string ("Formule chargées : "^(enum_formules f));
      print_string "\nCommande # ";
      try 
	let formule=command (read_line ()) f in invite formule
      with 
	|ErreurEntree ->(print_string "Commande invalide, tapez 'aide' pour recevoir de l'aide\n";invite f);
	|Exit -> print_string "Au revoir!\n";
	|ErreurFormule i -> print_string ((curseur i)^"Formule incorrecte, tapez 'aide' pour recevoir de l'aide\n");invite f;
    end 
 in (print_string "----------------------------------------------------------\n";
     print_string "Projet de Programmation Fonctionnelle \n";
     print_string "Evaluateur et solveur de formules propositionnelles\n";
     print_string "Cyprien RUFFINO \n";
     invite [Vide]);;
 
toplevel ();;

(***********************************************************************************************)
(* Fin du programme *)
(***********************************************************************************************)
