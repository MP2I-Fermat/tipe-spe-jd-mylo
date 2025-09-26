open Lexer
open Automaton

type ('token_type, 'non_terminal) grammar_entry =
  | NonTerminal of 'non_terminal
  | Terminal of 'token_type

type ('token_type, 'non_terminal) rule =
  'non_terminal * (('token_type, 'non_terminal) grammar_entry list)

type ('token_type, 'non_terminal) grammar =
  ('token_type, 'non_terminal) rule list

type ('token_type, 'non_terminal) syntax_tree =
  | Node of 'non_terminal * ('token_type, 'non_terminal) syntax_tree list
  | Leaf of 'token_type token

(* Représente les situations LR(1), du style
 * α₁…αⱼ↑ α₁₊ⱼ…αₙ ~ {b₁…bₙ} *)
type ('token_type, 'non_terminal) lr1_situation =
  ('token_type, 'non_terminal) rule * int * ('token_type list) list


(* Renvoie l’ensemble Premier_LR(1)(s) dans la grammaire g *)
let premier_LR1
    (s: ('token_type, 'non_terminal) grammar_entry list)
    (g: ('token_type, 'non_terminal) grammar) : ('token_type list) =
  (* Renvoie l’ensemble Premierₙ(s) dans la grammaire g *)
  let rec premier_LR1_n
      (n: int)
      (g: ('token_type, 'non_terminal) grammar)
      (s': ('token_type, 'non_terminal) grammar_entry list):
      ('token_type list) =
    if n = 0 then
      match s' with
      | [Terminal a] -> [a]
      | _ -> []  (* on n’a pas de règles N->ε *)
    else begin
      match s' with
      | [] -> failwith "s' est une liste vide…"
      | [NonTerminal non_terminal] ->
        print_string "coucou";
        let rules =
          List.filter (fun (x: ('token_type, 'non_terminal) rule) -> fst x = non_terminal) g
          |> List.map snd in
        print_int (List.length rules);
        if rules = [[]] then print_endline "en fait oui" else print_endline "non c’est bon";
        if rules = [[Terminal 'a'; Terminal 'b']] then print_endline "ça marche" else print_endline "ça ne marche pas";
        (premier_LR1_n (n-1) g s')::(List.map (premier_LR1_n (n-1) g) rules)
      | a_1::q ->
          [(premier_LR1_n (n-1) g [a_1]); (premier_LR1_n (n-1) g s')]
      end |> List.concat |> List.sort_uniq compare
  in
  let rec sature_premier_LR1
      (n: int)
      (g: ('token_type, 'non_terminal) grammar)
      (s': ('token_type, 'non_terminal) grammar_entry list)
      (last: 'token_type list):
      ('token_type list) =
    print_int n;
    print_endline " (sature_premier)";
    let next = premier_LR1_n n g s' in
    if next = last then next
    else sature_premier_LR1 (n+1) g s' next
  in
  sature_premier_LR1 1 g s (premier_LR1_n 0 g s)


let test_premier_LR1 =
  let grammaire1 (* page 123, exemple 144 *) = [
    ('S', [Terminal 'a'; NonTerminal 'T']);
    ('T', [Terminal 'b'])
  ] in
  assert (premier_LR1 [Terminal 'a'; NonTerminal 'T'] grammaire1 = ['a']);
  assert (premier_LR1 [NonTerminal 'T'] grammaire1 = ['b']);
  let grammaire2 (* page 60, exemple 24 *) = [
    ('S', [NonTerminal 'U']);
    ('S', [NonTerminal 'V']);
    ('U', [Terminal 'a'; Terminal 'b']);
    ('V', [Terminal 'c'; Terminal 'd']);
  ] in
  assert (premier_LR1 [Terminal 'a'; Terminal 'b'] grammaire2 = ['a']);
  assert (premier_LR1 [Terminal 'c'; Terminal 'd'] grammaire2 = ['c']);
  assert (premier_LR1 [NonTerminal 'U'] grammaire2 = ['a']);
  assert (premier_LR1 [NonTerminal 'V'] grammaire2 = ['c']);
  assert (premier_LR1 [NonTerminal 'S'] grammaire2 = ['a'; 'c'])


(*
let parse (g : ('token_type, 'non_terminal) grammar)
    (text : 'token_type token list) : ('token_type, 'non_terminal) syntax_tree =
  _
*)
