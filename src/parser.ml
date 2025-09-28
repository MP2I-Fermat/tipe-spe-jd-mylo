open Lexer
open Automaton

type ('token_type, 'non_terminal) grammar_entry =
  | NonTerminal of 'non_terminal
  | Terminal of 'token_type

type ('token_type, 'non_terminal) rule =
  'non_terminal * ('token_type, 'non_terminal) grammar_entry list

type ('token_type, 'non_terminal) grammar =
  ('token_type, 'non_terminal) rule list

type ('token_type, 'non_terminal) syntax_tree =
  | Node of 'non_terminal * ('token_type, 'non_terminal) syntax_tree list
  | Leaf of 'token_type token

(* Représente les situations LR(1), du style
 * α₁…αⱼ↑ α₁₊ⱼ…αₙ ~ {b₁…bₙ} *)
type ('token_type, 'non_terminal) lr1_situation =
  ('token_type, 'non_terminal) rule * int * 'token_type list list

(* Renvoie l’ensemble Premier_LR(1)(s) dans la grammaire g *)
let premier_LR1 (s : ('token_type, 'non_terminal) grammar_entry list)
    (g : ('token_type, 'non_terminal) grammar) : 'token_type list =
  let rec premier_n (n : int)
      (s : ('token_type, 'non_terminal) grammar_entry list) :
      'token_type list * bool =
    if n = 0 then
      match s with [ Terminal a ] -> ([ a ], true) | _ -> ([], false)
    else
      match s with
      | [ NonTerminal a1 ] ->
          let premier_nm1, premier_est_constant = premier_n (n - 1) s in
          if premier_est_constant then (premier_nm1, true)
          else
            let derivations =
              List.filter_map
                (fun (symbol, derivation) ->
                  if symbol = a1 then Some derivation else None)
                g
            in
            let premiers_et_variations_derivations =
              List.map (premier_n (n - 1)) derivations
            in
            let premiers_derivations_sont_constantes =
              List.for_all
                (fun (_, est_constant) -> est_constant)
                premiers_et_variations_derivations
            in
            let premiers_derivations =
              List.map fst premiers_et_variations_derivations
            in
            let prem_n =
              List.fold_left List.rev_append premier_nm1 premiers_derivations
              |> List.sort_uniq compare
            in
            (* (premier_i(N)) est en fait constant a partir du rang n - 1, voir preuves/premier_n_cts.
            On ne s'en rend compte que maintenant car on n'avait pas calculé premier_n des derivations possibles. *)
            ( prem_n,
              premiers_derivations_sont_constantes && prem_n = premier_nm1 )
      | a1 :: _ ->
          let prem_nm1, prem_est_constant = premier_n (n - 1) s in
          if prem_est_constant then (prem_nm1, true)
          else
            let prem_nm1_a1, prem_a1_est_constant = premier_n (n - 1) [ a1 ] in
            let prem_n =
              List.rev_append prem_nm1_a1 prem_nm1 |> List.sort_uniq compare
            in
            (* premier_i(a1...am) est constant a partir du rang n - 1, voir preuves/premier_n_cts. *)
            (prem_n, prem_a1_est_constant && prem_n = prem_nm1)
      | [] -> failwith "Les règles N -> epsilon ne sont pas gérées"
  in
  let rec trouve_premier_constant (n : int) =
    let premier_n, est_constant = premier_n n s in
    if est_constant then premier_n else trouve_premier_constant (n + 1)
  in
  trouve_premier_constant 0

let test_premier_LR1 =
  let grammaire1 (* page 123, exemple 144 *) =
    [ ('S', [ Terminal 'a'; NonTerminal 'T' ]); ('T', [ Terminal 'b' ]) ]
  in
  assert (premier_LR1 [ Terminal 'a'; NonTerminal 'T' ] grammaire1 = [ 'a' ]);
  assert (premier_LR1 [ NonTerminal 'T' ] grammaire1 = [ 'b' ]);
  let grammaire2 (* page 60, exemple 24 *) =
    [
      ('S', [ NonTerminal 'U' ]);
      ('S', [ NonTerminal 'V' ]);
      ('U', [ Terminal 'a'; Terminal 'b' ]);
      ('V', [ Terminal 'c'; Terminal 'd' ]);
    ]
  in
  assert (premier_LR1 [ Terminal 'a'; Terminal 'b' ] grammaire2 = [ 'a' ]);
  assert (premier_LR1 [ Terminal 'c'; Terminal 'd' ] grammaire2 = [ 'c' ]);
  assert (premier_LR1 [ NonTerminal 'U' ] grammaire2 = [ 'a' ]);
  assert (premier_LR1 [ NonTerminal 'V' ] grammaire2 = [ 'c' ]);
  assert (premier_LR1 [ NonTerminal 'S' ] grammaire2 = [ 'a'; 'c' ])

(*
let parse (g : ('token_type, 'non_terminal) grammar)
    (text : 'token_type token list) : ('token_type, 'non_terminal) syntax_tree =
  _
*)
