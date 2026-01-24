open Caml_light
open Rectify

(* Renvoie l’AST de la fonction récursive terminale f une fois avoir été
 * transformée en boucle while (la sortie est toujours l’AST d’une fonction).
 * Les appels récursifs sont supposés être faits sur des noms de variables
 * uniquement (i.e. la fonction appelée ne doit pas être le résultat d’une
 * expression) et la liste de variables pouvant conduire à un appel récursif
 * sont listées dans `recursive_call_names`.
 *)
let fonction_vers_while
    (name: variable)
    (parameters: pattern list)
    (body: expression)
    (recursive_call_names: variable list) : expression =

  (* Renvoie une liste de définitions de refs correspondant aux arguments *)
  let rec parameter_list_to_ref_list (p: string list) (inner_expr: expression) :
      expression =
    match p with
    | [] ->
        (LetBinding ({
          bindings = [
            Variable {
              lhs = Ident "_call_";
              value = FunctionApplication {
                receiver = Variable "ref";
                arguments = [Variable "true"]
              }
            }
          ];
          is_rec = false;
          inner = inner_expr
        }))
    | x::q ->
        parameter_list_to_ref_list q
        (LetBinding {
          bindings = [
            Variable {
              lhs = Ident (x^"_ref");
              value = FunctionApplication {
                receiver = Variable "ref";
                arguments = [Variable x]
              }
            }
          ];
          is_rec = false;
          inner = inner_expr
        })
  in

  (* Renvoie une liste de définitions de variables temporaires correspondant aux
   * arguments *)
  let rec parameter_list_to_temp_list (p: string list)
      (new_vals: expression list) (inner_expr: expression) : expression =
    match p, new_vals with
    | [], [] -> inner_expr
    | [], _ | _, [] -> failwith "pas la même taille"
    | x::q, v::qv ->
        parameter_list_to_temp_list q qv
        (LetBinding {
          bindings = [
            Variable {
              lhs = Ident (x^"_temp");
              value = replace_args_with_refs p v
            }
          ];
          is_rec = false;
          inner = inner_expr
        })

  (* Remplace les références aux arguments par les refs correspondants *)
  and replace_args_with_refs (p: string list) (inner_expr: expression) :
      expression =
    match inner_expr with
    | Variable(s) ->
        if List.mem s p then
          Dereference(Variable(s^"_ref"))
        else
          Variable(s)
    | Constant(c) -> Constant(c)
    | Parenthesised { inner ; style } ->
        Parenthesised { inner = replace_args_with_refs p inner ; style = style}
    | TypeCoercion {inner ; typ } ->
        TypeCoercion { inner = replace_args_with_refs p inner ; typ = typ }
    | ListLiteral(l) ->
        ListLiteral (List.map (replace_args_with_refs p) l)
    | ArrayLiteral(l) ->
        ArrayLiteral (List.map (replace_args_with_refs p) l)
    | RecordLiteral(l) ->
        RecordLiteral
          (List.map (fun (lbl, expr) -> (lbl, replace_args_with_refs p expr)) l)
    | WhileLoop { condition ; body } ->
        WhileLoop {
          condition = replace_args_with_refs p condition ;
          body = replace_args_with_refs p body
        }
    | ForLoop { direction; variable; start; finish; body } ->
        ForLoop {
          direction = direction;
          variable = variable;
          start = replace_args_with_refs p start;
          finish = replace_args_with_refs p finish;
          body = replace_args_with_refs p body
        }
    | Dereference(e) ->
        Dereference(replace_args_with_refs p e)
    | FieldAccess { receiver ; target } ->
        FieldAccess {
          receiver = replace_args_with_refs p receiver ;
          target
        }
    | ArrayAccess { receiver ; target } ->
        ArrayAccess {
          receiver = replace_args_with_refs p receiver ;
          target = replace_args_with_refs p target
        }
    | FunctionApplication { receiver ; arguments } ->
        begin match receiver with
        | Parenthesised { inner=Variable(rec_call_name) ; style=_ }
        | Variable(rec_call_name)
            when List.mem rec_call_name recursive_call_names ->
          let seq = Caml_light.Sequence (
            ReferenceAssignment {
              receiver = Variable("_call_");
              value = Variable("true")
            }::
            List.map
            (fun nom ->
              Caml_light.ReferenceAssignment {
                receiver = Variable(nom^"_ref");
                value = Variable(nom^"_temp")
              }
            )
            p
          )
          in
          parameter_list_to_temp_list p arguments seq
        | _ ->
          FunctionApplication {
            receiver = replace_args_with_refs p receiver ;
            arguments = List.map (replace_args_with_refs p) arguments
          }
        end
    | PrefixOperation { receiver ; operation } ->
        PrefixOperation {
          receiver = replace_args_with_refs p receiver ;
          operation
        }
    | InfixOperation { lhs ; rhs ; operation } ->
        InfixOperation {
          lhs = replace_args_with_refs p lhs ;
          rhs = replace_args_with_refs p rhs ;
          operation
        }
    | Negation(e) ->
        Negation(replace_args_with_refs p e)
    | Tuple(l) ->
        Tuple (List.map (replace_args_with_refs p) l)
    | FieldAssignment { receiver ; target ; value } ->
        FieldAssignment {
          receiver = replace_args_with_refs p receiver ;
          target;
          value = replace_args_with_refs p value
        }
    | ArrayAssignment { receiver ; target ; value } ->
        ArrayAssignment {
          receiver = replace_args_with_refs p receiver ;
          target = replace_args_with_refs p target ;
          value = replace_args_with_refs p value
        }
    | ReferenceAssignment { receiver ; value } ->
        ReferenceAssignment {
          receiver = replace_args_with_refs p receiver ;
          value = replace_args_with_refs p value
    }
    | If { condition ; body ; else_body } ->
        If {
          condition = replace_args_with_refs p condition ;
          body = replace_args_with_refs p body ;
          else_body =
            match else_body with
            | None -> None
            | Some(e) -> Some(replace_args_with_refs p e)
        }
    | Sequence(l) ->
        Sequence (List.map (replace_args_with_refs p) l)
    | Match { value ; cases } ->
        Match {
          value = replace_args_with_refs p value ;
          cases = List.map
            (fun (pattern, expr) -> (pattern, replace_args_with_refs p expr))
            cases
        }
    | Try { value ; cases } ->
        Try {
          value = replace_args_with_refs p value ;
          cases = List.map
            (fun (pattern, expr) -> (pattern, replace_args_with_refs p expr))
            cases
        }
    | FunctionLiteral { style ; cases } ->
        (* TODO à repenser certainemenjt *)
        FunctionLiteral {
          style;
          cases = List.map
            (fun (pattern, expr) -> (pattern, replace_args_with_refs p expr))
            cases
        }
    | LetBinding {
        bindings : binding node list;
        is_rec : bool;
        inner : expression node;
      } ->
        LetBinding {
          bindings = List.map
            (fun (b: binding) ->
              match b with
              | Variable { lhs ; value } ->
                  (Variable {
                    lhs ;
                    value = replace_args_with_refs p value
                  }: binding)
              | Function { name ; parameters ; body } ->
                  (* TODO à repenser aussi *)
                  Function {
                    name ;
                    parameters ;
                    body = replace_args_with_refs p body
                  }
            ) bindings ;
          is_rec ;
          inner = replace_args_with_refs p inner
        }
    | StringAccess { receiver ; target } ->
        StringAccess {
          receiver = replace_args_with_refs p receiver;
          target = replace_args_with_refs p target
        }
    | StringAssignment { receiver ; target ; value } ->
        StringAssignment {
          receiver = replace_args_with_refs p receiver;
          target = replace_args_with_refs p target;
          value = replace_args_with_refs p value;
        }
  in

  let wrap_in_while (body: expression) : expression =
    WhileLoop {
      condition = Dereference(Variable "_call_");
      body = Sequence [
        ReferenceAssignment {
          receiver = Variable "_call_" ;
          value = Variable "false"
        };
        body
      ]
    }
  in

  let params = List.filter_map
    (fun (x: pattern) -> match x with
      | (TypeCoercion {inner = Ident name; _})
      | Ident name -> Some name
      | _ -> None
    ) parameters in
  parameter_list_to_ref_list params
    (wrap_in_while (replace_args_with_refs params body))


let parse_file name =
  let input_channel = open_in name in
  let content = really_input_string input_channel
      (in_channel_length input_channel) in
  close_in input_channel;
  parse_caml_light_ast content


let whilify (program: phrase list) =
  program
  |> List.map (
    fun phrase ->
       match phrase with
       | ValueDefinition { bindings; is_rec }
           when is_rec && List.length bindings = 1 -> (
         let one_binding = List.hd bindings in

         let linearised_binding_option =
           match one_binding with
           | Variable _ -> None
           | Function {name; parameters; body } ->
               let body_lin, _ = linearize body 0 in
               Some (
                 name,
                 FunctionLiteral {
                   style = Fun;
                   cases = [ (parameters, body_lin) ];
                 }
               )
           in

           match linearised_binding_option with
           | None -> [phrase]
           | Some linearised_binding -> begin
             let new_name (n : string) = n ^ "_rectified" in

             match cloture_rectifiable [linearised_binding] with
             | None ->
                 print_endline
                  ("(* Avertissement : cloture_rectifiable a renvoyé None " ^
                   "pour la fonction" ^ (fst linearised_binding) ^ ")");
                 [phrase]
             | Some clot ->
               let name, new_fn, parameters = match linearised_binding with
               | name, (
                 FunctionLiteral {
                   style; cases = [(parameters, body_lin)]
                 }) ->
                  let body_delin, _ =
                   delinearize
                     (push_rectified_definitions
                        (rectify body_lin clot)
                        clot new_name) [] in
                  let body_while =
                    fonction_vers_while
                      (new_name name) (parameters @ [Ident "cont"]) body_delin
                      (List.map new_name clot) in
                  name, (Function {
                      name = name^"_whilified";
                      parameters = parameters @ [Ident "cont"];
                      body = body_while
                   } : Caml_light.binding), parameters
               | _ -> failwith "Pas une fonction ?"

               in
               [
                 ValueDefinition {
                   is_rec = false;
                   bindings = [new_fn]
                 } ; ValueDefinition {
                   is_rec = false;
                   bindings = [
                     Function {
                       name = name;
                       parameters =
                         List.mapi
                         Caml_light.(fun i x ->
                            match x with
                            | Ident(v) -> Ident(v)
                            | TypeCoercion { inner=Ident(v); typ } ->
                                TypeCoercion { inner=Ident(v); typ }
                            | _ -> Ident("arg"^(string_of_int i))
                         )
                         parameters;
                       body = FunctionApplication {
                         receiver = Variable(name^"_whilified");
                         arguments =
                           List.mapi
                           Caml_light.(fun i x ->
                             match x with
                             | Ident(v) -> Variable(v)
                             | TypeCoercion { inner=Ident(v); typ } ->
                                 Variable(v)
                             | _ -> Variable("arg"^(string_of_int i))
                           )
                           parameters @ [
                             Parenthesised {
                               style = Parenthesis;
                               inner = FunctionLiteral {
                                 style = Fun;
                                 cases = [[Ident "x"], Variable "x"]
                               }
                            }
                          ]
                       }
                     }
                   ]
                 }
              ]
            end)
       | _ -> [phrase]
  ) |> List.concat


let main () =
  let test_source =
    if Array.length Sys.argv <= 1 then
      failwith "Merci de donner un argument : le nom de fichier"
    else begin
      let test_source_fp = open_in Sys.argv.(1) in
      let test_source =
        really_input_string test_source_fp (in_channel_length test_source_fp)
      in
      close_in test_source_fp;
      test_source
    end
  in
  let program = parse_caml_light_ast test_source in
  whilify program |> string_of_ast


let () = print_endline (main ())

(*
let test2 =
  let src = parse_file "../test2.ml" in
  match src with
  | [ValueDefinition
  {bindings =
    [Function
      {name = "fizzbuzz";
       parameters =
        [TypeCoercion
          {inner = Ident "max";
           typ = Construction {constructor = "int"; arguments = []}}];
       body =
        LetBinding
         {bindings =
           [Function
             {name;
              parameters;
              body}];
          is_rec = true;
          inner =
           FunctionApplication
            {receiver = Variable "fizzbuzz_a_partir";
             arguments = [Constant (IntegerLiteral 1)]}}}];
     is_rec = false}]
     ->
    [ValueDefinition
    {bindings =
    [Function
      {name = "fizzbuzz";
       parameters =
        [TypeCoercion
          {inner = Ident "max";
           typ = Construction {constructor = "int"; arguments = []}}];
       body =
        LetBinding
         {bindings =
           [Function
             {name;
              parameters;
              body = fonction_vers_while name parameters body ["fizzbuzz_a_partir"]}];
          is_rec = false;
          inner =
           FunctionApplication
            {receiver = Variable "fizzbuzz_a_partir";
             arguments = [Constant (IntegerLiteral 1)]}}}];
     is_rec = false}] |> string_of_ast
  | _ -> failwith "pas le test2"

(*let () = print_endline test2*)
  *)
