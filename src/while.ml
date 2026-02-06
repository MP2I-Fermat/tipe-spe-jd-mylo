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
              lhs = Ident "res_ref";
              value = FunctionApplication {
                receiver = Variable "ref";
                arguments = [Variable "None"]
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

  (* res_ref := Some(inner) *)
  let modify_res (inner: expression) : expression =
    ReferenceAssignment {
      receiver = Variable "res_ref";
      value =
        Parenthesised {
          style = Parenthesis;
          inner = FunctionApplication {
            receiver = Variable "Some";
            arguments = [Parenthesised{style=Parenthesis; inner}]
          }
        }
    }
  in

  (* Renvoie une liste de définitions de variables temporaires correspondant aux
   * anciennes valeurs des arguments *)
  let rec parameter_list_to_let_list (p: string list) (inner_expr: expression) :
      expression =
    match p with
    | [] -> inner_expr
    | x::q ->
        parameter_list_to_let_list q
        (LetBinding {
          bindings = [
            Variable {
              lhs = Ident x;
              value = Dereference(Variable(x^"_ref"))
            }
          ];
          is_rec = false;
          inner = inner_expr
        })
  in

  (* modifie `res_ref` quand on trouve la valeur de l’expression *)
  let rec replace_result (p: string list) (inner_expr: expression) :
      expression =
    match inner_expr with
    | Parenthesised { inner ; style } ->
        Parenthesised {
          inner = replace_result p inner ;
          style = style
        }
    | TypeCoercion {inner ; typ } ->
        TypeCoercion {
          inner = replace_result p inner ;
          typ = typ
        }
    | FunctionApplication { receiver ; arguments } ->
        begin match receiver with
        | Parenthesised { inner=Variable(rec_call_name) ; style=_ }
        | Variable(rec_call_name)
            when List.mem rec_call_name recursive_call_names ->
          let seq = Caml_light.Sequence (
            List.map
            (fun (nom, valeur) ->
              Caml_light.ReferenceAssignment {
                receiver = Variable(nom^"_ref");
                value = valeur
              }
            )
            (List.combine p arguments)
          )
          in
          Parenthesised {
            style = BeginEnd;
            inner = seq
          }
        | _ ->
          modify_res (FunctionApplication { receiver ; arguments })
        end
    | If { condition ; body ; else_body } ->
        If {
          condition = condition ;
          body = replace_result p body ;
          else_body =
            Option.map (replace_result p) else_body
        }
    | Sequence(l) ->
        let n = List.length l in
        Sequence (
          List.mapi (fun i x -> if i = (n-1) then replace_result p x else x) l
        )
    | Match { value ; cases } ->
        Match {
          value ;
          cases = List.map
            (fun (pattern, expr) -> (pattern, replace_result p expr))
            cases
        }
    | Try { value ; cases } ->
        Try {
          value ;
          cases = List.map
            (fun (pattern, expr) -> (pattern, replace_result p  expr))
            cases
        }
    | FunctionLiteral f ->
        (* TODO à repenser certainement *)
        modify_res (FunctionLiteral f)
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
                    value ;
                  }: binding)
              | Function { name ; parameters ; body ; return_type } ->
                  (* TODO à repenser aussi *)
                  Function {
                    name ;
                    parameters ;
                    body ;
                    return_type
                  }
            ) bindings ;
          is_rec ;
          inner = replace_result p inner
        }
    | v -> modify_res v
  in

  let wrap_in_while (body: expression) : expression =
    Sequence [
      WhileLoop {
        condition = InfixOperation {
          lhs = Dereference(Variable "res_ref");
          rhs = Variable "None";
          operation = Eq
        };
        body;
      };
      FunctionApplication {
        receiver = FieldAccess { receiver = Variable "Option"; target = "get"};
        arguments = [
          Parenthesised {
            style = Parenthesis;
            inner = Dereference(Variable "res_ref")
          }
        ]
      }
    ]
  in

  let params = List.filter_map
    (fun (x: pattern) -> match x with
      | (TypeCoercion {inner = Ident name; _})
      | Ident name -> Some name
      | _ -> None
    ) parameters in
  replace_result params body
  |> parameter_list_to_let_list params
  |> wrap_in_while
  |> parameter_list_to_ref_list params


let parse_file name =
  let input_channel = open_in name in
  let content = really_input_string input_channel
      (in_channel_length input_channel) in
  close_in input_channel;
  parse_caml_light_ast content


let whilify (program: phrase list) =
  let interceptor (name: string) (parameters: pattern list)
      (return_type: type_expression option) : binding =
    Function {
      name;
      return_type;
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
        arguments = List.mapi
          Caml_light.(fun i x ->
            match x with
            | Ident(v) -> Variable(v)
            | TypeCoercion { inner=Ident(v); typ } -> Variable(v)
            | _ -> Variable("arg"^(string_of_int i))
          ) parameters @ [
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
  in
  let whilify_phrase (phrase: phrase) : phrase list =
    match phrase with
    | ValueDefinition { bindings; is_rec }
        when is_rec && List.length bindings = 1 -> (
      let one_binding = List.hd bindings in

      let linearised_binding_option =
        match one_binding with
        | Variable _ -> None
        | Function {name; parameters; body; return_type} ->
            let body_lin, _ = linearize body 0 in
            Some (
              name,
              FunctionLiteral {
                style = Fun;
                cases = [(parameters, body_lin)];
                return_type_for_delinearize = return_type;
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
                "pour la fonction" ^ (fst linearised_binding) ^ " *)");
              [phrase]
          | Some clot ->
            let name, new_fn, parameters, return_type =
              match linearised_binding with
              | name, (
                FunctionLiteral {
                  style; cases = [(parameters, body_lin)];
                  return_type_for_delinearize
                }) ->
                 let body_delin, _ =
                  delinearize
                    (rename_elements
                       (rectify body_lin clot body_lin)
                       clot new_name) [] in
                 let body_while =
                   fonction_vers_while
                     (new_name name) (parameters @ [Ident "cont"]) body_delin
                     (List.map new_name clot) in
                 name, (Function {
                     name = name^"_whilified";
                     parameters = parameters @ [Ident "cont"];
                     body = body_while;
                     return_type = return_type_for_delinearize
                  } : Caml_light.binding), parameters,
                  return_type_for_delinearize
              | _ -> failwith "Pas une fonction ?"

            in
            [
              ValueDefinition {
                is_rec = false;
                bindings = [new_fn]
              } ; ValueDefinition {
                is_rec = false;
                bindings = [interceptor name parameters return_type]
              }
           ]
         end)
    | _ -> [phrase]
  in
  program |> List.map whilify_phrase |> List.concat


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

