open Caml_light

(* Renvoie l’AST de la fonction récursive f une fois avoir été transformée en
 * boucle while (la sortie est toujours l’AST d’une fonction) *)
let fonction_vers_while
    (name: variable)
    (parameters: pattern list)
    (body: expression) : expression =
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
                arguments = [Variable "false"]
              }
            }
          ];
          is_rec = false;
          inner = inner_expr
        }))
    | x::q ->
        parameter_list_to_ref_list q
        (LetBinding ({
          bindings = [
            Variable {
              lhs = Ident ("_"^x^"_ref_");
              value = FunctionApplication {
                receiver = Variable "ref";
                arguments = [Variable x]
              }
            }
          ];
          is_rec = false;
          inner = inner_expr
        }))
  in
  let params = List.filter_map
    (fun x -> match x with
      | (TypeCoercion {inner = Ident name; _})
      | Ident name -> Some name
      | _ -> None
    ) parameters in
  parameter_list_to_ref_list params body

let parse_file name =
  let input_channel = open_in name in
  let content = really_input_string input_channel (in_channel_length input_channel) in
  close_in input_channel;
  parse_caml_light_ast content

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
             arguments = [Constant (IntegerLiteral 0)]}}}];
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
              body = fonction_vers_while name parameters body}];
          is_rec = false;
          inner =
           FunctionApplication
            {receiver = Variable "fizzbuzz_a_partir";
             arguments = [Constant (IntegerLiteral 0)]}}}];
     is_rec = false}] |> string_of_ast
  | _ -> failwith "pas le test2"


let () = print_endline test2;
