open Lexer
open Regex_grammar
open Parser
open Grammar_grammar

let caml_light_tokens, caml_light_grammar =
  let caml_light_grammar_definition_fp = open_in "../caml_light.grammar" in
  let caml_light_grammar_definition =
    really_input_string caml_light_grammar_definition_fp
      (in_channel_length caml_light_grammar_definition_fp)
  in
  close_in caml_light_grammar_definition_fp;
  parse_grammar caml_light_grammar_definition

let caml_light_automaton =
  construit_automate_LR1 caml_light_grammar "IMPLEMENTATION" "<eof>"

let rec collapse_precedence (target : string)
    (tree : (string, string) syntax_tree) : (string, string) syntax_tree =
  match tree with
  | Node (nt1, [ Node (nt2, children) ])
    when nt1 = target && String.starts_with ~prefix:target nt2 ->
      collapse_precedence target (Node (target, children))
  | Node (nt, children)
    when nt <> target && String.starts_with ~prefix:target nt ->
      collapse_precedence target (Node (target, children))
  | Node (nt, children) ->
      Node (nt, List.map (collapse_precedence target) children)
  | _ -> tree

let parse_caml_light_syntax_tree (source : string) =
  let enhanced_token_rules =
    List.rev_append caml_light_tokens
      [
        (parse_regex "( |\\n|\\t)+", "<whitespace>");
        (parse_regex "\\(\\*", "<comment_start>");
        (parse_regex "\\*\\)", "<comment_end>");
        (parse_regex "[ -~]", "<unrecognizable>");
      ]
  in
  let tokens = tokenize enhanced_token_rules "<eof>" source in

  let rec filter_tokens_from (tokens : string token list) (comment_level : int)
      (res : string token list) =
    if comment_level < 0 then failwith "Too many comment end tags"
    else
      match tokens with
      | [] -> List.rev res
      | x :: q -> (
          match x.token_type with
          | "<comment_start>" -> filter_tokens_from q (comment_level + 1) res
          | "<comment_end>" -> filter_tokens_from q (comment_level - 1) res
          | "<whitespace>" -> filter_tokens_from q comment_level res
          | _ ->
              if comment_level > 0 then filter_tokens_from q comment_level res
              else filter_tokens_from q comment_level (x :: res))
  in

  let filtered_tokens = filter_tokens_from tokens 0 [] in
  parse caml_light_automaton "<eof>" filtered_tokens "IMPLEMENTATION"
  |> collapse_precedence "EXPR"
  |> collapse_precedence "PATTERN"
  |> collapse_precedence "TYP_EXPR"
