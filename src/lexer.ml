open Regex
open Automaton
open Utils

type 'a token = { token_type : 'a; value : string; start : int; length : int }

exception Tokenize_failure of { current_pos : int }

let tokenize (rules : (uchar regex * 'a) list) (tok_eof : 'a) (tok_unknown : 'a)
    (text : string) : 'a token list =
  if List.find_opt (fun (_, token_type) -> token_type = tok_eof) rules <> None
  then failwith "EOF token had production rule"
  else
    let automatons =
      List.map
        (fun (regex, t) ->
          ( regex |> automaton_of_regex |> remove_epsilon_transitions
            |> determinize |> remove_state [],
            t ))
        rules
    in
    let rec tokenize_from (global_offset : int) (remaining_text : uchar list)
        (reversed_result : 'a token list) : 'a token list =
      if remaining_text = [] then
        { token_type = tok_eof; value = ""; start = global_offset; length = 0 }
        :: reversed_result
      else
        let rec read_longest_token_from (start : int)
            (alive_states : (uchar, _) execution_state list)
            (current_result : ('a token * uchar list) option)
            (current_lexeme : uchar list) (remaining_text : uchar list) :
            ('a token * uchar list) option =
          if List.length alive_states = 0 then current_result
          else
            let final_states = List.filter is_final_state alive_states in
            let next_result =
              match final_states with
              | [] -> current_result
              | e :: _ ->
                  Some
                    ( {
                        token_type = List.assq e.automaton automatons;
                        value = implode_uchar (List.rev current_lexeme);
                        start;
                        length = List.length current_lexeme;
                      },
                      remaining_text )
            in
            match remaining_text with
            | [] -> next_result
            | c :: next_text ->
                let next_states =
                  alive_states
                  |> List.filter_map (fun state -> next_state state c)
                in
                let next_lexeme = c :: current_lexeme in
                read_longest_token_from start next_states next_result
                  next_lexeme next_text
        in
        let states = automatons |> List.map fst |> List.map start_execution in
        match
          read_longest_token_from global_offset states None [] remaining_text
        with
        (* | None -> raise (Tokenize_failure { current_pos = global_offset }) *)
        | None ->
            tokenize_from (global_offset + 1) (List.tl remaining_text)
              ({
                 start = global_offset;
                 token_type = tok_unknown;
                 value = string_of_uchar (List.hd remaining_text);
                 length = 1;
               }
              :: reversed_result)
        | Some (token, remaining_text) ->
            tokenize_from
              (global_offset + token.length)
              remaining_text (token :: reversed_result)
    in
    List.rev (tokenize_from 0 (uchar_list_of_string text) [])

let string_of_token (string_of_type : 'a -> string) (token : 'a token) =
  "Token("
  ^ string_of_type token.token_type
  ^ ", " ^ token.value ^ ", start=" ^ string_of_int token.start ^ ")"
