open Regex_grammar

let r1 = parse_regex "abc|(bc)*"

let _ =
  assert (
    r1
    = Regex.Concatenation
        ( Regex.Symbol 'a',
          Regex.Concatenation
            ( Regex.Symbol 'b',
              Regex.Union
                ( Regex.Symbol 'c',
                  Regex.Star
                    (Regex.Concatenation (Regex.Symbol 'b', Regex.Symbol 'c'))
                ) ) ))
