let explode (s : string) : char list =
  List.init (String.length s) (String.get s)

let implode (chars : char list) : string = String.of_seq (List.to_seq chars)
