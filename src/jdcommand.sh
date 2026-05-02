#!/usr/bin/sh

ocamlopt -g utils.ml automaton.ml regex.ml lexer.ml parser.ml regex_grammar.ml grammar_grammar.ml caml_light.ml rectify.ml rectify_helper.ml while.ml while_cli.ml && ./a.out ../test2.1.ml | ocamlformat --name="test2.1g.ml" -
rm *.cmi
rm *.cmx
rm *.cmo
rm *.o
