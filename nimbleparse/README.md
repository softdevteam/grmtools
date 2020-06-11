# `nimbleparse`

`nimbleparse` is a simple grammar debugging aid. It takes as input a Lex
specification, a Yacc specification, and an input file and prints any warnings
about the specifications (e.g. shift/reduce errors) as well as the resulting
parse tree to stdout. If the parse is unsuccessful it will report parsing
errors and, when possible fixes. If parsing is successful, `nimbleparse` exits
with 0; if an error is detected it exits with 1.

The full command-line specification is as follows:

```
nimbleparse [-r <cpctplus|none>] [-y <eco|grmtools|original>] [-q] <lexer.l> <parser.y> <input file>
```

where:

* `-r` selects the recovery algorithm to be used. Defaults to `cpctplus`.
* `-y` selects the Yacc variant to be used. Defaults to `original`.
* `-q` prevents warnings (e.g. shift/reduce errors) from being reported.

You can use your own Lex/Yacc files. A small repository of example grammars can
be found at https://github.com/softdevteam/grammars/.

An example invocation is as follows:

```
$ cat Hello.java
class Hello {
    public static void main(String[] args) {
        System.out.println("Hello world");
    }
}
$ nimbleparse java7.l java7.y Hello.java
goal
 compilation_unit
  type_declarations_opt
   type_declarations
    type_declaration
     class_declaration
      modifiers_opt
      CLASS class
      IDENTIFIER Hello
      type_parameters_opt
      super_opt
      interfaces_opt
      class_body
       LBRACE {
       class_body_declarations_opt
        class_body_declarations
         class_body_declaration
          class_member_declaration
           method_declaration
            method_header
             modifiers_opt
              modifiers
               modifiers
                modifier
                 PUBLIC public
               modifier
                STATIC static
             VOID void
             method_declarator
              IDENTIFIER main
              LPAREN (
              formal_parameter_list_opt
               formal_parameter_list
                formal_parameter
                 type
                  reference_type
                   array_type
                    name
                     simple_name
                      IDENTIFIER String
                    dims
                     LBRACK [
                     RBRACK ]
                 variable_declarator_id
                  IDENTIFIER args
              RPAREN )
             throws_opt
            method_body
             block
              LBRACE {
              block_statements_opt
               block_statements
                block_statement
                 statement
                  statement_without_trailing_substatement
                   expression_statement
                    statement_expression
                     method_invocation
                      qualified_name
                       name
                        qualified_name
                         name
                          simple_name
                           IDENTIFIER System
                         DOT .
                         IDENTIFIER out
                       DOT .
                       IDENTIFIER println
                      LPAREN (
                      argument_list_opt
                       argument_list
                        expression
                         assignment_expression
                          conditional_expression
                           conditional_or_expression
                            conditional_and_expression
                             inclusive_or_expression
                              exclusive_or_expression
                               and_expression
                                equality_expression
                                 instanceof_expression
                                  relational_expression
                                   shift_expression
                                    additive_expression
                                     multiplicative_expression
                                      unary_expression
                                       unary_expression_not_plus_minus
                                        postfix_expression
                                         primary
                                          primary_no_new_array
                                           literal
                                            STRING_LITERAL "Hello world"
                      RPAREN )
                    SEMICOLON ;
              RBRACE }
       RBRACE }
$ cat SyntaxError.java
class SyntaxError {
    int x y;
}
$ nimbleparse java7.l java7.y Hello.java
goal
 compilation_unit
  type_declarations_opt
   type_declarations
    type_declaration
     class_declaration
      modifiers_opt
      CLASS class
      IDENTIFIER SyntaxError
      type_parameters_opt
      super_opt
      interfaces_opt
      class_body
       LBRACE {
       class_body_declarations_opt
        class_body_declarations
         class_body_declaration
          class_member_declaration
           field_declaration
            modifiers_opt
            type
             primitive_type
              numeric_type
               integral_type
                INT int
            variable_declarators
             variable_declarators
              variable_declarator
               variable_declarator_id
                IDENTIFIER x
             COMMA 
             variable_declarator
              variable_declarator_id
               IDENTIFIER y
            SEMICOLON ;
       RBRACE }

Parsing error at line 2 column 11. Repair sequences found:
   1: Insert ,
   2: Insert =
   3: Delete y
```
