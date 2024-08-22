%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Define value type for semantic actions
typedef struct {
    int num;
    char* name;
    // Add other types if needed
} YYSTYPE;

#define YYSTYPE YYSTYPE
%}

%token IF THEN ELSE WHILE DO SKIP TO MEAS FOR END TRUE FALSE 
%token NAME NUMBER OR AND EQ NEQ GEQ LEQ BITAND BITOR 
// Define other tokens...

%left OR AND
%left EQ NEQ
%left '+' '-'
%left '*' '/'



%%
triple: bexpr ',' program ',' bexpr

program:
    statements ;

statements:
    statement
    | statements ';' statement
    ;

statement: IF bexpr THEN program ELSE program END 
    | WHILE aexpr DO program END
    | SKIP
    ;


bexpr: bterm
    | bterm BITAND bexpr 
    | bterm BITOR bexpr
    ;
    
bterm: 

    | aexpr LEQ aexpr
    | aexpr GEQ aexpr
    | aexpr EQ aexpr
    | aexpr NEQ aexpr
    | aexpr
    ;

aexpr: aterm
    | aterm '+' aexpr
    | aterm '-' aexpr
    ;

aterm: afactor 
    | afactor '*' aterm
    | afactor '/' aterm
    ;

afactor: NUMBER
    | NAME
    ;

%%

int main() {
    yyparse();
    return 0;
}

// void yyerror(const char *s) {
//     fprintf(stderr, "Error: %s\n", s);
// }
