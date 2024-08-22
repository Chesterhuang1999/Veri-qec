%{
#include "qec_parser.tab.h"  // Bison-generated header file
%}

%%
[Ii][Ff]          { return IF; }
[Tt][Hh][Ee][Nn]  { return THEN; }
[Ee][Ll][Ss][Ee]  { return ELSE; }
[Ww][Hh][Ii][Ll][Ee] { return WHILE; }
[Ee][Nn][Dd]      { return END; }   
[Dd][Oo]          { return DO; }
[Ss][Kk][Ii][Pp]  { return SKIP; }
[Tt][Oo]          { return TO; }
[Mm][Ee][Aa][Ss]  { return MEAS; }
[Ff][Oo][Rr]      { return FOR; }
[Tt][Rr][Uu][Ee]  { return TRUE; }
[Ff][Aa][Ll][Ss][Ee] { return FALSE; }

[0-9]+            { yylval.num = atoi(yytext); return NUMBER; }
[a-zA-Z]+ { yylval.name = strdup(yytext); return NAME; }
"||"              { return OR; }
"&&"              { return AND; }
"|"              { return BITOR; }
"&"              { return BITAND; }
"=="              { return EQ; }
"!="              { return NEQ; }
"<="              { return LEQ; }
">="              { return GEQ; }

[\t]+ ;
\n;
.;
%%

int yywrap(void) {
    return 1; // End of file
}
