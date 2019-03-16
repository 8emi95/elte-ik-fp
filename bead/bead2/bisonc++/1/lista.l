%option noyywrap c++

%{
#include "Parserbase.h"
%}

BETU        [a-zA-Z]
SZAMJEGY    [0-9]
WS      [ \t\n]

%%

({BETU}|{SZAMJEGY})+    return Parser::ELEM;
","         return Parser::VESSZO;
"["         return Parser::NYITO;
"]"         return Parser::CSUKO;

{WS}+   // feher szokozok: semmi teendo

. {
    std::cerr << "lexikalis hiba" << std::endl;
    exit(1);
}

%%
