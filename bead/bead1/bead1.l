%option noyywrap c++ yylineno

%{
#include <iostream>
#include <cstdlib>
%}

DIGIT   [0-9]
WS      [ \t\n]

%%

{DIGIT}+                std::cout << "szam:                     " << YYText() << std::endl; // karakterek

int                     std::cout << "kulcsszo:                 " << YYText() << std::endl; // kulcsszavak
main                    std::cout << "kulcsszo:                 " << YYText() << std::endl;
unsigned                std::cout << "kulcsszo:                 " << YYText() << std::endl;
bool                    std::cout << "kulcsszo:                 " << YYText() << std::endl;
true                    std::cout << "kulcsszo:                 " << YYText() << std::endl;
false                   std::cout << "kulcsszo:                 " << YYText() << std::endl;
if                      std::cout << "kulcsszo:                 " << YYText() << std::endl;
else                    std::cout << "kulcsszo:                 " << YYText() << std::endl;
while                   std::cout << "kulcsszo:                 " << YYText() << std::endl;
cout                    std::cout << "kulcsszo:                 " << YYText() << std::endl;
cin                     std::cout << "kulcsszo:                 " << YYText() << std::endl;

[a-zA-Z][a-zA-Z0-9_]*   std::cout << "valtozo:                  " << YYText() << std::endl; // azonositok

"//".*                  std::cout << "megjegyzes:               " << YYText() << std::endl; // megjegyzesek

"+"                     std::cout << "osszeadas:                " << YYText() << std::endl; // operatorok
"-"                     std::cout << "kivonas:                  " << YYText() << std::endl;
"*"                     std::cout << "szorzas:                  " << YYText() << std::endl;
"/"                     std::cout << "osztas:                   " << YYText() << std::endl;
"%"                     std::cout << "maradekkepzes:            " << YYText() << std::endl;
"("                     std::cout << "nyito zarojel:            " << YYText() << std::endl;
")"                     std::cout << "zaro zarojel:             " << YYText() << std::endl;
"=="                    std::cout << "egyenloseg:               " << YYText() << std::endl;
"<"                     std::cout << "kisebb:                   " << YYText() << std::endl;
">"                     std::cout << "nagyobb:                  " << YYText() << std::endl;
"<="                    std::cout << "kisebb vagy egyenlo:      " << YYText() << std::endl;
">="                    std::cout << "nagyobb vagy egyenlo:     " << YYText() << std::endl;
"&&"                    std::cout << "konjunkcio:               " << YYText() << std::endl;
"||"                    std::cout << "diszjunkcio:              " << YYText() << std::endl;
"!"                     std::cout << "negacio:                  " << YYText() << std::endl;
"="                     std::cout << "ertekadas:                " << YYText() << std::endl;
">>"                    std::cout << "beolvasas:                " << YYText() << std::endl;
"<<"                    std::cout << "kiiras:                   " << YYText() << std::endl;

"{"                     std::cout << "nyito kapcsos zarojel:    " << YYText() << std::endl; // torzs, utasitas
"}"                     std::cout << "zaro kapcsos zarojel:     " << YYText() << std::endl;
";"                     std::cout << "pontosvesszo:             " << YYText() << std::endl;

{WS}+   // Whitespace

. {
    std::cerr << lineno() << ": Lexikalis hiba." << std::endl;
    exit(1);
}

%%
