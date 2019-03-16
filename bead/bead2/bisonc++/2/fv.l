%option noyywrap c++

%{
#include "Parserbase.h"
%}

BETU		[a-zA-Z]
SZAMJEGY	[0-9]
WS		[ \t\n]

%%

{BETU}({BETU}|{SZAMJEGY}|"_")*	return Parser::AZONOSITO;
","				return Parser::VESSZO;
"("				return Parser::NYITO;
")"				return Parser::CSUKO;
";"				return Parser::PONTOSVESSZO;

{WS}+	// feher szokozok: semmi teendo

. {
	std::cerr << "lexikalis hiba" << std::endl;
	return 0;
}

%%
